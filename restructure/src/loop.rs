use array_tool::vec::Intersect;
use ast::{Reduce, SideEffects};
use cfg::block::{BlockEdge, BranchType};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use tuple::Map;

use crate::GraphStructurer;
use petgraph::{algo::dominators::Dominators, stable_graph::NodeIndex, visit::EdgeRef};

impl GraphStructurer {
    /// Checks if a node is a loop header
    #[inline]
    pub(crate) fn is_loop_header(&self, node: NodeIndex) -> bool {
        self.loop_headers.contains(&node)
    }

    /// Checks if a node contains a for-loop next statement
    #[inline]
    pub(crate) fn is_for_next(&self, node: NodeIndex) -> bool {
        self.function
            .block(node)
            .and_then(|block| block.first())
            .map_or(false, |s| {
                matches!(
                    s,
                    ast::Statement::GenericForNext(_) | ast::Statement::NumForNext(_)
                )
            })
    }

    /// Finds the initialization block and index for a for-loop
    /// Returns (block_index, statement_index)
    fn find_for_init(&self, for_loop: NodeIndex) -> (NodeIndex, usize) {
        let predecessors: Vec<_> = self
            .function
            .predecessor_blocks(for_loop)
            .filter(|&p| p != for_loop)
            .collect();

        let init_blocks = predecessors.into_iter().filter_map(|p| {
            self.function
                .block(p)?
                .iter()
                .enumerate()
                .rev()
                .find(|(_, s)| {
                    s.has_side_effects()
                        || s.as_num_for_init().is_some()
                        || s.as_generic_for_init().is_some()
                })
                .and_then(|(i, s)| {
                    if s.as_num_for_init().is_some() || s.as_generic_for_init().is_some() {
                        Some((p, i))
                    } else {
                        None
                    }
                })
        });

        init_blocks
            .exactly_one()
            .expect("Expected exactly one for-loop initialization block")
    }

    /// Sets unconditional edge and matches jump
    #[inline]
    fn set_unconditional_edge_and_match(&mut self, from: NodeIndex, to: Option<NodeIndex>) {
        if let Some(target) = to {
            self.function.set_edges(
                from,
                vec![(target, BlockEdge::new(BranchType::Unconditional))],
            );
        } else {
            self.function.remove_edges(from);
        }
        self.match_jump(from, to);
    }

    /// Creates a numeric or generic for-loop statement from init and next blocks
    fn create_for_statement(
        &mut self,
        statement: ast::Statement,
        init_block: NodeIndex,
        init_index: usize,
        body_ast: ast::Block,
    ) -> ast::Statement {
        let init_ast = self.function.block_mut(init_block).unwrap();
        
        match statement {
            ast::Statement::NumForNext(num_for_next) => {
                let for_init = init_ast.remove(init_index).into_num_for_init().unwrap();
                ast::NumericFor::new(
                    for_init.counter.1,
                    for_init.limit.1,
                    for_init.step.1,
                    num_for_next.counter.0.as_local().unwrap().clone(),
                    body_ast,
                )
                .into()
            }
            ast::Statement::GenericForNext(generic_for_next) => {
                let for_init = init_ast.remove(init_index).into_generic_for_init().unwrap();
                ast::GenericFor::new(
                    generic_for_next
                        .res_locals
                        .iter()
                        .map(|l| l.as_local().unwrap().clone())
                        .collect(),
                    for_init.0.right,
                    body_ast,
                )
                .into()
            }
            _ => unreachable!("Expected NumForNext or GenericForNext statement"),
        }
    }

    /// Handles for-loop collapsing when the header is not a loop header
    fn collapse_for_non_header(
        &mut self,
        header: NodeIndex,
    ) -> bool {
        if !self.is_for_next(header) {
            return false;
        }

        // Handle Luau's for-loop quirk: https://github.com/luau-lang/luau/issues/679
        let (then_node, else_node) = self
            .function
            .conditional_edges(header)
            .unwrap()
            .map(|e| e.target());

        let then_successors: Vec<_> = self.function.successor_blocks(then_node).collect();

        if then_successors.len() > 1 {
            return false;
        }

        let (init_block, init_index) = self.find_for_init(header);
        
        if then_node != else_node && self.function.predecessor_blocks(then_node).count() != 1 {
            return false;
        }

        let else_successors: Vec<_> = self.function.successor_blocks(else_node).collect();
        
        // Validate loop structure
        let valid_structure = (!then_successors.is_empty() && then_successors[0] == else_node)
            || (else_successors.len() == 1 && then_successors[0] == else_successors[0])
            || (then_successors[0] == header && else_node == init_block);

        if !valid_structure {
            return false;
        }

        let statement = self.function.block_mut(header).unwrap().pop().unwrap();
        let statements = std::mem::take(&mut self.function.block_mut(header).unwrap().0);

        let body_ast = if then_node == init_block {
            vec![ast::Break {}.into()].into()
        } else {
            let mut body_ast = self.function.remove_block(then_node).unwrap();
            body_ast.extend(statements.iter().cloned());
            if !matches!(body_ast.last(), Some(ast::Statement::Return(_))) {
                body_ast.push(ast::Break {}.into());
            }
            body_ast
        };

        // Get statements before borrowing init_ast
        let init_ast = self.function.block_mut(init_block).unwrap();
        init_ast.extend(statements);
        
        // Drop the borrow before calling create_for_statement
        drop(init_ast);
        
        let new_stat = self.create_for_statement(statement, init_block, init_index, body_ast);
        
        // Re-borrow to push the new statement
        self.function.block_mut(init_block).unwrap().push(new_stat);
        
        self.function.remove_block(header);
        self.set_unconditional_edge_and_match(init_block, Some(else_node));
        
        true
    }

    /// Handles self-looping headers (while/repeat/for loops that jump to themselves)
    fn collapse_self_loop(&mut self, header: NodeIndex) -> bool {
        let successors: Vec<_> = self.function.successor_blocks(header).collect();
        
        if !self.is_for_next(header) {
            return self.collapse_while_or_repeat(header, &successors);
        }
        
        self.collapse_for_self_loop(header, &successors)
    }

    /// Handles while/repeat loop collapsing for self-loops
    fn collapse_while_or_repeat(&mut self, header: NodeIndex, successors: &[NodeIndex]) -> bool {
        if successors.len() == 2 {
            let if_stat = self
                .function
                .block_mut(header)
                .unwrap()
                .pop()
                .unwrap()
                .into_if()
                .unwrap();
            
            let mut condition = if_stat.condition;
            let (then_edge, else_edge) = self.function.conditional_edges(header).unwrap();
            
            let next = if then_edge.target() == header {
                condition = ast::Unary::new(condition, ast::UnaryOperation::Not).reduce_condition();
                else_edge.target()
            } else {
                then_edge.target()
            };
            
            let header_block = self.function.block_mut(header).unwrap();
            *header_block = if header_block.is_empty() {
                vec![ast::While::new(
                    ast::Unary::new(condition, ast::UnaryOperation::Not).reduce_condition(),
                    header_block.clone(),
                )
                .into()]
                .into()
            } else {
                vec![ast::Repeat::new(condition, header_block.clone()).into()].into()
            };
            
            self.set_unconditional_edge_and_match(header, Some(next));
        } else {
            let header_block = self.function.block_mut(header).unwrap();
            *header_block = vec![ast::While::new(
                ast::Literal::Boolean(true).into(),
                header_block.clone(),
            )
            .into()]
            .into();
            
            self.set_unconditional_edge_and_match(header, None);
        }
        
        true
    }

    /// Handles for-loop collapsing when it's a self-loop
    fn collapse_for_self_loop(&mut self, header: NodeIndex, successors: &[NodeIndex]) -> bool {
        let next = match successors.len() {
            1 => None,
            2 => {
                let (then_edge, else_edge) = self.function.conditional_edges(header).unwrap();
                assert!(then_edge.target() == header, "Expected then edge to point to header");
                Some(else_edge.target())
            }
            _ => unreachable!("Expected 1 or 2 successors for for-loop header"),
        };

        let statement = self.function.block_mut(header).unwrap().pop().unwrap();
        let statements = std::mem::take(&mut self.function.block_mut(header).unwrap().0);

        let (init_block, init_index) = self.find_for_init(header);

        let body_ast: ast::Block = statements.to_vec().into();
        
        // Extend init_ast with statements
        let init_ast = self.function.block_mut(init_block).unwrap();
        init_ast.extend(statements);
        
        // Drop the borrow before calling create_for_statement
        drop(init_ast);
        
        let new_stat = self.create_for_statement(statement, init_block, init_index, body_ast);
        
        // Re-borrow to push the new statement
        self.function.block_mut(init_block).unwrap().push(new_stat);
        
        self.function.remove_block(header);
        self.set_unconditional_edge_and_match(init_block, next);
        
        true
    }

    /// Handles standard loop patterns (while loops with separate body blocks)
    fn collapse_standard_loop(
        &mut self,
        header: NodeIndex,
        successors: &[NodeIndex],
        dominators: &Dominators<NodeIndex>,
        post_dom: &Dominators<NodeIndex>,
    ) -> bool {
        let (mut next, mut body) = (successors[0], successors[1]);
        
        if post_dom.immediate_dominator(header) == Some(body) {
            std::mem::swap(&mut next, &mut body);
        }
        
        assert_ne!(body, header, "Body should not be the header itself");

        // Ensure body has only one non-self predecessor
        if self
            .function
            .predecessor_blocks(body)
            .filter(|&p| p != body)
            .count()
            != 1
        {
            std::mem::swap(&mut next, &mut body);
            if self
                .function
                .predecessor_blocks(body)
                .filter(|&p| p != body)
                .count()
                != 1
            {
                return false;
            }
        }

        let continues: Vec<_> = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != header)
            .filter(|&n| {
                dominators
                    .dominators(n)
                    .map_or(false, |mut x| x.contains(&header))
            })
            .collect();

        let mut changed = false;

        // Find common post-dominator for loop exit refinement
        let common_post_doms = post_dom
            .dominators(body)
            .map(|d| d.collect_vec())
            .unwrap_or_default()
            .intersect(
                post_dom
                    .dominators(next)
                    .map(|d| d.collect_vec())
                    .unwrap_or_default(),
            );

        // Refine loop exit if needed
        if !self.is_for_next(header) {
            if let Some(new_next) = common_post_doms.into_iter().find(|&p| {
                self.function.has_block(p)
                    && continues
                        .iter()
                        .all(|&n| post_dom.dominators(n).unwrap().contains(&p))
            }) {
                if new_next != next {
                    next = new_next;
                    let condition_block = self.function.new_block();
                    body = condition_block;
                    
                    let mut new_header_block = ast::Block::default();
                    new_header_block.push(
                        ast::If::new(
                            ast::Literal::Boolean(true).into(),
                            ast::Block::default(),
                            ast::Block::default(),
                        )
                        .into(),
                    );
                    
                    *self.function.block_mut(condition_block).unwrap() =
                        std::mem::replace(self.function.block_mut(header).unwrap(), new_header_block);
                    
                    let edges = self.function.remove_edges(header);
                    self.function.set_edges(condition_block, edges);
                    self.function.set_edges(
                        header,
                        vec![
                            (body, BlockEdge::new(BranchType::Then)),
                            (next, BlockEdge::new(BranchType::Else)),
                        ],
                    );
                    changed = true;
                }
            }
        }

        let breaks: Vec<_> = self
            .function
            .predecessor_blocks(next)
            .filter(|&n| n != header)
            .filter(|&n| dominators.dominators(n).unwrap().contains(&body))
            .collect();

        // Check for invalid loop structure
        if self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != header)
            .any(|n| {
                !dominators.dominators(n).is_some_and(|mut d| d.contains(&body))
                    && dominators.dominators(n).is_some_and(|mut d| d.contains(&header))
                    && dominators.dominators(n).is_some_and(|mut d| d.contains(&next))
            })
            && self.function.successor_blocks(body).exactly_one().ok() != Some(header)
        {
            return changed;
        }

        let next = if self.function.successor_blocks(body).exactly_one().ok() == Some(header)
            || post_dom.dominators(header).is_some_and(|mut p| p.contains(&next))
        {
            Some(next)
        } else {
            None
        };

        // Refine virtual edges for breaks and continues
        for node in breaks.into_iter().chain(continues).collect::<FxHashSet<_>>() {
            if let Some((then_edge, else_edge)) = self.function.conditional_edges(node) {
                changed |= self.refine_virtual_edge_conditional(
                    post_dom,
                    node,
                    then_edge.target(),
                    else_edge.target(),
                    header,
                    next,
                );
            } else if let Some(edge) = self.function.unconditional_edge(node) {
                changed |= self.refine_virtual_edge_jump(post_dom, node, edge.target(), header, next);
            }
        }

        // Convert to while or for loop
        if self.function.successor_blocks(body).exactly_one().ok() == Some(header) {
            if let Some(next) = next {
                changed |= self.finalize_loop_conversion(header, body, next);
            }
        }

        changed
    }

    /// Finalizes the conversion of a loop structure into a while/for loop
    fn finalize_loop_conversion(
        &mut self,
        header: NodeIndex,
        body: NodeIndex,
        next: NodeIndex,
    ) -> bool {
        let statement = self.function.block_mut(header).unwrap().pop().unwrap();

        if let ast::Statement::If(if_stat) = statement {
            let mut if_condition = if_stat.condition;
            let header_else_target = self.function.conditional_edges(header).unwrap().1.target();
            let block = self.function.remove_block(body).unwrap();

            let while_stat = if !self.function.block_mut(header).unwrap().is_empty() {
                let mut body_block = std::mem::take(self.function.block_mut(header).unwrap());
                
                if header_else_target != body {
                    if_condition = ast::Unary::new(if_condition, ast::UnaryOperation::Not)
                        .reduce_condition();
                }
                
                body_block.push(
                    ast::If::new(
                        if_condition,
                        vec![ast::Break {}.into()].into(),
                        ast::Block::default(),
                    )
                    .into(),
                );
                body_block.extend(block.0);

                ast::While::new(ast::Literal::Boolean(true).into(), body_block)
            } else {
                if header_else_target == body {
                    if_condition = ast::Unary::new(if_condition, ast::UnaryOperation::Not)
                        .reduce_condition();
                }

                ast::While::new(if_condition, block)
            };

            self.function.block_mut(header).unwrap().push(while_stat.into());
            self.set_unconditional_edge_and_match(header, Some(next));
            true
        } else {
            // Handle for-loop conversion
            let statements = std::mem::take(&mut self.function.block_mut(header).unwrap().0);
            let (init_block, init_index) = self.find_for_init(header);

            let mut body_ast = self.function.remove_block(body).unwrap();
            body_ast.extend(statements.iter().cloned());
            
            // Extend init_ast with statements
            let init_ast = self.function.block_mut(init_block).unwrap();
            init_ast.extend(statements);
            
            // Drop the borrow before calling create_for_statement
            drop(init_ast);
            
            let new_stat = self.create_for_statement(statement, init_block, init_index, body_ast);
            
            // Re-borrow to push the new statement
            self.function.block_mut(init_block).unwrap().push(new_stat);
            
            self.function.remove_block(header);
            self.set_unconditional_edge_and_match(init_block, Some(next));
            true
        }
    }

    /// Handles single-successor infinite loops
    fn collapse_infinite_loop(&mut self, header: NodeIndex, body: NodeIndex) -> bool {
        if !self
            .function
            .successor_blocks(body)
            .exactly_one()
            .is_ok_and(|s| s == header)
        {
            return false;
        }

        let block = self.function.remove_block(body).unwrap();
        let mut body_block = std::mem::take(self.function.block_mut(header).unwrap());
        body_block.extend(block.0);

        self.function
            .block_mut(header)
            .unwrap()
            .push(ast::While::new(ast::Literal::Boolean(true).into(), body_block).into());
        
        self.function.set_edges(header, Vec::new());
        true
    }

    /// Main entry point for loop collapsing
    /// Attempts to identify and collapse various loop patterns into high-level constructs
    pub(crate) fn try_collapse_loop(
        &mut self,
        header: NodeIndex,
        dominators: &Dominators<NodeIndex>,
        post_dom: &Dominators<NodeIndex>,
    ) -> bool {
        // Handle for-loops that aren't marked as loop headers
        if !self.is_loop_header(header) {
            return self.collapse_for_non_header(header);
        }

        let successors: Vec<_> = self.function.successor_blocks(header).collect();
        
        // Self-looping header (while/repeat/for with continue)
        if successors.contains(&header) {
            return self.collapse_self_loop(header);
        }
        
        // Standard two-successor loop pattern
        if successors.len() == 2 {
            return self.collapse_standard_loop(header, &successors, dominators, post_dom);
        }
        
        // Single-successor infinite loop
        if let Ok(&body) = successors.iter().exactly_one() {
            return self.collapse_infinite_loop(header, body);
        }

        false
    }
}
