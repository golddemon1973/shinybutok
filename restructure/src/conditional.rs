use ast::Reduce;
use cfg::block::{BlockEdge, BranchType};
use itertools::Itertools;
use parking_lot::Mutex;
use petgraph::visit::EdgeRef;
use triomphe::Arc;
use tuple::Map;

use crate::GraphStructurer;
use petgraph::{algo::dominators::Dominators, stable_graph::NodeIndex};

impl GraphStructurer {
    /// Simplifies an if statement by removing unnecessary negations.
    /// If the condition is a NOT operation, swap then/else blocks and remove the NOT.
    fn simplify_if(if_stat: &mut ast::If) {
        if let Some(unary) = if_stat.condition.as_unary() {
            if unary.operation == ast::UnaryOperation::Not {
                if_stat.condition = *unary.value.clone();
                std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
            }
        }
    }

    /// Expands an if statement by extracting common return patterns.
    /// Returns the block that should be appended after the if statement, if any.
    fn expand_if(if_stat: &mut ast::If) -> Option<ast::Block> {
        let mut then_block = if_stat.then_block.lock();
        let mut else_block = if_stat.else_block.lock();
        
        let then_return = then_block.last().and_then(|x| x.as_return());
        let else_return = else_block.last().and_then(|x| x.as_return());
        
        let (then_return, else_return) = match (then_return, else_return) {
            (Some(t), Some(e)) => (t, e),
            _ => return None,
        };

        let then_empty = then_return.values.is_empty();
        let else_empty = else_return.values.is_empty();

        match (then_empty, else_empty) {
            // Both returns are empty - remove both
            (true, true) => {
                then_block.pop();
                else_block.pop();
                None
            }
            // Only then has values - extract else block
            (false, true) => Some(std::mem::take(&mut else_block)),
            // Only else has values - swap and extract
            (true, false) => {
                let extracted = std::mem::replace(&mut *then_block, std::mem::take(&mut else_block));
                if_stat.condition = Self::negate_condition(&if_stat.condition);
                Some(extracted)
            }
            // Both have values - extract the longer block
            (false, false) => {
                match then_block.len().cmp(&else_block.len()) {
                    std::cmp::Ordering::Less => Some(std::mem::take(&mut else_block)),
                    std::cmp::Ordering::Greater => {
                        let extracted = std::mem::replace(&mut *then_block, std::mem::take(&mut else_block));
                        if_stat.condition = Self::negate_condition(&if_stat.condition);
                        Some(extracted)
                    }
                    std::cmp::Ordering::Equal => None,
                }
            }
        }
    }

    /// Helper to negate a condition and reduce it.
    #[inline]
    fn negate_condition(condition: &ast::Expression) -> ast::Expression {
        ast::Unary::new(condition.clone(), ast::UnaryOperation::Not).reduce_condition()
    }

    /// Matches a diamond-shaped conditional pattern: a -> b -> d + a -> c -> d
    /// Results in: a -> d with merged blocks
    fn match_diamond_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let mut then_successors = self.function.successor_blocks(then_node).collect_vec();
        let mut else_successors = self.function.successor_blocks(else_node).collect_vec();

        // Handle loop headers with back edges
        if then_successors.len() > 1 || else_successors.len() > 1 {
            if !self.is_loop_header(entry) {
                return false;
            }

            let (then_has_back_edge, else_has_back_edge) = 
                self.handle_loop_back_edges(entry, &mut then_successors, &mut else_successors);

            if !self.validate_loop_successors(then_has_back_edge, else_has_back_edge, &then_successors, &else_successors) {
                return false;
            }

            if then_successors != else_successors {
                return false;
            }

            let changed = self.refine_loop_edges(entry, then_node, else_node, then_has_back_edge, else_has_back_edge);
            if !changed {
                return false;
            }
        } else if then_successors != else_successors {
            return false;
        }

        // Ensure single predecessor for both branches
        if self.function.predecessor_blocks(then_node).count() != 1
            || self.function.predecessor_blocks(else_node).count() != 1
        {
            return false;
        }

        self.merge_diamond_blocks(entry, then_node, else_node, then_successors.first().cloned())
    }

    /// Handles removal of back edges to loop headers from successors.
    fn handle_loop_back_edges(
        &self,
        entry: NodeIndex,
        then_successors: &mut Vec<NodeIndex>,
        else_successors: &mut Vec<NodeIndex>,
    ) -> (bool, bool) {
        let then_has_back_edge = if let Some(idx) = then_successors.iter().position(|n| *n == entry) {
            then_successors.swap_remove(idx);
            true
        } else {
            false
        };

        let else_has_back_edge = if let Some(idx) = else_successors.iter().position(|n| *n == entry) {
            else_successors.swap_remove(idx);
            true
        } else {
            false
        };

        (then_has_back_edge, else_has_back_edge)
    }

    /// Validates that successors are valid after removing back edges.
    #[inline]
    fn validate_loop_successors(
        &self,
        then_has_back_edge: bool,
        else_has_back_edge: bool,
        then_successors: &[NodeIndex],
        else_successors: &[NodeIndex],
    ) -> bool {
        (!then_has_back_edge && then_successors.len() == 1 || then_has_back_edge)
            && (!else_has_back_edge && else_successors.len() == 1 || else_has_back_edge)
    }

    /// Refines loop edges by inserting continue statements where appropriate.
    fn refine_loop_edges(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        then_has_back_edge: bool,
        else_has_back_edge: bool,
    ) -> bool {
        let mut refine_node = |node: NodeIndex| -> bool {
            let (then_target, else_target) = self
                .function
                .conditional_edges(node)
                .unwrap()
                .map(|e| e.target());

            let block = self.function.block_mut(node).unwrap();
            let Some(if_stat) = block.last_mut().unwrap().as_if_mut() else {
                return false;
            };

            let mut changed = false;
            if then_target == entry {
                if_stat.then_block = Self::create_continue_block();
                changed = true;
            }
            if else_target == entry {
                if_stat.else_block = Self::create_continue_block();
                changed = true;
            }
            changed
        };

        let then_changed = then_has_back_edge && refine_node(then_node);
        let else_changed = else_has_back_edge && refine_node(else_node);

        if !then_changed && !else_changed {
            return false;
        }

        if then_has_back_edge && else_has_back_edge {
            debug_assert!(then_changed && else_changed, "Both edges should be refined");
        }

        true
    }

    /// Creates a block containing a single continue statement.
    #[inline]
    fn create_continue_block() -> Arc<Mutex<ast::Block>> {
        Arc::new(Mutex::new(vec![ast::Continue {}.into()].into()))
    }

    /// Creates a block containing a single break statement.
    #[inline]
    fn create_break_block() -> Arc<Mutex<ast::Block>> {
        Arc::new(Mutex::new(vec![ast::Break {}.into()].into()))
    }

    /// Merges diamond conditional blocks into the entry block.
    fn merge_diamond_blocks(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        exit: Option<NodeIndex>,
    ) -> bool {
        let then_block = self.function.remove_block(then_node).unwrap();
        let else_block = self.function.remove_block(else_node).unwrap();

        let block = self.function.block_mut(entry).unwrap();
        let if_stat = block.last_mut().unwrap().as_if_mut().unwrap();
        
        if_stat.then_block = Arc::new(then_block.into());
        if_stat.else_block = Arc::new(else_block.into());
        
        Self::simplify_if(if_stat);

        let after = Self::expand_if(if_stat);
        
        // Normalize: ensure then_block is non-empty
        if if_stat.then_block.lock().is_empty() {
            if_stat.condition = Self::negate_condition(&if_stat.condition);
            std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
        }

        if let Some(after) = after {
            block.extend(after.0);
        }

        if let Some(exit) = exit {
            self.function.set_edges(
                entry,
                vec![(exit, BlockEdge::new(BranchType::Unconditional))],
            );
        } else {
            self.function.remove_edges(entry);
        }
        
        self.match_jump(entry, exit);

        true
    }

    /// Matches a triangle-shaped conditional pattern: a -> b -> c + a -> c
    /// Results in: a -> c with merged block
    fn match_triangle_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        self.try_match_triangle(entry, then_node, else_node, false)
            || self.try_match_triangle(entry, else_node, then_node, true)
    }

    /// Attempts to match a triangle pattern with optional inversion.
    fn try_match_triangle(
        &mut self,
        entry: NodeIndex,
        branch_node: NodeIndex,
        direct_node: NodeIndex,
        invert_condition: bool,
    ) -> bool {
        let branch_successors = self.function.successor_blocks(branch_node).collect_vec();

        // Branch node must have at most one successor
        if branch_successors.len() > 1 {
            return false;
        }

        // Branch node must have exactly one predecessor (entry)
        if self.function.predecessor_blocks(branch_node).count() != 1 {
            return false;
        }

        // Branch successor must either be empty or point to direct node
        if !branch_successors.is_empty() && branch_successors[0] != direct_node {
            return false;
        }

        let branch_block = self.function.remove_block(branch_node).unwrap();

        let block = self.function.block_mut(entry).unwrap();
        let if_stat = block.last_mut().unwrap().as_if_mut().unwrap();
        if_stat.then_block = Arc::new(branch_block.into());

        if invert_condition {
            if_stat.condition = Self::negate_condition(&if_stat.condition);
        }

        self.function.set_edges(
            entry,
            vec![(direct_node, BlockEdge::new(BranchType::Unconditional))],
        );

        self.match_jump(entry, Some(direct_node));

        true
    }

    /// Refines virtual edges for jump statements (continue/break).
    pub(crate) fn refine_virtual_edge_jump(
        &mut self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        node: NodeIndex,
        header: NodeIndex,
        next: Option<NodeIndex>,
    ) -> bool {
        let statement = if node == header {
            // Validate that this is a valid back edge
            if !self.validate_back_edge_dominance(post_dom, entry, header) {
                return false;
            }
            ast::Continue {}.into()
        } else if Some(node) == next {
            ast::Break {}.into()
        } else {
            return false;
        };

        let block = self.function.block_mut(entry).unwrap();
        block.push(statement);
        self.function.set_edges(entry, vec![]);
        
        true
    }

    /// Validates that a back edge has proper dominance relationships.
    fn validate_back_edge_dominance(
        &self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        header: NodeIndex,
    ) -> bool {
        self.function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(entry)
                    .is_some_and(|mut p| p.contains(&n))
            })
    }

    /// Refines virtual edges for conditional statements (if with continue/break).
    pub(crate) fn refine_virtual_edge_conditional(
        &mut self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        header: NodeIndex,
        next: Option<NodeIndex>,
    ) -> bool {
        let (then_is_continue, else_is_continue) = 
            self.analyze_branch_continuations(post_dom, entry, then_node, else_node, header);

        let header_successors = self.function.successor_blocks(header).collect_vec();
        
        // First pass: modify the if statement blocks
        let (then_empty, else_empty) = {
            let block = self.function.block_mut(entry).unwrap();
            
            let Some(if_stat) = block.last_mut().unwrap().as_if_mut() else {
                return false;
            };

            let mut changed = false;

            // Handle then branch
            if then_node == header && !header_successors.contains(&entry) && then_is_continue {
                if_stat.then_block = Self::create_continue_block();
                changed = true;
            } else if Some(then_node) == next {
                if_stat.then_block = Self::create_break_block();
                changed = true;
            }

            // Handle else branch
            if else_node == header && !header_successors.contains(&entry) && else_is_continue {
                if_stat.else_block = Self::create_continue_block();
                changed = true;
            } else if Some(else_node) == next {
                if_stat.else_block = Self::create_break_block();
                changed = true;
            }

            if !changed {
                return false;
            }

            // Check emptiness before releasing the borrow
            (if_stat.then_block.lock().is_empty(), if_stat.else_block.lock().is_empty())
        };

        // Second pass: normalize edges based on emptiness (borrow released)
        let edge_changed = self.normalize_conditional_edges_by_emptiness(
            entry, 
            then_node, 
            else_node, 
            then_empty, 
            else_empty
        );

        edge_changed
    }

    /// Analyzes whether branches should be treated as continuations.
    fn analyze_branch_continuations(
        &self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        header: NodeIndex,
    ) -> (bool, bool) {
        let then_is_continue = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(then_node)
                    .is_some_and(|mut p| p.contains(&n))
            });

        let else_is_continue = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(else_node)
                    .is_some_and(|mut p| p.contains(&n))
            });

        (then_is_continue, else_is_continue)
    }

    /// Normalizes conditional edges based on which branches are populated.
    fn normalize_conditional_edges_by_emptiness(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        then_empty: bool,
        else_empty: bool,
    ) -> bool {
        match (then_empty, else_empty) {
            // Only else has content - swap and use else node
            (true, false) => {
                let block = self.function.block_mut(entry).unwrap();
                let if_stat = block.last_mut().unwrap().as_if_mut().unwrap();
                if_stat.condition = Self::negate_condition(&if_stat.condition);
                std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
                drop(block); // Explicitly drop to release borrow
                
                self.function.set_edges(
                    entry,
                    vec![(then_node, BlockEdge::new(BranchType::Unconditional))],
                );
                true
            }
            // Only then has content - use then node
            (false, true) => {
                self.function.set_edges(
                    entry,
                    vec![(else_node, BlockEdge::new(BranchType::Unconditional))],
                );
                true
            }
            // Both have content - remove edges
            (false, false) => {
                self.function.remove_edges(entry);
                true
            }
            // Both empty - no change
            (true, true) => false,
        }
    }

    /// Matches and processes conditional patterns.
    pub(crate) fn match_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let block = self.function.block_mut(entry).unwrap();
        
        // Skip if not an if statement (e.g., for loops)
        if block.last_mut().unwrap().as_if_mut().is_none() {
            return false;
        }

        self.match_diamond_conditional(entry, then_node, else_node)
            || self.match_triangle_conditional(entry, then_node, else_node)
    }
}
