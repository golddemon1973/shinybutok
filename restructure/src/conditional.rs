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
    /// Helpers -------------------------------------------------------
    #[inline]
    fn continue_block() -> Arc<Mutex<ast::Block>> {
        Arc::new(Mutex::new(vec![ast::Continue {}.into()].into()))
    }

    #[inline]
    fn break_block() -> Arc<Mutex<ast::Block>> {
        Arc::new(Mutex::new(vec![ast::Break {}.into()].into()))
    }

    #[inline]
    fn invert_condition_unary(if_stat: &mut ast::If) {
        if_stat.condition =
            ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                .reduce_condition();
    }

    /// simplify `if` that starts with `not` by inverting and swapping branches.
    fn simplify_if(if_stat: &mut ast::If) {
        if let Some(unary) = if_stat.condition.as_unary() {
            if unary.operation == ast::UnaryOperation::Not {
                if_stat.condition = *unary.value.clone();
                std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
            }
        }
    }

    /// If both branches end with returns, attempt to "expand" the if:
    /// - if both returns are empty returns -> remove last statements and return None
    /// - if only one branch returns values -> return the other block to be appended after the if
    /// - if both return values -> choose the longer block (or none if equal)
   fn expand_if(if_stat: &mut ast::If) -> Option<ast::Block> {
    let mut then_block = if_stat.then_block.lock();
    let mut else_block = if_stat.else_block.lock();

    let then_return = then_block.last().and_then(|s| s.as_return());
    let else_return = else_block.last().and_then(|s| s.as_return());

    match (then_return, else_return) {
        (Some(then_r), Some(else_r)) => {
            let then_empty = then_r.values.is_empty();
            let else_empty = else_r.values.is_empty();

            match (then_empty, else_empty) {
                (true, true) => {
                    then_block.pop();
                    else_block.pop();
                    None
                }
                (false, true) => {
                    // Return else branch to append after if
                    Some(std::mem::take(&mut else_block))
                }
                (true, false) => {
                    // Swap, invert condition, return previous then
                    let prev_then = std::mem::take(&mut then_block);
                    then_block.extend(std::mem::take(&mut else_block));
                    Self::invert_condition_unary(if_stat);
                    Some(prev_then)
                }
                (false, false) => {
                    match then_block.len().cmp(&else_block.len()) {
                        std::cmp::Ordering::Less => Some(std::mem::take(&mut else_block)),
                        std::cmp::Ordering::Greater => {
                            let prev_then = std::mem::take(&mut then_block);
                            then_block.extend(std::mem::take(&mut else_block));
                            Self::invert_condition_unary(if_stat);
                            Some(prev_then)
                        }
                        std::cmp::Ordering::Equal => None,
                    }
                }
            }
        }
        _ => None,
    }
}
    // a -> b -> d + a -> c -> d  => a -> d
    fn match_diamond_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let mut then_successors = self.function.successor_blocks(then_node).collect_vec();
        let mut else_successors = self.function.successor_blocks(else_node).collect_vec();

        // if either side has multiple successors, only allow if we're dealing with a loop header
        // and the only extra successor is the loop back edge to `entry`.
        if then_successors.len() > 1 || else_successors.len() > 1 {
            if self.is_loop_header(entry) {
                // try to remove potential back-edge to `entry` from each successor list
                let then_has_back = if let Some(pos) = then_successors.iter().position(|&n| n == entry) {
                    then_successors.swap_remove(pos);
                    true
                } else {
                    false
                };
                let else_has_back = if let Some(pos) = else_successors.iter().position(|&n| n == entry) {
                    else_successors.swap_remove(pos);
                    true
                } else {
                    false
                };

                // after removing back edges, both sides must have exactly one successor and match
                if ((!then_has_back && then_successors.len() != 1) || (!else_has_back && else_successors.len() != 1))
                {
                    return false;
                }
                if then_successors != else_successors {
                    return false;
                }

                // refine: we need to turn the branch that goes to `entry` into a `continue` in its if block
                let mut refine = |n: NodeIndex| -> bool {
                    let edges = match self.function.conditional_edges(n) {
                        Some(e) => e,
                        None => return false,
                    };
                    let (then_target, else_target) = edges.map(|e| e.target());
                    let block = match self.function.block_mut(n) {
                        Some(b) => b,
                        None => return false,
                    };
                    if let Some(if_stat) = block.last_mut().and_then(|s| s.as_if_mut()) {
                        if then_target == entry {
                            if_stat.then_block = Self::continue_block();
                            true
                        } else if else_target == entry {
                            if_stat.else_block = Self::continue_block();
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                };

                let then_changed = if then_has_back { refine(then_node) } else { false };
                let else_changed = if else_has_back { refine(else_node) } else { false };
                if !then_changed && !else_changed {
                    return false;
                }
                if then_has_back && else_has_back {
                    debug_assert!(then_changed && else_changed);
                }
            } else {
                return false;
            }
        } else if then_successors != else_successors {
            // both have exactly one successor but they must match
            return false;
        }

        // both then/else must have a single predecessor (the entry)
        if self.function.predecessor_blocks(then_node).count() != 1
            || self.function.predecessor_blocks(else_node).count() != 1
        {
            return false;
        }

        // remove the then/else nodes and attach their blocks to the if at `entry`
        let then_block = self.function.remove_block(then_node).unwrap();
        let else_block = self.function.remove_block(else_node).unwrap();

        let block = self.function.block_mut(entry).unwrap();
        let if_stat = block.last_mut().unwrap().as_if_mut().unwrap();
        if_stat.then_block = Arc::new(then_block.into());
        if_stat.else_block = Arc::new(else_block.into());
        Self::simplify_if(if_stat);

        // possibly expand and append the trailing block after the if
        let after = Self::expand_if(if_stat);
        if if_stat.then_block.lock().is_empty() {
            // move condition and swap branches (keep semantics)
            Self::invert_condition_unary(if_stat);
            std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
        }
        if let Some(after_block) = after {
            block.extend(after_block.0);
        }

        // update edges from entry: either to the single exit or remove edges if none
        let exit = then_successors.first().cloned();
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

    // a -> b -> c + a -> c => a -> c
    fn match_triangle_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let try_match = |src: NodeIndex, target: NodeIndex, invert: bool, s: &mut Self| {
            let succs = s.function.successor_blocks(src).collect_vec();

            if succs.len() > 1 {
                return false;
            }

            if s.function.predecessor_blocks(src).count() != 1 {
                return false;
            }

            if !succs.is_empty() && succs[0] != target {
                return false;
            }

            let removed_block = s.function.remove_block(src).unwrap();
            let block = s.function.block_mut(entry).unwrap();
            let if_stat = block.last_mut().unwrap().as_if_mut().unwrap();
            if_stat.then_block = Arc::new(removed_block.into());

            if invert {
                if_stat.condition =
                    ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                        .reduce_condition();
            }

            s.function.set_edges(entry, vec![(target, BlockEdge::new(BranchType::Unconditional))]);
            s.match_jump(entry, Some(target));
            true
        };

        try_match(then_node, else_node, false, self) || try_match(else_node, then_node, true, self)
    }

    // refine virtual edge that is a jump (loop / break/continue)
    pub(crate) fn refine_virtual_edge_jump(
        &mut self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        node: NodeIndex,
        header: NodeIndex,
        next: Option<NodeIndex>,
    ) -> bool {
        if node == header {
            // check whether there's a predecessor (other than entry) dominated by `entry` in postdominator tree
            if !self
                .function
                .predecessor_blocks(header)
                .filter(|&n| n != entry)
                .any(|n| {
                    post_dom
                        .dominators(entry)
                        .is_some_and(|mut p| p.contains(&n))
                })
            {
                return false;
            }
            let block = &mut self.function.block_mut(entry).unwrap();
            block.push(ast::Continue {}.into());
        } else if Some(node) == next {
            let block = &mut self.function.block_mut(entry).unwrap();
            block.push(ast::Break {}.into());
        }
        self.function.set_edges(entry, vec![]);
        true
    }

    // refine virtual edges for conditionals (turn them into continue/break or set edges)
    pub(crate) fn refine_virtual_edge_conditional(
        &mut self,
        post_dom: &Dominators<NodeIndex>,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        header: NodeIndex,
        next: Option<NodeIndex>,
    ) -> bool {
        let then_main_cont = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(then_node)
                    .is_some_and(|mut p| p.contains(&n))
            });

        let else_main_cont = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(else_node)
                    .is_some_and(|mut p| p.contains(&n))
            });

        let mut changed = false;
        let header_successors = self.function.successor_blocks(header).collect_vec();
        let block = self.function.block_mut(entry).unwrap();

        if let Some(if_stat) = block.last_mut().unwrap().as_if_mut() {
            if then_node == header && !header_successors.contains(&entry) && then_main_cont {
                if_stat.then_block = Self::continue_block();
                changed = true;
            } else if Some(then_node) == next {
                if_stat.then_block = Self::break_block();
                changed = true;
            }

            if else_node == header && !header_successors.contains(&entry) && else_main_cont {
                if_stat.else_block = Self::continue_block();
                changed = true;
            } else if Some(else_node) == next {
                if_stat.else_block = Self::break_block();
                changed = true;
            }

            // decide edges based on which branches are empty
            if !if_stat.then_block.lock().is_empty() && if_stat.else_block.lock().is_empty() {
                self.function.set_edges(
                    entry,
                    vec![(else_node, BlockEdge::new(BranchType::Unconditional))],
                );
                changed = true;
            } else if if_stat.then_block.lock().is_empty() && !if_stat.else_block.lock().is_empty() {
                Self::invert_condition_unary(if_stat);
                std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
                self.function.set_edges(
                    entry,
                    vec![(then_node, BlockEdge::new(BranchType::Unconditional))],
                );
                changed = true;
            } else if !if_stat.then_block.lock().is_empty() && !if_stat.else_block.lock().is_empty() {
                self.function.remove_edges(entry);
                changed = true;
            }
        }

        changed
    }

    pub(crate) fn match_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let block = self.function.block_mut(entry).unwrap();
        if block.last_mut().unwrap().as_if_mut().is_none() {
            // might be part of a for loop or other construct where last is not an if
            return false;
        }

        self.match_diamond_conditional(entry, then_node, else_node)
            || self.match_triangle_conditional(entry, then_node, else_node)
    }
}
