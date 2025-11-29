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
    #[inline]
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
    /// 
    /// This helps prevent unnecessary gotos by pulling out common trailing code.
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
            (false, true) => Some(std::mem::take(&mut *else_block)),
            // Only else has values - swap and extract
            (true, false) => {
                let extracted = std::mem::replace(&mut *then_block, std::mem::take(&mut *else_block));
                if_stat.condition = ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                    .reduce_condition();
                Some(extracted)
            }
            // Both have values - extract the longer block to minimize nesting
            (false, false) => {
                match then_block.len().cmp(&else_block.len()) {
                    std::cmp::Ordering::Less => Some(std::mem::take(&mut *else_block)),
                    std::cmp::Ordering::Greater => {
                        let extracted = std::mem::replace(&mut *then_block, std::mem::take(&mut *else_block));
                        if_stat.condition = ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                            .reduce_condition();
                        Some(extracted)
                    }
                    std::cmp::Ordering::Equal => None,
                }
            }
        }
    }

    /// Checks if a block ends with a terminal statement (return/break/continue).
    #[inline]
    fn block_is_terminal(block: &ast::Block) -> bool {
        block.last().map_or(false, |s| {
            matches!(
                s,
                ast::Statement::Return(_) | ast::Statement::Break(_) | ast::Statement::Continue(_)
            )
        })
    }

    /// Checks if both branches of an if statement are terminal.
    fn if_branches_are_terminal(if_stat: &ast::If) -> bool {
        let then_terminal = Self::block_is_terminal(&if_stat.then_block.lock());
        let else_terminal = Self::block_is_terminal(&if_stat.else_block.lock());
        then_terminal && else_terminal
    }

    /// Matches a diamond-shaped conditional pattern: a -> b -> d + a -> c -> d
    /// Results in: a -> d with merged blocks
    fn match_diamond_conditional(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
    ) -> bool {
        let mut then_successors: Vec<_> = self.function.successor_blocks(then_node).collect();
        let mut else_successors: Vec<_> = self.function.successor_blocks(else_node).collect();

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

        self.merge_diamond_blocks(entry, then_node, else_node, then_successors.first().copied())
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
        (then_successors.len() == 1 || then_has_back_edge)
            && (else_successors.len() == 1 || else_has_back_edge)
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
            let Some((then_target, else_target)) = self
                .function
                .conditional_edges(node)
                .map(|(t, e)| (t.target(), e.target())) else {
                return false;
            };

            let block = self.function.block_mut(node).unwrap();
            let Some(if_stat) = block.last_mut().and_then(|s| s.as_if_mut()) else {
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

        then_changed || else_changed
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
        let if_stat = block.last_mut().and_then(|s| s.as_if_mut()).unwrap();
        
        if_stat.then_block = Arc::new(Mutex::new(then_block));
        if_stat.else_block = Arc::new(Mutex::new(else_block));
        
        Self::simplify_if(if_stat);

        let after = Self::expand_if(if_stat);
        
        // Normalize: ensure then_block is non-empty if possible
        if if_stat.then_block.lock().is_empty() && !if_stat.else_block.lock().is_empty() {
            if_stat.condition = ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                .reduce_condition();
            std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
        }

        // CRITICAL FIX: Check if both branches terminate
        // If they do, we shouldn't try to connect to the exit node
        let both_branches_terminal = Self::if_branches_are_terminal(if_stat);

        if let Some(after) = after {
            block.extend(after.0);
        }

        // Only set edges if branches don't both terminate
        if let Some(exit) = exit {
            if !both_branches_terminal {
                self.function.set_edges(
                    entry,
                    vec![(exit, BlockEdge::new(BranchType::Unconditional))],
                );
                self.match_jump(entry, Some(exit));
            } else {
                // Both branches terminate - no need for an exit edge
                self.function.remove_edges(entry);
            }
        } else {
            self.function.remove_edges(entry);
        }

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
        let branch_successors: Vec<_> = self.function.successor_blocks(branch_node).collect();

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
        let branch_is_terminal = Self::block_is_terminal(&branch_block);

        let block = self.function.block_mut(entry).unwrap();
        let if_stat = block.last_mut().and_then(|s| s.as_if_mut()).unwrap();
        if_stat.then_block = Arc::new(Mutex::new(branch_block));

        if invert_condition {
            if_stat.condition = ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                .reduce_condition();
        }

        // CRITICAL FIX: If the branch terminates (return/break/continue),
        // don't create an edge to the direct node
        if branch_is_terminal {
            self.function.remove_edges(entry);
        } else {
            self.function.set_edges(
                entry,
                vec![(direct_node, BlockEdge::new(BranchType::Unconditional))],
            );
            self.match_jump(entry, Some(direct_node));
        }

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
        self.function.set_edges(entry, Vec::new());
        
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
                    .map_or(false, |mut p| p.contains(&n))
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

        let header_successors: Vec<_> = self.function.successor_blocks(header).collect();
        
        // First pass: modify the if statement blocks
        let (then_empty, else_empty, both_terminal) = {
            let block = self.function.block_mut(entry).unwrap();
            
            let Some(if_stat) = block.last_mut().and_then(|s| s.as_if_mut()) else {
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

            // Check properties before releasing the borrow
            let then_empty = if_stat.then_block.lock().is_empty();
            let else_empty = if_stat.else_block.lock().is_empty();
            let both_terminal = Self::if_branches_are_terminal(if_stat);
            
            (then_empty, else_empty, both_terminal)
        };

        // Second pass: normalize edges based on branch properties
        let edge_changed = self.normalize_conditional_edges(
            entry, 
            then_node, 
            else_node, 
            then_empty, 
            else_empty,
            both_terminal,
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
                    .map_or(false, |mut p| p.contains(&n))
            });

        let else_is_continue = self
            .function
            .predecessor_blocks(header)
            .filter(|&n| n != entry)
            .any(|n| {
                post_dom
                    .dominators(else_node)
                    .map_or(false, |mut p| p.contains(&n))
            });

        (then_is_continue, else_is_continue)
    }

    /// Normalizes conditional edges based on branch properties.
    fn normalize_conditional_edges(
        &mut self,
        entry: NodeIndex,
        then_node: NodeIndex,
        else_node: NodeIndex,
        then_empty: bool,
        else_empty: bool,
        both_terminal: bool,
    ) -> bool {
        // CRITICAL FIX: If both branches are terminal, remove all edges
        if both_terminal {
            self.function.remove_edges(entry);
            return true;
        }

        match (then_empty, else_empty) {
            // Only else has content - swap and use else node
            (true, false) => {
                let block = self.function.block_mut(entry).unwrap();
                let if_stat = block.last_mut().and_then(|s| s.as_if_mut()).unwrap();
                if_stat.condition = ast::Unary::new(if_stat.condition.clone(), ast::UnaryOperation::Not)
                    .reduce_condition();
                std::mem::swap(&mut if_stat.then_block, &mut if_stat.else_block);
                drop(block);
                
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
            // Both have content - remove edges (both branches handle their own flow)
            (false, false) => {
                self.function.remove_edges(entry);
                true
            }
            // Both empty - no change needed
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
        // Verify this is actually an if statement
        {
            let block = self.function.block(entry).unwrap();
            if block.last().and_then(|s| s.as_if()).is_none() {
                return false;
            }
        }

        // Try to match known patterns
        self.match_diamond_conditional(entry, then_node, else_node)
            || self.match_triangle_conditional(entry, then_node, else_node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_block_is_terminal_with_return() {
        let mut block = ast::Block::default();
        block.push(ast::Return { values: vec![] }.into());
        assert!(GraphStructurer::block_is_terminal(&block));
    }

    #[test]
    fn test_block_is_terminal_with_break() {
        let mut block = ast::Block::default();
        block.push(ast::Break {}.into());
        assert!(GraphStructurer::block_is_terminal(&block));
    }

    #[test]
    fn test_block_not_terminal() {
        let block = ast::Block::default();
        assert!(!GraphStructurer::block_is_terminal(&block));
    }
}
