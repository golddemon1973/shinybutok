use ast::SideEffects;
use cfg::block::{BlockEdge, BranchType};
use itertools::Itertools;
use petgraph::{
    algo::dominators::Dominators,
    stable_graph::NodeIndex,
    visit::{EdgeRef, IntoEdgeReferences},
    Direction,
};

impl super::GraphStructurer {
    /// Removes unnecessary conditional statements where both branches lead to the same target
    /// 
    /// If a conditional has side effects (calls, method calls), preserves them as statements.
    /// Otherwise, the condition is discarded entirely.
    pub(crate) fn remove_redundant_condition(&mut self, node: NodeIndex) -> bool {
        let block = self.function.block(node).unwrap();
        
        if block.is_empty() {
            return false;
        }

        let Some(if_stmt) = block.last().and_then(|s| s.as_if()) else {
            return false;
        };

        let Some((then_edge, else_edge)) = self.function.conditional_edges(node) else {
            return false;
        };

        // Both branches must lead to the same target
        if then_edge.target() != else_edge.target() {
            return false;
        }

        let target = then_edge.target();
        let cond = self
            .function
            .block_mut(node)
            .unwrap()
            .pop()
            .unwrap()
            .into_if()
            .unwrap()
            .condition;

        // Preserve side effects from the condition
        let new_stat = self.extract_side_effects_from_condition(cond);
        
        if let Some(stat) = new_stat {
            self.function.block_mut(node).unwrap().push(stat);
        }

        self.function.set_edges(
            node,
            vec![(target, BlockEdge::new(BranchType::Unconditional))],
        );
        
        true
    }

    /// Extracts side effects from a condition into a statement
    /// 
    /// Returns None if the condition has no side effects
    fn extract_side_effects_from_condition(&self, cond: ast::RValue) -> Option<ast::Statement> {
        match cond {
            ast::RValue::Call(call) => Some(call.into()),
            ast::RValue::MethodCall(method_call) => Some(method_call.into()),
            cond if cond.has_side_effects() => Some(
                ast::Assign {
                    left: vec![ast::RcLocal::default().into()],
                    right: vec![cond],
                    prefix: true,
                    parallel: false,
                }
                .into(),
            ),
            _ => None,
        }
    }

    /// Redirects all incoming edges from `from_node` to `to_node`
    /// 
    /// Also attempts to remove unnecessary conditions on source nodes
    fn redirect_incoming_edges(&mut self, from_node: NodeIndex, to_node: NodeIndex) {
        let incoming_edges: Vec<_> = self
            .function
            .graph()
            .edges_directed(from_node, Direction::Incoming)
            .map(|e| (e.source(), e.id()))
            .collect();

        for (source, edge_id) in incoming_edges {
            let edge = self.function.graph_mut().remove_edge(edge_id).unwrap();
            self.function.graph_mut().add_edge(source, to_node, edge);
            self.remove_redundant_condition(source);
        }
    }

    /// Checks if a block can be safely bypassed (removed with edges redirected)
    fn can_bypass_block(&self, node: NodeIndex) -> bool {
        Self::block_is_no_op(self.function.block(node).unwrap())
            && self.function.entry() != &Some(node)
            && !self.is_loop_header(node)
    }

    /// Checks if a block can be merged into its predecessor
    fn can_merge_into_predecessor(&self, node: NodeIndex, target: NodeIndex) -> bool {
        self.function.predecessor_blocks(target).count() == 1
            && !self.has_circular_edge(node, target)
            && !self.has_circular_edge(target, target)
    }

    /// Checks if there's a circular edge (self-loop or back-edge) involving the nodes
    #[inline]
    fn has_circular_edge(&self, from: NodeIndex, to: NodeIndex) -> bool {
        self.function.edges_to_block(from).any(|(t, _)| t == to)
    }

    /// Attempts to bypass a no-op block by redirecting edges
    fn try_bypass_no_op_block(&mut self, node: NodeIndex) -> bool {
        if !self.can_bypass_block(node) {
            return false;
        }

        let Some(target) = self.function.successor_blocks(node).exactly_one().ok() else {
            return false;
        };

        if node == target {
            return false;
        }

        self.redirect_incoming_edges(node, target);
        self.function.remove_block(node);
        true
    }

    /// Attempts to merge a target block into the current node
    fn try_merge_target_into_node(&mut self, node: NodeIndex, target: NodeIndex) -> bool {
        if !self.can_merge_into_predecessor(node, target) {
            return false;
        }

        // Can't merge if target is entry, loop header, or for-next block
        if self.function.entry() == &Some(target)
            || self.is_loop_header(target)
            || self.is_for_next(target)
        {
            return false;
        }

        let edges = self.function.remove_edges(target);
        let block = self.function.remove_block(target).unwrap();
        self.function.block_mut(node).unwrap().extend(block.0);
        self.function.set_edges(node, edges);
        true
    }

    /// Attempts to merge current node into target (inverse merge)
    fn try_merge_node_into_target(&mut self, node: NodeIndex, target: NodeIndex) -> bool {
        if !self.can_merge_into_predecessor(node, target) {
            return false;
        }

        // Can't merge if node is entry or loop header
        if self.function.entry() == &Some(node) || self.is_loop_header(node) {
            return false;
        }

        self.redirect_incoming_edges(node, target);
        
        let mut block = self.function.remove_block(node).unwrap();
        block.extend(std::mem::take(self.function.block_mut(target).unwrap()).0);
        *self.function.block_mut(target).unwrap() = block;
        true
    }

    /// Attempts to remove a terminating no-op block
    fn try_remove_terminating_block(&mut self, node: NodeIndex) -> bool {
        // Check if block is removable
        if !Self::block_is_no_op(self.function.block(node).unwrap())
            || self.function.entry() == &Some(node)
            || self.is_loop_header(node)
            || self.is_for_next(node)
        {
            return false;
        }

        // All predecessors must have exactly one successor (this node)
        let predecessors: Vec<_> = self.function.predecessor_blocks(node).collect();
        for pred in &predecessors {
            if self.function.successor_blocks(*pred).count() != 1 {
                return false;
            }
        }

        // Remove all incoming edges and the block
        let incoming_edges: Vec<_> = self
            .function
            .graph()
            .edges_directed(node, Direction::Incoming)
            .map(|e| e.id())
            .collect();

        for edge_id in incoming_edges {
            let edge = self.function.graph_mut().remove_edge(edge_id).unwrap();
            assert_eq!(
                edge.branch_type,
                BranchType::Unconditional,
                "Expected unconditional branch to terminating block"
            );
        }

        self.function.remove_block(node);
        true
    }

    /// Main entry point for jump pattern matching
    /// 
    /// Attempts to:
    /// 1. Bypass no-op blocks
    /// 2. Merge blocks with single predecessors
    /// 3. Remove terminating no-op blocks
    pub(crate) fn match_jump(&mut self, node: NodeIndex, target: Option<NodeIndex>) -> bool {
        if let Some(target) = target {
            // Don't process self-loops
            if node == target {
                return false;
            }

            // Don't process for-next blocks (handled separately in loop restructuring)
            if self.is_for_next(node) {
                return false;
            }

            // Ensure we have an unconditional edge
            assert!(
                self.function.unconditional_edge(node).is_some(),
                "Expected unconditional edge for jump matching"
            );

            // Strategy 1: Bypass no-op blocks
            if self.try_bypass_no_op_block(node) {
                return true;
            }

            // Strategy 2: Merge target into node
            if self.try_merge_target_into_node(node, target) {
                return true;
            }

            // Strategy 3: Merge node into target (inverse)
            if self.try_merge_node_into_target(node, target) {
                return true;
            }

            false
        } else {
            // Node is terminating (no successors)
            self.try_remove_terminating_block(node)
        }
    }

    /// Alias for backward compatibility
    /// 
    /// Note: This is the same functionality as in structuring.rs but without block params.
    /// Consider consolidating if both modules need this functionality.
    #[inline]
    pub(crate) fn try_remove_unnecessary_condition(&mut self, node: NodeIndex) -> bool {
        self.remove_redundant_condition(node)
    }
}
