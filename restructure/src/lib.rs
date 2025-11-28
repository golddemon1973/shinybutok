use cfg::{block::BranchType, function::Function};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use petgraph::{
    algo::dominators::{simple_fast, Dominators},
    stable_graph::{EdgeIndex, NodeIndex, StableDiGraph},
    visit::*,
};
use tuple::Map;

mod conditional;
mod jump;
mod r#loop;

/// Computes post-dominators for a control flow graph
/// 
/// Post-dominators are computed by adding a fake exit node connected to all 
/// actual exit nodes, then computing dominators on the reversed graph.
pub fn post_dominators<N: Default, E: Default>(
    graph: &mut StableDiGraph<N, E>,
) -> Dominators<NodeIndex> {
    let exits: Vec<_> = graph
        .node_identifiers()
        .filter(|&n| graph.neighbors(n).next().is_none())
        .collect();
    
    let fake_exit = graph.add_node(Default::default());
    for exit in exits {
        graph.add_edge(exit, fake_exit, Default::default());
    }
    
    let res = simple_fast(Reversed(&*graph), fake_exit);
    assert!(graph.remove_node(fake_exit).is_some(), "Failed to remove fake exit node");
    res
}

/// Main structure for graph-based control flow restructuring
struct GraphStructurer {
    pub function: Function,
    loop_headers: FxHashSet<NodeIndex>,
    label_to_node: FxHashMap<ast::Label, NodeIndex>,
}

impl GraphStructurer {
    /// Identifies loop headers using depth-first search back edges
    fn find_loop_headers(&mut self) {
        self.loop_headers.clear();
        depth_first_search(
            self.function.graph(),
            Some(self.function.entry().unwrap()),
            |event| {
                if let DfsEvent::BackEdge(_, header) = event {
                    self.loop_headers.insert(header);
                }
            },
        );
    }

    /// Creates a new graph structurer from a function
    fn new(function: Function) -> Self {
        let mut this = Self {
            function,
            loop_headers: FxHashSet::default(),
            label_to_node: FxHashMap::default(),
        };
        this.find_loop_headers();
        this
    }

    /// Checks if a block contains only comments (no-op)
    #[inline]
    fn block_is_no_op(block: &ast::Block) -> bool {
        block.iter().all(|s| s.as_comment().is_some())
    }

    /// Attempts to match and collapse various control flow patterns
    fn try_match_pattern(
        &mut self,
        node: NodeIndex,
        dominators: &Dominators<NodeIndex>,
        post_dom: &Dominators<NodeIndex>,
    ) -> bool {
        let successors: Vec<_> = self.function.successor_blocks(node).collect();

        // Try to collapse loops first (highest priority)
        if self.try_collapse_loop(node, dominators, post_dom) {
            self.find_loop_headers();
            return true;
        }

        // Try to remove unnecessary conditions
        if self.try_remove_unnecessary_condition(node) {
            return true;
        }

        // Match based on number of successors
        match successors.len() {
            0 => false,
            1 => self.match_jump(node, Some(successors[0])),
            2 => {
                let (then_target, else_target) = self
                    .function
                    .conditional_edges(node)
                    .unwrap()
                    .map(|e| e.target());
                self.match_conditional(node, then_target, else_target)
            }
            _ => unreachable!("Node should have at most 2 successors"),
        }
    }

    /// Recomputes dominators and post-dominators
    #[inline]
    fn recompute_dominators(&mut self) -> (Dominators<NodeIndex>, Dominators<NodeIndex>) {
        let dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());
        let post_dom = post_dominators(self.function.graph_mut());
        (dominators, post_dom)
    }

    /// Main pattern matching loop - iterates until no more patterns can be matched
    fn match_blocks(&mut self) -> bool {
        // Collect reachable nodes via DFS
        let dfs: FxHashSet<_> = Dfs::new(self.function.graph(), self.function.entry().unwrap())
            .iter(self.function.graph())
            .collect();
        
        let mut dfs_postorder =
            DfsPostOrder::new(self.function.graph(), self.function.entry().unwrap());
        
        let (mut dominators, mut post_dom) = self.recompute_dominators();

        let mut changed = false;
        
        // Process nodes in post-order (bottom-up)
        while let Some(node) = dfs_postorder.next(self.function.graph()) {
            let matched = self.try_match_pattern(node, &dominators, &post_dom);
            if matched {
                (dominators, post_dom) = self.recompute_dominators();
            }
            changed |= matched;
        }

        // Handle unreachable blocks
        let unreachable_nodes: Vec<_> = self
            .function
            .graph()
            .node_indices()
            .filter(|node| !dfs.contains(node))
            .collect();

        for node in unreachable_nodes {
            // Block may have been removed in a previous iteration
            if !self.function.has_block(node) {
                continue;
            }

            if self.function.predecessor_blocks(node).next().is_none() {
                // Keep blocks with labels, remove others
                let has_label = self
                    .function
                    .block(node)
                    .and_then(|b| b.first())
                    .and_then(|s| s.as_label())
                    .is_some();

                if has_label {
                    let matched = self.try_match_pattern(node, &dominators, &post_dom);
                    changed |= matched;
                } else {
                    self.function.remove_block(node);
                }
            }
        }

        changed
    }

    /// Inserts goto statements or merges blocks for an edge
    fn insert_goto_for_edge(&mut self, edge: EdgeIndex) {
        let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
        let edge_weight = self.function.graph().edge_weight(edge).unwrap();
        
        // Try to merge blocks if possible
        if edge_weight.branch_type == BranchType::Unconditional
            && self.function.predecessor_blocks(target).count() == 1
        {
            assert_eq!(
                self.function.successor_blocks(source).count(),
                1,
                "Source should have exactly one successor"
            );
            
            self.merge_blocks(source, target);
        } else {
            self.insert_goto_statement(source, target, edge);
        }
    }

    /// Merges target block into source block
    fn merge_blocks(&mut self, source: NodeIndex, target: NodeIndex) {
        let edges = self.function.remove_edges(target);
        let block = self.function.remove_block(target).unwrap();
        self.function.block_mut(source).unwrap().extend(block.0);
        self.function.set_edges(source, edges);
    }

    /// Inserts a goto statement from source to target
    fn insert_goto_statement(&mut self, source: NodeIndex, target: NodeIndex, edge: EdgeIndex) {
        // Ensure target has a label
        let label = self.ensure_block_has_label(target);
        
        // Create a new block with goto statement
        let goto_block = self.function.new_block();
        self.function
            .block_mut(goto_block)
            .unwrap()
            .push(ast::Goto::new(label).into());

        // Redirect edge through goto block
        let edge_weight = self.function.graph_mut().remove_edge(edge).unwrap();
        self.function.graph_mut().add_edge(source, goto_block, edge_weight);
    }

    /// Ensures a block has a label, adding one if necessary
    fn ensure_block_has_label(&mut self, node: NodeIndex) -> ast::Label {
        let target_block = self.function.block_mut(node).unwrap();
        
        // Check if block already has a label
        if let Some(existing_label) = target_block.first().and_then(|s| s.as_label()) {
            return existing_label.clone();
        }
        
        // Create and insert new label
        let label = ast::Label(format!("l{}", node.index()));
        self.label_to_node.insert(label.clone(), node);
        target_block.insert(0, label.clone().into());
        label
    }

    /// Removes trailing empty return statements
    fn remove_last_return(mut block: ast::Block) -> ast::Block {
        if let Some(ast::Statement::Return(last_statement)) = block.last() {
            if last_statement.values.is_empty() {
                block.0.pop();
            }
        }
        block
    }

    /// Collects all goto destinations from a block recursively
    fn collect_gotos(block: &ast::Block, gotos: &mut FxHashSet<ast::Label>) {
        for statement in &block.0 {
            match statement {
                ast::Statement::Goto(goto) => {
                    gotos.insert(goto.0.clone());
                }
                ast::Statement::If(r#if) => {
                    Self::collect_gotos(&r#if.then_block.lock(), gotos);
                    Self::collect_gotos(&r#if.else_block.lock(), gotos);
                }
                ast::Statement::While(r#while) => {
                    Self::collect_gotos(&r#while.block.lock(), gotos);
                }
                ast::Statement::Repeat(repeat) => {
                    Self::collect_gotos(&repeat.block.lock(), gotos);
                }
                ast::Statement::NumericFor(numeric_for) => {
                    Self::collect_gotos(&numeric_for.block.lock(), gotos);
                }
                ast::Statement::GenericFor(generic_for) => {
                    Self::collect_gotos(&generic_for.block.lock(), gotos);
                }
                _ => {}
            }
        }
    }

    /// Determines if an edge should be converted to goto (heuristic-based)
    fn should_convert_edge_to_goto(
        &self,
        source: NodeIndex,
        target: NodeIndex,
        dominators: &Dominators<NodeIndex>,
    ) -> bool {
        let target_dominators = dominators.dominators(target);
        let source_dominators = dominators.dominators(source);
        
        // Skip unreachable nodes
        if target_dominators.is_none() || source_dominators.is_none() {
            return false;
        }
        
        let mut target_dominators = target_dominators.unwrap();
        let mut source_dominators = source_dominators.unwrap();
        
        // Prefer edges where source doesn't dominate target and vice versa
        // This heuristic reduces goto statements in structured code
        !target_dominators.contains(&source) && !source_dominators.contains(&target)
    }

    /// Main collapse algorithm - reduces the CFG to structured control flow
    fn collapse(&mut self) {
        loop {
            // Try to match patterns until no more matches are found
            while self.match_blocks() {}
            
            // If fully collapsed to single block, we're done
            if self.function.graph().node_count() == 1 {
                break;
            }

            // Last resort: insert goto statements to break cycles
            // Based on approach from: https://edmcman.github.io/papers/usenix13.pdf
            if !self.try_goto_refinement() {
                break;
            }
        }
    }

    /// Tries to insert goto statements to enable further pattern matching
    fn try_goto_refinement(&mut self) -> bool {
        let edges: Vec<_> = self.function.graph().edge_indices().collect();
        let dominators = simple_fast(self.function.graph(), self.function.entry().unwrap());

        // First pass: prefer edges where neither endpoint dominates the other
        for &edge in &edges {
            if !self.is_edge_valid(edge) {
                continue;
            }

            let (source, target) = self.function.graph().edge_endpoints(edge).unwrap();
            
            if self.should_convert_edge_to_goto(source, target, &dominators) {
                self.insert_goto_for_edge(edge);
                self.find_loop_headers();
                
                if self.match_blocks() {
                    return true;
                }
            }
        }

        // Second pass: try all remaining edges
        for edge in edges {
            if !self.is_edge_valid(edge) {
                continue;
            }

            self.insert_goto_for_edge(edge);
            self.find_loop_headers();
            
            if self.match_blocks() {
                return true;
            }
        }

        false
    }

    /// Checks if an edge is still valid (might have been removed by previous operations)
    #[inline]
    fn is_edge_valid(&self, edge: EdgeIndex) -> bool {
        self.function.graph().edge_weight(edge).is_some()
    }

    /// Processes blocks referenced by goto statements
    fn process_goto_destinations(
        &mut self,
        res_block: &mut ast::Block,
        node: NodeIndex,
        visited: &mut FxHashSet<NodeIndex>,
        stack: &mut Vec<NodeIndex>,
    ) {
        let block = self.function.remove_block(node).unwrap();
        
        // Collect all goto destinations from this block
        let mut goto_destinations = FxHashSet::default();
        Self::collect_gotos(&block, &mut goto_destinations);
        
        // Add referenced blocks to processing stack
        for label in goto_destinations {
            if let Some(&target_node) = self.label_to_node.get(&label) {
                if self.function.has_block(target_node) && !visited.contains(&target_node) {
                    stack.push(target_node);
                }
            }
        }

        // Remove redundant goto to this block if it's the last statement
        if let Some(ast::Statement::Goto(goto)) = res_block.last() {
            if goto.0 .0[1..] == node.index().to_string() {
                res_block.pop();
            }
        }

        // Add block marker comment if no label exists
        if !block.first().is_some_and(|s| matches!(s, ast::Statement::Label(_))) {
            res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
        }
        
        res_block.extend(block.0);
    }

    /// Processes remaining unreferenced blocks
    fn process_remaining_blocks(&mut self, res_block: &mut ast::Block) {
        for node in self.function.graph().node_indices().collect::<Vec<_>>() {
            let block = self.function.remove_block(node).unwrap();
            
            if !block.first().is_some_and(|s| matches!(s, ast::Statement::Label(_))) {
                res_block.push(ast::Comment::new(format!("block {}", node.index())).into());
            }
            
            res_block.extend(block.0);
        }
    }

    /// Finalizes the structured AST from the control flow graph
    fn structure(mut self) -> ast::Block {
        self.collapse();

        if self.function.graph().node_count() == 1 {
            // Fully structured - single block
            Self::remove_last_return(
                self.function
                    .remove_block(self.function.entry().unwrap())
                    .unwrap(),
            )
        } else {
            // Partially structured - emit blocks with gotos
            let mut res_block = ast::Block::default();
            let entry = self.function.entry().unwrap();
            let mut stack = vec![entry];
            let mut visited = FxHashSet::default();

            // Process reachable blocks
            while let Some(node) = stack.pop() {
                if visited.contains(&node) {
                    continue;
                }
                visited.insert(node);

                self.process_goto_destinations(&mut res_block, node, &mut visited, &mut stack);
            }

            // Process any remaining unreferenced blocks (likely dead code)
            self.process_remaining_blocks(&mut res_block);

            res_block
        }
    }
}

/// Main entry point for control flow graph restructuring
/// 
/// Takes a low-level CFG function and converts it to structured AST
pub fn lift(function: cfg::function::Function) -> ast::Block {
    GraphStructurer::new(function).structure()
}
