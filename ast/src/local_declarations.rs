use std::collections::BTreeMap;

use array_tool::vec::Intersect;
use by_address::ByAddress;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use parking_lot::Mutex;
use petgraph::{
    algo::dominators::{simple_fast, Dominators},
    prelude::{DiGraph, NodeIndex},
    Direction,
};
use rustc_hash::{FxHashMap, FxHashSet};
use triomphe::Arc;

use crate::{Assign, Block, LocalRw, RcLocal, Statement};

/// Node data in the control flow graph for local declaration analysis
type BlockNode = (Option<Arc<Mutex<Block>>>, usize);

/// Analyzes control flow to determine optimal local variable declaration positions
/// 
/// This struct builds a control flow graph from the AST and uses dominator analysis
/// to find the earliest point where each local variable should be declared.
#[derive(Default)]
pub struct LocalDeclarer {
    /// Maps blocks to their corresponding graph nodes
    block_to_node: FxHashMap<ByAddress<Arc<Mutex<Block>>>, NodeIndex>,
    
    /// Control flow graph: nodes are (block, statement_index), edges are control flow
    graph: DiGraph<BlockNode, ()>,
    
    /// Tracks where each local is written/used: local -> {node -> first_statement_index}
    local_usages: IndexMap<RcLocal, FxHashMap<NodeIndex, usize>>,
    
    /// Final declaration positions: block -> {statement_index -> {locals}}
    declarations: FxHashMap<ByAddress<Arc<Mutex<Block>>>, BTreeMap<usize, IndexSet<RcLocal>>>,
}

impl LocalDeclarer {
    /// Creates a new local declarer
    pub fn new() -> Self {
        Self::default()
    }

    /// Visits a block and builds the control flow graph recursively
    /// 
    /// Returns the graph node for this block
    fn visit(&mut self, block: Arc<Mutex<Block>>, stat_index: usize) -> NodeIndex {
        let node = self.graph.add_node((Some(block.clone()), stat_index));
        self.block_to_node.insert(block.clone().into(), node);
        
        let block_guard = block.lock();
        
        for (index, stat) in block_guard.iter().enumerate() {
            // For loops declare their own loop variables, so skip them
            if matches!(stat, Statement::GenericFor(_) | Statement::NumericFor(_)) {
                continue;
            }

            // Track where each local is written (locals are always written before read)
            for local in stat.values_written() {
                self.local_usages
                    .entry(local.clone())
                    .or_default()
                    .entry(node)
                    .or_insert(index);
            }
        }

        // Visit nested control structures
        for (index, stat) in block_guard.iter().enumerate() {
            self.visit_statement(node, stat, index);
        }
        
        drop(block_guard);
        node
    }

    /// Visits a single statement and adds edges for control flow structures
    fn visit_statement(&mut self, parent_node: NodeIndex, stat: &Statement, stat_index: usize) {
        match stat {
            Statement::If(r#if) => {
                // Create intermediate node for the if statement
                let if_node = self.graph.add_node((None, stat_index));
                self.graph.add_edge(parent_node, if_node, ());
                
                // Visit both branches
                let then_node = self.visit(r#if.then_block.clone(), stat_index);
                self.graph.add_edge(if_node, then_node, ());
                
                let else_node = self.visit(r#if.else_block.clone(), stat_index);
                self.graph.add_edge(if_node, else_node, ());
            }
            Statement::While(r#while) => {
                let child = self.visit(r#while.block.clone(), stat_index);
                self.graph.add_edge(parent_node, child, ());
            }
            Statement::Repeat(repeat) => {
                let child = self.visit(r#repeat.block.clone(), stat_index);
                self.graph.add_edge(parent_node, child, ());
            }
            Statement::NumericFor(numeric_for) => {
                let child = self.visit(r#numeric_for.block.clone(), stat_index);
                self.graph.add_edge(parent_node, child, ());
            }
            Statement::GenericFor(generic_for) => {
                let child = self.visit(r#generic_for.block.clone(), stat_index);
                self.graph.add_edge(parent_node, child, ());
            }
            _ => {}
        }
    }

    /// Finds the common dominator for multiple usage nodes
    fn find_common_dominator(
        &self,
        usages: &FxHashMap<NodeIndex, usize>,
        dominators: &Dominators<NodeIndex>,
    ) -> Option<NodeIndex> {
        let node_dominators: Vec<Vec<_>> = usages
            .keys()
            .filter_map(|&node| dominators.dominators(node).map(|d| d.collect()))
            .collect();

        if node_dominators.is_empty() {
            return None;
        }

        // Find intersection of all dominator sets
        let mut common = node_dominators[0].clone();
        for dominators in &node_dominators[1..] {
            common = common.intersect(dominators.clone());
        }

        common.first().copied()
    }

    /// Finds the declaration position for a local with multiple usages
    fn find_declaration_position(
        &self,
        usages: FxHashMap<NodeIndex, usize>,
        dominators: &Dominators<NodeIndex>,
    ) -> (NodeIndex, usize) {
        if usages.len() == 1 {
            return usages.into_iter().next().unwrap();
        }

        let node_dominators: Vec<Vec<_>> = usages
            .keys()
            .filter_map(|&node| dominators.dominators(node).map(|d| d.collect()))
            .collect();

        let common_dominator = self.find_common_dominator(&usages, dominators)
            .expect("Should have at least one common dominator");

        // Check if the common dominator itself uses this local
        if let Some(&first_stat_index) = usages.get(&common_dominator) {
            return (common_dominator, first_stat_index);
        }

        // Find the leftmost dominated child node
        let first_stat_index = self
            .find_leftmost_dominated_child(common_dominator, &node_dominators)
            .expect("Should find at least one dominated child");

        (common_dominator, first_stat_index)
    }

    /// Finds the leftmost (earliest) child node that's in the dominator sets
    fn find_leftmost_dominated_child(
        &self,
        parent: NodeIndex,
        node_dominators: &[Vec<NodeIndex>],
    ) -> Option<usize> {
        for child in self.graph.neighbors_directed(parent, Direction::Outgoing) {
            for dominators in node_dominators {
                if dominators.contains(&child) {
                    return Some(self.graph.node_weight(child)?.1);
                }
            }
        }
        None
    }

    /// Walks up the graph to find the actual block node (skipping intermediate nodes)
    fn find_actual_block_node(&self, mut node: NodeIndex, mut stat_index: usize) -> (NodeIndex, usize, Arc<Mutex<Block>>) {
        loop {
            let (block_opt, parent_stat_index) = self.graph.node_weight(node)
                .expect("Node should exist in graph");

            if let Some(block) = block_opt {
                return (node, stat_index, block.clone());
            }

            // This is an intermediate node, walk up to parent
            let parent = self
                .graph
                .neighbors_directed(node, Direction::Incoming)
                .exactly_one()
                .expect("Intermediate node should have exactly one parent");

            node = parent;
            stat_index = *parent_stat_index;
        }
    }

    /// Converts an existing assignment into a local declaration if possible
    fn try_convert_assignment_to_declaration(
        &self,
        statement: &mut Statement,
        locals: &mut IndexSet<RcLocal>,
    ) {
        if let Statement::Assign(assign) = statement {
            // Check if all left-hand sides are locals that we want to declare
            let all_are_declared_locals = assign
                .left
                .iter()
                .all(|lvalue| {
                    lvalue.as_local().is_some_and(|l| locals.contains(l))
                });

            if all_are_declared_locals {
                // Remove these locals from the set (they're already declared by assignment)
                locals.retain(|local| {
                    !assign
                        .left
                        .iter()
                        .any(|lvalue| lvalue.as_local() == Some(local))
                });
                
                // Mark as a prefixed declaration (local x = ...)
                assign.prefix = true;
            }
        }
    }

    /// Inserts local declarations into blocks at computed positions
    fn insert_declarations(&self, declarations: FxHashMap<ByAddress<Arc<Mutex<Block>>>, BTreeMap<usize, IndexSet<RcLocal>>>) {
        for (ByAddress(block), decls) in declarations {
            let mut block_guard = block.lock();
            
            // Process in reverse order to maintain correct indices
            for (stat_index, mut locals) in decls.into_iter().rev() {
                // Try to convert existing assignments to declarations
                self.try_convert_assignment_to_declaration(
                    &mut block_guard[stat_index],
                    &mut locals,
                );

                // Insert remaining declarations as separate statements
                if !locals.is_empty() {
                    let declaration = Assign {
                        left: locals.into_iter().map(Into::into).collect(),
                        right: vec![],
                        prefix: true,
                        parallel: false,
                    };
                    block_guard.insert(stat_index, declaration.into());
                }
            }
        }
    }

    /// Main entry point: analyzes control flow and declares locals optimally
    /// 
    /// # Arguments
    /// * `root_block` - The root block to analyze
    /// * `locals_to_ignore` - Locals that should not be declared (e.g., function parameters)
    pub fn declare_locals(
        mut self,
        root_block: Arc<Mutex<Block>>,
        locals_to_ignore: &FxHashSet<RcLocal>,
    ) {
        // Build control flow graph
        let root_node = self.visit(root_block, 0);
        
        // Compute dominators
        let dominators = simple_fast(&self.graph, root_node);

        // Determine declaration positions for each local
        for (local, usages) in self.local_usages {
            if locals_to_ignore.contains(&local) {
                continue;
            }

            let (node, first_stat_index) = 
                self.find_declaration_position(usages, &dominators);

            let (actual_node, actual_stat_index, block) = 
                self.find_actual_block_node(node, first_stat_index);

            // Record the declaration position
            self.declarations
                .entry(block.into())
                .or_default()
                .entry(actual_stat_index)
                .or_default()
                .insert(local);
        }

        // Insert all declarations
        self.insert_declarations(self.declarations);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_local_declarer_creation() {
        let declarer = LocalDeclarer::new();
        assert_eq!(declarer.graph.node_count(), 0);
        assert!(declarer.local_usages.is_empty());
    }

    #[test]
    fn test_empty_block() {
        let declarer = LocalDeclarer::new();
        let block = Arc::new(Mutex::new(Block::default()));
        let ignore_set = FxHashSet::default();
        
        declarer.declare_locals(block, &ignore_set);
        // Should complete without panicking
    }
}
