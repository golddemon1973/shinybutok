use parking_lot::Mutex;
use triomphe::Arc;
use std::fmt;

use crate::{
    formatter::Formatter, 
    LocalRw, 
    RcLocal, 
    SideEffects, 
    Traverse,
    Block, 
    RValue,
    Statement,
};

/// Represents an if-then-else statement in the AST
#[derive(Debug, Clone)]
pub struct If {
    pub condition: RValue,
    pub then_block: Arc<Mutex<Block>>,
    pub else_block: Arc<Mutex<Block>>,
}

impl PartialEq for If {
    fn eq(&self, other: &Self) -> bool {
        // Compare conditions
        if self.condition != other.condition {
            return false;
        }
        
        // Compare both blocks
        let self_then = self.then_block.lock();
        let other_then = other.then_block.lock();
        let self_else = self.else_block.lock();
        let other_else = other.else_block.lock();
        
        *self_then == *other_then && *self_else == *other_else
    }
}

impl Eq for If {}

impl If {
    /// Creates a new if statement
    #[inline]
    pub fn new(condition: RValue, then_block: Block, else_block: Block) -> Self {
        Self {
            condition,
            then_block: Arc::new(Mutex::new(then_block)),
            else_block: Arc::new(Mutex::new(else_block)),
        }
    }

    /// Creates a new if statement with already wrapped blocks
    #[inline]
    pub fn with_arc_blocks(
        condition: RValue,
        then_block: Arc<Mutex<Block>>,
        else_block: Arc<Mutex<Block>>,
    ) -> Self {
        Self {
            condition,
            then_block,
            else_block,
        }
    }

    /// Gets a reference to the condition
    #[inline]
    pub fn condition(&self) -> &RValue {
        &self.condition
    }

    /// Gets a mutable reference to the condition
    #[inline]
    pub fn condition_mut(&mut self) -> &mut RValue {
        &mut self.condition
    }

    /// Locks and returns the then block
    #[inline]
    pub fn then_block(&self) -> parking_lot::MutexGuard<Block> {
        self.then_block.lock()
    }

    /// Locks and returns the else block
    #[inline]
    pub fn else_block(&self) -> parking_lot::MutexGuard<Block> {
        self.else_block.lock()
    }

    /// Checks if the else block is empty
    #[inline]
    pub fn has_empty_else(&self) -> bool {
        self.else_block.lock().is_empty()
    }

    /// Checks if the then block is empty
    #[inline]
    pub fn has_empty_then(&self) -> bool {
        self.then_block.lock().is_empty()
    }

    /// Checks if both blocks are empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.has_empty_then() && self.has_empty_else()
    }

    /// Checks if this is a simple if-then (no else)
    #[inline]
    pub fn is_simple(&self) -> bool {
        self.has_empty_else()
    }

    /// Checks if both branches end with return statements
    pub fn both_branches_return(&self) -> bool {
        let then_returns = self.then_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Return(_)));
        
        let else_returns = self.else_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Return(_)));
        
        then_returns && else_returns
    }

    /// Checks if both branches end with break statements
    pub fn both_branches_break(&self) -> bool {
        let then_breaks = self.then_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Break(_)));
        
        let else_breaks = self.else_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Break(_)));
        
        then_breaks && else_breaks
    }

    /// Checks if both branches end with continue statements
    pub fn both_branches_continue(&self) -> bool {
        let then_continues = self.then_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Continue(_)));
        
        let else_continues = self.else_block
            .lock()
            .last()
            .map_or(false, |s| matches!(s, Statement::Continue(_)));
        
        then_continues && else_continues
    }

    /// Checks if either branch ends with a control flow statement (return/break/continue)
    pub fn has_terminal_branch(&self) -> bool {
        self.then_branch_is_terminal() || self.else_branch_is_terminal()
    }

    /// Checks if the then branch ends with a terminal statement
    pub fn then_branch_is_terminal(&self) -> bool {
        self.then_block.lock().last().map_or(false, |s| {
            matches!(
                s,
                Statement::Return(_) | Statement::Break(_) | Statement::Continue(_)
            )
        })
    }

    /// Checks if the else branch ends with a terminal statement
    pub fn else_branch_is_terminal(&self) -> bool {
        self.else_block.lock().last().map_or(false, |s| {
            matches!(
                s,
                Statement::Return(_) | Statement::Break(_) | Statement::Continue(_)
            )
        })
    }

    /// Returns the complexity of this if statement (for optimization decisions)
    pub fn complexity(&self) -> usize {
        let then_size = self.then_block.lock().len();
        let else_size = self.else_block.lock().len();
        let condition_complexity = self.condition.precedence();
        
        then_size + else_size + condition_complexity
    }

    /// Attempts to simplify this if statement (e.g., empty branches, constant conditions)
    /// Returns None if the if statement should be removed entirely
    pub fn simplify(mut self) -> Option<Self> {
        // If condition is constant true, the if is unnecessary but we keep the then block
        // The caller should extract the then_block statements
        if matches!(self.condition, RValue::Literal(crate::Literal::Boolean(true))) {
            // Condition is always true - just use then block
            // Return None to signal the if should be replaced with its then block
            return None;
        }

        // If condition is constant false, use else block
        if matches!(self.condition, RValue::Literal(crate::Literal::Boolean(false))) {
            // Condition is always false - just use else block
            // Swap to then block and return None
            self.then_block = self.else_block.clone();
            self.else_block = Arc::new(Mutex::new(Block::default()));
            return None;
        }

        // If both blocks are empty and condition has no side effects, remove entirely
        if self.is_empty() && !self.condition.has_side_effects() {
            return None;
        }

        // If both blocks are identical, we can optimize this
        if self.then_block.lock().0 == self.else_block.lock().0 {
            // Both branches do the same thing - the condition doesn't matter
            return None;
        }

        // Cannot simplify further
        Some(self)
    }
}

impl Traverse for If {
    fn rvalues_mut(&mut self) -> Vec<&mut RValue> {
        // Only traverse the condition, not the blocks
        // The blocks should be traversed separately when needed
        vec![&mut self.condition]
    }

    fn rvalues(&self) -> Vec<&RValue> {
        // Only traverse the condition, not the blocks
        // The blocks should be traversed separately when needed
        vec![&self.condition]
    }
}

impl SideEffects for If {
    fn has_side_effects(&self) -> bool {
        // Condition might have side effects
        if self.condition.has_side_effects() {
            return true;
        }

        // Check if either block has side effects
        let then_has_effects = self.then_block
            .lock()
            .iter()
            .any(|s| s.has_side_effects());

        let else_has_effects = self.else_block
            .lock()
            .iter()
            .any(|s| s.has_side_effects());

        then_has_effects || else_has_effects
    }
}

impl LocalRw for If {
    fn values_read(&self) -> Vec<&RcLocal> {
        // Only return values from the condition
        // Blocks should be handled separately
        self.condition.values_read()
    }

    fn values_read_mut(&mut self) -> Vec<&mut RcLocal> {
        // Only return values from the condition
        // Blocks should be handled separately
        self.condition.values_read_mut()
    }

    fn values_written(&self) -> Vec<&RcLocal> {
        // If statements don't write directly, only through their blocks
        // Blocks should be analyzed separately
        Vec::new()
    }

    fn values_written_mut(&mut self) -> Vec<&mut RcLocal> {
        // If statements don't write directly, only through their blocks
        // Blocks should be analyzed separately
        Vec::new()
    }
}

impl fmt::Display for If {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Formatter {
            indentation_level: 0,
            indentation_mode: Default::default(),
            output: f,
        }
        .format_if(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;

    #[test]
    fn test_if_creation() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let then_block = Block::default();
        let else_block = Block::default();
        
        let if_stmt = If::new(condition, then_block, else_block);
        assert!(if_stmt.has_empty_then());
        assert!(if_stmt.has_empty_else());
    }

    #[test]
    fn test_if_simplification_constant_true() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let if_stmt = If::new(condition, Block::default(), Block::default());
        
        // Should return None (indicating the if can be removed/simplified)
        assert!(if_stmt.simplify().is_none());
    }

    #[test]
    fn test_if_simplification_constant_false() {
        let condition = RValue::Literal(Literal::Boolean(false));
        let if_stmt = If::new(condition, Block::default(), Block::default());
        
        // Should return None (indicating the if can be removed/simplified)
        assert!(if_stmt.simplify().is_none());
    }

    #[test]
    fn test_terminal_branches() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let mut then_block = Block::default();
        then_block.push(Statement::Return(crate::Return { values: vec![] }));
        
        let if_stmt = If::new(condition, then_block, Block::default());
        assert!(if_stmt.then_branch_is_terminal());
        assert!(!if_stmt.else_branch_is_terminal());
    }

    #[test]
    fn test_equality() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let if1 = If::new(condition.clone(), Block::default(), Block::default());
        let if2 = If::new(condition, Block::default(), Block::default());
        
        assert_eq!(if1, if2);
    }
}
