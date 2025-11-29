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
    pub fn simplify(self) -> Result<Statement, Self> {
        // If condition is constant true, return then block
        if let RValue::Literal(crate::Literal::Boolean(true)) = self.condition {
            let then_statements = self.then_block.lock().0.clone();
            return Ok(Statement::Block(then_statements.into()));
        }

        // If condition is constant false, return else block
        if let RValue::Literal(crate::Literal::Boolean(false)) = self.condition {
            let else_statements = self.else_block.lock().0.clone();
            return Ok(Statement::Block(else_statements.into()));
        }

        // If both blocks are empty, convert to expression statement
        if self.is_empty() && !self.condition.has_side_effects() {
            return Ok(Statement::Comment(crate::Comment::new(
                "Empty if statement removed".to_string()
            )));
        }

        // If both blocks are identical, we can optimize this
        if self.then_block.lock().0 == self.else_block.lock().0 {
            let statements = self.then_block.lock().0.clone();
            return Ok(Statement::Block(statements.into()));
        }

        // Cannot simplify further
        Err(self)
    }
}

impl Traverse for If {
    fn rvalues_mut(&mut self) -> Vec<&mut RValue> {
        let mut rvalues = vec![&mut self.condition];
        
        // Traverse then block
        let mut then_block = self.then_block.lock();
        for statement in then_block.iter_mut() {
            rvalues.extend(statement.rvalues_mut());
        }
        
        // Traverse else block
        let mut else_block = self.else_block.lock();
        for statement in else_block.iter_mut() {
            rvalues.extend(statement.rvalues_mut());
        }
        
        rvalues
    }

    fn rvalues(&self) -> Vec<&RValue> {
        let mut rvalues = vec![&self.condition];
        
        // Traverse then block
        let then_block = self.then_block.lock();
        for statement in then_block.iter() {
            rvalues.extend(statement.rvalues());
        }
        
        // Traverse else block
        let else_block = self.else_block.lock();
        for statement in else_block.iter() {
            rvalues.extend(statement.rvalues());
        }
        
        rvalues
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
        let mut values = self.condition.values_read();
        
        // Collect from both blocks
        let then_block = self.then_block.lock();
        for statement in then_block.iter() {
            values.extend(statement.values_read());
        }
        
        let else_block = self.else_block.lock();
        for statement in else_block.iter() {
            values.extend(statement.values_read());
        }
        
        values
    }

    fn values_read_mut(&mut self) -> Vec<&mut RcLocal> {
        let mut values = self.condition.values_read_mut();
        
        // Collect from both blocks
        let mut then_block = self.then_block.lock();
        for statement in then_block.iter_mut() {
            values.extend(statement.values_read_mut());
        }
        
        let mut else_block = self.else_block.lock();
        for statement in else_block.iter_mut() {
            values.extend(statement.values_read_mut());
        }
        
        values
    }

    fn values_written(&self) -> Vec<&RcLocal> {
        let mut values = Vec::new();
        
        // Collect from both blocks
        let then_block = self.then_block.lock();
        for statement in then_block.iter() {
            values.extend(statement.values_written());
        }
        
        let else_block = self.else_block.lock();
        for statement in else_block.iter() {
            values.extend(statement.values_written());
        }
        
        values
    }

    fn values_written_mut(&mut self) -> Vec<&mut RcLocal> {
        let mut values = Vec::new();
        
        // Collect from both blocks
        let mut then_block = self.then_block.lock();
        for statement in then_block.iter_mut() {
            values.extend(statement.values_written_mut());
        }
        
        let mut else_block = self.else_block.lock();
        for statement in else_block.iter_mut() {
            values.extend(statement.values_written_mut());
        }
        
        values
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
        
        assert!(if_stmt.simplify().is_ok());
    }

    #[test]
    fn test_if_simplification_constant_false() {
        let condition = RValue::Literal(Literal::Boolean(false));
        let if_stmt = If::new(condition, Block::default(), Block::default());
        
        assert!(if_stmt.simplify().is_ok());
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
