use parking_lot::Mutex;
use triomphe::Arc;
use crate::{formatter::Formatter, has_side_effects, Block, LocalRw, RValue, RcLocal, Traverse};
use std::fmt;

#[derive(Debug, Clone)]
pub struct While {
    pub condition: RValue,
    pub block: Arc<Mutex<Block>>,
}

impl PartialEq for While {
    fn eq(&self, other: &Self) -> bool {
        // Compare conditions
        if self.condition != other.condition {
            return false;
        }
        
        // Compare blocks by locking and comparing contents
        let self_block = self.block.lock();
        let other_block = other.block.lock();
        *self_block == *other_block
    }
}

impl Eq for While {}

has_side_effects!(While);

impl While {
    /// Creates a new while loop with the given condition and block
    #[inline]
    pub fn new(condition: RValue, block: Block) -> Self {
        Self {
            condition,
            block: Arc::new(Mutex::new(block)),
        }
    }

    /// Creates a new while loop with an already wrapped block
    #[inline]
    pub fn with_arc_block(condition: RValue, block: Arc<Mutex<Block>>) -> Self {
        Self { condition, block }
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

    /// Locks and returns the block for reading/modification
    #[inline]
    pub fn block(&self) -> parking_lot::MutexGuard<Block> {
        self.block.lock()
    }

    /// Checks if the while loop has a constant condition
    #[inline]
    pub fn has_constant_condition(&self) -> bool {
        matches!(self.condition, RValue::Literal(_))
    }

    /// Checks if this is an infinite loop (while true do)
    #[inline]
    pub fn is_infinite(&self) -> bool {
        matches!(
            self.condition,
            RValue::Literal(crate::Literal::Boolean(true))
        )
    }
}

impl Traverse for While {
    fn rvalues_mut(&mut self) -> Vec<&mut RValue> {
        // Only traverse the condition, not the block
        // The block should be traversed separately when needed
        vec![&mut self.condition]
    }

    fn rvalues(&self) -> Vec<&RValue> {
        // Only traverse the condition, not the block
        // The block should be traversed separately when needed
        vec![&self.condition]
    }
}

impl LocalRw for While {
    fn values_read(&self) -> Vec<&RcLocal> {
        // Only return values from the condition
        // Block should be handled separately
        self.condition.values_read()
    }

    fn values_read_mut(&mut self) -> Vec<&mut RcLocal> {
        // Only return values from the condition
        // Block should be handled separately
        self.condition.values_read_mut()
    }

    fn values_written(&self) -> Vec<&RcLocal> {
        // While condition doesn't write, blocks should be analyzed separately
        Vec::new()
    }

    fn values_written_mut(&mut self) -> Vec<&mut RcLocal> {
        // While condition doesn't write, blocks should be analyzed separately
        Vec::new()
    }
}

impl fmt::Display for While {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Formatter {
            indentation_level: 0,
            indentation_mode: Default::default(),
            output: f,
        }
        .format_while(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Literal;

    #[test]
    fn test_while_creation() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let block = Block::default();
        let while_loop = While::new(condition.clone(), block);
        
        assert_eq!(while_loop.condition, condition);
    }

    #[test]
    fn test_while_infinite_detection() {
        let infinite = While::new(
            RValue::Literal(Literal::Boolean(true)),
            Block::default(),
        );
        assert!(infinite.is_infinite());

        let finite = While::new(
            RValue::Literal(Literal::Boolean(false)),
            Block::default(),
        );
        assert!(!finite.is_infinite());
    }

    #[test]
    fn test_while_constant_condition() {
        let constant = While::new(
            RValue::Literal(Literal::Number(42.0)),
            Block::default(),
        );
        assert!(constant.has_constant_condition());
    }

    #[test]
    fn test_while_equality() {
        let condition = RValue::Literal(Literal::Boolean(true));
        let block = Block::default();
        
        let while1 = While::new(condition.clone(), block.clone());
        let while2 = While::new(condition.clone(), block.clone());
        
        assert_eq!(while1, while2);
    }
}
