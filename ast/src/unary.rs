use std::fmt;

use crate::{Literal, LocalRw, RValue, RcLocal, Reduce, SideEffects, Traverse};

use super::{Binary, BinaryOperation};

/// Unary operations supported in Luau
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOperation {
    /// Logical NOT (not)
    Not,
    /// Arithmetic negation (-)
    Negate,
    /// Length operator (#)
    Length,
}

impl UnaryOperation {
    /// Returns true if this operation always has side effects
    #[inline]
    pub const fn always_has_side_effects(&self) -> bool {
        // Length operator can trigger __len metamethod
        matches!(self, Self::Length)
    }

    /// Returns the precedence level for this operation
    #[inline]
    pub const fn precedence(&self) -> usize {
        7 // All unary operations have the same precedence
    }
}

impl fmt::Display for UnaryOperation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Not => write!(f, "not "),
            Self::Negate => write!(f, "-"),
            Self::Length => write!(f, "#"),
        }
    }
}

/// Represents a unary operation in the AST
#[derive(Debug, Clone, PartialEq)]
pub struct Unary {
    pub value: Box<RValue>,
    pub operation: UnaryOperation,
}

impl Unary {
    /// Creates a new unary operation
    #[inline]
    pub fn new(value: RValue, operation: UnaryOperation) -> Self {
        Self {
            value: Box::new(value),
            operation,
        }
    }

    /// Returns the precedence of this unary operation
    #[inline]
    pub const fn precedence(&self) -> usize {
        self.operation.precedence()
    }

    /// Determines if the inner value needs to be grouped with parentheses
    pub fn group(&self) -> bool {
        // Group if precedence demands it
        if self.precedence() > self.value.precedence() {
            return true;
        }

        // Special case: avoid double negatives like --x or --5
        if matches!(self.operation, UnaryOperation::Negate) {
            match &*self.value {
                RValue::Unary(inner) if matches!(inner.operation, UnaryOperation::Negate) => {
                    return true;
                }
                RValue::Literal(Literal::Number(value))
                    if value.is_finite() && value.is_sign_negative() =>
                {
                    return true;
                }
                _ => {}
            }
        }

        false
    }

    /// Checks if the value is a boolean expression
    fn is_boolean(r: &RValue) -> bool {
        match r {
            RValue::Binary(binary) if binary.operation.is_comparator() => true,
            RValue::Binary(Binary {
                left,
                right,
                operation: BinaryOperation::And | BinaryOperation::Or,
            }) => Self::is_boolean(left) && Self::is_boolean(right),
            RValue::Literal(Literal::Boolean(_)) => true,
            _ => false,
        }
    }

    /// Ensures the result is a boolean by wrapping if necessary
    fn ensure_boolean(r: RValue) -> RValue {
        if Self::is_boolean(&r) {
            r
        } else {
            Binary::new(
                Binary::new(r, Literal::Boolean(true).into(), BinaryOperation::And).into(),
                Literal::Boolean(false).into(),
                BinaryOperation::Or,
            )
            .into()
        }
    }

    /// Applies De Morgan's laws: not (a and b) = (not a) or (not b)
    fn apply_demorgan(
        left: Box<RValue>,
        right: Box<RValue>,
        operation: BinaryOperation,
        for_condition: bool,
    ) -> RValue {
        let left_negated = Unary::new(*left, UnaryOperation::Not);
        let right_negated = Unary::new(*right, UnaryOperation::Not);

        let left_reduced = if for_condition {
            left_negated.reduce_condition()
        } else {
            left_negated.reduce()
        };

        let right_reduced = if for_condition {
            right_negated.reduce_condition()
        } else {
            right_negated.reduce()
        };

        let flipped_op = if operation == BinaryOperation::And {
            BinaryOperation::Or
        } else {
            BinaryOperation::And
        };

        let result = Binary::new(left_reduced, right_reduced, flipped_op);

        if for_condition {
            result.reduce_condition()
        } else {
            result.reduce()
        }
    }

    /// Inverts a comparison operator
    #[inline]
    fn invert_comparison(op: BinaryOperation) -> BinaryOperation {
        match op {
            BinaryOperation::GreaterThan => BinaryOperation::LessThanOrEqual,
            BinaryOperation::LessThanOrEqual => BinaryOperation::GreaterThan,
            BinaryOperation::GreaterThanOrEqual => BinaryOperation::LessThan,
            BinaryOperation::LessThan => BinaryOperation::GreaterThanOrEqual,
            BinaryOperation::Equal => BinaryOperation::NotEqual,
            BinaryOperation::NotEqual => BinaryOperation::Equal,
            _ => op,
        }
    }
}

impl SideEffects for Unary {
    fn has_side_effects(&self) -> bool {
        // Length operator can call __len metamethod (side effect)
        // Negate can call __unm metamethod (side effect)
        self.operation.always_has_side_effects() || self.value.has_side_effects()
    }
}

impl Traverse for Unary {
    fn rvalues_mut(&mut self) -> Vec<&mut RValue> {
        vec![&mut self.value]
    }

    fn rvalues(&self) -> Vec<&RValue> {
        vec![&self.value]
    }
}

impl Reduce for Unary {
    fn reduce(self) -> RValue {
        let reduced_value = self.value.reduce();

        match (&reduced_value, self.operation) {
            // Boolean NOT
            (RValue::Literal(Literal::Boolean(value)), UnaryOperation::Not) => {
                RValue::Literal(Literal::Boolean(!value))
            }

            // Double negation elimination: not (not x) => x (as boolean)
            (
                RValue::Unary(Unary {
                    value: inner,
                    operation: UnaryOperation::Not,
                }),
                UnaryOperation::Not,
            ) => Self::ensure_boolean(inner.as_ref().clone().reduce_condition()),

            // Numeric negation
            (RValue::Literal(Literal::Number(value)), UnaryOperation::Negate) => {
                RValue::Literal(Literal::Number(-value))
            }

            // String length
            (RValue::Literal(Literal::String(value)), UnaryOperation::Length) => {
                RValue::Literal(Literal::Number(value.len() as f64))
            }

            // NOT on comparisons - invert the comparison
            (
                RValue::Binary(Binary {
                    left,
                    right,
                    operation,
                }),
                UnaryOperation::Not,
            ) if operation.is_comparator() => {
                Binary::new(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                    Self::invert_comparison(*operation),
                )
                .reduce()
            }

            // De Morgan's laws: not (a and b) = (not a) or (not b)
            (
                RValue::Binary(Binary {
                    left,
                    right,
                    operation: op @ (BinaryOperation::And | BinaryOperation::Or),
                }),
                UnaryOperation::Not,
            ) => {
                let should_apply_demorgan = {
                    let left_reduced = Unary::new(left.as_ref().clone(), UnaryOperation::Not)
                        .reduce_condition();
                    let right_reduced = Unary::new(right.as_ref().clone(), UnaryOperation::Not)
                        .reduce_condition();

                    &left_reduced != left.as_ref() || &right_reduced != right.as_ref()
                };

                if should_apply_demorgan {
                    Self::ensure_boolean(Self::apply_demorgan(
                        left.clone(),
                        right.clone(),
                        *op,
                        false,
                    ))
                } else {
                    Self {
                        value: Box::new(reduced_value),
                        operation: self.operation,
                    }
                    .into()
                }
            }

            // No reduction possible
            _ => Self {
                value: Box::new(reduced_value),
                operation: self.operation,
            }
            .into(),
        }
    }

    fn reduce_condition(self) -> RValue {
        let reduced_value = self.value.reduce_condition();

        match (&reduced_value, self.operation) {
            // Boolean NOT
            (RValue::Literal(Literal::Boolean(value)), UnaryOperation::Not) => {
                RValue::Literal(Literal::Boolean(!value))
            }

            // Double negation elimination in conditions
            (
                RValue::Unary(Unary {
                    value: inner,
                    operation: UnaryOperation::Not,
                }),
                UnaryOperation::Not,
            ) => inner.as_ref().clone().reduce_condition(),

            // Numeric negation
            (RValue::Literal(Literal::Number(value)), UnaryOperation::Negate) => {
                RValue::Literal(Literal::Number(-value))
            }

            // Length always returns a number, numbers are always truthy
            (_, UnaryOperation::Length) => RValue::Literal(Literal::Boolean(true)),

            // NOT on comparisons - invert the comparison
            (
                RValue::Binary(Binary {
                    left,
                    right,
                    operation,
                }),
                UnaryOperation::Not,
            ) if operation.is_comparator() => {
                Binary::new(
                    left.as_ref().clone(),
                    right.as_ref().clone(),
                    Self::invert_comparison(*operation),
                )
                .reduce_condition()
            }

            // De Morgan's laws for conditions
            (
                RValue::Binary(Binary {
                    left,
                    right,
                    operation: op @ (BinaryOperation::And | BinaryOperation::Or),
                }),
                UnaryOperation::Not,
            ) => {
                let should_apply_demorgan = {
                    let left_reduced = Unary::new(left.as_ref().clone(), UnaryOperation::Not)
                        .reduce_condition();
                    let right_reduced = Unary::new(right.as_ref().clone(), UnaryOperation::Not)
                        .reduce_condition();

                    &left_reduced != left.as_ref() || &right_reduced != right.as_ref()
                };

                if should_apply_demorgan {
                    Self::apply_demorgan(left.clone(), right.clone(), *op, true)
                } else {
                    Self {
                        value: Box::new(reduced_value),
                        operation: self.operation,
                    }
                    .into()
                }
            }

            // No reduction possible
            _ => Self {
                value: Box::new(reduced_value),
                operation: self.operation,
            }
            .into(),
        }
    }
}

impl LocalRw for Unary {
    fn values_read(&self) -> Vec<&RcLocal> {
        self.value.values_read()
    }

    fn values_read_mut(&mut self) -> Vec<&mut RcLocal> {
        self.value.values_read_mut()
    }
}

impl fmt::Display for Unary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}{}",
            self.operation,
            if self.group() {
                format!("({})", self.value)
            } else {
                format!("{}", self.value)
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_negation_elimination() {
        let inner = RValue::Literal(Literal::Boolean(true));
        let double_not = Unary::new(Unary::new(inner, UnaryOperation::Not).into(), UnaryOperation::Not);
        
        let reduced = double_not.reduce_condition();
        assert_eq!(reduced, RValue::Literal(Literal::Boolean(true)));
    }

    #[test]
    fn test_comparison_inversion() {
        let left = RValue::Literal(Literal::Number(5.0));
        let right = RValue::Literal(Literal::Number(10.0));
        let comparison = Binary::new(left, right, BinaryOperation::GreaterThan);
        let negated = Unary::new(comparison.into(), UnaryOperation::Not);
        
        let reduced = negated.reduce();
        
        if let RValue::Binary(binary) = reduced {
            assert_eq!(binary.operation, BinaryOperation::LessThanOrEqual);
        } else {
            panic!("Expected binary operation");
        }
    }

    #[test]
    fn test_numeric_negation() {
        let unary = Unary::new(RValue::Literal(Literal::Number(42.0)), UnaryOperation::Negate);
        let reduced = unary.reduce();
        
        assert_eq!(reduced, RValue::Literal(Literal::Number(-42.0)));
    }

    #[test]
    fn test_string_length() {
        let unary = Unary::new(
            RValue::Literal(Literal::String("hello".to_string())),
            UnaryOperation::Length,
        );
        let reduced = unary.reduce();
        
        assert_eq!(reduced, RValue::Literal(Literal::Number(5.0)));
    }

    #[test]
    fn test_length_always_truthy() {
        let unary = Unary::new(
            RValue::Literal(Literal::String("test".to_string())),
            UnaryOperation::Length,
        );
        let reduced = unary.reduce_condition();
        
        assert_eq!(reduced, RValue::Literal(Literal::Boolean(true)));
    }

    #[test]
    fn test_grouping_double_negative() {
        let inner = Unary::new(
            RValue::Literal(Literal::Number(5.0)),
            UnaryOperation::Negate,
        );
        let outer = Unary::new(inner.into(), UnaryOperation::Negate);
        
        assert!(outer.group());
    }
}
