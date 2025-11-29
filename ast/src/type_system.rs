use crate::{Block, RcLocal};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

/// Represents types in the Luau type system
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Type {
    /// Any type (top type)
    Any,
    /// Nil type
    Nil,
    /// Boolean type
    Boolean,
    /// Number type
    Number,
    /// String type
    String,
    /// Table type with indexer and named fields
    Table {
        /// (key_type, value_type) for the indexer
        indexer: Box<(Type, Type)>,
        /// Named fields in the table
        fields: BTreeMap<String, Type>,
    },
    /// Function type: (parameters) -> (return_types)
    Function(Vec<Type>, Vec<Type>),
    /// Optional type (T | nil)
    Optional(Box<Type>),
    /// Union type (T1 | T2 | ...)
    Union(BTreeSet<Type>),
    /// Intersection type (T1 & T2 & ...)
    Intersection(BTreeSet<Type>),
    /// Variadic arguments type
    VarArg,
    /// Vector type (Roblox-specific)
    Vector,
}

impl Type {
    /// Checks if this type is a subtype of another type
    pub fn is_subtype_of(&self, other: &Self) -> bool {
        // Any is the top type - everything is a subtype of Any
        if matches!(other, Self::Any) {
            return true;
        }

        match (self, other) {
            // Reflexive: T <: T
            (a, b) if a == b => true,

            // Nil <: T?
            (Self::Nil, Self::Optional(_)) => true,

            // T <: T?
            (t, Self::Optional(inner)) => t.is_subtype_of(inner),

            // Table subtyping (structural)
            (
                Self::Table {
                    indexer: self_indexer,
                    fields: self_fields,
                },
                Self::Table {
                    indexer: other_indexer,
                    fields: other_fields,
                },
            ) => {
                // Indexer must be compatible
                let indexer_compatible = self_indexer.0.is_subtype_of(&other_indexer.0)
                    && self_indexer.1.is_subtype_of(&other_indexer.1);

                // All required fields must be present and compatible
                let fields_compatible = other_fields
                    .iter()
                    .all(|(key, other_type)| {
                        self_fields
                            .get(key)
                            .map_or(false, |self_type| self_type.is_subtype_of(other_type))
                    });

                indexer_compatible && fields_compatible
            }

            // Function subtyping (contravariant in parameters, covariant in returns)
            (Self::Function(self_params, self_returns), Self::Function(other_params, other_returns)) => {
                // Parameters are contravariant: other params must be subtypes of self params
                let params_compatible = self_params.len() == other_params.len()
                    && other_params
                        .iter()
                        .zip(self_params)
                        .all(|(other_param, self_param)| other_param.is_subtype_of(self_param));

                // Returns are covariant: self returns must be subtypes of other returns
                let returns_compatible = self_returns.len() == other_returns.len()
                    && self_returns
                        .iter()
                        .zip(other_returns)
                        .all(|(self_ret, other_ret)| self_ret.is_subtype_of(other_ret));

                params_compatible && returns_compatible
            }

            // Union subtyping: T <: (U1 | U2 | ...) if T <: Ui for some i
            (t, Self::Union(union)) => union.iter().any(|u| t.is_subtype_of(u)),

            // Union on left: (T1 | T2 | ...) <: U if Ti <: U for all i
            (Self::Union(union), u) => union.iter().all(|t| t.is_subtype_of(u)),

            // Intersection subtyping: (T1 & T2 & ...) <: U if Ti <: U for some i
            (Self::Intersection(intersection), u) => intersection.iter().any(|t| t.is_subtype_of(u)),

            // T <: (U1 & U2 & ...) if T <: Ui for all i
            (t, Self::Intersection(intersection)) => intersection.iter().all(|u| t.is_subtype_of(u)),

            _ => false,
        }
    }

    /// Returns the precedence level for parenthesization in display
    #[inline]
    pub const fn precedence(&self) -> usize {
        match self {
            Self::Any
            | Self::Nil
            | Self::Boolean
            | Self::Number
            | Self::String
            | Self::Optional(_)
            | Self::VarArg
            | Self::Vector => 0,
            Self::Table { .. } | Self::Function(_, _) => 1,
            Self::Union(_) | Self::Intersection(_) => 2,
        }
    }

    /// Simplifies the type by merging redundant unions/intersections
    pub fn simplify(self) -> Self {
        match self {
            Self::Union(mut types) => {
                // Remove Any from union (Any | T = Any)
                if types.iter().any(|t| matches!(t, Self::Any)) {
                    return Self::Any;
                }

                // Flatten nested unions
                let mut flattened = BTreeSet::new();
                for t in types.drain(..) {
                    match t.simplify() {
                        Self::Union(inner) => flattened.extend(inner),
                        simplified => {
                            flattened.insert(simplified);
                        }
                    }
                }

                match flattened.len() {
                    0 => Self::Nil,
                    1 => flattened.into_iter().next().unwrap(),
                    _ => Self::Union(flattened),
                }
            }
            Self::Intersection(mut types) => {
                // Flatten nested intersections
                let mut flattened = BTreeSet::new();
                for t in types.drain(..) {
                    match t.simplify() {
                        Self::Intersection(inner) => flattened.extend(inner),
                        simplified => {
                            flattened.insert(simplified);
                        }
                    }
                }

                match flattened.len() {
                    0 => Self::Any,
                    1 => flattened.into_iter().next().unwrap(),
                    _ => Self::Intersection(flattened),
                }
            }
            Self::Optional(inner) => Self::Optional(Box::new(inner.simplify())),
            Self::Function(params, returns) => Self::Function(
                params.into_iter().map(|t| t.simplify()).collect(),
                returns.into_iter().map(|t| t.simplify()).collect(),
            ),
            Self::Table { indexer, fields } => Self::Table {
                indexer: Box::new((indexer.0.simplify(), indexer.1.simplify())),
                fields: fields
                    .into_iter()
                    .map(|(k, v)| (k, v.simplify()))
                    .collect(),
            },
            other => other,
        }
    }

    /// Creates a union type, automatically simplifying if needed
    pub fn union(types: impl IntoIterator<Item = Type>) -> Self {
        let set: BTreeSet<_> = types.into_iter().collect();
        match set.len() {
            0 => Self::Nil,
            1 => set.into_iter().next().unwrap(),
            _ => Self::Union(set).simplify(),
        }
    }

    /// Creates an intersection type, automatically simplifying if needed
    pub fn intersection(types: impl IntoIterator<Item = Type>) -> Self {
        let set: BTreeSet<_> = types.into_iter().collect();
        match set.len() {
            0 => Self::Any,
            1 => set.into_iter().next().unwrap(),
            _ => Self::Intersection(set).simplify(),
        }
    }

    /// Creates an optional type (T | nil)
    pub fn optional(inner: Type) -> Self {
        Self::union([inner, Self::Nil])
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Type::Any => Cow::Borrowed("any"),
            Type::Nil => Cow::Borrowed("nil"),
            Type::Boolean => Cow::Borrowed("boolean"),
            Type::Number => Cow::Borrowed("number"),
            Type::String => Cow::Borrowed("string"),
            Type::Table { indexer, fields } => {
                let (indexer_type, element_type) = indexer.as_ref();

                // Array shorthand: {T} instead of {[number]: T}
                let indexer_str = if indexer_type == &Type::Number && fields.is_empty() {
                    element_type.to_string()
                } else {
                    format!("[{}]: {}", indexer_type, element_type)
                };

                let separator = if !fields.is_empty() { ", " } else { "" };

                let fields_str = fields
                    .iter()
                    .map(|(field, r#type)| format!("{}: {}", field, r#type))
                    .join(", ");

                Cow::Owned(format!("{{{}{}{}}}", indexer_str, separator, fields_str))
            }
            Type::Function(domain, codomain) => {
                let params = domain.iter().join(", ");

                let returns = if codomain.len() == 1 && self.precedence() >= codomain[0].precedence()
                {
                    codomain[0].to_string()
                } else if codomain.len() > 1 {
                    format!("({})", codomain.iter().join(", "))
                } else {
                    codomain.iter().join(", ")
                };

                Cow::Owned(format!("({}) -> {}", params, returns))
            }
            Type::Optional(r#type) => Cow::Owned(format!("{}?", r#type)),
            Type::Union(types) => Cow::Owned(types.iter().join(" | ")),
            Type::Intersection(types) => Cow::Owned(types.iter().join(" & ")),
            Type::VarArg => Cow::Borrowed("..."),
            Type::Vector => Cow::Borrowed("vector"),
        };

        write!(f, "{}", s)
    }
}

/// Type inference and checking system for Luau AST
pub struct TypeSystem<'a> {
    /// Maps local variables to their inferred types
    /// Using FxHashMap for better performance than BTreeMap
    annotations: FxHashMap<&'a RcLocal, Type>,
}

impl<'a> TypeSystem<'a> {
    /// Creates a new type system
    pub fn new() -> Self {
        Self {
            annotations: FxHashMap::default(),
        }
    }

    /// Analyzes a block and performs type inference
    pub fn analyze(block: &'a mut Block) -> Self {
        let mut system = Self::new();
        let _ = system.analyze_block(block);
        system
    }

    /// Analyzes a block and returns the types of return statements
    pub fn analyze_block(&mut self, block: &'a mut Block) -> Vec<Type> {
        let mut return_types = Vec::new();

        for statement in block.iter_mut() {
            match statement {
                crate::Statement::Assign(assign) => {
                    // Infer types for assignments
                    for (lvalue, rvalue) in assign.left.iter_mut().zip(assign.right.iter_mut()) {
                        let inferred_type = self.infer_rvalue(rvalue);

                        if let crate::LValue::Local(local) = lvalue {
                            self.update_local_type(local, inferred_type);
                        }
                    }
                }
                crate::Statement::If(r#if) => {
                    // Analyze both branches
                    let then_returns = self.analyze_block(&mut r#if.then_block.lock());
                    let else_returns = self.analyze_block(&mut r#if.else_block.lock());
                    
                    // Merge return types from both branches
                    if !then_returns.is_empty() || !else_returns.is_empty() {
                        return_types.push(Type::union(
                            then_returns.into_iter().chain(else_returns)
                        ));
                    }
                }
                crate::Statement::While(r#while) => {
                    let _ = self.analyze_block(&mut r#while.block.lock());
                }
                crate::Statement::Repeat(repeat) => {
                    let _ = self.analyze_block(&mut repeat.block.lock());
                }
                crate::Statement::NumericFor(num_for) => {
                    // Type the loop variable as number
                    self.annotations.insert(&num_for.variable, Type::Number);
                    let _ = self.analyze_block(&mut num_for.block.lock());
                }
                crate::Statement::GenericFor(gen_for) => {
                    let _ = self.analyze_block(&mut gen_for.block.lock());
                }
                crate::Statement::Return(r#return) => {
                    let types: Vec<_> = r#return
                        .values
                        .iter_mut()
                        .map(|v| self.infer_rvalue(v))
                        .collect();
                    return_types.extend(types);
                }
                crate::Statement::LocalAssign(local_assign) => {
                    for (local, rvalue) in local_assign.left.iter().zip(local_assign.right.iter_mut()) {
                        let inferred_type = self.infer_rvalue(rvalue);
                        self.annotations.insert(local, inferred_type);
                    }
                }
                _ => {}
            }
        }

        return_types
    }

    /// Updates the type of a local variable, creating unions for multiple assignments
    fn update_local_type(&mut self, local: &'a RcLocal, new_type: Type) {
        if let Some(existing_type) = self.annotations.get_mut(local) {
            // Merge with existing type using union
            let merged = Type::union([existing_type.clone(), new_type]);
            *existing_type = merged;
        } else {
            self.annotations.insert(local, new_type);
        }
    }

    /// Infers the type of an RValue
    fn infer_rvalue(&mut self, rvalue: &mut crate::RValue) -> Type {
        match rvalue {
            crate::RValue::Literal(lit) => match lit {
                crate::Literal::Nil => Type::Nil,
                crate::Literal::Boolean(_) => Type::Boolean,
                crate::Literal::Number(_) => Type::Number,
                crate::Literal::String(_) => Type::String,
            },
            crate::RValue::Local(local) => self.type_of(local).clone(),
            crate::RValue::Binary(binary) => {
                let _left_type = self.infer_rvalue(&mut binary.left);
                let _right_type = self.infer_rvalue(&mut binary.right);

                // Most binary operations return specific types
                match binary.operation {
                    crate::BinaryOperation::Add
                    | crate::BinaryOperation::Subtract
                    | crate::BinaryOperation::Multiply
                    | crate::BinaryOperation::Divide
                    | crate::BinaryOperation::Modulo
                    | crate::BinaryOperation::Power
                    | crate::BinaryOperation::IntegerDivide => Type::Number,
                    
                    crate::BinaryOperation::Concat => Type::String,
                    
                    crate::BinaryOperation::Equal
                    | crate::BinaryOperation::NotEqual
                    | crate::BinaryOperation::LessThan
                    | crate::BinaryOperation::LessThanOrEqual
                    | crate::BinaryOperation::GreaterThan
                    | crate::BinaryOperation::GreaterThanOrEqual => Type::Boolean,
                    
                    crate::BinaryOperation::And | crate::BinaryOperation::Or => {
                        // For and/or, the type depends on the operands
                        Type::Any
                    }
                }
            }
            crate::RValue::Unary(unary) => {
                let _inner_type = self.infer_rvalue(&mut unary.value);

                match unary.operation {
                    crate::UnaryOperation::Not => Type::Boolean,
                    crate::UnaryOperation::Negate => Type::Number,
                    crate::UnaryOperation::Length => Type::Number,
                }
            }
            crate::RValue::Table(_) => {
                // TODO: Infer table structure
                Type::Table {
                    indexer: Box::new((Type::Any, Type::Any)),
                    fields: BTreeMap::new(),
                }
            }
            crate::RValue::Call(_) | crate::RValue::MethodCall(_) => {
                // TODO: Infer from function signatures
                Type::Any
            }
            _ => Type::Any,
        }
    }

    /// Gets the type of a local variable
    pub fn type_of(&self, local: &RcLocal) -> &Type {
        self.annotations.get(local).unwrap_or(&Type::Any)
    }

    /// Gets all annotated locals
    pub fn annotations(&self) -> &FxHashMap<&'a RcLocal, Type> {
        &self.annotations
    }
}

impl<'a> Default for TypeSystem<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// Trait for types that can be inferred
pub trait Infer {
    fn infer<'a: 'b, 'b>(&'a mut self, system: &mut TypeSystem<'b>) -> Type;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subtyping_reflexive() {
        assert!(Type::Number.is_subtype_of(&Type::Number));
        assert!(Type::String.is_subtype_of(&Type::String));
    }

    #[test]
    fn test_subtyping_any() {
        assert!(Type::Number.is_subtype_of(&Type::Any));
        assert!(Type::String.is_subtype_of(&Type::Any));
    }

    #[test]
    fn test_subtyping_optional() {
        assert!(Type::Nil.is_subtype_of(&Type::Optional(Box::new(Type::Number))));
        assert!(Type::Number.is_subtype_of(&Type::Optional(Box::new(Type::Number))));
    }

    #[test]
    fn test_union_simplification() {
        let union = Type::union([Type::Number, Type::Number]);
        assert_eq!(union, Type::Number);

        let union = Type::union([Type::Number, Type::String]);
        assert!(matches!(union, Type::Union(_)));
    }

    #[test]
    fn test_type_display() {
        assert_eq!(Type::Number.to_string(), "number");
        assert_eq!(Type::String.to_string(), "string");
        assert_eq!(
            Type::Function(vec![Type::Number], vec![Type::String]).to_string(),
            "(number) -> string"
        );
    }

    #[test]
    fn test_optional_creation() {
        let opt = Type::optional(Type::Number);
        assert!(opt.to_string().contains("nil"));
    }
}
