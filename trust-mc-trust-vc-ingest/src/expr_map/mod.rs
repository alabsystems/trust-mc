// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Maps trust_vc infix or SMT-LIB `TypedExpr` strings into ay expressions.

use std::collections::BTreeMap;

use ay_bindings::{Expr, Sort};
use syn::{BinOp, Expr as SynExpr, ExprPath, Lit, UnOp};
use trust_vc_merge_contract::{SortMeta, TypedExpr};

use crate::{IngestError, MappedVar, translate_sort};

mod lower;
mod normalize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MappedExpr {
    pub original: String,
    pub sort: Sort,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeclaredFunction {
    pub name: String,
    pub param_names: Vec<String>,
    pub arg_sorts: Vec<Sort>,
    pub return_sort: Sort,
    pub is_recursive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TypeInfo {
    Bool,
    Int,
    BitVector { width: u32, signed: bool },
    Other(Sort),
}

impl TypeInfo {
    fn from_sort_meta(meta: &SortMeta) -> Result<Self, IngestError> {
        match meta {
            SortMeta::Bool => Ok(Self::Bool),
            SortMeta::MathInt => Ok(Self::Int),
            SortMeta::BitVector { width, signed } => {
                Ok(Self::BitVector { width: *width, signed: *signed })
            }
            _ => translate_sort(meta).map(Self::Other).map_err(|reason| {
                IngestError::UnsupportedExpression { expr: format!("{meta:?}"), reason }
            }),
        }
    }

    fn from_sort(sort: &Sort) -> Result<Self, IngestError> {
        if sort.is_bool() {
            Ok(Self::Bool)
        } else if sort.is_int() {
            Ok(Self::Int)
        } else if sort.is_bitvec() {
            Ok(Self::BitVector {
                width: sort.bitvec_width().expect("bitvector sort should expose width"),
                signed: false,
            })
        } else {
            Ok(Self::Other(sort.clone()))
        }
    }

    fn sort(&self) -> Sort {
        match self {
            Self::Bool => Sort::bool(),
            Self::Int => Sort::int(),
            Self::BitVector { width, .. } => Sort::bitvec(*width),
            Self::Other(sort) => sort.clone(),
        }
    }

    fn describe(&self) -> String {
        match self {
            Self::Bool => "Bool".to_string(),
            Self::Int => "Int".to_string(),
            Self::BitVector { width, signed } => {
                let signedness = if *signed { "signed" } else { "unsigned" };
                format!("BitVec({width}, {signedness})")
            }
            Self::Other(sort) => sort.to_string(),
        }
    }

    fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    fn is_numeric(&self) -> bool {
        matches!(self, Self::Int | Self::BitVector { .. })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionSig {
    name: String,
    param_names: Vec<String>,
    arg_types: Vec<TypeInfo>,
    return_type: TypeInfo,
    is_recursive: bool,
}

#[derive(Debug, Clone)]
struct SymbolInfo {
    ty: TypeInfo,
}

#[derive(Debug, Clone)]
struct NormalizedExpr {
    smt: String,
    ty: TypeInfo,
}

pub(crate) struct ExprMapper {
    variables: BTreeMap<String, SymbolInfo>,
    functions: BTreeMap<String, FunctionSig>,
}

impl ExprMapper {
    pub(crate) fn new(variables: &[MappedVar]) -> Self {
        let variables = variables
            .iter()
            .map(|var| {
                let ty = TypeInfo::from_sort_meta(&var.meta)
                    .expect("variable sorts already validated during bundle ingestion");
                (var.name.clone(), SymbolInfo { ty })
            })
            .collect();
        Self { variables, functions: BTreeMap::new() }
    }

    pub(crate) fn functions(&self) -> Vec<DeclaredFunction> {
        self.functions
            .values()
            .map(|sig| DeclaredFunction {
                name: sig.name.clone(),
                param_names: sig.param_names.clone(),
                arg_sorts: sig.arg_types.iter().map(TypeInfo::sort).collect(),
                return_sort: sig.return_type.sort(),
                is_recursive: sig.is_recursive,
            })
            .collect()
    }

    pub(crate) fn register_function(
        &mut self,
        function: DeclaredFunction,
    ) -> Result<(), IngestError> {
        let arg_types =
            function.arg_sorts.iter().map(TypeInfo::from_sort).collect::<Result<Vec<_>, _>>()?;
        let return_type = TypeInfo::from_sort(&function.return_sort)?;
        let sig = FunctionSig {
            name: function.name.clone(),
            param_names: function.param_names,
            arg_types,
            return_type,
            is_recursive: function.is_recursive,
        };

        if let Some(existing) = self.functions.get(&function.name) {
            if existing.arg_types != sig.arg_types || existing.return_type != sig.return_type {
                return Err(IngestError::FunctionSignature {
                    expr: function.name,
                    reason: format!(
                        "registered signature {} -> {} conflicts with existing {} -> {}",
                        describe_args(&sig.arg_types),
                        sig.return_type.describe(),
                        describe_args(&existing.arg_types),
                        existing.return_type.describe()
                    ),
                });
            }
            return Ok(());
        }

        self.functions.insert(function.name, sig);
        Ok(())
    }

    pub(crate) fn translate_with_bound_vars(
        &mut self,
        bound_vars: &[MappedVar],
        typed_expr: &TypedExpr,
    ) -> Result<MappedExpr, IngestError> {
        let bound_symbols = bound_vars
            .iter()
            .map(|var| {
                let ty = TypeInfo::from_sort_meta(&var.meta)?;
                Ok((var.name.clone(), SymbolInfo { ty }))
            })
            .collect::<Result<Vec<_>, IngestError>>()?;
        let previous = bound_symbols
            .into_iter()
            .map(|(name, symbol)| {
                let previous = self.variables.insert(name.clone(), symbol);
                (name, previous)
            })
            .collect::<Vec<_>>();

        let result = self.translate(typed_expr);

        for (name, symbol) in previous {
            if let Some(symbol) = symbol {
                self.variables.insert(name, symbol);
            } else {
                self.variables.remove(&name);
            }
        }

        result
    }

    pub(crate) fn translate(&mut self, typed_expr: &TypedExpr) -> Result<MappedExpr, IngestError> {
        let expected_ty = TypeInfo::from_sort_meta(typed_expr.sort())?;
        let lowered = match syn::parse_str::<SynExpr>(typed_expr.expr()) {
            Ok(parsed) => {
                let normalized = self.normalize(&parsed, Some(&expected_ty), typed_expr.expr())?;
                self.lower_from_smt(&normalized.smt, Some(&expected_ty), typed_expr.expr())?
            }
            Err(rust_err) => self
                .lower_from_smt(typed_expr.expr(), Some(&expected_ty), typed_expr.expr())
                .map_err(|smt_err| IngestError::ExpressionParse {
                    expr: typed_expr.expr().to_string(),
                    reason: format!(
                        "failed to parse as infix expression ({rust_err}); \
                         failed to parse/lower as SMT term ({smt_err})"
                    ),
                })?,
        };

        if lowered.sort() != &expected_ty.sort() {
            return Err(IngestError::ExpressionSortMismatch {
                expr: typed_expr.expr().to_string(),
                expected: expected_ty.describe(),
                actual: lowered.sort().to_string(),
            });
        }

        Ok(MappedExpr {
            original: typed_expr.expr().to_string(),
            sort: expected_ty.sort(),
            expr: lowered,
        })
    }
}

fn describe_args(args: &[TypeInfo]) -> String {
    let args = args.iter().map(TypeInfo::describe).collect::<Vec<_>>().join(", ");
    format!("({args})")
}

fn path_to_name(path: &ExprPath) -> Result<String, IngestError> {
    let segments =
        path.path.segments.iter().map(|segment| segment.ident.to_string()).collect::<Vec<_>>();
    if segments.is_empty() {
        return Err(IngestError::UnsupportedExpression {
            expr: "<empty path>".to_string(),
            reason: "empty path".to_string(),
        });
    }
    Ok(segments.join("::"))
}

fn syn_expr_kind(expr: &SynExpr) -> &'static str {
    match expr {
        SynExpr::Array(_) => "array",
        SynExpr::Assign(_) => "assign",
        SynExpr::Async(_) => "async",
        SynExpr::Await(_) => "await",
        SynExpr::Binary(_) => "binary",
        SynExpr::Block(_) => "block",
        SynExpr::Break(_) => "break",
        SynExpr::Call(_) => "call",
        SynExpr::Cast(_) => "cast",
        SynExpr::Closure(_) => "closure",
        SynExpr::Const(_) => "const",
        SynExpr::Continue(_) => "continue",
        SynExpr::Field(_) => "field",
        SynExpr::ForLoop(_) => "for-loop",
        SynExpr::Group(_) => "group",
        SynExpr::If(_) => "if",
        SynExpr::Index(_) => "index",
        SynExpr::Infer(_) => "infer",
        SynExpr::Let(_) => "let",
        SynExpr::Lit(_) => "literal",
        SynExpr::Loop(_) => "loop",
        SynExpr::Macro(_) => "macro",
        SynExpr::Match(_) => "match",
        SynExpr::MethodCall(_) => "method-call",
        SynExpr::Paren(_) => "paren",
        SynExpr::Path(_) => "path",
        SynExpr::Range(_) => "range",
        SynExpr::RawAddr(_) => "raw-addr",
        SynExpr::Reference(_) => "reference",
        SynExpr::Repeat(_) => "repeat",
        SynExpr::Return(_) => "return",
        SynExpr::Struct(_) => "struct",
        SynExpr::Try(_) => "try",
        SynExpr::TryBlock(_) => "try-block",
        SynExpr::Tuple(_) => "tuple",
        SynExpr::Unary(_) => "unary",
        SynExpr::Unsafe(_) => "unsafe",
        SynExpr::Verbatim(_) => "verbatim",
        SynExpr::While(_) => "while",
        SynExpr::Yield(_) => "yield",
        _ => "unknown",
    }
}

fn bin_op_kind(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add(_) => "add",
        BinOp::Sub(_) => "sub",
        BinOp::Mul(_) => "mul",
        BinOp::Div(_) => "div",
        BinOp::Rem(_) => "rem",
        BinOp::And(_) => "and",
        BinOp::Or(_) => "or",
        BinOp::BitXor(_) => "bitxor",
        BinOp::BitAnd(_) => "bitand",
        BinOp::BitOr(_) => "bitor",
        BinOp::Shl(_) => "shl",
        BinOp::Shr(_) => "shr",
        BinOp::Eq(_) => "eq",
        BinOp::Lt(_) => "lt",
        BinOp::Le(_) => "le",
        BinOp::Ne(_) => "ne",
        BinOp::Ge(_) => "ge",
        BinOp::Gt(_) => "gt",
        BinOp::AddAssign(_) => "add-assign",
        BinOp::SubAssign(_) => "sub-assign",
        BinOp::MulAssign(_) => "mul-assign",
        BinOp::DivAssign(_) => "div-assign",
        BinOp::RemAssign(_) => "rem-assign",
        BinOp::BitXorAssign(_) => "bitxor-assign",
        BinOp::BitAndAssign(_) => "bitand-assign",
        BinOp::BitOrAssign(_) => "bitor-assign",
        BinOp::ShlAssign(_) => "shl-assign",
        BinOp::ShrAssign(_) => "shr-assign",
        _ => "unknown",
    }
}

fn lit_kind(lit: &Lit) -> &'static str {
    match lit {
        Lit::Str(_) => "string",
        Lit::ByteStr(_) => "byte-string",
        Lit::Byte(_) => "byte",
        Lit::Char(_) => "char",
        Lit::Int(_) => "int",
        Lit::Float(_) => "float",
        Lit::Bool(_) => "bool",
        Lit::Verbatim(_) => "verbatim",
        _ => "unknown",
    }
}

fn un_op_kind(op: &UnOp) -> &'static str {
    match op {
        UnOp::Deref(_) => "deref",
        UnOp::Not(_) => "not",
        UnOp::Neg(_) => "neg",
        _ => "unknown",
    }
}
