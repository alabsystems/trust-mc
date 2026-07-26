// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use syn::{ExprBinary, ExprCall, ExprLit, ExprParen, ExprPath, ExprUnary};

#[derive(Debug, Clone, Copy)]
enum NumericOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone, Copy)]
enum CompareOp {
    Lt,
    Le,
    Gt,
    Ge,
}

impl ExprMapper {
    pub(super) fn normalize(
        &mut self,
        expr: &SynExpr,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        match expr {
            SynExpr::Binary(binary) => self.normalize_binary(binary, source),
            SynExpr::Call(call) => self.normalize_call(call, expected_ty, source),
            SynExpr::Lit(lit) => self.normalize_literal(lit, expected_ty, source),
            SynExpr::Paren(ExprParen { expr, .. }) => self.normalize(expr, expected_ty, source),
            SynExpr::Path(path) => self.normalize_path(path, source),
            SynExpr::Unary(unary) => self.normalize_unary(unary, expected_ty, source),
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported syntax node kind `{}`", syn_expr_kind(other)),
            }),
        }
    }

    fn normalize_binary(
        &mut self,
        binary: &ExprBinary,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        match &binary.op {
            BinOp::And(_) => self.normalize_bool_binop(binary, "and", source),
            BinOp::Or(_) => self.normalize_bool_binop(binary, "or", source),
            BinOp::Eq(_) => self.normalize_eq(binary, false, source),
            BinOp::Ne(_) => self.normalize_eq(binary, true, source),
            BinOp::Add(_) => self.normalize_numeric_binop(binary, NumericOp::Add, source),
            BinOp::Sub(_) => self.normalize_numeric_binop(binary, NumericOp::Sub, source),
            BinOp::Mul(_) => self.normalize_numeric_binop(binary, NumericOp::Mul, source),
            BinOp::Div(_) => self.normalize_numeric_binop(binary, NumericOp::Div, source),
            BinOp::Rem(_) => self.normalize_numeric_binop(binary, NumericOp::Rem, source),
            BinOp::Lt(_) => self.normalize_compare(binary, CompareOp::Lt, source),
            BinOp::Le(_) => self.normalize_compare(binary, CompareOp::Le, source),
            BinOp::Gt(_) => self.normalize_compare(binary, CompareOp::Gt, source),
            BinOp::Ge(_) => self.normalize_compare(binary, CompareOp::Ge, source),
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported binary operator kind `{}`", bin_op_kind(other)),
            }),
        }
    }

    fn normalize_bool_binop(
        &mut self,
        binary: &ExprBinary,
        op: &str,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        let left = self.normalize(&binary.left, Some(&TypeInfo::Bool), source)?;
        let right = self.normalize(&binary.right, Some(&TypeInfo::Bool), source)?;
        if !left.ty.is_bool() || !right.ty.is_bool() {
            return Err(IngestError::ExpressionSortMismatch {
                expr: source.to_string(),
                expected: "Bool".to_string(),
                actual: format!("{}, {}", left.ty.describe(), right.ty.describe()),
            });
        }
        Ok(NormalizedExpr { smt: format!("({op} {} {})", left.smt, right.smt), ty: TypeInfo::Bool })
    }

    fn normalize_eq(
        &mut self,
        binary: &ExprBinary,
        is_not_equal: bool,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        let left = self.normalize(&binary.left, None, source)?;
        let right = self.normalize(&binary.right, Some(&left.ty), source)?;
        let (left, right, _) = self.coerce_comparable_pair(left, right, source)?;
        let smt = if is_not_equal {
            format!("(distinct {} {})", left.smt, right.smt)
        } else {
            format!("(= {} {})", left.smt, right.smt)
        };
        Ok(NormalizedExpr { smt, ty: TypeInfo::Bool })
    }

    fn normalize_numeric_binop(
        &mut self,
        binary: &ExprBinary,
        op: NumericOp,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        let left = self.normalize(&binary.left, None, source)?;
        let right = self.normalize(&binary.right, Some(&left.ty), source)?;
        let (left, right, ty) = self.coerce_numeric_pair(left, right, source)?;
        let smt_op = match (&ty, op) {
            (TypeInfo::Int, NumericOp::Add) => "+",
            (TypeInfo::Int, NumericOp::Sub) => "-",
            (TypeInfo::Int, NumericOp::Mul) => "*",
            (TypeInfo::Int, NumericOp::Div) => "div",
            (TypeInfo::Int, NumericOp::Rem) => "mod",
            (TypeInfo::BitVector { .. }, NumericOp::Add) => "bvadd",
            (TypeInfo::BitVector { .. }, NumericOp::Sub) => "bvsub",
            (TypeInfo::BitVector { .. }, NumericOp::Mul) => "bvmul",
            (TypeInfo::BitVector { signed, .. }, NumericOp::Div) => {
                if *signed {
                    "bvsdiv"
                } else {
                    "bvudiv"
                }
            }
            (TypeInfo::BitVector { signed, .. }, NumericOp::Rem) => {
                if *signed {
                    "bvsrem"
                } else {
                    "bvurem"
                }
            }
            _ => {
                return Err(IngestError::UnsupportedExpression {
                    expr: source.to_string(),
                    reason: format!(
                        "numeric operator `{op:?}` is unsupported for {}",
                        ty.describe()
                    ),
                });
            }
        };
        Ok(NormalizedExpr { smt: format!("({smt_op} {} {})", left.smt, right.smt), ty })
    }

    fn normalize_compare(
        &mut self,
        binary: &ExprBinary,
        op: CompareOp,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        let left = self.normalize(&binary.left, None, source)?;
        let right = self.normalize(&binary.right, Some(&left.ty), source)?;
        let (left, right, ty) = self.coerce_numeric_pair(left, right, source)?;
        let smt_op = match (&ty, op) {
            (TypeInfo::Int, CompareOp::Lt) => "<",
            (TypeInfo::Int, CompareOp::Le) => "<=",
            (TypeInfo::Int, CompareOp::Gt) => ">",
            (TypeInfo::Int, CompareOp::Ge) => ">=",
            (TypeInfo::BitVector { signed, .. }, CompareOp::Lt) => {
                if *signed {
                    "bvslt"
                } else {
                    "bvult"
                }
            }
            (TypeInfo::BitVector { signed, .. }, CompareOp::Le) => {
                if *signed {
                    "bvsle"
                } else {
                    "bvule"
                }
            }
            (TypeInfo::BitVector { signed, .. }, CompareOp::Gt) => {
                if *signed {
                    "bvsgt"
                } else {
                    "bvugt"
                }
            }
            (TypeInfo::BitVector { signed, .. }, CompareOp::Ge) => {
                if *signed {
                    "bvsge"
                } else {
                    "bvuge"
                }
            }
            _ => {
                return Err(IngestError::UnsupportedExpression {
                    expr: source.to_string(),
                    reason: format!(
                        "comparison operator `{op:?}` is unsupported for {}",
                        ty.describe()
                    ),
                });
            }
        };
        Ok(NormalizedExpr {
            smt: format!("({smt_op} {} {})", left.smt, right.smt),
            ty: TypeInfo::Bool,
        })
    }

    fn normalize_call(
        &mut self,
        call: &ExprCall,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        let function_name = match &*call.func {
            SynExpr::Path(path) => path_to_name(path)?,
            other => {
                return Err(IngestError::UnsupportedExpression {
                    expr: source.to_string(),
                    reason: format!(
                        "unsupported callable expression kind `{}`",
                        syn_expr_kind(other)
                    ),
                });
            }
        };

        let arg_exprs = call
            .args
            .iter()
            .map(|arg| self.normalize(arg, None, source))
            .collect::<Result<Vec<_>, _>>()?;
        let arg_types = arg_exprs.iter().map(|expr| expr.ty.clone()).collect::<Vec<_>>();
        let return_type = if let Some(existing) = self.functions.get(&function_name) {
            if existing.arg_types != arg_types {
                return Err(IngestError::FunctionSignature {
                    expr: source.to_string(),
                    reason: format!(
                        "function `{function_name}` previously used with arg types {:?}, now {:?}",
                        existing.arg_types, arg_types
                    ),
                });
            }
            existing.return_type.clone()
        } else {
            expected_ty.cloned().ok_or_else(|| IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!(
                    "function `{function_name}` requires a typed context for its result sort"
                ),
            })?
        };

        let signature = FunctionSig {
            name: function_name.clone(),
            param_names: Vec::new(),
            arg_types,
            return_type: return_type.clone(),
            is_recursive: false,
        };
        match self.functions.get(&function_name) {
            Some(existing) if existing.return_type != return_type => {
                return Err(IngestError::FunctionSignature {
                    expr: source.to_string(),
                    reason: format!(
                        "function `{function_name}` previously returned {}, now {}",
                        existing.return_type.describe(),
                        return_type.describe()
                    ),
                });
            }
            None => {
                self.functions.insert(function_name.clone(), signature);
            }
            Some(_) => {}
        }

        Ok(NormalizedExpr {
            smt: format!(
                "({function_name}{})",
                arg_exprs.iter().map(|arg| format!(" {}", arg.smt)).collect::<String>()
            ),
            ty: return_type,
        })
    }

    fn normalize_literal(
        &mut self,
        lit: &ExprLit,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        match &lit.lit {
            Lit::Bool(value) => {
                Ok(NormalizedExpr { smt: value.value.to_string(), ty: TypeInfo::Bool })
            }
            Lit::Int(value) => {
                let digits = value.base10_digits().to_string();
                match expected_ty {
                    Some(TypeInfo::BitVector { width, .. }) => Ok(NormalizedExpr {
                        smt: format!("((_ int2bv {width}) {digits})"),
                        ty: TypeInfo::BitVector { width: *width, signed: false },
                    }),
                    Some(TypeInfo::Int) | None => {
                        Ok(NormalizedExpr { smt: digits, ty: TypeInfo::Int })
                    }
                    Some(other) => Err(IngestError::ExpressionSortMismatch {
                        expr: source.to_string(),
                        expected: other.describe(),
                        actual: "integer literal".to_string(),
                    }),
                }
            }
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported literal kind `{}`", lit_kind(other)),
            }),
        }
    }

    fn normalize_path(&self, path: &ExprPath, source: &str) -> Result<NormalizedExpr, IngestError> {
        let name = path_to_name(path)?;
        let symbol =
            self.variables.get(&name).ok_or_else(|| IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unknown symbol `{name}`"),
            })?;
        Ok(NormalizedExpr { smt: name, ty: symbol.ty.clone() })
    }

    fn normalize_unary(
        &mut self,
        unary: &ExprUnary,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        match &unary.op {
            UnOp::Not(_) => {
                let inner = self.normalize(&unary.expr, Some(&TypeInfo::Bool), source)?;
                if !inner.ty.is_bool() {
                    return Err(IngestError::ExpressionSortMismatch {
                        expr: source.to_string(),
                        expected: "Bool".to_string(),
                        actual: inner.ty.describe(),
                    });
                }
                Ok(NormalizedExpr { smt: format!("(not {})", inner.smt), ty: TypeInfo::Bool })
            }
            UnOp::Neg(_) => {
                let hinted = expected_ty.cloned().unwrap_or(TypeInfo::Int);
                let inner = self.normalize(&unary.expr, Some(&hinted), source)?;
                match inner.ty {
                    TypeInfo::Int => {
                        Ok(NormalizedExpr { smt: format!("(- {})", inner.smt), ty: TypeInfo::Int })
                    }
                    TypeInfo::BitVector { .. } => {
                        Ok(NormalizedExpr { smt: format!("(bvneg {})", inner.smt), ty: inner.ty })
                    }
                    _ => Err(IngestError::UnsupportedExpression {
                        expr: source.to_string(),
                        reason: format!("cannot negate {}", inner.ty.describe()),
                    }),
                }
            }
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported unary operator kind `{}`", un_op_kind(other)),
            }),
        }
    }

    fn coerce_comparable_pair(
        &self,
        left: NormalizedExpr,
        right: NormalizedExpr,
        source: &str,
    ) -> Result<(NormalizedExpr, NormalizedExpr, TypeInfo), IngestError> {
        if left.ty == right.ty {
            return Ok((left.clone(), right, left.ty));
        }
        if left.ty.is_numeric() && right.ty.is_numeric() {
            return self.coerce_numeric_pair(left, right, source);
        }
        Err(IngestError::ExpressionSortMismatch {
            expr: source.to_string(),
            expected: left.ty.describe(),
            actual: right.ty.describe(),
        })
    }

    fn coerce_numeric_pair(
        &self,
        left: NormalizedExpr,
        right: NormalizedExpr,
        source: &str,
    ) -> Result<(NormalizedExpr, NormalizedExpr, TypeInfo), IngestError> {
        match (&left.ty, &right.ty) {
            (TypeInfo::Int, TypeInfo::Int) => Ok((left, right, TypeInfo::Int)),
            (
                TypeInfo::BitVector { width: left_width, signed: left_signed },
                TypeInfo::BitVector { width: right_width, signed: right_signed },
            ) => {
                let target_width = (*left_width).max(*right_width);
                let target_ty = TypeInfo::BitVector {
                    width: target_width,
                    signed: *left_signed || *right_signed,
                };
                let left = self.coerce_to(left, &target_ty, source)?;
                let right = self.coerce_to(right, &target_ty, source)?;
                Ok((left, right, target_ty))
            }
            (TypeInfo::BitVector { .. }, TypeInfo::Int) => {
                let target_ty = left.ty.clone();
                let right = self.coerce_to(right, &target_ty, source)?;
                Ok((left, right, target_ty))
            }
            (TypeInfo::Int, TypeInfo::BitVector { .. }) => {
                let target_ty = right.ty.clone();
                let left = self.coerce_to(left, &target_ty, source)?;
                Ok((left, right, target_ty))
            }
            _ => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!(
                    "expected numeric operands, got {} and {}",
                    left.ty.describe(),
                    right.ty.describe()
                ),
            }),
        }
    }

    fn coerce_to(
        &self,
        expr: NormalizedExpr,
        target_ty: &TypeInfo,
        source: &str,
    ) -> Result<NormalizedExpr, IngestError> {
        if expr.ty == *target_ty {
            return Ok(expr);
        }
        match (&expr.ty, target_ty) {
            (TypeInfo::Int, TypeInfo::BitVector { width, signed }) => Ok(NormalizedExpr {
                smt: format!("((_ int2bv {width}) {})", expr.smt),
                ty: TypeInfo::BitVector { width: *width, signed: *signed },
            }),
            (
                TypeInfo::BitVector { width: from_width, signed: from_signed },
                TypeInfo::BitVector { width: to_width, signed },
            ) if from_width < to_width => {
                let extra_bits = to_width - from_width;
                let extender = if *from_signed { "sign_extend" } else { "zero_extend" };
                Ok(NormalizedExpr {
                    smt: format!("((_ {extender} {extra_bits}) {})", expr.smt),
                    ty: TypeInfo::BitVector { width: *to_width, signed: *signed },
                })
            }
            _ => Err(IngestError::ExpressionSortMismatch {
                expr: source.to_string(),
                expected: target_ty.describe(),
                actual: expr.ty.describe(),
            }),
        }
    }
}
