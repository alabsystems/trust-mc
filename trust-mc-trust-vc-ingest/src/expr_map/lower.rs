// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_frontend::{Command, Constant, Index, Term, parse};
use num_bigint::BigInt;

impl ExprMapper {
    pub(super) fn lower_from_smt(
        &mut self,
        smt_expr: &str,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<Expr, IngestError> {
        let script = format!("(assert {smt_expr})");
        let commands = parse(&script).map_err(|err| IngestError::ExpressionParse {
            expr: source.to_string(),
            reason: err.to_string(),
        })?;
        let term = match commands.as_slice() {
            [Command::Assert(term)] => term,
            other => {
                return Err(IngestError::ExpressionParse {
                    expr: source.to_string(),
                    reason: format!("unexpected SMT-LIB command sequence: {other:?}"),
                });
            }
        };
        self.lower_term(term, expected_ty, source)
    }

    fn lower_term(
        &mut self,
        term: &Term,
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<Expr, IngestError> {
        match term {
            Term::Const(constant) => self.lower_constant(constant, source),
            Term::Symbol(name) => {
                let symbol =
                    self.variables.get(name).ok_or_else(|| IngestError::UnsupportedExpression {
                        expr: source.to_string(),
                        reason: format!("unknown symbol `{name}`"),
                    })?;
                Ok(Expr::var(name.clone(), symbol.ty.sort()))
            }
            Term::App(name, args) => self.lower_app(name, args, expected_ty, source),
            Term::IndexedApp(name, indices, args) => {
                // ay-frontend moved indexed-app indices from String to typed
                // `Index` tokens; lower_indexed_app matches the typed tokens
                // (Numeral/Symbol/…) directly.
                self.lower_indexed_app(name, indices, args, source)
            }
            Term::Annotated(body, _) => self.lower_term(body, expected_ty, source),
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported normalized SMT term: {other:?}"),
            }),
        }
    }

    fn lower_constant(&self, constant: &Constant, source: &str) -> Result<Expr, IngestError> {
        match constant {
            Constant::True => Ok(Expr::true_()),
            Constant::False => Ok(Expr::false_()),
            Constant::Numeral(value) => Ok(Expr::int_const(parse_bigint(value, source)?)),
            Constant::Hexadecimal(bits) => {
                let digits =
                    bits.strip_prefix("#x").ok_or_else(|| IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid hexadecimal literal `{bits}`"),
                    })?;
                let width = digits
                    .len()
                    .checked_mul(4)
                    .and_then(|width| u32::try_from(width).ok())
                    .filter(|width| *width > 0)
                    .ok_or_else(|| IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid hexadecimal literal width for `{bits}`"),
                    })?;
                let value = BigInt::parse_bytes(digits.as_bytes(), 16).ok_or_else(|| {
                    IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid hexadecimal literal `{bits}`"),
                    }
                })?;
                Ok(Expr::bitvec_const(value, width))
            }
            Constant::Binary(bits) => {
                let digits =
                    bits.strip_prefix("#b").ok_or_else(|| IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid binary literal `{bits}`"),
                    })?;
                let width = u32::try_from(digits.len())
                    .ok()
                    .filter(|width| *width > 0)
                    .ok_or_else(|| IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid binary literal width for `{bits}`"),
                    })?;
                let value = BigInt::parse_bytes(digits.as_bytes(), 2).ok_or_else(|| {
                    IngestError::ExpressionParse {
                        expr: source.to_string(),
                        reason: format!("invalid binary literal `{bits}`"),
                    }
                })?;
                Ok(Expr::bitvec_const(value, width))
            }
            other => Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("unsupported constant in normalized SMT: {other:?}"),
            }),
        }
    }

    fn lower_app(
        &mut self,
        name: &str,
        args: &[Term],
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<Expr, IngestError> {
        match name {
            "not" => {
                unary(self.lower_args(args, Some(&TypeInfo::Bool), source)?, source, Expr::not)
            }
            "and" => Ok(Expr::and_many(self.lower_args(args, Some(&TypeInfo::Bool), source)?)),
            "or" => Ok(Expr::or_many(self.lower_args(args, Some(&TypeInfo::Bool), source)?)),
            "=" => binary(self.lower_args(args, None, source)?, source, Expr::eq),
            "distinct" => Ok(Expr::distinct(self.lower_args(args, None, source)?)),
            "ite" => self.lower_ite(args, source),
            "+" => binary(self.lower_args(args, None, source)?, source, Expr::int_add),
            "-" => match self.lower_args(args, None, source)?.as_slice() {
                [expr] => Ok(expr.clone().int_neg()),
                [left, right] => Ok(left.clone().int_sub(right.clone())),
                _ => Err(IngestError::UnsupportedExpression {
                    expr: source.to_string(),
                    reason: "integer subtraction expects one or two operands".to_string(),
                }),
            },
            "*" => binary(self.lower_args(args, None, source)?, source, Expr::int_mul),
            "div" => binary(self.lower_args(args, None, source)?, source, Expr::int_div),
            "mod" => binary(self.lower_args(args, None, source)?, source, Expr::int_mod),
            "bvadd" => binary(self.lower_args(args, None, source)?, source, Expr::bvadd),
            "bvsub" => binary(self.lower_args(args, None, source)?, source, Expr::bvsub),
            "bvmul" => binary(self.lower_args(args, None, source)?, source, Expr::bvmul),
            "bvudiv" => binary(self.lower_args(args, None, source)?, source, Expr::bvudiv),
            "bvsdiv" => binary(self.lower_args(args, None, source)?, source, Expr::bvsdiv),
            "bvurem" => binary(self.lower_args(args, None, source)?, source, Expr::bvurem),
            "bvsrem" => binary(self.lower_args(args, None, source)?, source, Expr::bvsrem),
            "bvneg" => unary(self.lower_args(args, None, source)?, source, Expr::bvneg),
            "bvult" => binary(self.lower_args(args, None, source)?, source, Expr::bvult),
            "bvule" => binary(self.lower_args(args, None, source)?, source, Expr::bvule),
            "bvugt" => binary(self.lower_args(args, None, source)?, source, Expr::bvugt),
            "bvuge" => binary(self.lower_args(args, None, source)?, source, Expr::bvuge),
            "bvslt" => binary(self.lower_args(args, None, source)?, source, Expr::bvslt),
            "bvsle" => binary(self.lower_args(args, None, source)?, source, Expr::bvsle),
            "bvsgt" => binary(self.lower_args(args, None, source)?, source, Expr::bvsgt),
            "bvsge" => binary(self.lower_args(args, None, source)?, source, Expr::bvsge),
            "<" => binary(self.lower_args(args, None, source)?, source, Expr::int_lt),
            "<=" => binary(self.lower_args(args, None, source)?, source, Expr::int_le),
            ">" => binary(self.lower_args(args, None, source)?, source, Expr::int_gt),
            ">=" => binary(self.lower_args(args, None, source)?, source, Expr::int_ge),
            other => {
                let lowered = self.lower_args(args, None, source)?;
                let arg_types = lowered
                    .iter()
                    .map(|expr| TypeInfo::from_sort(expr.sort()))
                    .collect::<Result<Vec<_>, _>>()?;
                let signature = if let Some(existing) = self.functions.get(other) {
                    existing.clone()
                } else {
                    let return_type =
                        expected_ty.cloned().ok_or_else(|| IngestError::FunctionSignature {
                            expr: source.to_string(),
                            reason: format!(
                                "function `{other}` requires a typed context for its result sort"
                            ),
                        })?;
                    let sig = FunctionSig {
                        name: other.to_string(),
                        param_names: Vec::new(),
                        arg_types: arg_types.clone(),
                        return_type,
                        is_recursive: false,
                    };
                    self.functions.insert(other.to_string(), sig.clone());
                    sig
                };
                if signature.arg_types.len() != lowered.len() {
                    return Err(IngestError::FunctionSignature {
                        expr: source.to_string(),
                        reason: format!(
                            "function `{other}` expects {} args, got {}",
                            signature.arg_types.len(),
                            lowered.len()
                        ),
                    });
                }
                for (idx, (expected, actual)) in
                    signature.arg_types.iter().zip(arg_types.iter()).enumerate()
                {
                    if expected != actual {
                        return Err(IngestError::FunctionSignature {
                            expr: source.to_string(),
                            reason: format!(
                                "function `{other}` arg {idx} expects {}, got {}",
                                expected.describe(),
                                actual.describe()
                            ),
                        });
                    }
                }
                Ok(Expr::func_app_with_sort(other, lowered, signature.return_type.sort()))
            }
        }
    }

    fn lower_ite(&mut self, args: &[Term], source: &str) -> Result<Expr, IngestError> {
        let [cond, then_term, else_term] = args else {
            return Err(IngestError::UnsupportedExpression {
                expr: source.to_string(),
                reason: format!("ite expects 3 operands, got {}", args.len()),
            });
        };
        let cond = self.lower_term(cond, Some(&TypeInfo::Bool), source)?;
        let then_expr = self.lower_term(then_term, None, source)?;
        let else_expr =
            self.lower_term(else_term, Some(&TypeInfo::from_sort(then_expr.sort())?), source)?;
        if then_expr.sort() != else_expr.sort() {
            return Err(IngestError::ExpressionSortMismatch {
                expr: source.to_string(),
                expected: then_expr.sort().to_string(),
                actual: else_expr.sort().to_string(),
            });
        }
        Ok(Expr::ite(cond, then_expr, else_expr))
    }

    fn lower_args(
        &mut self,
        args: &[Term],
        expected_ty: Option<&TypeInfo>,
        source: &str,
    ) -> Result<Vec<Expr>, IngestError> {
        args.iter().map(|arg| self.lower_term(arg, expected_ty, source)).collect()
    }

    fn lower_indexed_app(
        &mut self,
        name: &str,
        indices: &[Index],
        args: &[Term],
        source: &str,
    ) -> Result<Expr, IngestError> {
        let lowered = args
            .iter()
            .map(|arg| self.lower_term(arg, None, source))
            .collect::<Result<Vec<_>, _>>()?;
        let unsupported = || IngestError::UnsupportedExpression {
            expr: source.to_string(),
            reason: format!(
                "unsupported indexed application `{name}` with {} indices and {} operands",
                indices.len(),
                args.len()
            ),
        };
        // Dispatch on each slice's shape on its own, never on a tuple of
        // slices: every operand and index is bound by the length test that
        // selects its arm, and the literal's digits come from `strip_prefix`
        // rather than a re-slice of `name`.
        match indices {
            [Index::Numeral(width)] => match lowered.as_slice() {
                [] => {
                    let Some(digits) = bitvector_literal_digits(name) else {
                        return Err(unsupported());
                    };
                    let value = parse_bigint(digits, source)?;
                    let width = parse_u32(width, source, "bitvector literal width")?;
                    if width == 0 {
                        return Err(IngestError::ExpressionParse {
                            expr: source.to_string(),
                            reason: "bitvector literal width must be greater than zero".to_string(),
                        });
                    }
                    Ok(Expr::bitvec_const(value, width))
                }
                [expr] => match name {
                    "int2bv" => {
                        let width = parse_u32(width, source, "int2bv width")?;
                        expr.clone()
                            .try_int2bv(width)
                            .map_err(|err| indexed_sort_error(source, err))
                    }
                    "zero_extend" => {
                        let extra = parse_u32(width, source, "zero_extend width")?;
                        expr.clone()
                            .try_zero_extend(extra)
                            .map_err(|err| indexed_sort_error(source, err))
                    }
                    "sign_extend" => {
                        let extra = parse_u32(width, source, "sign_extend width")?;
                        expr.clone()
                            .try_sign_extend(extra)
                            .map_err(|err| indexed_sort_error(source, err))
                    }
                    _ => Err(unsupported()),
                },
                _ => Err(unsupported()),
            },
            [Index::Numeral(high), Index::Numeral(low)] if name == "extract" => {
                match lowered.as_slice() {
                    [expr] => {
                        let high = parse_u32(high, source, "extract high")?;
                        let low = parse_u32(low, source, "extract low")?;
                        expr.clone()
                            .try_extract(high, low)
                            .map_err(|err| indexed_sort_error(source, err))
                    }
                    _ => Err(unsupported()),
                }
            }
            _ => Err(unsupported()),
        }
    }
}

/// The decimal digits of an SMT-LIB `bv<digits>` literal name, or `None` when
/// `name` is not one.
fn bitvector_literal_digits(name: &str) -> Option<&str> {
    name.strip_prefix("bv")
        .filter(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

fn binary(
    mut args: Vec<Expr>,
    source: &str,
    op: impl FnOnce(Expr, Expr) -> Expr,
) -> Result<Expr, IngestError> {
    let right = args.pop().ok_or_else(|| IngestError::UnsupportedExpression {
        expr: source.to_string(),
        reason: "binary operation missing right-hand operand".to_string(),
    })?;
    let left = args.pop().ok_or_else(|| IngestError::UnsupportedExpression {
        expr: source.to_string(),
        reason: "binary operation missing left-hand operand".to_string(),
    })?;
    if !args.is_empty() {
        return Err(IngestError::UnsupportedExpression {
            expr: source.to_string(),
            reason: "binary operation received more than two operands".to_string(),
        });
    }
    Ok(op(left, right))
}

fn unary(
    mut args: Vec<Expr>,
    source: &str,
    op: impl FnOnce(Expr) -> Expr,
) -> Result<Expr, IngestError> {
    let expr = args.pop().ok_or_else(|| IngestError::UnsupportedExpression {
        expr: source.to_string(),
        reason: "unary operation missing operand".to_string(),
    })?;
    if !args.is_empty() {
        return Err(IngestError::UnsupportedExpression {
            expr: source.to_string(),
            reason: "unary operation received more than one operand".to_string(),
        });
    }
    Ok(op(expr))
}

fn parse_bigint(value: &str, source: &str) -> Result<BigInt, IngestError> {
    BigInt::parse_bytes(value.as_bytes(), 10).ok_or_else(|| IngestError::ExpressionParse {
        expr: source.to_string(),
        reason: format!("invalid integer literal `{value}`"),
    })
}

fn indexed_sort_error(source: &str, err: ay_bindings::SortError) -> IngestError {
    IngestError::UnsupportedExpression {
        expr: source.to_string(),
        reason: format!("invalid indexed application: {err}"),
    }
}

fn parse_u32(value: &str, source: &str, what: &str) -> Result<u32, IngestError> {
    value.parse::<u32>().map_err(|err| IngestError::ExpressionParse {
        expr: source.to_string(),
        reason: format!("invalid `{what}` `{value}`: {err}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_merge_contract::SortMeta;

    #[test]
    fn structural_bv_literal_does_not_collide_with_quoted_symbol() {
        let quoted_name = "(_ bv5 8)";
        let variable = MappedVar {
            name: quoted_name.to_string(),
            sort: Sort::bitvec(8),
            meta: SortMeta::BitVector { width: 8, signed: false },
        };
        let mut mapper = ExprMapper::new(&[variable]);

        let literal = mapper
            .lower_from_smt("(_ bv5 8)", None, "(_ bv5 8)")
            .expect("structural bitvector literal should lower");
        let quoted = mapper
            .lower_from_smt("|(_ bv5 8)|", None, "|(_ bv5 8)|")
            .expect("quoted same-spelled variable should lower as a variable");

        assert_eq!(literal, Expr::bitvec_const(BigInt::from(5_u8), 8));
        assert_eq!(quoted, Expr::var(quoted_name, Sort::bitvec(8)));
        assert_ne!(literal, quoted);
    }

    #[test]
    fn mapped_variable_types_match_sort_meta_translation() {
        let metas = [
            SortMeta::Bool,
            SortMeta::MathInt,
            SortMeta::Real,
            SortMeta::BitVector { width: 8, signed: true },
            SortMeta::BitVector { width: 32, signed: false },
            SortMeta::Opaque { name: "T".to_string() },
            SortMeta::Seq { elem: Box::new(SortMeta::MathInt) },
            SortMeta::Set { elem: Box::new(SortMeta::Bool) },
        ];
        for meta in metas {
            let sort = crate::translate_sort(&meta).expect("fixture sort should translate");
            let var = MappedVar { name: "v".to_string(), sort: sort.clone(), meta: meta.clone() };
            let via_meta = TypeInfo::from_sort_meta(&meta).expect("fixture sort should map");
            assert_eq!(TypeInfo::from_mapped_var(&var), via_meta, "{meta:?}");
            assert_eq!(via_meta.sort(), sort, "{meta:?}");
        }
        assert_eq!(
            TypeInfo::from_sort(&Sort::bitvec(16)).expect("bitvector sort should map"),
            TypeInfo::BitVector { width: 16, signed: false }
        );
        assert_eq!(
            TypeInfo::from_sort(&Sort::real()).expect("real sort should map"),
            TypeInfo::Other(Sort::real())
        );
    }

    #[test]
    fn indexed_applications_require_exact_numeral_indices() {
        for smt in [
            "((_ zero_extend |1|) #b0)",
            "((_ zero_extend 1 2) #b0)",
            "((_ extract 7 |0|) #xff)",
            "((_ extract 7 0 0) #xff)",
        ] {
            let err = ExprMapper::new(&[])
                .lower_from_smt(smt, None, smt)
                .expect_err("non-numeral or extra indices must fail closed");
            assert!(
                matches!(err, IngestError::UnsupportedExpression { .. }),
                "unexpected error for {smt}: {err}"
            );
        }
    }

    #[test]
    fn prefixed_bitvector_constants_lower_with_their_digit_width() {
        let mut mapper = ExprMapper::new(&[]);

        let binary =
            mapper.lower_from_smt("#b0101", None, "#b0101").expect("binary literal should lower");
        let hexadecimal =
            mapper.lower_from_smt("#x0f", None, "#x0f").expect("hexadecimal literal should lower");

        assert_eq!(binary, Expr::bitvec_const(BigInt::from(5_u8), 4));
        assert_eq!(hexadecimal, Expr::bitvec_const(BigInt::from(15_u8), 8));
    }

    #[test]
    fn zero_width_bitvectors_fail_closed_without_panicking() {
        for smt in ["(_ bv5 0)", "((_ int2bv 0) 5)"] {
            ExprMapper::new(&[])
                .lower_from_smt(smt, None, smt)
                .expect_err("zero-width bitvectors must be rejected");
        }
    }

    #[test]
    fn bitvector_literal_digits_accepts_only_bv_then_decimal_digits() {
        assert_eq!(bitvector_literal_digits("bv5"), Some("5"));
        assert_eq!(bitvector_literal_digits("bv0042"), Some("0042"));
        for name in ["bv", "bvx", "bv5a", "b5", "int2bv", ""] {
            assert_eq!(bitvector_literal_digits(name), None, "`{name}` is not a bv literal");
        }
    }

    #[test]
    fn indexed_applications_lower_each_supported_shape() {
        let variable = MappedVar {
            name: "x".to_string(),
            sort: Sort::bitvec(8),
            meta: SortMeta::BitVector { width: 8, signed: false },
        };
        let mut mapper = ExprMapper::new(&[variable]);
        let x = Expr::var("x", Sort::bitvec(8));
        let lower = |mapper: &mut ExprMapper, smt: &str| {
            mapper.lower_from_smt(smt, None, smt).unwrap_or_else(|err| panic!("{smt}: {err}"))
        };

        assert_eq!(lower(&mut mapper, "(_ bv7 4)"), Expr::bitvec_const(BigInt::from(7_u8), 4));
        assert_eq!(
            lower(&mut mapper, "((_ zero_extend 8) x)"),
            x.clone().try_zero_extend(8).expect("zero_extend")
        );
        assert_eq!(
            lower(&mut mapper, "((_ sign_extend 8) x)"),
            x.clone().try_sign_extend(8).expect("sign_extend")
        );
        assert_eq!(
            lower(&mut mapper, "((_ extract 3 0) x)"),
            x.clone().try_extract(3, 0).expect("extract")
        );
        assert_eq!(
            lower(&mut mapper, "((_ int2bv 8) 5)"),
            Expr::int_const(5).try_int2bv(8).expect("int2bv")
        );
    }

    #[test]
    fn indexed_applications_with_the_wrong_shape_are_unsupported() {
        for smt in [
            // a bv literal takes no operands, and only a `bv<digits>` name is one
            "((_ bv5 8) #b0)",
            "(_ bvx 8)",
            "(_ zero_extend 8)",
            // unary indexed operators take exactly one operand
            "((_ zero_extend 1) #b0 #b1)",
            "((_ int2bv 8) 1 2)",
            // extract takes two indices, and only extract takes two
            "((_ extract 7) #xff)",
            "((_ zero_extend 1 2) #b0)",
            "((_ frobnicate 1) #b0)",
        ] {
            let err = ExprMapper::new(&[])
                .lower_from_smt(smt, None, smt)
                .expect_err("a wrong-shaped indexed application must fail closed");
            assert!(
                matches!(err, IngestError::UnsupportedExpression { .. }),
                "unexpected error for {smt}: {err}"
            );
        }
    }
}
