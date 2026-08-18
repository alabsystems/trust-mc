// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ord / PartialOrd / fat-pointer comparison computation (Part of #2306).
//!
//! Pure computation helpers extracted from `codegen_call_cmp.rs`:
//! - `compute_cmp_result`: top-level dispatch to ord/eq/partial_ord
//! - `compute_ord_cmp`: Ord::cmp ITE chain (lt → −1, eq → 0, else → 1)
//! - `compute_bv128_wide_ptr_ord_cmp`: BV128 packed wide-pointer Ord
//! - `compute_fat_ptr_ord_cmp`: Datatype fat-pointer Ord
//! - `extract_fat_ptr_components`: field extraction from fat-pointer DT
//! - `compute_partial_ord`: PartialOrd::{lt,le,gt,ge}

use ay_bindings::Expr;

use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;
use tracing::warn;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Compute the raw comparison expression for the given stub and operands.
    /// Returns `None` when the sort combination is unsupported.
    /// Part of #4131: `is_raw_ptr` indicates the operands are raw-pointer
    /// comparison args, so BV128 values should decompose into (data, metadata)
    /// instead of being compared as scalar integers.
    pub(super) fn compute_cmp_result(
        stub: StubKind,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        is_raw_ptr: bool,
    ) -> Option<Expr> {
        match stub {
            StubKind::OrdCmp => Self::compute_ord_cmp(lhs, rhs, is_signed, is_raw_ptr),
            StubKind::PrimitivePartialEqEq | StubKind::PrimitivePartialEqNe => {
                let is_eq = stub == StubKind::PrimitivePartialEqEq;
                Self::compute_partial_eq(lhs, rhs, is_signed, is_eq)
            }
            StubKind::PrimitivePartialOrdLt
            | StubKind::PrimitivePartialOrdLe
            | StubKind::PrimitivePartialOrdGt
            | StubKind::PrimitivePartialOrdGe => {
                Self::compute_partial_ord(stub, lhs, rhs, is_signed, is_raw_ptr)
            }
            _other => {
                // partial dispatch: StubKind
                warn!(?_other, "codegen_call_primitive_cmp: unexpected stub — update routing");
                None
            }
        }
    }

    /// Build ITE chain for Ord::cmp: lt -> -1, eq -> 0, else -> 1.
    /// Part of #4131: `is_raw_ptr` routes BV128 wide-pointer operands through
    /// `(data_ptr, metadata)` decomposition instead of scalar integer ordering.
    pub(super) fn compute_ord_cmp(
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        is_raw_ptr: bool,
    ) -> Option<Expr> {
        if lhs.sort().is_bitvec()
            && rhs.sort().is_bitvec()
            && let Some(target_width) =
                lhs.sort().bitvec_width().zip(rhs.sort().bitvec_width()).map(|(l, r)| l.max(r))
        {
            // Part of #4131: BV128 raw pointers are packed wide pointers
            // (low 64 = data ptr, high 64 = metadata). Route through
            // fat-pointer decomposition for correct Rust ordering semantics.
            if is_raw_ptr && target_width == 128 {
                return Self::compute_bv128_wide_ptr_ord_cmp(&lhs, &rhs);
            }
            let (lhs, rhs) = (
                coerce_bitvec_width_safe(
                    lhs,
                    target_width,
                    SignExtension::for_signedness(is_signed),
                ),
                coerce_bitvec_width_safe(
                    rhs,
                    target_width,
                    SignExtension::for_signedness(is_signed),
                ),
            );
            let lt = if is_signed {
                lhs.clone().bvslt(rhs.clone())
            } else {
                lhs.clone().bvult(rhs.clone())
            };
            let eq = lhs.eq(rhs);
            Some(Expr::ite(
                lt,
                Expr::bitvec_const(-1i128, 32),
                Expr::ite(eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
            ))
        } else if lhs.sort().is_int() && rhs.sort().is_int() {
            let lt = lhs.clone().int_lt(rhs.clone());
            let eq = lhs.eq(rhs);
            Some(Expr::ite(
                lt,
                Expr::bitvec_const(-1i128, 32),
                Expr::ite(eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
            ))
        } else if let Some(cmp) = Self::compute_fat_ptr_ord_cmp(&lhs, &rhs) {
            Some(cmp)
        } else {
            None
        }
    }

    /// Part of #4131: Ord::cmp for BV128 packed wide pointers.
    /// Layout: low 64 bits = data pointer, high 64 bits = metadata (length).
    /// Rust semantics: compare data pointer first, metadata as tie-breaker.
    ///
    /// # The tie-break may not be read off the width
    ///
    /// The caller establishes from the MIR type that both operands are raw
    /// pointers, and the `target_width == 128` gate that both occupy a wide
    /// slot. Neither fact says the high half is METADATA: a thin pointer that
    /// `coerce_bitvec_width_safe` widened into that slot carries extension
    /// padding there, and ordering two pointers on padding decides `cmp` on a
    /// value the program never computed. This is the same defect the two
    /// `raw_pointer_*_components` decoders and
    /// `try_translate_inline_wide_pointer_binop` already fixed; #4131 added a
    /// third copy after that sweep.
    ///
    /// `PtrRepr` splits the three cases: both `Fat` keeps the tie-break; both
    /// metadata-free compares the address lane alone (for an extension the high
    /// halves are equal exactly when the low halves are, so this is the same
    /// predicate minus the padding terms); mixed has nothing honest to compare
    /// and declines to the caller's generic lane.
    pub(super) fn compute_bv128_wide_ptr_ord_cmp(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
        let (lhs_data, lhs_meta) = PtrRepr::classify(lhs)?.into_parts();
        let (rhs_data, rhs_meta) = PtrRepr::classify(rhs)?.into_parts();
        let meta = match (lhs_meta, rhs_meta) {
            (Some(l), Some(r)) => Some((l.into_expr(), r.into_expr())),
            (None, None) => None,
            _ => return None,
        };
        let (lhs_ptr, rhs_ptr) = (lhs_data.into_expr(), rhs_data.into_expr());
        let ptr_lt = lhs_ptr.clone().bvult(rhs_ptr.clone());
        let ptr_eq = lhs_ptr.eq(rhs_ptr);
        let tie_cmp = match meta {
            Some((lhs_meta, rhs_meta)) => {
                let meta_lt = lhs_meta.clone().bvult(rhs_meta.clone());
                let meta_eq = lhs_meta.eq(rhs_meta);
                Expr::ite(
                    meta_lt,
                    Expr::bitvec_const(-1i128, 32),
                    Expr::ite(meta_eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
                )
            }
            // No metadata on either side: equal addresses are equal pointers.
            None => Expr::bitvec_const(0, 32),
        };
        Some(Expr::ite(
            ptr_lt,
            Expr::bitvec_const(-1i128, 32),
            Expr::ite(ptr_eq, tie_cmp, Expr::bitvec_const(1, 32)),
        ))
    }

    /// Ord::cmp for fat pointers (Datatype with fld_ptr + fld_len/fld_meta).
    /// Compares data pointer first; on tie, compares metadata.
    pub(super) fn compute_fat_ptr_ord_cmp(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
        let (lhs_ptr, lhs_meta) = Self::extract_fat_ptr_components(lhs)?;
        let (rhs_ptr, rhs_meta) = Self::extract_fat_ptr_components(rhs)?;
        let ptr_lt = lhs_ptr.clone().bvult(rhs_ptr.clone());
        let ptr_eq = lhs_ptr.eq(rhs_ptr);
        let tie_cmp = match (lhs_meta, rhs_meta) {
            (None, None) => Expr::bitvec_const(0, 32),
            (Some(lm), Some(rm)) => {
                let meta_lt = lm.clone().bvult(rm.clone());
                let meta_eq = lm.eq(rm);
                Expr::ite(
                    meta_lt,
                    Expr::bitvec_const(-1i128, 32),
                    Expr::ite(meta_eq, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
                )
            }
            _ => return None,
        };
        Some(Expr::ite(
            ptr_lt,
            Expr::bitvec_const(-1i128, 32),
            Expr::ite(ptr_eq, tie_cmp, Expr::bitvec_const(1, 32)),
        ))
    }

    /// Extract (data_ptr, Option<metadata>) from a fat pointer Datatype.
    pub(super) fn extract_fat_ptr_components(expr: &Expr) -> Option<(Expr, Option<Expr>)> {
        if expr.sort().is_bitvec() {
            return Some((expr.clone(), None));
        }
        let dt = expr.sort().datatype_sort()?;
        let cons = dt.constructors.first()?;
        let ptr_field = cons.fields.iter().find(|f| {
            matches!(f.name.as_str(), "fld_ptr" | "ptr" | "fld_data") && f.sort.is_bitvec()
        })?;
        let ptr = expr.clone().field_select(&dt.name, &ptr_field.name, ptr_field.sort.clone());
        let metadata = cons
            .fields
            .iter()
            .find(|f| {
                matches!(f.name.as_str(), "fld_len" | "fld_vtable" | "fld_meta")
                    && f.sort.is_bitvec()
            })
            .map(|f| expr.clone().field_select(&dt.name, &f.name, f.sort.clone()));
        Some((ptr, metadata))
    }

    /// PartialOrd::{lt, le, gt, ge}.
    /// Part of #4131: `is_raw_ptr` routes BV128 wide pointers through
    /// Ord::cmp decomposition for correct data-ptr-first ordering.
    pub(super) fn compute_partial_ord(
        stub: StubKind,
        lhs: Expr,
        rhs: Expr,
        is_signed: bool,
        is_raw_ptr: bool,
    ) -> Option<Expr> {
        if lhs.sort().is_bitvec()
            && rhs.sort().is_bitvec()
            && let Some(target_width) =
                lhs.sort().bitvec_width().zip(rhs.sort().bitvec_width()).map(|(l, r)| l.max(r))
        {
            // Part of #4131: BV128 raw pointers need wide-pointer decomposition.
            if is_raw_ptr && target_width == 128 {
                if let Some(cmp) = Self::compute_bv128_wide_ptr_ord_cmp(&lhs, &rhs) {
                    let less = Expr::bitvec_const(-1i128, 32);
                    let greater = Expr::bitvec_const(1, 32);
                    return Some(match stub {
                        StubKind::PrimitivePartialOrdLt => cmp.eq(less),
                        StubKind::PrimitivePartialOrdLe => cmp.ne(greater),
                        StubKind::PrimitivePartialOrdGt => cmp.eq(greater),
                        StubKind::PrimitivePartialOrdGe => cmp.ne(less),
                        _other => return None,
                    });
                }
            }
            let lhs = coerce_bitvec_width_safe(
                lhs,
                target_width,
                SignExtension::for_signedness(is_signed),
            );
            let rhs = coerce_bitvec_width_safe(
                rhs,
                target_width,
                SignExtension::for_signedness(is_signed),
            );
            Some(match stub {
                StubKind::PrimitivePartialOrdLt => {
                    if is_signed {
                        lhs.bvslt(rhs)
                    } else {
                        lhs.bvult(rhs)
                    }
                }
                StubKind::PrimitivePartialOrdLe => {
                    if is_signed {
                        lhs.bvsle(rhs)
                    } else {
                        lhs.bvule(rhs)
                    }
                }
                StubKind::PrimitivePartialOrdGt => {
                    if is_signed {
                        lhs.bvsgt(rhs)
                    } else {
                        lhs.bvugt(rhs)
                    }
                }
                StubKind::PrimitivePartialOrdGe => {
                    if is_signed {
                        lhs.bvsge(rhs)
                    } else {
                        lhs.bvuge(rhs)
                    }
                }
                _other => {
                    // partial dispatch: StubKind
                    warn!(?_other, "codegen_call_primitive_cmp: unexpected PartialOrd stub");
                    return None;
                }
            })
        } else if lhs.sort().is_int() && rhs.sort().is_int() {
            Some(match stub {
                StubKind::PrimitivePartialOrdLt => lhs.int_lt(rhs),
                StubKind::PrimitivePartialOrdLe => lhs.int_le(rhs),
                StubKind::PrimitivePartialOrdGt => lhs.int_gt(rhs),
                StubKind::PrimitivePartialOrdGe => lhs.int_ge(rhs),
                _other => {
                    // partial dispatch: StubKind
                    warn!(?_other, "codegen_call_primitive_cmp: unexpected PartialOrd stub (int)");
                    return None;
                }
            })
        } else if let Some(cmp) = Self::compute_fat_ptr_ord_cmp(&lhs, &rhs) {
            // Part of #4030: fat pointer PartialOrd via Ord::cmp decomposition.
            let less = Expr::bitvec_const(-1i128, 32);
            let greater = Expr::bitvec_const(1, 32);
            Some(match stub {
                StubKind::PrimitivePartialOrdLt => cmp.eq(less),
                StubKind::PrimitivePartialOrdLe => cmp.ne(greater),
                StubKind::PrimitivePartialOrdGt => cmp.eq(greater),
                StubKind::PrimitivePartialOrdGe => cmp.ne(less),
                _other => return None,
            })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Sort;

    #[test]
    fn bv128_wide_pointer_ordering_decomposes_data_and_metadata() {
        let lhs = Expr::var("lhs_wide_ptr", Sort::bitvec(128));
        let rhs = Expr::var("rhs_wide_ptr", Sort::bitvec(128));

        let cmp = ChcCtx::compute_bv128_wide_ptr_ord_cmp(&lhs, &rhs)
            .expect("BV128 wide-pointer comparison should lower");
        let smt = cmp.to_string();

        assert!(
            smt.contains("extract 63 0"),
            "wide-pointer ordering should compare low 64-bit data pointers first: {smt}"
        );
        assert!(
            smt.contains("extract 127 64"),
            "wide-pointer ordering should use high 64-bit metadata as tie-breaker: {smt}"
        );
        assert!(
            smt.contains("bvult"),
            "wide-pointer ordering should use unsigned pointer/metadata order: {smt}"
        );
    }
}
