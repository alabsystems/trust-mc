// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared pointer-address normalization helpers for CHC Mem-track deref paths.

use ay_bindings::{Expr, ExprValue};
use tracing::warn;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;

/// True when `expr` is a symbolic sub-pointer-width VALUE widened into
/// pointer width (`zero_extend`/`sign_extend` of a narrow non-constant).
///
/// fc-interior-mut: such expressions are never real storage addresses — the
/// split-pointer model's obj_id (upper 32 bits) is forced to 0/sign-fill,
/// i.e. the null object. They arise when ref-dematerialization launders a
/// flattened referent VALUE (e.g. a Cell<u32> payload) through a
/// pointer-sorted local. Constant widenings are exempt: literal addresses
/// (e.g. `0 as *const T`) keep the legacy null-deref check behavior.
pub(in crate::codegen_ay::chc) fn is_value_widened_into_address(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. } => {
            inner.sort().bitvec_width().is_some_and(|w| w < POINTER_WIDTH)
                && !matches!(inner.value(), ExprValue::BitVecConst { .. })
        }
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Reduce wide or wrapped pointer expressions to the thin storage-address
    /// lane used by Mem-track byte-offset arithmetic.
    pub(in crate::codegen_ay::chc) fn normalize_deref_address_expr(
        &self,
        pointer_expr: Expr,
        pointer_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let addr_expr = self.extract_pointer_storage_expr(&pointer_expr).unwrap_or(pointer_expr);
        let Some(addr_width) = addr_expr.sort().bitvec_width() else {
            warn!(
                ?pointer_ty,
                sort = ?addr_expr.sort(),
                "CHC: translate_ref_to_address - deref produced non-bitvec address"
            );
            return None;
        };
        // fc-interior-mut: NEVER widen a sub-pointer-width expression into an
        // address. A narrow bitvec here is a dematerialized referent VALUE
        // (e.g. the flattened u32 payload of a Cell reached through contract
        // instrumentation), not a pointer; zero-extending it fabricates
        // obj_id=0 provenance whose deref checks are decided by the cell's
        // arbitrary payload (spurious Genuine CTREX) — or are silently checked
        // at the wrong object. Returning None routes every caller to its
        // existing sound fallback/demoted lane (OffsetProvenanceUnresolved
        // discipline: recover a real address or fail closed, never fabricate).
        if addr_width < POINTER_WIDTH {
            warn!(
                ?pointer_ty,
                addr_width,
                "CHC: translate_ref_to_address - refusing to widen sub-pointer-width \
                 value into an address (value-as-address fabrication)"
            );
            return None;
        }
        // Same fabrication, pre-widened upstream (e.g. an assignment coercion
        // already zero-extended the flattened value into a pointer-sorted
        // local): the shape is a symbolic narrow value under a widening node,
        // which forces obj_id = 0 (null object) — never a real address.
        if is_value_widened_into_address(&addr_expr) {
            warn!(
                ?pointer_ty,
                "CHC: translate_ref_to_address - refusing pre-widened value-as-address \
                 (zero/sign-extended sub-pointer-width value, obj_id forced to 0)"
            );
            return None;
        }
        Some(if addr_width == POINTER_WIDTH {
            addr_expr
        } else {
            // Wider-than-pointer (fat-pointer wrappers): keep the existing
            // thin-lane extraction behavior.
            coerce_bitvec_width_safe(addr_expr, POINTER_WIDTH, SignExtension::ZeroExtend)
        })
    }
}
