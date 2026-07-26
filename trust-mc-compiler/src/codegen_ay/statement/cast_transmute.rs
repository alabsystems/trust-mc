// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC transmute-specific cast handler.
//!
//! Part of #3809: layout-sensitive cross-ADT transmutes must fail closed
//! instead of using generic DT→DT structural coercion (which assumes
//! field-by-field identity and is unsound when rustc may reorder fields).
//!
//! Safe cases (same sort, BV↔BV, single-field wrappers, repr(C) structs
//! with matching layouts) still delegate to `codegen_cast(...)`.

use ay_bindings::{Expr, SortInner};
use rustc_public::mir::Operand;
use rustc_public::ty::Ty;
use tracing::warn;

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::shared::transmute_layout::transmute_requires_layout_fallback;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Transmute-specific cast entrypoint for the BMC backend.
    ///
    /// Preserves existing precise behavior for same-sort and layout-compatible
    /// cases, but blocks layout-sensitive multi-field cross-ADT transmutes by
    /// recording `unsupported("Cast", ...)` and returning `None`.
    pub(super) fn codegen_transmute_cast(
        &mut self,
        operand: &Operand,
        target_ty: Ty,
    ) -> Option<Expr> {
        let target_sort = Self::infer_sort_from_ty(target_ty)?;
        let src_ty = operand.ty(self.body.locals()).into_option();

        // Fast path: if we can determine both sorts without full codegen,
        // check for layout-sensitive cross-ADT transmutes before proceeding.
        if let Some(src_ty) = src_ty {
            let src_sort = Self::infer_sort_from_ty(src_ty);
            if let Some(ref ss) = src_sort {
                // Same sort → identity, no layout concern.
                if *ss == target_sort {
                    return self.codegen_operand(operand);
                }
                // Both DT with different names → check layout compatibility.
                if let (SortInner::Datatype(src_dt), SortInner::Datatype(tgt_dt)) =
                    (ss.inner(), target_sort.inner())
                {
                    if src_dt.name != tgt_dt.name
                        && transmute_requires_layout_fallback(
                            src_ty,
                            target_ty,
                            ss,
                            &target_sort,
                            |ty| ty,
                        )
                    {
                        warn!(
                            src = %src_dt.name,
                            tgt = %tgt_dt.name,
                            "BMC: layout-sensitive cross-ADT transmute blocked (Part of #3809)"
                        );
                        self.ctx.unsupported(
                            "Cast",
                            format!(
                                "transmute layout-sensitive: {} → {}",
                                src_dt.name, tgt_dt.name
                            ),
                        );
                        return None;
                    }
                }
            }
        }

        // All other cases: delegate to the existing generic cast handler.
        // This covers same-sort identity, BV↔BV, BV↔DT (niche opts),
        // single-field wrappers, and repr(C) structs with matching layouts.
        self.codegen_cast(operand, target_ty)
    }
}
