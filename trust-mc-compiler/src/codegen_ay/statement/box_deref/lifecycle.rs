// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A genuine Global Box with empty pointee glue only deallocates its storage.
//! User destructor effects stay with the existing real-body/refusal path.

use super::*;
use crate::codegen_ay::shared::native_box_raw::{
    native_bmc_box_drop_is_modeled, native_thin_global_box_pointee,
};
use rustc_public::mir::Place;

impl StatementCodegen<'_, '_, '_> {
    pub(in crate::codegen_ay::statement) fn try_native_box_drop(&mut self, place: &Place) -> bool {
        let Some(ty) = place.ty(self.body.locals()).ok() else { return false };
        if self.is_native_box_target(ty)
            && native_thin_global_box_pointee(self.ctx.tcx, ty).is_none()
        {
            self.ctx.unsupported_with_fallback("BoxAllocatorMetadata",
                "native Box drop has unmodeled allocator or fat metadata; retain its real-body/refusal path");
            return false;
        }
        if !native_bmc_box_drop_is_modeled(self.ctx.tcx, ty) {
            return false;
        }
        let pointee = native_thin_global_box_pointee(self.ctx.tcx, ty).unwrap();
        if crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(
            self.ctx.tcx,
        ) {
            self.ctx.unsupported_with_fallback(
                "BoxGlobalAllocator",
                "Box drop must execute the user global allocator's body effects",
            );
            return true;
        }
        let result = (|| {
            let value = self.codegen_operand(&Operand::Move(place.clone()))?;
            let pointer = self.box_pointer_value(&value)?;
            let checks = self.native_box_pointer_checks(&pointer, pointee)?;
            let layout = LayoutOf::new(pointee);
            Some((pointer, checks, layout.size_of()?, layout.align_of()?))
        })();
        let Some((pointer, checks, size, align)) = result else {
            self.ctx.unsupported_with_fallback(
                "BoxDropValidity",
                "native Box drop has no checked pointer origin and metadata",
            );
            return true;
        };
        for check in checks {
            self.record_violation_guarded_with_message(
                check.not(),
                "box_deref_validity",
                Some("Box drop source validity".into()),
            );
        }
        if size != 0 {
            self.ctx.heap_dealloc_on_path(
                pointer,
                Expr::bitvec_const(size as u64, 64),
                Expr::bitvec_const(align as u64, 64),
                self.store_path_condition(),
            );
        }
        true
    }
}
