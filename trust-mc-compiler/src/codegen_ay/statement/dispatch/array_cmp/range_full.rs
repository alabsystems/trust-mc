// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! RangeFull identity handling for array/slice comparison dispatch.

use rustc_public::mir::{BasicBlockIdx, LocalDecl, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::statement::{IntoOption, StatementCodegen};
use crate::rustc_public::CrateDef;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle `Index::index(slice, RangeFull)` as identity.
    pub(super) fn try_codegen_range_full_index(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let src = args.first()?;
        let value = self.get_value_through_ref(src).or_else(|| self.codegen_operand(src))?;
        let dest_base = self.ssa_base_name(destination);
        self.env_update(dest_base, value);
        target
    }
}

pub(super) fn is_range_full_index_call(
    callee_path: &str,
    args: &[Operand],
    locals: &[LocalDecl],
) -> bool {
    if !(callee_path.contains("Index") && callee_path.ends_with("index")) || args.len() < 2 {
        return false;
    }

    args[1].ty(locals).into_option().is_some_and(|ty| {
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "RangeFull"
        )
    })
}
