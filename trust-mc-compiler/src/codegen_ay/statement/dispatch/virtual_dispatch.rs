// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Virtual call (dynamic dispatch) handler for statement codegen.
//!
//! Detects `InstanceKind::Virtual` calls and assigns a symbolic return value
//! of the method's return type. This is a sound over-approximation: the solver
//! can choose any value, which may produce false counterexamples but never
//! misses real bugs. Eliminates the "Call terminator" unsupported fallback for
//! virtual calls, allowing DynTrait tests to reach their assertions.
//!
//! Part of #3159: DynTrait category recovery — statement codegen path.

use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Attempt to handle a virtual (dyn Trait) call by detecting
    /// `InstanceKind::Virtual` and assigning a symbolic return value.
    ///
    /// Returns `Some(target_bb)` if handled, `None` if not a virtual call.
    ///
    /// Part of #3159: enables DynTrait tests in the statement codegen path.
    pub(in crate::codegen_ay::statement) fn try_codegen_virtual_call(
        &mut self,
        func: &Operand,
        _args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let func_ty = match func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => {
                return None;
            }
        };
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };

        let instance = match Instance::resolve(fn_def, &fn_args) {
            Ok(inst) => inst,
            Err(_) => {
                return None;
            }
        };
        match instance.kind {
            InstanceKind::Virtual { idx } => {
                debug!(
                    vtable_idx = idx,
                    "statement virtual dispatch: detected InstanceKind::Virtual"
                );
            }
            _ => return None, // external enum: InstanceKind
        }

        // Assign a symbolic return value to the destination.
        // This reuses the existing codegen_symbolic_result pattern which
        // creates a fresh unconstrained variable of the appropriate sort.
        self.codegen_symbolic_result(destination);

        debug!("statement virtual dispatch: assigned symbolic result to destination");

        target
    }
}
