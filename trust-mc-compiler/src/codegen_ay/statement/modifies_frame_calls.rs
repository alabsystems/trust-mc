// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06 (BMC): stores made inside call handlers that inline no body.
//!
//! `statement::modifies_frame` classifies every store the register model
//! encodes through a deref, a call destination or a discriminant write. A call
//! that a stub, Kani model, abstracted fallback, virtual-dispatch havoc or
//! foreign effect frame encodes directly never exposes its stores that way:
//! `v.push(7)` under `#[kani::modifies(&p.a)]` verified SUCCESSFUL with a clean
//! qualifier (negative/modifies_frame_residual.rs::vec_push_outside_must_fail),
//! as did `String::push` and `Vec::pop`.
//!
//! So after such a handler runs inside a frame, every argument that can carry
//! a writable pointer is treated as a possible store to what it points at:
//! - `&mut T` and `*mut T`, and `&T` whose `T` is not provably `Freeze`
//!   (interior mutability), at the top level or as the single pointer field of
//!   a wrapper passed by value (`Pin<&mut T>`);
//! - a pointee the footprint covers is certified (a passing assigns check), a
//!   pointee created inside the frame needs nothing, and anything else fails
//!   closed (`unsupported_with_fallback`). A handler may not write at all, so
//!   nothing is ever accused from here.
//!
//! Known limit, documented on purpose: an aggregate passed BY VALUE that owns a
//! pointer deeper than one field (a `Vec` moved into `into_iter`) is not
//! attributed; a store through it reaches memory the caller no longer names.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::{Mutability, Operand};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use std::sync::Arc;
use tracing::debug;

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::shared::mono_ty;

/// How an argument can carry a writable pointer.
enum ArgPointer {
    /// No writable pointer.
    None,
    /// The argument itself points at the storage that may be written.
    Direct,
    /// The argument is a wrapper whose field `index` is the pointer.
    Field(usize),
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    fn modifies_arg_pointer(ty: Ty) -> ArgPointer {
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Ref(_, _, Mutability::Mut) | RigidTy::RawPtr(_, Mutability::Mut),
            ) => ArgPointer::Direct,
            TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not)) => {
                if Self::definitely_freeze(pointee, 0) {
                    ArgPointer::None
                } else {
                    ArgPointer::Direct
                }
            }
            TyKind::RigidTy(RigidTy::Adt(def, adt_args)) if def.kind() == AdtKind::Struct => {
                let variants = def.variants();
                let [variant] = variants.as_slice() else {
                    return ArgPointer::None;
                };
                let pointer_fields: Vec<usize> = variant
                    .fields()
                    .iter()
                    .enumerate()
                    .filter(|(_, field)| {
                        // A field whose type does not instantiate counts as a
                        // pointer candidate (fail closed).
                        mono_ty::field_ty(field, &adt_args).is_none_or(|field_ty| {
                            matches!(Self::modifies_arg_pointer(field_ty), ArgPointer::Direct)
                        })
                    })
                    .map(|(index, _)| index)
                    .collect();
                match pointer_fields.as_slice() {
                    [index] => ArgPointer::Field(*index),
                    _ => ArgPointer::None,
                }
            }
            _ => ArgPointer::None,
        }
    }

    /// After a handler encoded `func(args)` without inlining a body, classify
    /// every pointee a writable-pointer argument names against the innermost
    /// modifies frame.
    pub(super) fn bmc_modifies_classify_handled_call(
        &mut self,
        args: &[Operand],
        handler: &'static str,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        for arg in args {
            let (Operand::Copy(place) | Operand::Move(place)) = arg else {
                continue;
            };
            let Some(ty) = place.ty(self.body.locals()).into_option() else {
                continue;
            };
            let pointer_key: Arc<str> = match Self::modifies_arg_pointer(ty) {
                ArgPointer::None => continue,
                ArgPointer::Direct => Arc::from(self.ssa_base_name(place)),
                ArgPointer::Field(index) => {
                    let base = self.ssa_base_name(place);
                    Arc::from(crate::codegen_ay::names::indexed_field_name(&base, index))
                }
            };
            self.bmc_modifies_classify_pointee_of(&pointer_key, handler);
        }
    }

    /// Certify, skip or fail closed on the storage `pointer_key` points at.
    fn bmc_modifies_classify_pointee_of(&mut self, pointer_key: &Arc<str>, handler: &'static str) {
        let pointees: Vec<Option<Arc<str>>> =
            match self.ref_pointees.merged_alternatives(pointer_key.as_ref()) {
                Some(alternatives) => alternatives.iter().map(|alt| alt.pointee.clone()).collect(),
                None => vec![self.ref_pointees.get(pointer_key.as_ref()).cloned()],
            };
        let mut all_covered = true;
        let mut all_fresh = true;
        let mut first_uncovered: Option<Arc<str>> = None;
        for pointee in &pointees {
            let Some(pointee) = pointee else {
                all_covered = false;
                all_fresh = false;
                continue;
            };
            let names = self.bmc_modifies_alias_chain(pointee);
            let (covered, fresh) = self.bmc_modifies_coverage(&names);
            all_covered &= covered;
            all_fresh &= fresh;
            if !(covered || fresh) && first_uncovered.is_none() {
                first_uncovered = names.first().cloned();
            }
        }
        if all_fresh {
            return;
        }
        if all_covered {
            debug!(pointer = %pointer_key, handler, "FC-06(bmc): handled call store certified");
            self.record_violation_guarded_with_message(
                ay_bindings::Expr::bool_const(false),
                "assigns_check",
                Some(format!("Check that *{pointer_key} is assignable")),
            );
            return;
        }
        debug!(pointer = %pointer_key, handler, "FC-06(bmc): handled call store not attributable (fail-closed)");
        let store = format!("{handler} through {pointer_key}");
        self.bmc_modifies_fail_closed(&store, first_uncovered.as_deref());
    }
}
