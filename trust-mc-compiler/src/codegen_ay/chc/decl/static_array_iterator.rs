// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A borrowed static iterator keeps storage identity in fld_ptr. Its copied
//! data field is never used for item payloads in the admitted fragment.
use super::ChcCtx;
use super::static_path::same_ty_modulo_regions;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn static_borrowed_iter_constructor(
        &mut self,
        arg: &Operand,
        dest: usize,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        if !self.static_iterator_uses_closed() {
            return None;
        }
        let elem = self.borrowed_slice_item_ty(self.body.locals().get(dest)?.ty)?;
        self.static_iterator_sources(
            &Operand::Copy(Place { local: dest, projection: vec![] }),
            16,
        )?;
        let sources = self.static_pointer_sources(arg, 16)?;
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = arg.ty(self.body.locals()).ok()?.kind()
        else {
            return None;
        };
        let source_elem = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Array(e, _) | RigidTy::Slice(e)) => e,
            _ => return None,
        };
        if !same_ty_modulo_regions(elem, source_elem) {
            return None;
        }
        let pointer = self.translate_operand_with_modified(arg, modified)?;
        let repr = PtrRepr::classify(&pointer)?;
        let len = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Array(_, n)) => {
                Expr::bitvec_const(n.eval_target_usize().ok()? as u128, POINTER_WIDTH)
            }
            TyKind::RigidTy(RigidTy::Slice(_)) => repr.metadata()?.as_expr().clone(),
            _ => return None,
        };
        // The data snapshot is a representation field only in this fragment:
        // all consumers are closed next/identity operations, and next returns
        // base + old_cursor * stride rather than selecting this snapshot.
        let mut data = None;
        for key in sources {
            let object = self.ref_resolution.global_objects.get(&key)?;
            let idx = *self.ref_resolution.static_state_idx_by_obj.get(&object.obj_id)?;
            let TyKind::RigidTy(RigidTy::Array(e, _)) =
                self.ref_resolution.static_state_ty.get(&idx)?.kind()
            else {
                return None;
            };
            if !same_ty_modulo_regions(e, elem) {
                return None;
            }
            data = Some(self.static_state_current(idx, modified)?);
        }
        let data = data?;
        let elem_sort = data.sort().array_sort()?.element_sort.clone();
        let width = elem_sort.bitvec_width()?;
        // Every consumer and every next producer is closed above. Borrowed
        // items are addresses, so fld_data is an unused representation ghost,
        // not a copy of mutable storage and never a referent-value seed.
        let data = Expr::const_array(ptr_sort(), Expr::bitvec_const(0u128, width));
        let name = crate::codegen_ay::names::slice_sort_name(
            &crate::codegen_ay::names::sort_short_name(&elem_sort),
        );
        let sort = Sort::struct_type(
            &name,
            vec![
                ("fld_ptr", ptr_sort()),
                ("fld_len", ptr_sort()),
                ("fld_data", data.sort().clone()),
            ],
        );
        self.declare_datatype_sort_if_needed(&sort);
        let ctor = crate::codegen_ay::names::resolve_ctor_name(&sort, &name);
        let slice = Expr::datatype_constructor(
            &name,
            ctor,
            vec![repr.into_data().into_expr(), len, data],
            sort.clone(),
        );
        self.make_vec_into_iter_chc(slice)
    }
}
