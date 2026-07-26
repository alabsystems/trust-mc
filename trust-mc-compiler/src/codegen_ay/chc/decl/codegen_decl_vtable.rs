// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pre-declaration of vtable state variables for dyn Trait locals.
//!
//! Extracted from codegen_decl.rs per file size limit (Part of #3159).
//! Scans MIR for Unsize coercion sites and propagation chains, then creates
//! `__vtable_sv_N` / `__vtable_sv_N__out` state variable pairs so they appear
//! in `declare-rel` relation signatures and can propagate vtable values between
//! blocks.

use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::mir::{CastKind, Operand, Place, PointerCoercion, Rvalue, StatementKind};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, trace};

use crate::kani_middle::abi::LayoutOf;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-declare vtable state variables for dyn Trait locals (Part of #3159).
    ///
    /// Scans MIR for:
    /// 1. Unsize coercion assignments (`Cast(PointerCoercion::Unsize, ...)`) where
    ///    the target type involves `dyn Trait` — these locals will have Dyn_Trait
    ///    expressions with vtable IDs at runtime.
    /// 2. Move/Copy assignments from dyn Trait locals — these propagate the vtable.
    ///
    /// Creates `__vtable_sv_N` / `__vtable_sv_N__out` state variable pairs so they
    /// appear in `declare-rel` relation signatures and can propagate vtable values
    /// between blocks. Without this, late-created vtable state vars are only
    /// `declare-var` (universally quantified per rule) and cannot carry values
    /// across block boundaries.
    ///
    /// Also pre-populates `vtable_type_metadata` with concrete type layouts from
    /// Unsize coercion sources (Part of #3159). This ensures that
    /// `Layout::for_value_raw::<dyn T>()` in earlier-numbered blocks can find the
    /// concrete pointee's (size, align) instead of defaulting to pointer-width (8, 8).
    pub(in crate::codegen_ay::chc) fn predeclare_vtable_state_vars(&mut self) {
        let mut dyn_locals: HashSet<usize> = HashSet::new();
        // Part of #3159: Collect concrete type layouts from Unsize coercion sources.
        let mut concrete_layouts: Vec<(u64, u64)> = Vec::new();
        let locals = self.body.locals();

        // Pass 1: Find locals assigned via Unsize coercion to dyn Trait types.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(Place { local, projection }, rvalue) = &stmt.kind
                    && projection.is_empty()
                {
                    // Trace Cast rvalues to diagnose Unsize coercion detection.
                    if let Rvalue::Cast(kind, _, target_ty) = rvalue {
                        trace!(
                            local = *local,
                            cast_kind = ?kind,
                            target_ty = ?target_ty,
                            is_dyn = Self::ty_involves_dyn_trait(target_ty),
                            "CHC: predeclare_vtable scan saw Cast (#3159)"
                        );
                    }
                    if let Rvalue::Cast(
                        CastKind::PointerCoercion(PointerCoercion::Unsize),
                        operand,
                        target_ty,
                    ) = rvalue
                    {
                        if Self::ty_involves_dyn_trait(target_ty) {
                            dyn_locals.insert(*local);
                            // Part of #3159: Extract the source concrete type's layout.
                            // Unwrap Box/Ref/Ptr to get the inner concrete type.
                            if let Ok(src_ty) = operand.ty(locals) {
                                let concrete_ty = Self::unwrap_to_concrete_inner(&src_ty);
                                let layout = LayoutOf::new(concrete_ty);
                                if let (Some(size), Some(align)) =
                                    (layout.size_of(), layout.align_of())
                                {
                                    concrete_layouts.push((size as u64, align as u64));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Part of #3347: Store concrete layouts in predeclared_concrete_layouts
        // instead of vtable_type_metadata. Sequential placeholder indices (0,1,2...)
        // collide with per-trait vtable IDs from resolve_vtable_id_for_type, causing
        // wrong (size, align) in multi-trait harnesses. The separate Vec provides
        // fallback layouts without polluting the vtable_id→layout mapping.
        self.predeclared_concrete_layouts = concrete_layouts;

        debug!(
            count = dyn_locals.len(),
            locals = ?dyn_locals,
            "CHC: predeclare_vtable_state_vars found dyn Trait locals (#3159)"
        );
        if dyn_locals.is_empty() {
            return;
        }

        // Pass 2: Find locals assigned via Move/Copy/Ref/AddressOf/Cast from
        // dyn Trait locals. Iterate until fixpoint since chains like
        // _a = Unsize, _b = move _a, _c = &(*_b).
        // Part of #3589: Must match all patterns in extract_vtable_source_local
        // (codegen_stmt_assign_simple.rs) so the pre-scan covers every local
        // that receives a vtable at runtime. Missing Ref/CopyForDeref/AddressOf
        // caused virtual dispatch to use unconstrained vtable discriminants.
        let mut changed = true;
        while changed {
            changed = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(Place { local, projection }, rvalue) = &stmt.kind
                        && projection.is_empty()
                    {
                        // Extract the source local from all vtable-propagating
                        // rvalue kinds (mirrors extract_vtable_source_local).
                        let src_local = match rvalue {
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p.local),
                            Rvalue::Ref(_, _, place) | Rvalue::CopyForDeref(place) => {
                                Some(place.local)
                            }
                            Rvalue::AddressOf(_, place) => Some(place.local),
                            Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => {
                                Some(p.local)
                            }
                            _ => None,
                        };
                        if let Some(src) = src_local {
                            if dyn_locals.contains(&src) && dyn_locals.insert(*local) {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        // Create vtable state variable pairs for each identified dyn Trait local.
        let sort = Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH);
        for &local_idx in &dyn_locals {
            use std::fmt::Write;
            let mut in_name = String::with_capacity(20);
            in_name.push_str("__vtable_sv_");
            let _ = write!(in_name, "{local_idx}");
            let mut out_name = String::with_capacity(25);
            out_name.push_str(&in_name);
            out_name.push_str("__out");
            let in_arc: Arc<str> = Arc::from(in_name.as_str());

            if self.state_var_mgr.declared_state_var_names.insert(Arc::clone(&in_arc)) {
                self.push_state_var_pair_arc(Arc::clone(&in_arc), &out_name, sort.clone());
                let out_arc: Arc<str> = Arc::from(out_name.as_str());
                debug!(
                    local_idx,
                    in_name = %in_arc,
                    state_var_count = self.state_var_mgr.state_vars.len(),
                    "CHC: predeclared vtable state variable (#3159)"
                );
                self.vtable_state_vars.insert(local_idx, (in_arc, out_arc));
            }
        }
    }

    /// Check if a type involves `dyn Trait` (RigidTy::Dynamic) through any
    /// level of wrapping (Box, &, *, etc.).
    fn ty_involves_dyn_trait(ty: &rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Dynamic(_, _)) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Self::ty_involves_dyn_trait(&inner),
            TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(
                |arg| matches!(arg, GenericArgKind::Type(t) if Self::ty_involves_dyn_trait(t)),
            ),
            _ => false,
        }
    }

    /// Unwrap a type through Box/Ref/Ptr to get the concrete inner type.
    /// Used in the vtable pre-pass to extract the concrete pointee type from
    /// Unsize coercion sources like `Box<S>` → `S`.
    /// Part of #3159.
    fn unwrap_to_concrete_inner(ty: &rustc_public::ty::Ty) -> rustc_public::ty::Ty {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
            TyKind::RigidTy(RigidTy::Adt(_, args)) => args
                .0
                .iter()
                .find_map(|arg| match arg {
                    GenericArgKind::Type(t) => Some(*t),
                    _ => None,
                })
                .unwrap_or(*ty),
            _ => *ty,
        }
    }
}
