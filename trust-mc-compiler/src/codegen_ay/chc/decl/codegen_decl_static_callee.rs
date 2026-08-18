// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pre-scan callee bodies for static references before entry rule emission.
//!
//! Part of #4014: `collect_static_state_vars()` only scans the harness body.
//! When the inline walker processes a callee that references statics not in
//! the harness, the static's address falls through to the promoted-constant
//! fallback and the entry rule never constrains the memory array. This module
//! fixes the phase ordering by discovering callee statics during declaration.

use rustc_public::CrateDef;
use rustc_public::mir::alloc::GlobalAlloc;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-registers statics found in a callee body before inline translation.
    ///
    /// Scans a callee body for `GlobalAlloc::Static` constants not yet in
    /// `static_address_exprs`, allocates addresses, and registers memory init
    /// constraints so the entry rule seeds them correctly.
    ///
    /// Part of #4014: Fix unconstrained static mut in inlined callee bodies.
    pub(in crate::codegen_ay::chc) fn register_callee_body_statics(
        &mut self,
        callee_body: &rustc_public::mir::Body,
    ) {
        use rustc_public::ty::{ConstantKind, TyConstKind};

        for bb_data in &callee_body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(_lhs, rhs) = &stmt.kind else {
                    continue;
                };
                let const_op = match rhs {
                    Rvalue::Use(Operand::Constant(c)) => c,
                    _ => continue,
                };

                let mir_const = &const_op.const_;
                let alloc_provenance = match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => {
                        if alloc.provenance.ptrs.is_empty() {
                            continue;
                        }
                        alloc.provenance.clone()
                    }
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(_, alloc) => {
                            if alloc.provenance.ptrs.is_empty() {
                                continue;
                            }
                            alloc.provenance.clone()
                        }
                        _ => continue,
                    },
                    _ => continue,
                };

                let alloc_id = alloc_provenance.ptrs[0].1.0;
                let GlobalAlloc::Static(static_def) = GlobalAlloc::from(alloc_id) else {
                    continue;
                };

                // Already registered (from harness body or a previous callee).
                if self.ref_resolution.static_address_exprs.contains_key(&alloc_id) {
                    continue;
                }
                // Also check by DefId (cross-body AllocId aliasing).
                let target_def_id = static_def.def_id();
                let already_known =
                    self.ref_resolution.static_address_exprs.keys().any(|&existing_id| {
                        matches!(
                            GlobalAlloc::from(existing_id),
                            GlobalAlloc::Static(d) if d.def_id() == target_def_id
                        )
                    });
                if already_known {
                    // Part of #4097: Register the callee's AllocId as an alias
                    // for the existing address so cross-body static references
                    // resolve correctly in the inline walker.
                    let existing_addr = self
                        .ref_resolution
                        .static_address_exprs
                        .iter()
                        .find(|(existing_id, _)| {
                            matches!(
                                GlobalAlloc::from(**existing_id),
                                GlobalAlloc::Static(d) if d.def_id() == target_def_id
                            )
                        })
                        .map(|(_, addr)| addr.clone());
                    if let Some(addr) = existing_addr {
                        self.ref_resolution.static_address_exprs.insert(alloc_id, addr);
                    }
                    continue;
                }

                let static_name = static_def.name();
                let static_ty = static_def.ty();

                let Some(sort) = Self::translate_ty(static_ty) else {
                    continue;
                };

                // Allocate a unique address for this callee-discovered static.
                let Some(obj_id) = self.heap_state.next_alloc_id() else {
                    continue;
                };
                // Freshly minted object base: an address by construction, so
                // this is where the tag belongs.
                let addr = crate::codegen_ay::provenance::Loc::of_address(
                    ay_bindings::Expr::bitvec_const(obj_id as i128, 32)
                        .concat(ay_bindings::Expr::bitvec_const(0i128, 32)),
                );
                self.ref_resolution.static_address_exprs.insert(alloc_id, addr.as_expr().clone());

                // Record static layout metadata for entry-rule size/alignment
                // constraints on callee-discovered statics.
                if let Some(type_size) = self.get_type_size(static_ty) {
                    let type_align = self.get_type_align(static_ty).unwrap_or(1);
                    self.ref_resolution.static_alloc_sizes.push((
                        obj_id,
                        type_size as u32,
                        type_align,
                    ));
                }

                // Read initial value and register memory init. A foreign
                // (`extern "C"`) static has no initializer body — calling
                // `eval_initializer()` on it span_bugs/panics (uncatchable by
                // `.ok()`). Model it as nondet (the None-path below leaves the
                // static memory unconstrained). NEVER assume zero.
                let internal_def_id =
                    rustc_public::rustc_internal::internal(self.tcx, static_def.def_id());
                let init_alloc_opt = if self.tcx.is_foreign_item(internal_def_id) {
                    None
                } else {
                    static_def.eval_initializer().ok()
                };
                let init_expr_opt = init_alloc_opt
                    .as_ref()
                    .and_then(|alloc| self.static_init_from_alloc(alloc, &sort, static_ty));

                // P2-S1: contract CHECK harness — a callee `static mut` must
                // NOT have its memory pinned to the initializer (the contract
                // holds for arbitrary ambient state; pinning is fail-open).
                // Interior-mut immutable statics flow through the per-field
                // gate inside `register_static_memory_init_entries`.
                let contract_havoc_mut_static =
                    self.contract_static_havoc && self.tcx.is_mutable_static(internal_def_id);

                if contract_havoc_mut_static {
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: contract harness — callee static mut left havocked (P2-S1)"
                    );
                } else if let Some(init_value) = init_expr_opt {
                    self.register_static_memory_init_entries(static_ty, init_value, addr);
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: registered callee static memory init (#4014)"
                    );
                } else {
                    debug!(
                        static_name = %static_name,
                        obj_id,
                        "CHC: callee static address allocated, no init value (#4014)"
                    );
                }
            }
        }
    }

    /// Pre-scans harness body Call terminators for callee statics.
    ///
    /// Resolves each Call's target Instance, obtains its body, and calls
    /// `register_callee_body_statics` so that static addresses and memory
    /// init values are available before `emit_entry_rule()`.
    ///
    /// Part of #4014.
    pub(in crate::codegen_ay::chc) fn prescan_callee_statics(&mut self) {
        use rustc_public::mir::TerminatorKind;
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::{RigidTy, TyKind};

        let callee_bodies: Vec<_> = self
            .body
            .blocks
            .iter()
            .filter_map(|bb| {
                let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
                    return None;
                };
                let func_ty = func.ty(self.body.locals()).ok()?;
                let (fn_def, fn_substs) = match func_ty.kind() {
                    TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
                    _ => return None,
                };
                let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
                instance.body()
            })
            .collect();

        for callee_body in &callee_bodies {
            self.register_callee_body_statics(callee_body);
        }
    }
}
