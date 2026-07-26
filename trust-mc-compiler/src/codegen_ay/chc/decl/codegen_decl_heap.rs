// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Heap region array predeclaration for CHC relation signatures.
//!
//! Extracted from codegen_decl.rs per #4119. This module predeclares region
//! arrays for heap allocations before relation signatures are built, ensuring
//! they are part of the CHC relation arguments and that subsequent rule
//! generation sees consistent state variable lists. (#1448)

use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{bv8_sort, ptr_sort};

use super::ChcCtx;
use super::codegen_rules_entry::CodegenRulesEntry;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Predeclare a single region state variable for a heap allocation.
    ///
    /// This ensures the region array is part of the CHC relation arguments and that
    /// subsequent rule generation sees consistent state variable lists. (#1448)
    pub(in crate::codegen_ay::chc) fn predeclare_region_state_var(
        &mut self,
        obj_id: u32,
        elem_sort: Sort,
    ) {
        let (arr_name, out_name) =
            self.heap_state.assign_region_array(obj_id, elem_sort.clone(), &self.fn_name);
        let arr_sort = Sort::array(ptr_sort(), elem_sort);

        if self.state_var_mgr.declared_state_var_names.insert(Arc::clone(&arr_name)) {
            debug!(
                obj_id,
                arr_name = %arr_name,
                "CHC: predeclared heap region state var"
            );
            self.push_state_var_pair_arc(arr_name, &out_name, arr_sort);
        }
    }

    /// Predeclare region arrays for heap allocations before relation signatures are built.
    ///
    /// This ensures region arrays are part of the CHC relation arguments and that
    /// subsequent rule generation sees consistent state variable lists. (#1448)
    pub(in crate::codegen_ay::chc) fn predeclare_heap_region_arrays(&mut self) {
        if self.track_level < ChcTrackLevel::Ptr {
            return;
        }

        // Allocate stack locals early so heap IDs follow stack IDs consistently.
        if self.encode.stack_alloc_constraints.is_none() {
            self.encode.stack_alloc_constraints = Some(self.allocate_stack_locals());
        }

        for (bb_idx, bb_data) in self.body.blocks.iter().enumerate() {
            if let TerminatorKind::Call { func, args, destination, target, .. } =
                &bb_data.terminator.kind
                && let Some(stub) = self.detect_alloc_stub(func)
            {
                match stub {
                    StubKind::BoxNew
                    | StubKind::RustAlloc
                    | StubKind::RustAllocZeroed
                    | StubKind::RustRealloc => {
                        let Some(obj_id) = self.heap_state.reserve_heap_alloc_id() else {
                            warn!(
                                ?bb_idx,
                                "CHC: allocation ID overflow during alloc stub pre-declaration"
                            );
                            continue;
                        };
                        // Part of #3714: Predict the typed element sort for the region.
                        // BoxNew: the first arg's type IS the boxed element type (Box::new(val)).
                        // RustAlloc/RustAllocZeroed: if the call target immediately wraps or casts
                        // the returned pointer to a typed allocation payload, use that payload type.
                        // This keeps the allocator's real obj_id typed from declaration time
                        // without reserving a phantom wrapper obj_id.
                        // RustRealloc keeps BV8: it preserves or aliases existing regions later.
                        let elem_sort =
                            self.alloc_stub_elem_sort(stub, args, destination.local, *target);
                        self.predeclare_region_state_var(obj_id, elem_sort.clone());
                        debug!(
                            ?bb_idx,
                            obj_id,
                            ?elem_sort,
                            "CHC: predeclared region array for alloc stub"
                        );
                    }
                    StubKind::RustDealloc => {} // No pre-declaration needed for dealloc
                    other => {
                        trace!(?other, "CHC: stub kind does not need alloc region pre-declaration");
                    }
                }
            }
        }
    }

    /// Predeclare region arrays for Rc::new / Arc::new calls in the harness body.
    ///
    /// Part of #4193: The `codegen_rc_arc_new` stub internally allocates one heap
    /// region via `translate_alloc_call(BoxNew, ...)`. But `predeclare_heap_region_arrays`
    /// only detects direct alloc stubs (BoxNew, RustAlloc, etc.) in the harness body.
    /// Rc::new/Arc::new are dispatched as dedicated stubs, not as raw alloc calls,
    /// so their allocation is invisible to the scanner. This creates late region
    /// state vars (e.g., `region_39_bv8`) that widen CHC relation arity mid-encoding.
    ///
    /// This method counts Rc::new / Arc::new calls in the harness body and predeclares
    /// exactly one BV8 region per call, matching the allocation the stub will perform.
    pub(in crate::codegen_ay::chc) fn predeclare_callee_heap_region_arrays(&mut self) {
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::{RigidTy, TyKind};

        if self.track_level < ChcTrackLevel::Ptr {
            return;
        }

        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, .. } = &bb_data.terminator.kind else {
                continue;
            };
            let Ok(func_ty) = func.ty(self.body.locals()) else {
                continue;
            };
            let (fn_def, fn_substs) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
                _ => continue,
            };
            let Ok(instance) = Instance::resolve(fn_def, &fn_substs) else {
                continue;
            };
            let path = instance.name();

            // Check if this is an Rc::new or Arc::new call.
            if !ChcCtx::is_rc_arc_new_path(&path) {
                continue;
            }

            let Some(obj_id) = self.heap_state.reserve_heap_alloc_id() else {
                warn!("CHC: allocation ID overflow during Rc/Arc::new pre-declaration");
                continue;
            };
            // Rc/Arc::new stub allocates with BoxNew which starts as BV8.
            self.predeclare_region_state_var(obj_id, bv8_sort());
            debug!(
                obj_id,
                callee = %path,
                "CHC: predeclared region array for Rc/Arc::new"
            );
        }
    }

    fn alloc_stub_elem_sort(
        &self,
        stub: StubKind,
        args: &[Operand],
        destination_local: usize,
        target: Option<usize>,
    ) -> Sort {
        match stub {
            StubKind::BoxNew => args
                .first()
                .and_then(|arg| arg.ty(self.body.locals()).ok())
                .map(|ty| self.elem_sort_for_memory_array(ty))
                .unwrap_or_else(bv8_sort),
            StubKind::RustAlloc | StubKind::RustAllocZeroed => target
                .and_then(|target_bb| {
                    self.target_block_elem_sort_for_alloc(target_bb, destination_local)
                })
                .unwrap_or_else(bv8_sort),
            StubKind::RustRealloc => bv8_sort(),
            _ => bv8_sort(),
        }
    }

    fn target_block_elem_sort_for_alloc(
        &self,
        target_bb: usize,
        alloc_local: usize,
    ) -> Option<Sort> {
        let block = self.body.blocks.get(target_bb)?;
        block.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                return None;
            };

            match rvalue {
                Rvalue::ShallowInitBox(operand, boxed_ty)
                    if Self::operand_is_unprojected_local(operand, alloc_local) =>
                {
                    Some(self.elem_sort_for_memory_array(*boxed_ty))
                }
                Rvalue::Cast(_, operand, target_ty)
                    if Self::operand_is_unprojected_local(operand, alloc_local) =>
                {
                    Self::pointee_ty(*target_ty).map(|ty| self.elem_sort_for_memory_array(ty))
                }
                _ => None,
            }
        })
    }

    fn pointee_ty(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
            _ => None,
        }
    }

    fn operand_is_unprojected_local(operand: &Operand, local: usize) -> bool {
        matches!(
            operand,
            Operand::Copy(place) | Operand::Move(place)
                if place.local == local && place.projection.is_empty()
        )
    }
}
