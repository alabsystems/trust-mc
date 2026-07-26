// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Stub-internal declaration-time type-array prediction for CHC.
//!
//! Extracted from `codegen_decl_deref.rs` to keep declaration helpers under
//! the 500-line limit while extending prediction coverage for Vec/iterator
//! carrier types. Part of #3714.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{StatementKind, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;

/// Return an instance's MIR body only when a body can actually be built.
///
/// `Instance::body()` builds the body via rustc shim construction, which
/// `bug!`s (panics at `rustc_mir_transform/shim.rs`) for `Virtual` (vtable
/// dispatch) and `Intrinsic` instances — "InstanceKind::Virtual is for direct
/// calls only" / "creating shims from intrinsics is unsupported". These
/// prediction passes walk callee bodies best-effort, so a callee resolved to a
/// virtual/intrinsic instance should simply be skipped rather than crash the
/// whole compilation. See kani #2312 (ZST virtual-call ABI) and DynTrait upcast.
fn safe_instance_body(instance: &Instance) -> Option<rustc_public::mir::Body> {
    if matches!(instance.kind, InstanceKind::Virtual { .. } | InstanceKind::Intrinsic) {
        return None;
    }
    instance.body()
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-declare type arrays for types used internally by CHC stubs.
    ///
    /// Part of #2982: eliminate late type arrays via comprehensive prediction.
    /// Part of #3713: generalized MaybeUninit<T> prediction from body locals.
    /// Part of #3714: recover hidden element types from Vec/iterator/Box carriers.
    pub(in crate::codegen_ay::chc) fn predeclare_stub_internal_type_arrays(&mut self) {
        // Part of #4181: `u8` is used pervasively by the heap model (bool stored
        // as u8, pointer casts, coroutine captured upvars). Always predeclare it
        // to avoid late-creation gaps that cause Z3 "unknown constant" errors.
        // Part of #2982: common scalar types are used pervasively by field
        // access through tuples, struct projections, and iterator internals.
        // Predeclaring them universally eliminates late-creation gaps for
        // harnesses that use these types as struct/tuple fields.
        let universal_stub_types = [
            "std_option_Option_usize",
            "std_alloc_Layout",
            "std_ptr_Alignment",
            "u8",
            "i32",
            "u32",
            "i64",
            "u64",
            "i128",
            "u128",
            "isize",
            "bool",
            "unit",
            "slice_unit",
        ];

        for type_key in &universal_stub_types {
            self.predeclare_type_array_if_missing(type_key);
        }

        // Part of #3713: Predict MaybeUninit<T> inner type keys from body locals.
        // Array iterator stores use MaybeUninit<T> locals whose inner T needs a
        // type array. `type_key_for_body_ty` unwraps MaybeUninit transparently
        // (via `unwrap_heap_transparent_ty`), so we detect MaybeUninit by ADT
        // name on the resolved type _before_ unwrapping, then predeclare the
        // inner type's key.
        let maybe_uninit_inner_keys: Vec<String> = self
            .body
            .locals()
            .iter()
            .filter_map(|local| {
                let resolved = self.resolve_body_ty(local.ty);
                let TyKind::RigidTy(RigidTy::Adt(def, args)) = resolved.kind() else {
                    return None;
                };
                if def.trimmed_name() != "MaybeUninit" {
                    return None;
                }
                let GenericArgKind::Type(inner_ty) = args.0.first()? else {
                    return None;
                };
                Some(self.type_key_for_body_ty(*inner_ty).into_owned())
            })
            .collect();

        for key in &maybe_uninit_inner_keys {
            self.predeclare_type_array_if_missing(key);
        }

        // Part of #2982/#3099: StorageLive/StorageDead can mention locals whose
        // typed memory is later reached by cleanup/drop translation even when the
        // normal local-use scan does not retain them. Predeclare those storage
        // marker carrier types up front so transition generation does not widen
        // block relations with late type arrays.
        let storage_marker_keys = self.predict_storage_marker_type_keys();
        for (key, ty) in &storage_marker_keys {
            self.predeclare_type_array_for_ty_if_missing(key, *ty);
        }

        let predicted_elem_keys = self.predict_stub_internal_elem_type_keys();
        for key in &predicted_elem_keys {
            self.predeclare_type_array_if_missing(key);
        }

        // Part of #4046 Bucket C: predeclare Vec infrastructure type arrays.
        // Vec<T> operations internally create type arrays for RawVec<T, Global>,
        // slice_T, PhantomData<T>, plus universal allocator infrastructure types.
        // Without predeclaration these become late state vars, disconnecting
        // stores from loads across CHC blocks.
        let vec_elem_keys = self.predict_vec_elem_type_keys();
        if !vec_elem_keys.is_empty() {
            let universal_vec_infra = [
                "u8",
                "u64",
                "alloc_raw_vec_RawVecInner_std_alloc_Global",
                "std_ptr_Unique_u8",
                "core_num_niche_types_UsizeNoHighBit",
                "std_alloc_Global",
            ];
            for key in &universal_vec_infra {
                self.predeclare_type_array_if_missing(key);
            }
            for elem_key in &vec_elem_keys {
                let slice_key = format!("slice_{elem_key}");
                let raw_vec_key = format!("alloc_raw_vec_RawVec_{elem_key}_std_alloc_Global");
                let phantom_key = format!("std_marker_PhantomData_{elem_key}");
                self.predeclare_type_array_if_missing(&slice_key);
                self.predeclare_type_array_if_missing(&raw_vec_key);
                self.predeclare_type_array_if_missing(&phantom_key);
            }
        }

        // Part of #4033: predeclare Rc/Weak infrastructure type arrays.
        // Rc<T> operations internally create type arrays for RcInner<T>,
        // WeakInner, PhantomData<RcInner<T>>, plus universal allocator and
        // reference types. Without predeclaration these become late state
        // vars, disconnecting stores from loads across CHC blocks.
        //
        // When the harness uses Rc<dyn Trait>, the concrete type (e.g. Table)
        // is only visible inside called functions. predict_callee_rc_elem_type_keys
        // performs a one-level callee body scan to discover these hidden types.
        let mut rc_elem_keys = self.predict_rc_elem_type_keys();
        rc_elem_keys.extend(self.predict_callee_rc_elem_type_keys());
        if !rc_elem_keys.is_empty() {
            // Stdlib-internal Rc machinery uses `bool` and `u8` as element types
            // deep in Rc::drop / dealloc call chains, invisible to callee scanning.
            // Always include these when any Rc usage is detected.
            rc_elem_keys.insert("bool".to_owned());
            rc_elem_keys.insert("u8".to_owned());

            let universal_rc_infra = [
                "std_rc_WeakInner",
                "ref_usize",
                "ref_isize",
                "ref_std_alloc_Global",
                "std_alloc_Global",
                "u64",
                // Rc::new / alloc path uses std::ptr::Alignment for layout
                // computation. Without predeclaration, this becomes a late
                // state var that widens relation signatures mid-encoding.
                "std_ptr_Alignment",
                // Full Rc/Weak wrappers for stdlib-internal element types.
                // These come from Rc's internal reference counting machinery
                // and are not visible at any callee scanning depth.
                "std_rc_Rc_bool_std_alloc_Global",
                "std_rc_Weak_u8_ref_std_alloc_Global",
            ];
            for key in &universal_rc_infra {
                self.predeclare_type_array_if_missing(key);
            }
            for elem_key in &rc_elem_keys {
                let rc_inner_key = format!("std_rc_RcInner_{elem_key}");
                let phantom_rc_inner_key =
                    format!("std_marker_PhantomData_std_rc_RcInner_{elem_key}");
                let nonnull_rc_inner_key = format!("std_ptr_NonNull_std_rc_RcInner_{elem_key}");
                self.predeclare_type_array_if_missing(&rc_inner_key);
                self.predeclare_type_array_if_missing(&phantom_rc_inner_key);
                self.predeclare_type_array_if_missing(&nonnull_rc_inner_key);
            }
        }

        // Part of #2982: predeclare slice iterator infrastructure type arrays.
        // Iter<'_, T> and IterMut<'_, T> internally use NonNull<T>, *const T,
        // and PhantomData<&T>. These are discovered late during inline encoding
        // when stdlib MIR is unavailable. Predict them from body locals.
        let iter_elem_keys = self.predict_slice_iter_elem_type_keys();
        for elem_key in &iter_elem_keys {
            let nonnull_key = format!("std_ptr_NonNull_{elem_key}");
            let ptr_key = format!("ptr_{elem_key}");
            let phantom_ref_key = format!("std_marker_PhantomData_ref_{elem_key}");
            self.predeclare_type_array_if_missing(&nonnull_key);
            self.predeclare_type_array_if_missing(&ptr_key);
            self.predeclare_type_array_if_missing(&phantom_ref_key);
        }

        // Part of #4075: when the harness reaches the async spawn scheduler,
        // predeclare the runtime support arrays up front so translation does not
        // widen relation signatures mid-block for noop waker/context carriers
        // and boxed-future task slots.
        self.predeclare_spawn_scheduler_type_arrays();
    }

    /// Helper: predeclare a single type array if not already present.
    fn predeclare_type_array_if_missing(&mut self, type_key: &str) {
        self.predeclare_type_array_with_sort_if_missing(
            type_key,
            Self::sort_from_type_key(type_key),
        );
    }

    /// Ty-aware variant of [`Self::predeclare_type_array_if_missing`] for
    /// prediction lanes that still hold the concrete `Ty` behind the key.
    ///
    /// The string tables stay authoritative: when `try_sort_from_type_key`
    /// resolves the key, the sort is identical to the string-only path. Only
    /// when the string key is unknown — which previously ALWAYS recorded a
    /// PROOF-demoting `type_sort_fallback` and guessed an opaque byte-array —
    /// do we resolve the layout-accurate sort from the `Ty` itself
    /// (`elem_sort_for_memory_array`). That closes the spurious demotion for
    /// concrete-layout foreign types with all-lowercase keys (e.g. macOS
    /// libc `pthread_mutex_t` inside `Arc<Mutex<[u8]>>` drop, whose key
    /// `libc_libc_unix_bsd_apple_pthread_mutex_t` misses the uppercase-ADT
    /// catch-all) while staying fail-closed: if the `Ty` itself is
    /// unresolvable, `elem_sort_for_memory_array` falls through to
    /// `sort_from_type_key` internally and records the fallback exactly as
    /// before.
    fn predeclare_type_array_for_ty_if_missing(
        &mut self,
        type_key: &str,
        ty: Option<rustc_public::ty::Ty>,
    ) {
        if self.heap_state.type_arrays.contains_key(type_key) {
            return;
        }
        let elem_sort = match Self::try_sort_from_type_key(type_key) {
            Some(sort) => sort,
            None => match ty {
                Some(ty) => self.elem_sort_for_memory_array(ty),
                // Derived string-only keys (e.g. "LazyLeafRange_…"): keep the
                // recording fallback semantics.
                None => Self::sort_from_type_key(type_key),
            },
        };
        self.predeclare_type_array_with_sort_if_missing(type_key, elem_sort);
    }

    pub(super) fn predeclare_type_array_with_sort_if_missing(
        &mut self,
        type_key: &str,
        elem_sort: Sort,
    ) {
        if self.heap_state.type_arrays.contains_key(type_key) {
            return;
        }

        let (arr_name, arr_out_name) =
            crate::codegen_ay::names::mem_array_name_pair(&self.fn_name, type_key);
        let arr_sort = Sort::array(ptr_sort(), elem_sort.clone());

        debug!(
            type_key = %type_key,
            "CHC: pre-declared stub-internal type array (#2982/#3713/#3714)"
        );

        self.heap_state
            .type_arrays
            .insert(type_key.into(), (Arc::clone(&arr_name), elem_sort.clone()));
        self.heap_state.array_name_to_elem_sort.insert(Arc::clone(&arr_name), elem_sort);
        self.push_state_var_pair_arc(arr_name, &arr_out_name, arr_sort);
    }

    // Spawn scheduler type-array prediction extracted to
    // codegen_decl_stub_internal_spawn.rs per #4119.

    /// Predict element type keys specifically from Vec<T> body locals.
    ///
    /// Part of #4046 Bucket C: Vec<T> operations create infrastructure type
    /// arrays (RawVec<T>, slice_T, PhantomData<T>) that need predeclaration.
    fn predict_vec_elem_type_keys(&self) -> BTreeSet<String> {
        let mut keys: BTreeSet<String> = self
            .body
            .locals()
            .iter()
            .filter_map(|local| {
                let ty = self.resolve_body_ty(local.ty);
                match ty.kind() {
                    TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Vec" => {
                        args.0.iter().find_map(|arg| match arg {
                            GenericArgKind::Type(elem_ty) => {
                                let resolved = self.resolve_body_ty(*elem_ty);
                                if self.stub_internal_ignored_elem_ty(resolved) {
                                    None
                                } else {
                                    Some(self.type_key_for_body_ty(resolved).into_owned())
                                }
                            }
                            _ => None,
                        })
                    }
                    _ => None,
                }
            })
            .collect();

        // Part of #4050: also scan ADT struct fields for nested Vec<T>.
        keys.extend(self.predict_vec_elem_from_adt_fields());
        keys
    }

    /// Part of #4050: Predict Vec element types from ADT struct fields (e.g. ArraySolver).
    fn predict_vec_elem_from_adt_fields(&self) -> BTreeSet<String> {
        let skip = ["Vec", "RawVec", "RawVecInner", "Box", "Rc", "Arc", "Option"];
        let mut keys = BTreeSet::new();
        for local in self.body.locals() {
            let ty = self.resolve_body_ty(local.ty);
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { continue };
            if skip.contains(&def.trimmed_name().as_str()) {
                continue;
            }
            for variant in def.variants() {
                for field in variant.fields() {
                    let ft = self.resolve_body_ty(field.ty());
                    let TyKind::RigidTy(RigidTy::Adt(fd, fa)) = ft.kind() else { continue };
                    if fd.trimmed_name() != "Vec" {
                        continue;
                    }
                    let Some(GenericArgKind::Type(et)) = fa.0.first() else { continue };
                    let resolved = self.resolve_body_ty(*et);
                    if self.stub_internal_ignored_elem_ty(resolved) {
                        continue;
                    }
                    keys.insert(self.type_key_for_body_ty(resolved).into_owned());
                }
            }
        }
        keys
    }

    /// Predict element type keys from Rc<T> and Weak<T> body locals.
    ///
    /// Part of #4033: Rc<T> operations create infrastructure type arrays
    /// (RcInner<T>, PhantomData<RcInner<T>>, WeakInner, etc.) that need
    /// predeclaration to avoid late state vars.
    fn predict_rc_elem_type_keys(&self) -> BTreeSet<String> {
        self.body
            .locals()
            .iter()
            .filter_map(|local| {
                let ty = self.resolve_body_ty(local.ty);
                match ty.kind() {
                    TyKind::RigidTy(RigidTy::Adt(def, args))
                        if matches!(def.trimmed_name().as_str(), "Rc" | "Weak" | "RcInner") =>
                    {
                        args.0.iter().find_map(|arg| match arg {
                            GenericArgKind::Type(elem_ty) => {
                                let resolved = self.resolve_body_ty(*elem_ty);
                                if self.stub_internal_ignored_elem_ty(resolved) {
                                    None
                                } else {
                                    Some(self.type_key_for_body_ty(resolved).into_owned())
                                }
                            }
                            _ => None,
                        })
                    }
                    _ => None,
                }
            })
            .collect()
    }

    /// Predict Rc element type keys by scanning direct callee body locals.
    ///
    /// Part of #4033: When the harness body contains `Rc<dyn Trait>`, the concrete
    /// type behind the trait (e.g., `Table`) is only visible inside called functions
    /// (e.g., `Table::new_furniture`). This one-level callee scan discovers concrete
    /// Rc/Weak element types that body-local scanning alone cannot predict.
    fn predict_callee_rc_elem_type_keys(&self) -> BTreeSet<String> {
        let mut keys = BTreeSet::new();

        for bb in &self.body.blocks {
            let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
                continue;
            };
            let Ok(func_ty) = func.ty(self.body.locals()) else {
                continue;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
                continue;
            };
            let Ok(instance) = Instance::resolve(def, &args) else {
                continue;
            };
            let Some(callee_body) = safe_instance_body(&instance) else {
                continue;
            };

            for local in callee_body.locals() {
                let ty = self.resolve_body_ty(local.ty);
                if let TyKind::RigidTy(RigidTy::Adt(callee_def, callee_args)) = ty.kind() {
                    if matches!(callee_def.trimmed_name().as_str(), "Rc" | "Weak" | "RcInner") {
                        if let Some(GenericArgKind::Type(elem_ty)) = callee_args.0.first() {
                            let resolved = self.resolve_body_ty(*elem_ty);
                            if !self.stub_internal_ignored_elem_ty(resolved) {
                                let key = self.type_key_for_body_ty(resolved).into_owned();
                                debug!(
                                    callee = %instance.name(),
                                    type_key = %key,
                                    "CHC: callee body reveals Rc element type (#4033)"
                                );
                                keys.insert(key);
                            }
                        }
                    }
                }
            }
        }

        keys
    }

    /// Predict element type keys from slice Iter/IterMut body locals.
    ///
    /// Part of #2982: Iter<'_, T> and IterMut<'_, T> internally use NonNull<T>,
    /// *const T, and PhantomData<&T>. When stdlib MIR is unavailable for these
    /// iterator methods, the type arrays are created late during inline encoding.
    /// This prediction pass discovers the element types so infrastructure arrays
    /// can be predeclared.
    fn predict_slice_iter_elem_type_keys(&self) -> BTreeSet<String> {
        self.body
            .locals()
            .iter()
            .filter_map(|local| {
                let ty = self.resolve_body_ty(local.ty);
                let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
                    return None;
                };
                let trimmed = def.trimmed_name();
                let full = def.name();
                if !((trimmed == "Iter" || trimmed == "IterMut") && full.contains("slice")) {
                    return None;
                }
                args.0.iter().find_map(|arg| match arg {
                    GenericArgKind::Type(elem_ty) => {
                        let resolved = self.resolve_body_ty(*elem_ty);
                        if self.stub_internal_ignored_elem_ty(resolved) {
                            None
                        } else {
                            Some(self.type_key_for_body_ty(resolved).into_owned())
                        }
                    }
                    _ => None,
                })
            })
            .collect()
    }

    /// Predict inner element type keys needed by stub-internal collection carriers.
    fn predict_stub_internal_elem_type_keys(&self) -> BTreeSet<String> {
        self.body
            .locals()
            .iter()
            .filter_map(|local| self.stub_internal_predicted_elem_ty(local.ty))
            .map(|elem_ty| self.type_key_for_body_ty(elem_ty).into_owned())
            .collect()
    }

    /// Predict type keys for locals named only by storage markers.
    ///
    /// Each key maps to the concrete `Ty` it was derived from when one is
    /// available (`None` for string-derived keys like `ptr_…` pointer views
    /// and `LazyLeafRange_…`), so predeclaration can resolve layout-accurate
    /// sorts for keys the string tables do not know.
    fn predict_storage_marker_type_keys(&self) -> BTreeMap<String, Option<rustc_public::ty::Ty>> {
        let mut keys = BTreeMap::new();
        self.collect_storage_marker_type_keys_from_body(self.body, &mut keys, 0);
        self.collect_local_item_storage_marker_type_keys(&mut keys);
        for key in keys.keys().cloned().collect::<Vec<_>>() {
            if let Some(suffix) = key.strip_prefix("std_option_Option_LazyLeafHandle_") {
                keys.entry(format!("LazyLeafRange_{suffix}")).or_insert(None);
            }
        }
        keys
    }

    fn collect_local_item_storage_marker_type_keys(
        &self,
        keys: &mut BTreeMap<String, Option<rustc_public::ty::Ty>>,
    ) {
        for item in rustc_public::all_local_items() {
            let Ok(instance) = Instance::try_from(item) else {
                continue;
            };
            let Some(body) = safe_instance_body(&instance) else {
                continue;
            };
            self.collect_storage_marker_type_keys_from_body(&body, keys, 0);
        }
    }

    fn collect_storage_marker_type_keys_from_body(
        &self,
        body: &rustc_public::mir::Body,
        keys: &mut BTreeMap<String, Option<rustc_public::ty::Ty>>,
        depth: usize,
    ) {
        if depth > 3 {
            return;
        }

        for block in &body.blocks {
            for stmt in &block.statements {
                let local = match stmt.kind {
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => local,
                    _ => continue,
                };
                if let Some(local_decl) = body.locals().get(local) {
                    self.collect_storage_marker_type_keys(local_decl.ty, keys, 0);
                    self.collect_storage_marker_drop_body_type_keys(local_decl.ty, keys, depth + 1);
                }
            }

            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                self.collect_storage_marker_call_body_type_keys(func, body, keys, depth + 1);
            }
        }
    }

    fn collect_storage_marker_call_body_type_keys(
        &self,
        func: &rustc_public::mir::Operand,
        body: &rustc_public::mir::Body,
        keys: &mut BTreeMap<String, Option<rustc_public::ty::Ty>>,
        depth: usize,
    ) {
        if depth > 3 {
            return;
        }

        let Ok(func_ty) = func.ty(body.locals()) else {
            return;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return;
        };
        let Ok(instance) = Instance::resolve(def, &args) else {
            return;
        };
        let Some(callee_body) = safe_instance_body(&instance) else {
            return;
        };
        self.collect_storage_marker_type_keys_from_body(&callee_body, keys, depth);
    }

    fn collect_storage_marker_drop_body_type_keys(
        &self,
        ty: rustc_public::ty::Ty,
        keys: &mut BTreeMap<String, Option<rustc_public::ty::Ty>>,
        depth: usize,
    ) {
        if depth > 3 {
            return;
        }

        let ty = self.resolve_body_ty(ty);
        let drop_instance = Instance::resolve_drop_in_place(ty);
        let Some(drop_body) = safe_instance_body(&drop_instance) else {
            return;
        };
        self.collect_storage_marker_type_keys_from_body(&drop_body, keys, depth);
    }

    fn collect_storage_marker_type_keys(
        &self,
        ty: rustc_public::ty::Ty,
        keys: &mut BTreeMap<String, Option<rustc_public::ty::Ty>>,
        depth: usize,
    ) {
        if depth > 4 {
            return;
        }

        let ty = self.resolve_body_ty(ty);
        // A ty-backed entry upgrades a previously string-derived (None) one.
        keys.entry(self.type_key_for_body_ty(ty).into_owned())
            .and_modify(|slot| {
                if slot.is_none() {
                    *slot = Some(ty);
                }
            })
            .or_insert(Some(ty));

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                self.collect_storage_marker_type_keys(inner, keys, depth + 1);
            }
            TyKind::RigidTy(RigidTy::Array(inner, _)) | TyKind::RigidTy(RigidTy::Slice(inner)) => {
                self.collect_storage_marker_type_keys(inner, keys, depth + 1);
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                if matches!(def.trimmed_name().as_str(), "NonNull" | "Unique")
                    && let Some(GenericArgKind::Type(inner)) = args.0.first()
                {
                    let inner = self.resolve_body_ty(*inner);
                    let inner_key = self.type_key_for_body_ty(inner);
                    keys.entry(format!("ptr_{inner_key}")).or_insert(None);
                    self.collect_storage_marker_type_keys(inner, keys, depth + 1);
                }

                for arg in args.0 {
                    if let GenericArgKind::Type(inner) = arg {
                        self.collect_storage_marker_type_keys(inner, keys, depth + 1);
                    }
                }

                for variant in def.variants() {
                    for field in variant.fields() {
                        self.collect_storage_marker_type_keys(field.ty(), keys, depth + 1);
                    }
                }
            }
            _ => {}
        }
    }

    /// Recover a body-local element type hidden inside Vec/iterator/Box carriers.
    fn stub_internal_predicted_elem_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<rustc_public::ty::Ty> {
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                self.stub_internal_predicted_elem_ty(inner)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, _))
            | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => Some(self.resolve_body_ty(elem_ty)),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let trimmed_name = def.trimmed_name();
                let full_name = def.name();
                let predicts_first_type_arg =
                    matches!(trimmed_name.as_str(), "Vec" | "Box" | "Rc" | "Weak" | "RcInner")
                        || (trimmed_name == "IntoIter"
                            && (full_name.contains("vec") || full_name.contains("array")))
                        || ((trimmed_name == "Iter" || trimmed_name == "IterMut")
                            && full_name.contains("slice"));
                if !predicts_first_type_arg {
                    return None;
                }

                let elem_ty = args.0.iter().find_map(|arg| match arg {
                    GenericArgKind::Type(elem_ty) => Some(self.resolve_body_ty(*elem_ty)),
                    _ => None,
                })?;
                let elem_ty = match elem_ty.kind() {
                    TyKind::RigidTy(RigidTy::Array(inner, _))
                    | TyKind::RigidTy(RigidTy::Slice(inner)) => self.resolve_body_ty(inner),
                    _ => elem_ty,
                };
                if self.stub_internal_ignored_elem_ty(elem_ty) { None } else { Some(elem_ty) }
            }
            _ => None,
        }
    }

    /// Skip obvious non-element infrastructure generics when predicting keys.
    fn stub_internal_ignored_elem_ty(&self, ty: rustc_public::ty::Ty) -> bool {
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.is_empty() => true,
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                matches!(def.trimmed_name().as_str(), "Global" | "PhantomData")
            }
            _ => false,
        }
    }
}
