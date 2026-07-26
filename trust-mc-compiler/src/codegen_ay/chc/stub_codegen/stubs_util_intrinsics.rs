// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC intrinsic, memory, and pointer stub utilities.
//!
//! Converted from include!() to proper module per #2595.
//! Extracted from stubs_util.rs per #2220 decomposition.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::codegen_call_vtable_intrinsic::VtableIntrinsicKind;
use super::stubs::StubKind;
use super::types::POINTER_WIDTH;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detect `std::intrinsics::raw_eq` calls.
    ///
    /// `raw_eq` compares two values by their raw byte representation.
    /// In CHC, we model this as SMT equality on the translated operands.
    /// Part of #1739: Recover harnesses using array `==` (which lowers to `raw_eq`).
    pub(in crate::codegen_ay::chc) fn detect_raw_eq_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("intrinsics::") && p.contains("raw_eq"))
    }

    /// Detect lowered `std::ptr::copy_nonoverlapping` calls.
    ///
    /// Some MIR paths lower pointer copy to a call terminator instead of
    /// `StatementKind::Intrinsic(CopyNonOverlapping)`. Route these through the
    /// same CHC array-update modeling as intrinsic statements (Part of #2110).
    pub(in crate::codegen_ay::chc) fn detect_copy_nonoverlapping_call(
        &self,
        func: &Operand,
    ) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            (p.starts_with("core::") || p.starts_with("std::")) && p.contains("copy_nonoverlapping")
        })
    }

    /// Detect `<[T]>::as_ptr` and `<[T]>::as_mut_ptr` calls (Part of #2979).
    ///
    /// These methods return a raw pointer to the first element. When MIR is
    /// unavailable for inlining, they appear as opaque calls whose return values
    /// are left unconstrained, causing spurious pointer-validity error rules.
    /// The CHC stub models them as identity on the pointer argument.
    pub(in crate::codegen_ay::chc) fn detect_slice_as_ptr_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            (p.contains("as_ptr") || p.contains("as_mut_ptr"))
                // `<impl str>::as_ptr` shares the identity-pointer semantics: the
                // str-literal receiver carries a promoted-const obj_id, so routing
                // it here yields a split-pointer address whose obj_id lane
                // const-folds — the offset alloc-bound check emits the REAL bound
                // instead of tripping the fail-closed provenance demotion.
                && (p.contains("slice::<impl") || p.contains("<impl str>"))
                && !p.contains("MaybeUninit")
                && !p.contains("Vec")
                && !p.contains("NonNull")
        })
    }

    /// Detect `str::as_bytes`.
    ///
    /// The return value is the same fat pointer/length pair viewed as `[u8]`,
    /// but downstream slice indexing needs the string's concrete byte backing.
    pub(in crate::codegen_ay::chc) fn detect_str_as_bytes_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("<impl str>") && p.ends_with("::as_bytes"))
    }

    /// Detect `str::len` calls that appear in panic formatting paths.
    ///
    /// `core::str::<impl str>::len` returns the byte length of a string slice.
    /// When MIR is unavailable, it falls through as unhandled. On panic paths
    /// this is dead code, but the conservative unsoundness demotion still
    /// fires. Handling it as unconstrained eliminates the demotion.
    pub(in crate::codegen_ay::chc) fn detect_str_len_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("<impl str>") && p.ends_with("::len"))
    }

    /// Detect `<dyn Any>::downcast_unchecked_ref` call terminator.
    ///
    /// `Any::downcast_ref` is inlined by MIR optimizer, leaving
    /// `downcast_unchecked_ref<T>` as the remaining call. This function
    /// transmutes `&dyn Any` to `&T` after the TypeId check succeeds.
    /// Part of #1739: D3 TypeId comparison stub for any_cast_int.
    /// Part of #3635: Handler wired in the `codegen_call_dispatch_misc` module.
    pub(in crate::codegen_ay::chc) fn detect_downcast_unchecked_ref(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("Any") && p.contains("downcast_unchecked_ref"))
    }

    /// Detect `UnsafeCell::get` calls — transparent pointer cast.
    ///
    /// `core::cell::UnsafeCell::<T>::get(&self) -> *mut T` returns a raw pointer
    /// to the inner value. Since UnsafeCell is `#[repr(transparent)]`, get() is a
    /// pointer identity cast. Without this handler, get() is an uninterpreted
    /// function producing unconstrained output, breaking all Stable atomic paths.
    /// Part of #3452: OptionCopied + UnsafeCell::get handler.
    pub(in crate::codegen_ay::chc) fn detect_unsafe_cell_get_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let Some(suffix) = p
                .strip_prefix("core::cell::UnsafeCell")
                .or_else(|| p.strip_prefix("std::cell::UnsafeCell"))
            else {
                return false;
            };
            (suffix.starts_with("::") || suffix.starts_with('<')) && p.ends_with("::get")
        })
    }

    /// Detect `Cell::new` constructor — value identity.
    ///
    /// `core::cell::Cell::<T>::new(value: T) -> Cell<T>` wraps a value in a Cell.
    /// Since `Cell<T>` is already modeled as `T` at the sort level
    /// (`codegen_types_adt.rs:214`), the constructor is a value identity:
    /// `dest = arg0`. Without this handler, `Cell::new` falls through as
    /// unhandled, losing the value constraint for downstream Rc construction paths.
    /// Part of #3681: required for `unsized_rc_cast` harness recovery.
    pub(in crate::codegen_ay::chc) fn detect_cell_new_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let Some(suffix) =
                p.strip_prefix("core::cell::Cell").or_else(|| p.strip_prefix("std::cell::Cell"))
            else {
                return false;
            };
            (suffix.starts_with("::") || suffix.starts_with('<')) && p.ends_with("::new")
        })
    }

    /// Detect `Mutex::new`, `Mutex::into_inner`, `Mutex::get_mut`,
    /// `RwLock::new`, `RwLock::into_inner`, `RwLock::get_mut` calls.
    ///
    /// In single-threaded verification these are transparent identity operations.
    /// Part of #4067: Mutex/RwLock are transparent wrappers.
    pub(in crate::codegen_ay::chc) fn detect_mutex_new_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let is_sync = p.contains("sync::Mutex") || p.contains("sync::RwLock");
            if !is_sync {
                return false;
            }
            p.ends_with("::new") || p.ends_with("::into_inner") || p.ends_with("::get_mut")
        })
    }

    /// Detect `drop_in_place::<Mutex<T>>` and `<Mutex as Drop>::drop` calls.
    ///
    /// Mutex/RwLock drop destroys the platform mutex (pthread), which has no
    /// semantic effect in single-threaded CHC verification. Without this, fn-inline
    /// walks the drop body into pthread foreign calls.
    /// Part of #4067: Mutex/RwLock drop is a no-op.
    pub(in crate::codegen_ay::chc) fn detect_mutex_drop_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let is_sync = p.contains("sync::Mutex") || p.contains("sync::RwLock");
            if !is_sync {
                return false;
            }
            p.contains("drop_in_place") || p.ends_with("::drop")
        })
    }

    /// Detect `Mutex::lock`, `RwLock::read`, `RwLock::write` calls.
    ///
    /// In single-threaded verification these always succeed and return the
    /// inner value wrapped in `Result::Ok(Guard)`. Without this handler they
    /// fall through to `pthread_mutex_lock` (foreign function) and produce
    /// unconstrained results that poison downstream proofs.
    /// Part of #4067: Mutex FFI stub — D2 lock/read/write.
    pub(in crate::codegen_ay::chc) fn detect_mutex_lock_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let is_sync = p.contains("sync::Mutex") || p.contains("sync::RwLock");
            if !is_sync {
                return false;
            }
            p.ends_with("::lock") || p.ends_with("::read") || p.ends_with("::write")
        })
    }

    /// Detect filesystem operations (`std::fs::remove_file`, `std::fs::write`, etc.).
    ///
    /// Filesystem operations are pure OS side effects with no verification semantics.
    /// In CHC verification these are modeled as nondeterministic `Result` producers.
    /// Without this handler, they fall through as unresolved calls producing ERROR.
    /// Part of #4134: pathbuf fat-pointer recovery.
    ///
    /// MIR inlining can produce paths with a duplicated `std::` prefix
    /// (e.g., `std::std::fs::remove_file`). We normalize by stripping
    /// repeated `std::` before matching. Part of #4231.
    pub(in crate::codegen_ay::chc) fn detect_fs_operation_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            let normalized = Self::normalize_std_prefix(&p);
            normalized.starts_with("std::fs::") || normalized.starts_with("core::fs::")
        })
    }

    /// Normalize paths with duplicated `std::` prefix from MIR inlining.
    ///
    /// After MIR inlining, `def_path_str()` can produce paths like
    /// `std::std::fs::remove_file` where the `std::` prefix is doubled.
    /// This collapses repeated leading `std::` segments into a single one.
    fn normalize_std_prefix(path: &str) -> &str {
        let mut s = path;
        while s.starts_with("std::std::") {
            s = &s[5..]; // strip one "std::" (5 bytes)
        }
        s
    }

    /// Detect which vtable intrinsic is being called (size or align).
    ///
    /// These appear in Box drop paths for dyn Trait types: the compiler queries
    /// the vtable for the concrete type's size and alignment to construct the
    /// Layout for deallocation. Without handling, they fall through as unhandled
    /// calls causing CTREX (EncodingGap).
    /// Part of #3159: DynTrait category recovery — vtable metadata constraining.
    pub(in crate::codegen_ay::chc) fn detect_vtable_intrinsic_kind(
        &self,
        func: &Operand,
    ) -> Option<VtableIntrinsicKind> {
        let path = self.resolve_callee_path(func)?;
        let is_core_or_std = path.starts_with("core::")
            || path.starts_with("std::")
            || path.starts_with("<core::")
            || path.starts_with("<std::");
        if !is_core_or_std {
            return None;
        }
        // Raw vtable intrinsics: core::ptr::vtable_size / vtable_align
        if path.contains("vtable_size") {
            return Some(VtableIntrinsicKind::Size);
        }
        if path.contains("vtable_align") {
            return Some(VtableIntrinsicKind::Align);
        }
        // Part of #3367: DynMetadata::size_of / DynMetadata::align_of methods.
        // These return the same vtable metadata as vtable_size/vtable_align but
        // appear as method calls on DynMetadata<dyn Trait> rather than raw
        // intrinsics. Path format: <std::ptr::DynMetadata<Dyn>>::size_of
        if path.contains("DynMetadata") {
            if path.ends_with(">::size_of") || path.ends_with("::size_of") {
                return Some(VtableIntrinsicKind::Size);
            }
            if path.ends_with(">::align_of") || path.ends_with("::align_of") {
                return Some(VtableIntrinsicKind::Align);
            }
        }
        None
    }

    /// Detect kani::mem helper functions that may not inline from kani_core.
    ///
    /// Part of #1229: `is_ptr_aligned`, `is_inbounds`, and `assert_is_initialized`
    /// are plain Rust functions without `fn_marker` attributes. If their MIR bodies
    /// are unavailable (precompiled kani_core), they appear as opaque calls.
    /// We over-approximate them soundly: alignment/bounds checks return true,
    /// initialization assertion is a no-op.
    /// Extract the generic type argument `T` from `mem::size_of::<T>` /
    /// `mem::align_of::<T>` function operands.
    pub(in crate::codegen_ay::chc) fn mem_intrinsic_type_arg(
        &self,
        func: &Operand,
    ) -> Option<rustc_public::ty::Ty> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) = func_ty.kind() else {
            return None;
        };
        fn_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _other => None, // external enum: GenericArgKind
        })
    }

    /// Translate `mem::size_of::<T>` / `mem::align_of::<T>` to BV64 constants.
    /// For dyn Trait types, uses vtable_type_metadata instead of dropping.
    /// Part of #3159: eliminate translation drops in Box<dyn Trait> dealloc.
    pub(in crate::codegen_ay::chc) fn translate_mem_intrinsic_call(
        &mut self,
        stub: StubKind,
        func: &Operand,
    ) -> Option<Expr> {
        let ty = self.mem_intrinsic_type_arg(func)?;
        let value: u64 = match stub {
            StubKind::MemSizeOf => {
                if let Some(size) = self.get_type_size(ty) {
                    size as u64
                } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                    // Part of #3159: dyn Trait → resolve from vtable metadata.
                    return Some(
                        self.dyn_trait_metadata_expr(VtableIntrinsicKind::Size, "__dyn_sizeof"),
                    );
                } else if let TyKind::RigidTy(RigidTy::Slice(elem_ty)) = ty.kind() {
                    // Part of #3464: size_of_val_raw::<[T]> for slice types.
                    // Rustc's MIR lowering of typed_swap_nonoverlapping expands to
                    // slice_from_raw_parts_mut(ptr, 1) + size_of_val_raw::<[T]>(fat_ptr).
                    // For count=1 (typed_swap), sizeof([T]) = sizeof(T). Return the
                    // element size as a sound approximation — the result flows into
                    // swap_nonoverlapping_bytes which is already an inferable predicate,
                    // so the concrete element size constrains the solver input without
                    // affecting the over-approximated swap semantics.
                    if let Some(elem_size) = self.get_type_size(elem_ty) {
                        debug!(
                            ?ty,
                            elem_size,
                            "CHC: size_of_val_raw for slice type — using element size approximation (Part of #3504)"
                        );
                        // Part of #3504: This returns sizeof(T), not sizeof(T)*len.
                        // Sound approximation for count=1 (typed_swap), but incorrect
                        // for len>1. Record fallback so the demotion pipeline demotes
                        // to OverApprox if this path is reached.
                        self.record_sound_fallback_reason("size_of_val_slice_approx");
                        elem_size as u64
                    } else {
                        warn!(
                            ?ty,
                            "CHC fail-closed: mem::size_of_val_raw slice with unknown element type, dropping translation"
                        );
                        self.record_sound_fallback_reason("size_of_val_unknown_elem");
                        return None;
                    }
                } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    // Part of #3655: str is layout-identical to [u8] (element
                    // size = 1 byte). Return sizeof(u8) = 1 as the exact
                    // element size. The Box<str> dealloc transition
                    // (emit_box_dealloc_transition) does not use the allocation
                    // size for any size-based check — it only validates
                    // obj_valid and offset==0. So returning the element size
                    // is sufficient and should NOT be classified as a sound
                    // fallback (which would cause OverApproximation CTREX).
                    debug!(?ty, "CHC: size_of for str — returning element size 1 (Part of #3655)");
                    1_u64
                } else {
                    warn!(?ty, "CHC fail-closed: mem::size_of unknown type, dropping translation");
                    self.record_sound_fallback_reason("size_of_unknown_type");
                    return None;
                }
            }
            StubKind::MemAlignOf => {
                if let Some(align) = self.get_type_align(ty) {
                    align
                } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                    return Some(
                        self.dyn_trait_metadata_expr(VtableIntrinsicKind::Align, "__dyn_alignof"),
                    );
                } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    // Part of #3655: str has alignment 1 (same as u8).
                    1_u64
                } else {
                    warn!(?ty, "CHC fail-closed: mem::align_of unknown type, dropping translation");
                    self.record_sound_fallback_reason("align_of_unknown_type");
                    return None;
                }
            }
            _ => return None, // partial dispatch: StubKind
        };
        Some(Expr::bitvec_const(value as i128, POINTER_WIDTH))
    }

    /// Resolve dyn Trait size/align. Checks vtable_type_metadata first (correct
    /// IDs from translation), falls back to predeclared_concrete_layouts (#3347).
    fn dyn_trait_metadata_expr(&self, kind: VtableIntrinsicKind, prefix: &str) -> Expr {
        let layout = self
            .vtable_type_metadata
            .values()
            .next()
            .or_else(|| self.predeclared_concrete_layouts.first());
        if let Some(&(size, align)) = layout {
            let value = match kind {
                VtableIntrinsicKind::Size => size,
                VtableIntrinsicKind::Align => align,
            };
            debug!(kind = ?kind, value, "dyn Trait mem intrinsic: from vtable metadata");
            return Expr::bitvec_const(value as u128, POINTER_WIDTH);
        }
        // Part of #3447: Record that dyn Trait mem intrinsic has no vtable
        // metadata — result is unconstrained symbolic size/align.
        self.record_aggregate_gap("intrinsic_dyn_trait_no_vtable_metadata");
        debug!(kind = ?kind, "dyn Trait mem intrinsic: symbolic (no vtable metadata)");
        declare_pending_var(chc_fresh_name(prefix), Sort::bitvec(POINTER_WIDTH))
    }
}
