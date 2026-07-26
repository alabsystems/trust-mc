// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer, NonNull, and Try::branch helpers for AY codegen (#1112).
//!
//! Extracted from alloc.rs per #2231 — NonNull::new, slice_from_raw_parts,
//! as_non_null_ptr, Option::ok_or, Try::branch, ptr::add/read/write.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::alloc::FALLBACK_PTR;
use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::{
    POINTER_WIDTH, bool_sort, int_ty_to_bitvec_width, ptr_sort, uint_ty_to_bitvec_width,
};
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `NonNull::new(ptr) -> Option<NonNull<T>>`.
    ///
    /// Wraps a raw pointer in Option<NonNull<T>>.
    /// For verification, we assume the allocation path always produces non-null pointers,
    /// so we return Some(ptr) directly.
    ///
    /// REQUIRES: args.len() >= 1 (ptr)
    /// ENSURES: destination receives non-null pointer as BitVec(POINTER_WIDTH)
    pub(super) fn codegen_nonnull_new(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_nonnull_new: missing ptr arg — fail-closed (#2497)");
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_nonnull_new: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // NonNull wraps a raw pointer. For Option<NonNull>, we construct Some(ptr).
        // The destination should be Option<NonNull<T>> datatype.
        // For simplicity, assign the pointer value directly - types will be resolved
        // at the datatype level.
        let ptr = self.coerce_to_ptr_width(ptr);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_nonnull_new: wrapped ptr in NonNull");
        target
    }

    /// Codegen `NonNull::slice_from_raw_parts(ptr, len) -> NonNull<[T]>`.
    ///
    /// Creates a slice pointer from raw parts.
    /// For verification, we treat this as pointer passthrough since we don't
    /// model slice lengths in the heap abstraction.
    ///
    /// REQUIRES: args.len() >= 1 (ptr)
    /// ENSURES: destination receives ptr as BitVec(POINTER_WIDTH)
    pub(super) fn codegen_nonnull_slice_from_raw_parts(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_nonnull_slice_from_raw_parts: missing ptr arg — fail-closed (#2497)");
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_nonnull_slice_from_raw_parts: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // For slice pointers, we just return the data pointer.
        // The length is not tracked in our heap model.
        let ptr = self.coerce_to_ptr_width(ptr);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_nonnull_slice_from_raw_parts: created slice pointer");
        target
    }

    /// Codegen `Option::ok_or(self, err) -> Result<T, E>`.
    ///
    /// Converts Option<T> to Result<T, E>.
    /// For verification with allocation paths, we assume Some(value), returning Ok(value).
    ///
    /// REQUIRES: args.len() >= 1 (option value)
    /// ENSURES: destination receives inner value (assumes Some variant)
    pub(super) fn codegen_option_ok_or(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_option_ok_or: missing option arg — fail-closed (#2497)");
            return None;
        }

        // Extract the inner value from Option (assuming Some variant)
        let option_val = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_option_ok_or: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // For allocation paths, assume we have Some(ptr), so return Ok(ptr)
        // The Result<NonNull<T>, AllocError> is constructed by assigning the inner value
        self.assign_value_to_place(destination, option_val);
        debug!("codegen_option_ok_or: converted Some to Ok");
        target
    }

    // Note: Box::new is inlined by rustc before codegen, so no stub is needed.
    // The inlined sequence stores values via raw pointer writes (*ptr = value),
    // which are tracked in heap_pointees by codegen_assign. See #1118.

    /// Codegen `NonNull::<[T]>::as_non_null_ptr() -> NonNull<T>`.
    ///
    /// Extracts the data pointer from a slice pointer.
    /// Since we model pointers as bv64 and don't track slice lengths,
    /// this is just a pointer pass-through.
    ///
    /// REQUIRES: args.len() >= 1 (self/slice pointer)
    /// ENSURES: destination receives ptr as BitVec(POINTER_WIDTH)
    pub(super) fn codegen_nonnull_as_nonnull_ptr(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Self is first argument (slice pointer)
        if args.is_empty() {
            warn!("codegen_nonnull_as_nonnull_ptr: missing self arg — fail-closed (#2497)");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "nonnull_as_nonnull_ptr_missing_arg",
                "missing self arg",
            );
            return None;
        }

        let slice_ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            warn!("codegen_nonnull_as_nonnull_ptr: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // If the slice is modeled as a (ptr, len) struct, extract the ptr field.
        // Otherwise, fall back to the raw value (bitvec).
        let data_ptr = if let Some(dt_name) = slice_ptr.clone().sort().datatype_name() {
            if slice_ptr.sort().datatype_has_field("ptr") {
                slice_ptr.field_select(dt_name, "ptr", ptr_sort())
            } else {
                self.coerce_to_ptr_width(slice_ptr)
            }
        } else {
            // Slice pointer's data pointer is the same as the slice pointer value
            // (we don't model the length separately)
            self.coerce_to_ptr_width(slice_ptr)
        };
        self.assign_value_to_place(destination, data_ptr);
        debug!("codegen_nonnull_as_nonnull_ptr: extracted data pointer from slice");
        target
    }

    /// Codegen `Allocator::allocate(&self, layout) -> Result<NonNull<[u8]>, AllocError>`.
    ///
    /// Main allocation trait method. Delegates to heap_alloc.
    ///
    /// REQUIRES: args.len() >= 2 (&self, layout)
    /// ENSURES: destination receives fresh non-null pointer
    /// ENSURES: ctx.heap tracks the new allocation
    pub(super) fn codegen_allocator_allocate(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Args: (&self, layout: Layout)
        // Skip self arg (the allocator), extract layout from args[1]
        if args.is_empty() {
            debug!("codegen_allocator_allocate: no args — fail-closed (#2455)");
            return None;
        }

        let (size, align) = if args.len() > 1 {
            if let Some(layout) = self.codegen_operand(&args[1]) {
                if let Some((s, a)) = self.try_extract_layout_fields(&layout) {
                    (s, a)
                } else if layout.sort().is_bitvec() {
                    // Layout may have been simplified to just size
                    (layout, Expr::bitvec_const(1, POINTER_WIDTH))
                } else {
                    // Non-Layout, non-bitvec: unconstrained symbolic (#2455)
                    let name = self.ctx.fresh_name("allocator_size");
                    warn!(
                        "codegen_allocator_allocate: unexpected sort {:?}, using symbolic",
                        layout.sort()
                    );
                    (Expr::var(name, ptr_sort()), Expr::bitvec_const(1, POINTER_WIDTH))
                }
            } else {
                debug!("codegen_allocator_allocate: layout codegen failed — fail-closed (#2455)");
                return None;
            }
        } else {
            // Try first arg as layout (some signatures may vary)
            if let Some(layout) = self.codegen_operand(&args[0]) {
                if let Some((s, a)) = self.try_extract_layout_fields(&layout) {
                    (s, a)
                } else if layout.sort().is_bitvec() {
                    (layout, Expr::bitvec_const(1, POINTER_WIDTH))
                } else {
                    // Non-Layout, non-bitvec: unconstrained symbolic (#2455)
                    let name = self.ctx.fresh_name("allocator_size");
                    warn!(
                        "codegen_allocator_allocate: unexpected sort {:?}, using symbolic",
                        layout.sort()
                    );
                    (Expr::var(name, ptr_sort()), Expr::bitvec_const(1, POINTER_WIDTH))
                }
            } else {
                debug!("codegen_allocator_allocate: arg[0] codegen failed — fail-closed (#2455)");
                return None;
            }
        };

        let size = self.coerce_to_ptr_width(size);
        let align = self.coerce_to_ptr_width(align);

        // Allocate and return Ok(NonNull<[u8]>)
        // For verification, we model this as returning a pointer (success case)
        let ptr = self.ctx.heap_alloc(size, align);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_allocator_allocate: allocated via Allocator trait");
        target
    }

    /// Codegen `std::ops::Try::branch(self) -> ControlFlow<Residual, Output>`.
    ///
    /// Handles the ? operator in allocation paths.
    /// Since allocation never fails (per --no-malloc-may-fail assumption),
    /// we always return the Continue variant with the success value.
    ///
    /// For Result<T, E>::branch():
    /// - Ok(v) -> ControlFlow::Continue(v)
    /// - Err(e) -> ControlFlow::Break(Err(e))
    ///
    /// We assume Ok case and return the inner value directly.
    ///
    /// REQUIRES: args.len() >= 1 (self/Result value)
    /// ENSURES: destination receives inner value as BitVec(POINTER_WIDTH)
    pub(super) fn codegen_try_branch(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        warn!("codegen_try_branch CALLED - destination={:?}", destination);
        // Self is first argument (Result/Option being branched on)
        if args.is_empty() {
            warn!("codegen_try_branch: missing self arg — fail-closed (#2497)");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback("try_branch_missing_arg", "missing self arg");
            return None;
        }

        // Part of #4112 follow-up: `<Option<T> as Try>::branch` with a datatype
        // Option self has exact semantics — encode both ControlFlow variants
        // instead of assuming Continue. Iterator desugaring (`try_fold` /
        // `advance_by`) reaches the Break path on every loop exit, so the
        // always-Continue assumption produced junk fallback pointers here.
        if self.try_codegen_try_branch_option_exact(args, destination) {
            return target;
        }

        let self_val = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            warn!("codegen_try_branch: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // For allocation paths, we have Result<NonNull<T>, AllocError>
        // Assuming allocation succeeds, this is Ok(ptr).
        // Try::branch returns ControlFlow::Continue(ptr)
        //
        // We simplify by assigning the inner value directly to destination.
        // The destination type is ControlFlow<Residual, Output>, but since
        // we only take the Continue path, we can model it as just the output.
        let value = self.coerce_to_ptr_width(self_val);
        self.assign_value_to_place(destination, value);
        debug!("codegen_try_branch: returned Continue with success value");
        target
    }

    /// Exact encoding of `<Option<T> as Try>::branch(self) -> ControlFlow<Option<Infallible>, T>`.
    ///
    /// When `self` is a proper Option datatype with a bitvec payload, the
    /// ControlFlow destination is stored piecewise (matching the flattened-enum
    /// convention that `codegen_place` / `codegen_discriminant` resolve):
    ///   - `{dest}.0`                 = ite(is_some(self), 0, 1)  (Continue=0, Break=1)
    ///   - `{dest}_variant_0_field_0` = Some-payload accessor (read only under discr==0)
    ///   - `{dest}_variant_1_field_0` = residual `Option::<Infallible>::None` (sole inhabitant)
    ///   - `{dest}`                   = payload bitvec (flattened-base convention)
    ///
    /// Returns `true` when the exact encoding was emitted (the caller proceeds to
    /// its own `target`). Returns `false` when the shape doesn't apply, so the
    /// legacy allocation-path behavior is preserved. Part of #4112 follow-up.
    fn try_codegen_try_branch_option_exact(
        &mut self,
        args: &[Operand],
        destination: &Place,
    ) -> bool {
        use ay_bindings::Sort;

        // Self must be a genuine std Option (by MIR type) ...
        let Some(self_ty) = args[0].ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Adt(self_def, _)) = self_ty.kind() else {
            return false;
        };
        if self_def.trimmed_name() != "Option" {
            return false;
        }

        // ... and a datatype value with the Option shape (one empty, one unary ctor).
        let Some(self_val) = self.codegen_operand(&args[0]) else {
            return false;
        };
        let Some(dt) = self_val.sort().datatype_sort() else {
            return false;
        };
        if dt.constructors.len() != 2 {
            return false;
        }
        let Some(some_idx) = dt.constructors.iter().position(|c| c.fields.len() == 1) else {
            return false;
        };
        let none_idx = 1 - some_idx;
        if !dt.constructors[none_idx].fields.is_empty() {
            return false;
        }
        let dt_name = dt.name.clone();
        let some_ctor_name = dt.constructors[some_idx].name.clone();

        // Flattened-base convention requires a bitvec payload.
        let Some(payload) =
            crate::codegen_ay::types::datatype_field_select(self_val.clone(), some_idx, 0)
        else {
            return false;
        };
        if !payload.sort().is_bitvec() {
            return false;
        }

        // Destination must be ControlFlow<Residual, Output> (Continue=0, Break=1).
        let Some(dest_ty) = destination.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Adt(cf_def, cf_args)) = dest_ty.kind() else {
            return false;
        };
        if cf_def.trimmed_name() != "ControlFlow" {
            return false;
        }
        let cf_variants = cf_def.variants();
        if cf_variants.len() != 2 {
            return false;
        }

        // discr: Some -> Continue (0), None -> Break (1). Exact, value-linked.
        let is_some = self_val.is_constructor(&dt_name, &some_ctor_name);
        let discr = Expr::ite(is_some, Expr::bitvec_const(0u64, 32), Expr::bitvec_const(1u64, 32));

        let dest_base = self.ssa_base_name(destination);

        let discrim_key = crate::codegen_ay::names::discrim_name(&dest_base);
        let discrim_name = self.ssa_name_from_base(&discrim_key, true);
        let discrim_var = self.ctx.declare_var(&discrim_name, Sort::bitvec(32));
        self.assert_ssa_def(discrim_var.clone(), discr, &discrim_key);
        self.env_update(discrim_key, discrim_var);

        // Continue payload: `(dest as variant#0).0`. Reads occur only on the
        // discr==0 path, where the accessor is exact.
        let cont_key = crate::codegen_ay::names::base_variant_field_name(&dest_base, 0, 0);
        let cont_name = self.ssa_name_from_base(&cont_key, true);
        let cont_var = self.ctx.declare_var(&cont_name, payload.sort().clone());
        self.assert_ssa_def(cont_var.clone(), payload.clone(), &cont_key);
        self.env_update(cont_key, cont_var);

        // Break residual: `(dest as variant#1).0` has type Option<Infallible>,
        // whose sole inhabitant is None — encode that constructor exactly when
        // the residual type supports it; otherwise leave the key unset (reads
        // fall back to the existing honest unsupported path).
        let break_field_ty = cf_variants[1]
            .fields()
            .first()
            .map(|f| f.ty())
            .and_then(|ty| Self::resolve_generic_ty(ty, &cf_args));
        if let Some(break_ty) = break_field_ty
            && let Some(residual_val) = Self::try_singleton_enum_value(break_ty)
        {
            let break_key = crate::codegen_ay::names::base_variant_field_name(&dest_base, 1, 0);
            let break_name = self.ssa_name_from_base(&break_key, true);
            let break_var = self.ctx.declare_var(&break_name, residual_val.sort().clone());
            self.assert_ssa_def(break_var.clone(), residual_val, &break_key);
            self.env_update(break_key, break_var);
        }

        // Base entry: payload bitvec (flattened-base convention, used by the
        // bv64-transparent Downcast(variant#0) path and width coercions).
        self.assign_value_to_place(destination, payload);

        debug!(
            "codegen_try_branch: exact Option->ControlFlow piecewise encoding (Part of #4112 follow-up)"
        );
        true
    }

    // Pointer arithmetic and writes

    /// Codegen `*mut T::add(count) -> *mut T`.
    ///
    /// Pointer arithmetic: returns ptr + count * sizeof(T).
    /// The offset is in units of T, not bytes.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr + offset_bytes
    pub(in crate::codegen_ay::statement) fn codegen_ptr_add(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_ptr_add: insufficient args (need ptr, count) — fail-closed (#2497)");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback("ptr_add_insufficient_args", "need ptr + count");
            return None;
        }

        // Get pointer (self)
        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_add: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        // Get count
        let count = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_add: count arg failed");
            Expr::bitvec_const(0, POINTER_WIDTH)
        });

        // Get sizeof(T) from the pointer's pointee type
        let elem_size = args[0]
            .ty(self.body.locals())
            .into_option()
            .and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    // size_of_head() returns usize, need to wrap in Some
                    Some(LayoutOf::new(pointee).size_of_head())
                }
                _ => None, // external enum: TyKind
            })
            .unwrap_or(1);

        // Compute offset in bytes: count * sizeof(T)
        let ptr_coerced = self.coerce_to_ptr_width(ptr);
        let count_coerced = self.coerce_to_ptr_width(count);
        let elem_size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
        let offset_bytes = count_coerced.bvmul(elem_size_expr);

        // New pointer = ptr + offset
        let new_ptr = ptr_coerced.bvadd(offset_bytes);
        self.assign_value_to_place(destination, new_ptr);
        debug!("codegen_ptr_add: ptr + {} * {} = new_ptr", "count", elem_size);
        target
    }

    /// Codegen `std::ptr::read(ptr) -> T`.
    ///
    /// Raw pointer load: reads a value from the memory location pointed to.
    /// No destructor is called on the source value, it's a bitwise copy.
    ///
    /// For verification, we model this as returning a symbolic value of type T,
    /// since we don't track heap contents at the byte level.
    ///
    /// REQUIRES: args.len() >= 1 (ptr)
    /// ENSURES: destination receives a symbolic value of destination type
    pub(in crate::codegen_ay::statement) fn codegen_ptr_read(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Get the destination type to create an appropriate symbolic value
        let dest_ty = destination.ty(self.body.locals()).into_option();

        // Evaluate the pointer argument for any side effects, but we don't
        // actually track what's stored at that address in our simplified model.
        if !args.is_empty() {
            let _ptr = self.codegen_operand(&args[0]);
        }

        // Return a symbolic value for the read result.
        // In a more complete model, we would look up the value in heap_pointees.
        // For now, create a symbolic value of the destination type.
        let value = dest_ty.and_then(|ty| self.symbolic_value_for_type(ty)).unwrap_or_else(|| {
            // Fallback to a non-deterministic pointer-width value
            debug!("codegen_ptr_read: unknown destination type, using symbolic bv64");
            let name = self.ctx.fresh_name("ptr_read");
            Expr::var(name, ptr_sort())
        });

        self.assign_value_to_place(destination, value);
        debug!("codegen_ptr_read: returned symbolic value");
        target
    }

    /// Create a symbolic value for the given type.
    fn symbolic_value_for_type(&mut self, ty: rustc_public::ty::Ty) -> Option<Expr> {
        use rustc_public::ty::RigidTy::{Bool, Int, RawPtr, Ref, Uint};

        let name = self.ctx.fresh_name("sym");
        match ty.kind() {
            TyKind::RigidTy(Bool) => Some(Expr::var(name, bool_sort())),
            TyKind::RigidTy(Int(k)) => {
                Some(Expr::var(name, ay_bindings::Sort::bitvec(int_ty_to_bitvec_width(k))))
            }
            TyKind::RigidTy(Uint(k)) => {
                Some(Expr::var(name, ay_bindings::Sort::bitvec(uint_ty_to_bitvec_width(k))))
            }
            TyKind::RigidTy(RawPtr(_, _)) | TyKind::RigidTy(Ref(_, _, _)) => {
                Some(Expr::var(name, ptr_sort()))
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Codegen `*mut T::write(value)`.
    ///
    /// Raw pointer store: writes value to the memory location pointed to by self.
    /// No destructor is called on any existing value, and no drop flags are modified.
    ///
    /// For BMC verification, we model this as a no-op since:
    /// 1. Heap content arrays aren't tracked (only validity/size)
    /// 2. The write happens but doesn't affect verification conditions
    /// 3. A full model would add heap content tracking (future work)
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, value)
    /// ENSURES: continues to target block (store effect not modeled)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_write(
        &mut self,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // REQUIRES: args.len() >= 2 (self ptr, value)
        // Fail-closed on insufficient args (#2721) — consistent with all other
        // pointer functions in this file.
        if args.len() < 2 {
            warn!("codegen_ptr_write: insufficient args (need ptr, value) — fail-closed (#2721)");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback("ptr_write_insufficient_args", "need ptr + value");
            return None;
        }

        // Evaluate operands for side effects, but don't model the store.
        // The heap model tracks validity/size but not content.
        let _ptr = self.codegen_operand(&args[0]);
        let _value = self.codegen_operand(&args[1]);
        debug!("codegen_ptr_write: store operation (content not modeled)");
        target
    }
}
