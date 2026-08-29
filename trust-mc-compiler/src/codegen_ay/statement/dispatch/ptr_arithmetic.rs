// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer offset arithmetic intrinsics.
//!
//! Extracted from helpers.rs per design D1 (file-decomposition-500loc-compliance).

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

use super::super::IntoOption;

/// Whether a pointer offset carries the out-of-bounds UB obligations.
#[derive(Clone, Copy, PartialEq, Eq)]
enum OffsetUb {
    /// `ptr::offset` — leaving the object is UB.
    Checked,
    /// `arith_offset` — wrapping; leaving the object is permitted.
    Wrapping,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn codegen_ptr_offset_intrinsic(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_ptr_offset_common(args, destination, target, OffsetUb::Checked)
    }

    /// `arith_offset` — the WRAPPING pointer offset.
    ///
    /// Computing an out-of-bounds address is NOT UB here: `arith_offset` is
    /// `wrapping_offset`, and only a later dereference of the result is
    /// undefined. The corpus states exactly that — `arith-offset-overflow`
    /// calls `arith_offset(ptr, isize::MAX)` with no dereference and expects
    /// VERIFICATION:- SUCCESSFUL. So this shares the offset arithmetic and
    /// emits none of the `offset_*` obligations; the deref-site object-bounds
    /// check carries the obligation for any later read or write.
    ///
    /// Shipping this required two prior pieces, in order, and both attempts
    /// without them produced FALSE PROOFS (fail-closed demotions traded for
    /// clean SUCCESSFULs on UB): first the deref-site bounds check itself, and
    /// then real `fld_len` metadata for fat-pointer views — `&str` fat pointers
    /// were synthesized with an UNCONSTRAINED length, so the bounds check could
    /// never fire through `str::as_ptr` and `arith-offset-u8-fail` verified
    /// clean.
    pub(in crate::codegen_ay::statement) fn codegen_arith_offset_intrinsic(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_ptr_offset_common(args, destination, target, OffsetUb::Wrapping)
    }

    fn codegen_ptr_offset_common(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        ub: OffsetUb,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let ptr_operand_expr = self.codegen_operand(&args[0])?;
        let count_expr = self.codegen_operand(&args[1])?;

        // ESTABLISH that args[0] really is `*T` / `&T`.
        //
        // This used to be an inline `match ptr_ty.kind()` with a `_ => 1` arm
        // and an `else { 1 }` arm, so a non-pointer operand fell straight
        // through to the `Loc` tag below carrying a fabricated element size.
        // `pointee_size_for_offset_ty` is `None` for every `TyKind` that is not
        // `RawPtr`/`Ref` (and for an unsized pointee with no computable tail),
        // which is what makes the tag a fact instead of an assumption. It is the
        // same establisher `BinOp::Offset` in `rvalue.rs` already uses.
        let ptr_ty = args[0].ty(self.body.locals()).into_option();
        let Some(pointee_size) = ptr_ty.and_then(Self::pointee_size_for_offset_ty) else {
            warn!(
                ?ptr_ty,
                "ptr::offset: base operand is not `*T`/`&T` with a computable pointee size; \
                 demoting instead of assuming a pointer"
            );
            self.ctx
                .unsupported_with_fallback("ptr_offset_non_pointer_base", format!("{ptr_ty:?}"));
            self.codegen_symbolic_result(destination);
            return target;
        };

        let ptr_expr = self.coerce_to_ptr_width(ptr_operand_expr.clone());
        let ptr_width = ptr_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
        // Sign-extend count (isize) — negative offsets must preserve sign.
        let count_expr = Self::coerce_to_width_typed(count_expr, ptr_width, true);

        let zero = Expr::bitvec_const(0u128, ptr_width);
        let base_non_null = ptr_expr.clone().eq(zero).not();
        self.assert_guarded(base_non_null);

        let isize_max = (1u128 << (ptr_width - 1)) - 1;
        let max_valid_base = if ptr_width >= 128 {
            u128::MAX - isize_max
        } else {
            ((1u128 << ptr_width) - 1) - isize_max
        };
        let max_valid_expr = Expr::bitvec_const(max_valid_base, ptr_width);
        let base_in_range = ptr_expr.clone().bvule(max_valid_expr);
        self.assert_guarded(base_in_range);

        // ESTABLISH the address. The MIR type above says args[0] IS a pointer;
        // all that is left is whether the TERM the encoder handed back denotes
        // storage, and that is decided on the UNCOERCED term — `ptr_expr` has
        // already been through `coerce_to_ptr_width`, which is exactly the step
        // that would launder a value (or a `FALLBACK_PTR` literal) into an
        // address. args[1] is the element count, a value by role.
        let count = Val::of_value(count_expr.clone());
        if matches!(ub, OffsetUb::Wrapping) {
            // Wrapping offset: the address may legally leave the object, so
            // there is no obligation here. The deref site carries it.
        } else if let Some(base) = Self::establish_pointer_base_address(&ptr_operand_expr) {
            self.emit_offset_overflow_check(&base, &count, pointee_size);
        } else {
            // No address exists here, so `pointer_invalid` cannot be asked and
            // the wrap checks would be about a fabricated base. Fail closed via
            // the demotion counter rather than tag the fabrication `Loc`.
            warn!(
                sort = ?ptr_operand_expr.sort(),
                "ptr::offset: pointer-typed operand whose term is not an address \
                 (value widened into pointer width, or a sort `coerce_to_ptr_width` \
                 would replace with FALLBACK_PTR); dropping the offset obligations"
            );
            self.ctx.unsupported_with_fallback(
                "ptr_offset_base_not_an_address",
                format!("{:?}", ptr_operand_expr.sort()),
            );
        }

        let byte_offset = match pointee_size {
            0 => Expr::bitvec_const(0u128, ptr_width),
            1 => count_expr,
            _ => {
                // non-enum: usize (pointee_size)
                let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
                count_expr.bvmul(size_expr)
            }
        };

        let result = ptr_expr.bvadd(byte_offset);
        self.assign_value_to_place(destination, result);
        target
    }

    /// Codegen ptr_offset_from intrinsic.
    ///
    /// Part of #1490: Made pub(super) for use by KaniModel handlers.
    pub(in crate::codegen_ay::statement) fn codegen_ptr_offset_from(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        unsigned: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_expr = self.codegen_operand(&args[0])?;
        let rhs_expr = self.codegen_operand(&args[1])?;
        let lhs_ptr = self.coerce_to_ptr_width(lhs_expr);
        let rhs_ptr = self.coerce_to_ptr_width(rhs_expr);
        let ptr_width = lhs_ptr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

        let pointee_size = if let Some(ptr_ty) = args[0].ty(self.body.locals()).into_option() {
            match ptr_ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    let layout = LayoutOf::new(pointee);
                    if layout.is_sized() {
                        layout.size_of_head()
                    } else if let Some(elem_ty) = layout.unsized_tail_elem_ty() {
                        LayoutOf::new(elem_ty).size_of_head()
                    } else {
                        1
                    }
                }
                _ => 1, // external enum: TyKind
            }
        } else {
            1
        };

        let diff_bytes = lhs_ptr.clone().bvsub(rhs_ptr.clone());
        let elem_size = if pointee_size == 0 { 1 } else { pointee_size };
        let size_expr = Expr::bitvec_const(elem_size as u128, ptr_width);

        // Obligations from Kani's ptr_offset_from model
        // (library/kani_core/src/models.rs), which this handler replaces:
        // for ptr1 != ptr2 the pointers must point into the SAME allocation,
        // the byte distance must be a multiple of size_of::<T>, and the
        // unsigned variant additionally demands a non-negative distance.
        // None of these were emitted — the handler lowered straight to
        // (ptr1 - ptr2) / size, so the corpus test whose whole purpose is
        // the out-of-bounds failure reported [AY:VACUOUS:dead-checks]
        // (tests/expected/offset-bounds-check/offset_from_unsigned.rs) and
        // a genuinely UB offset_from proved SAFE. Each check follows Kani's
        // assert-then-assume lowering (code after a failed check is
        // path-constrained).
        let differs = lhs_ptr.clone().eq(rhs_ptr.clone()).not();
        let same_alloc = self
            .ctx
            .heap_pointer_object(lhs_ptr.clone())
            .eq(self.ctx.heap_pointer_object(rhs_ptr.clone()));
        self.record_violation_guarded_with_message(
            differs.clone().and(same_alloc.clone().not()),
            "ptr_offset_from_same_alloc",
            Some("Offset result and original pointer should point to the same allocation".to_string()),
        );
        let mut no_ub = differs.clone().not().or(same_alloc);
        if elem_size > 1 {
            let zero = Expr::bitvec_const(0u128, ptr_width);
            let rem_zero = diff_bytes.clone().bvsrem(size_expr.clone()).eq(zero);
            self.record_violation_guarded_with_message(
                differs.clone().and(rem_zero.clone().not()),
                "ptr_offset_from_exact_multiple",
                Some(
                    "Expected the distance between the pointers, in bytes, to be a multiple of the size of `T`"
                        .to_string(),
                ),
            );
            no_ub = no_ub.and(differs.clone().not().or(rem_zero));
        }
        if unsigned {
            let zero = Expr::bitvec_const(0u128, ptr_width);
            let non_negative = diff_bytes.clone().bvslt(zero).not();
            self.record_violation_guarded_with_message(
                differs.clone().and(non_negative.clone().not()),
                "ptr_offset_from_non_negative",
                Some("Expected non-negative distance between pointers".to_string()),
            );
            no_ub = no_ub.and(differs.not().or(non_negative));
        }
        let constraint = match &self.current_path_condition {
            None => no_ub,
            Some(pc) => pc.clone().implies(no_ub),
        };
        self.ctx.add_ordered_assumption(constraint);

        let offset =
            if unsigned { diff_bytes.bvudiv(size_expr) } else { diff_bytes.bvsdiv(size_expr) };

        self.assign_value_to_place(destination, offset);
        target
    }

    /// Codegen `KaniModel::Offset` — `ptr::offset(ptr, count)`.
    ///
    /// Part of #2912: Kani rewrites `core::ptr::offset` to this model function.
    /// Computes `ptr + count * sizeof(T)` where T is the pointee type.
    /// Essential for inlined `IntoIter::next()` which advances the read pointer.
    pub(in crate::codegen_ay::statement) fn codegen_model_offset(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        _instance: &Option<rustc_public::mir::mono::Instance>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            tracing::warn!("Model(Offset): expected 2 args, got {}", args.len());
            self.codegen_symbolic_result(destination);
            return target;
        }

        let ptr_operand_expr = self.codegen_operand(&args[0])?;
        let count_expr = self.codegen_operand(&args[1])?;

        // ESTABLISH the pointer type, exactly as `codegen_ptr_offset_intrinsic`
        // does — the `_ => 1` / `else { 1 }` arms that used to sit here let a
        // non-pointer operand reach the `Loc` tag below.
        let ptr_ty = args[0].ty(self.body.locals()).into_option();
        let Some(pointee_size) = ptr_ty.and_then(Self::pointee_size_for_offset_ty) else {
            warn!(
                ?ptr_ty,
                "Model(Offset): base operand is not `*T`/`&T` with a computable pointee \
                 size; demoting instead of assuming a pointer"
            );
            self.ctx
                .unsupported_with_fallback("ptr_offset_non_pointer_base", format!("{ptr_ty:?}"));
            self.codegen_symbolic_result(destination);
            return target;
        };

        let ptr_coerced = self.coerce_to_ptr_width(ptr_operand_expr.clone());
        let ptr_width = ptr_coerced.sort().bitvec_width().unwrap_or(POINTER_WIDTH);

        // Sign-extend count (isize) — negative offsets must preserve sign.
        let count_extended = Self::coerce_to_width_typed(count_expr, ptr_width, true);

        // Safety checks matching codegen_ptr_offset_intrinsic:
        // ptr::offset requires non-null base and no wrapping overflow.
        let zero = Expr::bitvec_const(0u128, ptr_width);
        self.assert_guarded(ptr_coerced.clone().eq(zero).not());
        // Same provenance story as `codegen_ptr_offset_intrinsic`: the address is
        // established structurally from the UNCOERCED operand term, never from
        // `coerce_to_ptr_width`'s output.
        let count = Val::of_value(count_extended.clone());
        if let Some(base) = Self::establish_pointer_base_address(&ptr_operand_expr) {
            self.emit_offset_overflow_check(&base, &count, pointee_size);
        } else {
            warn!(
                sort = ?ptr_operand_expr.sort(),
                "Model(Offset): pointer-typed operand whose term is not an address; \
                 dropping the offset obligations"
            );
            self.ctx.unsupported_with_fallback(
                "ptr_offset_base_not_an_address",
                format!("{:?}", ptr_operand_expr.sort()),
            );
        }

        let byte_offset = match pointee_size {
            0 => Expr::bitvec_const(0u128, ptr_width),
            1 => count_extended,
            _ => {
                let size_expr = Expr::bitvec_const(pointee_size as u128, ptr_width);
                count_extended.bvmul(size_expr)
            }
        };

        let result = ptr_coerced.bvadd(byte_offset);

        tracing::debug!(
            pointee_size,
            "codegen Model(Offset): ptr + count * {} = result",
            pointee_size
        );

        self.assign_value_to_place(destination, result);

        // PROVENANCE: carry the array identity across pointer arithmetic, and
        // record WHICH element the advanced pointer addresses.
        //
        // Without this, `a.as_mut_ptr().add(2)` produced an address with no
        // relationship to `a`, so a store through it was dropped and
        // `assert!(a[2] == 0)` was PROVED after writing 9. The element index is
        // encoded in the pointee NAME using the existing `_idx_by_<local>`
        // convention that `try_propagate_indexed_ref_write_to_array` already
        // understands, so the write-back reuses the machinery the `&mut a[i]`
        // path uses rather than inventing a second one.
        self.record_offset_ptr_provenance(args, destination);
        target
    }

    /// Propagate `ref_pointees` across `ptr.add(count)` / `ptr.offset(count)`,
    /// naming the element the result points at.
    ///
    /// Declines unless the base pointer has array provenance AND the count is a
    /// plain local: an unresolvable count would otherwise be silently recorded
    /// as element 0, which is a wrong answer rather than a missing one.
    fn record_offset_ptr_provenance(&mut self, args: &[Operand], destination: &Place) {
        let (Some(ptr_arg), Some(count_arg)) = (args.first(), args.get(1)) else {
            return;
        };
        let ptr_place = match ptr_arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return,
        };
        let ptr_base = self.root_ssa_base_name(ptr_place);
        let Some(array_base) = self.ref_pointees.get(ptr_base.as_str()).cloned() else {
            return;
        };
        // Already element-qualified (a second `.add` on an advanced pointer):
        // the indices would have to be summed, which this does not model.
        if array_base.contains("_idx_by_") {
            return;
        }
        let count_place = match count_arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return,
        };
        if !count_place.projection.is_empty() {
            return;
        }
        let dest_base: std::sync::Arc<str> =
            std::sync::Arc::from(self.root_ssa_base_name(destination));
        let qualified = format!("{}_idx_by_{}", array_base, count_place.local);
        debug!("Model(Offset): provenance {} -> {}", dest_base, qualified);
        self.ref_pointees.insert(dest_base, std::sync::Arc::from(qualified.as_str()));
    }

    /// Try to codegen `offset_from_unsigned::runtime_ptr_ge(self, origin) -> bool`.
    ///
    /// Part of #3783: BMC-side handler for the internal runtime check within
    /// `offset_from_unsigned`. Without this, the BMC path records an unsupported
    /// construct that taints the CHC verdict via demotion.
    ///
    /// Encodes as `bvuge(lhs, rhs)` — unsigned pointer comparison.
    pub(in crate::codegen_ay::statement) fn try_codegen_runtime_ptr_ge(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        if !(callee_path.ends_with("::runtime_ptr_ge") && callee_path.contains("::ptr::")) {
            return None;
        }
        if args.len() < 2 {
            return None;
        }

        let lhs = self.codegen_operand(&args[0])?;
        let rhs = self.codegen_operand(&args[1])?;
        let lhs = self.coerce_to_ptr_width(lhs);
        let rhs = self.coerce_to_ptr_width(rhs);

        // runtime_ptr_ge returns bool: true if self >= origin.
        let result = lhs.bvuge(rhs);
        self.assign_value_to_place(destination, result);
        target
    }
}
