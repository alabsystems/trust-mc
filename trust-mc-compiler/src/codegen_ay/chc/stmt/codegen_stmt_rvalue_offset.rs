// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer offset rvalue translation and overflow checks for CHC encoding.
//!
//! Extracted from `codegen_stmt_rvalue.rs` per #3920 to reduce merge-conflict
//! contention. Contains `translate_pointer_offset_with_modified` and
//! `ptr_offset_overflow_conditions`.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value;
use crate::codegen_ay::chc::expr::codegen_expr_signedness::ExprSignedness;
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::pointer_step::step_split_pointer;

use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};

/// One hop of the fail-closed offset-provenance walk
/// (`single_assign_stack_owner_local`).
enum OffsetProvenanceStep {
    /// The chain terminates: this local OWNS the allocation.
    Owner(usize),
    /// Part of #72: the chain terminates at a promoted-const `&T` operand
    /// (`Use(Constant)` def, e.g. `let v: &[u128] = &[0; 10]`). Carries the
    /// pointee type whose layout size is the allocation extent; promoted
    /// const addresses are encoded `obj_id ## 0`
    /// (`promoted_const_address_for`), so walked offset lanes are
    /// allocation-relative exactly as for stack owners.
    ConstRef(rustc_public::ty::Ty),
    /// Allocation-preserving hop to the defining source local.
    Through(usize),
    /// Raw-alloc route: the chain terminates at the destination local of a
    /// `__rust_alloc` / `__rust_alloc_zeroed` stub call (`std::alloc::alloc`
    /// family). The local is single-assignment (walk precondition), so the
    /// `known_alloc_ids` entry recorded by the stub is uniquely attributable
    /// to that one call site — the flow-insensitivity objection to metadata
    /// side-tables does not apply. The stub returns `concat(obj_id, 0)`
    /// (allocation start), so walked offset lanes are allocation-relative
    /// exactly as for stack owners.
    HeapAlloc(usize),
}

/// P4-3: base local of a (possibly field-projected) place.
fn place_local_of(place: &rustc_public::mir::Place) -> usize {
    place.local
}

/// P4-3: whether `ty` is `std::vec::Vec<..>`.
fn is_vec_adt_ty(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::CrateDef;
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Vec")
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate `BinOp::Offset` for pointer arithmetic.
    ///
    /// MIR `Offset` uses element counts, not raw byte counts, so we scale the offset
    /// by the pointee size when pointer type info is available.
    ///
    /// Part of #3920: extracted from `codegen_stmt_rvalue.rs`.
    pub(in crate::codegen_ay::chc) fn translate_pointer_offset_with_modified(
        &mut self,
        lhs_op: &Operand,
        rhs_op: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let lhs = self.translate_operand_with_modified(lhs_op, modified_locals)?;
        let rhs = self.translate_operand_with_modified(rhs_op, modified_locals)?;

        // Part of #2875: Coerce Int-lifted operands to BV before pointer arithmetic.
        let lhs = if lhs.sort().is_int() { lhs.int2bv(POINTER_WIDTH) } else { lhs };
        let rhs = if rhs.sort().is_int() { rhs.int2bv(POINTER_WIDTH) } else { rhs };
        // Part of #2007: If the pointer operand is not a bitvec (e.g., Int sort
        // from BigInt), we cannot compute a meaningful pointer offset.
        if !lhs.sort().is_bitvec() {
            debug!("translate_ptr_offset: lhs is not bitvec ({:?}), returning None", lhs.sort());
            return None;
        }
        let lhs_ptr = coerce_bitvec_width_safe(lhs, POINTER_WIDTH, SignExtension::ZeroExtend);
        // Offsets are signed (isize) in MIR pointer arithmetic.
        let rhs_count = coerce_bitvec_width_safe(rhs, POINTER_WIDTH, SignExtension::SignExtend);

        let pointee_size_opt = lhs_op.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.get_type_size(inner),
            _ => None, // external enum: TyKind
        });
        let pointee_size = if let Some(s) = pointee_size_opt {
            s
        } else {
            // Part of #3099: Reclassified to SOUND_APPROXIMATION — unknown
            // pointee size means offset result is unconstrained (universally
            // quantified). Returns fresh symbolic instead of None to avoid
            // double-counting: returning None would trigger the parent
            // self-loop handler's record_fallback() (DEMOTED).
            warn!("CHC: Offset pointee size unknown — sound over-approximation");
            self.record_sound_fallback_reason("offset_pointee_size_unknown");
            let name = chc_fresh_name("__ptr_offset_nondet");
            return Some(declare_pending_var(name, ptr_sort()));
        };

        let byte_offset = if pointee_size == 1 {
            rhs_count
        } else {
            rhs_count.bvmul(Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH))
        };

        // Part of #3921: use split-pointer step to preserve obj_id.
        Some(step_split_pointer(lhs_ptr, byte_offset).result)
    }

    /// Generate pointer offset overflow safety check conditions for `BinOp::Offset` (#3300).
    ///
    /// Mirrors the logic from `stubs_ptr_overflow.rs::emit_ptr_offset_overflow_error_rules`,
    /// but instead of emitting error rules directly, returns conditions to be pushed
    /// to `safety_checks` (consumed by the caller's error rule emission).
    ///
    /// Checks, each a "no_overflow" condition (positive — must be true for correctness):
    /// 1. `offset_value_overflow`: count within isize bounds
    /// 2. `offset_bytes_overflow`: count * sizeof(T) doesn't overflow isize
    /// 3. `offset_result_overflow`: ptr + byte_offset doesn't wrap around
    /// 4. `offset_alloc_bound`: result stays within the base allocation
    ///    (inclusive of one-past-end) when the base obj_id const-folds
    ///
    /// Default-on under `memory_safety_checks`. The provenance-validity check
    /// (obj_valid select) additionally requires `extra_pointer_checks` because
    /// it references heap-metadata state arrays that never const-fold, which
    /// defeats static discharge of fully-concrete harnesses.
    pub(in crate::codegen_ay::chc) fn ptr_offset_overflow_conditions(
        &mut self,
        lhs_op: &Operand,
        rhs_op: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Vec<Expr> {
        let mut checks = Vec::new();

        let Some(lhs) = self.translate_operand_with_modified(lhs_op, modified_locals) else {
            return checks;
        };
        let Some(rhs) = self.translate_operand_with_modified(rhs_op, modified_locals) else {
            return checks;
        };

        // Coerce to bitvec, same as translate_pointer_offset_with_modified.
        let lhs = if lhs.sort().is_int() { lhs.int2bv(POINTER_WIDTH) } else { lhs };
        let rhs = if rhs.sort().is_int() { rhs.int2bv(POINTER_WIDTH) } else { rhs };

        if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
            return checks;
        }

        let ptr = coerce_bitvec_width_safe(lhs, POINTER_WIDTH, SignExtension::ZeroExtend);
        // `BinOp::Offset`'s RHS is the element COUNT: an integer VALUE, never an
        // address. It is sign-extended to pointer width purely so the arithmetic
        // below is well-typed against `ptr` — that coercion is why every later
        // "is this 64 bits wide?" test on `count` is uninformative.
        let count =
            Val::of_value(coerce_bitvec_width_safe(rhs, POINTER_WIDTH, SignExtension::SignExtend));

        // Resolve pointee size (same logic as translate_pointer_offset_with_modified).
        let pointee_size = lhs_op.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.get_type_size(inner),
            _ => None,
        });
        let Some(pointee_size) = pointee_size else {
            return checks;
        };

        let isize_max = Expr::bitvec_const((1i128 << (POINTER_WIDTH - 1)) - 1, POINTER_WIDTH);
        let isize_min = Expr::bitvec_const(-(1i128 << (POINTER_WIDTH - 1)), POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);

        // Constant-count fast-path: fold the count-only checks numerically so
        // fully-concrete offsets don't leave live error rules (static discharge).
        //
        // SOUNDNESS (#4118): the signedness must come from the count OPERAND's
        // own type, not a hardcoded `true`. `in_range` is
        // `count_is_signed || value <= isize_max`, so pinning it to `true` made
        // every 64-bit two's-complement value "in range" — check 1 was VACUOUS
        // for all concrete counts. `ptr.add(count: usize)` lowers to MIR
        // `Offset` with an UNSIGNED count, whose real obligation is
        // `count <= isize::MAX`; that is exactly the check Kani's
        // `to_isize.safety_check` performs. `unwrap_or(false)` matches the
        // KaniModel twin (codegen_call_kani_model.rs) and fails closed: unknown
        // signedness is treated as unsigned, i.e. the check is emitted.
        let count_signedness = self.operand_signedness(rhs_op);
        if count_signedness.is_none() {
            // Neither reading is safe to assume when the count's type is
            // unknown: one 64-bit pattern is a huge positive under the unsigned
            // reading and a small negative under the signed one. Asserting the
            // unsigned bound would FABRICATE a violation for `ptr.offset(-1)`;
            // asserting the signed range is vacuous. So skip the obligation and
            // fail closed instead — an unaudited reason hits the catch-all
            // `FallbackSoundness::FailClose` and stays UNACCOUNTED, so no Safe
            // verdict can rest on the range check being skipped here.
            self.record_sound_fallback_reason("offset_count_signedness_unknown");
        }
        // Signed on the unknown path so the fold cannot manufacture a failure;
        // the demotion above is what keeps that case honest.
        let count_is_signed = count_signedness.unwrap_or(true);
        let const_count_checks =
            Self::const_fold_offset_count_checks(&count, count_is_signed, pointee_size as u64);

        // Check 1: offset value within isize bounds. KINDED (PointerOverflow +
        // Kani's exact message) via pending_kinded_checks so the failing check
        // renders a named per-property report line and the exact-derivation
        // lane attributes the CTREX Genuine — instead of the anonymous
        // aggregate `chc.0` that classified as CtrexCategory::Unknown
        // (Overflow/pointer_overflow_fail, expected/pointer-overflow).
        //
        // ZST-EXEMPT (#3896, #4118): `offset` accepts a `count` past isize::MAX
        // for ZSTs, because the byte offset is `count * 0 == 0`. Kani's oracle
        // in expected/offset-overflows-isize pins this exactly — `test_zst` and
        // `test_non_zst` pass the SAME `(isize::MAX as usize) + 1`, and only the
        // non-ZST one fails — so this obligation must be skipped when the
        // pointee is zero-sized. (Check 4 below is deliberately NOT exempt.)
        if pointee_size != 0 {
            match const_count_checks {
                Some((true, _)) => {}
                Some((false, _)) => self.heap_state.pending_kinded_checks.push((
                    Expr::bool_const(false),
                    trust_mc_core::violation::PropertyKind::PointerOverflow,
                    Some("Offset value overflows isize".to_string()),
                )),
                None => {
                    // An unsigned count needs the UNSIGNED bound: every 64-bit
                    // value satisfies the signed range, so `bvsle/bvsge` would
                    // be vacuous here for the same reason the fold was.
                    let count_in_range = if count_is_signed {
                        count
                            .as_expr()
                            .clone()
                            .bvsle(isize_max)
                            .and(count.as_expr().clone().bvsge(isize_min))
                    } else {
                        count.as_expr().clone().bvule(isize_max)
                    };
                    self.heap_state.pending_kinded_checks.push((
                        count_in_range,
                        trust_mc_core::violation::PropertyKind::PointerOverflow,
                        Some("Offset value overflows isize".to_string()),
                    ));
                    debug!("CHC: generated offset_value_overflow safety check (#3300)");
                }
            }
        }

        // Check 4 (Part of #3176): base pointer has valid allocation provenance.
        // Applies even for ZST offsets: pointer arithmetic on a dangling base
        // should still fail under extra_pointer_checks. Stays gated: the
        // obj_valid select references state arrays that never const-fold.
        if self.extra_pointer_checks && !self.int_lift {
            if let Some((obj_id, _offset)) = self.split_pointer(&ptr) {
                let obj_valid = self.current_obj_valid_array();
                // Part of #3221: track metadata access for pruning correctness.
                self.mark_heap_metadata_read();
                let is_valid = obj_valid.select(obj_id);
                checks.push(is_valid);
                debug!("CHC: generated provenance_valid safety check (#3176)");
            }
        }

        // For ZST (size 0), no byte offset, so no further checks needed.
        if pointee_size == 0 {
            return checks;
        }

        // Check 2: byte offset overflow (count * sizeof(T) doesn't overflow).
        // KINDED — see check 1; message matches Kani's expected-file text.
        if pointee_size > 1 {
            match const_count_checks {
                Some((_, true)) => {}
                Some((_, false)) => self.heap_state.pending_kinded_checks.push((
                    Expr::bool_const(false),
                    trust_mc_core::violation::PropertyKind::PointerOverflow,
                    Some("Offset in bytes overflows isize".to_string()),
                )),
                None => {
                    let size_expr = Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH);
                    let offset = count.as_expr().clone().bvmul(size_expr.clone());
                    let div_back = offset.bvsdiv(size_expr);
                    let no_mul_overflow = div_back.eq(count.as_expr().clone());
                    self.heap_state.pending_kinded_checks.push((
                        no_mul_overflow,
                        trust_mc_core::violation::PropertyKind::PointerOverflow,
                        Some("Offset in bytes overflows isize".to_string()),
                    ));
                    debug!("CHC: generated offset_bytes_overflow safety check (#3300)");
                }
            }
        }

        // Check 4b gate (see below). Computed early because the P4-3
        // projected-Vec lane also depends on it.
        //
        // SOUNDNESS GATE on the metadata side-channel: only resolve provenance
        // when the count-only checks POSITIVELY fold clean (concrete count, no
        // isize-range or byte-product overflow). Resolving on a symbolic or
        // overflowing count removes the OffsetProvenanceUnresolved demotion —
        // the load-bearing fail-closed net — while the overflow obligation can
        // still be lost downstream (offset-bytes-overflow: count=2^60, byte
        // product wraps to exactly 2^64 -> vacuous discharge -> false Safe).
        // With the gate, such shapes keep the wave-2 demotion.
        let count_checks_fold_clean = matches!(const_count_checks, Some((true, true)));

        // P4-3: projected-Vec base lane. `vec.as_ptr().add(k)` has heap
        // provenance the stack walk refuses, so the harness previously kept
        // the OffsetProvenanceUnresolved demotion even when the value model
        // was exact. When the base pointer fail-closed-traces to a projected
        // Vec's data start, the buffer extent IS the seeded cap state var
        // (element units): emit `0 <= k && k <= cap` (one-past-end inclusive)
        // as the alloc-bound obligation. Same const-fold-clean soundness gate
        // as the stack lane (symbolic/overflowing counts keep the demotion).
        //
        // P3-uninit: resolved BEFORE the wrap / same-object checks — those
        // operate on the 32-bit offset LANE of the split-pointer ENCODING of
        // `fld_ptr`, which for a projected Vec base is an unconstrained
        // symbolic value, so the solver can pick a lane value that "wraps"
        // and produce a spurious Genuine-looking CTREX (vec-read-init FP).
        // Semantically the cap bound subsumes them for this lane: the walk
        // proves the base is the ALLOCATION START (buffer offset 0), Rust
        // allocations fit isize, and the gate has already checked the
        // concrete count and its byte product fit isize — a real address at
        // offset 0 stepping 0 <= k <= cap cannot wrap and cannot change
        // objects.
        if count_checks_fold_clean
            && let Some(vec_bound) = self.projected_vec_offset_bound_for_operand(
                lhs_op,
                count.as_expr(),
                modified_locals,
            )
        {
            checks.push(vec_bound);
            debug!("CHC: generated projected-Vec offset_alloc_bound safety check (P4-3)");
            return checks;
        }

        // Raw-alloc route: anchored fold lane. When the base pointer provably
        // sits at a CONCRETE byte delta from the start of a `__rust_alloc`
        // allocation with a CONCRETE size, the whole bound folds numerically
        // at emission (no live error rule for in-bounds steps; an
        // unconditional error rule for out-of-bounds ones). Subsumes the
        // wrap / same-object checks by the same argument as the P4-3 Vec
        // lane: the base is a real address at a concrete in-extent offset,
        // the fold-clean gate verified the concrete count and its byte
        // product, and the folded end offset lies in `[0, size]` — such a
        // step cannot wrap and cannot change objects.
        if count_checks_fold_clean
            && let Some(bound) = self.anchored_alloc_offset_bound_for_operand(
                lhs_op,
                count.as_expr(),
                pointee_size as u64,
            )
        {
            checks.push(bound);
            debug!("CHC: folded anchored raw-alloc offset_alloc_bound (raw-alloc route)");
            return checks;
        }

        // Check 3: result pointer doesn't wrap around address space.
        // Part of #3921: use split-pointer step for same-object preservation.
        let byte_offset = if pointee_size > 1 {
            count.as_expr().clone().bvmul(Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH))
        } else {
            count.as_expr().clone()
        };
        let step = step_split_pointer(ptr.clone(), byte_offset);
        let result_ptr = step.result;

        // If offset positive and result < ptr → wrapped forward.
        let positive_offset = count.as_expr().clone().bvsge(zero.clone());
        let wrapped_forward = positive_offset.and(result_ptr.clone().bvult(ptr.clone()));
        // If offset negative and result > ptr → wrapped backward.
        let negative_offset = count.as_expr().clone().bvslt(zero);
        let wrapped_backward = negative_offset.and(result_ptr.clone().bvugt(ptr.clone()));
        let no_ptr_wrap = wrapped_forward.or(wrapped_backward).not();
        checks.push(no_ptr_wrap);
        debug!("CHC: generated offset_result_overflow safety check (#3300)");

        // When split-pointer recomposition was used, enforce same-object preservation.
        if let Some(same_object_ok) = step.same_object_ok {
            checks.push(same_object_ok);
            debug!("CHC: generated split_pointer_same_object safety check (#3921)");
        }

        // Check 4b: allocation-size bound — the previously-vacuous part of the
        // "same allocation" guarantee. Without it, in-bounds-lane OOB steps
        // (e.g. base+10 over a 5-byte buffer) passed all checks above.
        // (Gate `count_checks_fold_clean` computed above.)

        let known_obj_id =
            count_checks_fold_clean.then(|| self.offset_bound_obj_id_for_operand(lhs_op)).flatten();
        if let Some(bound_ok) = self.ptr_offset_alloc_bound_check(&ptr, &result_ptr, known_obj_id) {
            checks.push(bound_ok);
            debug!("CHC: generated offset_alloc_bound safety check");
        }

        checks
    }

    /// P4-3: cap-based alloc-bound for an offset whose base pointer provably
    /// denotes a projected Vec's data start (`vec.as_ptr()` /
    /// `vec.as_mut_ptr()`, buffer offset 0).
    ///
    /// Fail-closed by construction, mirroring the stack lane's discipline:
    /// every hop of the backward walk must be a SINGLE-ASSIGNMENT local, the
    /// hops are value-preserving only (plain Copy/Move + pointer-preserving
    /// casts), and the walk terminates ONLY at a field-projection read out of
    /// a Vec-typed local (the inlined `as_ptr` buffer-pointer read — any
    /// pointer-typed field path out of Vec is the buffer pointer, which sits
    /// at allocation offset 0). Arithmetic hops (`ptr.add` chains) are
    /// call/BinOp-defined and therefore refused — a non-zero base offset can
    /// never sneak through. The pointee size must equal the element width so
    /// the count is in element units.
    ///
    /// The returned obligation `0 <= count && count <= cap` is
    /// proof-STRENGTHENING relative to the demotion it replaces: cap is the
    /// exact buffer extent seeded by the Vec constructor stubs.
    pub(in crate::codegen_ay::chc) fn projected_vec_offset_bound_for_operand(
        &mut self,
        op: &Operand,
        count: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use crate::codegen_ay::chc::codegen_ctx::types::CollectionProjectionKind;
        use rustc_public::mir::{CastKind, Rvalue, StatementKind};

        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }

        // Fail-closed single-assignment backward walk to a Vec-typed source.
        //
        // `via_as_ptr` guards the `&vec` ref terminal: a plain `&vec` holds a
        // pointer to the Vec HEADER (24 bytes) — only the `Vec::as_ptr` /
        // `as_mut_ptr` return value is the BUFFER start whose extent is `cap`.
        let mut current = place.local;
        let mut seen = HashSet::from([current]);
        let mut vec_local: Option<usize> = None;
        let mut via_as_ptr = false;
        'walk: for _ in 0..12 {
            if !self.encode.single_assign_locals.contains(&current) {
                return None;
            }
            let mut next: Option<usize> = None;
            'find: for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(dest, rhs) = &stmt.kind else { continue };
                    if dest.local != current || !dest.projection.is_empty() {
                        continue;
                    }
                    let src = match rhs {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => p,
                        Rvalue::CopyForDeref(p) => p,
                        Rvalue::Cast(kind, Operand::Copy(p) | Operand::Move(p), _)
                            if matches!(
                                kind,
                                CastKind::PtrToPtr
                                    | CastKind::PointerCoercion(_)
                                    | CastKind::Transmute
                                    | CastKind::Subtype
                            ) =>
                        {
                            p
                        }
                        // `_r = &vec` / `&raw vec`: the as_ptr receiver. Only
                        // a data-start terminal when the walk already passed
                        // through the as_ptr call itself.
                        Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p)
                            if via_as_ptr
                                && p.projection.is_empty()
                                && self
                                    .body
                                    .locals()
                                    .get(p.local)
                                    .is_some_and(|decl| is_vec_adt_ty(decl.ty)) =>
                        {
                            vec_local = Some(p.local);
                            break 'walk;
                        }
                        _ => return None,
                    };
                    let src_local = place_local_of(src);
                    if self.body.locals().get(src_local).is_some_and(|decl| is_vec_adt_ty(decl.ty))
                    {
                        // Terminal: a (field-projected) read out of the Vec —
                        // the buffer pointer at allocation offset 0.
                        vec_local = Some(src_local);
                        break 'walk;
                    }
                    if !src.projection.is_empty() {
                        // Field reads out of NON-Vec sources (NonNull/Unique
                        // wrappers, arbitrary structs) are not provably the
                        // allocation start — refuse.
                        return None;
                    }
                    if !seen.insert(src_local) {
                        return None;
                    }
                    next = Some(src_local);
                    break 'find;
                }
            }
            if next.is_none() {
                // No statement def — the unique def may be a Call terminator:
                // `_p = Vec::as_ptr(&vec)` / `as_mut_ptr`. Hop to the receiver.
                for bb in &self.body.blocks {
                    let rustc_public::mir::TerminatorKind::Call { func, args, destination, .. } =
                        &bb.terminator.kind
                    else {
                        continue;
                    };
                    if destination.local != current || !destination.projection.is_empty() {
                        continue;
                    }
                    let Some(path) = self.resolve_callee_path(func) else { return None };
                    let is_vec_as_ptr = (path.ends_with("::as_ptr")
                        || path.ends_with("::as_mut_ptr"))
                        && path.contains("Vec");
                    if !is_vec_as_ptr {
                        return None;
                    }
                    let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else {
                        return None;
                    };
                    if !p.projection.is_empty() {
                        return None;
                    }
                    via_as_ptr = true;
                    if !seen.insert(p.local) {
                        return None;
                    }
                    next = Some(p.local);
                    break;
                }
            }
            current = next?;
        }
        let vec_local = vec_local?;
        if self.collections.projection_locals.get(&vec_local).copied()
            != Some(CollectionProjectionKind::Vec)
        {
            return None;
        }

        // Element units: pointee size must equal the data-array element width.
        let pointee_size = op.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.get_type_size(inner),
            _ => None,
        })?;
        let base_idx = self.try_state_idx_for_local(vec_local)?;
        let vars = if modified_locals.contains(&vec_local) {
            &self.state_var_mgr.output_state_vars
        } else {
            &self.state_var_mgr.state_vars
        };
        let elem_width = vars
            .get(base_idx + 3)
            .and_then(|(_, s)| s.array_sort())
            .and_then(|arr| Self::sort_byte_width(&arr.element_sort))?;
        if elem_width == 0 || elem_width != pointee_size {
            return None;
        }
        let (cap_name, cap_sort) = vars.get(base_idx + 2).cloned()?;
        let cap = Expr::var(&*cap_name, cap_sort);
        let cap64 = coerce_bitvec_width_safe(cap, POINTER_WIDTH, SignExtension::ZeroExtend);

        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        debug!(
            base_local = place.local,
            vec_local, elem_width, "offset alloc-bound: resolved projected-Vec cap bound (P4-3)"
        );
        Some(count.clone().bvsge(zero).and(count.clone().bvule(cap64)))
    }

    /// Numerically folds the count-only offset checks when `count` is a
    /// 64-bit constant. Returns `(count_in_range, mul_no_overflow)` with the
    /// exact semantics of the symbolic checks:
    /// - `count_in_range`: count within isize bounds (`bvule isize_max` for
    ///   unsigned counts; trivially true for signed 64-bit counts)
    /// - `mul_no_overflow`: `bvsdiv(bvmul(count, size), size) == count`
    ///
    /// Emission-time folding matters for static discharge: the straightline
    /// prover does not fold `bvsdiv`, so a fully-concrete harness would keep
    /// a live error rule and lose whole-harness collapse to `false => error`.
    pub(in crate::codegen_ay::chc) fn const_fold_offset_count_checks(
        count: &Val,
        count_is_signed: bool,
        pointee_size: u64,
    ) -> Option<(bool, bool)> {
        let (value, width) = const_bv_value(count.as_expr())?;
        // Address-vs-value (wave 1): `count` is a VALUE, so this is NOT the
        // "is it a pointer?" test it used to read as. It is a genuine
        // precondition of the fold ITSELF — every constant below (`1 << 64`,
        // `1 << 63`, the isize bound) is 64-bit two's-complement arithmetic, so
        // a differently-sized constant simply cannot be folded here and must
        // fall through to the symbolic obligation. RETAINED deliberately:
        // widening it would mean folding at other widths, which is a semantic
        // change, not a retyping. See the conversion queue, wave 1.
        if width != 64 {
            return None;
        }
        let modulus = BigInt::from(1u8) << 64u32;
        let half = BigInt::from(1u8) << 63u32;
        let isize_max = &half - 1u8;
        let signed_value = if value >= half { &value - &modulus } else { value.clone() };

        // Any 64-bit two's-complement value is within [isize::MIN, isize::MAX];
        // only the unsigned interpretation can exceed isize::MAX.
        let in_range = count_is_signed || value <= isize_max;

        let mul_ok = if pointee_size <= 1 {
            true
        } else {
            // Exact bvmul/bvsdiv semantics: wrap the product to 64-bit
            // two's complement, then signed division truncating toward zero
            // (BigInt `/` truncates toward zero, matching bvsdiv).
            let size = BigInt::from(pointee_size);
            let product = &signed_value * &size;
            let wrapped = ((product % &modulus) + &modulus) % &modulus;
            let wrapped_signed = if wrapped >= half { &wrapped - &modulus } else { wrapped };
            &wrapped_signed / &size == signed_value
        };

        Some((in_range, mul_ok))
    }

    /// Allocation-size bound for pointer arithmetic: the stepped pointer must
    /// land inside the base pointer's allocation, INCLUSIVE of the
    /// one-past-end address (this is pointer arithmetic, not a dereference —
    /// the per-access checks in `heap_access_checks` own the strict bound).
    ///
    /// The lower bound (`base_offset + byte_offset >= 0`) is already enforced
    /// by the `same_object_ok` lane-carry/underflow predicate from
    /// `step_split_pointer`, so only the upper bound is emitted here.
    ///
    /// Emits only when the base pointer's obj_id lane const-folds; genuinely
    /// unknown provenance keeps the fail-open discipline of
    /// `heap_access_checks` (the allocation size is a caller contract we
    /// cannot invent). Size resolution mirrors `heap_access_checks`:
    /// stack-local layout, then known heap allocations, then the `obj_size`
    /// metadata array (which the entry rule seeds for statics and promoted
    /// constants).
    /// Real byte length of a promoted-constant allocation, derived from its
    /// seeded memory-init entries (max byte_offset + element byte width).
    /// The entry rule seeds `obj_size` with a GENEROUS 4096 for promoted
    /// regions (dealloc-check convention), so the metadata array is useless
    /// for offset-bound precision; this is the exact object extent, enabling
    /// the constant fast-path to fold offset bound checks statically instead
    /// of dragging the obj_size array into the solver query.
    fn promoted_const_byte_size(&self, obj_id: u32) -> Option<u32> {
        let mut end: Option<u32> = None;
        for (_, elem_sort, _, promoted_obj_id, byte_offset) in
            &self.ref_resolution.const_ref_memory_inits
        {
            if *promoted_obj_id != obj_id {
                continue;
            }
            let width = elem_sort.bitvec_width().unwrap_or(8).div_ceil(8) as u64;
            let entry_end = u32::try_from(byte_offset + width).ok()?;
            end = Some(end.map_or(entry_end, |e| e.max(entry_end)));
        }
        end
    }

    /// Metadata-side-channel provenance for a pointer operand: the allocation
    /// id recorded for the operand's (unprojected) local by the identity call
    /// routes (`known_alloc_ids`) or the promoted-constant collector
    /// (`const_ref_promoted_obj_ids`). Used by the offset alloc-bound checks
    /// when the value's obj_id lane is an opaque SSA variable rather than a
    /// syntactic `concat`.
    pub(in crate::codegen_ay::chc) fn known_obj_id_for_operand(&self, op: &Operand) -> Option<u32> {
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        let id = self.known_alloc_ids.get(&place.local).copied().or_else(|| {
            self.ref_resolution.const_ref_promoted_obj_ids.get(&place.local).copied()
        })?;
        // SCOPE: promoted-const allocations ONLY. For str/slice literals the
        // FULL check chain is verified to engage (offset alloc-bound with the
        // real byte length + deref-site `idx < len`). For heap/stack ids the
        // provenance demotion is today the accidental-but-load-bearing net
        // over missing models (e.g. -Z uninit-checks shadow memory:
        // alloc-to-slice went false-Safe when heap provenance resolved) — do
        // NOT resolve those here until their real checks exist.
        self.is_promoted_const_obj_id(id).then_some(id)
    }

    /// Offset-site provenance for the ALLOC-BOUND-emitting offset paths
    /// (`BinOp::Offset` rvalues and `KaniModel::Offset` calls): the
    /// promoted-const lane of `known_obj_id_for_operand`, plus a gated STACK
    /// lane (offset-deref stack-provenance keystone).
    ///
    /// The stack lane resolves the base allocation of an offset over a stack
    /// object (e.g. `arr.as_ptr()` whose obj_id lane is an opaque SSA state
    /// var) so the REAL `result_offset <= alloc_size` obligation is emitted
    /// instead of the `OffsetProvenanceUnresolved` demotion. It is
    /// deliberately NOT part of `known_obj_id_for_operand`: the arith_offset
    /// route consults that method to SUPPRESS its demotion without emitting a
    /// bound at the offset site, so widening it would trade the fail-closed
    /// net for an unverified deref-side check chain.
    ///
    /// Gates (each individually load-bearing — a wrong (obj, size) recovery
    /// here is a false-Safe factory):
    /// - operand local is SINGLE-ASSIGNMENT (#3905 prescan): the metadata
    ///   side-tables are flow-insensitive (last-processed-block wins), so a
    ///   branch-merged pointer could resolve to the WRONG object — with a
    ///   larger claimed size that proves a real OOB safe. One assignment
    ///   site total makes the recorded id path-independent.
    /// - the id names a STACK local (`local_idx_for_obj_id`) whose layout
    ///   size resolves concretely, OR (raw-alloc route) a `__rust_alloc`
    ///   stub allocation with a CONCRETE recorded size: the emitted bound is
    ///   the exact object extent, never an invented one. Other heap ids
    ///   (realloc, Vec/Box internals) KEEP the demotion.
    /// - the former blanket `-Z uninit-checks` refusal is removed — see
    ///   `stack_provenance_for_local` for why the scalar shadow-memory model
    ///   plus the type-punning fail-closed net make resolution sound there.
    pub(in crate::codegen_ay::chc) fn offset_bound_obj_id_for_operand(
        &self,
        op: &Operand,
    ) -> Option<u32> {
        if let Some(id) = self.known_obj_id_for_operand(op) {
            return Some(id);
        }
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        self.stack_provenance_for_local(place.local)
            .map(|(obj_id, _)| obj_id)
            // Raw-alloc route: heap-alloc lane, resolvable ONLY together with
            // a concrete recorded size — `ptr_offset_alloc_bound_check` then
            // emits the real `result_offset <= size` bound (never an invented
            // one; a size-less alloc keeps the demotion).
            .or_else(|| self.heap_alloc_provenance_for_local(place.local).map(|(obj_id, _)| obj_id))
    }

    /// Precise `(obj_id, allocation_size)` recovery for a pointer LOCAL whose
    /// value provably points into a stack allocation, via the fail-closed
    /// single-assignment use-def walk. Shared by the offset-site alloc-bound
    /// resolution and the deref-site strict-bound emission.
    ///
    /// Raw-alloc route: the `-Z uninit-checks` refusal that used to live here
    /// is REMOVED. It existed because the provenance demotion was the
    /// accidental net over the then-missing shadow-memory model for
    /// raw-pointer writes (alloc-to-slice precedent). The scalar shadow model
    /// (MEMUB-24/25/27, `codegen_call_kani_model_mem_init.rs`) now tracks
    /// those reads/writes, and the type-punning fail-closed net in
    /// `codegen_stmt_rvalue.rs` still demotes every punned-pointer shape the
    /// shadow model cannot follow — so resolving stack provenance here only
    /// swaps the demotion for the REAL `offset/deref within layout size`
    /// obligations (proof-strengthening, must-FAIL duals in
    /// `tests/expected/uninit/access-padding-uninit/`).
    pub(in crate::codegen_ay::chc) fn stack_provenance_for_local(
        &self,
        local: usize,
    ) -> Option<(u32, u32)> {
        let owner_local = self.single_assign_stack_owner_local(local)?;
        let Some(obj_id) = self.heap_state.local_addresses.get(&owner_local).map(|(id, _)| *id)
        else {
            debug!(local, owner_local, "offset stack lane: refused (owner has no stack address)");
            return None;
        };
        let Some(size) = self
            .body
            .locals()
            .get(owner_local)
            .and_then(|decl| self.get_type_size(decl.ty))
            .and_then(|size| u32::try_from(size).ok())
        else {
            debug!(local, obj_id, owner_local, "offset stack lane: refused (no layout size)");
            return None;
        };
        debug!(local, obj_id, owner_local, size, "offset stack lane: resolved stack provenance");
        Some((obj_id, size))
    }

    /// Raw-alloc route: precise `(obj_id, allocation_size)` recovery for a
    /// pointer LOCAL whose value provably points into a `__rust_alloc` /
    /// `__rust_alloc_zeroed` allocation, via the same fail-closed
    /// single-assignment walk as [`Self::stack_provenance_for_local`].
    ///
    /// Gates (each load-bearing):
    /// - the walk terminates at the alloc stub call's destination local,
    ///   which is SINGLE-ASSIGNMENT (walk precondition) — the recorded
    ///   `known_alloc_ids` entry names exactly that call site's object;
    /// - the stub recorded a CONCRETE allocation size
    ///   (`heap_state.heap_alloc_size`, seeded from the resolved Layout).
    ///   A symbolic-size allocation keeps the `OffsetProvenanceUnresolved`
    ///   demotion — the bound we would emit is the object's real extent or
    ///   nothing.
    pub(in crate::codegen_ay::chc) fn heap_alloc_provenance_for_local(
        &self,
        local: usize,
    ) -> Option<(u32, u32)> {
        let Some(OffsetProvenanceStep::HeapAlloc(owner)) =
            self.single_assign_provenance_terminal(local)
        else {
            return None;
        };
        let Some(obj_id) = self.known_alloc_ids.get(&owner).copied() else {
            debug!(local, owner, "offset heap-alloc lane: refused (no recorded obj id)");
            return None;
        };
        let Some(size) = self.heap_state.heap_alloc_size(obj_id) else {
            debug!(local, owner, obj_id, "offset heap-alloc lane: refused (no concrete size)");
            return None;
        };
        debug!(local, owner, obj_id, size, "offset heap-alloc lane: resolved alloc provenance");
        Some((obj_id, size))
    }

    /// Raw-alloc route: fully-folded alloc bound for an offset whose base
    /// pointer is ANCHORED — provably at a concrete byte delta from the start
    /// of a `__rust_alloc{_zeroed}` allocation with a concrete recorded size
    /// — and whose count is a 64-bit constant. Returns the numerically-folded
    /// bound (`true` folds away at emission; `false` becomes an unconditional
    /// error rule), or `None` to fall back to the symbolic lanes.
    pub(in crate::codegen_ay::chc) fn anchored_alloc_offset_bound_for_operand(
        &mut self,
        op: &Operand,
        count: &Expr,
        pointee_size: u64,
    ) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        let (_, size, base_delta) = self.alloc_anchored_provenance(place.local)?;
        let (value, 64) = const_bv_value(count)? else {
            return None;
        };
        // Signed (isize) interpretation, exactly as const_fold_offset_count_checks.
        let modulus = BigInt::from(1u8) << 64u32;
        let half = BigInt::from(1u8) << 63u32;
        let signed_count = if value >= half { value - modulus } else { value };
        let end = BigInt::from(base_delta) + signed_count * BigInt::from(pointee_size);
        // Pointer arithmetic: one-past-end inclusive.
        let in_bounds = end >= BigInt::from(0u8) && end <= BigInt::from(size);
        debug!(
            base_local = place.local,
            base_delta, size, in_bounds, "offset anchored raw-alloc lane: folded bound"
        );
        Some(Expr::bool_const(in_bounds))
    }

    /// Raw-alloc route: the ANCHORED provenance walk — like
    /// [`Self::heap_alloc_provenance_for_local`] but additionally tracking the
    /// EXACT byte delta of the walked pointer from the allocation start.
    /// Hops:
    /// - value-preserving copies / pointer casts (delta unchanged);
    /// - raw-pointer `add`/`sub`/`offset` calls (incl. the Kani offset model)
    ///   whose count resolves to a CONSTANT via the fail-closed unique-def
    ///   walk — delta accumulates `count * pointee_size` exactly (i128, no
    ///   wrap). `wrapping_*` variants are refused: their wrap semantics are
    ///   not representable as an exact delta.
    /// Terminal: the raw-alloc stub call destination (single-assignment; the
    /// recorded obj id and concrete size resolve, else refuse).
    ///
    /// Returns `(obj_id, alloc_size, base_byte_delta)`; a negative or
    /// non-u64 accumulated delta refuses (fail-closed).
    fn alloc_anchored_provenance(&mut self, start_local: usize) -> Option<(u32, u32, u64)> {
        use rustc_public::mir::{CastKind, Rvalue, StatementKind, TerminatorKind};
        let mut local = start_local;
        let mut delta: i128 = 0;
        let mut seen = HashSet::from([local]);
        'walk: for _ in 0..12 {
            if !self.encode.single_assign_locals.contains(&local) {
                return None;
            }
            let mut next: Option<usize> = None;
            for bb_idx in 0..self.body.blocks.len() {
                let bb = &self.body.blocks[bb_idx];
                for stmt in &bb.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != local || !lhs.projection.is_empty() {
                        continue;
                    }
                    let src = match rhs {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.projection.is_empty() =>
                        {
                            p.local
                        }
                        Rvalue::Cast(kind, Operand::Copy(p) | Operand::Move(p), _)
                            if p.projection.is_empty()
                                && matches!(
                                    kind,
                                    CastKind::PtrToPtr
                                        | CastKind::PointerCoercion(_)
                                        | CastKind::PointerExposeAddress
                                        | CastKind::PointerWithExposedProvenance
                                        | CastKind::Transmute
                                        | CastKind::Subtype
                                ) =>
                        {
                            p.local
                        }
                        _ => return None,
                    };
                    if !seen.insert(src) {
                        return None;
                    }
                    next = Some(src);
                    break;
                }
                if next.is_some() {
                    break;
                }
                let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind
                else {
                    continue;
                };
                if destination.local != local || !destination.projection.is_empty() {
                    continue;
                }
                // Terminal: the raw-alloc stub call itself (base offset 0).
                if let Some(stub) = self.detect_alloc_stub(func)
                    && matches!(
                        stub,
                        crate::codegen_ay::stubs::StubKind::RustAlloc
                            | crate::codegen_ay::stubs::StubKind::RustAllocZeroed
                    )
                {
                    let obj_id = self.known_alloc_ids.get(&local).copied()?;
                    let size = self.heap_state.heap_alloc_size(obj_id)?;
                    let base_delta = u64::try_from(delta).ok()?;
                    return Some((obj_id, size, base_delta));
                }
                // Constant-count pointer-arithmetic hop.
                let path = self.resolve_callee_path(func)?;
                let is_exact_arith = ((path.ends_with("::add")
                    || path.ends_with("::sub")
                    || path.ends_with("::offset"))
                    && (path.contains("const_ptr") || path.contains("mut_ptr")))
                    || path.contains("rustc_intrinsics::offset");
                if !is_exact_arith {
                    return None;
                }
                let recv = match args.first() {
                    Some(Operand::Copy(p) | Operand::Move(p)) if p.projection.is_empty() => p.local,
                    _ => return None,
                };
                let elem = args.first().and_then(|a| a.ty(self.body.locals()).ok()).and_then(
                    |ty| match ty.kind() {
                        TyKind::RigidTy(RigidTy::RawPtr(inner, _))
                        | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.get_type_size(inner),
                        _ => None,
                    },
                )?;
                let count_expr = {
                    let count_op = args.get(1)?.clone();
                    self.unique_def_const_operand(&count_op, 8)?
                };
                let (value, 64) = const_bv_value(&count_expr)? else {
                    return None;
                };
                let modulus = BigInt::from(1u8) << 64u32;
                let half = BigInt::from(1u8) << 63u32;
                let signed = if value >= half { value - modulus } else { value };
                let signed = if path.ends_with("::sub") { -signed } else { signed };
                let step: i128 = (signed * BigInt::from(elem)).try_into().ok()?;
                delta = delta.checked_add(step)?;
                if !seen.insert(recv) {
                    return None;
                }
                next = Some(recv);
                break;
            }
            match next {
                Some(n) => local = n,
                None => break 'walk,
            }
        }
        None
    }

    /// Strict deref-site bound for a walk-resolved stack or raw-alloc heap
    /// pointer: the access span `[offset, offset + access_size)` must lie
    /// inside the base allocation. Emitted ALONGSIDE `heap_access_checks`,
    /// which fail-opens ("unconstrained obj_id — skip bounds check") when the
    /// address's obj_id lane is an opaque SSA variable — the case this closes
    /// for offset-derived pointers (the deref half of the offset-deref
    /// keystone: the offset alloc-bound is INCLUSIVE of one-past-end, so
    /// `*arr.as_ptr().add(len)` / `*alloc_ptr.add(size)` is only caught
    /// here). Purely additive: pushing extra obligations can only turn proofs
    /// into failures, never the reverse.
    pub(in crate::codegen_ay::chc) fn provenance_deref_bound_checks(
        &self,
        addr: &Expr,
        pointee_ty: rustc_public::ty::Ty,
        ptr_local: usize,
    ) -> Vec<Expr> {
        let Some((_, alloc_size)) = self
            .stack_provenance_for_local(ptr_local)
            .or_else(|| self.heap_alloc_provenance_for_local(ptr_local))
        else {
            return Vec::new();
        };
        let Some(access_size) =
            self.get_type_size(pointee_ty).filter(|&s| s > 0).and_then(|s| u32::try_from(s).ok())
        else {
            return Vec::new();
        };
        let Some((_, offset)) = self.split_pointer(addr) else {
            return Vec::new();
        };
        let end = offset.clone().bvadd(Expr::bitvec_const(access_size as u128, 32));
        let no_wrap = end.clone().bvuge(offset);
        let in_bounds = end.bvule(Expr::bitvec_const(alloc_size as u128, 32));
        debug!(ptr_local, alloc_size, access_size, "CHC: provenance strict deref bound emitted");
        vec![no_wrap, in_bounds]
    }

    /// Fail-closed use-def walk from a pointer local to the STACK local that
    /// owns its allocation. Every link on the chain must be a
    /// SINGLE-ASSIGNMENT local (#3905 prescan): the walk then denotes the
    /// same object on every execution path, which is what makes the recovered
    /// (obj, size) safe to use for a proof-strengthening bound. Deliberately
    /// does NOT consult the flow-insensitive metadata side-tables
    /// (`known_alloc_ids` / `ref_targets` snapshots): those are
    /// last-processed-block-wins at merge points, which is exactly the
    /// wrong-object false-Safe factory this gate exists to exclude.
    ///
    /// The walk terminates ONLY at a direct `Ref`/`AddressOf` of a place with
    /// no `Deref` projection — the owning local itself. Pointers into heap
    /// storage (Vec/Box backing stores) necessarily pass through a `Deref`
    /// or an unrecognized call and are refused (heap stays demoted).
    fn single_assign_stack_owner_local(&self, start_local: usize) -> Option<usize> {
        match self.single_assign_provenance_terminal(start_local) {
            Some(OffsetProvenanceStep::Owner(owner)) => Some(owner),
            _ => None,
        }
    }

    /// The fail-closed walk core: follow single-assignment allocation-
    /// preserving hops until a TERMINAL step (`Owner` / `ConstRef`) or a
    /// refusal. Never returns `Through`.
    fn single_assign_provenance_terminal(
        &self,
        start_local: usize,
    ) -> Option<OffsetProvenanceStep> {
        let mut local = start_local;
        let mut seen = HashSet::from([local]);
        for _ in 0..12 {
            if !self.encode.single_assign_locals.contains(&local) {
                debug!(local, start_local, "offset stack lane: refused (not single-assignment)");
                return None;
            }
            match self.offset_walk_unique_def(local) {
                Some(OffsetProvenanceStep::Through(src)) => {
                    if !seen.insert(src) {
                        debug!(local, start_local, "offset stack lane: refused (cyclic chain)");
                        return None;
                    }
                    local = src;
                }
                Some(terminal) => return Some(terminal),
                None => {
                    debug!(local, start_local, "offset stack lane: refused (untraceable def)");
                    return None;
                }
            }
        }
        None
    }

    /// Part of #72: ALLOCATION-SIZE-only provenance for a pointer local —
    /// the extent of the object the pointer provably points into, through the
    /// same fail-closed single-assignment walk as
    /// [`Self::stack_provenance_for_local`], extended with the promoted-const
    /// `&T` terminal (stack locals AND promoted constants both place the
    /// allocation base at offset lane 0, so a walked pointer's offset lane is
    /// allocation-relative in both cases). Used by the `offset_from`
    /// same-allocation in-bounds check, where only the extent matters.
    pub(in crate::codegen_ay::chc) fn provenance_alloc_size_for_local(
        &self,
        local: usize,
    ) -> Option<u32> {
        if self.uninit_checks {
            debug!(local, "provenance alloc size: refused (uninit-checks active)");
            return None;
        }
        match self.single_assign_provenance_terminal(local)? {
            OffsetProvenanceStep::Owner(owner) => {
                // Same gates as stack_provenance_for_local: the owner must
                // have a materialized stack address and a concrete layout.
                if !self.heap_state.local_addresses.contains_key(&owner) {
                    debug!(local, owner, "provenance alloc size: refused (no stack address)");
                    return None;
                }
                self.body
                    .locals()
                    .get(owner)
                    .and_then(|decl| self.get_type_size(decl.ty))
                    .and_then(|size| u32::try_from(size).ok())
            }
            OffsetProvenanceStep::ConstRef(pointee) => {
                self.get_type_size(pointee).and_then(|size| u32::try_from(size).ok())
            }
            // Raw-alloc route: real extent of a `__rust_alloc` allocation —
            // same gates as `heap_alloc_provenance_for_local` (single-
            // assignment stub destination, concrete recorded size).
            OffsetProvenanceStep::HeapAlloc(owner) => self
                .known_alloc_ids
                .get(&owner)
                .copied()
                .and_then(|obj_id| self.heap_state.heap_alloc_size(obj_id)),
            OffsetProvenanceStep::Through(_) => None,
        }
    }

    /// The unique defining site of a single-assignment local, classified for
    /// the provenance walk. Returns `None` for any shape the walk does not
    /// positively understand (fail-closed).
    fn offset_walk_unique_def(&self, target: usize) -> Option<OffsetProvenanceStep> {
        use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != target || !lhs.projection.is_empty() {
                    continue;
                }
                return match rhs {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        Some(OffsetProvenanceStep::Through(src.local))
                    }
                    // Part of #72: promoted-const `&T` root (`let v = &[0; 10]`
                    // where the array is lifetime-promoted). The ref names the
                    // WHOLE promoted allocation, whose extent is the pointee
                    // layout size.
                    Rvalue::Use(Operand::Constant(const_op)) => match const_op.const_.ty().kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                            Some(OffsetProvenanceStep::ConstRef(pointee))
                        }
                        _ => None,
                    },
                    // Casts: ONLY bit-value-preserving pointer casts. A
                    // numeric cast (IntToInt et al.) can TRUNCATE the address
                    // — walking through one would claim (obj, size) for a
                    // value whose obj_id lane the cast destroyed, and at the
                    // demotion-suppressing offset site that is a false-Safe
                    // factory. (`Transmute` is same-size by construction, so
                    // it preserves the 64-bit pointer value.)
                    Rvalue::Cast(kind, Operand::Copy(src) | Operand::Move(src), _)
                        if src.projection.is_empty()
                            && matches!(
                                kind,
                                rustc_public::mir::CastKind::PtrToPtr
                                    | rustc_public::mir::CastKind::PointerCoercion(_)
                                    | rustc_public::mir::CastKind::PointerExposeAddress
                                    | rustc_public::mir::CastKind::PointerWithExposedProvenance
                                    | rustc_public::mir::CastKind::Transmute
                                    | rustc_public::mir::CastKind::Subtype
                            ) =>
                    {
                        Some(OffsetProvenanceStep::Through(src.local))
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        let mut projs = place.projection.iter();
                        let leading_deref = matches!(
                            place.projection.first(),
                            Some(rustc_public::mir::ProjectionElem::Deref)
                        );
                        if leading_deref {
                            projs.next();
                        }
                        if projs.any(|p| matches!(p, rustc_public::mir::ProjectionElem::Deref)) {
                            // A deref DEEPER in the chain reads a pointer out
                            // of memory — not traceable syntactically.
                            None
                        } else if leading_deref {
                            // Reborrow `&(*p)[i]` / `&(*p).f`: points into the
                            // SAME allocation as `p` — continue the walk
                            // through the base pointer local.
                            Some(OffsetProvenanceStep::Through(place.local))
                        } else {
                            Some(OffsetProvenanceStep::Owner(place.local))
                        }
                    }
                    _ => None,
                };
            }
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            if destination.local != target || !destination.projection.is_empty() {
                continue;
            }
            // Raw-alloc route: terminate at a raw allocator stub call. The
            // stub registers a fresh heap object at offset 0 for this
            // destination; `heap_alloc_provenance_for_local` recovers its
            // (obj_id, concrete size) — fail-closed when either is missing.
            if let Some(stub) = self.detect_alloc_stub(func)
                && matches!(
                    stub,
                    crate::codegen_ay::stubs::StubKind::RustAlloc
                        | crate::codegen_ay::stubs::StubKind::RustAllocZeroed
                )
            {
                return Some(OffsetProvenanceStep::HeapAlloc(target));
            }
            let path = self.resolve_callee_path(func)?;
            if !Self::offset_walk_identity_callee(&path) {
                debug!(target, %path, "offset stack lane: refused (non-identity callee)");
                return None;
            }
            return args.first().and_then(|arg| match arg {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                    Some(OffsetProvenanceStep::Through(p.local))
                }
                _ => None,
            });
        }
        None
    }

    /// Calls whose destination provably shares the first argument's
    /// allocation: slice/array `as_ptr`/`as_mut_ptr` (ref -> thin pointer
    /// identity) and raw-pointer offset arithmetic (`add`/`sub`/`offset`,
    /// including the Kani offset model), which shifts the in-object offset
    /// but never the allocation.
    ///
    /// Part of #72: the `wrapping_*` family is included — wrapping pointer
    /// arithmetic RETAINS the original allocation's provenance by definition
    /// (only dereference/`offset_from` of an out-of-bounds result is UB), and
    /// the split-pointer stub model likewise preserves the obj-id lane. Every
    /// consumer of this walk emits proof-STRENGTHENING obligations against the
    /// recovered object, so resolving through a wrapping step can only surface
    /// checks (e.g. the offset-wraps-around `offset_from` in-bounds check),
    /// never suppress one.
    pub(in crate::codegen_ay::chc) fn offset_walk_identity_callee(path: &str) -> bool {
        ((path.ends_with("::as_ptr") || path.ends_with("::as_mut_ptr")) && path.contains("slice"))
            || ((path.ends_with("::add")
                || path.ends_with("::sub")
                || path.ends_with("::offset")
                || path.ends_with("::wrapping_add")
                || path.ends_with("::wrapping_sub")
                || path.ends_with("::wrapping_offset")
                || path.ends_with("::wrapping_byte_add")
                || path.ends_with("::wrapping_byte_sub")
                || path.ends_with("::wrapping_byte_offset"))
                && (path.contains("const_ptr") || path.contains("mut_ptr")))
            || path.contains("rustc_intrinsics::offset")
            // Raw-alloc route: `slice::from_raw_parts{,_mut}` /
            // `ptr::slice_from_raw_parts{,_mut}` — the returned fat pointer's
            // DATA lane is exactly arg0, so the hop preserves the allocation
            // (the claimed length is metadata, irrelevant to the walk). Lets
            // slice-element derefs over alloc/stack-derived buffers resolve
            // the real allocation extent.
            || (path.contains("from_raw_parts")
                && (path.contains("slice") || path.contains("ptr")))
    }

    /// Whether `obj_id` names a promoted-constant allocation (str/byte-string
    /// literals collected by Pass 4 / decl-time slice metadata).
    pub(in crate::codegen_ay::chc) fn is_promoted_const_obj_id(&self, obj_id: u32) -> bool {
        self.ref_resolution.const_ref_promoted_obj_ids.values().any(|&v| v == obj_id)
            || self
                .ref_resolution
                .const_ref_memory_inits
                .iter()
                .any(|(_, _, _, promoted_obj_id, _)| *promoted_obj_id == obj_id)
    }

    pub(in crate::codegen_ay::chc) fn ptr_offset_alloc_bound_check(
        &mut self,
        base_ptr: &Expr,
        result_ptr: &Expr,
        known_obj_id: Option<u32>,
    ) -> Option<Expr> {
        if self.int_lift {
            return None;
        }
        let (obj_id, _) = self.split_pointer(base_ptr)?;
        // The obj_id lane of an identity-modeled pointer (e.g. str/slice
        // `as_ptr`) is an SSA state VARIABLE — semantically equal to the
        // receiver's `concat(obj_id, 0)` via the transition constraint, but
        // syntactically opaque to `const_obj_id_u32`. `known_obj_id` is the
        // metadata side-channel (`known_alloc_ids`/promoted-const tracking,
        // maintained by the same identity routes) resolving that case.
        let Some(const_obj_id) = Self::const_obj_id_u32(&obj_id).or(known_obj_id) else {
            // Fail-open provenance: the base pointer's obj_id lane is symbolic
            // (e.g. from `from_raw_parts`, whose stdlib MIR is unavailable), so
            // we cannot resolve the allocation to bound the offset. Record the
            // skipped safety check so the harness is demoted — a Safe verdict
            // must never rest on an offset bound we never checked — AND plumb the
            // base pointer's freed identity (Task #78) so a count-overflow
            // counterexample independent of the symbolic obj_id can recertify.
            self.record_offset_provenance_unresolved(base_ptr);
            return None;
        };
        let Some((_, result_offset)) = self.split_pointer(result_ptr) else {
            // Provenance resolved but the RESULT pointer's lanes cannot be
            // split — the bound check cannot be emitted. Same fail-closed
            // discipline as the symbolic-provenance case (a silent `?` here
            // would skip the check with no demotion).
            self.record_offset_provenance_unresolved(base_ptr);
            return None;
        };

        // Constant fast-path: fully-concrete steps fold to a literal bool so
        // statically-discharged harnesses don't grow live error rules
        // (trivially-true conditions are skipped at emission time).
        let concrete_size = self
            .heap_state
            .local_idx_for_obj_id(const_obj_id)
            .and_then(|local_idx| self.body.locals().get(local_idx))
            .and_then(|local_decl| self.get_type_size(local_decl.ty))
            .and_then(|size| u32::try_from(size).ok())
            .or_else(|| self.heap_state.heap_alloc_size(const_obj_id))
            .or_else(|| self.promoted_const_byte_size(const_obj_id));
        if let Some(size) = concrete_size {
            if let Some((offset_value, 32)) = const_bv_value(&result_offset) {
                let in_bounds = size == 0 || offset_value <= BigInt::from(size);
                return Some(Expr::bool_const(in_bounds));
            }
            // Known size, symbolic offset lane (identity-modeled base pointers
            // are SSA state vars, so the lane doesn't const-fold even when the
            // step is constant): emit the bound against the CONSTANT size —
            // linear BV the solver discharges easily, no metadata array pulled
            // into the query.
            if size == 0 {
                return Some(Expr::bool_const(true));
            }
            return Some(result_offset.bvule(Expr::bitvec_const(size as u128, 32)));
        }

        // Use the CONSTANT obj_id for the size lookup: in the syntactic-fold
        // case it equals the lane trivially; in the known_obj_id case it equals
        // the lane by the identity-route transition constraint — and a constant
        // select index keeps the obligation solvable.
        let obj_id_const = Expr::bitvec_const(const_obj_id as i128, 32);
        let Some(alloc_size) = self.alloc_size_expr_for_const_obj_id(const_obj_id, &obj_id_const)
        else {
            // Defensive: obj_id resolved but the allocation size could not be
            // resolved. Same fail-closed discipline as the symbolic-provenance case.
            self.record_offset_provenance_unresolved(base_ptr);
            return None;
        };
        // Zero-size exemption mirrors heap_access_checks: dyn-trait and other
        // vtable-resolved allocations record obj_size = 0.
        let is_zero_size = alloc_size.clone().eq(Expr::bitvec_const(0u64, 32));
        Some(Expr::or(is_zero_size, result_offset.bvule(alloc_size)))
    }

    /// Task #78: record a skipped pointer-offset alloc-bound check AND the
    /// SMT-var identity of the freed (symbolic-provenance) base pointer.
    ///
    /// When `ptr_offset_alloc_bound_check` cannot resolve the base pointer's
    /// allocation it skips the alloc-bound obligation and increments
    /// `offset_provenance_unresolved` (a DEMOTED category — a Safe verdict must
    /// never rest on a skipped bound). This helper ALSO plumbs the identity of
    /// the base pointer's `obj_id`-carrying value into the VC artifact so the
    /// driver's Task #78 dependence check can certify an offset counterexample
    /// Genuine iff its violated `error_p{N}` is data-independent of that value.
    ///
    /// It taints every `Var` in the ACTUAL `base_ptr` Expr (not the base local's
    /// state var): the provenance / wrap / same-object checks are all built from
    /// `base_ptr`, so they read a tainted var (`approximation_dependent =
    /// Some(true)` → stay demoted); the count / mul-overflow checks read only the
    /// offset operand, no tainted var (`Some(false)` → certifiable). Records
    /// EXACTLY one accounted approximation per skip (the completeness checksum),
    /// mirroring the `write_bytes` precedent (`misc_intrinsics_write_bytes.rs`):
    /// `record_approximation_identity` bumps `accounted_approximations` once with
    /// the first var (or `None` if the base pointer has no vars — dead/accounted),
    /// and `note_additional_freed_var` records the rest WITHOUT re-accounting.
    /// Coarse whole-`base_ptr` tainting is a sound over-approximation: it can only
    /// LOSE conversions, never mislabel a spurious counterexample Genuine.
    pub(in crate::codegen_ay::chc) fn record_offset_provenance_unresolved(
        &mut self,
        base_ptr: &Expr,
    ) {
        self.diagnostics.offset_provenance_unresolved.inc();
        let mut it = Self::offset_provenance_freed_vars(base_ptr).into_iter();
        match it.next() {
            Some(first) => {
                self.vc.record_approximation_identity(Some(&first));
                for rest in it {
                    self.vc.note_additional_freed_var(&rest);
                }
            }
            None => self.vc.record_approximation_identity(None),
        }
    }

    fn offset_provenance_freed_vars(base_ptr: &Expr) -> Vec<String> {
        let mut vars: Vec<String> = Vec::new();
        let mut stack = vec![base_ptr];
        while let Some(node) = stack.pop() {
            if let ExprValue::Var { name } = node.value()
                && !vars.contains(name)
            {
                vars.push(name.clone());
            }
            stack.extend(node.children());
        }
        vars
    }
}

#[cfg(test)]
mod tests {
    use ay_bindings::{Expr, Sort};

    use super::ChcCtx;
    use crate::codegen_ay::provenance::Val;

    #[test]
    fn const_count_checks_fold_small_positive_count() {
        let count = Expr::bitvec_const(10u128, 64);
        assert_eq!(
            ChcCtx::const_fold_offset_count_checks(&Val::of_value(count), true, 4),
            Some((true, true))
        );
    }

    #[test]
    fn const_count_checks_detect_byte_offset_mul_overflow() {
        // 2^62 elements of size 4 wrap the signed 64-bit byte offset.
        let count = Expr::bitvec_const(1u128 << 62, 64);
        assert_eq!(
            ChcCtx::const_fold_offset_count_checks(&Val::of_value(count), true, 4),
            Some((true, false))
        );
    }

    #[test]
    fn const_count_checks_unsigned_count_exceeding_isize_max() {
        let count = Expr::bitvec_const(1u128 << 63, 64);
        assert_eq!(
            ChcCtx::const_fold_offset_count_checks(&Val::of_value(count), false, 1),
            Some((false, true))
        );
    }

    #[test]
    fn const_count_checks_negative_count_folds_exactly() {
        // -1 (two's complement) with size 4: product -4, div-back -1 == count.
        let count = Expr::bitvec_const(u64::MAX as u128, 64);
        assert_eq!(
            ChcCtx::const_fold_offset_count_checks(&Val::of_value(count), true, 4),
            Some((true, true))
        );
    }

    #[test]
    fn const_count_checks_symbolic_count_does_not_fold() {
        let count = Expr::var("sym_count", Sort::bitvec(64));
        assert_eq!(ChcCtx::const_fold_offset_count_checks(&Val::of_value(count), true, 4), None);
    }

    #[test]
    fn offset_provenance_freed_vars_collects_and_deduplicates_nested_inputs() {
        let obj_id = Expr::var("obj_id", Sort::bitvec(64));
        let addr = Expr::var("addr", Sort::bitvec(64));
        let base = obj_id.clone().bvadd(addr).bvadd(obj_id);

        let mut vars = ChcCtx::offset_provenance_freed_vars(&base);
        vars.sort();
        assert_eq!(vars, vec!["addr", "obj_id"]);
        assert!(ChcCtx::offset_provenance_freed_vars(&Expr::bitvec_const(0u128, 64)).is_empty());
    }
}
