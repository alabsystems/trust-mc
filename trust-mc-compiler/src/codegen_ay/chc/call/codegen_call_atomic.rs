// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Atomic intrinsic dispatch for CHC codegen: detection, load, store, new.
//! RMW/cxchg in `codegen_call_atomic_rmw`, from_ptr in `codegen_call_atomic_from_ptr`.
//! Part of #3435, #3452, #3598.

use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};
use trust_mc_codegen_types::types::unwrap_single_field_datatype;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_atomic_from_ptr::codegen_atomic_from_ptr;
use super::codegen_call_atomic_mem::{
    atomic_load_from_memory, atomic_receiver_mem_target, drain_atomic_pending_checks,
    emit_atomic_mem_store_transition,
};
use super::codegen_call_atomic_rmw::{
    codegen_atomic_compare_exchange, codegen_atomic_cxchg, codegen_atomic_rmw,
};
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_misc::Referent;
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::provenance::{MaybeLoc, Val};
use crate::codegen_ay::ptr_repr::PtrSlot;

// ---------------------------------------------------------------------------
// Atomic kind detection
// ---------------------------------------------------------------------------

/// Classification of atomic intrinsic operations.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) enum AtomicKind {
    Load,
    Store,
    Exchange,
    Cxchg,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
    FetchNand,
    FetchMax,
    FetchMin,
    FetchUmax,
    FetchUmin,
    Fence,
    /// Stable API constructor: `AtomicBool::new(val)`, `AtomicIsize::new(val)`, etc.
    /// Stores the initial value into the destination local. Part of #3452.
    New,
    /// Stable API `compare_exchange`/`compare_exchange_weak`. Returns `Result<T, T>`
    /// (flattened as `(is_ok: Bool, payload: T)`) instead of raw cxchg's `(T, bool)`.
    /// Part of #3452.
    CompareExchange,
    /// Stable API `AtomicUsize::from_ptr(ptr)` — transparent alias boundary.
    /// Creates a `&AtomicT` reference from a raw pointer. Semantically equivalent
    /// to `unsafe { &*ptr.cast() }`. Part of #3598.
    FromPtr,
    /// Stable API `get_mut(&mut self)` — exclusive access identity.
    /// Returns `&mut T` from `&mut Atomic<T>`. Since Atomic<T> is transparent,
    /// this is identity in single-threaded verification. Part of #4067.
    GetMut,
}

/// Strip trailing generic arguments from a def-path string.
///
/// Const-generic unstable atomics produce paths like:
///   `core::intrinsics::atomic_xadd::<u8, u8, AtomicOrdering::SeqCst>`
/// Naive `rsplit("::")` on that returns `"SeqCst>"` instead of `"atomic_xadd"`.
/// This strips everything from the first `::<` onward. Part of #3741.
pub(in crate::codegen_ay::chc) fn strip_generic_args(path: &str) -> &str {
    path.find("::<").map_or(path, |idx| &path[..idx])
}

/// Detect atomic intrinsic from callee path.
///
/// Matches raw intrinsic names and stable `std::sync::atomic` method names.
/// Part of #3452, #3741, #3776.
pub(in crate::codegen_ay::chc) fn detect_atomic_intrinsic(path: &str) -> Option<AtomicKind> {
    if !path.contains("atomic") {
        return None;
    }

    // --- Stable API (sync::atomic) — checked BEFORE strip_generic_args ---
    // Part of #3776: stable paths have generics on the TYPE (`AtomicPtr::<i32>`),
    // not the method. strip_generic_args strips from the first `::<`, losing the
    // method name. rsplit("::") on the original path correctly yields it.
    if path.contains("sync::atomic") {
        let m = path.rsplit("::").next()?;
        return match m {
            "load" => Some(AtomicKind::Load),
            "store" => Some(AtomicKind::Store),
            "swap" => Some(AtomicKind::Exchange),
            "fetch_add" | "fetch_byte_add" => Some(AtomicKind::FetchAdd),
            "fetch_sub" | "fetch_byte_sub" => Some(AtomicKind::FetchSub),
            "fetch_and" => Some(AtomicKind::FetchAnd),
            "fetch_or" => Some(AtomicKind::FetchOr),
            "fetch_xor" => Some(AtomicKind::FetchXor),
            "fetch_nand" => Some(AtomicKind::FetchNand),
            "fetch_max" => Some(AtomicKind::FetchMax),
            "fetch_min" => Some(AtomicKind::FetchMin),
            "fence" => Some(AtomicKind::Fence),
            // Stable API constructor: AtomicBool::new(val), AtomicIsize::new(val), etc.
            // Part of #3452: stores initial value into destination local.
            "new" => Some(AtomicKind::New),
            // Stable compare_exchange returns Result<T, T> (flattened as (is_ok, payload)).
            // Part of #3452: separate from raw cxchg which returns (T, bool).
            "compare_exchange" | "compare_exchange_weak" => Some(AtomicKind::CompareExchange),
            // Part of #3598: from_ptr creates &AtomicT from *mut T (transparent alias).
            "from_ptr" => Some(AtomicKind::FromPtr),
            // Part of #4067: get_mut(&mut self) returns exclusive &mut to inner value.
            // Since Atomic<T> is transparent, this is identity (self passthrough).
            "get_mut" => Some(AtomicKind::GetMut),
            _ => None,
        };
    }

    // --- Raw intrinsic names — strip_generic_args safe here (#3741) ---
    let base = strip_generic_args(path);
    let m = base.rsplit("::").next()?;

    // Unsigned prefixes checked before signed (e.g., atomic_umax before atomic_max).
    if m.starts_with("atomic_load") {
        return Some(AtomicKind::Load);
    } else if m.starts_with("atomic_store") {
        return Some(AtomicKind::Store);
    } else if m.starts_with("atomic_xchg") {
        return Some(AtomicKind::Exchange);
    } else if m.starts_with("atomic_cxchg") {
        return Some(AtomicKind::Cxchg);
    } else if m.starts_with("atomic_xadd") || m.starts_with("atomic_uadd") {
        return Some(AtomicKind::FetchAdd);
    } else if m.starts_with("atomic_xsub") || m.starts_with("atomic_usub") {
        return Some(AtomicKind::FetchSub);
    } else if m.starts_with("atomic_and") {
        return Some(AtomicKind::FetchAnd);
    } else if m.starts_with("atomic_or") {
        return Some(AtomicKind::FetchOr);
    } else if m.starts_with("atomic_xor") {
        return Some(AtomicKind::FetchXor);
    } else if m.starts_with("atomic_nand") {
        return Some(AtomicKind::FetchNand);
    } else if m.starts_with("atomic_umax") {
        return Some(AtomicKind::FetchUmax);
    } else if m.starts_with("atomic_umin") {
        return Some(AtomicKind::FetchUmin);
    } else if m.starts_with("atomic_max") {
        return Some(AtomicKind::FetchMax);
    } else if m.starts_with("atomic_min") {
        return Some(AtomicKind::FetchMin);
    } else if m.starts_with("atomic_fence") || m.starts_with("atomic_singlethreadfence") {
        return Some(AtomicKind::Fence);
    }

    None
}

/// Re-exports from shared raw-pointer receiver module (#3697, #3761).
pub(in crate::codegen_ay::chc) use super::ptr_receiver_mem::{
    mark_atomic_ptr_forwarded, resolve_ptr_target_local,
};

// Dispatch entry point

/// Extension trait for atomic intrinsic dispatch in CHC call terminators.
pub(in crate::codegen_ay::chc) trait CallDispatchAtomic {
    fn try_dispatch_call_atomic(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchAtomic for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_atomic(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        // Part of #3741: try resolve_callee_path first, then fall back to
        // FnDef def_id name for const-generic unstable intrinsics where
        // resolve_callee_path may return None.
        let callee_path = dcx
            .callee_path
            .clone()
            .or_else(|| self.resolve_callee_path(dcx.func))
            .or_else(|| self.resolve_fn_def_name(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(kind) = detect_atomic_intrinsic(path) else { return false };

        // Fences: no-op in sequential verification — no memory effect, no return value.
        if matches!(kind, AtomicKind::Fence) {
            debug!("CHC atomic_fence (no-op) bb{}", dcx.bb_idx);
            if let Some(target) = dcx.target {
                let out = self.build_output_args(dcx.modified_locals, &[]);
                self.emit_goto_rule(dcx.from_app, *target, &out, dcx.stmt_constraints);
            }
            return true;
        }

        let Some(target) = dcx.target else { return true };
        match kind {
            AtomicKind::Load => codegen_atomic_load(self, dcx, *target),
            AtomicKind::Store => codegen_atomic_store(self, dcx, *target),
            AtomicKind::Cxchg => codegen_atomic_cxchg(self, dcx, *target),
            AtomicKind::CompareExchange => codegen_atomic_compare_exchange(self, dcx, *target),
            AtomicKind::New => codegen_atomic_new(self, dcx, *target),
            AtomicKind::FromPtr => codegen_atomic_from_ptr(self, dcx, *target),
            AtomicKind::Fence => return true, // #3124: graceful no-op (handled above)
            AtomicKind::GetMut => codegen_atomic_get_mut(self, dcx, *target),
            kind => codegen_atomic_rmw(self, dcx, *target, kind),
        }
        true
    }
}

// ---------------------------------------------------------------------------
// Non-RMW handlers: load, store, cxchg
// ---------------------------------------------------------------------------

/// Extract local index from a plain operand for obj_valid checks (#3636).
fn extract_atomic_ptr_local(arg: &Operand) -> Option<usize> {
    match arg {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The referent DATUM an atomic load may bind directly, when one is
/// ESTABLISHED — never when it merely looks like one.
///
/// Two independent establishing facts, and no guess:
///
/// * [`Referent::Value`] — the resolver reports that a tier dereferenced, so
///   the term IS the referent's datum. This is the fact §4 item 1 was missing.
/// * [`Referent::Unreported`] whose SORT has no pointer slot at all
///   ([`PtrSlot::of_sort`] answers `None`): the memory model addresses storage
///   by a pointer-slot bitvector and nothing else, so a term of any other sort
///   cannot be an address in it and can only be the datum. That is a
///   representation fact about a DECLARED sort — nothing widens a sort — and it
///   is what the retired `bitvec_width() != Some(64)` disjunct was reaching
///   for. A `Thin` or `Wide` unreported term is exactly the ambiguous case and
///   gets `None`: it goes to the Mem-load lane, or to the sound fallback.
fn atomic_referent_datum(referent: &Referent) -> Option<Val> {
    match referent {
        Referent::Value(val) => Some(val.clone()),
        Referent::Unreported(expr) => {
            PtrSlot::of_sort(expr.sort()).is_none().then(|| Val::of_value(expr.clone()))
        }
    }
}

/// Emit the sound fallback for atomic call terminators after flushing any
/// deferred pointer-safety checks queued on the shared memory path.
fn emit_atomic_sound_fallback_goto(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_locals: &[usize],
) {
    drain_atomic_pending_checks(ctx, dcx, target);
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        dest_locals,
        dcx.stmt_constraints,
    );
}

/// `atomic_load(ptr)` → `dest = *ptr`. Tries ref_target resolution first,
/// falls back to Mem-level load for CSE'd UnsafeCell::get paths (#3452).
fn codegen_atomic_load(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.is_empty() {
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
        return;
    }

    // #3636: atomic_load must check obj_valid like a normal dereference.
    // Same gap as volatile_load — loading through a freed/stale pointer is unsound.
    if let Some(ptr_local) = extract_atomic_ptr_local(&dcx.args[0]) {
        ctx.emit_ptr_obj_valid_check(ptr_local, dcx.modified_locals);
    }

    // Part of #3710: check ref_target first to distinguish stack-local
    // pointers (value resolution) from heap-backed pointers (address only).
    let has_ref_target = resolve_ptr_target_local(ctx, &dcx.args[0]).is_some();
    // Part of #3761: register raw pointer as call-forwarded for consistent deref.
    if has_ref_target {
        mark_atomic_ptr_forwarded(ctx, &dcx.args[0]);
    }

    // Resolve what the pointer points to, and keep WHICH TIER answered.
    // Tiers 1-4.5 dereference and hand back the referent's datum
    // ([`Referent::Value`]); tiers 5-6 hand back the operand's own term, which
    // for a reference operand is the pointer ([`Referent::Unreported`]).
    let resolved = ctx.resolve_ref_or_const_referent_tagged(&dcx.args[0], dcx.modified_locals);

    // Determine the pointee type for Mem-level fallback.
    let pointee_ty = dcx.args[0].ty(ctx.body.locals()).ok().and_then(|ty| match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    });

    // Choose between the resolved referent datum and a Mem-level load.
    //
    // §4 item 1 (`docs/addr-vs-value-conversion-queue.md`) RESOLVED, and the
    // fix is not the one that item asked for. The comment that stood here said
    // the partition "cannot be resolved" because an `AtomicUsize` holds either
    // a pointer bit-pattern or an integer depending on run-time history, and
    // proposed an `AtomicCell` tag written by the last store. That information
    // does not exist and would not have helped: `store_forward_map` records the
    // store's DECLARED type key, which is `usize` under either reading.
    //
    // The question the partition actually asks is not "what does the atomic
    // hold?" but "did the resolver dereference, or hand back the pointer?" —
    // and that is a compile-time fact about which of six tiers answered, known
    // at the producer and previously discarded. `Referent` carries it, so the
    // `bitvec_width() == Some(64)` guess is DELETED rather than narrowed:
    //
    // * `Value` — a tier that resolved THROUGH the reference (or a by-value
    //   operand whose MIR type is not an address). It is the referent's datum,
    //   whatever its width, so an `AtomicUsize` datum no longer loses to its own
    //   width. Part of #3452's relaxed sort check is subsumed: `AtomicBool`
    //   resolves to BV8 against a Bool destination and
    //   `make_coerced_eq_constraint` handles the BV<->Bool crossing.
    // * `Unreported` — tier 5/6 handed back the operand's own term. For a
    //   reference operand that is the POINTER (the #3710 hazard), so this lane
    //   loads THROUGH it, and the address stays `MaybeLoc::Unknown` because
    //   `translate_operand_with_modified` still reports nothing about it.
    //
    // See `atomic_referent_datum` for the one case where an `Unreported` term
    // is still bound directly, and why that is a representation fact rather
    // than the width guess it replaces.
    //
    // `has_ref_target` is no longer consulted for the partition. It was a proxy
    // for "did a dereferencing tier run", asked of a different function
    // (`resolve_ptr_target_local`) that can disagree with the tier that actually
    // answered; the tag is the fact it was approximating. It still gates the
    // #3761 call-forwarding registration above, which is a different question.
    let loaded: Val = if let Some(ref referent) = resolved
        && ctx.resolve_destination(dest_local).is_some()
        && let Some(datum) = atomic_referent_datum(referent)
    {
        debug!(dest_local, "atomic_load: referent datum established");
        datum
    } else if let Some(Referent::Unreported(ref addr)) = resolved
        && matches!(PtrSlot::of_sort(addr.sort()), Some(PtrSlot::Thin))
        && let Some(pty) = pointee_ty
    {
        // Unreported term in a shape the memory model can be addressed by —
        // Mem-level load with repr(transparent) aliasing (#3452, #3710).
        // `PtrSlot::Thin` is a REPRESENTATION test (does this sort fit the
        // memory model's address slot?), not evidence of addresshood; the
        // provenance is `Unknown` and says so.
        let mem_val = atomic_load_from_memory(ctx, &MaybeLoc::Unknown(addr.clone()), pty);
        if let Some(mem_val) = mem_val {
            debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_load: Mem-level load");
            mem_val
        } else {
            debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_load: Mem load failed");
            emit_atomic_sound_fallback_goto(ctx, dcx, target, &[dest_local]);
            return;
        }
    } else if resolved.is_none()
        && let Some(pty) = pointee_ty
        && let Some((addr, _)) = atomic_receiver_mem_target(ctx, &dcx.args[0], dcx.modified_locals)
    {
        // Part of #3710: standalone Mem-level fallback for heap-backed atomics.
        // When resolve_ref_or_const_referent returns None (no ref_target or
        // const_ref_values for this local — e.g., from_ptr on a Box pointer),
        // resolve the pointer address directly and load from the memory model.
        let mem_val = atomic_load_from_memory(ctx, &addr, pty);
        if let Some(mem_val) = mem_val {
            debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_load: Mem-level load (standalone)");
            mem_val
        } else {
            debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_load: standalone Mem load failed");
            emit_atomic_sound_fallback_goto(ctx, dcx, target, &[dest_local]);
            return;
        }
    } else {
        warn!(
            dest_local,
            bb_idx = dcx.bb_idx,
            resolved_is_some = resolved.is_some(),
            pointee_ty_is_some = pointee_ty.is_some(),
            "atomic_load: no path to resolve value"
        );
        emit_atomic_sound_fallback_goto(ctx, dcx, target, &[dest_local]);
        return;
    };

    // Unwrap repr(transparent) datatype wrappers before coercion (Part of #3452).
    // AtomicBool resolves to Datatype(AtomicBool, [fld_v: BV8]) via ref_target.
    // The destination sort is Bool. Without unwrapping, coercion sees
    // Datatype→Bool which is unsupported. Unwrapping yields BV8, then
    // BV8→Bool coercion (BV8 != 0) succeeds via make_coerced_eq_constraint.
    let loaded = loaded.into_expr();
    let loaded = unwrap_single_field_datatype(&loaded).unwrap_or(loaded);

    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let s = dest_var.sort().clone();
        let eq = ctx.make_coerced_eq_constraint(&dest_var, loaded, &s, dest_local, "atomic_load");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        drain_atomic_pending_checks(ctx, dcx, target);
        if let Some(eq) = eq {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
        } else {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        }
    } else {
        emit_atomic_sound_fallback_goto(ctx, dcx, target, &[dest_local]);
    }
}

/// `atomic_store(ptr, val)` → `*ptr = val`
fn codegen_atomic_store(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 2 {
        // Part of #3721: atomic_store drops the memory write on fallback,
        // so this is an under-approximation, not a sound over-approximation.
        ctx.record_fallback();
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    let Some(new_value) = ctx.translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
    else {
        // Part of #3721: write-dropping fallback.
        ctx.record_fallback();
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    };

    let ref_local = resolve_ptr_target_local(ctx, &dcx.args[0]);
    // Part of #3761: register raw pointer as call-forwarded for consistent deref.
    if ref_local.is_some() {
        mark_atomic_ptr_forwarded(ctx, &dcx.args[0]);
    }
    if let Some(referent_local) = ref_local {
        debug!(
            "CHC atomic_store: referent_local={} (bb{}->bb{})",
            referent_local, dcx.bb_idx, target
        );

        let mut extra = Vec::new();
        if let Some((_, rv)) = ctx.resolve_destination(referent_local) {
            let s = rv.sort().clone();
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &rv,
                new_value.clone(),
                &s,
                referent_local,
                "atomic_store",
            ) {
                extra.push(eq);
            }
        }

        // Part of #3710: if ref_target resolved but produced no constraint
        // (e.g., sort mismatch between pointer variable and value), fall
        // through to Mem-level instead of emitting an unconstrained rule.
        if !extra.is_empty() {
            let out = ctx.build_output_args(dcx.modified_locals, &[dest_local, referent_local]);
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, extra);
            return;
        }
        debug!(
            referent_local,
            bb_idx = dcx.bb_idx,
            "atomic_store: ref_target produced no constraint, falling through to Mem-level"
        );
    }

    let mem_tgt = atomic_receiver_mem_target(ctx, &dcx.args[0], dcx.modified_locals);
    if let Some((addr, pointee_ty)) = mem_tgt
        // The stored datum is the call's second operand: `atomic_store(ptr, val)`.
        && emit_atomic_mem_store_transition(
            ctx,
            dcx,
            target,
            Val::of_value(new_value),
            addr,
            pointee_ty,
        )
    {
        debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_store: Mem-level store");
        return;
    }

    // Part of #3721: atomic_store final fallback drops the memory write.
    ctx.record_fallback();
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
}

/// `AtomicBool::new(val)` / `AtomicIsize::new(val)` / etc. → `dest = val`
///
/// Stable API constructor: creates atomic with initial value. Coerces between
/// wrapper sort (e.g., BV8 for AtomicBool) and value sort (e.g., Bool).
/// Part of #3452.
fn codegen_atomic_new(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    if dcx.args.is_empty() {
        // No-arg new() — shouldn't happen but handle gracefully.
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
        return;
    }

    // Translate the initial value from args[0].
    let init_value = ctx.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals);

    let Some(init_value) = init_value else {
        debug!(dest_local, bb_idx = dcx.bb_idx, "atomic_new: could not translate init value");
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
        return;
    };

    debug!(
        dest_local,
        bb_idx = dcx.bb_idx,
        init_sort = ?init_value.sort(),
        "atomic_new: constraining dest = init value"
    );

    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        // For repr(transparent) datatype wrappers (AtomicBool, AtomicIsize, etc.),
        // the dest sort is Datatype(Atomic*, [fld_v: inner_sort]) but init_value
        // has the inner value sort (Bool for AtomicBool::new(true)). Constrain
        // the inner field directly so coercion (Bool→BV8 etc.) can succeed.
        let (coerce_target, coerce_sort) =
            if let Some(inner) = unwrap_single_field_datatype(&dest_var) {
                let s = inner.sort().clone();
                (inner, s)
            } else {
                let s = dest_var.sort().clone();
                (dest_var, s)
            };
        let eq = ctx.make_coerced_eq_constraint(
            &coerce_target,
            init_value,
            &coerce_sort,
            dest_local,
            "atomic_new",
        );
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        if let Some(eq) = eq {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
        } else {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        }
    } else {
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
    }
}

/// `Atomic*::get_mut(&mut self)` → identity passthrough.
///
/// In single-threaded verification, exclusive `&mut` access makes `get_mut`
/// equivalent to returning the receiver — since `Atomic<T>` is transparent
/// to `T` in the CHC model, the result is the same pointer/value.
/// Part of #4067: used by `Arc::new` internally via `OnceBox`.
fn codegen_atomic_get_mut(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.is_empty() {
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
        return;
    }
    // get_mut(&mut self) → identity: return the receiver value.
    let receiver = ctx.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals);
    if let Some(val) = receiver
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        let dest_sort = dest_var.sort().clone();
        let eq = ctx.make_coerced_eq_constraint(
            &dest_var,
            val,
            &dest_sort,
            dest_local,
            "atomic::get_mut",
        );
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        if let Some(eq) = eq {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
        } else {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        }
    } else {
        #[rustfmt::skip]
        emit_sound_fallback_goto(ctx, dcx.from_app, target, dcx.modified_locals, &[dest_local], dcx.stmt_constraints);
    }
    debug!(dest_local, "atomic_get_mut: identity passthrough");
}
