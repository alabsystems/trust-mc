// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! P3-uninit: use-scan for type-punning `PtrToPtr` casts under
//! `-Z uninit-checks`.
//!
//! The punned-cast fail-closed net (`codegen_stmt_rvalue.rs`) demotes any
//! harness containing a size-mismatched pointee reinterpretation, because a
//! punned deref WRITE re-shapes initialization/padding in ways the scalar
//! shadow-memory model does not track (Kani's delayed-UB points-to pass;
//! trust-mc task #24). That is far coarser than necessary for the dominant
//! benign shape: `ptr::copy(p as *const u8, q as *mut u8, N)`, where the
//! punned pointer is consumed ONLY by
//!
//! - the copy intrinsic family (`copy` / `copy_nonoverlapping` /
//!   `volatile_copy*`): the VALUE effect is byte-splice-or-fail-closed
//!   (`try_copy_scalar_byte_splice` + demoting `copy_destination_self_loop`),
//!   and the SHADOW effect is the instrumentation's own `CopyInitState`
//!   call, encoded precise-or-fail-open-with-sound-fallback
//!   (`codegen_call_kani_model_mem_init.rs`);
//! - the `kani::mem_init` bookkeeping calls themselves (`Set*/Is*/Copy*` —
//!   shadow-model updates, no untracked memory effect);
//! - pointer-identity flows (`Use` / further `PtrToPtr` casts) into locals
//!   whose uses are, transitively, in this same set;
//! - no use at all (e.g. `let ptr = addr_of!(s) as *const u8;`).
//!
//! Every other occurrence — punned deref read/write, pointer arithmetic,
//! escape into an arbitrary call, aggregate capture, drop, switch — keeps
//! the demoting fallback (fail-closed). The scan is purely syntactic over
//! the (post-inlining) harness body and errs on the side of `false`.

use rustc_public::mir::{
    BinOp, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

use super::ChcCtx;

/// Does the operand read this local at all (with or without projections)?
fn operand_uses_local(op: &Operand, local: usize) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place.local == local,
        Operand::Constant(_) => false,
    }
}

/// Comparison binops yield a `bool` — a pure pointer-value predicate with no
/// memory/shadow effect (unlike arithmetic binops, which can derive a new
/// pointer). Includes the pointer-metadata `Offset` guard's own comparisons.
fn is_comparison_binop(op: BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Cmp)
}

/// Is the operand a BARE deref read of this local (`*p` exactly — no field /
/// index projections after the deref)?
fn operand_is_bare_deref_of_local(op: &Operand, local: usize) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            place.local == local
                && place.projection.len() == 1
                && matches!(place.projection[0], ProjectionElem::Deref)
        }
        Operand::Constant(_) => false,
    }
}

/// Is the operand exactly this local, with no projections (pure pointer
/// VALUE use, no deref / field access through it)?
fn operand_is_bare_local(op: &Operand, local: usize) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            place.local == local && place.projection.is_empty()
        }
        Operand::Constant(_) => false,
    }
}

/// Any read of the local inside a place used as an lvalue or place-context
/// (projection bases include derefs through the punned pointer).
fn place_uses_local(place: &Place, local: usize) -> bool {
    place.local == local
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// See module docs. `true` means every transitive use of `dest_local`
    /// (the punned cast's destination) is precisely-tracked, so the punned
    /// cast needs no demoting fallback.
    pub(in crate::codegen_ay::chc) fn punned_ptr_uses_are_tracked(
        &self,
        dest_local: usize,
    ) -> bool {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut worklist: Vec<usize> = vec![dest_local];

        while let Some(local) = worklist.pop() {
            if !seen.insert(local) {
                continue;
            }
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    if !self.pun_scan_statement_ok(stmt, local, &mut worklist) {
                        tracing::debug!(
                            local,
                            root = dest_local,
                            stmt = ?stmt.kind,
                            "pun scan: blocking statement use — keeping demotion"
                        );
                        return false;
                    }
                }
                if !self.pun_scan_terminator_ok(&bb.terminator.kind, local, &mut worklist) {
                    tracing::debug!(
                        local,
                        root = dest_local,
                        term = ?bb.terminator.kind,
                        "pun scan: blocking terminator use — keeping demotion"
                    );
                    return false;
                }
            }
        }
        true
    }

    fn pun_scan_statement_ok(
        &self,
        stmt: &rustc_public::mir::Statement,
        local: usize,
        worklist: &mut Vec<usize>,
    ) -> bool {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                // A projected store INTO the punned pointer (`*p = ...`) is
                // exactly the untracked write the net exists for.
                if place.local == local && !place.projection.is_empty() {
                    return false;
                }
                match rvalue {
                    // Pointer-identity flows: follow the value into the
                    // destination local and vet its uses too.
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                        if operand_is_bare_local(op, local) {
                            if !place.projection.is_empty() {
                                return false;
                            }
                            worklist.push(place.local);
                            true
                        } else if operand_is_bare_deref_of_local(op, local)
                            && place.projection.is_empty()
                            && place.local != local
                        {
                            // Raw-alloc route: a BARE deref READ (`_v = *p`).
                            // Reads cannot corrupt shadow tracking; the
                            // uninit-ness of the read is checked by the
                            // instrumentation's own paired `IsPtrInitialized`
                            // call (an allowed mem_init use), and the loaded
                            // VALUE is byte-memory precise-or-overapprox —
                            // same argument as the allowed `ptr::read` callee
                            // below. Punned deref WRITES (projected stores)
                            // stay demoted.
                            true
                        } else {
                            // Projected read through the pun (e.g. `(*p).f`).
                            !operand_uses_local(op, local)
                        }
                    }
                    // A pointer TO the punned pointer (`&raw const p` — the
                    // ub_checks / instrumentation calling convention): follow
                    // the pointer-to-pointer local; its own uses are vetted by
                    // the same rules (a deref WRITE through it shows up as a
                    // projected store and blocks).
                    Rvalue::AddressOf(_, place_r) | Rvalue::Ref(_, _, place_r) => {
                        if place_r.local == local && place_r.projection.is_empty() {
                            if !place.projection.is_empty() {
                                return false;
                            }
                            worklist.push(place.local);
                            true
                        } else {
                            !place_uses_local(place_r, local)
                        }
                    }
                    // Any other rvalue mentioning the local (deref reads,
                    // pointer arithmetic, discriminants, ...) — bail.
                    Rvalue::CopyForDeref(place_r)
                    | Rvalue::Discriminant(place_r)
                    | Rvalue::Len(place_r) => !place_uses_local(place_r, local),
                    // Raw-alloc route: a pointer-VALUE COMPARISON (`p == null`,
                    // `p < q`, ...) yields a bool, not a derived pointer — the
                    // ub_checks / is_null machinery emits these. Pure reads of
                    // the pointer value, no memory or shadow effect, so they do
                    // not block. Arithmetic binops (Offset/Add/...) can produce
                    // a derived pointer that is later deref'd — those still bail.
                    Rvalue::BinaryOp(op, a, b) if is_comparison_binop(*op) => {
                        let _ = (a, b);
                        true
                    }
                    Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                        !operand_uses_local(a, local) && !operand_uses_local(b, local)
                    }
                    Rvalue::UnaryOp(_, op)
                    | Rvalue::Repeat(op, _)
                    | Rvalue::ShallowInitBox(op, _) => !operand_uses_local(op, local),
                    Rvalue::Aggregate(_, ops) => {
                        !ops.iter().any(|op| operand_uses_local(op, local))
                    }
                    Rvalue::ThreadLocalRef(_) | Rvalue::NullaryOp(..) => true,
                }
            }
            // The copy-intrinsic statement form: bare pointer-value operands
            // are the tracked shape; anything projected is not.
            StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                [&copy.src, &copy.dst, &copy.count]
                    .into_iter()
                    .all(|op| !operand_uses_local(op, local) || operand_is_bare_local(op, local))
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                !operand_uses_local(op, local)
            }
            // Liveness / diagnostics markers: no runtime effect.
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => true,
            // Discriminant writes / retags touching the punned pointer:
            // conservative bail.
            StatementKind::SetDiscriminant { place, .. } => !place_uses_local(place, local),
            StatementKind::Retag(_, place) => !place_uses_local(place, local),
        }
    }

    fn pun_scan_terminator_ok(
        &self,
        kind: &TerminatorKind,
        local: usize,
        worklist: &mut Vec<usize>,
    ) -> bool {
        match kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                if operand_uses_local(func, local) {
                    return false;
                }
                let used_in_args = args.iter().any(|arg| operand_uses_local(arg, local));
                if !used_in_args {
                    // The call may overwrite the local as its destination —
                    // that's a kill, not a use.
                    let _ = destination;
                    return true;
                }
                // All argument uses must be bare pointer values into an
                // allowed callee (copy family or mem-init bookkeeping).
                if !args
                    .iter()
                    .all(|arg| !operand_uses_local(arg, local) || operand_is_bare_local(arg, local))
                {
                    return false;
                }
                // Raw-alloc route: allocation-identity callees (raw-pointer
                // `add`/`sub`/`offset`, slice `as_ptr`, `from_raw_parts`) are
                // pointer-VALUE transformers with no memory effect — the pun
                // continues in the DESTINATION local, so vet its uses
                // transitively instead of bailing. The destination's derefs
                // get the REAL walk-resolved alloc-bound obligations
                // (`offset_bound_obj_id_for_operand` /
                // `provenance_deref_bound_checks`), and its shadow reads are
                // instrumented like any other pointer.
                if let Some(path) = self.resolve_callee_path(func)
                    && Self::offset_walk_identity_callee(&path)
                    && destination.projection.is_empty()
                {
                    worklist.push(destination.local);
                    return true;
                }
                self.pun_scan_callee_is_tracked(func)
            }
            TerminatorKind::SwitchInt { discr, .. } => !operand_uses_local(discr, local),
            TerminatorKind::Assert { cond, .. } => !operand_uses_local(cond, local),
            TerminatorKind::Drop { place, .. } => !place_uses_local(place, local),
            TerminatorKind::InlineAsm { .. } => false,
            TerminatorKind::Goto { .. }
            | TerminatorKind::Resume
            | TerminatorKind::Abort
            | TerminatorKind::Return
            | TerminatorKind::Unreachable => true,
        }
    }

    /// Callees a punned pointer may flow into without losing tracking:
    /// the copy intrinsic family (value: splice-or-fail-closed; shadow:
    /// paired `CopyInitState`), the `kani::mem_init` shadow bookkeeping,
    /// and `core::ub_checks` precondition predicates (pure reads of the
    /// pointer VALUE — alignment/null/overlap checks, no memory effect).
    fn pun_scan_callee_is_tracked(&self, func: &Operand) -> bool {
        let Ok(func_ty) = func.ty(self.body.locals()) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            return false;
        };
        let name = fn_def.0.name();
        name.contains("intrinsics::copy")
            || name.contains("volatile_copy")
            // Non-inlined `std::ptr::copy{,_nonoverlapping}` calls route to the
            // same fail-closed copy encoder (`generic_preroutes.rs`).
            || name.contains("ptr::copy")
            // Non-inlined `std::ptr::read{,_unaligned,_volatile}` routes to the
            // PtrRead memory stub (`translate_ptr_read_call`): a typed-array
            // load whose value is unconstrained-or-checked (never wrongly
            // precise for a punned type), deref safety checks are emitted, and
            // the uninit-ness of the READ is checked by the instrumentation's
            // own `IsPtrInitialized` (an allowed mem_init call). Reads cannot
            // corrupt shadow tracking; punned WRITES stay demoted.
            || name.contains("ptr::read")
            || name.contains("mem_init::")
            || name.contains("ub_checks::")
            // `assert_unsafe_precondition!` expansions: `<fn>::precondition_check`
            // (e.g. `std::ptr::copy::precondition_check`) — pure pointer-value
            // predicates that abort on violation, no memory effect.
            || name.ends_with("::precondition_check")
            // Pointer-value predicates the (partially inlined) ub_checks
            // machinery calls: `<impl *const T>::is_null` / `is_null::runtime`
            // / `is_aligned*`. Pure reads of the pointer VALUE.
            || name.contains("::is_null")
            || name.contains("::is_aligned")
    }
}
