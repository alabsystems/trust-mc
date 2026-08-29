// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! C-variadic call specialization for the function inlining pass.
//!
//! Variadic-ness is a calling-convention fiction: a model checker needs the
//! argument SEQUENCE, not an ABI, and MIR already carries it. At a `Call`
//! terminator whose callee signature has `c_variadic` set, the `args` vector
//! holds the actual variadic arguments, so the callee can be specialized to
//! that exact list and variadic-ness disappears.
//!
//! The model, applied while `inline_function` splices a `c_variadic` callee:
//!
//! 1. **Call-site monomorphization.** The named parameters bind 1:1 as usual.
//!    The trailing `VaListImpl` parameter binds to nothing; instead each actual
//!    variadic argument is copied into a fresh caller local at the call site
//!    (arguments are evaluated by the caller, so a later write inside the
//!    inlined body cannot disturb them).
//! 2. **`VaListImpl` = actual list + cursor.** A fresh `usize` cursor local is
//!    initialised to 0. Every `VaListImpl::arg::<T>()` / `va_arg` fetch in the
//!    spliced body becomes `dest = actual[cursor]; cursor += 1`, encoded as a
//!    `switchInt` over the cursor with one arm per actual.
//! 3. **Default argument promotions.** The arm for actual `k` coerces it to the
//!    fetch type `T` using exactly the C promotions that demonstrably apply at
//!    the call site: an integer narrower than `int` widens to `int`, `f32`
//!    widens to `f64`, and same-width integer reads are bit-identical. Any
//!    other actual/fetch pairing is NOT modelled (see below).
//! 4. **UB obligations.** `va_arg` past the end of the actual list is UB, so the
//!    fetch is guarded by a real `Assert` (`cursor < N`) — a proof obligation
//!    that the caller must discharge, never an assumption. Nothing is assumed
//!    about the callee: the actual list is read from the caller's own MIR.
//!
//! Where the cursor is not statically resolvable this module DECLINES: a
//! `VaListImpl` that escapes into an opaque callee, is stored through a
//! projection, or is fetched at a type the C promotions do not relate to the
//! actual, all return `None` from [`plan_variadic_inline`]. Declining leaves
//! the ordinary un-inlined call in place, whose result the CHC/BMC dispatch
//! leaves unconstrained — the sound over-approximation. Guessing a cursor is
//! the convenient assumption in this construct, and it is never taken.

use super::remap::monomorphize_ty;
use crate::kani_middle::transform::body::MutableBody;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AssertMessage, BasicBlock, BasicBlockIdx, BinOp, Body, CastKind, Local, LocalDecl, Mutability,
    Operand, Place, Rvalue, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind,
};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, Span, Ty, TyKind, UintTy};
use std::collections::HashSet;
use tracing::debug;

/// A committed plan to specialize one `c_variadic` call site.
pub(super) struct VariadicPlan {
    /// Number of NAMED parameters, i.e. callee arg locals `1..=named_count`.
    /// The callee's remaining arg local is the `VaListImpl` standing for `...`.
    pub(super) named_count: usize,
    /// Callee basic-block indices whose terminator is a `va_arg` fetch.
    pub(super) fetch_bbs: Vec<BasicBlockIdx>,
    /// Caller-side types of the actual variadic arguments, in order.
    pub(super) actual_tys: Vec<Ty>,
}

/// Decide whether this call site can be specialized, and how.
///
/// Pure: reads the callee body and the caller's local declarations, mutates
/// nothing. `None` means "not a modellable variadic call" — the caller falls
/// back to its ordinary inline path (or to leaving the call in place).
pub(super) fn plan_variadic_inline(
    tcx: TyCtxt<'_>,
    callee_instance: Instance,
    callee: &Body,
    caller: &MutableBody,
    call_args: &[Operand],
) -> Option<VariadicPlan> {
    if !callee_sig_is_c_variadic(callee_instance) {
        return None;
    }

    // The `...` parameter lowers to a trailing `VaListImpl` arg local.
    let arg_count = callee.arg_locals().len();
    if arg_count == 0 {
        return None;
    }
    let named_count = arg_count - 1;
    let valist_local: Local = arg_count;
    if !is_va_list_ty(callee.locals()[valist_local].ty) {
        debug!("variadic: trailing arg local is not a VaListImpl — declining");
        return None;
    }
    if call_args.len() < named_count {
        debug!("variadic: call site has fewer args than named params — declining");
        return None;
    }

    let fetch_bbs = collect_fetch_sites(callee, valist_local)?;

    // Actual variadic argument types, read from the CALLER's MIR (ground truth).
    let mut actual_tys = Vec::with_capacity(call_args.len() - named_count);
    for arg in &call_args[named_count..] {
        let Ok(ty) = arg.ty(caller.locals()) else {
            debug!("variadic: actual argument type unresolved — declining");
            return None;
        };
        actual_tys.push(ty);
    }

    // Every (fetch site, actual index) pair must be related by a C default
    // argument promotion. The cursor is dynamic, so a single unmodellable pair
    // sinks the whole specialization.
    for &bb in &fetch_bbs {
        let fetch_ty = fetch_ty_at(tcx, callee_instance, callee, bb)?;
        for actual_ty in &actual_tys {
            if promoted_coercion(*actual_ty, fetch_ty).is_none() {
                debug!("variadic: no C promotion relates an actual to a fetch type — declining");
                return None;
            }
        }
    }

    debug!(
        "variadic: specializing call site — {} named param(s), {} actual(s), {} fetch site(s)",
        named_count,
        actual_tys.len(),
        fetch_bbs.len()
    );
    Some(VariadicPlan { named_count, fetch_bbs, actual_tys })
}

/// Rewrite every `va_arg` fetch in the already-remapped callee blocks.
///
/// Returns the extra basic blocks to append AFTER `new_blocks` (and after the
/// projected-destination post-return block, if any); `first_extra_bb` is the
/// caller block index the first of them will receive.
pub(super) fn rewrite_fetch_terminators(
    caller: &mut MutableBody,
    new_blocks: &mut [BasicBlock],
    plan: &VariadicPlan,
    actual_locals: &[Local],
    cursor_local: Local,
    first_extra_bb: BasicBlockIdx,
    span: Span,
) -> Vec<BasicBlock> {
    let bool_ty = Ty::from_rigid_kind(RigidTy::Bool);
    let n_actuals = actual_locals.len();
    let mut extra: Vec<BasicBlock> = Vec::new();

    for &fetch_bb in &plan.fetch_bbs {
        let Some(block) = new_blocks.get_mut(fetch_bb) else { continue };
        let TerminatorKind::Call { destination, target, unwind, .. } = &block.terminator.kind
        else {
            continue;
        };
        let dest = destination.clone();
        let Some(orig_target) = *target else { continue };
        let unwind = unwind.clone();

        // `cursor < N` — a real proof obligation. `va_arg` past the end of the
        // actual argument list is UB, so this is asserted, never assumed.
        let len_operand = caller.new_uint_operand(n_actuals as u128, UintTy::Usize, span);
        let in_range = caller.new_local(bool_ty, span, Mutability::Not);
        block.statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from(in_range),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Copy(Place::from(cursor_local)),
                    len_operand.clone(),
                ),
            ),
            span,
        });

        // With zero actuals every fetch is UB; the assert alone carries it and
        // there is no arm to branch to.
        let assert_target = if n_actuals == 0 { orig_target } else { first_extra_bb + extra.len() };
        block.terminator = Terminator {
            kind: TerminatorKind::Assert {
                cond: Operand::Move(Place::from(in_range)),
                expected: true,
                msg: AssertMessage::BoundsCheck {
                    len: len_operand,
                    index: Operand::Copy(Place::from(cursor_local)),
                },
                target: assert_target,
                unwind: unwind.clone(),
            },
            span,
        };
        if n_actuals == 0 {
            continue;
        }

        // switchInt(cursor) -> one arm per actual. The assert above pins the
        // cursor into `0..N`, so the `otherwise` edge is the last arm.
        let switch_bb_idx = first_extra_bb + extra.len();
        extra.push(BasicBlock {
            statements: Vec::new(),
            terminator: Terminator { kind: TerminatorKind::Unreachable, span },
        });

        let mut branches: Vec<(u128, BasicBlockIdx)> = Vec::with_capacity(n_actuals);
        for (k, &actual_local) in actual_locals.iter().enumerate() {
            let arm_idx = first_extra_bb + extra.len();
            let actual_ty = plan.actual_tys[k];
            let fetch_ty = caller.locals()[dest.local].ty;
            let value = promoted_coercion(actual_ty, fetch_ty)
                .expect("coercion validated in plan_variadic_inline")
                .rvalue(actual_local, fetch_ty);
            let one = caller.new_uint_operand(1, UintTy::Usize, span);
            extra.push(BasicBlock {
                statements: vec![
                    Statement { kind: StatementKind::Assign(dest.clone(), value), span },
                    Statement {
                        kind: StatementKind::Assign(
                            Place::from(cursor_local),
                            Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::from(cursor_local)),
                                one,
                            ),
                        ),
                        span,
                    },
                ],
                terminator: Terminator { kind: TerminatorKind::Goto { target: orig_target }, span },
            });
            branches.push((k as u128, arm_idx));
        }

        let otherwise = branches.pop().expect("at least one actual").1;
        extra[switch_bb_idx - first_extra_bb].terminator = Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(cursor_local)),
                targets: SwitchTargets::new(branches, otherwise),
            },
            span,
        };
    }

    extra
}

// ── Signature / type predicates ──────────────────────────────────────────────

fn callee_sig_is_c_variadic(callee_instance: Instance) -> bool {
    callee_instance.ty().kind().fn_sig().is_some_and(|sig| sig.value.c_variadic)
}

fn is_va_list_ty(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => def.0.name().contains("VaListImpl"),
        _ => false,
    }
}

/// Is this callee the `VaListImpl` argument fetch (`arg::<T>` or the intrinsic
/// it lowers to)?
fn is_va_arg_callee(func: &Operand, locals: &[LocalDecl]) -> bool {
    let Ok(ty) = func.ty(locals) else { return false };
    let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = ty.kind() else { return false };
    let name = fn_def.0.name();
    name.ends_with("::va_arg") || (name.contains("VaList") && name.ends_with("::arg"))
}

/// Monomorphized type fetched by the `va_arg` call terminating `bb`.
fn fetch_ty_at(
    tcx: TyCtxt<'_>,
    callee_instance: Instance,
    callee: &Body,
    bb: BasicBlockIdx,
) -> Option<Ty> {
    let TerminatorKind::Call { destination, .. } = &callee.blocks[bb].terminator.kind else {
        return None;
    };
    if !destination.projection.is_empty() {
        return None;
    }
    Some(monomorphize_ty(tcx, callee_instance, callee.locals()[destination.local].ty))
}

// ── C default argument promotions ────────────────────────────────────────────

/// How an actual variadic argument reaches the type a `va_arg` fetch asks for.
enum Promotion {
    /// Same type (or a same-width integer read): bit-identical.
    Identity,
    /// C integer promotion to `int`.
    IntWiden,
    /// C floating promotion `f32` -> `f64`.
    FloatWiden,
}

impl Promotion {
    fn rvalue(&self, actual_local: Local, fetch_ty: Ty) -> Rvalue {
        let operand = Operand::Copy(Place::from(actual_local));
        match self {
            Promotion::Identity => Rvalue::Use(operand),
            Promotion::IntWiden => Rvalue::Cast(CastKind::IntToInt, operand, fetch_ty),
            Promotion::FloatWiden => Rvalue::Cast(CastKind::FloatToFloat, operand, fetch_ty),
        }
    }
}

/// The C default argument promotions, and nothing else.
///
/// `None` means the pairing is not modelled — the caller declines rather than
/// invent a conversion. In particular a fetch WIDER than its actual (reading
/// eight bytes where four were passed) is genuine UB whose value no sound model
/// can supply, so it is never coerced.
fn promoted_coercion(actual_ty: Ty, fetch_ty: Ty) -> Option<Promotion> {
    if actual_ty == fetch_ty {
        return Some(Promotion::Identity);
    }
    match (int_width(actual_ty), int_width(fetch_ty)) {
        (Some(a), Some(f)) if a == f => return Some(Promotion::Identity),
        // Integer promotion: anything narrower than `int` arrives as `int`.
        (Some(a), Some(f)) if a < 32 && f == 32 => return Some(Promotion::IntWiden),
        _ => {}
    }
    match (float_width(actual_ty), float_width(fetch_ty)) {
        (Some(32), Some(64)) => Some(Promotion::FloatWiden),
        _ => None,
    }
}

fn int_width(ty: Ty) -> Option<u32> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int_ty)) => Some(match int_ty {
            IntTy::I8 => 8,
            IntTy::I16 => 16,
            IntTy::I32 => 32,
            IntTy::I64 => 64,
            IntTy::I128 => 128,
            IntTy::Isize => usize::BITS,
        }),
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Some(match uint_ty {
            UintTy::U8 => 8,
            UintTy::U16 => 16,
            UintTy::U32 => 32,
            UintTy::U64 => 64,
            UintTy::U128 => 128,
            UintTy::Usize => usize::BITS,
        }),
        _ => None,
    }
}

fn float_width(ty: Ty) -> Option<u32> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Float(float_ty)) => Some(match float_ty {
            FloatTy::F16 => 16,
            FloatTy::F32 => 32,
            FloatTy::F64 => 64,
            FloatTy::F128 => 128,
        }),
        _ => None,
    }
}

// ── Cursor resolvability ─────────────────────────────────────────────────────

/// Locate every `va_arg` fetch on `valist_local`, or decline.
///
/// Declines unless the `VaListImpl` is used ONLY to reach fetches: any other
/// use (escaping into an opaque callee, a store through it, a read of its
/// fields) means the fetch cursor is not statically resolvable, and a guessed
/// cursor would fabricate values.
fn collect_fetch_sites(callee: &Body, valist_local: Local) -> Option<Vec<BasicBlockIdx>> {
    let alias = alias_closure(callee, valist_local);
    let mut fetch_bbs = Vec::new();

    for (bb_idx, block) in callee.blocks.iter().enumerate() {
        for stmt in &block.statements {
            if !statement_use_is_recognized(stmt, &alias) {
                debug!("variadic: VaListImpl reached an unmodelled statement — declining");
                return None;
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { func, args, destination, target, .. } => {
                let touches = args.iter().any(|a| operand_mentions(a, &alias))
                    || alias.contains(&destination.local);
                if !touches {
                    continue;
                }
                let is_fetch = args.len() == 1
                    && matches!(&args[0], Operand::Copy(p) | Operand::Move(p)
                        if alias.contains(&p.local) && p.projection.is_empty())
                    && !alias.contains(&destination.local)
                    && destination.projection.is_empty()
                    && target.is_some()
                    && is_va_arg_callee(func, callee.locals());
                if !is_fetch {
                    debug!("variadic: VaListImpl escaped into an opaque call — declining");
                    return None;
                }
                fetch_bbs.push(bb_idx);
            }
            // Dropping the list is `va_end`: it ends the traversal and cannot
            // move the cursor of a list this body still reads.
            TerminatorKind::Drop { place, .. } => {
                if alias.contains(&place.local) && place.local != valist_local {
                    debug!("variadic: a VaListImpl alias was dropped — declining");
                    return None;
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                if operand_mentions(discr, &alias) {
                    return None;
                }
            }
            TerminatorKind::Assert { cond, .. } => {
                if operand_mentions(cond, &alias) {
                    return None;
                }
            }
            TerminatorKind::InlineAsm { .. } => return None,
            _ => {}
        }
    }

    Some(fetch_bbs)
}

/// Least set of locals that may denote the `VaListImpl` or a pointer to it.
fn alias_closure(callee: &Body, valist_local: Local) -> HashSet<Local> {
    let mut alias: HashSet<Local> = HashSet::new();
    alias.insert(valist_local);
    loop {
        let mut changed = false;
        for block in &callee.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                if !dest.projection.is_empty() {
                    continue;
                }
                let source = match rvalue {
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place) => Some(place),
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                        Some(place)
                    }
                    _ => None,
                };
                if let Some(place) = source
                    && alias.contains(&place.local)
                    && alias.insert(dest.local)
                {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    alias
}

/// Is this statement one of the recognized `VaListImpl` uses?
fn statement_use_is_recognized(stmt: &Statement, alias: &HashSet<Local>) -> bool {
    match &stmt.kind {
        StatementKind::Assign(dest, rvalue) => {
            // A write THROUGH the list (or into one of its fields) is outside
            // the model.
            if alias.contains(&dest.local) && !dest.projection.is_empty() {
                return false;
            }
            match rvalue {
                Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
                | Rvalue::CopyForDeref(place) => {
                    // Taking the address of the list (or re-borrowing a pointer
                    // to it) is how a fetch reaches it: fine, and the result is
                    // already in the alias set.
                    !alias.contains(&place.local) || alias.contains(&dest.local)
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                    if !alias.contains(&place.local) {
                        return true;
                    }
                    // Reading a FIELD of the list exposes the ABI cursor we do
                    // not model.
                    place.projection.is_empty() && alias.contains(&dest.local)
                }
                other => !rvalue_mentions(other, alias),
            }
        }
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::Nop
        | StatementKind::PlaceMention(_)
        | StatementKind::FakeRead(..)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Retag(..)
        | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter => true,
        StatementKind::SetDiscriminant { place, .. } => !alias.contains(&place.local),
        StatementKind::Intrinsic(_) => false,
    }
}

fn operand_mentions(operand: &Operand, alias: &HashSet<Local>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => alias.contains(&place.local),
        Operand::Constant(_) => false,
    }
}

fn rvalue_mentions(rvalue: &Rvalue, alias: &HashSet<Local>) -> bool {
    match rvalue {
        Rvalue::AddressOf(_, place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::Ref(_, _, place) => alias.contains(&place.local),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|o| operand_mentions(o, alias)),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_mentions(lhs, alias) || operand_mentions(rhs, alias)
        }
        Rvalue::Cast(_, operand, _)
        | Rvalue::Repeat(operand, _)
        | Rvalue::ShallowInitBox(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Use(operand) => operand_mentions(operand, alias),
        Rvalue::NullaryOp(..) | Rvalue::ThreadLocalRef(_) => false,
    }
}
