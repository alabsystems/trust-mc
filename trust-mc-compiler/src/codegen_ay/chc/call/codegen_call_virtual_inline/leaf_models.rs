// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Body-less callees the inline walker models itself instead of havocking.
//!
//! A call the walker cannot inline is havocked (`terminator_exec.rs`, the
//! nested-call fallback), and the havoc books its lost effect fail-closed
//! unless the callee is certified inert (Rule D). Two such callees are reached on
//! every walked `Box` or `dyn` shape and have a model the walker can state
//! (fix/chc-walker-fail-closed, package round 2 item e):
//!
//! * `vtable_size` / `vtable_align` read the vtable a `DynMetadata` points to.
//!   In the encoding a vtable pointer is a vtable IDENTITY minted at an unsize
//!   coercion, never an address a program can forge without breaking a
//!   `DynMetadata`'s validity invariant, so the read has nothing to check. Its
//!   value is exact when the pointer term is a registered identity (or an
//!   `ite` over them): the ite over the registered layouts. Otherwise it is
//!   the accounted havoc the fallback would mint, without the booking.
//! * `__rust_dealloc(ptr, size, align)` is the deallocator. Its obligations
//!   are the statement path's deallocator contract (`dealloc_pointer_terms`:
//!   the object is live and on the heap, `ptr` is its base, the size matches;
//!   the alignment is a power of two), which the walker now records under its
//!   path condition, and its effect (the object is freed) is applied to the
//!   rule's running `obj_valid`, so a later use or a second free is caught.
//!   Where the size or alignment argument rides a symbol the walker minted
//!   (a depth-exhausted `Layout::size`), those two obligations cannot be
//!   stated and the call keeps the fail-closed booking, exactly as the
//!   statement path records `dealloc_args_unresolved` for the same case.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::codegen_call_vtable_intrinsic::VtableIntrinsicKind;
use super::super::codegen_ctx::globals::chc_fresh_name;
use super::super::inline_shared::inline_operand_to_expr;
use super::execution_state::InlineExecutionState;
use super::loop_replay::InlineWalkCtx;
use super::terminator_exec::{TerminatorStep, apply_inline_writeback};
use crate::codegen_ay::chc::codegen_ctx::Havoc;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Try the models above for the call `func(args)` into `destination`.
/// `None`: not one of them, or the model declined; the caller takes its
/// havoc fallback (and its bookings) as before.
pub(super) fn try_execute_leaf_model<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    func: &Operand,
    args: &[Operand],
    destination: &Place,
    target_bb: usize,
) -> Option<TerminatorStep> {
    let instance = resolve_leaf_instance(ctx, func, walk_ctx)?;
    if let Some(kind) = vtable_read_kind(&instance) {
        return execute_vtable_read(ctx, walk_ctx, state, kind, args, destination, target_bb);
    }
    if is_rust_dealloc(&instance) {
        return execute_rust_dealloc(ctx, walk_ctx, state, args, destination, target_bb);
    }
    if let Some(half) = layout_getter_half(&instance) {
        return execute_layout_getter(ctx, walk_ctx, state, half, args, destination, target_bb);
    }
    None
}

/// Which half of the packed `Layout` (`bv128 = concat(size, align)`) a
/// getter reads: `Layout::size` the upper, `Layout::align` the lower.
#[derive(Clone, Copy, Debug)]
enum LayoutHalf {
    Size,
    Align,
}

fn layout_getter_half(instance: &Instance) -> Option<LayoutHalf> {
    let name = instance.name();
    let base = name.split("::<").next().unwrap_or(&name);
    if !base.contains("Layout::") {
        return None;
    }
    match base.rsplit("::").next()? {
        "size" => Some(LayoutHalf::Size),
        "align" => Some(LayoutHalf::Align),
        _ => None,
    }
}

/// `Layout::size` / `Layout::align` on the packed layout: the half the
/// allocator models read (`extract_layout_size_align`). The walked getter
/// body projects a field of the `bv128`, which the walker cannot, so the call
/// used to be havocked (at depth, or whenever the body walk failed) and a
/// `__rust_dealloc` downstream lost its size. A getter has no obligation.
fn execute_layout_getter<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    half: LayoutHalf,
    args: &[Operand],
    destination: &Place,
    target_bb: usize,
) -> Option<TerminatorStep> {
    let [receiver] = args else {
        return None;
    };
    // `&self` is thin: a 128-bit term for it is the transparent layout value,
    // never an address.
    let layout = inline_operand_to_expr(
        ctx,
        receiver,
        &state.local_exprs,
        &walk_ctx.resolver,
        walk_ctx.locals,
    )
    .filter(|term| term.sort().bitvec_width() == Some(128))?;
    let value = match half {
        LayoutHalf::Size => layout.extract(127, 64),
        LayoutHalf::Align => layout.extract(63, 0),
    };
    debug!(?half, "walker: Layout getter reads the packed layout");
    if apply_inline_writeback(ctx, walk_ctx, state, destination, value) {
        Some(TerminatorStep::ContinueAt(target_bb))
    } else {
        None
    }
}

fn resolve_leaf_instance(
    ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    walk_ctx: &InlineWalkCtx<'_>,
) -> Option<Instance> {
    let raw = func.ty(walk_ctx.locals).ok()?;
    let (def, args) = match ctx.resolve_body_ty(raw).kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => match raw.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None,
        },
    };
    Instance::resolve(def, &args).ok()
}

/// `vtable_size` / `vtable_align`, the intrinsics.
pub(super) fn vtable_read_kind(instance: &Instance) -> Option<VtableIntrinsicKind> {
    if !matches!(instance.kind, InstanceKind::Intrinsic) {
        return None;
    }
    match instance.intrinsic_name()?.as_str() {
        "vtable_size" => Some(VtableIntrinsicKind::Size),
        "vtable_align" => Some(VtableIntrinsicKind::Align),
        _ => None,
    }
}

/// The allocator's `__rust_dealloc`, a foreign item with no body.
fn is_rust_dealloc(instance: &Instance) -> bool {
    let name = instance.name();
    let base = name.split("::<").next().unwrap_or(&name);
    (base == "__rust_dealloc" || base.ends_with("::__rust_dealloc")) && !instance.has_body()
}

/// The value of a vtable read of `vtable` from the registered layouts
/// (`ChcCtx::vtable_type_metadata`): exact when the term is a registered
/// identity, or an `ite` whose every leaf is one. `None` otherwise.
pub(super) fn vtable_read_from_identities(
    vtable: &Expr,
    layouts: &HashMap<u64, (u64, u64)>,
    kind: VtableIntrinsicKind,
) -> Option<Expr> {
    match vtable.value() {
        ExprValue::BitVecConst { value, .. } => {
            let id = u64::try_from(value.clone()).ok()?;
            let &(size, align) = layouts.get(&id)?;
            let read = match kind {
                VtableIntrinsicKind::Size => size,
                VtableIntrinsicKind::Align => align,
            };
            Some(Expr::bitvec_const(u128::from(read), POINTER_WIDTH))
        }
        ExprValue::Ite { cond, then_expr, else_expr } => Some(Expr::ite(
            cond.clone(),
            vtable_read_from_identities(then_expr, layouts, kind)?,
            vtable_read_from_identities(else_expr, layouts, kind)?,
        )),
        _ => None,
    }
}

fn execute_vtable_read<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    kind: VtableIntrinsicKind,
    args: &[Operand],
    destination: &Place,
    target_bb: usize,
) -> Option<TerminatorStep> {
    let vtable = args.first().and_then(|arg| {
        inline_operand_to_expr(ctx, arg, &state.local_exprs, &walk_ctx.resolver, walk_ctx.locals)
    });
    let exact = vtable
        .as_ref()
        .filter(|term| term.sort().bitvec_width() == Some(POINTER_WIDTH))
        .and_then(|term| vtable_read_from_identities(term, &ctx.vtable_type_metadata, kind));
    let value = match exact {
        Some(value) => {
            debug!(?kind, "walker: vtable read resolved over the registered layouts");
            value
        }
        None => {
            // The pointer is no registered identity the walk can name by its
            // term (a state variable the host binds, say): the read is the
            // registered layout of whichever identity it holds, and unknown
            // for any other pointer. That default is the fallback's own
            // accounted freed variable; the read still checks nothing.
            let name = chc_fresh_name("__nested_call_overapprox_vtable_read");
            ctx.note_gap_reason("nested_call_overapprox@vtable_read");
            let booked =
                ctx.record_sound_fallback_reason_identified("nested_call_overapprox", Some(&name));
            debug!(?kind, "walker: vtable read of a pointer no registered identity names by term");
            let mut value = Havoc::booked(booked, name, Sort::bitvec(POINTER_WIDTH));
            if let Some(term) =
                vtable.filter(|term| term.sort().bitvec_width() == Some(POINTER_WIDTH))
            {
                let mut ids: Vec<(u64, (u64, u64))> =
                    ctx.vtable_type_metadata.iter().map(|(&id, &layout)| (id, layout)).collect();
                ids.sort_unstable();
                for (id, (size, align)) in ids.into_iter().rev() {
                    let read = match kind {
                        VtableIntrinsicKind::Size => size,
                        VtableIntrinsicKind::Align => align,
                    };
                    value = Expr::ite(
                        term.clone().eq(Expr::bitvec_const(u128::from(id), POINTER_WIDTH)),
                        Expr::bitvec_const(u128::from(read), POINTER_WIDTH),
                        value,
                    );
                }
            }
            value
        }
    };
    if apply_inline_writeback(ctx, walk_ctx, state, destination, value) {
        Some(TerminatorStep::ContinueAt(target_bb))
    } else {
        None
    }
}

/// Kani's descriptions of its `__rust_dealloc` checks (`kani_lib.c`) and of
/// CBMC's `free` checks.
const DEALLOC_MESSAGE: &str = "rust_dealloc: the freed pointer must be the base of a live heap \
     allocation whose allocated size matches its layout, with a power-of-two alignment";
const DEALLOC_LAYOUT_UNSTATED: &str = "walker_dealloc_layout_unstated";

fn execute_rust_dealloc<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    walk_ctx: &InlineWalkCtx<'_>,
    state: &mut InlineExecutionState,
    args: &[Operand],
    destination: &Place,
    target_bb: usize,
) -> Option<TerminatorStep> {
    let [ptr_op, size_op, align_op] = args else {
        return None;
    };
    let mut translate = |ctx: &mut ChcCtx<'tcx, 'body>, op: &Operand| {
        inline_operand_to_expr(ctx, op, &state.local_exprs, &walk_ctx.resolver, walk_ctx.locals)
    };
    let ptr = translate(ctx, ptr_op)?;
    // A size or alignment built from a symbol the walker minted where it gave
    // up is no program term: stating a check over it fails for a value the
    // program never passes, so it is not stated and the call fails closed.
    let exact = |term: Option<Expr>| {
        term.filter(|term| !super::execution_state::expr_mentions_walker_giveup_symbol(term))
    };
    let size = exact(translate(ctx, size_op));
    let align = exact(translate(ctx, align_op));
    let layout_stated = size.is_some() && align.is_some();
    debug!(%ptr, size = ?size.as_ref().map(ToString::to_string), align = ?align.as_ref().map(ToString::to_string), "walker: __rust_dealloc operands");
    let checks = ctx.inline_rust_dealloc(&ptr, size, align)?;
    for check in checks {
        debug!(%check, "walker: __rust_dealloc check");
        state.record_deferred_check(
            PropertyKind::MemorySafety,
            Some(DEALLOC_MESSAGE.to_string()),
            check,
            ctx.heap_state.write_mark(),
        );
    }
    if !layout_stated {
        debug!("walker: __rust_dealloc layout arguments not program terms — fail closed");
        ctx.record_sound_fallback_reason(DEALLOC_LAYOUT_UNSTATED);
    }
    debug!(layout_stated, "walker: __rust_dealloc modelled (free applied, contract recorded)");
    // `__rust_dealloc` returns `()`.
    if apply_inline_writeback(ctx, walk_ctx, state, destination, Expr::bool_const(true)) {
        Some(TerminatorStep::ContinueAt(target_bb))
    } else {
        None
    }
}
