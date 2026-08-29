// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Body inlining and drop shim resolution for the function inlining pass.
//!
//! Contains the core mechanics of inlining a callee body into a caller:
//! - `inline_function`: inlines a function body at a Call terminator site
//! - `resolve_drop_terminators`: resolves Drop terminators by inlining drop shims
//! - `inline_drop_shim`: inlines a drop shim body at a Drop terminator site
//!
//! These are pure transformation functions with no dependency on the inlining
//! pass configuration or call-site selection logic.

use super::remap::{monomorphize_ty, remap_block_with_ty};
use super::variadic;
use crate::kani_middle::transform::body::MutableBody;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BasicBlock, BasicBlockIdx, Body, Local, Mutability, Operand, Place,
    ProjectionElem, RawPtrKind, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Span, Ty, TyKind, UintTy};
use std::collections::HashMap;
use tracing::debug;

/// Inline a function body at a call site.
///
/// Handles projected destinations (e.g., `_3.0 = foo()`) by creating a
/// temporary return local and a post-return assignment block (#225).
///
/// Returns the number of actual variadic arguments when the callee was a
/// specialized `c_variadic` function with at least one `va_arg` fetch — a
/// construct-derived unwind bound for any loop that fetches (see
/// [`variadic`]).
pub(super) fn inline_function(
    tcx: TyCtxt<'_>,
    callee_instance: Instance,
    caller: &mut MutableBody,
    call_bb_idx: BasicBlockIdx,
    callee: &Body,
    call_args: &[Operand],
    call_dest: &Place,
    call_target: Option<BasicBlockIdx>,
    call_span: Span,
) -> Option<usize> {
    let callee_locals = callee.locals();
    let has_projection = !call_dest.projection.is_empty();

    // Defensive check: callee must have at least the return local (local 0)
    if callee_locals.is_empty() {
        debug!("inline_function: callee has no locals, skipping inline");
        return None;
    }

    // C-variadic specialization: the call site's own MIR carries the actual
    // argument sequence, so the `...` parameter is modelled as that list plus a
    // fetch cursor. Planned BEFORE any mutation so the actual argument types are
    // read from the untouched caller. `None` = not modellable; fall through to
    // the ordinary paths (which, for a genuinely variadic call, means the
    // arity mismatch below leaves the extra arguments unbound).
    let variadic_plan =
        variadic::plan_variadic_inline(tcx, callee_instance, callee, caller, call_args);

    // Map from callee local index to caller local index
    let mut local_map: HashMap<Local, Local> = HashMap::new();

    // For projected destinations, create a temporary local for the return value.
    // Otherwise, map directly to call_dest.local (fast path).
    let ret_tmp: Option<Local> = if has_projection {
        let return_ty = monomorphize_ty(tcx, callee_instance, callee_locals[0].ty);
        let return_span = callee_locals[0].span;
        let return_mutability = callee_locals[0].mutability;
        Some(caller.new_local(return_ty, return_span, return_mutability))
    } else {
        caller.set_local_ty(
            call_dest.local,
            monomorphize_ty(tcx, callee_instance, callee_locals[0].ty),
        );
        None
    };

    // Add callee locals to caller
    for (callee_local, decl) in callee_locals.iter().enumerate() {
        if callee_local == 0 {
            // Map return local: to ret_tmp if projected, otherwise to call_dest.local
            let target_local = ret_tmp.unwrap_or(call_dest.local);
            local_map.insert(callee_local, target_local);
        } else {
            let new_local = caller.new_local(
                monomorphize_ty(tcx, callee_instance, decl.ty),
                decl.span,
                decl.mutability,
            );
            local_map.insert(callee_local, new_local);
        }
    }

    // Initialize argument locals with call arguments.
    // #1582: If callee expects tuple but call site has spread args, pack them.
    // #1598: If call site provides tuple but callee expects spread args, un-tuple.
    let arg_count = callee.arg_locals().len();
    let needs_tuple_packing = arg_count == 2 && call_args.len() > 2;
    // Un-tuple only if: call site has 2 args, callee expects >2, AND tuple arg is a place (not constant)
    let tuple_arg_is_place =
        call_args.get(1).is_some_and(|op| matches!(op, Operand::Copy(_) | Operand::Move(_)));
    // A one-parameter closure has `arg_count == 2` (self + the parameter), and
    // the RustCall ABI still hands it a ONE-element tuple. `arg_count > 2` alone
    // therefore never fires for it, and the tuple was bound whole to the
    // parameter. The values line up -- a 1-tuple of `&u8` lays out like `&u8` --
    // so nothing looked wrong, but the reference's identity did not survive:
    // codegen tracks the pointee under the tuple's FIELD key while the body
    // dereferences the parameter itself, finds nothing, and invents a fresh
    // symbolic pointee. `kani::any_where(|s| *s < 10)` then constrained a value
    // unrelated to the one it returned.
    //
    // Decide by type rather than arity: un-tuple when the callee's parameter is
    // the tuple's ELEMENT, and leave it packed when the parameter really is the
    // tuple (a closure declared `|t: (&u8,)|`, whose RustCall argument is
    // `((&u8,),)`).
    //
    // The operand must genuinely BE a one-element tuple: an ordinary two-argument
    // call also has `call_args.len() == 2` and `arg_count == 2`, and spreading
    // its second argument would project a tuple field out of something that is
    // not a tuple.
    let untuple_single_param = arg_count == 2 && {
        let tuple_ty = call_args.get(1).and_then(|op| op.ty(caller.locals()).ok());
        let param_ty =
            callee_locals.get(2).map(|decl| monomorphize_ty(tcx, callee_instance, decl.ty));
        match (tuple_ty, param_ty) {
            (Some(tuple_ty), Some(param_ty)) => {
                matches!(
                    tuple_ty.kind(),
                    TyKind::RigidTy(RigidTy::Tuple(ref fields)) if fields.len() == 1
                ) && tuple_ty != param_ty
            }
            _ => false,
        }
    };
    let needs_untuple =
        call_args.len() == 2 && (arg_count > 2 || untuple_single_param) && tuple_arg_is_place;

    // Locals materializing the `...` parameter for a specialized variadic call.
    let mut va_actual_locals: Vec<Local> = Vec::new();
    let mut va_cursor_local: Local = 0;

    let init_stmts: Vec<Statement> = if let Some(plan) = &variadic_plan {
        let mut stmts = Vec::new();

        // Named parameters bind 1:1, exactly as in a non-variadic call.
        for i in 0..plan.named_count {
            let caller_arg_local = local_map[&(i + 1)];
            stmts.push(Statement {
                kind: StatementKind::Assign(
                    Place::from(caller_arg_local),
                    Rvalue::Use(call_args[i].clone()),
                ),
                span: call_span,
            });
        }

        // Each actual variadic argument is COPIED at the call site: arguments
        // are evaluated by the caller, so a later write inside the inlined body
        // must not disturb what a fetch reads.
        for (k, actual_ty) in plan.actual_tys.iter().enumerate() {
            let local = caller.new_local(*actual_ty, call_span, Mutability::Mut);
            stmts.push(Statement {
                kind: StatementKind::Assign(
                    Place::from(local),
                    Rvalue::Use(call_args[plan.named_count + k].clone()),
                ),
                span: call_span,
            });
            va_actual_locals.push(local);
        }

        // The fetch cursor starts at the first actual. The trailing
        // `VaListImpl` arg local is deliberately left unbound: nothing reads it
        // (checked by the plan), and binding it would model an ABI the checker
        // does not need.
        va_cursor_local = caller.new_local(
            Ty::from_rigid_kind(RigidTy::Uint(UintTy::Usize)),
            call_span,
            Mutability::Mut,
        );
        let zero = caller.new_uint_operand(0, UintTy::Usize, call_span);
        stmts.push(Statement {
            kind: StatementKind::Assign(Place::from(va_cursor_local), Rvalue::Use(zero)),
            span: call_span,
        });

        stmts
    } else if needs_untuple {
        debug!(
            "#1598: Un-tupling args for closure (call site has {} args, callee expects {})",
            call_args.len(),
            arg_count
        );

        let mut stmts = Vec::new();

        // First arg (index 0): closure environment/self
        if let Some(env_arg) = call_args.first() {
            let callee_arg_local = 1; // local 1 = self
            let caller_arg_local = local_map[&callee_arg_local];
            let rvalue = match env_arg {
                Operand::Copy(place) => Rvalue::Use(Operand::Copy(place.clone())),
                Operand::Move(place) => Rvalue::Use(Operand::Move(place.clone())),
                Operand::Constant(c) => Rvalue::Use(Operand::Constant(c.clone())),
            };
            stmts.push(Statement {
                kind: StatementKind::Assign(Place::from(caller_arg_local), rvalue),
                span: call_span,
            });
        }

        // Remaining args: un-tuple call_args[1] into individual callee arg locals
        // call_args[1] is the args tuple, extract fields for locals 2, 3, ...
        // We know tuple_arg is a place because we checked tuple_arg_is_place above
        let tuple_place = match &call_args[1] {
            Operand::Copy(p) | Operand::Move(p) => p.clone(),
            Operand::Constant(_) => unreachable!("tuple_arg_is_place check ensures this"),
        };

        // Extract each field from the tuple for callee arg locals 2, 3, ...
        // Callee local i corresponds to tuple field (i - 2)
        for callee_arg_idx in 2..=arg_count {
            let field_idx = callee_arg_idx - 2;
            let field_ty =
                monomorphize_ty(tcx, callee_instance, callee.locals()[callee_arg_idx].ty);

            // Create place for tuple field access
            let mut field_projection = tuple_place.projection.clone();
            field_projection.push(ProjectionElem::Field(field_idx, field_ty));
            let field_place = Place { local: tuple_place.local, projection: field_projection };

            let caller_arg_local = local_map[&callee_arg_idx];
            let rvalue = Rvalue::Use(Operand::Copy(field_place));
            stmts.push(Statement {
                kind: StatementKind::Assign(Place::from(caller_arg_local), rvalue),
                span: call_span,
            });
        }

        stmts
    } else if needs_tuple_packing {
        debug!(
            "#1582: Packing {} call args into tuple for closure (callee expects {} args)",
            call_args.len(),
            arg_count
        );

        let mut stmts = Vec::new();

        // First arg (index 0): closure environment/self
        if let Some(env_arg) = call_args.first() {
            let callee_arg_local = 1; // local 1 = self
            let caller_arg_local = local_map[&callee_arg_local];
            let rvalue = match env_arg {
                Operand::Copy(place) => Rvalue::Use(Operand::Copy(place.clone())),
                Operand::Move(place) => Rvalue::Use(Operand::Move(place.clone())),
                Operand::Constant(c) => Rvalue::Use(Operand::Constant(c.clone())),
            };
            stmts.push(Statement {
                kind: StatementKind::Assign(Place::from(caller_arg_local), rvalue),
                span: call_span,
            });
        }

        // Remaining args: pack into tuple for local 2
        let tuple_operands: Vec<Operand> = call_args[1..].to_vec();
        let tuple_rvalue = Rvalue::Aggregate(AggregateKind::Tuple, tuple_operands);
        let callee_arg_local = 2; // local 2 = args tuple
        let caller_arg_local = local_map[&callee_arg_local];
        stmts.push(Statement {
            kind: StatementKind::Assign(Place::from(caller_arg_local), tuple_rvalue),
            span: call_span,
        });

        stmts
    } else {
        // Standard case: map call args 1:1 to callee arg locals
        (0..arg_count)
            .filter_map(|i| {
                let callee_arg_local = i + 1;
                let caller_arg_local = local_map[&callee_arg_local];

                call_args.get(i).map(|arg_operand| {
                    let rvalue = match arg_operand {
                        Operand::Copy(place) => Rvalue::Use(Operand::Copy(place.clone())),
                        Operand::Move(place) => Rvalue::Use(Operand::Move(place.clone())),
                        Operand::Constant(c) => Rvalue::Use(Operand::Constant(c.clone())),
                    };
                    Statement {
                        kind: StatementKind::Assign(Place::from(caller_arg_local), rvalue),
                        span: call_span,
                    }
                })
            })
            .collect()
    };

    // Clone callee blocks with remapped locals and block indices
    let callee_blocks = &callee.blocks;
    let caller_blocks_base = caller.num_blocks();

    // For projected destinations, we need to create a post_return_bb that:
    // 1. Assigns call_dest = move ret_tmp
    // 2. Goes to call_target
    // Return terminators in inlined code will go to post_return_bb instead of call_target.
    let return_target: Option<BasicBlockIdx> = if has_projection {
        // post_return_bb will be added after all inlined blocks
        // Its index is: caller_blocks_base + callee_blocks.len()
        Some(caller_blocks_base + callee_blocks.len())
    } else {
        call_target
    };

    let block_map = |callee_bb: BasicBlockIdx| -> BasicBlockIdx { caller_blocks_base + callee_bb };
    let remap_ty = |ty| monomorphize_ty(tcx, callee_instance, ty);

    let mut new_blocks: Vec<BasicBlock> = Vec::with_capacity(callee_blocks.len());
    for callee_block in callee_blocks {
        let new_block =
            remap_block_with_ty(callee_block, &local_map, &block_map, return_target, &remap_ty);
        new_blocks.push(new_block);
    }

    // Specialized variadic fetches: `dest = actual[cursor]; cursor += 1`,
    // guarded by the `cursor < N` UB obligation. Emitted here so the extra
    // blocks land after every block this inline already reserved.
    let va_extra_blocks: Vec<BasicBlock> = if let Some(plan) = &variadic_plan {
        let first_extra_bb =
            caller_blocks_base + callee_blocks.len() + usize::from(ret_tmp.is_some());
        variadic::rewrite_fetch_terminators(
            caller,
            &mut new_blocks,
            plan,
            &va_actual_locals,
            va_cursor_local,
            first_extra_bb,
            call_span,
        )
    } else {
        Vec::new()
    };

    // Replace the Call terminator with Goto to inlined entry
    let call_block = caller.block_mut(call_bb_idx);
    for stmt in init_stmts {
        call_block.statements.push(stmt);
    }

    let inlined_entry = caller_blocks_base;
    call_block.terminator =
        Terminator { kind: TerminatorKind::Goto { target: inlined_entry }, span: call_span };

    // Add all inlined blocks to caller
    for new_block in new_blocks {
        caller.push_block(new_block);
    }

    // For projected destinations, add post_return_bb that copies ret_tmp to call_dest
    if let Some(ret_tmp_local) = ret_tmp {
        // Create statement: call_dest = move ret_tmp
        let assign_stmt = Statement {
            kind: StatementKind::Assign(
                call_dest.clone(),
                Rvalue::Use(Operand::Move(Place::from(ret_tmp_local))),
            ),
            span: call_span,
        };

        // Create terminator: goto call_target (or Unreachable if no target)
        let post_return_terminator = if let Some(target) = call_target {
            Terminator { kind: TerminatorKind::Goto { target }, span: call_span }
        } else {
            Terminator { kind: TerminatorKind::Unreachable, span: call_span }
        };

        let post_return_bb =
            BasicBlock { statements: vec![assign_stmt], terminator: post_return_terminator };

        caller.push_block(post_return_bb);

        // callee_locals.len() - 1 (non-return locals) + 1 (ret_tmp) = callee_locals.len()
        let added_locals = callee_locals.len();
        debug!(
            "inline_function: added {} blocks + post_return_bb, {} locals (projected dest)",
            callee_blocks.len(),
            added_locals,
        );
    } else {
        // -1 because return local 0 maps to existing call_dest.local
        let added_locals = if callee_locals.is_empty() { 0 } else { callee_locals.len() - 1 };
        debug!("inline_function: added {} blocks, {} locals", callee_blocks.len(), added_locals,);
    }

    for extra_block in va_extra_blocks {
        caller.push_block(extra_block);
    }

    // Report the actual-argument count when a specialized fetch can run inside
    // a loop: the (N+1)-th `va_arg` is UB and its bounds assert fails, so no
    // non-failing execution reaches the loop body more than N times. That is a
    // real, construct-derived unwind bound the CHC lane can use.
    variadic_plan.filter(|plan| !plan.fetch_bbs.is_empty()).map(|plan| plan.actual_tys.len())
}

/// Resolve Drop terminators in the body. Part of #3039.
///
/// For each `TerminatorKind::Drop`:
/// - If the drop shim is empty (type has no `Drop` impl): replace with `Goto`
/// - If the drop shim has a body: inline the shim body
///
/// Returns `true` if any changes were made.
pub(super) fn resolve_drop_terminators<F>(
    tcx: TyCtxt<'_>,
    mutable_body: &mut MutableBody,
    instance: &Instance,
    body_provider: &mut F,
    max_drops: usize,
    drops_resolved: &mut usize,
) -> bool
where
    F: FnMut(Instance) -> Option<Body>,
{
    // Collect Drop terminator info (clone what we need to avoid borrow conflicts).
    let drop_sites: Vec<(usize, Place, BasicBlockIdx)> = mutable_body
        .blocks()
        .iter()
        .enumerate()
        .filter_map(|(idx, block)| {
            if let TerminatorKind::Drop { place, target, .. } = &block.terminator.kind {
                Some((idx, place.clone(), *target))
            } else {
                None
            }
        })
        .collect();

    if drop_sites.is_empty() {
        return false;
    }

    let mut changed = false;

    // Process in reverse order to avoid index invalidation when pushing blocks.
    for (drop_bb_idx, drop_place, target) in drop_sites.into_iter().rev() {
        if *drops_resolved >= max_drops {
            break;
        }

        // Resolve the type of the dropped place.
        let drop_ty = match drop_place.ty(mutable_body.locals()) {
            Ok(ty) => ty,
            Err(_) => continue,
        };

        // Part of #4067: Preserve Arc/Rc/Mutex/RwLock Drop terminators for CHC handlers.
        if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _)) =
            drop_ty.kind()
            && matches!(def.trimmed_name().as_str(), "Arc" | "Rc" | "Mutex" | "RwLock")
        {
            debug!("resolve_drop: SKIP ({} — CHC handler) bb{}", def.trimmed_name(), drop_bb_idx);
            continue;
        }

        // Inline owning containers (ArrayVec/SmallVec) whose Drop only drops their
        // `len` initialized elements: when the ELEMENT type is trivially-droppable
        // (its own drop shim is EMPTY), the whole container Drop is a no-op on a
        // dying value — replace it with a Goto instead of inlining the element-drop
        // loop (e.g. `ArrayVec::clear`'s non-DAG `MaybeUninit` loop), which the BMC
        // mini-inliner cannot model and which otherwise forces an unsound
        // "Call terminator" fallback that demotes the whole proof. SOUND: gated on
        // the element's empty drop shim, so a container of `Drop`-having elements is
        // NOT skipped (it falls through to normal inlining). These are INLINE buffers
        // (no heap alloc), so there is not even a dealloc to model. (aterm's Parser
        // holds inline ArrayVec<u16>/ArrayVec<u8> param buffers.)
        if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, args)) =
            drop_ty.kind()
            && matches!(def.trimmed_name().as_str(), "ArrayVec" | "ArrayVecImpl" | "SmallVec")
            && let Some(rustc_public::ty::GenericArgKind::Type(elem_ty)) = args.0.first()
            && Instance::resolve_drop_in_place(*elem_ty).is_empty_shim()
        {
            let span = mutable_body.blocks()[drop_bb_idx].terminator.span;
            mutable_body.block_mut(drop_bb_idx).terminator =
                Terminator { kind: TerminatorKind::Goto { target }, span };
            debug!(
                "resolve_drop: bb{} benign inline container {} (empty-drop elem) → Goto bb{}",
                drop_bb_idx,
                def.trimmed_name(),
                target,
            );
            changed = true;
            continue;
        }

        // Resolve the drop shim instance.
        let drop_instance = Instance::resolve_drop_in_place(drop_ty);

        // Empty drop shim → replace with Goto (no drop glue needed).
        if drop_instance.is_empty_shim() {
            let span = mutable_body.blocks()[drop_bb_idx].terminator.span;
            mutable_body.block_mut(drop_bb_idx).terminator =
                Terminator { kind: TerminatorKind::Goto { target }, span };
            debug!(
                "resolve_drop: bb{} empty shim for {} → Goto bb{}",
                drop_bb_idx,
                drop_instance.name(),
                target,
            );
            changed = true;
            continue;
        }

        // Self-recursion guard.
        if drop_instance.def.def_id() == instance.def.def_id() {
            debug!("resolve_drop: SKIP (self-recursion) bb{}", drop_bb_idx);
            continue;
        }

        // Get the drop shim body.
        let callee_body = match body_provider(drop_instance) {
            Some(body) => body,
            None => {
                debug!(
                    "resolve_drop: SKIP (no body) bb{} for {}",
                    drop_bb_idx,
                    drop_instance.name(),
                );
                continue;
            }
        };

        debug!(
            "resolve_drop: inlining drop shim at bb{} for {} ({} blocks)",
            drop_bb_idx,
            drop_instance.name(),
            callee_body.blocks.len(),
        );

        inline_drop_shim(
            tcx,
            drop_instance,
            mutable_body,
            drop_bb_idx,
            &callee_body,
            &drop_place,
            target,
        );

        changed = true;
        *drops_resolved += 1;
    }

    changed
}

/// Inline a drop shim body at a `Drop` terminator site. Part of #3039.
///
/// The drop shim takes `*mut T` (local 1) and returns `()` (local 0).
/// Internal `Call` terminators are picked up by call inlining in later iterations.
fn inline_drop_shim(
    tcx: TyCtxt<'_>,
    callee_instance: Instance,
    caller: &mut MutableBody,
    drop_bb_idx: BasicBlockIdx,
    callee: &Body,
    drop_place: &Place,
    target: BasicBlockIdx,
) {
    let callee_locals = callee.locals();
    if callee_locals.is_empty() {
        debug!("inline_drop_shim: callee has no locals, skipping");
        return;
    }

    let drop_span = caller.blocks()[drop_bb_idx].terminator.span;

    // Build local map: callee local → caller local.
    let mut local_map: HashMap<Local, Local> = HashMap::new();

    // Local 0 (return place): create fresh () local (drop returns unit).
    let unit_local = caller.new_local(Ty::new_tuple(&[]), drop_span, Mutability::Not);
    local_map.insert(0, unit_local);

    // Local 1 (parameter *mut T): create a new local for the raw pointer.
    // Use the shim's declared parameter type for correctness.
    if callee_locals.len() > 1 {
        let ptr_ty = monomorphize_ty(tcx, callee_instance, callee_locals[1].ty);
        let ptr_local = caller.new_local(ptr_ty, drop_span, Mutability::Mut);
        local_map.insert(1, ptr_local);
    }

    // Remaining callee locals → fresh caller locals.
    for (i, decl) in callee_locals.iter().enumerate() {
        if i <= 1 {
            continue; // already mapped
        }
        let new_local = caller.new_local(
            monomorphize_ty(tcx, callee_instance, decl.ty),
            decl.span,
            decl.mutability,
        );
        local_map.insert(i, new_local);
    }

    // Create the initialization statement: ptr_local = &raw mut drop_place.
    // This gives the shim a raw pointer to the value being dropped.
    let init_stmt = local_map.get(&1).map(|&ptr_local| Statement {
        kind: StatementKind::Assign(
            Place::from(ptr_local),
            Rvalue::AddressOf(RawPtrKind::Mut, drop_place.clone()),
        ),
        span: drop_span,
    });

    // Remap callee blocks: offset all block indices by the current block count.
    let caller_blocks_base = caller.num_blocks();
    let block_map = |callee_bb: BasicBlockIdx| -> BasicBlockIdx { caller_blocks_base + callee_bb };
    let remap_ty = |ty| monomorphize_ty(tcx, callee_instance, ty);

    // Shim's Return terminators become Goto to the original drop target.
    let return_target: Option<BasicBlockIdx> = Some(target);

    let mut new_blocks: Vec<BasicBlock> = Vec::with_capacity(callee.blocks.len());
    for callee_block in &callee.blocks {
        let new_block =
            remap_block_with_ty(callee_block, &local_map, &block_map, return_target, &remap_ty);
        new_blocks.push(new_block);
    }

    // Replace the Drop terminator: add init stmt + Goto to shim entry.
    let call_block = caller.block_mut(drop_bb_idx);
    if let Some(stmt) = init_stmt {
        call_block.statements.push(stmt);
    }

    let inlined_entry = caller_blocks_base;
    call_block.terminator =
        Terminator { kind: TerminatorKind::Goto { target: inlined_entry }, span: drop_span };

    // Add all inlined blocks to caller.
    for new_block in new_blocks {
        caller.push_block(new_block);
    }

    let added_locals = callee_locals.len(); // includes mapped locals
    debug!(
        "inline_drop_shim: added {} blocks at offset {}, {} locals for bb{}",
        callee.blocks.len(),
        caller_blocks_base,
        added_locals,
        drop_bb_idx,
    );
}
