// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06: modifies frame-condition instrumentation for contract CHECK mode.
//!
//! In check mode the contract macro wraps the original function body in a
//! "modifies wrapper" closure that receives `_wrapper_arg` — a tuple of
//! `*const T` pointers derived from the `#[kani::modifies(...)]` clause.
//! Upstream Kani hands that tuple to CBMC as a DFCC assigns clause; the AY
//! backends have no CBMC, so this module instruments the wrapper body at the
//! MIR level instead:
//!
//! * `kani::internal::modifies_frame_enter(_wrapper_arg)` at body entry, and
//! * `kani::internal::modifies_frame_exit()` right before every `Return`.
//!
//! Both markers survive `FunctionInlinePass` (fn_marker'd functions are never
//! inlined), so after the wrapper body — and everything it calls — is inlined
//! into the harness, the marker calls delimit exactly the dynamic extent of
//! the checked function. The CHC backend lowers them into a ghost
//! "frame active" flag plus footprint registers and checks every memory store
//! executed while the flag is set (see `codegen_ay::chc`).

use crate::kani_middle::attributes::ContractAttributes;
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Mutability, Operand, Place, TerminatorKind, VarDebugInfoContents};
use rustc_public::ty::{
    ClosureDef, ClosureKind, FnDef, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind,
};
use tracing::debug;

/// Find a closure declared in `body` by its debug name, returning both the
/// closure definition and its generic arguments (needed to resolve its own
/// body). Unlike `contracts::find_closure` this is a soft lookup.
fn find_closure_with_args(body: &Body, name: &str) -> Option<(ClosureDef, GenericArgs)> {
    body.var_debug_info.iter().find_map(|var_info| {
        if var_info.name.as_str() == name {
            let ty = match &var_info.value {
                VarDebugInfoContents::Place(place) => place.ty(body.locals()).ok()?,
                VarDebugInfoContents::Const(const_op) => const_op.ty(),
            };
            if let TyKind::RigidTy(RigidTy::Closure(def, args)) = ty.kind() {
                return Some((def, args));
            }
        }
        None
    })
}

/// Resolve a closure's MIR body from its definition and generic args.
fn closure_body(def: ClosureDef, args: &GenericArgs) -> Option<Body> {
    let instance = Instance::resolve_closure(def, args, ClosureKind::FnOnce).ok()?;
    instance.body()
}

/// Resolve the modifies-wrapper closure of a contract-annotated function that
/// is being verified in (recursive) check mode.
///
/// The wrapper is not declared in the function body itself: it is nested
/// inside the check closure (which, for recursive checks, is itself nested
/// inside the recursion-check closure). Walk that nesting via debug names.
pub(super) fn resolve_modifies_wrapper(
    _tcx: TyCtxt,
    fn_def: FnDef,
    fn_body: &Body,
    contract: &ContractAttributes,
    recursive: bool,
) -> Option<ClosureDef> {
    let check_body = if recursive {
        let (rec_def, rec_args) =
            find_closure_with_args(fn_body, contract.recursion_check.as_str())?;
        let rec_body = closure_body(rec_def, &rec_args)?;
        let (check_def, check_args) =
            find_closure_with_args(&rec_body, contract.checked_with.as_str())?;
        closure_body(check_def, &check_args)?
    } else {
        let (check_def, check_args) =
            find_closure_with_args(fn_body, contract.checked_with.as_str())?;
        closure_body(check_def, &check_args)?
    };
    let wrapper =
        find_closure_with_args(&check_body, contract.modifies_wrapper.as_str()).map(|(def, _)| def);
    if wrapper.is_none() {
        debug!(
            function = fn_def.name(),
            wrapper_name = contract.modifies_wrapper.as_str(),
            "FC-06: failed to resolve modifies wrapper closure"
        );
    }
    wrapper
}

/// Instrument the modifies-wrapper closure body with frame markers.
///
/// Inserts `modifies_frame_enter(_wrapper_arg)` at body entry and
/// `modifies_frame_exit()` immediately before every `Return` terminator.
pub(super) fn instrument_wrapper_body(enter_fn: FnDef, exit_fn: FnDef, body: Body) -> (bool, Body) {
    // Closure signature is `|env, _wrapper_arg: (...)| -> T`:
    // local 0 = return place, locals 1..=arg_count = args, last arg = tuple.
    let arg_count = body.arg_locals().len();
    if arg_count == 0 {
        debug!("FC-06: wrapper closure has no arguments; skipping instrumentation");
        return (false, body);
    }
    let wrapper_arg_local = arg_count;
    let tuple_ty = body.locals()[wrapper_arg_local].ty;
    let Ok(enter_instance) =
        Instance::resolve(enter_fn, &GenericArgs(vec![GenericArgKind::Type(tuple_ty)]))
    else {
        debug!("FC-06: failed to resolve modifies_frame_enter; skipping instrumentation");
        return (false, body);
    };
    let Ok(exit_instance) = Instance::resolve(exit_fn, &GenericArgs(vec![])) else {
        debug!("FC-06: failed to resolve modifies_frame_exit; skipping instrumentation");
        return (false, body);
    };

    let mut new_body = MutableBody::from(body);

    // Insert `modifies_frame_exit()` before every Return terminator first;
    // splitting moves each Return into a freshly appended block, so snapshot
    // the Return block indices up front (appends never renumber them).
    let return_bbs: Vec<usize> = new_body
        .blocks()
        .iter()
        .enumerate()
        .filter_map(|(idx, bb)| matches!(bb.terminator.kind, TerminatorKind::Return).then_some(idx))
        .collect();
    for bb in return_bbs {
        let mut source = SourceInstruction::Terminator { bb };
        let span = source.span(new_body.blocks());
        let ret_place = Place {
            local: new_body.new_local(Ty::new_tuple(&[]), span, Mutability::Not),
            projection: vec![],
        };
        new_body.insert_call(
            &exit_instance,
            &mut source,
            InsertPosition::Before,
            vec![],
            ret_place,
        );
    }

    // Insert `modifies_frame_enter(_wrapper_arg)` at body entry.
    let mut source = if new_body.blocks()[0].statements.is_empty() {
        SourceInstruction::Terminator { bb: 0 }
    } else {
        SourceInstruction::Statement { idx: 0, bb: 0 }
    };
    let span = source.span(new_body.blocks());
    let ret_place = Place {
        local: new_body.new_local(Ty::new_tuple(&[]), span, Mutability::Not),
        projection: vec![],
    };
    new_body.insert_call(
        &enter_instance,
        &mut source,
        InsertPosition::Before,
        vec![Operand::Copy(Place { local: wrapper_arg_local, projection: vec![] })],
        ret_place,
    );

    debug!("FC-06: instrumented modifies wrapper body with frame markers");
    (true, new_body.into())
}
