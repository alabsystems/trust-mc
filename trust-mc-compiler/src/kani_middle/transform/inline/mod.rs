// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! MIR transformation pass for function inlining.
//!
//! This pass inlines simple, non-recursive function calls to enable
//! BMC verification in backends that don't support function calls
//! (like the AY backend).
//!
//! Part of #217
//!
//! # Design
//!
//! ## What Gets Inlined
//!
//! - Functions with bodies (not intrinsics)
//! - Non-recursive functions (no self-calls in call graph)
//! - Non-kani intrinsics (those are handled specially)
//! - Closures (FnOnce/FnMut/Fn) via CallableKind enum (#1575)
//!
//! ## Algorithm
//!
//! 1. Find Call terminators in the body
//! 2. Resolve the callee instance
//! 3. Check if callee should be inlined
//! 4. If yes:
//!    a. Clone callee body
//!    b. Prefix all callee locals with unique suffix
//!    c. Replace callee params with caller args
//!    d. Replace callee returns with gotos to target
//!    e. Insert cloned blocks into caller
//! 5. Iterate until no more calls or max depth reached
//!
//! ## Limitations
//!
//! - Max inline depth to prevent explosion
//! - Recursive functions not inlined
//! - Closures supported via CallableKind enum (#1575)

mod body_inline;
pub(crate) mod devirtualize;
mod handler_boundaries;
mod remap;
#[cfg(test)]
mod stable_atomic_tests;
mod variadic;

#[cfg(test)]
mod tests;

use super::TransformPass;
use crate::kani_middle::attributes;
use crate::kani_middle::transform::TransformationType;
use crate::kani_middle::transform::body::MutableBody;
use crate::kani_queries::QueryDb;
use body_inline::{inline_function, resolve_drop_terminators};
use devirtualize::{try_devirtualize, try_devirtualize_via_receiver};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, Mutability, Operand, StatementKind, TerminatorKind};
use rustc_public::ty::{
    AdtKind, ClosureDef, ClosureKind, FnDef, GenericArgKind, GenericArgs, RigidTy, TyKind,
};
use std::sync::OnceLock;
use tracing::{debug, warn};
use trust_mc_codegen_stubs::{StubKind, StubRegistry};

/// Represents either a regular function or a closure for inlining purposes.
///
/// Part of #1575 closure inlining support.
#[derive(Debug, Clone)]
enum CallableKind {
    FnDef(FnDef),
    Closure(ClosureDef, ClosureKind),
}

/// Configuration for function inlining.
#[derive(Debug, Clone)]
pub(crate) struct InlineConfig {
    /// Maximum depth of inlining (to prevent infinite expansion).
    pub max_depth: usize,
    /// Whether inlining is enabled.
    pub enabled: bool,
    /// Keep every `block_on` call as a call boundary.
    ///
    /// The CHC lane needs the boundary: its `try_dispatch_call_block_on`
    /// specializer rewrites the busy-poll loop into a single-poll `Ready` path,
    /// and MIR-inlining the body first would leave it an unbounded self-loop
    /// around `poll` that CHC cannot encode (#3955, #3988).
    ///
    /// The BMC lane has NO `block_on` handler at all. Preserving the boundary
    /// there hands the call to the statement mini-inliner, which admits only
    /// acyclic bodies — and `kani::block_on` IS a loop — so every `async fn`
    /// harness bailed as an unsupported `Call terminator` with zero
    /// obligations. Set to `false` for BMC: the poll loop is then an ordinary
    /// loop of the harness body and the unroller cuts it under the unwind
    /// bound with a loud unwinding assertion (`Poll::Pending` on the last
    /// permitted poll FAILS; it is never silently pruned).
    pub preserve_block_on: bool,
}

impl Default for InlineConfig {
    fn default() -> Self {
        InlineConfig { max_depth: 10, enabled: true, preserve_block_on: true }
    }
}

/// Inline depth to use once a contract-instrumentation chain is detected in the
/// working body. The contract indirection (`run_contract_fn` -> closure ->
/// real body) consumes ~10-20 inline steps of budget before the REAL callee is
/// even reached, so a plain proof that transitively reaches a contract needs a
/// higher ceiling than the default just to get PAST the closure machinery to the
/// callee. Matches the static boost `codegen_function` applies for the direct /
/// stubbing cases. SOUND: deeper inlining only eliminates `Call terminator`s; it
/// never changes semantics. Bounded (not unlimited) as a BMC state-explosion
/// backstop; recursive callees are already skipped by the inliner. (Note: a
/// callee whose OWN body is a whole large state machine — e.g. a terminal
/// parser's byte dispatch — is not made tractable by inlining depth alone; the
/// resulting BMC formula can exceed the solver's capacity regardless.)
const CONTRACT_INLINE_DEPTH: usize = 32;

/// Absolute ceiling on the contract headroom granted by
/// [`body_has_contract_glue_call`]. The headroom is re-granted every time
/// another layer of glue is UNCOVERED, which is what a chain of contract-carrying
/// callees needs, so this is the only thing standing between a pathological
/// program and unbounded inlining. Deliberately far above what real chains need
/// (a three-deep `proof_for_contract` chain measures ~120) and far below
/// anything that could plausibly be inlined by accident.
const MAX_CONTRACT_INLINE_DEPTH: usize = 512;

/// Does the (working) body still contain a call to Kani contract GLUE —
/// `kani_contract_mode`, `kani_force_fn_once[_with_args]` or
/// `kani_register_contract`?
///
/// # Why this earns its own budget
///
/// These four are not user code and carry no user state: `kani_contract_mode`
/// is a constant, `kani_force_fn_once[_with_args]` is literally `fn(f: F) -> F
/// { f }`, and `kani_register_contract` is rewritten to `run_contract_fn`,
/// a single tail call of the closure it was handed
/// (`library/kani_macros/src/sysroot/contracts/mod.rs`). Inlining them is a
/// constant-fold / identity / tail-call rewrite that hands the backend the
/// contract frame as ORDINARY MIR — which is the only shape in which the
/// backend models it faithfully.
///
/// Leaving one behind is not a neutral loss of precision. A surviving
/// `kani_register_contract` sends the whole contract frame down the CHC
/// walker's closure-capture path, where the four parts of a contract stop
/// agreeing with each other: the precondition read, the `old(..)` history
/// snapshot, the body's write-back and the ensures read each end up resolved
/// against a different copy of the modified place, so a SAFE program reports a
/// counterexample (`function-contract/as-assertions/precedence.rs`,
/// `function-contract/history/stub.rs`).
///
/// A two-level `proof_for_contract` chain needs ~50 inline steps and a
/// three-level one ~120, so the flat [`CONTRACT_INLINE_DEPTH`] ceiling ran out
/// mid-chain. Each glue layer only becomes visible once the layer above it is
/// inlined, so the budget is re-granted whenever glue is still pending, bounded
/// by [`MAX_CONTRACT_INLINE_DEPTH`].
///
/// Deliberately NARROWER than [`body_has_contract_chain`]: the Fn-trait call
/// shims that predicate also accepts are emitted by ordinary closure code, so
/// granting repeated headroom on them would let any closure-heavy body inline
/// without limit. Only the four compiler-generated contract markers do.
fn body_has_contract_glue_call(body: &MutableBody) -> bool {
    body.blocks().iter().any(|bb| {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            return false;
        };
        matches!(
            attributes::fn_marker(fn_def).as_deref(),
            Some(
                "kani_contract_mode"
                    | "kani_force_fn_once"
                    | "kani_force_fn_once_with_args"
                    | "kani_register_contract"
            )
        )
    })
}

/// Does the (working) body still contain a Kani contract-instrumentation chain
/// (`run_contract_fn`/closure-shim/contract-marker calls)?
///
/// The static depth boost in `codegen_function` only scans the harness's DIRECT
/// body, so a plain `#[kani::proof]` that reaches a contract-annotated fn only
/// TRANSITIVELY (e.g. aterm's `state_always_valid` -> `advance` -> `process_byte`
/// -> contract-carrying `process_byte_inner`) keeps the low default depth, and
/// the contract's inner call (`process_byte_dispatch`) leaks as an unsupported
/// `Call terminator` + #3017 variant-0 fallback. Detecting the chain in the
/// WORKING body — after inlining has exposed it — lets the fixpoint loop raise
/// the cap dynamically. SOUND: deeper inlining only eliminates Call terminators;
/// it never changes semantics.
fn body_has_contract_chain(body: &MutableBody) -> bool {
    for bb in body.blocks() {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            continue;
        };
        let fn_name = fn_def.0.name();
        if fn_name.contains("FnOnce::call_once")
            || fn_name.contains("FnMut::call_mut")
            || fn_name.contains("::Fn::call")
        {
            return true;
        }
        if let Some(marker) = attributes::fn_marker(fn_def)
            && matches!(
                marker.as_str(),
                "kani_contract_mode"
                    | "kani_force_fn_once"
                    | "kani_force_fn_once_with_args"
                    | "kani_register_contract"
            )
        {
            return true;
        }
    }
    false
}

/// Is this body a no-op / trivial shim — a single block that just returns, touching
/// only its own locals? Used to force-inline provably-empty concrete-impl callees
/// (e.g. a test sink's empty trait-method bodies) PAST the inline depth limit.
///
/// Inlining such a body is a pure `Call` -> `Goto` rewrite: it adds no basic blocks,
/// mutates no memory (only bare-local assigns like `_0 = ()` are allowed — any
/// Deref/Field-projected place, or any non-Return terminator / Call / Drop / Assert,
/// disqualifies it), and changes no behavior. So bypassing the depth cap for it can
/// never cause BMC state explosion and is strictly safer than leaving an unsupported
/// `Call terminator` that forces the #3017 variant-0 fallback. Conservative by
/// construction: anything with real statements or control flow returns false and is
/// left depth-skipped exactly as before.
fn body_is_noop_shim(body: &Body) -> bool {
    if body.blocks.len() != 1 {
        return false;
    }
    let bb = &body.blocks[0];
    if !matches!(bb.terminator.kind, TerminatorKind::Return) {
        return false;
    }
    bb.statements.iter().all(|s| match &s.kind {
        StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => true,
        // Bare-local assigns only (e.g. the implicit `_0 = ()` return of an empty fn).
        // A projected place (Deref/Field) would be a memory write — reject.
        StatementKind::Assign(place, _) => place.projection.is_empty(),
        _ => false,
    })
}

/// Function inlining transformation pass.
#[derive(Debug, Default, Clone)]
pub(crate) struct FunctionInlinePass {
    config: InlineConfig,
    /// Largest actual-argument count over the `c_variadic` calls this pass
    /// specialized whose `va_arg` fetches survive into the caller body.
    ///
    /// A fetch past the end of that list is UB and its bounds assert fails, so
    /// no non-failing execution can run a fetching loop body more than that many
    /// times. `codegen_function` reads it as a construct-derived unwind bound.
    variadic_actual_bound: Option<usize>,
}

impl FunctionInlinePass {
    /// Create a new inline pass with the given configuration.
    pub(crate) fn new(config: InlineConfig) -> Self {
        FunctionInlinePass { config, variadic_actual_bound: None }
    }

    /// Find all Call terminators in a MutableBody that should be inlined.
    fn find_calls_to_inline_mutable(&self, body: &MutableBody) -> Vec<usize> {
        let mut call_sites = Vec::new();
        for (idx, block) in body.blocks().iter().enumerate() {
            if let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind {
                // Note: Projected destinations (e.g., _3.0 = foo()) are now handled
                // correctly via ret_tmp + post_return_bb. See #225 and Phase 4 M1.
                if !destination.projection.is_empty() {
                    debug!(
                        "FunctionInlinePass: call with projected destination at bb{} (will use ret_tmp)",
                        idx
                    );
                }
                if self.should_inline_mutable(func, body) {
                    call_sites.push(idx);
                }
            }
        }
        call_sites
    }

    /// Check if a function name is one of the closure call shims (FnOnce/FnMut/Fn).
    fn is_closure_call_shim(fn_name: &str) -> bool {
        (fn_name.contains("FnOnce") && fn_name.contains("call_once"))
            || (fn_name.contains("FnMut") && fn_name.contains("call_mut"))
            || (fn_name.contains("::Fn") && fn_name.contains("::call"))
    }

    fn closure_kind_from_shim(fn_name: &str) -> ClosureKind {
        if fn_name.contains("FnOnce") && fn_name.contains("call_once") {
            ClosureKind::FnOnce
        } else if fn_name.contains("FnMut") && fn_name.contains("call_mut") {
            ClosureKind::FnMut
        } else {
            ClosureKind::Fn
        }
    }

    /// Extract closure definition + args from the first call argument.
    fn closure_info_from_arg(
        arg: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> Option<(ClosureDef, rustc_public::ty::GenericArgs)> {
        let arg_ty = arg.ty(locals).ok()?;
        match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, fn_args)) => Some((def, fn_args)),
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => match inner.kind() {
                TyKind::RigidTy(RigidTy::Closure(def, fn_args)) => Some((def, fn_args)),
                _ => None, // external enum: TyKind
            },
            _ => None, // external enum: TyKind
        }
    }

    /// Check if a function call should be inlined (MutableBody variant).
    ///
    /// Handles both FnDef (regular functions) and Closure types (#1575).
    fn should_inline_mutable(&self, func: &Operand, body: &MutableBody) -> bool {
        // Get the function type
        let func_ty: rustc_public::ty::Ty = match func.ty(body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };

        // Accept FnDef or Closure types (#1575)
        let (fn_name, fn_def_for_resolve, fn_args_for_resolve) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(fn_def, fn_args)) => {
                // Don't inline kani functions that have marker attributes (hooks,
                // intrinsics, models) — the AY codegen has special handlers for
                // these. kani::mem:: predicates (can_dereference, can_read_unaligned,
                // etc.) are also blocked — see has_special_codegen_handler.
                // Part of #1229, #3470.
                //
                // Part of #3207: Also inline AnyModel (kani::any<T>()) so that
                // custom Arbitrary impls with kani::assume() constraints are
                // resolved at the MIR level. Without this, CHC codegen intercepts
                // AnyModel and produces fully unconstrained values, bypassing
                // the Arbitrary impl's constraint logic.
                if let Some(marker) = attributes::fn_marker(fn_def) {
                    let marker = marker.as_str();
                    if marker == "AnyModel"
                        && handler_boundaries::any_model_raw_compatible_array(&fn_args)
                    {
                        debug!(
                            "Not inlining kani AnyModel raw-compatible array: {}",
                            fn_def.0.name()
                        );
                        return false;
                    }
                    if marker == "AnyModel" && handler_boundaries::any_model_char(&fn_args) {
                        debug!("Not inlining kani AnyModel char: {}", fn_def.0.name());
                        return false;
                    }
                    if marker == "AnyModel" && handler_boundaries::any_model_nonzero(&fn_args) {
                        debug!("Not inlining kani AnyModel NonZero: {}", fn_def.0.name());
                        return false;
                    }
                    let should_inline = matches!(
                        marker,
                        "kani_contract_mode"
                            | "kani_force_fn_once"
                            | "kani_force_fn_once_with_args"
                            | "kani_register_contract"
                            | "AnyModel"
                    );
                    if !should_inline {
                        debug!(
                            "Not inlining kani function with marker {}: {}",
                            marker,
                            fn_def.0.name()
                        );
                        return false;
                    }
                    debug!("Inlining kani marker {}: {}", marker, fn_def.0.name());
                }
                (fn_def.0.name(), Some(fn_def), Some(fn_args))
            }
            TyKind::RigidTy(RigidTy::Closure(closure_def, _args)) => {
                // Closures have compiler-generated names like "{closure#0}"
                let name = closure_def.0.name();
                debug!("Closure candidate for inlining: {}", name);
                return true; // Closures don't have special handlers
            }
            _ => return false, // external enum: TyKind
        };

        // `<String as BoundedArbitrary>::bounded_any::<N>` must reach codegen
        // rather than be inlined. Its body runs through `utf8_chunks()` /
        // `Utf8Chunk::valid()`, which codegen abstracts to unconstrained
        // symbolics, so inlining discards the one guarantee the API makes --
        // that the String holds at most N bytes -- and
        // `bounded_any::<String, 4>().len() <= 4` reported FAILED.
        //
        // Match on the GENERIC ARGS, not the name: `fn_def.0.name()` here is the
        // unmonomorphised trait path `kani::BoundedArbitrary::bounded_any`, with
        // no mention of String at all. (The fully-qualified
        // `...<impl BoundedArbitrary for std::string::String>::bounded_any` that
        // shows up in codegen logs is the resolved instance, a different string.)
        if fn_name.ends_with("::bounded_any")
            && fn_args_for_resolve.as_ref().is_some_and(|args| {
                args.0.iter().any(|arg| {
                    matches!(arg, rustc_public::ty::GenericArgKind::Type(t)
                        if matches!(t.kind(),
                            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(def, _))
                            if def.0.name().ends_with("String")))
                })
            })
        {
            debug!("Not inlining bounded_any for String (codegen models the bound)");
            return false;
        }

        // Preserve destructor Calls (`drop_in_place::<T>`) for inline owning
        // containers (ArrayVec/SmallVec) whose ELEMENT type is trivially droppable
        // (empty drop shim). Leaving them as Calls lets the BMC drop-glue intercept
        // skip them as a genuine no-op, instead of inlining the unmodellable
        // element-drop loop (`ArrayVec::clear`'s non-DAG `MaybeUninit` loop) which
        // forces an unsound "Call terminator" fallback that demotes the whole proof.
        // SOUND: gated on the element's empty drop shim, so a container of
        // `Drop`-having elements still inlines (and is modeled/demoted) normally.
        {
            use rustc_public::CrateDef;
            if fn_name.contains("drop_in_place")
                && let Some(fn_args) = fn_args_for_resolve.as_ref()
                && let Some(rustc_public::ty::GenericArgKind::Type(t)) = fn_args.0.first()
                && let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Adt(
                    cdef,
                    cargs,
                )) = t.kind()
                && matches!(cdef.trimmed_name().as_str(), "ArrayVec" | "ArrayVecImpl" | "SmallVec")
                && let Some(rustc_public::ty::GenericArgKind::Type(elem)) = cargs.0.first()
                && rustc_public::mir::mono::Instance::resolve_drop_in_place(*elem).is_empty_shim()
            {
                debug!("Not inlining benign inline-container destructor: {}", fn_name);
                return false;
            }
        }

        // `block_on` is a call boundary ONLY for the CHC single-poll
        // specializer (see `InlineConfig::preserve_block_on`). In BMC the body
        // is inlined like any other user function so its busy-poll loop reaches
        // the harness-level unroller instead of the DAG-only mini-inliner.
        if Self::is_block_on_path(&fn_name) {
            if self.config.preserve_block_on {
                debug!("Not inlining block_on (CHC specializer boundary): {}", fn_name);
                return false;
            }
            debug!("Inlining block_on (BMC: poll loop unrolled under the unwind bound): {}", fn_name);
        }

        // Don't inline functions with special codegen handlers (#274)
        // These are handled in try_codegen_std_intrinsic and need to
        // be visible as function calls, not inlined match arms.
        if Self::has_special_codegen_handler(&fn_name) {
            debug!("Not inlining function with special handler: {}", fn_name);
            return false;
        }

        // For trait method calls like From::from, the def-path name is generic
        // (e.g. "std::convert::From::from") and doesn't reveal the impl type.
        // Resolve the instance to get the impl-specific path and check if the
        // stub registry would handle it. (#3679)
        if let (Some(fn_def), Some(fn_args)) = (fn_def_for_resolve, fn_args_for_resolve) {
            if Self::has_stubbed_trait_impl(&fn_name, fn_def, &fn_args) {
                debug!("Not inlining trait method with stubbed impl: {}", fn_name);
                return false;
            }
            // Rc::clone / Arc::clone — preserve for CHC clone dispatch (Part of #3978).
            // At the MIR def-path level, Rc::clone appears as `std::clone::Clone::clone`.
            // Resolve the instance to get the impl-specific name (e.g.
            // `<Rc<T> as Clone>::clone`) and check for Rc/Arc wrapper mention.
            if Self::is_rc_arc_clone_resolved(fn_def, &fn_args) {
                debug!("Not inlining Rc/Arc clone (resolved): {}", fn_name);
                return false;
            }
            // Part of #4112: Iterator adapter next() — preserve for CHC adapter dispatch.
            // At the MIR def-path level, `<FlatMap<I,U,F> as Iterator>::next` appears as
            // `Iterator::next` (the trait method). The fn_name check in
            // `is_iterator_adapter_next` only matches when the adapter type name
            // (FlatMap, Map, Filter, etc.) appears in the def-path, which it does NOT
            // for trait-dispatched calls. Resolve the instance to get the impl-specific
            // name (e.g., `core::iter::adapters::flatten::FlatMap::<I, U, F>::next`)
            // which DOES contain the adapter type name.
            if fn_name.ends_with("::next") && Self::is_adapter_next_resolved(fn_def, &fn_args) {
                debug!("Not inlining adapter next() (resolved): {}", fn_name);
                return false;
            }
            // Integer Ord::{min,max,clamp} — preserve the call boundary so CHC
            // comparison dispatch can encode signedness directly.
            if Self::is_integer_ord_min_max_clamp_resolved(fn_def, &fn_args) {
                debug!("Not inlining integer Ord min/max/clamp (resolved): {}", fn_name);
                return false;
            }
            // PartialEq::eq/ne on compound types (Option, Result, enums) —
            // preserve for CHC cmp_stub dispatch which handles Datatype equality
            // via structural SMT comparison. If MIR-inlined, the derived
            // PartialEq body expands into 10+ basic blocks with typed memory
            // operations that ay-chc cannot solve (produces UNKNOWN). Primitive
            // type PartialEq (u8, u32, bool, etc.) must still be inlined because
            // Range<u32>::next() uses PartialEq for loop termination, and
            // blocking it breaks CHC loop invariant synthesis.
            if Self::is_compound_partial_eq_resolved(fn_def, &fn_args) {
                debug!("Not inlining compound PartialEq (resolved): {}", fn_name);
                return false;
            }
        }

        // For now, only inline simple user functions
        debug!("Candidate for inlining: {}", fn_name);
        true
    }

    /// Is `fn_name` any `block_on` — `kani::block_on` or a user-defined one?
    ///
    /// Part of #3955, Part of #3988: the CHC specializer validates the
    /// poll→SwitchInt→backedge pattern of whatever body it is handed and falls
    /// through to generic dispatch for non-matching bodies, so the name is the
    /// only gate. `block_on_with_spawn` deliberately does NOT match: it drives
    /// a scheduler, and the CHC lane has its own D3 dispatch for it.
    fn is_block_on_path(fn_name: &str) -> bool {
        fn_name.ends_with("::block_on") || fn_name == "block_on"
    }

    /// Check if a function has special codegen handling in try_codegen_std_intrinsic.
    ///
    /// These functions must not be inlined because the AY codegen has special
    /// handlers for them that produce SMT primitives directly.
    fn has_special_codegen_handler(fn_name: &str) -> bool {
        // Allocator/layout helpers - preserve for stub dispatch (Part of #3841).
        // If fn_inline erases std::alloc::dealloc / Global::deallocate before
        // CHC/BMC codegen sees the Call terminator, heap metadata updates
        // (obj_valid false, obj_size checks) disappear and negative allocator
        // harnesses can flip from CTREX to PROOF.
        if Self::is_alloc_or_layout_stub_boundary(fn_name) {
            debug!("Not inlining alloc/layout stub boundary: {}", fn_name);
            return true;
        }

        // Option methods with special SMT handling
        if fn_name.contains("Option") {
            // is_none, is_some, unwrap, unwrap_or, unwrap_unchecked
            if fn_name.contains("is_none")
                || fn_name.contains("is_some")
                || fn_name.contains("unwrap")
            {
                return true;
            }
        }

        // Checked/wrapping/saturating/overflowing/unchecked arithmetic
        // These are handled as intrinsics with special SMT semantics
        if fn_name.contains("checked_")
            || fn_name.contains("wrapping_")
            || fn_name.contains("saturating_")
            || fn_name.contains("overflowing_")
            || fn_name.contains("unchecked_")
        {
            return true;
        }

        // str::as_ptr / str::as_mut_ptr — preserve the call boundary so the CHC
        // identity route (detect_slice_as_ptr_call) models the result as the
        // receiver's promoted-const split-pointer address WITH its obj_id lane
        // and propagates the const backing + subslice_len metadata. The inlined
        // MIR body extracts the data half through memory ops that lose
        // provenance, so every downstream offset alloc-bound check fail-opens
        // into the OffsetProvenanceUnresolved demotion (false positives on
        // provably-safe str offset harnesses like offset_u8_ok).
        if fn_name.contains("<impl str>")
            && (fn_name.ends_with("::as_ptr") || fn_name.ends_with("::as_mut_ptr"))
        {
            debug!("Not inlining str::as_ptr identity boundary: {}", fn_name);
            return true;
        }

        // Keep canonical Cell accessors visible to the fail-closed CHC
        // quarantine. Deep-inlining currently loses pointer/value provenance;
        // user types with similar names must not inherit this boundary.
        if let Some(suffix) = fn_name
            .strip_prefix("core::cell::Cell")
            .or_else(|| fn_name.strip_prefix("std::cell::Cell"))
            && (suffix.starts_with("::") || suffix.starts_with('<'))
            && !fn_name.ends_with("::new")
        {
            debug!("Not inlining quarantined Cell accessor boundary: {}", fn_name);
            return true;
        }

        // Canonical RefCell replace/replace_with/as_ptr — preserve the call
        // boundary so the CHC semantic lane (codegen_call_cell.rs) models the
        // mutators as a direct load/store at the referent's real
        // (obj_id, offset) address and as_ptr as the referent-address identity
        // (so `*self.as_ptr()` contract reads observe the store — the
        // read-observes-store pairing; without it this would be a vacuous
        // PROOF). Declines fail closed at the CHC quarantine
        // (cell_accessor_semantics_quarantined), never codegen-time
        // deep-inline. Exact canonical matching only: user types whose path
        // merely contains `cell::RefCell` must not inherit this boundary.
        if let Some(suffix) = fn_name
            .strip_prefix("core::cell::RefCell")
            .or_else(|| fn_name.strip_prefix("std::cell::RefCell"))
            && (suffix.starts_with("::") || suffix.starts_with('<'))
            && (fn_name.ends_with("::replace")
                || fn_name.ends_with("::replace_with")
                || fn_name.ends_with("::as_ptr"))
        {
            debug!("Not inlining RefCell semantic-lane boundary: {}", fn_name);
            return true;
        }

        // Power operations — preserve for CHC pow handler (Part of #3402)
        // Plain `pow` is not caught by the `wrapping_` prefix above, but the CHC
        // handler (codegen_call_cmp_string::is_pow_method) handles both `pow` and
        // `wrapping_pow`. Without this, MIR inlines the exp-by-squaring loop body
        // before CHC codegen can intercept the Call terminator.
        if fn_name.ends_with("::pow") {
            return true;
        }

        // Euclidean division/remainder — preserve for CHC euclid handler (Part of #3424)
        // div_euclid/rem_euclid have branching MIR bodies that fn_inline expands into
        // complex CHC rules the solver cannot handle. The CHC handler encodes these
        // directly as ite-guarded bvsdiv/bvsrem (signed) or bvudiv/bvurem (unsigned).
        if fn_name.ends_with("::div_euclid") || fn_name.ends_with("::rem_euclid") {
            return true;
        }

        // HashMap/HashSet/hashbrown - preserve for CHC Array codegen (#798, #788, #3057)
        // Note: This only prevents trust_mc's own inlining pass, not rustc's MIR inlining.
        // For precompiled std, HashMap calls are already inlined before we see them.
        // This handler helps with user code that directly uses hashbrown.
        // Part of #3057: Also block hash_map::/hash_set:: module paths — iterator types
        // (IntoIter, Iter, Keys, Values) live in these modules, not on the HashMap/HashSet
        // type path. Without this, IntoIter::next() gets inlined, exposing hashbrown
        // internals that CHC codegen can't handle.
        if fn_name.contains("hashbrown::")
            || fn_name.contains("HashMap")
            || fn_name.contains("HashSet")
            || fn_name.contains("hash_map::")
            || fn_name.contains("hash_set::")
        {
            return true;
        }

        // TrustMcMap is the verification-friendly HashMap that CHC codegen intercepts
        // via StubRegistry. Keep this method list aligned with
        // StubRegistry::lookup_trust_mcmap_suffix so we only freeze calls that have
        // concrete CHC handlers (#788).
        let is_trust_mcmap_path = fn_name.contains("::TrustMcMap::")
            || fn_name.contains("::TrustMcMap::<")
            || fn_name.contains("::TrustMcMap<")
            || fn_name.contains("TrustMcMapIntoIter");
        if is_trust_mcmap_path {
            let method = fn_name.rsplit("::").next().unwrap_or_default();
            let is_trust_mcmap_stubbed_method = matches!(
                method,
                "new"
                    | "default"
                    | "insert"
                    | "get"
                    | "contains_key"
                    | "remove"
                    | "len"
                    | "is_empty"
                    | "clear"
                    | "clone"
                    | "into_iter"
            ) || (method == "next"
                && fn_name.contains("TrustMcMapIntoIter"));
            if is_trust_mcmap_stubbed_method {
                return true;
            }
        }

        // BTreeSet/BTreeMap - preserve for SMT Array codegen (Part of #1659)
        // These collections have semantic stubs that model them as SMT arrays.
        // If inlined, we'd hit internal BTree node/search operations that lack stubs.
        // The prefix-based abstraction in reachability.rs handles the internal methods,
        // but inlining can expose them before reachability runs.
        if fn_name.contains("BTreeSet") || fn_name.contains("BTreeMap") || fn_name.contains("btree")
        {
            return true;
        }

        // Part of #4050: ArraySolver methods — preserve for shadow dispatch.
        // The shadow dispatcher (codegen_call_array_solver_shadow.rs) intercepts
        // ArraySolver method calls and replaces loop-heavy bodies (get_assignment,
        // pop, record_assignment) with single SMT array operations. Without this
        // guard, Kani's InlinePass inlines these methods into the harness body,
        // exposing while-loop structures that PDR cannot solve.
        if fn_name.contains("ArraySolver::") {
            return true;
        }

        // Vec operations - preserve for stub codegen (#1037)
        // Vec has semantic stubs (VecNew, VecPush, etc.) that model it as (ptr, len, cap).
        // If inlined, we'd hit RawVec internals which lack MIR/stubs.
        // Note: fn_name has format like "std::vec::Vec::<T>::push" or "std::vec::Vec::<T, A>::len"
        // Exclude RawVec itself since those need to be inlined if ever encountered.
        let contains_vec = fn_name.contains("std::vec::Vec") || fn_name.contains("alloc::vec::Vec");
        if contains_vec && !fn_name.contains("RawVec") {
            // Stubbed Vec methods: new, push, pop, len, capacity, is_empty, clear, clone
            let is_vec_stub = fn_name.ends_with("::new")
                || fn_name.ends_with("::push")
                || fn_name.ends_with("::push_mut")  // Internal push helper
                || fn_name.ends_with("::pop")
                || fn_name.ends_with("::len")
                || fn_name.ends_with("::capacity")
                || fn_name.ends_with("::is_empty")
                || fn_name.ends_with("::clear")
                || fn_name.ends_with("::with_capacity")
                || fn_name.ends_with("::as_mut_ptr")  // Returns pointer to buffer
                || fn_name.ends_with("::as_ptr")     // Returns const pointer
                || fn_name.ends_with("::as_slice") // Returns slice view
                || fn_name.ends_with("::into_iter"); // Produces IntoIter (#2876 RC2)
            if is_vec_stub {
                debug!("Not inlining Vec stub: {}", fn_name);
                return true;
            }
        }

        // Vec IntoIter operations - preserve for stub codegen (#2876 RC2)
        // IntoIter has a different path (alloc::vec::into_iter::IntoIter) that doesn't
        // match the "alloc::vec::Vec" pattern above. Without this, IntoIter::next() gets
        // inlined into raw pointer operations (NonNull::add, NonNull::read, etc.).
        if fn_name.contains("IntoIter")
            && (fn_name.contains("alloc::vec") || fn_name.contains("std::vec"))
        {
            debug!("Not inlining Vec IntoIter operation: {}", fn_name);
            return true;
        }

        // String operations - preserve for stub codegen (#1691)
        // String has semantic stubs (StringNew, StringLen, StringFromUtf8Lossy, etc.)
        // If inlined, we'd hit internal String/RawVec operations that blow up the MIR.
        // Note: alloc::string::String and std::string::String are both common paths
        let contains_string =
            fn_name.contains("alloc::string::String") || fn_name.contains("std::string::String");
        if contains_string {
            debug!("Not inlining String operation: {}", fn_name);
            return true;
        }

        // Cow<str> operations - preserve for stub codegen (#1691)
        // Cow<str>::to_string has a dedicated stub (CowToString).
        // from_utf8_lossy returns Cow<str>, and the whole chain is modeled as String.
        // If inlined, we'd hit Cow/Borrow internals that lack stubs.
        if fn_name.contains("std::borrow::Cow") || fn_name.contains("alloc::borrow::Cow") {
            debug!("Not inlining Cow operation: {}", fn_name);
            return true;
        }

        // Core/std conversion helpers with explicit CHC/BMC stubs (#3679).
        // These must remain as Call terminators so dispatch can match them
        // before we descend into iterator / Utf8Error / ParseIntError internals.
        if (fn_name.contains("core::str::")
            || fn_name.contains("std::str::")
            || fn_name.contains("alloc::str::")
            || fn_name.starts_with("str::"))
            && fn_name.ends_with("from_utf8")
        {
            debug!("Not inlining str::from_utf8 conversion: {}", fn_name);
            return true;
        }
        // Vec::from(&[T]) is handled via has_stubbed_trait_impl() instance
        // resolution (#3679) — the def-path name is "std::convert::From::from"
        // which doesn't contain "Vec", so string matching cannot work here.
        if (fn_name.contains("core::str::") || fn_name.contains("std::str::"))
            && fn_name.contains("FromStr")
            && fn_name.ends_with("::from_str")
        {
            debug!("Not inlining FromStr::from_str conversion: {}", fn_name);
            return true;
        }

        // ToString trait - preserve for stub codegen (#1691)
        // ToString::to_string is stubbed to return symbolic String.
        // If inlined, we'd hit Display/format internals.
        if fn_name.contains("ToString") && fn_name.contains("to_string") {
            debug!("Not inlining ToString::to_string: {}", fn_name);
            return true;
        }

        // Pointer provenance methods — preserve for CHC stub handlers (Part of #3492)
        // addr() and with_addr() are strict-provenance methods whose MIR bodies
        // expand to cast chains + wrapping_sub + wrapping_byte_offset. At Mem level,
        // intermediate isize values from casts land in typed memory arrays that
        // wrapping_sub's operand resolver cannot read, producing unconstrained
        // (sound but imprecise) results. Blocking inlining lets the CHC stub
        // handlers (PtrAddr, PtrWithAddr) compute results directly.
        if (fn_name.contains("mut_ptr::") || fn_name.contains("const_ptr::"))
            && (fn_name.ends_with("::addr") || fn_name.ends_with("::with_addr"))
        {
            return true;
        }

        // SIMD operations — preserve for CHC SIMD dispatch (Part of #3792)
        // These methods go through MaybeUninit + copy_nonoverlapping internally,
        // which the inline translator cannot handle (produces Bool for Array
        // destinations). After transparent SIMD type unwrapping both Simd<T,N>
        // and [T;N] have the same Array sort, enabling direct CHC encoding.
        if (fn_name.contains("Simd") || fn_name.contains("simd"))
            && (fn_name.ends_with("::from_array")
                || fn_name.ends_with("::to_array")
                || fn_name.ends_with("::as_array")
                || fn_name.ends_with("::as_mut_array")
                || fn_name.ends_with("::splat")
                || fn_name.ends_with("::resize"))
        {
            debug!("Not inlining SIMD identity operation: {}", fn_name);
            return true;
        }

        // Stable atomic operations — preserve for CHC atomic stubs (Part of #3452, #3777)
        // Uses the shared classifier from stable_atomic_policy to keep reachability
        // and inline pass on one policy ledger.
        if crate::kani_middle::stable_atomic_policy::is_handler_backed_stable_atomic(fn_name) {
            debug!("Not inlining stable atomic operation: {}", fn_name);
            return true;
        }

        // slice::contains — preserve for CHC direct dispatch (Part of #4072).
        // The CHC handler lowers `[T]::contains` straight to a finite disjunction
        // over the backing array. If fn_inline tries to descend into stdlib
        // wrappers first, the call boundary becomes unstable and pub_static falls
        // back into iterator/chunks lowering.
        if handler_boundaries::is_handler_backed_slice_contains(fn_name) {
            debug!("Not inlining slice::contains handler boundary: {}", fn_name);
            return true;
        }

        // Range/RangeInclusive::contains — preserve for BMC range contains
        // handling. Inlining expands through RangeBounds::{start,end}_bound and
        // Bound<&T>, which can degrade value comparisons into generated reference
        // address comparisons in BMC.
        if handler_boundaries::is_handler_backed_range_contains(fn_name) {
            debug!("Not inlining range contains handler boundary: {}", fn_name);
            return true;
        }

        // slice::first / slice::is_empty — preserve for CHC stub dispatch (Part of #4113).
        // The CHC SliceFirst handler produces canonical ZST ref encoding (BV64(1))
        // for `[(); N]::first()` that matches promoted constant `Some(&())`.
        // If FunctionInlinePass inlines `first()` before CHC codegen, the inlined
        // body produces a heap address reference that mismatches the promoted
        // constant, causing CTREX on ZST harnesses.
        if handler_boundaries::is_handler_backed_slice_accessor(fn_name) {
            debug!("Not inlining slice accessor handler boundary: {}", fn_name);
            return true;
        }

        // Allocator functions - preserve for stub codegen (#2075)
        // exchange_malloc (Box::new entry point), public alloc wrappers, and
        // low-level __rust_* symbols have stubs in stubs_alloc.rs that model
        // heap operations directly. If inlined, we route through wrapper-level
        // precondition checks that currently produce spurious CTREX under CHC.
        if fn_name.contains("exchange_malloc")
            || fn_name.contains("alloc::alloc::alloc")
            || fn_name.contains("alloc::alloc::alloc_zeroed")
            || fn_name.contains("alloc::alloc::dealloc")
            || fn_name.contains("alloc::alloc::realloc")
            || fn_name.contains("std::alloc::alloc")
            || fn_name.contains("std::alloc::alloc_zeroed")
            || fn_name.contains("std::alloc::dealloc")
            || fn_name.contains("std::alloc::realloc")
            || fn_name.contains("__rust_alloc")
            || fn_name.contains("__rust_dealloc")
            || fn_name.contains("__rust_realloc")
        {
            debug!("Not inlining allocator function: {}", fn_name);
            return true;
        }

        // Misc compiler intrinsics — preserve for CHC misc intrinsic handler (Part of #3464)
        // typed_swap_nonoverlapping has a default MIR body that expands into
        // swap_nonoverlapping → swap_nonoverlapping_bytes (20+ blocks). If inlined,
        // the CHC solver cannot handle the byte-level operations. The CHC handler
        // (codegen_typed_swap in misc_intrinsics_volatile.rs) models the swap as
        // direct cross-assignment: *x = old_*y, *y = old_*x.
        // Also block std::mem::swap which calls typed_swap_nonoverlapping internally.
        if fn_name.contains("typed_swap_nonoverlapping")
            || (fn_name.contains("std::mem::swap") && !fn_name.contains("swap_nonoverlapping"))
        {
            debug!("Not inlining swap intrinsic: {}", fn_name);
            return true;
        }

        // kani::mem predicates — preserve for CHC kani_mem stub dispatch (Part of #3470)
        // can_dereference, can_read_unaligned, can_write, can_write_unaligned,
        // is_inbounds, is_ptr_aligned, assert_is_initialized are all kani_mem stubs
        // that CHC over-approximates as true. If inlined, the expanded MIR has
        // short-circuit && control flow with Option pattern matching (from
        // checked_size_of_raw inside is_inbounds) that CHC encoding handles
        // incorrectly — inner calls evaluate to unconstrained, causing spurious CTREX.
        // Blocking inlining lets stub detection recognize the whole predicate.
        if fn_name.contains("kani") && fn_name.contains("::mem::") {
            let method = fn_name.rsplit("::").next().unwrap_or_default();
            if matches!(
                method,
                "can_dereference"
                    | "can_read_unaligned"
                    | "can_write"
                    | "can_write_unaligned"
                    | "is_inbounds"
                    | "is_ptr_aligned"
                    | "assert_is_initialized"
            ) {
                debug!("Not inlining kani::mem predicate: {}", fn_name);
                return true;
            }
        }

        // Part of #4067: Rc::new / Arc::new — preserve for CHC codegen_rc_arc_new
        // dispatch (codegen_call_dispatch_dyn.rs). If MIR-inlined, the body expands
        // into Box::new + into_raw_with_allocator + Global field projections that
        // CHC codegen cannot handle (Place field projection sort, unconstrained
        // Global allocator assignment). The CHC handler models Arc/Rc::new as
        // allocate + store inner value, bypassing the stdlib body entirely.
        if (fn_name.contains("rc::Rc") || fn_name.contains("sync::Arc"))
            && fn_name.ends_with("::new")
        {
            debug!("Not inlining Rc/Arc::new: {}", fn_name);
            return true;
        }

        // Part of #4112: Iterator adapter next() — preserve for CHC adapter dispatch.
        // detect_adapter_next_by_receiver_type (stubs_impl.rs) needs a Call terminator
        // to FlatMap::next/Map::next/etc. to detect the adapter type from the receiver.
        // If MIR-inlined, the adapter body expands into nested iterator/closure calls
        // that the main CHC encoder handles through memory stores/selects, producing
        // incorrect memory aliasing for concrete-element iteration (CTREX).
        // The CHC handler models these as position-indexed ITE chains.
        if Self::is_iterator_adapter_next(fn_name) {
            debug!("Not inlining iterator adapter next(): {}", fn_name);
            return true;
        }

        false
    }

    /// Check if a function is an iterator adapter `next()` method with a dedicated
    /// CHC handler.
    ///
    /// Iterator adapters (FlatMap, Map, Filter, FilterMap, Zip, Chain, Flatten,
    /// FlattenCompat) have `next()` implementations that the CHC adapter dispatch
    /// (`detect_adapter_next_by_receiver_type` in stubs_impl.rs) intercepts by
    /// checking the receiver type. If MIR-inlined, the Call terminator disappears
    /// and the adapter detection cannot fire. Part of #4112.
    fn is_iterator_adapter_next(fn_name: &str) -> bool {
        if !fn_name.ends_with("::next") {
            return false;
        }
        // Match adapter type names in the def-path.
        // Typical fn_name: "core::iter::adapters::flatten::FlatMap::<I, U, F>::next"
        // or "<core::iter::adapters::map::Map<I, F> as Iterator>::next"
        fn_name.contains("FlatMap")
            || fn_name.contains("flatten::Flatten")
            || fn_name.contains("FlattenCompat")
            || fn_name.contains("adapters::map::Map")
            || fn_name.contains("adapters::filter::Filter")
            || fn_name.contains("FilterMap")
            || fn_name.contains("adapters::zip::Zip")
            || fn_name.contains("adapters::chain::Chain")
    }

    /// Check if a resolved `Clone::clone` instance is `Rc::clone` or `Arc::clone`.
    ///
    /// At the MIR def-path level, `Rc::clone` appears as `std::clone::Clone::clone`.
    /// Instance resolution produces the impl-specific name (e.g.
    /// `<Rc<i32> as Clone>::clone`) where `rc::Rc` or `sync::Arc` is visible.
    ///
    /// CHC codegen has dedicated handlers (`codegen_rc_arc_clone` in
    /// `codegen_call_dispatch_dyn.rs`) that model clone as pointer identity.
    /// If the inline pass expands the stdlib clone body first, the CHC handler
    /// never fires. Part of #3978.
    fn is_rc_arc_clone_resolved(fn_def: FnDef, fn_args: &GenericArgs) -> bool {
        let Ok(instance) = Instance::resolve(fn_def, fn_args) else {
            return false;
        };
        let resolved = instance.name();
        resolved.ends_with("::clone")
            && (resolved.contains("rc::Rc") || resolved.contains("sync::Arc"))
    }

    /// Check if a resolved `PartialEq::eq`/`ne` instance is for a compound type.
    ///
    /// At the MIR def-path level, `<Option<u8> as PartialEq>::eq` appears as
    /// `core::cmp::PartialEq::eq` (the trait method). Instance resolution
    /// produces the impl-specific name (e.g.
    /// `<core::option::Option<u8> as core::cmp::PartialEq>::eq`) where the
    /// concrete Self type is visible.
    ///
    /// Compound types (Option, Result, enums with data) have derived PartialEq
    /// bodies that expand into 10+ basic blocks with typed memory operations
    /// when MIR-inlined. The CHC cmp_stub handler can compare these types
    /// directly via structural SMT Datatype equality. Blocking inlining
    /// preserves the Call terminator for the cmp_stub to intercept.
    ///
    /// Primitive types (u8, u32, bool, usize, etc.) must NOT be blocked because
    /// Range<T>::next() uses PartialEq for loop termination — blocking it
    /// changes MIR structure and breaks CHC loop invariant synthesis.
    fn is_compound_partial_eq_resolved(fn_def: FnDef, fn_args: &GenericArgs) -> bool {
        let Ok(instance) = Instance::resolve(fn_def, fn_args) else {
            return false;
        };
        let resolved = instance.name();
        // Must be a PartialEq::eq or PartialEq::ne method
        let is_partial_eq_method = resolved.contains("PartialEq")
            && (resolved.ends_with("::eq") || resolved.ends_with("::ne"));
        if !is_partial_eq_method {
            return false;
        }
        // Fast path: known std enum types with dedicated CHC Datatype encoding.
        if resolved.contains("Option")
            || resolved.contains("Result")
            || resolved.contains("Ordering")
            || resolved.contains("Poll")
            || resolved.contains("ControlFlow")
        {
            return true;
        }
        // Generic path: any enum type with derived PartialEq.
        // Enums encoded as SMT Datatypes use structural equality which matches
        // derived PartialEq semantics. If MIR-inlined, the derived body expands
        // into discriminant-switch + per-variant field comparisons (10+ basic
        // blocks) that CHC cannot solve. Structs and primitives are NOT blocked.
        if let Some(GenericArgKind::Type(self_ty)) = fn_args.0.first() {
            if let TyKind::RigidTy(RigidTy::Adt(adt_def, _)) = self_ty.kind() {
                if adt_def.kind() == AdtKind::Enum {
                    return true;
                }
            }
        }
        false
    }

    /// Check if a resolved `Ord::min`/`max`/`clamp` instance is for an integer type.
    ///
    /// At the MIR def-path level, primitive calls such as `a.min(b)` appear as
    /// `core::cmp::Ord::min`. Resolving the instance reveals the concrete `Self`
    /// type. Keep only integer Ord calls uninlined: the CHC comparison dispatcher
    /// already has signed/unsigned bitvector encodings for these methods, while
    /// inlining exposes branchy MIR that can lose the intended signedness in
    /// mixed i*/usize harnesses.
    fn is_integer_ord_min_max_clamp_resolved(fn_def: FnDef, fn_args: &GenericArgs) -> bool {
        let Ok(instance) = Instance::resolve(fn_def, fn_args) else {
            return false;
        };
        let resolved = instance.name();
        let is_ord_method = resolved.contains("cmp::Ord")
            && (resolved.ends_with("::min")
                || resolved.ends_with("::max")
                || resolved.ends_with("::clamp"));
        if !is_ord_method {
            return false;
        }
        matches!(
            fn_args.0.first(),
            Some(GenericArgKind::Type(self_ty))
                if matches!(
                    self_ty.kind(),
                    TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))
                )
        )
    }

    /// Check if a resolved `Iterator::next` instance is an adapter next() method.
    ///
    /// At the MIR def-path level, trait method calls like
    /// `<FlatMap<I,U,F> as Iterator>::next` appear as `Iterator::next`. The
    /// `is_iterator_adapter_next` name-based check misses these because the
    /// fn_name is the trait method path, not the concrete implementation path.
    ///
    /// This function resolves the instance to get the impl-specific path (e.g.,
    /// `core::iter::adapters::flatten::FlatMap::<I, U, F>::next`) and checks
    /// for known adapter type names.
    ///
    /// Part of #4112: Fixes FlatMap::next being MIR-inlined, preventing CHC
    /// adapter dispatch from producing concrete element constraints.
    fn is_adapter_next_resolved(fn_def: FnDef, fn_args: &GenericArgs) -> bool {
        let Ok(instance) = Instance::resolve(fn_def, fn_args) else {
            debug!("adapter-next: Instance::resolve failed for {}", fn_def.0.name());
            return false;
        };
        let resolved = instance.name();
        debug!(%resolved, "adapter-next: resolved");
        if !resolved.ends_with("::next") {
            return false;
        }
        resolved.contains("FlatMap")
            || resolved.contains("flatten::Flatten")
            || resolved.contains("FlattenCompat")
            || resolved.contains("adapters::map::Map")
            || resolved.contains("adapters::filter::Filter")
            || resolved.contains("FilterMap")
            || resolved.contains("adapters::zip::Zip")
            || resolved.contains("adapters::chain::Chain")
    }

    fn is_alloc_or_layout_stub_boundary(fn_name: &str) -> bool {
        static REGISTRY: OnceLock<StubRegistry> = OnceLock::new();
        let registry = REGISTRY.get_or_init(StubRegistry::new);
        let Some(stub) = registry.lookup(fn_name) else {
            return false;
        };

        stub.is_alloc_extra()
            || stub.is_layout_extra()
            || matches!(
                stub,
                StubKind::BoxNew
                    | StubKind::RustAlloc
                    | StubKind::RustAllocZeroed
                    | StubKind::RustDealloc
                    | StubKind::RustRealloc
                    | StubKind::LayoutSize
                    | StubKind::LayoutAlign
                    | StubKind::LayoutIsSizeAlignValid
            )
    }

    /// Check if a trait method call resolves to an impl with a stub (#3679).
    ///
    /// For trait methods like `From::from`, `fn_def.0.name()` returns the trait
    /// definition path (e.g. `std::convert::From::from`) which doesn't reveal
    /// the implementing type. This method resolves the instance to get the full
    /// impl path (e.g. `<Vec<u8> as From<&[u8]>>::from`) and checks whether
    /// the stub dispatch would recognize it.
    fn has_stubbed_trait_impl(fn_name: &str, fn_def: FnDef, fn_args: &GenericArgs) -> bool {
        // Only resolve for known trait method patterns that the stub registry
        // handles via type-dependent dispatch.
        if !(fn_name.contains("convert::From") && fn_name.ends_with("::from")) {
            return false;
        }
        let Ok(instance) = Instance::resolve(fn_def, fn_args) else {
            return false;
        };
        let resolved_name = instance.name();
        // Vec::from(&[T]) → VecFromSlice stub (#3673)
        if resolved_name.contains("Vec") && resolved_name.contains("From") {
            debug!("Resolved trait impl has Vec stub: {}", resolved_name);
            return true;
        }
        // String::from(&str) → StringFrom stub
        if resolved_name.contains("String") && resolved_name.contains("From") {
            debug!("Resolved trait impl has String stub: {}", resolved_name);
            return true;
        }
        false
    }

    /// Run inlining with a caller-supplied callee body provider.
    ///
    /// The default `TransformPass` implementation uses raw MIR bodies
    /// (`Instance::body`). AY codegen can call this with transformed bodies so
    /// inlined callees include contract/stub rewrites.
    pub(crate) fn transform_with_body_provider<F>(
        &mut self,
        tcx: TyCtxt<'_>,
        body: Body,
        instance: Instance,
        mut body_provider: F,
    ) -> (bool, Body)
    where
        F: FnMut(Instance) -> Option<Body>,
    {
        let name = instance.name();
        debug!(
            "FunctionInlinePass: checking {} (enabled={}, blocks={})",
            name,
            self.config.enabled,
            body.blocks.len()
        );

        // Reset per body: the bound belongs to THIS body's specialized variadic
        // calls, and the pass is reused across bodies.
        self.variadic_actual_bound = None;

        if !self.config.enabled {
            debug!("FunctionInlinePass: disabled, skipping {}", name);
            return (false, body);
        }

        let mut mutable_body = MutableBody::from(body);
        let mut ever_changed = false;
        let mut total_inline_count: usize = 0;
        let mut variadic_actual_bound: Option<usize> = None;
        // Per-body budget. The contract raises below are a property of THIS
        // body's contract machinery, so they must not leak into the next body
        // the (reused, `&mut self`) pass is handed.
        let mut max_depth = self.config.max_depth;

        // Iterate until fixpoint or max_depth reached.
        // Each iteration resolves Drop terminators, then inlines Call sites.
        // Part of #3039: Drop shim inlining added to the fixpoint loop.
        loop {
            // Transitive contract-chain depth boost. The static boost in
            // `codegen_function` only scans the harness's DIRECT body; a plain
            // proof that reaches a contract-annotated fn only transitively keeps
            // the low default depth and leaks the contract's inner call as an
            // unsupported `Call terminator`. Once inlining has EXPOSED the chain
            // in the working body, raise the cap here. SOUND: deeper inlining
            // only eliminates Call terminators; it never changes semantics.
            if max_depth < CONTRACT_INLINE_DEPTH && body_has_contract_chain(&mutable_body) {
                debug!(
                    "FunctionInlinePass: contract chain exposed in {} — raising max_depth {} -> {}",
                    name, max_depth, CONTRACT_INLINE_DEPTH
                );
                max_depth = CONTRACT_INLINE_DEPTH;
            }

            // Contract GLUE still pending: re-grant the contract budget from
            // where we are now. Each layer of glue only becomes visible once
            // the layer above it has been inlined, so a chain of
            // contract-carrying callees needs more than one flat grant — and
            // stopping mid-chain leaves a `kani_register_contract` behind,
            // which costs the contract frame's internal agreement rather than
            // merely some precision (see `body_has_contract_glue_call`).
            let contract_headroom = total_inline_count
                .saturating_add(CONTRACT_INLINE_DEPTH)
                .min(MAX_CONTRACT_INLINE_DEPTH);
            if max_depth < contract_headroom && body_has_contract_glue_call(&mutable_body) {
                debug!(
                    "FunctionInlinePass: contract glue pending in {} — extending max_depth {} -> {}",
                    name, max_depth, contract_headroom
                );
                max_depth = contract_headroom;
            }

            if total_inline_count >= max_depth {
                debug!("FunctionInlinePass: max inline depth reached ({})", total_inline_count);
                break;
            }

            let mut iteration_changed = false;

            // Phase 1: Resolve Drop terminators (Part of #3039).
            // Empty drop shims → Goto. Non-empty shims → inline body.
            // Inlined drop shims contain Call terminators to Drop::drop,
            // which Phase 2 picks up in the next iteration.
            if resolve_drop_terminators(
                tcx,
                &mut mutable_body,
                &instance,
                &mut body_provider,
                max_depth.saturating_sub(total_inline_count),
                &mut total_inline_count,
            ) {
                iteration_changed = true;
            }

            // Phase 2: Find call sites in current body state
            let call_sites = self.find_calls_to_inline_mutable(&mutable_body);
            if call_sites.is_empty() && !iteration_changed {
                break;
            }

            if !call_sites.is_empty() {
                debug!(
                    "FunctionInlinePass: found {} call sites to inline in {} (iteration {})",
                    call_sites.len(),
                    name,
                    total_inline_count + 1
                );
            }

            // Process call sites in reverse order to avoid index invalidation
            for &call_bb_idx in call_sites.iter().rev() {
                // Defer depth check: virtual calls bypass the limit because leaving
                // them unresolved produces unsound unconstrained results in SSA codegen.
                let depth_exceeded = total_inline_count >= max_depth;
                // Wall-2: a callee operand typed as the CLOSURE ITSELF is the
                // loop-contract proof-rule / decreases invariant-evaluation
                // shape (`rule.rs::fn_op` — `Instance::ty()` of a closure Fn
                // shim is the closure type). Those tiny compiler-generated
                // evaluations bypass the depth limit below: leaving one
                // un-inlined loses the loop-contract obligation it computes
                // (the call falls through CHC dispatch to havoc and the
                // base/step checks go symbolic — the multiple_loops class).
                let mut direct_closure_callee = false;

                // Extract info from the call terminator, cloning what we need
                // Supports both FnDef and Closure types (#1575)
                let call_info = {
                    let block = &mutable_body.blocks()[call_bb_idx];
                    if let TerminatorKind::Call { func, args, destination, target, .. } =
                        &block.terminator.kind
                    {
                        let func_ty = match func.ty(mutable_body.locals()) {
                            Ok(ty) => ty,
                            Err(_) => continue,
                        };

                        // Extract callable info - either FnDef or Closure (#1575)
                        let callable_info = match func_ty.kind() {
                            TyKind::RigidTy(RigidTy::FnDef(def, fn_args)) => {
                                let fn_name = def.0.name();
                                if Self::is_closure_call_shim(&fn_name) {
                                    let closure_kind = Self::closure_kind_from_shim(&fn_name);
                                    // Try to extract closure info from first arg
                                    let closure_info = args
                                        .first()
                                        .and_then(|arg0| {
                                            Self::closure_info_from_arg(arg0, mutable_body.locals())
                                        })
                                        .or_else(|| {
                                            // Contract wrappers pass closures through generic `F`,
                                            // so arg0 type may be a type parameter. Recover closure
                                            // type from call shim generic args when available.
                                            fn_args.0.first().and_then(|generic_arg| {
                                                let GenericArgKind::Type(closure_ty) = generic_arg
                                                else {
                                                    return None;
                                                };
                                                match closure_ty.kind() {
                                                    TyKind::RigidTy(RigidTy::Closure(
                                                        closure_def,
                                                        closure_args,
                                                    )) => Some((closure_def, closure_args)),
                                                    _ => None, // external enum: TyKind
                                                }
                                            })
                                        });

                                    if let Some((closure_def, closure_args)) = closure_info {
                                        debug!(
                                            "FunctionInlinePass: treating {} as closure call shim for {}",
                                            fn_name,
                                            closure_def.0.name()
                                        );
                                        Some((
                                            CallableKind::Closure(closure_def, closure_kind),
                                            closure_args,
                                        ))
                                    } else {
                                        // Fall back to regular FnDef - let codegen handle it
                                        // This avoids skipping calls when closure extraction fails
                                        debug!(
                                            "FunctionInlinePass: closure call shim {} - fallback to FnDef",
                                            fn_name
                                        );
                                        Some((CallableKind::FnDef(def), fn_args.clone()))
                                    }
                                } else {
                                    Some((CallableKind::FnDef(def), fn_args.clone()))
                                }
                            }
                            TyKind::RigidTy(RigidTy::Closure(def, fn_args)) => {
                                // Direct closure-typed call: derive the closure
                                // kind from the self-arg mode. `&C` calls the
                                // closure's own fn item (ClosureKind::Fn — has
                                // MIR); by-value `C` needs the FnOnce shim.
                                // Loop-contract `decreases` instrumentation
                                // and the #47 loop-contract proof rule's
                                // invariant evaluations emit the `&C` shape.
                                let kind = match args
                                    .first()
                                    .and_then(|arg0| arg0.ty(mutable_body.locals()).ok())
                                    .map(|ty| ty.kind())
                                {
                                    Some(TyKind::RigidTy(RigidTy::Ref(_, _, mutability))) => {
                                        if mutability == Mutability::Mut {
                                            ClosureKind::FnMut
                                        } else {
                                            ClosureKind::Fn
                                        }
                                    }
                                    _ => ClosureKind::FnOnce,
                                };
                                direct_closure_callee = true;
                                Some((CallableKind::Closure(def, kind), fn_args.clone()))
                            }
                            _ => None, // external enum: TyKind
                        };

                        callable_info.map(|(callable, fn_args)| {
                            (
                                callable,
                                fn_args,
                                args.clone(),
                                destination.clone(),
                                *target,
                                block.terminator.span,
                            )
                        })
                    } else {
                        None
                    }
                };

                let Some((callable, fn_args, args, destination, target, call_span)) = call_info
                else {
                    continue;
                };

                // Resolve the instance to get the concrete body
                // Different resolution for FnDef vs Closure (#1575)
                let callee_instance = match &callable {
                    CallableKind::FnDef(fn_def) => {
                        if let Ok(inst) = Instance::resolve(*fn_def, &fn_args) {
                            // Part of #3159: Devirtualize virtual calls.
                            // When Instance::resolve returns InstanceKind::Virtual,
                            // the vtable call has no body to inline. Try single-impl
                            // devirtualization first, then receiver-type tracing.
                            if matches!(inst.kind, InstanceKind::Virtual { .. }) {
                                if let Some(concrete) = try_devirtualize(tcx, *fn_def, &fn_args) {
                                    concrete
                                } else if let Some(concrete) = try_devirtualize_via_receiver(
                                    tcx,
                                    *fn_def,
                                    &fn_args,
                                    &args,
                                    &mutable_body,
                                ) {
                                    concrete
                                } else {
                                    debug!(
                                        "FunctionInlinePass: SKIP virtual (cannot devirtualize) fn={}",
                                        fn_def.0.name()
                                    );
                                    continue;
                                }
                            } else if depth_exceeded {
                                // Part of #3348: Clone::clone for user-defined structs
                                // bypasses the depth limit. Derive'd Clone is trivial
                                // (field-by-field copy) and the PrimitiveClone CHC stub
                                // cannot handle struct clones with collection fields
                                // (it only resolves the scalar state var, missing the
                                // Array). Inlining Clone exposes per-field clone calls
                                // that each have proper stubs (BTreeMapClone, etc.).
                                let fn_name = fn_def.0.name();
                                if fn_name.contains("Clone") && fn_name.contains("clone") {
                                    debug!(
                                        "FunctionInlinePass: force-inline Clone::clone past depth limit: {}",
                                        fn_name
                                    );
                                    inst
                                } else if body_provider(inst)
                                    .as_ref()
                                    .is_some_and(body_is_noop_shim)
                                {
                                    // Empty/no-op concrete-impl shim (e.g. a test sink's
                                    // empty ActionSink methods): force-inline past the depth
                                    // limit. A single-block Return body that touches only its
                                    // own locals inlines as a pure Call->Goto (no added
                                    // blocks, no behavior change, no state explosion), so
                                    // bypassing the cap is strictly safer than leaving an
                                    // unsupported Call terminator -> #3017 variant-0 fallback.
                                    // Mirrors the Clone::clone bypass above.
                                    debug!(
                                        "FunctionInlinePass: force-inline empty shim past depth limit: {}",
                                        fn_name
                                    );
                                    inst
                                } else {
                                    // Non-virtual calls respect the depth limit.
                                    // Use continue (not break) so remaining call sites
                                    // are still checked — virtual calls bypass depth.
                                    continue;
                                }
                            } else {
                                inst
                            }
                        } else {
                            debug!(
                                "FunctionInlinePass: cannot resolve instance for {}",
                                fn_def.0.name()
                            );
                            continue;
                        }
                    }
                    CallableKind::Closure(closure_def, closure_kind) => {
                        if depth_exceeded && !direct_closure_callee {
                            // Closures respect the depth limit, but continue
                            // to allow virtual calls later in the loop.
                            // Exception (Wall-2): direct closure-typed callee
                            // operands — loop-rule/decreases invariant
                            // evaluations — bypass the cap (see above).
                            continue;
                        }
                        debug!(
                            "FunctionInlinePass: resolve closure {} kind={:?} fn_args={:?}",
                            closure_def.0.name(),
                            closure_kind,
                            fn_args
                        );
                        match Instance::resolve_closure(
                            *closure_def,
                            &fn_args,
                            closure_kind.clone(),
                        ) {
                            Ok(inst) => inst,
                            Err(e) => {
                                warn!(
                                    "FunctionInlinePass: cannot resolve closure {} ({:?}): {:?}",
                                    closure_def.0.name(),
                                    closure_kind,
                                    e
                                );
                                continue;
                            }
                        }
                    }
                };

                // Self-recursion guard: don't inline function into itself (design gap C).
                // This prevents infinite inlining loops. See #223 and function-inlining-v2.md:86-91.
                if callee_instance.def.def_id() == instance.def.def_id() {
                    debug!(
                        "FunctionInlinePass: SKIP (self-recursion) fn={}",
                        callee_instance.name()
                    );
                    continue;
                }

                // Get the callee body from caller-provided resolver.
                let callee_body = if let Some(b) = body_provider(callee_instance) {
                    b
                } else {
                    // Enhanced logging for #279: identify stdlib trait methods with missing MIR
                    let callee_name = callee_instance.name();
                    let crate_name = callee_instance.def.krate().name;
                    let is_stdlib =
                        matches!(crate_name.as_str(), "core" | "alloc" | "std" | "proc_macro");
                    debug!(
                        "FunctionInlinePass: SKIP (no MIR body) crate={} stdlib={} fn={}",
                        crate_name, is_stdlib, callee_name
                    );
                    // Warn about missing stdlib MIR except for the known alloc shim marker,
                    // which is a no-op symbol often unavailable to the inliner.
                    let is_alloc_shim_signal =
                        callee_name.contains("__rust_no_alloc_shim_is_unstable_v2");
                    if is_stdlib && !is_alloc_shim_signal {
                        // Say it once. The inliner reaches the same callee from
                        // every harness and every pass over a body, so an
                        // ordinary `for e in v.iter_mut()` reported the same six
                        // functions four times over -- two dozen identical lines
                        // between the user's harness and its verdict. The fact
                        // is worth surfacing (an un-inlined stdlib function is
                        // stubbed or over-approximated, which bears on what a
                        // proof covers); the repetition is not.
                        if first_report_of_missing_stdlib_mir(&crate_name, &callee_name) {
                            tracing::warn!(
                                "Stdlib function MIR unavailable: {}::{} - inlining skipped",
                                crate_name,
                                callee_name
                            );
                        }
                    } else if is_alloc_shim_signal {
                        debug!(
                            "FunctionInlinePass: skip warning for alloc shim marker {}::{}",
                            crate_name, callee_name
                        );
                    }
                    continue;
                };

                // Self-RECURSIVE callee guard: the caller==callee check above
                // misses the peeling case — inlining a self-recursive callee
                // into its caller replaces the call with one peeled level PLUS
                // the residual self-call, which this pass then inlines again on
                // the next iteration, up to its budget. The peel is pure loss:
                // the residual call always survives, and the deep peel levels
                // are statically dead at runtime (rec55: count(6) peeled 10
                // levels; the dead residual arg 6-10 wrapped and the CHC
                // walker exhausted on dead code, leaking a recursion-unwind
                // assert). Matches the module-doc contract ("non-recursive
                // functions only"); the CHC walker's const-arg depth relief
                // handles recursion from the un-peeled call site.
                let callee_self_recursive = callee_body.blocks.iter().any(|bb| {
                    let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
                    else {
                        return false;
                    };
                    let Ok(func_ty) = func.ty(callee_body.locals()) else {
                        return false;
                    };
                    match func_ty.kind() {
                        rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(
                            def,
                            _,
                        )) => def.def_id() == callee_instance.def.def_id(),
                        _ => false,
                    }
                });
                if callee_self_recursive {
                    debug!(
                        "FunctionInlinePass: SKIP (self-recursive callee) fn={}",
                        callee_instance.name()
                    );
                    continue;
                }

                debug!(
                    "FunctionInlinePass: inlining {} into {} at bb{}",
                    callee_instance.name(),
                    name,
                    call_bb_idx
                );

                // Inline the callee
                let variadic_actuals = inline_function(
                    tcx,
                    callee_instance,
                    &mut mutable_body,
                    call_bb_idx,
                    &callee_body,
                    &args,
                    &destination,
                    target,
                    call_span,
                );
                if let Some(n) = variadic_actuals {
                    variadic_actual_bound =
                        Some(variadic_actual_bound.map_or(n, |prev: usize| prev.max(n)));
                }

                iteration_changed = true;
                total_inline_count += 1;
            }

            if iteration_changed {
                ever_changed = true;
            } else {
                // No progress this iteration - all remaining calls are non-inlinable
                break;
            }
        }

        if ever_changed {
            debug!("FunctionInlinePass: inlined {} function(s) into {}", total_inline_count, name);
        }

        self.variadic_actual_bound = variadic_actual_bound;
        (ever_changed, mutable_body.into())
    }

    /// Construct-derived unwind bound left by the last body this pass processed.
    ///
    /// `Some(n)` when a `c_variadic` call was specialized into that body and its
    /// `va_arg` fetches survive: no non-failing execution fetches more than `n`
    /// times, because fetch `n + 1` fails its `cursor < n` bounds obligation.
    pub(crate) fn variadic_actual_bound(&self) -> Option<usize> {
        self.variadic_actual_bound
    }
}

impl TransformPass for FunctionInlinePass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Instrumentation
    }

    fn is_enabled(&self, _query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        self.config.enabled
    }

    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        self.transform_with_body_provider(tcx, body, instance, |callee_instance| {
            callee_instance.body()
        })
    }
}

/// Has this missing-MIR callee already been reported in this run?
///
/// Returns true exactly once per distinct `crate::function`, so a diagnostic
/// the inliner rediscovers on every pass is printed once rather than once per
/// visit. Process-global because the compiler runs once per crate and the
/// inliner has no single owner to hang this on.
fn first_report_of_missing_stdlib_mir(crate_name: &str, callee_name: &str) -> bool {
    use std::collections::HashSet;
    use std::sync::{Mutex, OnceLock};

    static REPORTED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let mut key = String::with_capacity(crate_name.len() + callee_name.len() + 2);
    key.push_str(crate_name);
    key.push_str("::");
    key.push_str(callee_name);
    REPORTED
        .get_or_init(|| Mutex::new(HashSet::new()))
        .lock()
        .map_or(true, |mut seen| seen.insert(key))
}
