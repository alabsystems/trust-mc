// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Positive evidence that a harness has NO obligation site anywhere REACHABLE.
//!
//! # Why this exists
//!
//! Zero emitted checks has two causes the driver cannot tell apart: the body
//! genuinely had nothing to prove, or an obligation was DROPPED and calling
//! that a proof is a false Safe. Every signal available to the driver is an
//! *absence* (no drop marker, no counter), and absence of evidence is exactly
//! what a silent drop looks like — so no absence-based rule can ever be sound.
//! The compiler is the only side that sees the MIR, so it certifies instead.
//!
//! The first certificate was "this body has no `Call` and no `Assert`
//! terminator". Sound, but it refuses the moment a harness calls ANYTHING —
//! and `bar();`, `Path::new(..)`, or `println!(..)` are calls, so most
//! genuinely-obligation-free harnesses were refused. This walks the call graph
//! instead and asks the same question of every body it can reach.
//!
//! # What makes it sound
//!
//! It is FAIL-CLOSED at every step. The walk certifies only when it has SEEN
//! every reachable body and found no obligation site in any of them. Anything
//! it cannot see — an unresolvable callee, a body it cannot fetch, a virtual
//! or indirect call, inline asm, a drop glue it cannot resolve, or simply too
//! much code to walk within budget — returns `false`. A `false` costs parity;
//! it can never manufacture a proof.

use std::collections::HashSet;

use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use trust_mc_codegen_shared::IntoOption;
use trust_mc_kani_types::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};

use rustc_public::CrateDef;
use rustc_public::rustc_internal;
use rustc_middle::ty::TyCtxt;

use crate::kani_middle::attributes;

/// Bodies the walk will visit before giving up. A harness that reaches more
/// code than this is not the `fn check() {}` shape this certificate is for,
/// and refusing it costs only parity.
const MAX_BODIES: usize = 256;

/// Blocks the walk will visit before giving up, summed across all bodies.
const MAX_BLOCKS: usize = 20_000;

/// What the walk could establish about a body's obligation sites.
///
/// Three-valued on purpose. "Not provably obligation-free" and "provably HAS
/// an obligation" are different facts and have different consumers:
///
/// * the vacuity certificate may act only on [`Free`](Verdict::Free) — anything
///   less must fail closed;
/// * the nested-call fallback may act only on
///   [`HasObligation`](Verdict::HasObligation) — a POSITIVE sighting. Treating
///   [`Unknown`](Verdict::Unknown) as "has an obligation" would demote nearly
///   every harness that touches an un-inlinable stdlib call, which is the cost
///   the `nested_call_overapprox` blessing exists to avoid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// Every reachable body was walked; none holds an obligation site.
    Free,
    /// An obligation site was SEEN, in a body the walk could actually read.
    HasObligation,
    /// The walk could not finish: an unresolvable callee, an absent body,
    /// inline asm, or the budget. Says nothing either way.
    Unknown,
}

impl Verdict {
    /// `HasObligation` dominates `Unknown` dominates `Free`: seeing one
    /// obligation settles the body however much else went unread.
    fn merge(self, other: Verdict) -> Verdict {
        match (self, other) {
            (Verdict::HasObligation, _) | (_, Verdict::HasObligation) => Verdict::HasObligation,
            (Verdict::Unknown, _) | (_, Verdict::Unknown) => Verdict::Unknown,
            _ => Verdict::Free,
        }
    }
}

/// Does `body` — and every body reachable from it — contain no obligation
/// site?
///
/// See the module docs. The answer is `false` whenever the walk cannot prove
/// the answer is `true`.
pub(crate) fn body_is_transitively_obligation_free(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    stubs: &StubMap,
) -> bool {
    walk_verdict(tcx, instance, body, stubs) == Verdict::Free
}

/// Did the walk POSITIVELY see an obligation reachable from `instance`, in a
/// body written in the crate UNDER VERIFICATION?
///
/// `false` for both "provably none" and "could not tell", so a caller acting
/// on this is acting on evidence, never on ignorance.
///
/// # Why local-crate only
///
/// A dropped obligation matters when nothing else models it. That is the case
/// for the user's own code: `assert!(a == 43)` inside an `async` block is the
/// whole point of the harness, and when the walker gives up on that coroutine
/// the assertion simply vanishes.
///
/// It is NOT the case for the standard library, whose behaviour trust-mc
/// models through dedicated handlers rather than by walking MIR.
/// `<[T]>::into_vec` reaches allocator internals full of obligation sites, but
/// the encoder separately constructs a provably-valid backing for it — so
/// demoting on those sightings fails a CORRECT program.
/// `tools/soundness-duals/dual_bounded_any_vec_valid.rs` is exactly that
/// program, and it went FAILED (`nested_call_dropped_obligation=4`) when this
/// check was crate-blind. The dual wall caught it before it shipped.
///
/// LIMIT, stated rather than implied: an obligation dropped inside a
/// DEPENDENCY's code is still missed. Narrowing to the local crate is a strict
/// improvement over blessing everything, not a complete fix.
pub(crate) fn body_has_visible_obligation(tcx: TyCtxt, instance: Instance) -> bool {
    let stubs = StubMap::default();
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return false;
    }
    if !rustc_internal::internal(tcx, instance.def.def_id()).is_local() {
        return false;
    }
    let Some(body) = instance.body() else { return false };
    walk_verdict(tcx, instance, &body, &stubs) == Verdict::HasObligation
}

/// `from -> to` stub replacements for the unit under verification.
pub(crate) type StubMap = std::collections::HashMap<rustc_public::ty::FnDef, rustc_public::ty::FnDef>;

fn walk_verdict(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    stubs: &StubMap,
) -> Verdict {
    let mut walker = Walker {
        seen: HashSet::new(),
        bodies_visited: 0,
        blocks_visited: 0,
        stubs,
        tcx,
    };
    walker.seen.insert(instance_key(&instance));
    walker.walk(body)
}

/// A stable identity for an already-visited instance, so a recursive or
/// diamond call graph terminates.
fn instance_key(instance: &Instance) -> String {
    instance.mangled_name()
}

struct Walker<'s, 'tcx> {
    tcx: TyCtxt<'tcx>,
    seen: HashSet<String>,
    bodies_visited: usize,
    blocks_visited: usize,
    /// Resolved THROUGH, so the walk inspects the same program the encoder
    /// encodes. A stub can ADD an obligation the original lacks
    /// (`#[kani::stub(clean, panicking)]`), and walking the original would
    /// certify a harness whose emitted check fails.
    stubs: &'s StubMap,
}

impl Walker<'_, '_> {
    fn walk(&mut self, body: &Body) -> Verdict {
        self.bodies_visited += 1;
        if self.bodies_visited > MAX_BODIES {
            return Verdict::Unknown;
        }

        // An obligation SEEN settles the body and returns at once. Anything
        // merely UNREAD is remembered and the scan continues, because a later
        // block may still show an obligation outright.
        let mut acc = Verdict::Free;
        for block in body.blocks.iter() {
            self.blocks_visited += 1;
            if self.blocks_visited > MAX_BLOCKS {
                return acc.merge(Verdict::Unknown);
            }
            let step = match &block.terminator.kind {
                // Obligation SITES. This is the whole point of the walk.
                TerminatorKind::Assert { .. } => Verdict::HasObligation,

                // Reaching this is UB, and the encoder models it as an
                // obligation: `statement/terminator.rs` emits
                // `record_violation_guarded(true, "unreachable")` for it.
                TerminatorKind::Unreachable => Verdict::HasObligation,

                // Opaque to MIR: nothing here can vouch for what it does.
                TerminatorKind::InlineAsm { .. } => Verdict::Unknown,

                TerminatorKind::Call { func, target, .. } => {
                    // A call that never returns is a panic, an abort, or a
                    // diverging loop. `assert!(false)` lowers to a CALL to
                    // `core::panicking::panic`, not to an `Assert` terminator,
                    // so without this the walk followed it into a panic body
                    // that itself has no `Assert` and CERTIFIED a harness whose
                    // whole point was to fail. Structural, not a name list:
                    // anything `-> !` is refused whatever it is called.
                    if target.is_none() {
                        Verdict::HasObligation
                    } else {
                        self.walk_call(func, body)
                    }
                }

                // Drop glue can panic and can deref. Resolve it and walk it
                // like any other call; refuse when it cannot be resolved.
                TerminatorKind::Drop { place, .. } => match place.ty(body.locals()) {
                    Ok(place_ty) => {
                        let drop_instance = Instance::resolve_drop_in_place(place_ty);
                        if drop_instance.is_empty_shim() {
                            Verdict::Free
                        } else {
                            self.walk_instance(drop_instance)
                        }
                    }
                    Err(_) => Verdict::Unknown,
                },

                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Return => Verdict::Free,
            };
            if step != Verdict::Free {
                // Say WHICH terminator decided it. A refusal is otherwise
                // silent, and "why was this harness not certified?" is the
                // only question worth asking of a `[AY:VACUOUS:no-checks]`
                // row.
                let kind = match &block.terminator.kind {
                    TerminatorKind::Assert { .. } => "Assert",
                    TerminatorKind::Unreachable => "Unreachable",
                    TerminatorKind::InlineAsm { .. } => "InlineAsm",
                    TerminatorKind::Call { target: None, .. } => "Call(diverging)",
                    TerminatorKind::Call { .. } => "Call",
                    TerminatorKind::Drop { .. } => "Drop",
                    _ => "other",
                };
                tracing::debug!(
                    ?step,
                    terminator = kind,
                    "obligation-free walk: block decided the verdict"
                );
            }
            if step == Verdict::HasObligation {
                return Verdict::HasObligation;
            }
            acc = acc.merge(step);
        }
        acc
    }

    fn walk_call(&mut self, func: &rustc_public::mir::Operand, body: &Body) -> Verdict {
        let Ok(func_ty) = func.ty(body.locals()) else {
            return Verdict::Unknown;
        };
        // Only a direct, fully-monomorphized callee can be walked. A function
        // pointer or a `dyn` receiver is exactly the case where the walk
        // cannot see the callee.
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return Verdict::Unknown;
        };
        // Follow the stub, when this unit stubs this callee.
        let def = self.stubs.get(&def).copied().unwrap_or(def);
        let Some(instance) = Instance::resolve(def, &args).into_option() else {
            return Verdict::Unknown;
        };
        // A `dyn` receiver picks its callee at run time — but when the trait has
        // exactly ONE non-blanket concrete impl, it is decided statically.
        // `try_devirtualize` is the encoder's own resolver and REFUSES every
        // ambiguous case (blanket impls, generic impls, more than one
        // candidate) by returning None, so this can only narrow an `Unknown`
        // into a real body — it never guesses one. Without it a harness whose
        // only call is `(x as &dyn Super).method()` on a single-impl trait was
        // uncertifiable and reported VACUOUS despite genuinely having nothing
        // to prove (`kani/DynTrait/upcast.rs`).
        if matches!(instance.kind, InstanceKind::Virtual { .. })
            && let Some(concrete) = crate::kani_middle::transform::inline::devirtualize::
                try_devirtualize(self.tcx, def, &args)
        {
            return self.walk_instance(concrete);
        }
        self.walk_instance(instance)
    }

    fn walk_instance(&mut self, instance: Instance) -> Verdict {
        // A virtual call's target is chosen at run time; the walk has no
        // single body to inspect. `walk_call` gets first refusal via
        // `try_devirtualize`, so reaching here means the callee is genuinely
        // undecided.
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return Verdict::Unknown;
        }
        // A shim with no body does nothing, so it has nothing to prove.
        if instance.is_empty_shim() {
            return Verdict::Free;
        }
        if !self.seen.insert(instance_key(&instance)) {
            // Already visited on this walk. Its own scan reported whatever it
            // holds; revisiting cannot add a sighting.
            return Verdict::Free;
        }
        // Belt to the `target.is_none()` brace: a panic entry that a MIR
        // transform rewrote into a RETURNING call would slip past the
        // structural test, and certifying a panic is the one mistake that
        // turns this certificate into a false Safe.
        if is_panic_entry(&instance.name()) {
            return Verdict::HasObligation;
        }
        // trust-mc's own `library/std` REDEFINES `assert!` to call
        // `kani::assert`, whose body is an empty `Return`. Walking the plain
        // MIR therefore saw a harmless no-op where the encoder sees the
        // obligation, and certified `fn h() { inner() }` with
        // `fn inner() { assert!(false) }` inside it. The marker attribute is
        // what the encoder itself dispatches on, so reading the same thing
        // keeps the two from drifting apart.
        if let Some(marker) = attributes::fn_marker(instance.def) {
            return if kani_function_is_obligation_free(try_get_kani_function(&marker)) {
                Verdict::Free
            } else {
                Verdict::HasObligation
            };
        }
        // A body-less callee is an intrinsic, a foreign function, or something
        // the compiler declined to give us, and any of those could do
        // anything — with ONE exception the encoder itself declares.
        //
        // An atomic fence is dispatched as "no-op in sequential verification —
        // no memory effect, no return value" (`codegen_call_atomic`), so it
        // has nothing to prove. Reading the encoder's OWN classifier rather
        // than matching names here is deliberate: a private name list is free
        // to drift away from what the encoder actually does, which is exactly
        // how `assert!` came to be certified.
        let callee_name = instance.name();
        if matches!(
            crate::codegen_ay::chc::detect_atomic_intrinsic(&callee_name),
            Some(crate::codegen_ay::chc::AtomicKind::Fence)
        ) {
            return Verdict::Free;
        }
        // `libc::sysconf` — `codegen_call_sysconf` models it as an environment
        // query with no Rust-visible memory side effect, emitting a plain goto
        // with a fresh destination SPECIFICALLY so the call does not take the
        // generic undefined-foreign path "which introduces an `error` rule".
        // No obligation exists to drop.
        if crate::codegen_ay::chc::is_modeled_sysconf_path(&callee_name) {
            return Verdict::Free;
        }
        // `arith_offset` — the WRAPPING pointer offset. Computing an
        // out-of-bounds address is explicitly NOT UB for it (leaving the object
        // is permitted), and `codegen_arith_offset` emits no obligation. The
        // DEREFERENCE of such a pointer is a separate site with its own check,
        // which this hatch does not touch.
        if is_wrapping_arith_offset(&callee_name) {
            return Verdict::Free;
        }
        let Some(callee_body) = instance.body() else {
            // Name the callee that blocked certification. The walk otherwise
            // refuses in silence, and "which body-less callee?" is the only
            // question that matters when triaging a `[AY:VACUOUS:no-checks]`
            // row — it is what identified `libc::sysconf` and `arith_offset`.
            tracing::debug!(
                callee = %callee_name,
                "obligation-free walk: UNKNOWN — callee has no body"
            );
            return Verdict::Unknown;
        };
        self.walk(&callee_body)
    }
}

/// Is this Kani function safe to walk THROUGH — i.e. it cannot itself be an
/// obligation?
///
/// Fail-closed on purpose: an unrecognised marker, or one whose meaning is not
/// listed here, answers `false`. A new hook added upstream then costs parity
/// until it is classified, which is the correct direction to be wrong in.
fn kani_function_is_obligation_free(kani_fn: Option<KaniFunction>) -> bool {
    matches!(
        kani_fn,
        Some(KaniFunction::Hook(
            // Constrains the state; proves nothing.
            KaniHook::Assume
                // Reads a symbolic value or a pointer property.
                | KaniHook::AnyRaw
                | KaniHook::PointerObject
                | KaniHook::PointerOffset
                | KaniHook::IsAllocated
                // Contract/spec bookkeeping, not a check.
                | KaniHook::InitContracts
                | KaniHook::ModifiesFrameEnter
                | KaniHook::ModifiesFrameExit
                | KaniHook::ValueView
        ))
    )
}

/// The wrapping pointer offset, which is legal out of bounds and emits no
/// obligation. Matched by name because the CHC handler dispatches it through
/// a misc-intrinsic table rather than a shared predicate.
fn is_wrapping_arith_offset(name: &str) -> bool {
    // A monomorphized intrinsic carries its generic args:
    // `std::intrinsics::arith_offset::<u8>`. Strip them before matching, or
    // the predicate silently never fires.
    let base = name.split("::<").next().unwrap_or(name);
    base.ends_with("::arith_offset") || base == "arith_offset"
}

/// Entry points into the panic/abort machinery.
///
/// Reaching one IS the obligation — it is what a failed `assert!`, a failed
/// bounds check, or an `unwrap` on `None` calls.
fn is_panic_entry(name: &str) -> bool {
    const NEEDLES: &[&str] = &[
        "core::panicking::",
        "std::panicking::",
        "rust_begin_unwind",
        "begin_panic",
        "panic_fmt",
        "panic_nounwind",
        "panic_bounds_check",
        "panic_misaligned_pointer_dereference",
        "panic_null_pointer_dereference",
        "unreachable_unchecked",
        "::abort",
    ];
    NEEDLES.iter().any(|needle| name.contains(needle))
}

#[cfg(test)]
mod tests {
    use super::is_panic_entry;

    #[test]
    fn test_is_panic_entry_matches_the_machinery_asserts_lower_to() {
        for name in [
            "core::panicking::panic",
            "core::panicking::panic_fmt",
            "core::panicking::assert_failed::<u32, u32>",
            "std::panicking::begin_panic::<&str>",
            "rust_begin_unwind",
            "core::panicking::panic_bounds_check",
            "std::process::abort",
        ] {
            assert!(is_panic_entry(name), "{name} should be recognised as a panic entry");
        }
    }

    #[test]
    fn test_obligation_hooks_are_never_walked_through() {
        use super::kani_function_is_obligation_free;
        use trust_mc_kani_types::kani_functions::{KaniFunction, KaniHook};

        for hook in [
            KaniHook::Assert,
            KaniHook::Check,
            KaniHook::Cover,
            KaniHook::Panic,
            KaniHook::SafetyCheck,
            KaniHook::SafetyCheckNoAssume,
            KaniHook::UnsupportedCheck,
            KaniHook::UntrackedDeref,
        ] {
            assert!(
                !kani_function_is_obligation_free(Some(KaniFunction::Hook(hook))),
                "{hook:?} IS an obligation — walking through it certifies a harness \
                 whose only check is the one being skipped"
            );
        }
        // An unrecognised marker must fail closed.
        assert!(!kani_function_is_obligation_free(None));
    }

    #[test]
    fn test_assume_and_friends_are_walked_through() {
        use super::kani_function_is_obligation_free;
        use trust_mc_kani_types::kani_functions::{KaniFunction, KaniHook};

        for hook in [KaniHook::Assume, KaniHook::AnyRaw, KaniHook::PointerObject] {
            assert!(
                kani_function_is_obligation_free(Some(KaniFunction::Hook(hook))),
                "{hook:?} proves nothing, so it must not block certification"
            );
        }
    }

    #[test]
    fn test_wrapping_arith_offset_matches_the_MONOMORPHIZED_name() {
        use super::is_wrapping_arith_offset;
        // A monomorphized intrinsic carries generic args. Matching the bare
        // path silently never fired, and `arith-offset-overflow/main.rs`
        // stayed vacuous with the hatch apparently in place.
        assert!(is_wrapping_arith_offset("std::intrinsics::arith_offset::<u8>"));
        assert!(is_wrapping_arith_offset("core::intrinsics::arith_offset"));
        assert!(!is_wrapping_arith_offset("std::intrinsics::offset::<u8>"));
        assert!(!is_wrapping_arith_offset("my_crate::arith_offset_helper"));
    }

    #[test]
    fn test_is_panic_entry_does_not_swallow_ordinary_callees() {
        for name in [
            "core::str::<impl str>::as_bytes",
            "std::ptr::NonNull::<T>::cast",
            "my_crate::compute_total",
            "core::mem::replace::<u32>",
        ] {
            assert!(!is_panic_entry(name), "{name} is not a panic entry");
        }
    }
}
