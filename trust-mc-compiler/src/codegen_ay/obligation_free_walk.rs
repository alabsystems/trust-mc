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
//!
//! # Obligation sites are STATEMENTS as well as terminators
//!
//! Until 2026-09-12 the walk read terminators only: `Assert`, a diverging
//! `Call`, `Unreachable`, and whatever a callee held. That is the shape a
//! SAFE harness takes — `a + b` is an `Assert` on the overflow flag, `v[i]` an
//! `Assert` on the bound, `*p` an `Assert` on null and alignment — but it is
//! not what the encoder checks. Its obligations sit on statements too:
//! `BinOp::AddUnchecked` (`emit_overflow_check`), `BinOp::Div` / `Rem`
//! (`emit_division_by_zero_check`), `BinOp::Offset` (`emit_offset_*_check`),
//! a raw-pointer `Deref` projection (`emit_raw_ptr_deref_checks`), a signed
//! `UnOp::Neg` (`emit_neg_overflow_check`), the `CopyNonOverlapping`
//! intrinsic (`codegen_copy_nonoverlapping`). rustc lowers intrinsics to
//! exactly these (`LowerIntrinsics`), core's own MIR is compiled without the
//! debug assertions that add the `Assert`s, and `--prove-safety-only` turns
//! them off for the harness crate. A certificate that could not see those
//! sites was one the driver could not let a verdict rest on (D16). It counts
//! them now: [`statement_verdict`] mirrors the encoder's emitters site for
//! site, and every rvalue, cast or projection it does not recognise is
//! [`Unknown`](Verdict::Unknown).

use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;

use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    BinOp, Body, CastKind, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
    Statement, StatementKind, TerminatorKind, UnOp,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use trust_mc_codegen_shared::IntoOption;
use trust_mc_kani_types::kani_functions::{KaniFunction, KaniHook, try_get_kani_function};

use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::rustc_internal;

use crate::kani_middle::attributes;

/// Intrinsics with no obligation site and no write: total, with no UB
/// precondition (their checked forms, `unchecked_*`, `exact_div`,
/// `ctlz_nonzero` / `cttz_nonzero`, are not here), so the encoder emits no
/// check for a call of one. One list, read by this walk and by Rule D's region
/// scan (`chc::call::inline_walk_guard::region_may_check_or_write`).
pub(crate) const OBLIGATION_FREE_INTRINSICS: &[&str] = &[
    "black_box",
    "ctpop",
    "ctlz",
    "cttz",
    "bswap",
    "bitreverse",
    "rotate_left",
    "rotate_right",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_mul",
    "add_with_overflow",
    "sub_with_overflow",
    "mul_with_overflow",
    "saturating_add",
    "saturating_sub",
    "three_way_compare",
    "size_of",
    "align_of",
    "min_align_of",
    "needs_drop",
    "type_id",
    "type_name",
    "likely",
    "unlikely",
    "cold_path",
    "ub_checks",
];

/// Whether `instance` is an intrinsic in [`OBLIGATION_FREE_INTRINSICS`].
pub(crate) fn is_obligation_free_intrinsic(instance: &Instance) -> bool {
    instance
        .intrinsic_name()
        .is_some_and(|name| OBLIGATION_FREE_INTRINSICS.contains(&name.as_str()))
}

/// Bodies the walk will visit before giving up. A harness that reaches more
/// code than this is not the `fn check() {}` shape this certificate is for,
/// and refusing it costs only parity.
const MAX_BODIES: usize = 256;

/// Blocks the walk will visit before giving up, summed across all bodies.
const MAX_BLOCKS: usize = 20_000;

/// How much code one walk reads before it gives up ([`MAX_BODIES`],
/// [`MAX_BLOCKS`]); a test passes a smaller one to exercise the limit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct WalkBudget {
    pub(crate) bodies: usize,
    pub(crate) blocks: usize,
}

impl WalkBudget {
    pub(crate) const DEFAULT: WalkBudget = WalkBudget { bodies: MAX_BODIES, blocks: MAX_BLOCKS };
}

/// What the walk could establish about a body's obligation sites.
///
/// Three-valued on purpose. "Not provably obligation-free" and "provably HAS
/// an obligation" are different facts and have different consumers:
///
/// * the vacuity certificate may act only on [`Free`](Verdict::Free) — anything
///   less must fail closed;
/// * so may the CHC walker's nested-call fallback (Rule D, design
///   trust-mc-reds-final §4.1): its value havoc stays a sound havoc only for a
///   callee certified `Free`; an obligation sighted and "could not tell" both
///   book the lost effect fail-closed. (Before Rule D it acted on a POSITIVE
///   sighting in the crate under verification only, so an `Unknown` callee's
///   obligations were blessed away.) A callee of another crate gets no finer
///   reading there: the merge of fix/chc-walker-fail-closed dropped the
///   branch's, which counted only the panics of a safe foreign callee
///   (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: the merge
///   with main's Rule D").
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
    walk_verdict(tcx, instance, body, stubs, trust_no_callee) == Verdict::Free
}

/// [`body_is_transitively_obligation_free`], with every callee `trusted`
/// accepts counted [`Verdict::Free`] without being walked. For a caller that
/// asks "can this body fail a check?" rather than "does it hold a check
/// site?": a total std function such as `str::chars` holds offset sites the
/// encoder checks, and none of them can fail for a valid argument.
pub(crate) fn body_is_transitively_obligation_free_trusting(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    stubs: &StubMap,
    trusted: fn(&Instance) -> bool,
) -> bool {
    walk_verdict(tcx, instance, body, stubs, trusted) == Verdict::Free
}

fn trust_no_callee(_: &Instance) -> bool {
    false
}

/// The verdict of the REGION of `body` reachable from `start` along
/// normal-path successors (unwind cleanups are not followed: a panic is an
/// error, not a path verification continues), by the same rules as a whole
/// body, callees walked through. A block `is_dead` says rustc proved
/// unreachable is skipped. Rule D's predicate
/// (`chc::call::inline_walk_guard::region_may_check_or_write`) reads it: a
/// region the walker replaces by nothing loses an obligation unless this is
/// [`Verdict::Free`].
pub(crate) fn region_verdict(
    tcx: TyCtxt<'_>,
    body: &Body,
    start: usize,
    is_dead: impl Fn(usize) -> bool,
) -> Verdict {
    region_verdict_discharging(tcx, body, start, is_dead, None)
}

/// Sites of the REGION's own body (not of the callees it reaches) proved to
/// hold on every path: a statement whose every obligation is discharged, an
/// `Assert` whose condition is proved to equal its expectation (the CHC
/// walker's interval facts, `codegen_call_virtual_inline/region_intervals.rs`).
/// Dropping a check that cannot fail loses nothing, so such a site is not an
/// obligation of the region. Only a statement the walk SIGHTS is read through
/// `statement` (a `HasObligation` turned `Free`); one it cannot vouch for
/// stays `Unknown`, so the predicate must answer `true` only for a statement
/// whose sole obligations are the discharged ones.
pub(crate) struct RegionDischarge<'a> {
    pub(crate) statement: &'a dyn Fn(&Statement) -> bool,
    pub(crate) assert_holds: &'a dyn Fn(&rustc_public::mir::Operand, bool) -> bool,
}

/// [`region_verdict`], with the region body's own discharged sites
/// ([`RegionDischarge`]) not counted.
pub(crate) fn region_verdict_discharging(
    tcx: TyCtxt<'_>,
    body: &Body,
    start: usize,
    is_dead: impl Fn(usize) -> bool,
    discharge: Option<&RegionDischarge<'_>>,
) -> Verdict {
    let stubs = StubMap::default();
    let mut walker = Walker::new(tcx, &stubs, WalkMode::Full);
    walker.bodies_visited = 1;
    let exempt_unreachable = HashSet::new();
    let mut seen_blocks = HashSet::new();
    let mut stack = vec![start];
    let mut acc = Verdict::Free;
    while let Some(bb) = stack.pop() {
        if !seen_blocks.insert(bb) || is_dead(bb) {
            continue;
        }
        let Some(block) = body.blocks.get(bb) else {
            return acc.merge(Verdict::Unknown);
        };
        match walker.block_discharging(bb, block, body, &exempt_unreachable, discharge) {
            Verdict::HasObligation => return Verdict::HasObligation,
            step => acc = acc.merge(step),
        }
        match &block.terminator.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::Call { target: Some(target), .. } => stack.push(*target),
            TerminatorKind::SwitchInt { targets, .. } => {
                stack.extend(targets.branches().map(|(_, bb)| bb));
                stack.push(targets.otherwise());
            }
            TerminatorKind::InlineAsm { destination: Some(target), .. } => stack.push(*target),
            _ => {}
        }
    }
    acc
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
/// DEPENDENCY's code is missed by THIS sighting. The CHC walker's nested-call
/// fallback does not rely on it: under Rule D it books every callee it cannot
/// certify inert (`terminator_exec.rs`, `nested_callee_is_certified_inert`).
///
/// `stubs` is the unit's stub map: callees resolve through it, so the walk
/// sees the body the unit actually runs.
///
/// THE BUDGET IS NOT EVIDENCE. A walk that runs out of its [`MAX_BODIES`] /
/// [`MAX_BLOCKS`] before it could finish counts as a sighting: the unread
/// rest of the call graph may hold the obligation, and "too much code to
/// read" is a cost limit, not a finding that nothing is there. It used to
/// answer `false` (the walk's `Unknown`), so a local callee whose `assert!`
/// sat past 256 obligation-free bodies kept the `nested_call_overapprox`
/// blessing and its havoc proved the harness
/// (`tools/soundness-duals/walker_obligation_budget_dual.rs`). The other
/// `Unknown`s (an absent body, an rvalue the walk does not classify) keep the
/// documented "could not tell" blessing: those are shapes the walk read to
/// the end and could not vouch for, not code it never looked at. Every
/// obligation site in any crate is a sighting in this walk, so a callee
/// reaching real standard-library code is sighted long before the budget.
pub(crate) fn body_has_visible_obligation(
    tcx: TyCtxt,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    body_has_visible_obligation_within(tcx, instance, stubs, WalkBudget::DEFAULT)
}

/// [`body_has_visible_obligation`] with an explicit [`WalkBudget`].
pub(crate) fn body_has_visible_obligation_within(
    tcx: TyCtxt,
    instance: Instance,
    stubs: &StubMap,
    budget: WalkBudget,
) -> bool {
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return false;
    }
    if !rustc_internal::internal(tcx, instance.def.def_id()).is_local() {
        return false;
    }
    let Some(body) = instance.callee_body() else { return false };
    let mut walker = Walker::new(tcx, stubs, WalkMode::Full);
    walker.budget = budget;
    walker.seen.insert(instance_key(&instance));
    let verdict = walker.walk(&body);
    if walker.budget_exhausted && verdict != Verdict::HasObligation {
        tracing::debug!(
            callee = %instance.name(),
            bodies = walker.bodies_visited,
            blocks = walker.blocks_visited,
            "obligation walk: budget exhausted before the walk finished; counted as a sighting"
        );
        return true;
    }
    verdict == Verdict::HasObligation
}

/// What the walk establishes about `instance`: its own body and every body
/// reachable from it, in ANY crate (unlike [`body_has_visible_obligation`]),
/// read with the CHC walker's semantics.
///
/// For a caller that must decide whether a callee it abandons CAN carry an
/// obligation the walker would have checked: anything but [`Verdict::Free`]
/// means it may (a positive sighting, or a body the walk could not read to
/// the end). Two sites the certificate counts are not counted here, because
/// the walker never records a check for them when it does walk the body
/// (`Walker::walker_semantics`): an `Unreachable` block reached only as the
/// `otherwise` of a SwitchInt no encodable value selects (an exhaustive
/// `match` on a data-carrying enum, [`switch_otherwise_is_invalid_only`]),
/// and a call to an intrinsic Kani checks nothing for
/// ([`is_obligation_free_intrinsic`]).
///
/// `stubs` is the unit's stub map; `instance` itself must already be the one
/// the unit runs ([`resolve_through_stubs`]).
pub(crate) fn instance_obligation_verdict(
    tcx: TyCtxt<'_>,
    instance: Instance,
    stubs: &StubMap,
) -> Verdict {
    let mut walker = Walker::new(tcx, stubs, WalkMode::Full);
    walker.walker_semantics = true;
    walker.walk_instance(instance)
}

/// Can a SAFE callee in another crate fail for its caller, when a model that
/// keeps only the call's value takes the call over?
///
/// Its consumer is [`callee_may_fail_for_caller`], the statement-path pattern
/// models' gate. (It was also the CHC walker's nested-call fallback's, until
/// the merge of fix/chc-walker-fail-closed with Rule D: see LIMIT below.) A
/// model that keeps the call's value drops every check the callee would have
/// made. For a safe function in another crate that is exactly:
///
/// * the checks of the crate's OWN code it reaches: a closure handed to
///   `Option::map`, a trait impl behind an adapter (every obligation site
///   there is sighted, as in the certificate);
/// * its PANICS, at any depth: an `Assert` terminator, a diverging call, a
///   panic entry, a Kani assertion. They are how a safe function reports a
///   bad argument, and the argument decides whether they fire:
///   `Option::expect` on `None` in its own body, `slice::windows(0)` one call
///   down in `Option::expect`, `StepBy::new`'s `assert!(step != 0)`, the
///   bounds panic several calls below `Index::index` for `&s[..w]`;
/// * whatever the walk cannot follow, fail-closed: an indirect call (a
///   function pointer, a `dyn` method it cannot devirtualize), which may
///   land in the crate's code or in a panicking function, an unresolvable
///   callee, and the walk budget.
///
/// NOT counted are the undefined-behaviour sites inside the other crate's
/// bodies (a raw-pointer access, an unchecked operation, `assume`,
/// `Unreachable`): a safe function cannot reach UB for any argument, so
/// those checks hold whatever the caller passes, and counting them is what
/// failed the correct `dual_bounded_any_vec_valid.rs` when the sighting was
/// crate-blind. A body-less callee (an intrinsic, a foreign function) does
/// not panic.
///
/// LIMIT: "for any argument" holds only while the argument's invariants do.
/// Once unsafe code has broken one (`Vec::set_len` past the capacity), the
/// callee's UB checks can fail, and Kani checks them; that is why the
/// nested-call fallback no longer uses this walk. Measured 2026-10-14 for the
/// pattern models' shapes (`iter().copied().collect()`, `clone`, slice
/// index, `last`, a `for` over `iter()` after `set_len(4)` on a capacity-2
/// `Vec`): Kani FAILS each, and the CHC lane reports them VACUOUS (its `Vec`
/// model's invariant contradicts the state), never SUCCESSFUL.
///
/// Replaces the two narrower sightings of 2026-09-26 (the crate's code only,
/// plus the callee's own body only), which blessed the deeper panics
/// (docs/chc-hole-fix-designs-2026-09-24.md, "Walker fail-closed: review
/// round").
pub(crate) fn safe_foreign_callee_may_fail(
    tcx: TyCtxt<'_>,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    let mut walker = Walker::new(tcx, stubs, WalkMode::SafeForeignCallee);
    walker.walker_semantics = true;
    walker.in_local_body = false;
    walker.walk_instance(instance) == Verdict::HasObligation
}

/// Can a callee that a statement-path PATTERN MODEL takes over (the struct
/// accessor, iter-collect and passthrough dispatchers, which run after the
/// fn-inline walk declined the call and state only the pattern they match)
/// fail for its caller? The [`safe_foreign_callee_may_fail`] walk from any
/// root: every obligation site in the crate's own bodies (a local root's
/// included), panics at any depth in other crates, the preconditions of an
/// unsafe foreign function the crate's code calls, and, fail-closed, whatever
/// the walk cannot follow or finish.
pub(crate) fn callee_may_fail_for_caller(
    tcx: TyCtxt<'_>,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    safe_foreign_callee_may_fail(tcx, instance, stubs)
}

/// The instance the unit RUNS for a call of `def` with `args`: the stub's,
/// when the unit stubs `def` (`#[kani::stub]`) or the impl item a trait-method
/// call of `def` resolves to (`Clone::clone` on `Foo` runs a stubbed
/// `<Foo as Clone>::clone`), else `def`'s own.
pub(crate) fn resolve_through_stubs(
    def: rustc_public::ty::FnDef,
    args: &rustc_public::ty::GenericArgs,
    stubs: &StubMap,
) -> Option<Instance> {
    if let Some(stubbed) =
        crate::kani_middle::transform::stubbed_callee_instance(stubs, def, args, false)
    {
        return Some(stubbed);
    }
    Instance::resolve(def, args).into_option()
}

/// Does `instance`'s body, or any body it reaches (in any crate, through the
/// unit's stub map), hold a loop Kani unwinds: a cycle in a body's normal
/// control flow, or a call back into a function the walk is inside
/// (recursion)? `true` wherever the walk cannot tell: an indirect call it
/// cannot devirtualize, an unresolvable callee, the budget. A body-less
/// callee (an intrinsic, a foreign function) holds no loop Kani unwinds, and
/// neither does a Kani marker function; a diverging call (a panic) ends
/// Kani's path, so what it reaches is not followed.
///
/// For a caller that abandons code under a DECLARED unwind bound with
/// unwinding assertions on: a loop in that code can fail Kani's unwinding
/// assertion, a check like any other
/// (`chc/call/codegen_call_virtual_inline/uncertified_check.rs`,
/// `region_may_fail_unwinding_assertion`).
pub(crate) fn instance_may_loop(tcx: TyCtxt<'_>, instance: Instance, stubs: &StubMap) -> bool {
    LoopWalk { tcx, stubs, seen: HashSet::new(), on_stack: HashSet::new(), bodies: 0, blocks: 0 }
        .instance(instance)
}

/// The state of one [`instance_may_loop`] walk.
struct LoopWalk<'s, 'tcx> {
    tcx: TyCtxt<'tcx>,
    stubs: &'s StubMap,
    seen: HashSet<String>,
    on_stack: HashSet<String>,
    bodies: usize,
    blocks: usize,
}

impl LoopWalk<'_, '_> {
    fn instance(&mut self, instance: Instance) -> bool {
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return true;
        }
        if instance.is_empty_shim() {
            return false;
        }
        let key = instance_key(&instance);
        if self.on_stack.contains(&key) {
            return true;
        }
        if !self.seen.insert(key.clone()) {
            return false;
        }
        if attributes::fn_marker(instance.def).is_some() || is_panic_entry(&instance.name()) {
            return false;
        }
        if runs_kani_memcmp_loop(&instance) {
            tracing::debug!(instance = %instance.name(), "loop walk: Kani runs it as memcmp, a loop");
            return true;
        }
        let Some(body) = instance.callee_body() else {
            tracing::debug!(instance = %instance.name(), kind = ?instance.kind, "loop walk: body-less, no loop");
            return false;
        };
        self.bodies += 1;
        self.blocks += body.blocks.len();
        if self.bodies > MAX_BODIES || self.blocks > MAX_BLOCKS {
            return true;
        }
        if !crate::codegen_ay::loop_unroll::Cfg::from_body(&body).is_acyclic() {
            return true;
        }
        self.on_stack.insert(key.clone());
        let found = self.calls_may_loop(&body);
        self.on_stack.remove(&key);
        found
    }

    fn calls_may_loop(&mut self, body: &Body) -> bool {
        for block in &body.blocks {
            let found = match &block.terminator.kind {
                TerminatorKind::Call { func, target: Some(_), .. } => {
                    self.call_may_loop(func, body)
                }
                TerminatorKind::Drop { place, .. } => match place.ty(body.locals()) {
                    Ok(ty) => match mono_ty::drop_in_place(ty) {
                        None => true,
                        Some(glue) => !glue.is_empty_shim() && self.instance(glue),
                    },
                    Err(_) => true,
                },
                _ => false,
            };
            if found {
                return true;
            }
        }
        false
    }

    fn call_may_loop(&mut self, func: &Operand, body: &Body) -> bool {
        let Ok(func_ty) = func.ty(body.locals()) else {
            return true;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return true;
        };
        let Some(instance) = resolve_through_stubs(def, &args, self.stubs) else {
            return true;
        };
        if matches!(instance.kind, InstanceKind::Virtual { .. })
            && let Some(concrete) =
                crate::kani_middle::transform::inline::devirtualize::try_devirtualize(
                    self.tcx, def, &args,
                )
        {
            return self.instance(concrete);
        }
        self.instance(instance)
    }
}

/// Does Kani run `instance` as CBMC's builtin `memcmp`, a loop over the
/// bytes it unwinds once per byte? `raw_eq` (array `==` of bytewise-comparable
/// elements, `SpecArrayEq`) and `compare_bytes` (slice `==` and `[u8]` /
/// `str` ordering, `SlicePartialEq` / `SliceOrd`) are body-less intrinsics
/// (Kani `codegen_intrinsic_raw_eq`, `codegen_compare_bytes`), so the walk
/// read them as loop-free, and `[x, 7u32] == [x, 7]` under `unwind(3)`, a
/// `Vec<&str>::sort` and `dedup` verified clean where Kani fails `unwinding
/// assertion loop 0` in `memcmp` (walker fail-closed repair round 5,
/// `model_call_unwind_memcmp_dual.rs`). `raw_eq` of a zero-sized value is
/// `true` without the call.
fn runs_kani_memcmp_loop(instance: &Instance) -> bool {
    if !matches!(instance.kind, InstanceKind::Intrinsic) {
        return false;
    }
    let Some(intrinsic) = instance.intrinsic_name() else {
        return false;
    };
    match intrinsic.as_str() {
        "compare_bytes" => true,
        "raw_eq" => {
            let compared = instance.args().0.iter().find_map(|arg| match arg {
                rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                _ => None,
            });
            !compared
                .is_some_and(|ty| ty.layout().is_ok_and(|layout| layout.shape().size.bytes() == 0))
        }
        _ => false,
    }
}

/// Can `instance`, or anything it reaches (in any crate, through the unit's
/// stub map), manufacture a value its type does not allow: a fieldless
/// enum's out-of-range discriminant? Only through a transmute, a read or
/// write through a raw pointer, a union field, a `copy_nonoverlapping`, inline
/// asm, or a callee the walk cannot read (a body-less function other than a
/// pure arithmetic intrinsic, an indirect call, the budget). Every other MIR
/// statement builds values of their own types: an enum constant, an
/// aggregate, a copy of a valid value.
///
/// For a caller that replaces such a callee's result by a fresh value
/// (`chc/call/codegen_call_virtual_inline/terminator_exec.rs`, the
/// nested-call fallback): when this is `false`, the value the program sees is
/// valid for its type, and the fresh value may be constrained to that.
pub(crate) fn instance_may_forge_invalid_value(
    tcx: TyCtxt<'_>,
    instance: Instance,
    stubs: &StubMap,
) -> bool {
    ForgeWalk { tcx, stubs, carry: None, seen: HashSet::new(), bodies: 0, blocks: 0 }
        .instance(instance)
}

/// Can the value a call to `instance` with `arg_tys` returns be anything but
/// a valid value of `target`, a fieldless enum the callee returns: can the
/// callee forge one ([`instance_may_forge_invalid_value`]), or PASS ON one
/// its caller forged?
///
/// Passing on needs a way in: an argument whose type can hold a `target`
/// ([`ty_may_carry`]: by value, behind a reference, in an array, slice, tuple
/// or field; a `dyn`, closure or opaque type always may), or a constant
/// reference anywhere the callee reaches whose pointee can (a `static` the
/// harness may have written through a pointer). The forge walk alone
/// counted a copy of an argument, or a read through `&E`, as building a
/// value of its own type, so a helper returning its enum argument passed an
/// invalid value its caller wrote through `*mut u8` on as a valid one, and
/// the exhaustive `otherwise` arm's "unreachable code" check was assumed
/// away (walker fail-closed review 6 round 2, finding 2,
/// `rp1_forged_enum.rs`).
pub(crate) fn call_may_return_invalid_value(
    tcx: TyCtxt<'_>,
    instance: Instance,
    arg_tys: &[Ty],
    target: Ty,
    stubs: &StubMap,
) -> bool {
    arg_tys.iter().any(|ty| ty_may_carry(*ty, target))
        || ForgeWalk { tcx, stubs, carry: Some(target), seen: HashSet::new(), bodies: 0, blocks: 0 }
            .instance(instance)
}

/// Can a value of type `ty` hold a value of type `target`: be it, or hold one
/// behind a reference or raw pointer, in an array, slice, tuple or ADT field?
/// `true` for a type this cannot see into (`dyn`, a closure or coroutine, a
/// foreign or unnormalized type) or past a depth of 16.
pub(crate) fn ty_may_carry(ty: Ty, target: Ty) -> bool {
    fn go(ty: Ty, target: Ty, seen: &mut HashSet<Ty>, depth: usize) -> bool {
        if ty == target {
            return true;
        }
        if depth > 16 {
            return true;
        }
        match ty.kind() {
            TyKind::RigidTy(rigid) => match rigid {
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Str
                | RigidTy::Never
                | RigidTy::FnDef(..)
                | RigidTy::FnPtr(..) => false,
                RigidTy::Ref(_, inner, _)
                | RigidTy::RawPtr(inner, _)
                | RigidTy::Array(inner, _)
                | RigidTy::Slice(inner) => go(inner, target, seen, depth + 1),
                RigidTy::Tuple(elems) => {
                    elems.iter().any(|elem| go(*elem, target, seen, depth + 1))
                }
                RigidTy::Adt(def, args) => {
                    if !seen.insert(ty) {
                        return false;
                    }
                    def.variants_iter().any(|variant| {
                        variant.fields().iter().any(|field| {
                            mono_ty::field_ty(field, &args)
                                .is_none_or(|field_ty| go(field_ty, target, seen, depth + 1))
                        })
                    })
                }
                _ => true,
            },
            _ => true,
        }
    }
    go(ty, target, &mut HashSet::new(), 0)
}

/// The state of one [`instance_may_forge_invalid_value`] walk.
struct ForgeWalk<'s, 'tcx> {
    tcx: TyCtxt<'tcx>,
    stubs: &'s StubMap,
    /// [`call_may_return_invalid_value`]'s target: a constant reference
    /// whose pointee may carry it counts as forging.
    carry: Option<Ty>,
    seen: HashSet<String>,
    bodies: usize,
    blocks: usize,
}

impl ForgeWalk<'_, '_> {
    fn instance(&mut self, instance: Instance) -> bool {
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return true;
        }
        if instance.is_empty_shim() {
            return false;
        }
        if !self.seen.insert(instance_key(&instance)) {
            return false;
        }
        // Kani's own functions (`kani::any`, `assume`, `assert`) produce
        // valid values or none.
        if attributes::fn_marker(instance.def).is_some() || is_panic_entry(&instance.name()) {
            return false;
        }
        if is_obligation_free_intrinsic(&instance) {
            return false;
        }
        let Some(body) = instance.callee_body() else {
            return true;
        };
        self.bodies += 1;
        self.blocks += body.blocks.len();
        if self.bodies > MAX_BODIES || self.blocks > MAX_BLOCKS {
            return true;
        }
        self.body(&body)
    }

    fn body(&mut self, body: &Body) -> bool {
        for block in &body.blocks {
            for stmt in &block.statements {
                let forges = match &stmt.kind {
                    StatementKind::Assign(place, rvalue) => {
                        place_may_forge(place, body) || rvalue_may_forge(rvalue, body, self.carry)
                    }
                    StatementKind::SetDiscriminant { place, .. } => place_may_forge(place, body),
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => true,
                    _ => false,
                };
                if forges {
                    return true;
                }
            }
            let forges = match &block.terminator.kind {
                TerminatorKind::InlineAsm { .. } => true,
                TerminatorKind::Call { func, args, destination, target, .. } => {
                    place_may_forge(destination, body)
                        || args.iter().any(|arg| operand_may_forge(arg, body, self.carry))
                        || (target.is_some() && self.call(func, body))
                }
                TerminatorKind::Drop { place, .. } => match place.ty(body.locals()) {
                    Ok(ty) => match mono_ty::drop_in_place(ty) {
                        None => true,
                        Some(glue) => !glue.is_empty_shim() && self.instance(glue),
                    },
                    Err(_) => true,
                },
                TerminatorKind::SwitchInt { discr, .. } => {
                    operand_may_forge(discr, body, self.carry)
                }
                TerminatorKind::Assert { cond, .. } => operand_may_forge(cond, body, self.carry),
                _ => false,
            };
            if forges {
                return true;
            }
        }
        false
    }

    fn call(&mut self, func: &Operand, body: &Body) -> bool {
        let Ok(func_ty) = func.ty(body.locals()) else {
            return true;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return true;
        };
        let Some(instance) = resolve_through_stubs(def, &args, self.stubs) else {
            return true;
        };
        if matches!(instance.kind, InstanceKind::Virtual { .. })
            && let Some(concrete) =
                crate::kani_middle::transform::inline::devirtualize::try_devirtualize(
                    self.tcx, def, &args,
                )
        {
            return self.instance(concrete);
        }
        self.instance(instance)
    }
}

/// A place that reads or writes through a raw pointer, or a union field.
fn place_may_forge(place: &Place, body: &Body) -> bool {
    for (idx, elem) in place.projection.iter().enumerate() {
        let base = Place { local: place.local, projection: place.projection[..idx].to_vec() };
        let Ok(base_ty) = base.ty(body.locals()) else {
            return true;
        };
        match (elem, base_ty.kind()) {
            (ProjectionElem::Deref, TyKind::RigidTy(RigidTy::Ref(..))) => {}
            (ProjectionElem::Deref, _) => return true,
            (ProjectionElem::Field(..), TyKind::RigidTy(RigidTy::Adt(def, _)))
                if def.kind() == rustc_public::ty::AdtKind::Union =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// A place [`place_may_forge`] refuses; with a `carry` target, also a
/// constant reference or pointer whose pointee may carry it
/// ([`call_may_return_invalid_value`]).
fn operand_may_forge(op: &Operand, body: &Body, carry: Option<Ty>) -> bool {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place_may_forge(place, body),
        Operand::Constant(constant) => carry.is_some_and(|target| match constant.ty().kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                ty_may_carry(pointee, target)
            }
            _ => false,
        }),
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

/// A transmute, or an operand or place [`place_may_forge`] refuses; `true`
/// for an rvalue this does not classify.
fn rvalue_may_forge(rvalue: &Rvalue, body: &Body, carry: Option<Ty>) -> bool {
    match rvalue {
        Rvalue::Cast(CastKind::Transmute, ..) => true,
        Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _) => {
            operand_may_forge(op, body, carry)
        }
        Rvalue::UnaryOp(_, op) => operand_may_forge(op, body, carry),
        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_may_forge(lhs, body, carry) || operand_may_forge(rhs, body, carry)
        }
        Rvalue::Aggregate(_, operands) => {
            operands.iter().any(|op| operand_may_forge(op, body, carry))
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::AddressOf(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => place_may_forge(place, body),
        #[cfg(not(trust_toolchain))]
        Rvalue::ShallowInitBox(op, _) => operand_may_forge(op, body, carry),
        #[cfg(not(trust_toolchain))]
        Rvalue::NullaryOp(_) => false,
        #[allow(unreachable_patterns)]
        _ => true,
    }
}

/// Blocks whose terminator is `Unreachable` and that no valid value reaches:
/// every edge into them (directly, or through one `Goto` block) is the
/// `otherwise` arm of a SwitchInt whose `otherwise` no valid value selects
/// ([`switch_otherwise_is_invalid_only`]): the arm rustc adds to an exhaustive
/// enum `match`, and a coroutine's invalid-state arm.
///
/// An `Unreachable` on an EXPLICIT arm is not among them, even on an enum:
/// `match o { Some(x) => x, None => unsafe { core::intrinsics::unreachable() } }`
/// reaches it with a valid `None`.
pub(crate) fn enum_exhaustive_unreachable_blocks(body: &Body) -> HashSet<usize> {
    let block_count = body.blocks.len();
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); block_count];
    for (bb, block) in body.blocks.iter().enumerate() {
        for succ in block.terminator.successors() {
            if succ < block_count && !preds[succ].contains(&bb) {
                preds[succ].push(bb);
            }
        }
    }
    // Is `pred`'s edge into `bb` the invalid-only `otherwise` of its switch,
    // and no explicit arm of it?
    let invalid_only_edge = |pred: usize, bb: usize| match &body.blocks[pred].terminator.kind {
        TerminatorKind::SwitchInt { discr, targets } => {
            targets.otherwise() == bb
                && targets.branches().all(|(_, target)| target != bb)
                && switch_otherwise_is_invalid_only(body, discr, targets)
        }
        _ => false,
    };
    let mut exempt = HashSet::new();
    for (bb, block) in body.blocks.iter().enumerate() {
        if !matches!(block.terminator.kind, TerminatorKind::Unreachable) || preds[bb].is_empty() {
            continue;
        }
        let only_invalid = preds[bb].iter().all(|&pred| {
            invalid_only_edge(pred, bb)
                || (matches!(body.blocks[pred].terminator.kind, TerminatorKind::Goto { .. })
                    && !preds[pred].is_empty()
                    && preds[pred].iter().all(|&p| invalid_only_edge(p, pred)))
        });
        if only_invalid {
            exempt.insert(bb);
        }
    }
    exempt
}

/// Does no value the CHC encoding can hold select the `otherwise` arm of a
/// SwitchInt on `discr` with `targets`? True when `discr` reads a local
/// assigned only by `Rvalue::Discriminant` of
///
/// * an enum with a DATA-CARRYING variant whose every variant has an explicit
///   arm (the explicit values are distinct discriminants, so as many values
///   as variants is all of them). Such an enum is a datatype sort
///   (`decl/codegen_types_adt_sort.rs` `translate_adt_sort`): every term of
///   it is one of its constructors, so its discriminant is always one of the
///   explicit values;
/// * a coroutine: its state is the compiler's, and the resume body's switch
///   names every state it can hold.
///
/// NOT a fieldless ("unit") enum. Those are raw bitvectors in the encoding,
/// and a value written through memory keeps whatever bits were written:
/// `*(&mut e as *mut E as *mut u8) = x` in the harness, then an exhaustive
/// `match e` in a walked body, reached Kani's "unreachable code" for
/// `x > 1`, and the walker, which kept this arm dead on the argument that
/// validity is checked where a value is BUILT ("invalid enum construction",
/// which covers a transmute but not a raw write), proved the harness clean
/// (`tools/soundness-duals/walker_invalid_enum_dual.rs`). The statement path
/// checks the arm; the walker now records its not-taken condition like any
/// other `Unreachable` arm, which a validly built value discharges.
pub(crate) fn switch_otherwise_is_invalid_only(
    body: &Body,
    discr: &Operand,
    targets: &rustc_public::mir::SwitchTargets,
) -> bool {
    let Some(source_ty) = enum_discriminant_source_ty(body, discr) else {
        return false;
    };
    match source_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == rustc_public::ty::AdtKind::Enum => {
            let unit_only = def.variants().iter().all(|variant| variant.fields().is_empty());
            let values: HashSet<u128> = targets.branches().map(|(value, _)| value).collect();
            !unit_only && values.len() >= def.num_variants()
        }
        TyKind::RigidTy(RigidTy::Coroutine(..)) => true,
        _ => false,
    }
}

/// The type whose discriminant the SwitchInt operand `discr` reads: `discr`
/// is a local assigned only by `Rvalue::Discriminant` in `body`, of places
/// of one type.
fn enum_discriminant_source_ty(body: &Body, discr: &Operand) -> Option<Ty> {
    let (Operand::Copy(place) | Operand::Move(place)) = discr else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    let mut source_ty: Option<Ty> = None;
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(dest, rvalue) = &stmt.kind
                && dest.local == place.local
            {
                let Rvalue::Discriminant(source) = rvalue else {
                    return None;
                };
                if !dest.projection.is_empty() {
                    return None;
                }
                let ty = source.ty(body.locals()).ok()?;
                if source_ty.is_some_and(|seen| seen != ty) {
                    return None;
                }
                source_ty = Some(ty);
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
            && destination.local == place.local
        {
            return None;
        }
    }
    source_ty
}

/// A statement with no effect the walker or the encoder models.
pub(crate) fn statement_is_inert(stmt: &Statement) -> bool {
    matches!(
        stmt.kind,
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(..)
            | StatementKind::ConstEvalCounter
    )
}

/// `vtable_size` / `vtable_align`: a read of the vtable a `DynMetadata`
/// points to. The CHC walker records no check for it (`leaf_models.rs`): in
/// the encoding a vtable pointer is a vtable identity minted at an unsize
/// coercion, never an address a program can forge without breaking a
/// `DynMetadata`'s validity invariant. Free under `walker_semantics` only;
/// the certificate still reads it as the body-less callee it is.
pub(crate) fn is_vtable_read_intrinsic(instance: &Instance) -> bool {
    matches!(instance.kind, InstanceKind::Intrinsic)
        && instance
            .intrinsic_name()
            .is_some_and(|name| matches!(name.as_str(), "vtable_size" | "vtable_align"))
}

/// `from -> to` stub replacements for the unit under verification.
pub(crate) type StubMap =
    std::collections::HashMap<rustc_public::ty::FnDef, rustc_public::ty::FnDef>;

fn walk_verdict(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    stubs: &StubMap,
    trusted: fn(&Instance) -> bool,
) -> Verdict {
    let mut walker = Walker::new(tcx, stubs, WalkMode::Full);
    walker.trusted = trusted;
    walker.seen.insert(instance_key(&instance));
    walker.walk(body)
}

/// A stable identity for an already-visited instance, so a recursive or
/// diamond call graph terminates.
fn instance_key(instance: &Instance) -> String {
    instance.mangled_name()
}

/// Which sites a walk sights where (see the public entry points).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WalkMode {
    /// Every obligation site in every body: the certificate,
    /// [`body_has_visible_obligation`], [`instance_obligation_verdict`].
    Full,
    /// [`safe_foreign_callee_may_fail`]: every site in the crate's own bodies;
    /// in other crates' bodies only panics; and anything the walk cannot
    /// follow.
    SafeForeignCallee,
}

struct Walker<'s, 'tcx> {
    tcx: TyCtxt<'tcx>,
    seen: HashSet<String>,
    bodies_visited: usize,
    blocks_visited: usize,
    /// How much code the walk reads ([`WalkBudget::DEFAULT`] but in tests).
    budget: WalkBudget,
    /// The walk stopped reading because it ran out of its [`WalkBudget`]
    /// (see [`body_has_visible_obligation`]).
    budget_exhausted: bool,
    /// Resolved THROUGH, so the walk inspects the same program the encoder
    /// encodes. A stub can ADD an obligation the original lacks
    /// (`#[kani::stub(clean, panicking)]`), and walking the original would
    /// certify a harness whose emitted check fails.
    stubs: &'s StubMap,
    /// Callees counted `Free` without a walk
    /// ([`body_is_transitively_obligation_free_trusting`]); none by default.
    trusted: fn(&Instance) -> bool,
    mode: WalkMode,
    /// Whether the body being walked belongs to the crate under verification
    /// (read in [`WalkMode::SafeForeignCallee`]).
    in_local_body: bool,
    /// [`WalkMode::SafeForeignCallee`]: inside an `unsafe` function of
    /// another crate called from the crate's own code, whose UB sites are the
    /// preconditions that code must meet: sight them as in a local body.
    in_unsafe_from_local: bool,
    /// Read sites as the CHC walker checks them ([`instance_obligation_verdict`]):
    /// an enum-exhaustive `Unreachable` block and a check-free intrinsic are
    /// not sites. Off for the certificate, which answers for the statement
    /// encoder.
    walker_semantics: bool,
}

impl<'s, 'tcx> Walker<'s, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, stubs: &'s StubMap, mode: WalkMode) -> Self {
        Walker {
            seen: HashSet::new(),
            bodies_visited: 0,
            blocks_visited: 0,
            budget: WalkBudget::DEFAULT,
            budget_exhausted: false,
            stubs,
            tcx,
            mode,
            in_local_body: true,
            in_unsafe_from_local: false,
            walker_semantics: false,
            trusted: trust_no_callee,
        }
    }

    /// Does an undefined-behaviour site (a statement site, `Unreachable`,
    /// inline asm) in the body being walked count? Always, except for a safe
    /// foreign callee's bodies outside the crate under verification (and not
    /// inside an `unsafe` function the crate's own code called).
    fn sights_ub_here(&self) -> bool {
        self.mode == WalkMode::Full || self.in_local_body || self.in_unsafe_from_local
    }

    /// What the walk answers where it cannot follow a call: `Unknown`, which
    /// is a SIGHTING for a safe foreign callee (fail-closed: the call may
    /// land in the crate's code or in a panicking function).
    fn blind(&self) -> Verdict {
        match self.mode {
            WalkMode::Full => Verdict::Unknown,
            WalkMode::SafeForeignCallee => Verdict::HasObligation,
        }
    }
}

impl Walker<'_, '_> {
    fn walk(&mut self, body: &Body) -> Verdict {
        self.bodies_visited += 1;
        if self.bodies_visited > self.budget.bodies {
            self.budget_exhausted = true;
            return self.blind();
        }
        let exempt_unreachable = if self.walker_semantics {
            enum_exhaustive_unreachable_blocks(body)
        } else {
            HashSet::new()
        };

        // An obligation SEEN settles the body and returns at once. Anything
        // merely UNREAD is remembered and the scan continues, because a later
        // block may still show an obligation outright.
        let mut acc = Verdict::Free;
        for (bb, block) in body.blocks.iter().enumerate() {
            let step = self.block(bb, block, body, &exempt_unreachable);
            if step == Verdict::HasObligation {
                return Verdict::HasObligation;
            }
            acc = acc.merge(step);
            if self.blocks_visited > self.budget.blocks {
                return acc;
            }
        }
        acc
    }

    /// The verdict of block `bb` of `body`: its statements, then its
    /// terminator (a callee or drop glue walked through). Counts against the
    /// block budget; `exempt_unreachable` are the enum-exhaustive
    /// `Unreachable` blocks the walker's reading does not count.
    fn block(
        &mut self,
        bb: usize,
        block: &rustc_public::mir::BasicBlock,
        body: &Body,
        exempt_unreachable: &HashSet<usize>,
    ) -> Verdict {
        self.block_discharging(bb, block, body, exempt_unreachable, None)
    }

    /// [`Self::block`], with `discharge`'s sites of this block not counted
    /// ([`RegionDischarge`]; the callees it reaches are walked in full).
    fn block_discharging(
        &mut self,
        bb: usize,
        block: &rustc_public::mir::BasicBlock,
        body: &Body,
        exempt_unreachable: &HashSet<usize>,
        discharge: Option<&RegionDischarge<'_>>,
    ) -> Verdict {
        self.blocks_visited += 1;
        if self.blocks_visited > self.budget.blocks {
            self.budget_exhausted = true;
            return self.blind();
        }
        let mut acc = Verdict::Free;
        {
            // STATEMENT sites first, in program order. See the module docs:
            // these are where the encoder's own checks live once rustc has
            // lowered the intrinsics, and a safe-code `Assert` is not always
            // in front of them.
            if self.sights_ub_here() {
                for stmt in &block.statements {
                    let mut step = statement_verdict(stmt, body);
                    if step == Verdict::HasObligation
                        && discharge.is_some_and(|d| (d.statement)(stmt))
                    {
                        step = Verdict::Free;
                    }
                    if step != Verdict::Free {
                        tracing::debug!(
                            ?step,
                            statement = ?stmt.kind,
                            "obligation-free walk: statement decided the verdict"
                        );
                    }
                    if step == Verdict::HasObligation {
                        return Verdict::HasObligation;
                    }
                    acc = acc.merge(step);
                }
            }
            let step = match &block.terminator.kind {
                // Obligation SITES. This is the whole point of the walk. An
                // `Assert` is a panic, which a safe foreign callee raises for
                // its caller too.
                TerminatorKind::Assert { cond, expected, .. } => {
                    if discharge.is_some_and(|d| (d.assert_holds)(cond, *expected)) {
                        Verdict::Free
                    } else {
                        Verdict::HasObligation
                    }
                }

                // Reaching this is UB, and the encoder models it as an
                // obligation: `statement/terminator.rs` emits
                // `record_violation_guarded(true, "unreachable")` for it. The
                // CHC walker does not for an enum-exhaustive arm
                // (`walker_semantics`), and a safe foreign callee never
                // reaches UB.
                TerminatorKind::Unreachable => {
                    if !self.sights_ub_here() || exempt_unreachable.contains(&bb) {
                        Verdict::Free
                    } else {
                        Verdict::HasObligation
                    }
                }

                // Opaque to MIR: nothing here can vouch for what it does.
                TerminatorKind::InlineAsm { .. } => {
                    if self.sights_ub_here() {
                        Verdict::Unknown
                    } else {
                        Verdict::Free
                    }
                }

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
                    Ok(place_ty) => match mono_ty::drop_in_place(place_ty) {
                        None => self.blind(),
                        Some(glue) if glue.is_empty_shim() => Verdict::Free,
                        Some(glue) => self.walk_instance(glue),
                    },
                    Err(_) => self.blind(),
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
            acc.merge(step)
        }
    }

    fn walk_call(&mut self, func: &rustc_public::mir::Operand, body: &Body) -> Verdict {
        let Ok(func_ty) = func.ty(body.locals()) else {
            return self.blind();
        };
        // Only a direct, fully-monomorphized callee can be walked. A function
        // pointer or a `dyn` receiver is exactly the case where the walk
        // cannot see the callee.
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return self.blind();
        };
        // Follow the stub, when this unit stubs this callee (directly, or the
        // impl item a trait-method call resolves to).
        let Some(instance) = resolve_through_stubs(def, &args, self.stubs) else {
            return self.blind();
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
            && let Some(concrete) =
                crate::kani_middle::transform::inline::devirtualize::try_devirtualize(
                    self.tcx, def, &args,
                )
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
            return self.blind();
        }
        // A shim with no body does nothing, so it has nothing to prove.
        if instance.is_empty_shim() {
            return Verdict::Free;
        }
        if (self.trusted)(&instance) {
            return Verdict::Free;
        }
        // What the callee's body sights depends, for a safe foreign callee,
        // on whether the crate's own code owes the preconditions of an
        // `unsafe` function on the way, so the visit is keyed by that too.
        let callee_local = rustc_internal::internal(self.tcx, instance.def.def_id()).is_local();
        let unsafe_from_local = self.in_unsafe_from_local
            || (self.in_local_body && !callee_local && instance_is_unsafe_fn(&instance));
        let key = match self.mode {
            WalkMode::Full => instance_key(&instance),
            WalkMode::SafeForeignCallee => {
                format!("{}#{unsafe_from_local}", instance_key(&instance))
            }
        };
        if !self.seen.insert(key) {
            // Already visited on this walk. Its own scan reported whatever it
            // holds; revisiting cannot add a sighting.
            return Verdict::Free;
        }
        // A safe foreign callee's `assert_unsafe_precondition!` checks guard
        // the UB preconditions of the unsafe operations inside it: behind
        // `check_library_ub()` / `check_language_ub()` (false in Kani and
        // here), and unable to fail for any argument of a sound safe function.
        // They panic through `panic_nounwind`, which would otherwise read as
        // an argument-dependent panic.
        if !self.sights_ub_here() && is_ub_precondition_check(&instance.name()) {
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
        // An intrinsic with no obligation site and no write
        // ([`OBLIGATION_FREE_INTRINSICS`]): nothing to check, in every
        // reading. A vtable read, for the CHC walker's reading
        // (`walker_semantics`) only. A safe foreign callee reaches no UB
        // through any intrinsic, and none of these panics.
        if is_obligation_free_intrinsic(&instance)
            || (self.walker_semantics && is_vtable_read_intrinsic(&instance))
        {
            return Verdict::Free;
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
        let Some(callee_body) = instance.callee_body() else {
            // Name the callee that blocked certification. The walk otherwise
            // refuses in silence, and "which body-less callee?" is the only
            // question that matters when triaging a `[AY:VACUOUS:no-checks]`
            // row — it is what identified `libc::sysconf` and `arith_offset`.
            tracing::debug!(
                callee = %callee_name,
                "obligation-free walk: UNKNOWN — callee has no body"
            );
            // Unknown for the certificate. A safe foreign callee's body-less
            // callee (an intrinsic, a foreign function) raises no panic, and
            // its UB sites are not sightings there; from the crate's own code
            // it is the same `Unknown` a statement the walk cannot vouch for
            // is, which does not sight either.
            return Verdict::Unknown;
        };
        let caller_local = self.in_local_body;
        let caller_unsafe_from_local = self.in_unsafe_from_local;
        self.in_local_body = callee_local;
        // The crate's own code calling an `unsafe` function elsewhere owes its
        // preconditions, whose checks sit in that function's body (`ptr::add`
        // carries the `Offset` check a closure handed to `Option::map` must
        // pass).
        self.in_unsafe_from_local = unsafe_from_local;
        let verdict = self.walk(&callee_body);
        self.in_local_body = caller_local;
        self.in_unsafe_from_local = caller_unsafe_from_local;
        verdict
    }
}

/// How a place is being used, which decides what a raw-pointer `Deref` in it
/// means.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PlaceUse {
    /// The place is read or written: the dereference happens.
    Access,
    /// `&place` / `&mut place`: creating a reference through a raw pointer
    /// requires the pointer to be valid, but the encoder emits NO check for
    /// it — `codegen_address_of` treats `&*ptr` as the identity and hands the
    /// pointer value back (Kani checks derefs on access, not on reborrow).
    /// Not a sighting, then; but not something this walk vouches for either.
    Borrow,
    /// `&raw const place` / `&raw mut place`: no access and no validity
    /// requirement, but nothing here vouches for how the encoder models it.
    AddressOf,
}

/// The obligation verdict of one MIR statement, mirroring the encoder's
/// statement-level check emitters site for site.
///
/// `HasObligation` names a site the encoder emits a check for in BOTH lanes.
/// `Unknown` is everything the walk cannot vouch for — a float operation
/// whose obligation depends on `--nan-check`, a transmute, a thread-local, an
/// rvalue or cast kind this match does not name. `Free` is only what the
/// encoder demonstrably has nothing to prove about.
pub(crate) fn statement_verdict(stmt: &Statement, body: &Body) -> Verdict {
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            place_verdict(place, body, PlaceUse::Access).merge(rvalue_verdict(rvalue, body))
        }
        StatementKind::SetDiscriminant { place, .. } => {
            place_verdict(place, body, PlaceUse::Access)
        }
        // `assume(cond)` is asserted in both lanes ("Rust intrinsic assumption
        // failed"), as Kani does.
        StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_)) => Verdict::HasObligation,
        // Alignment of both pointers, validity of both regions, no overlap,
        // and no byte-count overflow (`codegen_copy_nonoverlapping`;
        // `try_encode_copy_nonoverlapping_intrinsic` on the CHC side).
        StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => {
            Verdict::HasObligation
        }
        StatementKind::FakeRead(..)
        | StatementKind::PlaceMention(..)
        | StatementKind::AscribeUserType { .. }
        | StatementKind::Coverage(..)
        | StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::Nop
        | StatementKind::ConstEvalCounter => Verdict::Free,
        #[cfg(not(trust_toolchain))]
        StatementKind::Retag(..) => Verdict::Free,
        // A statement kind this walk has never classified. Fail closed rather
        // than guess: the cost is parity, the alternative is a false Safe.
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

fn rvalue_verdict(rvalue: &Rvalue, body: &Body) -> Verdict {
    match rvalue {
        Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) => operand_verdict(op, body),
        Rvalue::Ref(_, _, place) => place_verdict(place, body, PlaceUse::Borrow),
        Rvalue::AddressOf(_, place) => place_verdict(place, body, PlaceUse::AddressOf),
        Rvalue::Len(place) | Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => {
            place_verdict(place, body, PlaceUse::Access)
        }
        Rvalue::Cast(kind, op, _) => operand_verdict(op, body).merge(cast_verdict(kind)),
        Rvalue::BinaryOp(op, lhs, rhs) => operand_verdict(lhs, body)
            .merge(operand_verdict(rhs, body))
            .merge(binop_verdict(*op, lhs, body)),
        // Yields `(value, overflowed)`; the obligation, if any, is the
        // `Assert` terminator that reads the flag, which the block scan
        // counts. A flag nobody asserts on (`checked_add`) proves nothing and
        // needs nothing.
        Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
            operand_verdict(lhs, body).merge(operand_verdict(rhs, body))
        }
        Rvalue::UnaryOp(op, operand) => {
            operand_verdict(operand, body).merge(unop_verdict(*op, operand, body))
        }
        Rvalue::Aggregate(_, operands) => {
            operands.iter().fold(Verdict::Free, |acc, op| acc.merge(operand_verdict(op, body)))
        }
        // The allocation that precedes it is a `Call` the walk follows.
        // Nightly-only rvalue: Trust's `rustc_public` has no `ShallowInitBox`
        // variant, and the catch-all below fails any unclassified shape closed.
        #[cfg(not(trust_toolchain))]
        Rvalue::ShallowInitBox(op, _) => operand_verdict(op, body),
        // Modelled as a fresh symbolic variable (single-thread model): not a
        // check, but not something this walk vouches for either.
        Rvalue::ThreadLocalRef(_) => Verdict::Unknown,
        // `cfg!(ub_checks)` and friends: compile-time constants.
        #[cfg(not(trust_toolchain))]
        Rvalue::NullaryOp(_) => Verdict::Free,
        // Trust: the shared form is unmodelled (`codegen_rvalue` fails it
        // closed) and the exclusive form is a copy the encoder rewrites; the
        // walk does not repeat that rewrite.
        #[cfg(trust_toolchain)]
        Rvalue::Reborrow(..) => Verdict::Unknown,
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

fn operand_verdict(op: &Operand, body: &Body) -> Verdict {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place_verdict(place, body, PlaceUse::Access),
        Operand::Constant(_) => Verdict::Free,
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

/// The obligation verdict of a place's projections.
///
/// A `Deref` through a RAW pointer is the memory-safety site:
/// `emit_raw_ptr_deref_checks` keys on exactly this (a `Deref` whose base
/// type is `RawPtr`) and emits null, alignment, object-bounds and
/// use-after-free checks. A `Deref` through a reference is safe by
/// construction. `Box` derefs do not reach optimized MIR in this form
/// (`ElaborateBoxDerefs` rewrites them to raw-pointer derefs), so any other
/// base type is refused.
///
/// An `Index` projection is refused too: `codegen_place` emits its own
/// `bounds_check` for it, and in safe code the bounds `Assert` stands in front
/// of it anyway. `ConstantIndex` and `Subslice` come from patterns rustc has
/// already checked the length for.
fn place_verdict(place: &Place, body: &Body, usage: PlaceUse) -> Verdict {
    let mut acc = Verdict::Free;
    for (idx, elem) in place.projection.iter().enumerate() {
        let step = match elem {
            ProjectionElem::Deref => {
                let base =
                    Place { local: place.local, projection: place.projection[..idx].to_vec() };
                let Ok(base_ty) = base.ty(body.locals()) else {
                    return Verdict::Unknown;
                };
                match base_ty.kind() {
                    TyKind::RigidTy(RigidTy::RawPtr(..)) => match usage {
                        PlaceUse::Access => Verdict::HasObligation,
                        // Refused, never SIGHTED: the certificate fails closed
                        // on a pointer nothing established, and the nested-call
                        // fallback does not demote on a check the encoder
                        // never emits.
                        PlaceUse::Borrow | PlaceUse::AddressOf => Verdict::Unknown,
                    },
                    TyKind::RigidTy(RigidTy::Ref(..)) => Verdict::Free,
                    _ => Verdict::Unknown,
                }
            }
            ProjectionElem::Index(_) => Verdict::HasObligation,
            ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Field(..)
            | ProjectionElem::Downcast(_)
            | ProjectionElem::OpaqueCast(_) => Verdict::Free,
            #[allow(unreachable_patterns)]
            _ => Verdict::Unknown,
        };
        if step == Verdict::HasObligation {
            return Verdict::HasObligation;
        }
        acc = acc.merge(step);
    }
    acc
}

/// The obligation verdict of a binary operation, by the checks the encoder
/// emits for it (`codegen_rvalue`'s `BinaryOp` arm; the CHC
/// `codegen_stmt_safety_checks` conditions mirror the same set).
fn binop_verdict(op: BinOp, lhs: &Operand, body: &Body) -> Verdict {
    let lhs_ty = lhs.ty(body.locals()).ok();
    match op {
        // `emit_overflow_check` / `emit_shift_distance_check`: overflow or an
        // out-of-range distance is UB, so the encoder asserts it cannot happen.
        BinOp::AddUnchecked
        | BinOp::SubUnchecked
        | BinOp::MulUnchecked
        | BinOp::ShlUnchecked
        | BinOp::ShrUnchecked => Verdict::HasObligation,
        // `emit_division_by_zero_check`, plus the signed `MIN / -1` overflow.
        // Float division has no such check, and its NaN obligation depends on
        // `--nan-check`; fail closed on it.
        BinOp::Div | BinOp::Rem => {
            if lhs_ty.is_some_and(ty_is_float) {
                Verdict::Unknown
            } else {
                Verdict::HasObligation
            }
        }
        // Non-null base, no overflow, and the result inside the object
        // (`emit_offset_overflow_check`, `emit_offset_object_bounds_check`).
        // The WRAPPING offset is `arith_offset`, a call, which the walk
        // clears separately.
        BinOp::Offset => Verdict::HasObligation,
        // Comparing fat pointers to trait objects reaches Kani's
        // `unstable_vtable_comparison` check; every other comparison is a
        // pure function of its operands.
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Cmp => {
            if lhs_ty.is_some_and(ty_is_dyn_ptr) {
                Verdict::HasObligation
            } else {
                Verdict::Free
            }
        }
        // Wrapping integer arithmetic (the checked form is `CheckedBinaryOp`
        // plus an `Assert`). Float arithmetic carries the `--nan-check`
        // obligation, so it is not vouched for.
        BinOp::Add | BinOp::Sub | BinOp::Mul => {
            if lhs_ty.is_some_and(ty_is_float) {
                Verdict::Unknown
            } else {
                Verdict::Free
            }
        }
        BinOp::Shl | BinOp::Shr | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => Verdict::Free,
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

/// Signed negation overflows on `MIN` (`emit_neg_overflow_check`; the CHC
/// `signed_neg_overflow_condition`). Float negation is a sign flip and `!` is
/// total.
fn unop_verdict(op: UnOp, operand: &Operand, body: &Body) -> Verdict {
    match op {
        UnOp::Neg => match operand.ty(body.locals()).map(|ty| ty.kind()) {
            Ok(TyKind::RigidTy(RigidTy::Int(_))) => Verdict::HasObligation,
            Ok(TyKind::RigidTy(RigidTy::Float(_) | RigidTy::Uint(_))) => Verdict::Free,
            _ => Verdict::Unknown,
        },
        UnOp::Not | UnOp::PtrMetadata => Verdict::Free,
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

/// Casts the encoder translates without an obligation. Float casts and
/// transmutes take dedicated, partly fail-closed paths (`cast_float`,
/// `cast_transmute`) that this walk does not re-derive.
fn cast_verdict(kind: &CastKind) -> Verdict {
    match kind {
        CastKind::IntToInt
        | CastKind::PtrToPtr
        | CastKind::FnPtrToPtr
        | CastKind::PointerCoercion(_)
        | CastKind::PointerExposeAddress
        | CastKind::PointerWithExposedProvenance
        | CastKind::Subtype => Verdict::Free,
        CastKind::FloatToInt
        | CastKind::FloatToFloat
        | CastKind::IntToFloat
        | CastKind::Transmute => Verdict::Unknown,
        #[allow(unreachable_patterns)]
        _ => Verdict::Unknown,
    }
}

fn ty_is_float(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(_)))
}

/// A pointer or reference to a trait object — a fat pointer carrying VTABLE
/// metadata, whose comparison Kani reports as an obligation.
fn ty_is_dyn_ptr(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
            matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
        }
        _ => false,
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

/// Is `instance` an `unsafe fn`?
fn instance_is_unsafe_fn(instance: &Instance) -> bool {
    instance
        .ty()
        .kind()
        .fn_sig()
        .is_some_and(|sig| matches!(sig.value.safety, rustc_public::mir::Safety::Unsafe))
}

/// The function `assert_unsafe_precondition!` generates inside each unsafe
/// operation it guards (`core::ptr::swap_nonoverlapping::precondition_check`).
///
/// The enclosing path carries its generic arguments
/// (`core::ptr::NonNull::<u8>::new_unchecked::precondition_check`), so the
/// name is matched at its END; the generated function itself takes none.
fn is_ub_precondition_check(name: &str) -> bool {
    name.ends_with("::precondition_check")
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
    fn test_ub_precondition_check_matches_behind_generic_parents() {
        use super::is_ub_precondition_check;
        assert!(is_ub_precondition_check(
            "core::ptr::NonNull::<u8>::new_unchecked::precondition_check"
        ));
        assert!(is_ub_precondition_check("core::ptr::swap_nonoverlapping::precondition_check"));
        assert!(!is_ub_precondition_check("my_crate::precondition_check_helper"));
        assert!(!is_ub_precondition_check("core::ptr::NonNull::<u8>::new_unchecked"));
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
