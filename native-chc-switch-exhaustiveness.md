# Native-CHC switch-exhaustiveness — design & decision record

**Status:** Deferred, and its premise SUPERSEDED. Investigated 2026-06-20; revisited
2026-08-28 after `a288817cc` (see "What changed on the MIR path").
**Area:** `trust-mc-trust-bmc/src/translate_chc.rs` (native CHC VC translator).
**Value:** Completeness-only. `main` is **already sound** without this — it *fails to prove* the affected obligations (the safe direction), it does not admit false proofs.

## Goal

When a `SwitchInt`'s `otherwise`/`default` arm targets `Inst::Unreachable` **and** the switch
covers *all* discriminant tags of the selector's enum, reaching the default is impossible for
well-typed inputs. Conjoining `selector ∈ {case tags}` onto the default→`Unreachable` arm makes
the arm's guard `(¬gᵢ) ∧ (⋁ gⱼ)` structurally **UNSAT**, which discharges the unreachable
obligation.

> **READ "What changed on the MIR path" BELOW BEFORE IMPLEMENTING ANY OF THIS.**
> This document originally justified the work as reaching parity with the
> codegen_ay/MIR path, "which already does this". It no longer does: that gate
> was REMOVED as unsound on 2026-07-15, and for a well-typed enum the conjunct
> it added was redundant anyway.

## Why the localized (translate_chc.rs-only) implementation is UNSOUND

The native translator consumes a `trust_ir::Module` and **does not have the information needed to
establish exhaustiveness soundly**:

- `Inst::Switch.value` (the selector) carries **no type** — `resolve_switch_selector`
  (`translate_chc.rs:4079`) defaults it to `Ty::I64`.
- There is **no `Discriminant` instruction** in the `trust_ir` `Inst` enum; the discriminant
  reaches the switch as an untyped fresh symbolic via `ExtractField`/`Load`.
- `EnumDef` (`trust-ir ty.rs:489`) and `EnumVariant` (`ty.rs:501`) carry only variant
  **names/count — no discriminant tag values**.
- The discriminant tags *do* exist, but only in `request.rs::NativeEnumVariantLayoutFact.discriminant`
  (`Option<i128>`, part of `NativeEnumLayoutFact`) — a **frontend-supplied verification-request
  fact**. It is **not** part of `Module` and is **not** threaded into the translator
  (`native_bundle.rs:115` passes only `bundle.module`).

Consequently, any in-translator heuristic (e.g. equating the `SwitchCase.value` set with the
variant *count* `0..n`, or guessing the selector is a discriminant from surrounding `ExtractField`
shape) could assert `selector ∈ cases` on a switch whose `otherwise` arm is **genuinely reachable**
(a partial match desugared with `unreachable_unchecked`, or a plain-integer unreachable). That would
make a real bug's path UNSAT and **falsely prove a defective program safe** — a soundness
violation, the worst failure class.

The MIR path was believed sound because it read ground-truth tags from rustc's `tcx`;
that turned out NOT to be sufficient, and the gate was deleted (below). `trust_ir`
has no such oracle either way.

**Do not add this logic to `translate_chc.rs` as-is.**

## The proof machinery already exists

Only a *sound tightening* of the default guard is missing — the discharge path is already present:

- `translate_switch` (`translate_chc.rs:2899`) lowers the default arm via
  `add_transition_rule(default, default_args, default_guard = ¬(⋁ case_guards), …)`.
- `Inst::Unreachable` (`translate_chc.rs:1799`) emits
  `add_error_rule(from, path_constraints, Expr::true_())`, i.e. `(reachable ∧ path) → ERROR`.

So if `default_guard` becomes structurally UNSAT for an exhaustive enum switch, the unreachable
proves with **no further machinery**.

## Sound designs (require a producer-side / contract change)

The fix must originate where the enum type ground-truth exists (the frontend with rustc `tcx`).

- **(A) Contract change.** Add `EnumVariant.discriminant: Option<i128>` to `trust_ir` *and* a typed
  selector channel (a `Discriminant` inst, or a `Ty`/`EnumId` on `Switch.value`) so the selector can
  be tied to a specific `EnumId`. Then `translate_switch` checks `cases == {variant discriminants}`
  before adding the constraint.
- **(B) Producer emits the assumption (lighter; preferred).** Have `trust-mir-extract` (which has
  `tcx`) emit, on the exhaustive-enum `otherwise→Unreachable` edge, an explicit
  `Inst::Assume(selector ∈ {case tags})`. The **existing** `Inst::Unreachable` error-rule then
  discharges it with **no `translate_chc.rs` change** — its own comment
  (`translate_chc.rs:1799-1807`) names exactly this shape. Note that such an
  `Assume` is a CLAIM about the selector, so it inherits the missed-bug F hazard:
  emitted on a value that a transmute can make invalid, it re-refutes the only
  error edge for invalid-discriminant UB.

Both live in the **`trust` compiler (a rustc fork)**, so validating either requires a heavy build —
weigh against the completeness-only value before undertaking.

## What changed on the MIR path (2026-07-15) — there is no reference implementation

This section used to point at `switchint_exhaustive_enum_unreachable` in
`trust-mc-compiler/src/codegen_ay/chc/rules/codegen_rules/transition_gen_terminators.rs`
and say "port these soundness conditions". **That function no longer exists**, and
porting it would have reintroduced a false-proof bug.

`a288817cc` (2026-07-15, *"drop unsound exhaustive-enum unreachable gate ... close
invalid-discriminant false Safe (missed-bug F)"*) deleted the gate and its helper.
The failure was exactly the one this document warns about in the section above,
except it had already shipped on the MIR path: conjoining `selector ∈ cases`
refuted the ONLY error edge for an **invalid** discriminant produced by an unsafe
transmute (`transmute::<u8,E>(3)` with E's tags `{10,20,30}`), so invalid-value UB
that real Rust and Kani both reach was dropped and the program proved SUCCESSFUL.
Reading ground-truth tags from `tcx` did not save it — the gate's assumption was
that the selector *is* a valid discriminant, which holds by construction only for
well-typed enums.

The live code now says so at the point of decision
(`transition_gen_terminators.rs:66-80`); `codegen_switchint` (line 25) is still
there, without the gate.

**This also undercuts the Goal above.** Per that commit, for a well-typed enum the
selector is already pinned to a valid discriminant VALUE by the encoding
(`SetDiscriminant`/literal construction store the value; `kani::any` is bounded to
the valid tag set by `unit_enum_discriminant_bounds`), so `selector ∉ cases` is
**already UNSAT** and the conjunct was redundant. The corpus agreed: removing it
flipped 0 rows of 1120 parity, "value-space-constructed corpus enum matches keep
the otherwise UNSAT". If the native path's encoding likewise pins the selector to a
value, the completeness gap this document was written to close may not exist —
**measure it before building anything.**

## Regression tests to add (with either design)

Model on `trust-mc-trust-bmc/src/tests.rs:2360`
(`switch_generates_typed_chc_successor_rules`), using `ModuleBuilder` (`fb.switch`/`fb.assume`/
`fb.unreachable`/`fb.add_enum`):

- **POSITIVE** — exhaustive enum match (cases == all tags) with `otherwise → Unreachable`: assert the
  default-edge guard is structurally UNSAT, so the unreachable obligation is discharged (no live
  error rule for the default edge).
- **NEGATIVE (false-proof guard)** — (a) a plain-int switch with a *reachable* default, and (b) a
  *partial* enum match (e.g. 3-variant enum, `cases == {0,1}`) with `otherwise → Unreachable`: assert
  **no** `selector ∈ cases` conjunct is added, so a genuinely-reachable variant still yields a
  counterexample/error rule.

## Decision

**Defer — and re-scope before picking up.** `main` is sound as-is. Two things changed
since this was written: the MIR-path implementation it proposed to copy was deleted
as unsound (missed-bug F), and the same commit showed the conjunct is redundant for
well-typed enums. So the first step is no longer design (A) or (B) — it is to
MEASURE whether the native path actually fails to discharge these obligations, i.e.
whether its encoding pins the selector to a valid discriminant value the way the MIR
path's does. If it does, close this document as moot. If it does not, design (B) is
still the lighter option, but it must carry an invalid-discriminant negative test
(the `transmute::<u8,E>(3)` repro) as an acceptance criterion, not just the positive
and partial-match tests listed above.
