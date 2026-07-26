# Native-CHC switch-exhaustiveness — design & decision record

**Status:** Deferred (sound design captured; not implemented). Investigated 2026-06-20.
**Area:** `trust-mc-trust-bmc/src/translate_chc.rs` (native CHC VC translator).
**Value:** Completeness-only. `main` is **already sound** without this — it *fails to prove* the affected obligations (the safe direction), it does not admit false proofs.

## Goal

When a `SwitchInt`'s `otherwise`/`default` arm targets `Inst::Unreachable` **and** the switch
covers *all* discriminant tags of the selector's enum, reaching the default is impossible for
well-typed inputs. Conjoining `selector ∈ {case tags}` onto the default→`Unreachable` arm makes
the arm's guard `(¬gᵢ) ∧ (⋁ gⱼ)` structurally **UNSAT**, which discharges the unreachable
obligation. This would bring the **native CHC** path to parity with the **codegen_ay** path,
which already does this (commit `fd018aa`, via rustc MIR).

## Why the localized (translate_chc.rs-only) implementation is UNSOUND

The native translator consumes a `trust_ir::Module` and **does not have the information needed to
establish exhaustiveness soundly**:

- `Inst::Switch.value` (the selector) carries **no type** — `resolve_switch_selector`
  (`translate_chc.rs:2275`) defaults it to `Ty::I64`.
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

The MIR path is sound only because it reads ground-truth tags from rustc's `tcx`
(`def.discriminant_for_variant(tcx, VariantIdx)`); `trust_ir` has no such oracle.

**Do not add this logic to `translate_chc.rs` as-is.**

## The proof machinery already exists

Only a *sound tightening* of the default guard is missing — the discharge path is already present:

- `translate_switch` (`translate_chc.rs:1392–1448`) lowers the default arm via
  `add_transition_rule(default, default_args, default_guard = ¬(⋁ case_guards), …)` (line ~1438).
- `Inst::Unreachable` (`translate_chc.rs:1066`) emits
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
  discharges it with **no `translate_chc.rs` change**. Reuse the soundness conditions already
  implemented for the MIR path (see reference below).

Both live in the **`trust` compiler (a rustc fork)**, so validating either requires a heavy build —
weigh against the completeness-only value before undertaking.

## Reference implementation (already sound, on the MIR path)

`trust-mc-compiler/src/codegen_ay/chc/rules/codegen_rules/transition_gen_terminators.rs`:
- `codegen_switchint` (~line 25)
- `switchint_exhaustive_enum_unreachable` (lines 125–192) — uses
  `discriminant_for_variant` (line ~188).

Its soundness conditions (port these): (1) `otherwise` arm is `TerminatorKind::Unreachable`;
(2) `discr` is a bare local; (3) that local is assigned **exactly once** by
`Rvalue::Discriminant(enum_place)` of enum type; (4) the explicit case set **equals** the enum's
full discriminant tag set. Any uncertainty ⇒ add nothing.

## Regression tests to add (with either design)

Model on `trust-mc-trust-bmc/src/tests.rs:1599`
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

**Defer.** `main` is sound as-is; this is a completeness improvement whose only sound
implementation requires a contract/frontend change in the rustc-fork compiler (heavy build). Pick up
via design (B) when build headroom is available.
