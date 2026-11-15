// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One source tree, two compilers: the rustc API shapes that differ between
//! the frozen `nightly-2025-12-03` Kani-compatibility lane and the Trust
//! compiler.
//!
//! STOCK-AS-ORACLE: every `not(trust_toolchain)` arm exists only for that
//! frozen nightly comparison baseline, kept by the owner's ruling of 2026-09-29
//! (owner directive 2026-09-28: ALab builds with Trust).
//! The build lane is Trust; a Trust-only arm must be written for it, not
//! discovered later on the nightly (1657228d3's missing
//! `Operand::RuntimeChecks` arm compiled only there).
//!
//! `build.rs` sets `cfg(trust_toolchain)` when `RUSTC -vV` identifies Trust.
//! Without it every item here is the literal nightly spelling, so the frozen
//! lane compiles the same program it compiled before this module existed. Under
//! it the item takes the Trust shape, which came from Trust's upstream
//! rust-lang migration (trust `cdbca2287b`, base rust-lang/rust `0d4eb098`)
//! and matches upstream Kani's port of the same code.
//!
//! The codemods under `tools/port/` rewrite the crate onto these items and are
//! re-runnable after a rebase. What each shim may and may not do:
//!
//! * [`rvalue_use!`] — `Rvalue::Use(op)` construction. Trust added a
//!   `WithRetag` flag; synthesized MIR uses `WithRetag::No`, as upstream Kani
//!   does. A retag is a Stacked/Tree Borrows event with no value semantics, and
//!   no trust-mc encoding models retags (the nightly `StatementKind::Retag`
//!   arms are all no-ops), so the flag is exact to drop.
//! * `Rvalue::Use(op, ..)` — the pattern spelling used on BOTH toolchains: the
//!   rest pattern matches zero fields on nightly and ignores `WithRetag` on
//!   Trust. No macro is needed.
//! * `PointerCoercion::ReifyFnPointer { .. }` — the pattern spelling used on
//!   BOTH toolchains. A braced rest pattern matches the nightly unit variant and
//!   the Trust `ReifyFnPointer(Safety)` tuple variant. The `Safety` payload
//!   only restates the target fn-pointer type, which the cast already carries.
//! * [`mir_span!`], [`mir_statement`], [`mir_terminator`] — Trust moved
//!   `Statement::span` / `Terminator::span` into `source_info: SourceInfo`.
//!   `mir_span!(x)` expands to the field place `x.span` / `x.source_info.span`,
//!   so it borrow-checks exactly like the original field read. Synthesized
//!   statements get scope 0, the outermost scope `Body::new` always allocates
//!   (upstream Kani's `synthetic_source_info`). No trust-mc code can read a
//!   scope: the nightly API never exposed one.
//! * [`prelude`] — trait imports method resolution needs on Trust:
//!   `CrateDefType` (home of `FieldDef::ty` / `ty_with_args` there) and
//!   [`VariantDefIdx`]. On nightly the `CrateDefType` import is compiled out,
//!   so method resolution there is unchanged.
//! * [`runtime_checks_value`] — Trust moved `Rvalue::NullaryOp(NullOp::RuntimeChecks)`
//!   to `Operand::RuntimeChecks`. This is the policy both backends already apply
//!   to the nightly rvalue, shared so every Trust operand arm agrees with it.
//! * [`VariantDefIdx::variant_idx`] — Trust made `VariantDef::idx` private
//!   behind an `idx()` accessor.
//! * [`early_binder_bind`] — Trust's `EarlyBinder::bind` takes the interner
//!   and marks aliases non-rigid. Exact only in front of a normalizing
//!   instantiation, which is the only way trust-mc uses it.
//! * [`skip_normalization`] — Trust wraps `type_of(..).instantiate_identity()`
//!   and `FieldDef::ty` in `Unnormalized`. Nightly returned the same
//!   unnormalized value directly, so unwrapping without normalizing is exact.
//! * [`impl_opt_trait_ref`] — Trust split `impl_trait_ref` (now total, for trait
//!   impls only) from `impl_opt_trait_ref`; nightly's `impl_trait_ref` is the
//!   optional one.
//! * [`instance_name`], [`def_name`] — Trust's `Instance::name` and
//!   `CrateDef::name` print the local crate's name in front of every local path
//!   (`fail::check` where nightly prints `check`). Kani reports harnesses, and
//!   `--harness`/`--exact` match, in the nightly form, so every name the engine
//!   REPORTS for a harness (or compares with one) comes from these two, which
//!   print exactly what the nightly `rustc_public` prints.
//! * `Rvalue::Reborrow(target_ty, mutability, place)` — Trust-only MIR for
//!   user-ADT reborrowing (`#![feature(reborrow)]`, the `Reborrow` /
//!   `CoerceShared` traits). At runtime it is a bitwise copy of `place` that
//!   never retags: rustc_codegen_ssa lowers it to
//!   `codegen_operand(Operand::Copy(place))` (trust `25ccaf01f`,
//!   `mir/rvalue.rs:672`), and the interpreter runs `copy_op` for `Mut` and
//!   `copy_op_allow_transmute` for `Not` (`interpret/step.rs:233`). `Mut`
//!   keeps the type, so [`exclusive_reborrow_as_copy`] rewrites it to
//!   `Use(Copy(place))` exactly. `Not` copies into the `CoerceShared` target, a
//!   DIFFERENT ADT whose layout is only "currently" equal, so an engine must
//!   fail it closed or check it, never treat it as a same-typed copy. Three
//!   traps:
//!   - rustc_public's `MirVisitor::super_rvalue` visits a `Mut` reborrow's
//!     place with a mutating `PlaceContext`, the one `&mut place` gets. A
//!     visitor whose `visit_place` depends on the context must visit the place
//!     as `Operand::Copy(place)` instead, as kani_middle's check_values, uninit
//!     and delayed-UB visitors do.
//!   - Upstream Kani main's points-to analysis groups `Reborrow` with `Ref`,
//!     so the result points AT `place`. A copy points where the value stored
//!     at `place` points, which is what trust-mc's points-to encodes.
//!   - Catch-all `_` arms absorb `Reborrow` without an E0004. The BMC rewrites
//!     `Mut` in `codegen_statement` and fails `Not` closed in `codegen_rvalue`;
//!     the CHC engine fails both closed (`codegen_ay::chc::trust_reborrow`).

#![cfg_attr(not(trust_toolchain), allow(dead_code))]
#![allow(unused_macros)]

use rustc_middle::ty::{EarlyBinder, TyCtxt, TypeFoldable};
use rustc_public::mir::{Statement, StatementKind, Terminator, TerminatorKind};
use rustc_public::ty::{Span, VariantDef, VariantIdx};

#[cfg(all(trust_toolchain, version("1.101")))]
pub(crate) use rustc_attr_ir::{AttrArgs, Attribute, LangItem};
#[cfg(not(all(trust_toolchain, version("1.101"))))]
pub(crate) use rustc_hir::{AttrArgs, Attribute, LangItem};

/// Kani's attribute map admits only unparsed tool attributes. Modern builtin
/// attributes may combine several source spans, so they have no general span
/// accessor and must never be assigned a synthetic tool-attribute span.
#[cfg(all(trust_toolchain, version("1.101")))]
pub(crate) fn tool_attribute_span(attribute: &Attribute) -> Option<rustc_span::Span> {
    match attribute {
        Attribute::Unparsed(item) => Some(item.span),
        Attribute::Parsed(_) => None,
    }
}

#[cfg(all(trust_toolchain, version("1.101")))]
pub(crate) trait ToolAttributeSpan {
    fn span(&self) -> rustc_span::Span;
}

#[cfg(all(trust_toolchain, version("1.101")))]
impl ToolAttributeSpan for Attribute {
    fn span(&self) -> rustc_span::Span {
        tool_attribute_span(self).unwrap_or_else(|| {
            rustc_middle::ty::tls::with(|tcx| {
                tcx.dcx()
                    .fatal("a parsed builtin attribute cannot be used as a Kani tool attribute")
            })
        })
    }
}

#[cfg(all(test, trust_toolchain, version("1.101")))]
mod tool_attribute_tests {
    use super::*;

    #[test]
    fn parsed_builtins_cannot_supply_a_tool_attribute_span() {
        let attribute = Attribute::Parsed(rustc_attr_ir::AttributeKind::Cold);
        assert_eq!(tool_attribute_span(&attribute), None);
    }

    #[test]
    fn unparsed_tool_attribute_keeps_its_exact_span() {
        rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2024,
            |_| {
                let span = rustc_span::Span::with_root_ctxt(
                    rustc_span::BytePos(11),
                    rustc_span::BytePos(29),
                );
                let attribute = Attribute::Unparsed(Box::new(rustc_attr_ir::AttrItem {
                    path: rustc_attr_ir::AttrPath {
                        segments: vec![
                            rustc_span::Symbol::intern("kanitool"),
                            rustc_span::Symbol::intern("proof"),
                        ]
                        .into_boxed_slice(),
                        span,
                    },
                    args: AttrArgs::Empty,
                    id: rustc_attr_ir::HashIgnoredAttrId {
                        attr_id: rustc_span::AttrId::from_u32(0),
                    },
                    style: rustc_ast::AttrStyle::Outer,
                    span,
                }));
                assert_eq!(tool_attribute_span(&attribute), Some(span));
                assert_eq!(ToolAttributeSpan::span(&attribute), span);
            },
        );
    }
}

// Error emission now distinguishes observational emit() from a guaranteed
// error. Both endpoints must return the actual error token, never fabricate it.
#[cfg(all(trust_toolchain, version("1.101")))]
macro_rules! emit_error {
    ($diagnostic:expr) => {
        ($diagnostic).emit_err()
    };
}
#[cfg(not(all(trust_toolchain, version("1.101"))))]
macro_rules! emit_error {
    ($diagnostic:expr) => {
        ($diagnostic).emit()
    };
}

// The measured Trust endpoints are 1.99 (the pinned seal) and 1.101. The
// latter names the same representation ValueRepr and carries the second
// scalar's offset explicitly. Consumers still use the actual FieldsShape
// offsets; neither this alias nor the pattern discards layout checks.
#[cfg(not(all(trust_toolchain, version("1.101"))))]
pub(crate) use rustc_public::abi::ValueAbi;
#[cfg(all(trust_toolchain, version("1.101")))]
pub(crate) use rustc_public::abi::ValueRepr as ValueAbi;

// Preserve a field place, rather than borrowing the entire LayoutShape:
// pointer-layout consumers also move its disjoint `fields` member.
#[cfg(all(trust_toolchain, version("1.101")))]
macro_rules! layout_value_abi {
    ($layout:expr) => {
        ($layout).value_repr
    };
}
#[cfg(not(all(trust_toolchain, version("1.101"))))]
macro_rules! layout_value_abi {
    ($layout:expr) => {
        ($layout).abi
    };
}

#[cfg(all(trust_toolchain, version("1.101")))]
macro_rules! scalar_pair_abi {
    ($first:pat, $second:pat $(,)?) => {
        $crate::rustc_compat::ValueAbi::ScalarPair { a: $first, b: $second, .. }
    };
}
#[cfg(not(all(trust_toolchain, version("1.101"))))]
macro_rules! scalar_pair_abi {
    ($first:pat, $second:pat $(,)?) => {
        $crate::rustc_compat::ValueAbi::ScalarPair($first, $second)
    };
}

/// Trait imports that method resolution needs on both toolchains.
///
/// Files that call `FieldDef::ty` / `ty_with_args` or `.variant_idx()`
/// glob-import this module.
pub(crate) mod prelude {
    #[cfg(trust_toolchain)]
    pub(crate) use rustc_public::CrateDefType as _;

    pub(crate) use super::VariantDefIdx as _;
}

/// Construct `Rvalue::Use` with the operand as its only meaningful payload.
///
/// Write the nightly constructor inside the macro:
/// `rvalue_use!(Rvalue::Use(operand))`. On the frozen nightly it expands to
/// exactly that expression. On Trust it appends `WithRetag::No` of whichever
/// `WithRetag` the enum's constructor expects (`rustc_public` or
/// `rustc_middle`).
macro_rules! rvalue_use {
    ($($path:ident)::+ ($op:expr $(,)?)) => {{
        #[cfg(not(trust_toolchain))]
        let rvalue = $($path)::+($op);
        #[cfg(trust_toolchain)]
        let rvalue = $($path)::+($op, ::core::convert::Into::into($crate::rustc_compat::NoRetag));
        rvalue
    }};
}
#[allow(unused_imports)]
pub(crate) use rvalue_use;

/// `WithRetag::No` for either `WithRetag` enum, selected by inference at the
/// `Rvalue::Use` constructor. See [`rvalue_use!`].
#[cfg(trust_toolchain)]
pub(crate) struct NoRetag;

#[cfg(trust_toolchain)]
impl From<NoRetag> for rustc_public::mir::WithRetag {
    fn from(_: NoRetag) -> Self {
        rustc_public::mir::WithRetag::No
    }
}

#[cfg(trust_toolchain)]
impl From<NoRetag> for rustc_middle::mir::WithRetag {
    fn from(_: NoRetag) -> Self {
        rustc_middle::mir::WithRetag::No
    }
}

/// The source span of a `rustc_public` MIR statement or terminator.
///
/// `mir_span!(stmt)` is the field place `stmt.span` on the frozen nightly and
/// `stmt.source_info.span` on Trust. It is a macro rather than a method so a
/// read next to a live `&mut` borrow of a sibling field (`bb.terminator.kind`)
/// borrow-checks exactly as the original field read did.
#[cfg(not(trust_toolchain))]
macro_rules! mir_span {
    ($statement_or_terminator:expr) => {
        $statement_or_terminator.span
    };
}
#[cfg(trust_toolchain)]
macro_rules! mir_span {
    ($statement_or_terminator:expr) => {
        $statement_or_terminator.source_info.span
    };
}
#[allow(unused_imports)]
pub(crate) use mir_span;

/// `SourceInfo` for a statement or terminator trust-mc synthesizes at `span`:
/// the outermost source scope, which `Body::new` always allocates.
#[cfg(trust_toolchain)]
#[inline]
pub(crate) fn synthetic_source_info(span: Span) -> rustc_public::mir::SourceInfo {
    rustc_public::mir::SourceInfo { span, scope: 0 }
}

/// `Statement { kind, span }` on either toolchain.
#[inline]
pub(crate) fn mir_statement(kind: StatementKind, span: Span) -> Statement {
    #[cfg(not(trust_toolchain))]
    let statement = Statement { kind, span };
    #[cfg(trust_toolchain)]
    let statement = Statement { kind, source_info: synthetic_source_info(span) };
    statement
}

/// `Terminator { kind, span }` on either toolchain.
#[inline]
pub(crate) fn mir_terminator(kind: TerminatorKind, span: Span) -> Terminator {
    #[cfg(not(trust_toolchain))]
    let terminator = Terminator { kind, span };
    #[cfg(trust_toolchain)]
    let terminator = Terminator { kind, source_info: synthetic_source_info(span) };
    terminator
}

/// The index of a variant within its ADT.
pub(crate) trait VariantDefIdx {
    fn variant_idx(&self) -> VariantIdx;
}

impl VariantDefIdx for VariantDef {
    #[inline]
    fn variant_idx(&self) -> VariantIdx {
        #[cfg(not(trust_toolchain))]
        let idx = self.idx;
        #[cfg(trust_toolchain)]
        let idx = self.idx();
        idx
    }
}

/// Codegen-time value of a runtime-checks flag.
///
/// This is the policy both backends apply to the nightly
/// `Rvalue::NullaryOp(NullOp::RuntimeChecks(..))` (BMC `codegen_rvalue`, CHC
/// `translate_rvalue`, CHC inline evaluation):
///
/// * `UbChecks` -> `false`, as Kani compiles every `RuntimeChecks` flag
///   (kani-compiler `codegen_rvalue`: `Expr::c_false()`). Core's
///   `assert_unsafe_precondition!` checks therefore never run. Their UB is
///   checked by the encoder's own obligations, as Kani's is: unchecked
///   arithmetic overflow, `offset` / `offset_from` allocation and distance,
///   `copy_nonoverlapping` alignment and overlap, and the `assume` intrinsic,
///   which both lanes ASSERT (Kani: "Rust intrinsic assumption failed").
///   `true` executed the preconditions against the encoder's stack addresses:
///   `offset_from_unsigned`'s `self >= origin` failed for two locals that the
///   address model ordered, so a harness Kani passes failed
///   (tools/soundness-duals/offset_from_unsigned_ub_precondition_dual.rs).
///   The #3299 reason for `true` (dead `AddUnchecked` asserts) is gone: the
///   encoder checks the unchecked BinOps itself -- BMC's statement path, CHC's
///   statement path, CHC `step_wrapping`, and the CHC inline walker
///   (`inline_shared/rvalue_ub.rs`, which recorded none before 2026-09-23).
///   That coverage is NOT complete in the CHC walker. Measured 2026-09-24
///   against the corpus-rev Kani (tools/soundness-duals/walker_*_dual.rs):
///   the drop-body consumers emit a walked drop body's checks, and a nested
///   fn-pointer call or a several-candidate `dyn Fn` call walks every
///   candidate under its dispatch guard. These routes FAIL CLOSED instead of
///   checking (a correct program there is demoted, never proved clean): a
///   value-only closure consumer (`Iterator::fold` replay,
///   map/collect, `RefCell::replace_with`), the quantifier closure-body walk,
///   a core `unchecked_*` wrapper havocked because an argument did not
///   translate, and a `dyn Fn` merge that cannot be built. These are still
///   MISSED, tracked known-red: a SwitchInt arm the walker cannot finish,
///   including a loop that outruns the replay budget (Mechanism C), a
///   non-panic diverging call (D), an untranslatable `Assert` condition (E),
///   and any other std callee the nested-call fallback havocs (B).
/// * `ContractChecks` -> `true`: contracts are checked in verification mode.
/// * `OverflowChecks` -> `false`: verification encodes overflow explicitly.
///
/// On Trust the same flag reaches codegen as `Operand::RuntimeChecks`, and
/// every operand arm that produces a value must use this function.
#[inline]
pub(crate) fn runtime_checks_value(checks: &rustc_public::mir::RuntimeChecks) -> bool {
    use rustc_public::mir::RuntimeChecks;
    match checks {
        RuntimeChecks::UbChecks => false,
        RuntimeChecks::ContractChecks => true,
        RuntimeChecks::OverflowChecks => false,
    }
}

/// `EarlyBinder::bind` for a value about to be instantiated WITH normalization.
///
/// Trust's `EarlyBinder::bind(tcx, value)` takes the interner and also marks
/// the value's aliases non-rigid ("instantiation will require normalization").
/// Nightly's `EarlyBinder::bind(value)` does neither. Pass the result straight
/// to a normalizing instantiation such as
/// `Instance::instantiate_mir_and_normalize_erasing_regions`. On Trust that call
/// normalizes the non-rigid aliases again, just as nightly's call normalized
/// every alias, so both lanes produce the same monomorphized, normalized value.
/// Upstream Kani main spells the Trust call the same way. Do not use this for a
/// non-normalizing instantiation, which on Trust would leave aliases non-rigid.
#[inline]
pub(crate) fn early_binder_bind<'tcx, T>(tcx: TyCtxt<'tcx>, value: T) -> EarlyBinder<'tcx, T>
where
    T: TypeFoldable<TyCtxt<'tcx>>,
{
    #[cfg(not(trust_toolchain))]
    let binder = {
        let _ = tcx;
        EarlyBinder::bind(value)
    };
    #[cfg(trust_toolchain)]
    let binder = EarlyBinder::bind(tcx, value);
    binder
}

/// The value of a computation Trust wraps in `Unnormalized`, deliberately left
/// unnormalized.
///
/// Trust returns `type_of(..).instantiate_identity()` and `FieldDef::ty` as
/// `Unnormalized`. Nightly returned the same instantiation, unnormalized,
/// directly, so unwrapping without normalizing yields exactly the nightly
/// value. On nightly this is the identity.
#[cfg(not(trust_toolchain))]
#[inline]
pub(crate) fn skip_normalization<T>(value: T) -> T {
    value
}

/// See the nightly definition above.
#[cfg(trust_toolchain)]
#[inline]
pub(crate) fn skip_normalization<'tcx, T>(value: rustc_middle::ty::Unnormalized<'tcx, T>) -> T {
    value.skip_normalization()
}

/// The trait an impl implements, `None` for an inherent impl.
#[cfg(not(trust_toolchain))]
pub(crate) fn impl_opt_trait_ref(
    tcx: TyCtxt<'_>,
    impl_def: rustc_hir::def_id::DefId,
) -> Option<EarlyBinder<'_, rustc_middle::ty::TraitRef<'_>>> {
    // On nightly-2025-12-03 `impl_trait_ref` returns the bare binder (and
    // expects a trait impl); the optional form is `impl_opt_trait_ref`.
    tcx.impl_opt_trait_ref(impl_def)
}

/// See the nightly definition above.
#[cfg(trust_toolchain)]
pub(crate) fn impl_opt_trait_ref(
    tcx: TyCtxt<'_>,
    impl_def: rustc_hir::def_id::DefId,
) -> Option<EarlyBinder<'_, rustc_middle::ty::TraitRef<'_>>> {
    tcx.impl_opt_trait_ref(impl_def)
}

/// Trust: `Rvalue::Use(Operand::Copy(place))` for an exclusive reborrow
/// `Rvalue::Reborrow(_, Mutability::Mut, place)`, and `None` for every other
/// rvalue, including the shared (`Mutability::Not`, `CoerceShared`) form.
///
/// Exact, not an approximation (see "Reborrow" in the module docs): an
/// exclusive reborrow copies `place` bit for bit into the same type and never
/// retags, which is exactly what `Use(Copy(place))` means. The borrow-checker
/// restrictions it adds have no runtime effect.
#[cfg(trust_toolchain)]
pub(crate) fn exclusive_reborrow_as_copy(
    rvalue: &rustc_public::mir::Rvalue,
) -> Option<rustc_public::mir::Rvalue> {
    use rustc_public::mir::{Mutability, Operand, Rvalue};
    match rvalue {
        Rvalue::Reborrow(_, Mutability::Mut, place) => {
            Some(rvalue_use!(Rvalue::Use(Operand::Copy(place.clone()))))
        }
        _ => None,
    }
}

/// An instance's name as the frozen nightly's `Instance::name` prints it: the absolute path
/// with generic arguments, and no crate name in front of local paths (`mod1::check`,
/// `generic::<Local>`); items of other crates keep their crate (`std::mem::swap::<u8>`).
///
/// Trust's `rustc_public` prints the same `def_path_str_with_args` under
/// `with_resolve_crate_name!` (trust `45dc60873`,
/// `compiler/rustc_public_bridge/src/context/impls.rs:739`), which writes the local crate's
/// name at every local path component, generic arguments included. The nightly prints it
/// under `with_no_trimmed_paths!` alone, so this calls rustc's printer that way on Trust.
/// Harness names are how Kani reports and selects harnesses (`Checking harness mod1::check`,
/// `--harness`, `--exact`), so both lanes must print them identically.
#[cfg(not(trust_toolchain))]
pub(crate) fn instance_name(
    tcx: TyCtxt<'_>,
    instance: rustc_public::mir::mono::Instance,
) -> String {
    let _ = tcx;
    instance.name()
}

/// See the nightly definition above.
#[cfg(trust_toolchain)]
pub(crate) fn instance_name(
    tcx: TyCtxt<'_>,
    instance: rustc_public::mir::mono::Instance,
) -> String {
    use rustc_middle::ty::print::with_no_trimmed_paths;
    let instance = rustc_public::rustc_internal::internal(tcx, instance);
    with_no_trimmed_paths!(tcx.def_path_str_with_args(instance.def_id(), instance.args))
}

/// A definition's name as the frozen nightly's `CrateDef::name` prints it: `def_path_str`
/// with no crate name in front of local paths. See [`instance_name`].
#[cfg(not(trust_toolchain))]
pub(crate) fn def_name(tcx: TyCtxt<'_>, def: &impl rustc_public::CrateDef) -> String {
    let _ = tcx;
    def.name()
}

/// See the nightly definition above.
#[cfg(trust_toolchain)]
pub(crate) fn def_name(tcx: TyCtxt<'_>, def: &impl rustc_public::CrateDef) -> String {
    use rustc_middle::ty::print::with_no_trimmed_paths;
    let def_id = rustc_public::rustc_internal::internal(tcx, def.def_id());
    with_no_trimmed_paths!(tcx.def_path_str(def_id))
}
