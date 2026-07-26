// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code for processing Rust attributes (like `kani::proof`).

mod parse;
mod stable;

pub(crate) use parse::is_proof_harness;
use parse::{
    UnstableAttribute, attr_kind, expect_key_string_value, expect_no_args, expect_single,
    parse_paths, parse_solver, parse_unwind, pretty_type_path,
};
pub(crate) use stable::fn_marker;
use stable::stable_tool_unstable_attrs;

use std::collections::{BTreeMap, HashSet};

use quote::ToTokens;
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    Attribute,
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::DefId as DefIdStable;
use rustc_public::mir::mono::Instance as InstanceStable;
use rustc_public::rustc_internal;
use rustc_public::ty::FnDef as FnDefStable;
use rustc_span::{Span, Symbol};
use strum_macros::{AsRefStr, EnumString};
use syn::TypePath;
use trust_mc_metadata::{HarnessAttributes, HarnessKind, Stub};

use super::resolve::{FnResolution, ResolveError, resolve_fn_path};
use tracing::{debug, trace};

#[derive(Debug, Clone, Copy, AsRefStr, EnumString, PartialEq, Eq, PartialOrd, Ord)]
#[strum(serialize_all = "snake_case")]
enum KaniAttributeKind {
    Proof,
    ShouldPanic,
    Solver,
    Stub,
    /// Marker emitted by `kani::stub_set!` for a reusable group of stubs.
    StubSet,
    /// Harness or stub-set attribute that applies a reusable group of stubs.
    UseStubSet,
    /// Attribute used to mark unstable APIs.
    Unstable,
    Unwind,
    /// A sound [`Self::Stub`] that replaces a function by a stub generated from
    /// its contract.
    StubVerified,
    /// A harness, similar to [`Self::Proof`], but for checking a function
    /// contract, e.g. the contract check is substituted for the target function
    /// before the the verification runs.
    ProofForContract,
    /// Internal attribute of the contracts implementation. Identifies the
    /// code implementing the function with its contract clauses asserted.
    AssertedWith,
    /// Attribute on a function with a contract that identifies the code
    /// implementing the check for this contract.
    CheckedWith,
    /// Internal attribute of the contracts implementation that identifies the
    /// name of the function which was generated as the sound stub from the
    /// contract of this function.
    ReplacedWith,
    /// Attribute on a function with a contract that identifies the code
    /// implementing the recursive check for the harness.
    RecursionCheck,
    /// Attribute on a function that was auto-generated from expanding a
    /// function contract.
    IsContractGenerated,
    /// A function with contract expanded to include the write set as arguments.
    ///
    /// Contains the original body of the contracted function. The signature is
    /// expanded with additional pointer arguments that are not used in the function
    /// but referenced by the `modifies` annotation.
    ModifiesWrapper,
    /// Attribute used to mark contracts for functions with recursion.
    /// We use this attribute to properly instantiate `kani::any_modifies` in
    /// cases when recursion is present given our contracts instrumentation.
    Recursion,
    /// Attribute used to mark the static variable used for tracking recursion check.
    RecursionTracker,
    /// Generic marker that can be used to mark functions so this list doesn't have to keep growing.
    /// This takes a key which is the marker.
    FnMarker,
    /// Used to mark functions where generating automatic pointer checks should be disabled. This is
    /// used later to automatically attach pragma statements to locations.
    DisableChecks,
}

impl KaniAttributeKind {
    /// Returns whether an item is only relevant for harnesses.
    fn is_harness_only(self) -> bool {
        match self {
            KaniAttributeKind::Proof
            | KaniAttributeKind::ShouldPanic
            | KaniAttributeKind::Solver
            | KaniAttributeKind::Stub
            | KaniAttributeKind::UseStubSet
            | KaniAttributeKind::ProofForContract
            | KaniAttributeKind::StubVerified
            | KaniAttributeKind::Unwind => true,
            KaniAttributeKind::Unstable
            | KaniAttributeKind::StubSet
            | KaniAttributeKind::FnMarker
            | KaniAttributeKind::Recursion
            | KaniAttributeKind::RecursionTracker
            | KaniAttributeKind::ReplacedWith
            | KaniAttributeKind::RecursionCheck
            | KaniAttributeKind::CheckedWith
            | KaniAttributeKind::ModifiesWrapper
            | KaniAttributeKind::AssertedWith
            | KaniAttributeKind::IsContractGenerated
            | KaniAttributeKind::DisableChecks => false,
        }
    }

    /// Is this an "active" function contract attribute? This means it is
    /// part of the function contract interface *and* it implies that a contract
    /// will be used (stubbed or checked) in some way, thus requiring that the
    /// user activate the unstable feature.
    ///
    /// If we find an "inactive" contract attribute we chose not to error,
    /// because it wouldn't have any effect anyway.
    fn demands_function_contract_use(self) -> bool {
        matches!(self, KaniAttributeKind::ProofForContract)
    }

    /// Is this a stubbing attribute that requires the experimental stubbing feature?
    fn demands_stubbing_use(self) -> bool {
        matches!(
            self,
            KaniAttributeKind::Stub
                | KaniAttributeKind::StubVerified
                | KaniAttributeKind::UseStubSet
        )
    }

    /// Is this attribute valid inside a `kani::stub_set!` expansion?
    fn is_stub_set_member(self) -> bool {
        matches!(self, KaniAttributeKind::Stub | KaniAttributeKind::UseStubSet)
    }
}

/// Bundles together common data used when evaluating the attributes of a given
/// function.
#[derive(Clone)]
pub(crate) struct KaniAttributes<'tcx> {
    /// Rustc type context/queries
    tcx: TyCtxt<'tcx>,
    /// The function which these attributes decorate.
    item: DefId,
    /// All attributes we found in raw format.
    map: BTreeMap<KaniAttributeKind, Vec<&'tcx Attribute>>,
}

#[derive(Clone, Debug)]
/// Bundle contract attributes for a function annotated with contracts.
pub(crate) struct ContractAttributes {
    /// Whether the contract was marked with `#[recursion]` attribute.
    #[allow(dead_code)]
    // Upstream Kani contract field - read via KaniAttributes::has_recursion()
    pub has_recursion: bool,
    /// The name of the contract recursion check.
    pub recursion_check: Symbol,
    /// The name of the contract check.
    pub checked_with: Symbol,
    /// The name of the contract replacement.
    pub replaced_with: Symbol,
    /// The name of the inner check used to modify clauses.
    /// FC-06: resolved by `contracts_frame::resolve_modifies_wrapper` to
    /// instrument the wrapper with modifies-frame markers in check mode.
    pub modifies_wrapper: Symbol,
    /// The name of the contract assert closure
    pub asserted_with: Symbol,
}

impl std::fmt::Debug for KaniAttributes<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KaniAttributes")
            .field("item", &self.tcx.def_path_debug_str(self.item))
            .field("map", &self.map)
            .finish()
    }
}

impl<'tcx> KaniAttributes<'tcx> {
    /// Perform preliminary parsing and checking for the attributes on this
    /// function
    pub(crate) fn for_instance(tcx: TyCtxt<'tcx>, instance: InstanceStable) -> Self {
        KaniAttributes::for_def_id(tcx, instance.def.def_id())
    }

    /// Look up the attributes by a stable MIR DefID
    pub(crate) fn for_def_id(tcx: TyCtxt<'tcx>, def_id: DefIdStable) -> Self {
        KaniAttributes::for_item(tcx, rustc_internal::internal(tcx, def_id))
    }

    pub(crate) fn for_item(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let all_attributes = tcx.get_all_attrs(def_id);
        let map = all_attributes.iter().fold(
            <BTreeMap<KaniAttributeKind, Vec<&'tcx Attribute>>>::default(),
            |mut result, attribute| {
                // Get the string the appears after "kanitool::" in each attribute string.
                // Ex - "proof" | "unwind" etc.
                if let Some(kind) = attr_kind(tcx, attribute) {
                    result.entry(kind).or_default().push(attribute);
                }
                result
            },
        );
        Self { map, tcx, item: def_id }
    }

    /// Expect that at most one attribute of this kind exists on the function
    /// and return it.
    fn expect_maybe_one(&self, kind: KaniAttributeKind) -> Option<&'tcx Attribute> {
        if let [one] = self.map.get(&kind)?.as_slice() {
            Some(one)
        } else {
            // non-enum: slice
            self.tcx.dcx().err(format!(
                "Too many {} attributes on {}, expected 0 or 1",
                kind.as_ref(),
                self.tcx.def_path_debug_str(self.item)
            ));
            None
        }
    }

    /// Parse, extract and resolve the target of `stub_verified(TARGET)`. The
    /// returned `Symbol` and `DefId` are respectively the name and id of
    /// `TARGET`. The `Span` is that of the contents of the attribute and used
    /// for error reporting.
    ///
    /// Any error is emitted and the attribute is filtered out.
    pub(crate) fn interpret_stub_verified_attribute(&self) -> Vec<FnDefStable> {
        self.map
            .get(&KaniAttributeKind::StubVerified)
            .map_or([].as_slice(), Vec::as_slice)
            .iter()
            .filter_map(|attr| {
                let target = self.parse_single_path_attr(attr).ok()?;
                Some(target.def())
            })
            .collect()
    }

    pub(crate) fn has_recursion(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::Recursion)
    }

    /// Whether this item is the contract machinery's recursion reentry
    /// tracker static (`#[kanitool::recursion_tracker]`). Such statics are
    /// verifier-internal state, never ambient program state — the
    /// contract-mode static havoc (P2-S1) must keep them pinned.
    pub(crate) fn is_recursion_tracker(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::RecursionTracker)
    }

    /// Parse and extract the `proof_for_contract(TARGET)` attribute. The
    /// returned symbol and DefId are respectively the name and id of `TARGET`,
    /// the span in the span for the attribute (contents).
    ///
    /// In the case of an error, this function will emit the error and return `None`.
    pub(crate) fn interpret_for_contract_attribute(&self) -> Option<FnDefStable> {
        self.expect_maybe_one(KaniAttributeKind::ProofForContract).and_then(|attr| {
            let target = self.parse_single_path_attr(attr).ok()?;
            Some(target.def())
        })
    }

    pub(crate) fn proof_for_contract(&self) -> Option<Result<Symbol, ErrorGuaranteed>> {
        self.expect_maybe_one(KaniAttributeKind::ProofForContract)
            .map(|target| expect_key_string_value(self.tcx.sess, target))
    }

    /// Extract the name of the local that represents this function's contract is
    /// checked with (if any).
    ///
    /// `None` indicates this function does not use a contract, or an error was found.
    /// Note that the error will already be emitted, so we don't return an error.
    pub(crate) fn contract_attributes(&self) -> Option<ContractAttributes> {
        let has_recursion = self.has_recursion();
        let recursion_check = self.attribute_value(KaniAttributeKind::RecursionCheck);
        let checked_with = self.attribute_value(KaniAttributeKind::CheckedWith);
        let replace_with = self.attribute_value(KaniAttributeKind::ReplacedWith);
        let modifies_wrapper = self.attribute_value(KaniAttributeKind::ModifiesWrapper);
        let asserted_with = self.attribute_value(KaniAttributeKind::AssertedWith);

        let total = recursion_check
            .iter()
            .chain(&checked_with)
            .chain(&replace_with)
            .chain(&modifies_wrapper)
            .chain(&asserted_with)
            .count();
        if total != 0 && total != 5 {
            self.tcx.sess.dcx().err(format!(
                "Failed to parse contract instrumentation tags in function `{}`.\
                Expected `5` attributes, but was only able to process `{total}`",
                self.tcx.def_path_str(self.item)
            ));
        }
        Some(ContractAttributes {
            has_recursion,
            recursion_check: recursion_check?,
            checked_with: checked_with?,
            replaced_with: replace_with?,
            modifies_wrapper: modifies_wrapper?,
            asserted_with: asserted_with?,
        })
    }

    // Is this a function inserted by Kani instrumentation?
    pub(crate) fn is_kani_instrumentation(&self) -> bool {
        self.fn_marker().is_some() || self.is_contract_generated()
    }

    // Is this a contract-generated function?
    // Note that this function currently always returns false because of https://github.com/model-checking/kani/issues/3921
    fn is_contract_generated(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::IsContractGenerated)
    }

    /// Return a function marker if any.
    pub(crate) fn fn_marker(&self) -> Option<Symbol> {
        self.attribute_value(KaniAttributeKind::FnMarker)
    }

    /// Check if function is annotated with any contract attribute.
    pub(crate) fn has_contract(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::CheckedWith)
    }

    /// Check that all attributes assigned to an item is valid.
    /// Returns a tuple of (stub_verified_targets_with_spans, proof_for_contract_targets).
    /// Errors will be added to the session. Invoke self.tcx.sess.abort_if_errors() to terminate
    /// the session and emit all errors found.
    pub(super) fn check_attributes(&self) -> (FxHashMap<FnDefStable, Span>, HashSet<FnDefStable>) {
        // Check that all attributes are correctly used and well formed.
        let is_harness = self.is_proof_harness();
        let is_stub_set = self.is_stub_set();

        let mut contract_targets = HashSet::default();
        let mut stub_verified_targets = FxHashMap::default();

        for (&kind, attrs) in &self.map {
            let local_error = |msg| self.tcx.dcx().span_err(attrs[0].span(), msg);

            if !is_harness && kind.is_harness_only() && !(is_stub_set && kind.is_stub_set_member())
            {
                local_error(format!(
                    "the `{}` attribute also requires the `#[kani::proof]` attribute",
                    kind.as_ref()
                ));
            }
            match kind {
                KaniAttributeKind::ShouldPanic => {
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        expect_no_args(self.tcx, kind, attr);
                    });
                }
                KaniAttributeKind::Recursion => {
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        expect_no_args(self.tcx, kind, attr);
                    });
                }
                KaniAttributeKind::Solver => {
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        parse_solver(self.tcx, attr);
                    });
                }
                KaniAttributeKind::Stub => {
                    // Members of a `kani::stub_set!` (`is_stub_set`) carry their
                    // stub targets as paths written relative to the *consuming
                    // harness*, not to the module the set is declared in. Resolve
                    // them lazily during harness expansion (see `expand_stub_set`);
                    // resolving here against the set's own module would spuriously
                    // fail for sets defined in a submodule (e.g. `stub_set_module`).
                    if !is_stub_set {
                        self.parse_stubs(self.current_module(), attrs);
                    }
                }
                KaniAttributeKind::UseStubSet => {
                    if !is_stub_set {
                        self.parse_stub_sets(self.current_module(), attrs);
                    }
                }
                KaniAttributeKind::StubSet => {
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        expect_no_args(self.tcx, kind, attr);
                    });
                }
                KaniAttributeKind::Unwind => {
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        parse_unwind(self.tcx, attr);
                    });
                }
                KaniAttributeKind::Proof => {
                    if self.map.contains_key(&KaniAttributeKind::ProofForContract) {
                        local_error(
                            "`proof` and `proof_for_contract` may not be used on the same function.".to_string(),
                        );
                    }
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| self.check_proof_attribute(kind, attr));
                }
                KaniAttributeKind::Unstable => attrs.iter().for_each(|attr| {
                    let _ = UnstableAttribute::try_from(*attr).map_err(|err| err.report(self.tcx));
                }),
                KaniAttributeKind::ProofForContract => {
                    if self.map.contains_key(&KaniAttributeKind::Proof) {
                        local_error(
                            "`proof` and `proof_for_contract` may not be used on the same function.".to_string(),
                        );
                    }
                    expect_single(self.tcx, kind, attrs);
                    attrs.iter().for_each(|attr| {
                        self.check_proof_attribute(kind, attr);
                        let res = self.parse_single_path_attr(attr);
                        if let Ok(target) = res {
                            contract_targets.insert(target.def());
                        }
                    });
                }
                KaniAttributeKind::StubVerified => {
                    attrs.iter().for_each(|attr| {
                        self.check_stub_verified(attr);
                        let res = self.parse_single_path_attr(attr);
                        if let Ok(target) = res {
                            stub_verified_targets.insert(target.def(), attr.span());
                        }
                    });
                }
                KaniAttributeKind::FnMarker
                | KaniAttributeKind::CheckedWith
                | KaniAttributeKind::ModifiesWrapper
                | KaniAttributeKind::RecursionCheck
                | KaniAttributeKind::AssertedWith
                | KaniAttributeKind::ReplacedWith => {
                    self.attribute_value(kind);
                }
                KaniAttributeKind::IsContractGenerated => {
                    // Ignored here because this is only used by the proc macros
                    // to communicate with one another. So by the time it gets
                    // here we don't care if it's valid or not.
                }
                KaniAttributeKind::RecursionTracker => {
                    // Nothing to do here. This is used by contract instrumentation.
                }
                KaniAttributeKind::DisableChecks => {
                    // Ignored here, because it should be an internal attribute. Actual validation
                    // happens when pragmas are generated.
                }
            }
        }
        (stub_verified_targets, contract_targets)
    }

    /// Get the value of an attribute if one exists.
    ///
    /// This expects up to one attribute with format `#[kanitool::<name>("<value>")]`.
    ///
    /// Any format or expectation error is emitted already, and does not need to be handled
    /// upstream.
    fn attribute_value(&self, kind: KaniAttributeKind) -> Option<Symbol> {
        self.expect_maybe_one(kind)
            .and_then(|target| expect_key_string_value(self.tcx.sess, target).ok())
    }

    /// Get the span for an attribute kind, falling back to the definition span.
    fn span_for_kind(&self, kind: KaniAttributeKind) -> Span {
        self.map
            .get(&kind)
            .and_then(|attrs| attrs.first())
            .map_or_else(|| self.tcx.def_span(self.item), |attr| attr.span())
    }

    pub(crate) fn has_unstable_feature_attr(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::Unstable)
    }

    /// Check that any unstable API has been enabled. Otherwise, emit an error.
    ///
    /// Error messages use the attribute span when available, falling back to the definition span.
    pub(crate) fn check_unstable_features(&self, enabled_features: &[String]) {
        if matches!(self.tcx.def_kind(self.item), DefKind::Closure) {
            // Skip closures since it shouldn't be possible to add an unstable attribute to them.
            // We have to explicitly skip them though due to an issue with rustc:
            // https://github.com/model-checking/kani/pull/2406#issuecomment-1534333862
            return;
        }

        // If the `function-contracts` unstable feature is not enabled then no
        // function should use any of those APIs.
        if !enabled_features.iter().any(|feature| feature == "function-contracts") {
            for kind in self.map.keys().copied().filter(|a| a.demands_function_contract_use()) {
                let msg = format!(
                    "Using the {} attribute requires activating the unstable `function-contracts` feature",
                    kind.as_ref()
                );
                self.tcx.dcx().span_err(self.span_for_kind(kind), msg);
            }
        }

        // If the `stubbing` unstable feature is not enabled then no
        // function should use any of those APIs.
        if !enabled_features.iter().any(|feature| feature == "stubbing") {
            for kind in self.map.keys().copied().filter(|a| a.demands_stubbing_use()) {
                let msg = format!(
                    "Using the {} attribute requires activating the unstable `stubbing` feature",
                    kind.as_ref()
                );
                self.tcx.dcx().span_err(self.span_for_kind(kind), msg);
            }
        }

        if let Some(unstable_attrs) = self.map.get(&KaniAttributeKind::Unstable) {
            for attr in unstable_attrs {
                let unstable_attr =
                    UnstableAttribute::try_from(*attr).expect("invalid unstable attribute");
                if !enabled_features.contains(&unstable_attr.feature) {
                    // Reached an unstable attribute that was not enabled.
                    self.report_unstable_forbidden(&unstable_attr);
                } else {
                    debug!(enabled=?attr, def_id=?self.item, "check_unstable_features");
                }
            }
        }
    }

    /// Report misusage of an unstable feature that was not enabled.
    fn report_unstable_forbidden(&self, unstable_attr: &UnstableAttribute) -> ErrorGuaranteed {
        let item_name = self.tcx.def_path_str(self.item);
        self.tcx
            .dcx()
            .struct_err(format!(
                "Use of unstable feature `{}`: {}",
                unstable_attr.feature, unstable_attr.reason
            ))
            .with_span_note(
                self.tcx.def_span(self.item),
                format!("the item `{item_name}` is unstable:"),
            )
            .with_note(format!("see issue {} for more information", unstable_attr.issue))
            .with_help(format!("use `-Z {}` to enable using this item.", unstable_attr.feature))
            .emit()
    }

    /// Is this item a harness? (either `proof` or `proof_for_contract`
    /// attribute are present)
    fn is_proof_harness(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::Proof)
            || self.map.contains_key(&KaniAttributeKind::ProofForContract)
    }

    /// Is this item a `kani::stub_set!` expansion?
    fn is_stub_set(&self) -> bool {
        self.map.contains_key(&KaniAttributeKind::StubSet)
    }

    /// Check that the function specified in the `proof_for_contract` attribute
    /// is reachable and emit an error if it isn't.
    /// This is different from the earlier `check_attributes` call:
    /// that checks that the specified target exists, but not if we can reach that target from the harness.
    pub(crate) fn check_proof_for_contract_reachability(
        &self,
        reachable_functions: &HashSet<DefIdStable>,
    ) {
        if let Some(def) = self.interpret_for_contract_attribute()
            && !reachable_functions.contains(&def.def_id())
        {
            let item_name = self.item_name();
            let target_name = def.trimmed_name();
            self.tcx.dcx().struct_span_err(
                self.tcx.def_span(self.item),
                format!(
                    "The function specified in the `proof_for_contract` attribute, `{target_name}`, is not reachable from the harness `{item_name}`.",
                )
            )
            .with_help(format!("Make sure that `{item_name}` calls `{target_name}`"))
            .emit();
        }
    }

    /// Extract harness attributes for a given `def_id`.
    ///
    /// We only extract attributes for harnesses that are local to the current crate.
    /// Note that all attributes should be valid by now.
    #[allow(clippy::panic)] // Internal validation - panics indicate compiler bugs
    pub(crate) fn harness_attributes(&self) -> HarnessAttributes {
        // Abort if not local.
        assert!(self.item.is_local(), "Expected a local item, but got: {:?}", self.item);
        trace!(?self, "extract_harness_attributes");
        assert!(self.is_proof_harness());
        let harness_attrs = if let Some(Ok(harness)) = self.proof_for_contract() {
            HarnessAttributes::new(HarnessKind::ProofForContract { target_fn: harness.to_string() })
        } else {
            HarnessAttributes::new(HarnessKind::Proof)
        };
        self.map.iter().fold(harness_attrs, |mut harness, (kind, attributes)| {
            match kind {
                KaniAttributeKind::ShouldPanic => harness.should_panic = true,
                KaniAttributeKind::Recursion => {
                    self.tcx.dcx().span_err(self.tcx.def_span(self.item), "The attribute `kani::recursion` should only be used in combination with function contracts.");
                }
                KaniAttributeKind::Solver => {
                    harness.solver = parse_solver(self.tcx, attributes[0]);
                }
                KaniAttributeKind::Stub => {
                    harness
                        .stubs
                        .extend_from_slice(&self.parse_stubs(self.current_module(), attributes));
                }
                KaniAttributeKind::UseStubSet => {
                    harness.stubs.extend(self.parse_stub_sets(self.current_module(), attributes));
                }
                KaniAttributeKind::Unwind => {
                    harness.unwind_value = parse_unwind(self.tcx, attributes[0]);
                }
                KaniAttributeKind::Proof => { /* no-op */ }
                KaniAttributeKind::ProofForContract => self.handle_proof_for_contract(attributes[0]),
                KaniAttributeKind::StubVerified => self.handle_stub_verified(&mut harness),
                KaniAttributeKind::Unstable => {
                    // Internal attribute which shouldn't exist here.
                    unreachable!("KaniAttributeKind::Unstable should be processed before harness attribute extraction")
                }
                KaniAttributeKind::StubSet => {
                    self.tcx.dcx().span_err(
                        self.tcx.def_span(self.item),
                        "`kani::stub_set!` cannot be used as a proof harness",
                    );
                }
                KaniAttributeKind::CheckedWith
                | KaniAttributeKind::IsContractGenerated
                | KaniAttributeKind::ModifiesWrapper
                | KaniAttributeKind::RecursionCheck
                | KaniAttributeKind::RecursionTracker
                | KaniAttributeKind::AssertedWith
                | KaniAttributeKind::ReplacedWith => {
                    self.tcx.dcx().span_err(self.tcx.def_span(self.item), format!("Contracts are not supported on harnesses. (Found the kani-internal contract attribute `{}`)", kind.as_ref()));
                }
                KaniAttributeKind::DisableChecks => {
                    // Internal attribute which shouldn't exist here.
                    unreachable!("KaniAttributeKind::DisableChecks should not appear on proof harnesses")
                }
                KaniAttributeKind::FnMarker => {
                    /* no-op */
                }
            }
            harness
        })
    }

    fn handle_proof_for_contract(&self, attr: &Attribute) {
        let target_def = match self.interpret_for_contract_attribute() {
            None => return, // This error was already emitted
            Some(def) => def,
        };
        let target_attributes = KaniAttributes::for_def_id(self.tcx, target_def.def_id());
        if target_attributes.contract_attributes().is_none() {
            self.tcx
                .dcx()
                .struct_span_err(
                    attr.span(),
                    format!(
                        "Failed to check contract: `{}` has no contract.",
                        target_attributes.item_name(),
                    ),
                )
                .with_span_note(
                    rustc_internal::internal(self.tcx, target_def.span()),
                    "Try adding a contract to this function.",
                )
                .emit();
        }
    }

    fn check_stub_verified(&self, attr: &Attribute) {
        let dcx = self.tcx.dcx();
        let mut seen = HashSet::new();
        for stub_target in self.interpret_stub_verified_attribute() {
            if seen.contains(&stub_target) {
                dcx.struct_span_warn(
                    rustc_internal::internal(self.tcx, stub_target.span()),
                    format!(
                        "Multiple occurrences of `stub_verified({})`.",
                        stub_target.trimmed_name()
                    ),
                )
                .with_help("Use a single annotation instead.")
                .emit();
            } else {
                seen.insert(stub_target);
            }
            if KaniAttributes::for_def_id(self.tcx, stub_target.def_id())
                .contract_attributes()
                .is_none()
            {
                dcx.struct_span_err(
                    attr.span(),
                    format!(
                        "Target function in stub_verified, `{}`, has no contract.",
                        stub_target.trimmed_name()
                    ),
                )
                    .with_span_note(
                        rustc_internal::internal(self.tcx, stub_target.span()),
                        "Try adding a contract to this function or use the unsound `stub` attribute instead.",
                    )
                    .emit();
            }
        }
    }

    /// Adds the verified stub names to the `harness.verified_stubs`.
    ///
    /// This method must be called after `check_stub_verified`, to ensure that
    /// the target names are known and have contracts, and there are no
    /// duplicate target names.
    fn handle_stub_verified(&self, harness: &mut HarnessAttributes) {
        for stub in self.interpret_stub_verified_attribute() {
            harness.verified_stubs.push(stub.name());
        }
    }

    fn item_name(&self) -> Symbol {
        self.tcx.item_name(self.item)
    }

    /// Check that if this item is tagged with a proof_attribute, it is a valid harness.
    fn check_proof_attribute(&self, kind: KaniAttributeKind, proof_attribute: &Attribute) {
        let span = proof_attribute.span();
        let tcx = self.tcx;
        if let KaniAttributeKind::Proof = kind {
            expect_no_args(tcx, kind, proof_attribute);
        }

        if tcx.def_kind(self.item) != DefKind::Fn {
            tcx.dcx().span_err(
                span,
                format!(
                    "the '#[kani::{}]' attribute can only be applied to functions",
                    kind.as_ref()
                ),
            );
        } else if tcx.generics_of(self.item).requires_monomorphization(tcx) {
            tcx.dcx().span_err(
                span,
                format!(
                    "the '#[kani::{}]' attribute cannot be applied to generic functions",
                    kind.as_ref()
                ),
            );
        }
    }

    fn resolve_path(
        &self,
        current_module: LocalDefId,
        path: &TypePath,
        span: Span,
    ) -> Result<FnResolution, ResolveError<'tcx>> {
        let result = resolve_fn_path(self.tcx, current_module, path);

        if let Err(ref resolve_err) = result {
            let mut err = self.tcx.dcx().struct_span_err(
                span,
                format!("failed to resolve `{}`: {resolve_err}", pretty_type_path(path)),
            );
            match resolve_err {
                ResolveError::AmbiguousPartialPath { .. } => {
                    err = err.with_help(format!(
                        "replace `{}` with a specific implementation.",
                        pretty_type_path(path)
                    ));
                }
                ResolveError::MissingTraitImpl { tcx: _, trait_fn_id, ty: _ } => {
                    let generics = self.tcx.generics_of(trait_fn_id);
                    let parent_generics =
                        generics.parent.map(|parent| self.tcx.generics_of(parent));
                    if !generics.own_params.is_empty()
                        || parent_generics.is_some_and(|generics| !generics.own_params.is_empty())
                    {
                        err = err.with_note(
                            "trust_mc does not currently support stubs or function contracts on generic functions in traits.\n \
                            See https://github.com/model-checking/kani/issues/1997#issuecomment-3134614734 for more information.",
                        );
                    }
                }
                ResolveError::AmbiguousGlob { .. }
                | ResolveError::ExtraSuper
                | ResolveError::InvalidPath { .. }
                | ResolveError::MissingItem { .. }
                | ResolveError::MissingPrimitiveItem { .. }
                | ResolveError::UnexpectedType { .. }
                | ResolveError::UnsupportedPath { .. } => {}
            }
            err.emit();
        }

        result
    }

    /// The module that unqualified paths on this item resolve relative to.
    fn current_module(&self) -> LocalDefId {
        self.tcx.parent_module_from_def_id(self.item.expect_local()).to_local_def_id()
    }

    /// Parse an attribute of the form #[kanitool::key = value], where value is the path to a function.
    fn parse_single_path_attr(
        &self,
        attr: &'tcx Attribute,
    ) -> Result<FnResolution, ResolveError<'tcx>> {
        self.resolve_single_path_attr_in(self.current_module(), attr)
    }

    /// Like [`Self::parse_single_path_attr`], but resolves the path relative to
    /// an explicit module rather than the module enclosing `self.item`. Stub set
    /// members are resolved relative to the *consuming harness*, so expansion
    /// threads the harness module through here.
    #[allow(clippy::panic)] // Internal validation - panics indicate compiler bugs
    fn resolve_single_path_attr_in(
        &self,
        current_module: LocalDefId,
        attr: &'tcx Attribute,
    ) -> Result<FnResolution, ResolveError<'tcx>> {
        let target = expect_key_string_value(self.tcx.sess, attr)
            .unwrap_or_else(|_| panic!("malformed attribute"));
        let target_str = target.as_str();
        let path = syn::parse_str(target_str).map_err(|err| ResolveError::InvalidPath {
            msg: format!("Expected a path, but found `{target_str}`. {err}"),
        });

        match path {
            Ok(path) => self.resolve_path(current_module, &path, attr.span()),
            Err(err) => {
                self.tcx.dcx().span_err(attr.span(), err.to_string());
                Err(err)
            }
        }
    }

    fn parse_stubs(&self, current_module: LocalDefId, attributes: &[&'tcx Attribute]) -> Vec<Stub> {
        attributes
        .iter()
        .filter_map(|attr| {
            let paths = parse_paths(self.tcx, attr).unwrap_or_else(|_| {
                self.tcx.dcx().span_err(
                    attr.span(),
                    "attribute `kani::stub` takes two path arguments; found argument that is not a path"
                );
                vec![]
            });
            match paths.as_slice() {
                [orig, replace] => {
                    let original_res = self.resolve_path(current_module, orig, attr.span()).map(|res| res.def());
                    let replace_res = self.resolve_path(current_module, replace, attr.span()).map(|res| res.def());

                    if let Ok(original_res) = original_res && let Ok(replace_res) = replace_res {
                        // Emit an error if either function is local, yet doesn't have a body.
                        // This can happen if a user specifies a trait fn without a default body, e.g. B::bar, where B is a trait.
                        // But extern functions are allowed - they don't have bodies but are valid stub targets (#983).
                        let o_foreign = self.tcx.is_foreign_item(rustc_internal::internal(self.tcx, original_res.def_id()));
                        let r_foreign = self.tcx.is_foreign_item(rustc_internal::internal(self.tcx, replace_res.def_id()));
                        let o_bad = original_res.krate().is_local && !original_res.has_body() && !o_foreign;
                        let r_bad = replace_res.krate().is_local && !replace_res.has_body() && !r_foreign;

                        if o_bad || r_bad {
                            let mut err = self.tcx.dcx().struct_span_err(
                                attr.span(),
                                "invalid stub: function does not have a body, but is not an extern function",
                            );
                            if o_bad {
                                err = err.with_span_note(
                                    rustc_internal::internal(self.tcx, original_res.span()),
                                    format!(
                                    "`{}` does not have a body",
                                    original_res.name()
                                ));
                            }
                            if r_bad {
                                err = err.with_span_note(
                                    rustc_internal::internal(self.tcx, replace_res.span()),
                                    format!(
                                    "`{}` does not have a body",
                                    replace_res.name()
                                ));
                            }
                            err = err.with_help(
                                "if this stub refers to associated functions, try using fully-qualified syntax instead"
                            );
                            err.emit();
                        }
                    }

                    Some(Stub {
                        original: orig.to_token_stream().to_string(),
                        replacement: replace.to_token_stream().to_string(),
                    })
                }
                [] => {
                    /* Error was already emitted */
                    None
                }
                _ => { // non-enum: slice (paths — more than two)
                    self.tcx.dcx().span_err(
                        attr.span(),
                        format!(
                            "attribute `kani::stub` takes two path arguments; found {}",
                            paths.len()
                        ),
                    );
                    None
                }
            }
        })
        .collect()
    }

    fn parse_stub_sets(
        &self,
        resolve_module: LocalDefId,
        attributes: &[&'tcx Attribute],
    ) -> Vec<Stub> {
        let mut stack = HashSet::new();
        attributes
            .iter()
            .flat_map(|attr| self.parse_stub_set(resolve_module, attr, &mut stack))
            .collect()
    }

    fn parse_stub_set(
        &self,
        resolve_module: LocalDefId,
        attr: &'tcx Attribute,
        stack: &mut HashSet<DefId>,
    ) -> Vec<Stub> {
        // The name in `use_stub_set(NAME)` must resolve to a
        // `kani::stub_set!`-generated marker fn, reached relative to the
        // consuming harness's module. Resolve without the generic
        // resolve-error path so that anything which is not a stub set (e.g. a
        // constant, or an unknown name) produces one clear diagnostic.
        let name_str =
            expect_key_string_value(self.tcx.sess, attr).map(|s| s.to_string()).unwrap_or_default();
        let resolved = syn::parse_str::<TypePath>(name_str.trim())
            .ok()
            .and_then(|path| resolve_fn_path(self.tcx, resolve_module, &path).ok());
        let Some(stub_set) = resolved else {
            self.tcx.dcx().span_err(
                attr.span(),
                format!(
                    "`{}` is not a stub set (missing `kani::stub_set!` definition)",
                    name_str.trim()
                ),
            );
            return vec![];
        };
        let stub_set_name = stub_set.def().trimmed_name();
        let stub_set_def = rustc_internal::internal(self.tcx, stub_set.def().def_id());
        if !stub_set_def.is_local() {
            self.tcx.dcx().span_err(
                attr.span(),
                format!(
                    "stub set `{}` is defined in another crate, which is not currently supported",
                    stub_set_name
                ),
            );
            return vec![];
        }

        let stub_set_attrs = KaniAttributes::for_item(self.tcx, stub_set_def);
        if !stub_set_attrs.is_stub_set() {
            self.tcx.dcx().span_err(
                attr.span(),
                format!(
                    "`{stub_set_name}` is not a stub set (missing `kani::stub_set!` definition)"
                ),
            );
            return vec![];
        }
        if !stack.insert(stub_set_def) {
            self.tcx
                .dcx()
                .span_err(attr.span(), format!("circular stub set reference: `{stub_set_name}`"));
            return vec![];
        }

        let stubs = stub_set_attrs.expand_stub_set(resolve_module, stack);
        stack.remove(&stub_set_def);
        stubs
    }

    fn expand_stub_set(&self, resolve_module: LocalDefId, stack: &mut HashSet<DefId>) -> Vec<Stub> {
        let mut stubs = vec![];
        if let Some(attributes) = self.map.get(&KaniAttributeKind::Stub) {
            stubs.extend(self.parse_stubs(resolve_module, attributes));
        }
        if let Some(attributes) = self.map.get(&KaniAttributeKind::UseStubSet) {
            for attr in attributes {
                stubs.extend(self.parse_stub_set(resolve_module, attr, stack));
            }
        }
        stubs
    }
}

pub(crate) fn check_stable_tool_unstable_features<T: CrateDef>(
    tcx: TyCtxt,
    def_id: DefIdStable,
    def: T,
    enabled_features: &[String],
) {
    let attributes = KaniAttributes::for_def_id(tcx, def_id);
    for unstable_attr in stable_tool_unstable_attrs(def) {
        match unstable_attr {
            Ok(unstable_attr) => {
                if !enabled_features.contains(&unstable_attr.feature) {
                    attributes.report_unstable_forbidden(&unstable_attr);
                }
            }
            Err(reason) => {
                let internal_def_id = rustc_internal::internal(tcx, def_id);
                tcx.dcx().span_err(
                    tcx.def_span(internal_def_id),
                    format!("failed to parse `#[kanitool::unstable]`: {reason}"),
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::KaniAttributeKind;
    use std::str::FromStr;

    // =========================================================================
    // KaniAttributeKind strum round-trip (Part of #2190)
    // =========================================================================

    /// All 20 KaniAttributeKind variants. Update this constant when variants are
    /// added or removed — any mismatch fails the count guard test below.
    const ALL_VARIANTS: [(&str, KaniAttributeKind); 20] = [
        ("proof", KaniAttributeKind::Proof),
        ("should_panic", KaniAttributeKind::ShouldPanic),
        ("solver", KaniAttributeKind::Solver),
        ("stub", KaniAttributeKind::Stub),
        ("stub_set", KaniAttributeKind::StubSet),
        ("use_stub_set", KaniAttributeKind::UseStubSet),
        ("unstable", KaniAttributeKind::Unstable),
        ("unwind", KaniAttributeKind::Unwind),
        ("stub_verified", KaniAttributeKind::StubVerified),
        ("proof_for_contract", KaniAttributeKind::ProofForContract),
        ("asserted_with", KaniAttributeKind::AssertedWith),
        ("checked_with", KaniAttributeKind::CheckedWith),
        ("replaced_with", KaniAttributeKind::ReplacedWith),
        ("recursion_check", KaniAttributeKind::RecursionCheck),
        ("is_contract_generated", KaniAttributeKind::IsContractGenerated),
        ("modifies_wrapper", KaniAttributeKind::ModifiesWrapper),
        ("recursion", KaniAttributeKind::Recursion),
        ("recursion_tracker", KaniAttributeKind::RecursionTracker),
        ("fn_marker", KaniAttributeKind::FnMarker),
        ("disable_checks", KaniAttributeKind::DisableChecks),
    ];

    #[test]
    fn strum_round_trip_all_variants() {
        for (name, expected) in ALL_VARIANTS {
            let parsed = KaniAttributeKind::from_str(name)
                .expect("all KaniAttributeKind variants should round-trip through from_str");
            assert_eq!(parsed, expected, "Mismatch for {name}");
            assert_eq!(parsed.as_ref(), name, "as_ref round-trip failed for {name}");
        }
    }

    /// Guard: is_harness_only covers every variant. The two test arrays below
    /// must sum to ALL_VARIANTS.len() — if a variant is added and not classified,
    /// this test fails.
    #[test]
    fn is_harness_only_exhaustive() {
        let harness_count = ALL_VARIANTS.iter().filter(|(_, k)| k.is_harness_only()).count();
        let non_harness_count = ALL_VARIANTS.iter().filter(|(_, k)| !k.is_harness_only()).count();
        assert_eq!(
            harness_count + non_harness_count,
            ALL_VARIANTS.len(),
            "is_harness_only must classify every variant"
        );
        assert_eq!(harness_count, 8, "harness-only variant count changed");
        assert_eq!(non_harness_count, 12, "non-harness variant count changed");
    }

    #[test]
    fn strum_rejects_unknown_strings() {
        assert!(KaniAttributeKind::from_str("unknown").is_err());
        assert!(KaniAttributeKind::from_str("").is_err());
        assert!(KaniAttributeKind::from_str("Proof").is_err()); // wrong case
        assert!(KaniAttributeKind::from_str("proof_").is_err());
    }

    // =========================================================================
    // is_harness_only (Part of #2190)
    // =========================================================================

    #[test]
    fn is_harness_only_true_for_harness_attributes() {
        let harness_only = [
            KaniAttributeKind::Proof,
            KaniAttributeKind::ShouldPanic,
            KaniAttributeKind::Solver,
            KaniAttributeKind::Stub,
            KaniAttributeKind::UseStubSet,
            KaniAttributeKind::ProofForContract,
            KaniAttributeKind::StubVerified,
            KaniAttributeKind::Unwind,
        ];
        for attr in harness_only {
            assert!(attr.is_harness_only(), "{attr:?} should be harness-only");
        }
    }

    #[test]
    fn is_harness_only_false_for_general_attributes() {
        let not_harness_only = [
            KaniAttributeKind::Unstable,
            KaniAttributeKind::StubSet,
            KaniAttributeKind::FnMarker,
            KaniAttributeKind::Recursion,
            KaniAttributeKind::RecursionTracker,
            KaniAttributeKind::ReplacedWith,
            KaniAttributeKind::RecursionCheck,
            KaniAttributeKind::CheckedWith,
            KaniAttributeKind::ModifiesWrapper,
            KaniAttributeKind::AssertedWith,
            KaniAttributeKind::IsContractGenerated,
            KaniAttributeKind::DisableChecks,
        ];
        for attr in not_harness_only {
            assert!(!attr.is_harness_only(), "{attr:?} should NOT be harness-only");
        }
    }

    // =========================================================================
    // demands_function_contract_use (Part of #2190)
    // =========================================================================

    #[test]
    fn demands_contract_use_only_proof_for_contract() {
        assert!(KaniAttributeKind::ProofForContract.demands_function_contract_use());
        // All others should be false
        assert!(!KaniAttributeKind::Proof.demands_function_contract_use());
        assert!(!KaniAttributeKind::Stub.demands_function_contract_use());
        assert!(!KaniAttributeKind::StubVerified.demands_function_contract_use());
    }

    // =========================================================================
    // demands_stubbing_use (Part of #2190)
    // =========================================================================

    #[test]
    fn demands_stubbing_use_stub_variants() {
        assert!(KaniAttributeKind::Stub.demands_stubbing_use());
        assert!(KaniAttributeKind::StubVerified.demands_stubbing_use());
        assert!(KaniAttributeKind::UseStubSet.demands_stubbing_use());
        // All others should be false
        assert!(!KaniAttributeKind::Proof.demands_stubbing_use());
        assert!(!KaniAttributeKind::ProofForContract.demands_stubbing_use());
        assert!(!KaniAttributeKind::FnMarker.demands_stubbing_use());
    }

    #[test]
    fn is_stub_set_member_only_for_stub_set_contents() {
        assert!(KaniAttributeKind::Stub.is_stub_set_member());
        assert!(KaniAttributeKind::UseStubSet.is_stub_set_member());
        assert!(!KaniAttributeKind::Proof.is_stub_set_member());
        assert!(!KaniAttributeKind::StubSet.is_stub_set_member());
    }
}
