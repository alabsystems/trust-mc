// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module handles Kani metadata generation. For example, generating HarnessMetadata for a
//! given function.

use std::collections::HashMap;
use std::path::Path;

use crate::kani_middle::codegen_units::Harness;
use crate::kani_middle::{KaniAttributes, SourceLocation};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::{CrateDef, CrateItems, DefId};
use trust_mc_metadata::ContractedFunction;
use trust_mc_metadata::{ArtifactType, HarnessAttributes, HarnessKind, HarnessMetadata};

use sha1_checked::Sha1;

/// Create the harness metadata for a proof harness for a given function.
pub(crate) fn gen_proof_metadata(
    tcx: TyCtxt,
    instance: Instance,
    base_name: &Path,
) -> HarnessMetadata {
    let def = instance.def;
    let kani_attributes = KaniAttributes::for_instance(tcx, instance);
    let pretty_name = instance.name();
    let mangled_name = instance.mangled_name();

    // We get the body span to include the entire function definition.
    // This is required for concrete playback to properly position the generated test.
    let loc = SourceLocation::new(instance.body().expect("proof harness should have body").span);
    let stem = base_name.file_stem().expect("output path should have file stem");
    let stem_str = stem.to_str().expect("output path file stem should be valid UTF-8");
    let file_stem = format!("{stem_str}_{mangled_name}");
    let model_file = base_name.with_file_name(file_stem).with_extension(ArtifactType::ModelBase);

    HarnessMetadata {
        pretty_name,
        mangled_name,
        crate_name: def.krate().name,
        original_file: loc.filename,
        original_start_line: loc.start_line,
        original_end_line: loc.end_line,
        attributes: kani_attributes.harness_attributes(),
        model_file,
        contract: Default::default(),
        has_loop_contracts: false,
        is_automatically_generated: false,
    }
}

/// Collects contract and contract harness metadata.
///
/// For each function with contracts (or that is a target of a contract harness),
/// construct a `ContractedFunction` object for it.
pub(crate) fn gen_contracts_metadata(
    tcx: TyCtxt,
    harness_info: &HashMap<Harness, HarnessMetadata>,
) -> Vec<ContractedFunction> {
    // We work with `rustc_public::CrateItem` instead of `rustc_public::Instance` to include generic items
    let crate_items: CrateItems = rustc_public::all_local_items();

    let mut fn_to_data: HashMap<DefId, ContractedFunction> = HashMap::new();

    for item in crate_items {
        let function = item.name();
        let file = SourceLocation::new(item.span()).filename;
        let attributes = KaniAttributes::for_def_id(tcx, item.def_id());

        if attributes.has_contract() {
            fn_to_data
                .insert(item.def_id(), ContractedFunction { function, file, harnesses: vec![] });
        // This logic finds manual contract harnesses only (automatic harnesses are a Kani intrinsic, not crate items annotated with the proof_for_contract attribute).
        } else if let Some(def) = attributes.interpret_for_contract_attribute() {
            let target_def_id = def.def_id();
            if let Some(cf) = fn_to_data.get_mut(&target_def_id) {
                cf.harnesses.push(function);
            } else {
                fn_to_data.insert(
                    target_def_id,
                    ContractedFunction {
                        // Note that we use the item's fully qualified-name, rather than the target name specified in the attribute.
                        // This is necessary for the automatic contract harness lookup, see below.
                        function: item.name(),
                        file,
                        harnesses: vec![function],
                    },
                );
            }
        }
    }

    // Find automatically generated contract harnesses (if the `autoharness` subcommand is running)
    // Build name→DefId index for O(1) lookups instead of O(n) linear search per harness (#1537)
    // Note: We can't resolve target_fn to a DefId because automatic harnesses
    // are Kani intrinsics with no resolution starting point. Instead we match
    // on the fully qualified name stored in ContractedFunction objects, which
    // gen_automatic_proof_metadata also uses. This will need revision when we
    // support multiple automatic harnesses per function (e.g., generics).
    let name_to_def_id: HashMap<String, DefId> =
        fn_to_data.iter().map(|(def_id, cf)| (cf.function.clone(), *def_id)).collect();

    // Collect updates to apply (avoids borrow conflict with name_to_def_id)
    let updates: Vec<(DefId, String)> = harness_info
        .iter()
        .filter(|(_, metadata)| metadata.is_automatically_generated)
        .filter_map(|(harness, metadata)| {
            if let HarnessKind::ProofForContract { target_fn } = &metadata.attributes.kind {
                let def_id = name_to_def_id
                    .get(target_fn)
                    .expect("target function should be in contracted functions map");
                Some((*def_id, harness.name()))
            } else {
                None
            }
        })
        .collect();

    // Apply updates
    for (def_id, harness_name) in updates {
        let target_cf = fn_to_data.get_mut(&def_id).expect("DefId should exist in fn_to_data");
        target_cf.harnesses.push(harness_name);
    }

    fn_to_data.into_values().collect()
}

/// Generate metadata for automatically generated harnesses.
/// For now, we just use the data from the function we are verifying; since we only generate one automatic harness per function,
/// the metdata from that function uniquely identifies the harness.
/// Note: When multiple harnesses per function are supported (e.g., for generics),
/// HarnessMetadata will need to differentiate between them.
pub(crate) fn gen_automatic_proof_metadata(
    tcx: TyCtxt,
    base_name: &Path,
    fn_to_verify: &Instance,
    harness_mangled_name: String,
) -> HarnessMetadata {
    let def = fn_to_verify.def;
    let pretty_name = fn_to_verify.name();
    let mangled_name = fn_to_verify.mangled_name();

    // Leave the concrete playback instrumentation for now, but this feature does not actually support concrete playback.
    let loc =
        SourceLocation::new(fn_to_verify.body().expect("function to verify should have body").span);
    let sha1_result = Sha1::try_digest(mangled_name);
    assert!(!sha1_result.has_collision());
    let stem = base_name.file_stem().expect("output path should have file stem");
    let stem_str = stem.to_str().expect("output path file stem should be valid UTF-8");
    let file_stem = format!("{stem_str}_{:x}_autoharness", sha1_result.hash());
    let model_file = base_name.with_file_name(file_stem).with_extension(ArtifactType::ModelBase);

    let kani_attributes = KaniAttributes::for_instance(tcx, *fn_to_verify);
    let harness_kind = if kani_attributes.has_contract() {
        HarnessKind::ProofForContract { target_fn: pretty_name.clone() }
    } else {
        HarnessKind::Proof
    };

    HarnessMetadata {
        // pretty_name is what gets displayed to the user, and that should be the name of the function being verified, hence using fn_to_verify name
        pretty_name,
        // The mangled name selects the entry point — must be the mangled name of the automatic harness intrinsic
        mangled_name: harness_mangled_name,
        crate_name: def.krate().name,
        original_file: loc.filename,
        original_start_line: loc.start_line,
        original_end_line: loc.end_line,
        attributes: HarnessAttributes::new(harness_kind),
        model_file,
        contract: Default::default(),
        has_loop_contracts: false,
        is_automatically_generated: true,
    }
}
