// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// This module invokes the compiler to gather the metadata for the list subcommand, then post-processes the output.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use crate::{
    CliIdentity, InvocationType,
    args::{
        VerificationArgs,
        list_args::{CargoListArgs, Format, StandaloneListArgs},
    },
    list::output::output_list_results,
    list::{
        FileName, HarnessName, ListMetadata, ProofObligation, ProofObligationRole,
        ProofObligationSource,
    },
    metadata::from_json,
    project::{Project, standalone_project, std_project},
    session::KaniSession,
    version::print_kani_version,
};
use anyhow::Result;
use trust_mc_metadata::{ContractedFunction, HarnessKind, HarnessMetadata, KaniMetadata};

fn proof_obligation(harness_meta: &HarnessMetadata) -> Option<ProofObligation> {
    let (role, source_form, target, id_kind) = match &harness_meta.attributes.kind {
        HarnessKind::Proof => (
            ProofObligationRole::Harness,
            ProofObligationSource::KaniProofAttribute,
            None,
            "kani-proof",
        ),
        HarnessKind::ProofForContract { target_fn } => (
            ProofObligationRole::ContractHarness,
            ProofObligationSource::KaniProofForContractAttribute,
            Some(target_fn.clone()),
            "kani-proof-for-contract",
        ),
        HarnessKind::Test => return None,
    };

    Some(ProofObligation {
        proof_item_id: format!(
            "trust_mc:{id_kind}:{}:{}",
            harness_meta.crate_name, harness_meta.pretty_name
        ),
        crate_name: harness_meta.crate_name.clone(),
        harness: harness_meta.pretty_name.clone(),
        role,
        source_form,
        target,
        file: harness_meta.original_file.clone(),
        start_line: harness_meta.original_start_line,
        end_line: harness_meta.original_end_line,
        engine: "trust-mc",
        required_by_full_verify: true,
    })
}

/// Process the KaniMetadata output from kani-compiler and output the list subcommand results
pub(crate) fn process_metadata(metadata: Vec<KaniMetadata>) -> BTreeSet<ListMetadata> {
    let mut list_metadata: BTreeSet<ListMetadata> = BTreeSet::new();

    let insert = |harness_meta: HarnessMetadata,
                  map: &mut BTreeMap<FileName, BTreeSet<HarnessName>>,
                  count: &mut usize| {
        *count += 1;
        if let Some(harnesses) = map.get_mut(&harness_meta.original_file) {
            harnesses.insert(harness_meta.pretty_name);
        } else {
            map.insert(harness_meta.original_file, BTreeSet::from([harness_meta.pretty_name]));
        }
    };

    for kani_meta in metadata {
        // We use ordered maps and sets so that the output is in lexicographic order (and consistent across invocations).
        let mut standard_harnesses: BTreeMap<FileName, BTreeSet<HarnessName>> = BTreeMap::new();
        let mut contract_harnesses: BTreeMap<FileName, BTreeSet<HarnessName>> = BTreeMap::new();
        let mut contracted_functions: BTreeSet<ContractedFunction> = BTreeSet::new();
        let mut proof_obligations: BTreeSet<ProofObligation> = BTreeSet::new();

        let mut standard_harnesses_count = 0;
        let mut contract_harnesses_count = 0;

        for harness_meta in kani_meta.proof_harnesses {
            if let Some(obligation) = proof_obligation(&harness_meta) {
                proof_obligations.insert(obligation);
            }

            match &harness_meta.attributes.kind {
                HarnessKind::Proof => {
                    insert(harness_meta, &mut standard_harnesses, &mut standard_harnesses_count);
                }
                HarnessKind::ProofForContract { .. } => {
                    insert(harness_meta, &mut contract_harnesses, &mut contract_harnesses_count);
                }
                HarnessKind::Test => {}
            }
        }

        contracted_functions.extend(kani_meta.contracted_functions.into_iter());

        list_metadata.insert(ListMetadata {
            crate_name: kani_meta.crate_name,
            standard_harnesses,
            standard_harnesses_count,
            contract_harnesses,
            contract_harnesses_count,
            contracted_functions,
            proof_obligations,
        });
    }

    list_metadata
}

pub(crate) fn list_cargo(
    args: CargoListArgs,
    mut verify_opts: VerificationArgs,
    identity: CliIdentity,
) -> Result<()> {
    verify_opts.common_args = args.common_args;
    list_cargo_with_format(args.format, verify_opts, identity)
}

pub(crate) fn list_cargo_with_format(
    format: Format,
    mut verify_opts: VerificationArgs,
    identity: CliIdentity,
) -> Result<()> {
    let quiet = verify_opts.common_args.quiet;
    let verbose = verify_opts.common_args.verbose;
    prepare_verify_opts_for_listing(&mut verify_opts);
    let mut session = KaniSession::new_for_listing(verify_opts)?;
    if !quiet {
        print_kani_version(InvocationType::CargoKani { args: vec![], identity }, verbose);
    }

    let outputs = session.cargo_build(false)?;
    let metadata_paths = metadata_paths_for_listing(&outputs.metadata, &outputs.outdir)?;
    let metadata =
        metadata_paths.iter().map(|md_file| from_json(md_file)).collect::<Result<Vec<_>>>()?;
    let list_metadata = process_metadata(metadata);

    output_list_results(list_metadata, format, quiet, identity)
}

pub(crate) fn list_standalone(
    args: StandaloneListArgs,
    mut verify_opts: VerificationArgs,
    identity: CliIdentity,
) -> Result<()> {
    let input = args.input;
    let crate_name = args.crate_name;
    let std = args.std;
    verify_opts.common_args = args.common_args;
    list_standalone_with_format(input, crate_name, std, args.format, verify_opts, identity)
}

pub(crate) fn list_standalone_with_format(
    input: PathBuf,
    crate_name: Option<String>,
    std: bool,
    format: Format,
    mut verify_opts: VerificationArgs,
    identity: CliIdentity,
) -> Result<()> {
    let quiet = verify_opts.common_args.quiet;
    let verbose = verify_opts.common_args.verbose;
    prepare_verify_opts_for_listing(&mut verify_opts);
    let session = KaniSession::new_for_listing(verify_opts)?;
    if !quiet {
        print_kani_version(InvocationType::Standalone { identity }, verbose);
    }

    let project: Project = if std {
        std_project(&input, &session)?
    } else {
        standalone_project(&input, crate_name, &session)?
    };

    let list_metadata = process_metadata(project.metadata);

    output_list_results(list_metadata, format, quiet, identity)
}

fn prepare_verify_opts_for_listing(verify_opts: &mut VerificationArgs) {
    // Listing is metadata-only from the driver's perspective, but the compiler
    // emits harness metadata from the backend. Keep the backend running while
    // asking it to stop before per-harness verification-condition generation.
    verify_opts.no_codegen = false;
    verify_opts.list_metadata_only = true;
}

fn metadata_paths_for_listing<P: AsRef<Path>>(
    metadata: &[P],
    outdir: &Path,
) -> Result<Vec<PathBuf>> {
    let paths: Vec<PathBuf> =
        metadata.iter().map(|artifact| artifact.as_ref().to_path_buf()).collect();
    if !paths.is_empty() {
        return Ok(paths);
    }

    let mut discovered = vec![];
    for entry in std::fs::read_dir(outdir)? {
        let entry = entry?;
        let path = entry.path();
        if path
            .file_name()
            .is_some_and(|name| name.to_string_lossy().ends_with(".kani-metadata.json"))
        {
            discovered.push(path);
        }
    }
    discovered.sort();
    Ok(discovered)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{test_harness, test_metadata_all};
    use clap::Parser;
    use trust_mc_metadata::{HarnessAttributes, HarnessKind};

    #[test]
    fn process_metadata_exports_required_kani_proof_obligations() {
        let mut standard = test_harness("module::check_standard", "proof_crate");
        standard.original_file = "src/lib.rs".to_string();
        standard.original_start_line = 10;
        standard.original_end_line = 12;

        let mut contract = test_harness("module::check_contract", "proof_crate");
        contract.attributes =
            HarnessAttributes::new(HarnessKind::ProofForContract { target_fn: "target_fn".into() });
        contract.original_file = "src/contracts.rs".to_string();
        contract.original_start_line = 20;
        contract.original_end_line = 24;

        let mut metadata =
            test_metadata_all("proof_crate", None, None, None, None, None, None, None, None);
        metadata.proof_harnesses = vec![standard, contract];

        let list_metadata = process_metadata(vec![metadata]);
        let crate_metadata = list_metadata.iter().next().expect("crate metadata");

        assert_eq!(crate_metadata.standard_harnesses_count, 1);
        assert_eq!(crate_metadata.contract_harnesses_count, 1);
        assert_eq!(crate_metadata.proof_obligations.len(), 2);

        let ids: BTreeSet<&str> = crate_metadata
            .proof_obligations
            .iter()
            .map(|obligation| obligation.proof_item_id.as_str())
            .collect();
        assert!(ids.contains("trust_mc:kani-proof:proof_crate:module::check_standard"));
        assert!(
            ids.contains("trust_mc:kani-proof-for-contract:proof_crate:module::check_contract")
        );

        let contract_obligation = crate_metadata
            .proof_obligations
            .iter()
            .find(|obligation| obligation.harness == "module::check_contract")
            .expect("contract harness obligation");
        assert_eq!(contract_obligation.role, ProofObligationRole::ContractHarness);
        assert_eq!(
            contract_obligation.source_form,
            ProofObligationSource::KaniProofForContractAttribute
        );
        assert_eq!(contract_obligation.target.as_deref(), Some("target_fn"));
        assert!(contract_obligation.required_by_full_verify);
    }

    #[test]
    fn listing_enables_compiler_metadata_only_mode() {
        let mut args =
            crate::args::CargoKaniArgs::try_parse_from(["cargo-trust-mc"]).unwrap().verify_opts;
        args.no_codegen = true;
        assert!(!args.list_metadata_only);

        prepare_verify_opts_for_listing(&mut args);

        assert!(!args.no_codegen);
        assert!(args.list_metadata_only);
    }

    #[test]
    fn listing_discovers_metadata_when_no_artifact_is_reported() {
        let temp = tempfile::tempdir().unwrap();
        let metadata_path = temp.path().join("crate.kani-metadata.json");
        std::fs::write(&metadata_path, "{}").unwrap();
        std::fs::write(temp.path().join("crate.rmeta"), "").unwrap();

        let paths = metadata_paths_for_listing::<PathBuf>(&[], temp.path()).unwrap();

        assert_eq!(paths, vec![metadata_path]);
    }
}
