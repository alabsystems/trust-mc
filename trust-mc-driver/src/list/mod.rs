// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Implements the list subcommand logic

use anyhow::Result;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use trust_mc_metadata::ContractedFunction;

pub(crate) mod collect_metadata;
pub(crate) mod output;

type FileName = String;
type HarnessName = String;

/// Machine-readable proof obligation exported for verifier-run consumers.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) struct ProofObligation {
    #[serde(rename = "proof-item-id")]
    pub proof_item_id: String,
    #[serde(rename = "crate")]
    pub crate_name: String,
    pub harness: String,
    pub role: ProofObligationRole,
    #[serde(rename = "source-form")]
    pub source_form: ProofObligationSource,
    pub target: Option<String>,
    pub file: String,
    #[serde(rename = "start-line")]
    pub start_line: usize,
    #[serde(rename = "end-line")]
    pub end_line: usize,
    pub engine: &'static str,
    #[serde(rename = "required-by-full-verify")]
    pub required_by_full_verify: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum ProofObligationRole {
    Harness,
    ContractHarness,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum ProofObligationSource {
    KaniProofAttribute,
    KaniProofForContractAttribute,
}

/// Metadata for the list subcommand for a given crate.
/// It is important that crate_name is the first field so that `Ord` orders two ListMetadata objects by crate name.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ListMetadata {
    crate_name: String,
    // Files mapped to their #[kani::proof] harnesses
    standard_harnesses: BTreeMap<FileName, BTreeSet<HarnessName>>,
    // Total number of #[kani::proof] harnesses
    standard_harnesses_count: usize,
    // Files mapped to their #[kani::proof_for_contract] harnesses
    contract_harnesses: BTreeMap<FileName, BTreeSet<HarnessName>>,
    // Total number of #[kani:proof_for_contract] harnesses
    contract_harnesses_count: usize,
    // Set of all functions under contract
    contracted_functions: BTreeSet<ContractedFunction>,
    // Fail-closed proof inventory for tRust and other verifier-run consumers
    proof_obligations: BTreeSet<ProofObligation>,
}

/// Given a collection of ListMetadata objects, merge them into a single ListMetadata object.
pub(crate) fn merge_list_metadata<T>(collection: T) -> Result<ListMetadata>
where
    T: Extend<ListMetadata>,
    T: IntoIterator<Item = ListMetadata>,
{
    collection
        .into_iter()
        .reduce(|mut acc, item| {
            acc.standard_harnesses.extend(item.standard_harnesses);
            acc.standard_harnesses_count += item.standard_harnesses_count;
            acc.contract_harnesses.extend(item.contract_harnesses);
            acc.contract_harnesses_count += item.contract_harnesses_count;
            acc.contracted_functions.extend(item.contracted_functions);
            acc.proof_obligations.extend(item.proof_obligations);
            acc
        })
        .ok_or_else(|| anyhow::anyhow!("cannot merge empty collection of ListMetadata objects"))
}
