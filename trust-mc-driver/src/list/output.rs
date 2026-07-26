// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module handles outputting the result for the list subcommand

use std::{
    collections::BTreeSet,
    fmt::Display,
    fs::File,
    io::{BufWriter, Write},
    path::Path,
};

use crate::{
    CliIdentity,
    args::list_args::Format,
    list::{ListMetadata, merge_list_metadata},
    version::KANI_VERSION,
};
use anyhow::Result;
use comfy_table::Table as PrettyTable;
use serde_json::{Value, json};
use to_markdown_table::MarkdownTable;

// Represents the version of our JSON file format.
// Increment this version (according to semantic versioning rules) whenever the JSON output format changes.
const FILE_VERSION: &str = "0.2";

/// Output the results of the list subcommand.
pub(crate) fn output_list_results(
    list_metadata: BTreeSet<ListMetadata>,
    format: Format,
    quiet: bool,
    identity: CliIdentity,
) -> Result<()> {
    match format {
        Format::Pretty => pretty(list_metadata),
        Format::Markdown => markdown(list_metadata, quiet, identity),
        Format::Json => json(list_metadata, quiet, identity),
    }
}

fn pretty_constructor(header: Vec<String>, rows: Vec<Vec<String>>) -> Result<PrettyTable> {
    let mut t = PrettyTable::new();
    t.set_header(header).add_rows(rows);
    Ok(t)
}

fn markdown_constructor(header: Vec<String>, rows: Vec<Vec<String>>) -> Result<MarkdownTable> {
    Ok(MarkdownTable::new(Some(header), rows)?)
}

/// Construct the "Contracts" and "Standard Harnesses" tables.
/// `table_constructor` is a function that, given the header and rows for the tables, creates a particular kind of table.
fn construct_output<T: Display>(
    list_metadata: BTreeSet<ListMetadata>,
    table_constructor: fn(Vec<String>, Vec<Vec<String>>) -> Result<T>,
) -> Result<(String, String)> {
    let contract_output = {
        const CONTRACTS_SECTION: &str = "Contracts:";
        const NO_CONTRACTS_MSG: &str = "No contracts or contract harnesses found.";
        let contract_table = if list_metadata.iter().all(|md| md.contracted_functions.is_empty()) {
            None
        } else {
            let (header, rows) = construct_contracts_table(&list_metadata);
            let t = table_constructor(header, rows)?;
            Some(t)
        };
        format_results(contract_table, CONTRACTS_SECTION, NO_CONTRACTS_MSG)
    };
    let standard_output = {
        const HARNESSES_SECTION: &str = "Standard Harnesses (#[kani::proof]):";
        const NO_HARNESSES_MSG: &str = "No standard harnesses found.";
        let standard_table = {
            let (header, rows) = construct_standard_table(&list_metadata);
            let t = table_constructor(header, rows)?;
            Some(t)
        };
        format_results(standard_table, HARNESSES_SECTION, NO_HARNESSES_MSG)
    };
    Ok((contract_output, standard_output))
}

/// Print results to the terminal.
fn pretty(list_metadata: BTreeSet<ListMetadata>) -> Result<()> {
    let (contract_output, standard_output) = construct_output(list_metadata, pretty_constructor)?;
    println!("{contract_output}");
    println!("{standard_output}");

    Ok(())
}

/// Output results to a Markdown file.
fn markdown(
    list_metadata: BTreeSet<ListMetadata>,
    quiet: bool,
    identity: CliIdentity,
) -> Result<()> {
    let (contract_output, standard_output) = construct_output(list_metadata, markdown_constructor)?;

    let out_path = Path::new(identity.list_artifact_stem()).with_extension("md");
    let mut out_file = File::create(&out_path)?;
    out_file.write_all(contract_output.as_bytes())?;
    out_file.write_all(standard_output.as_bytes())?;
    if !quiet {
        println!("Wrote list results to {}", std::fs::canonicalize(&out_path)?.display());
    }
    Ok(())
}

/// Output results as a JSON file.
fn json(list_metadata: BTreeSet<ListMetadata>, quiet: bool, identity: CliIdentity) -> Result<()> {
    let out_path = Path::new(identity.list_artifact_stem()).with_extension("json");
    let out_file = File::create(&out_path)?;
    let writer = BufWriter::new(out_file);

    let combined_md = merge_list_metadata(list_metadata)?;
    let json_obj = json_artifact(combined_md);

    serde_json::to_writer_pretty(writer, &json_obj)?;

    if !quiet {
        writeln!(
            std::io::stdout(),
            "Wrote list results to {}",
            std::fs::canonicalize(out_path)?.display()
        )?;
    }

    Ok(())
}

fn json_artifact(combined_md: ListMetadata) -> Value {
    let json_obj = json!({
        "kani-version": KANI_VERSION,
        "trust_mc-version": KANI_VERSION,
        "file-version": FILE_VERSION,
        "standard-harnesses": combined_md.standard_harnesses,
        "contract-harnesses": combined_md.contract_harnesses,
        "proof-obligations": combined_md.proof_obligations,
        "contracts": combined_md.contracted_functions,
        "totals": {
            "standard-harnesses": combined_md.standard_harnesses_count,
            "contract-harnesses": combined_md.contract_harnesses_count,
            "proof-obligations": combined_md.proof_obligations.len(),
            "functions-under-contract": combined_md.contracted_functions.len(),
        }
    });

    json_obj
}

/// Construct the rows for the table of contracts information.
/// Returns a tuple of the table header and the rows.
fn construct_contracts_table(
    list_metadata: &BTreeSet<ListMetadata>,
) -> (Vec<String>, Vec<Vec<String>>) {
    const NO_HARNESSES_MSG: &str = "NONE";
    const CRATE_NAME: &str = "Crate";
    const FUNCTION_HEADER: &str = "Function";
    const CONTRACT_HARNESSES_HEADER: &str = "Contract Harnesses (#[kani::proof_for_contract])";
    const TOTALS_HEADER: &str = "Total";

    let header = vec![
        String::new(),
        CRATE_NAME.to_string(),
        FUNCTION_HEADER.to_string(),
        CONTRACT_HARNESSES_HEADER.to_string(),
    ];

    let mut rows: Vec<Vec<String>> = vec![];
    let mut functions_under_contract_total = 0;
    let mut contract_harnesses_total = 0;

    for crate_md in list_metadata {
        for cf in &crate_md.contracted_functions {
            let mut row = vec![String::new(), crate_md.crate_name.clone(), cf.function.clone()];
            if cf.harnesses.is_empty() {
                row.push(NO_HARNESSES_MSG.to_string());
            } else {
                row.push(cf.harnesses.join(", "));
            }
            rows.push(row);
        }
        functions_under_contract_total += crate_md.contracted_functions.len();
        contract_harnesses_total += crate_md.contract_harnesses_count;
    }

    let totals_row = vec![
        TOTALS_HEADER.to_string(),
        String::new(),
        functions_under_contract_total.to_string(),
        contract_harnesses_total.to_string(),
    ];
    rows.push(totals_row);

    (header, rows)
}

fn construct_standard_table(
    list_metadata: &BTreeSet<ListMetadata>,
) -> (Vec<String>, Vec<Vec<String>>) {
    const CRATE_NAME: &str = "Crate";
    const HARNESS_HEADER: &str = "Harness";
    const TOTALS_HEADER: &str = "Total";

    let header = vec![String::new(), CRATE_NAME.to_string(), HARNESS_HEADER.to_string()];

    let mut rows: Vec<Vec<String>> = vec![];

    let mut total = 0;

    for crate_md in list_metadata {
        for harnesses in crate_md.standard_harnesses.values() {
            for harness in harnesses {
                rows.push(vec![String::new(), crate_md.crate_name.clone(), harness.clone()]);
            }
            total += harnesses.len();
        }
    }

    let totals_row = vec![TOTALS_HEADER.to_string(), String::new(), total.to_string()];
    rows.push(totals_row);

    (header, rows)
}

fn format_results<T: Display>(table: Option<T>, section_name: &str, absent_name: &str) -> String {
    use std::fmt::Write;
    let mut output = String::new();
    write!(output, "\n{section_name}\n").expect("write to String is infallible");
    if let Some(table) = table {
        write!(output, "{table}").expect("write to String is infallible");
    } else {
        output.push_str(absent_name);
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::list::{ProofObligation, ProofObligationRole, ProofObligationSource};
    use std::collections::BTreeMap;
    use trust_mc_metadata::ContractedFunction;

    #[test]
    fn json_artifact_keeps_trust_mc_identity_and_kani_compatibility_keys() {
        let artifact = json_artifact(sample_list_metadata());

        assert_eq!(artifact["kani-version"], KANI_VERSION);
        assert_eq!(artifact["trust_mc-version"], KANI_VERSION);
        assert_eq!(artifact["file-version"], FILE_VERSION);
        assert_eq!(artifact["totals"]["standard-harnesses"], 1);
        assert_eq!(artifact["totals"]["contract-harnesses"], 1);
        assert_eq!(artifact["totals"]["proof-obligations"], 1);
        assert_eq!(artifact["totals"]["functions-under-contract"], 1);
        assert_eq!(artifact["standard-harnesses"]["src/lib.rs"][0], "crate::standard");
        assert_eq!(artifact["contract-harnesses"]["src/lib.rs"][0], "crate::contract_harness");
        assert_eq!(artifact["contracts"][0]["function"], "crate::contracted");
        assert_eq!(
            artifact["proof-obligations"][0]["proof-item-id"],
            "trust_mc:kani-proof:crate:standard"
        );
    }

    #[test]
    fn output_filenames_match_cli_identity() {
        assert_eq!(
            Path::new(CliIdentity::trust_mc.list_artifact_stem()).with_extension("json"),
            Path::new("trust_mc-list.json")
        );
        assert_eq!(
            Path::new(CliIdentity::trust_mc.list_artifact_stem()).with_extension("md"),
            Path::new("trust_mc-list.md")
        );
        assert_eq!(
            Path::new(CliIdentity::Kani.list_artifact_stem()).with_extension("json"),
            Path::new("kani-list.json")
        );
        assert_eq!(
            Path::new(CliIdentity::Kani.list_artifact_stem()).with_extension("md"),
            Path::new("kani-list.md")
        );
    }

    fn sample_list_metadata() -> ListMetadata {
        let mut standard_harnesses = BTreeMap::new();
        standard_harnesses
            .insert("src/lib.rs".to_string(), BTreeSet::from(["crate::standard".to_string()]));

        let mut contract_harnesses = BTreeMap::new();
        contract_harnesses.insert(
            "src/lib.rs".to_string(),
            BTreeSet::from(["crate::contract_harness".to_string()]),
        );

        ListMetadata {
            crate_name: "crate".to_string(),
            standard_harnesses,
            standard_harnesses_count: 1,
            contract_harnesses,
            contract_harnesses_count: 1,
            contracted_functions: BTreeSet::from([ContractedFunction {
                function: "crate::contracted".to_string(),
                file: "src/lib.rs".to_string(),
                harnesses: vec!["crate::contract_harness".to_string()],
            }]),
            proof_obligations: BTreeSet::from([ProofObligation {
                proof_item_id: "trust_mc:kani-proof:crate:standard".to_string(),
                crate_name: "crate".to_string(),
                harness: "crate::standard".to_string(),
                role: ProofObligationRole::Harness,
                source_form: ProofObligationSource::KaniProofAttribute,
                target: None,
                file: "src/lib.rs".to_string(),
                start_line: 10,
                end_line: 12,
                engine: "ay-chc",
                required_by_full_verify: true,
            }]),
        }
    }
}
