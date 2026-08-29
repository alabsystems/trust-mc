// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! SARIF (Static Analysis Results Interchange Format) output support.
//!
//! Generates SARIF v2.1.0 output from verification results, providing
//! machine-readable output compatible with CI/code-scanning workflows.
//! Ported from upstream Kani's `sarif.rs` and adapted to trust_mc's
//! verification result model (AY backend, no CBMC ExitStatus).

use crate::demotion::is_effective_manual_success;
use crate::harness_runner::HarnessResult;
use crate::proof_summary::{HarnessVerdict, classify_harness_verdict};
use crate::property_model::{CheckStatus, Property, RawSourceLocation, TraceItem};
use crate::session::KaniSession;
use crate::verification_result::VerificationStatus;
use anyhow::{Context, Result};
use pathdiff::diff_paths;
use serde::Serialize;
use std::collections::BTreeMap;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};

const SARIF_VERSION: &str = "2.1.0";
const SARIF_SCHEMA: &str = "https://json.schemastore.org/sarif-2.1.0.json";
const TOOL_NAME: &str = "trust-mc";
const TOOL_INFO_URI: &str = "https://github.com/alabsystems/trust-mc";

impl KaniSession {
    pub(crate) fn write_sarif(&self, results: &[HarnessResult<'_>]) -> Result<()> {
        let Some(path) = &self.args.sarif else { return Ok(()) };
        let log = SarifLog::from_harness_results(results);
        write_sarif_file(path, &log)
    }
}

fn write_sarif_file(path: &Path, log: &SarifLog) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        std::fs::create_dir_all(parent).with_context(|| {
            format!("Failed to create SARIF output directory `{}`", parent.display())
        })?;
    }

    let file = File::create(path)
        .with_context(|| format!("Failed to create SARIF output file `{}`", path.display()))?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer_pretty(&mut writer, log)
        .with_context(|| format!("Failed to write SARIF output to `{}`", path.display()))?;
    writer.write_all(b"\n")?;
    Ok(())
}

#[derive(Serialize)]
struct SarifLog {
    version: &'static str,
    #[serde(rename = "$schema")]
    schema: &'static str,
    runs: Vec<Run>,
}

#[derive(Serialize)]
struct Run {
    tool: Tool,
    results: Vec<SarifResult>,
}

#[derive(Serialize)]
struct Tool {
    driver: Driver,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Driver {
    name: &'static str,
    version: &'static str,
    information_uri: &'static str,
    rules: Vec<ReportingDescriptor>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ReportingDescriptor {
    id: String,
    short_description: Message,
}

#[derive(Serialize)]
struct Message {
    text: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SarifResult {
    rule_id: String,
    level: &'static str,
    message: Message,
    locations: Vec<Location>,
    properties: ResultProperties,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ResultProperties {
    harness: String,
    property_name: Option<String>,
    /// The HARNESS-level verdict this finding belongs to.
    ///
    /// `level` is per-finding severity and says nothing about why the harness
    /// as a whole did not succeed: a check reported under a harness the solver
    /// never decided, and one under a harness whose assertion is genuinely
    /// refutable, both arrived as `"level": "error"`. Code scanning that reads
    /// only SARIF could not tell "raise the budget" from "your code is wrong".
    /// Carried in `properties` (SARIF's own extension point) so no consumer
    /// that ignores it can break, and named with the same tokens
    /// `--proof-summary-json` uses.
    verdict: &'static str,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Location {
    physical_location: PhysicalLocation,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct PhysicalLocation {
    artifact_location: ArtifactLocation,
    region: Region,
}

#[derive(Serialize)]
struct ArtifactLocation {
    uri: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Region {
    start_line: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    start_column: Option<u32>,
}

impl SarifLog {
    fn from_harness_results(results: &[HarnessResult<'_>]) -> Self {
        let mut rules = BTreeMap::<String, ReportingDescriptor>::new();
        let mut sarif_results = Vec::new();

        for harness_result in results {
            let harness = harness_result.harness;
            let result = &harness_result.result;

            if is_effective_manual_success(
                result.status,
                harness.attributes.should_panic,
                result.failed_properties,
            ) {
                continue;
            }

            let verdict = classify_harness_verdict(result, harness.attributes.should_panic);
            let results_before = sarif_results.len();

            for prop in &result.results {
                // Skip cover and code_coverage properties -- they are not verification findings.
                if prop.is_cover_property() || prop.property_class() == "code_coverage" {
                    continue;
                }

                let Some(level) = sarif_level(&prop.status) else { continue };
                let rule_id = format!("trust_mc.ay.{}", prop.property_id.class);

                rules.entry(rule_id.clone()).or_insert_with(|| ReportingDescriptor {
                    id: rule_id.clone(),
                    short_description: Message {
                        text: format!("AY property `{}`", prop.property_id.class),
                    },
                });

                let (file, line, column) = best_location(prop).unwrap_or_else(|| {
                    (
                        relativize_path(&harness.original_file),
                        harness.original_start_line as u32,
                        None,
                    )
                });

                sarif_results.push(SarifResult {
                    rule_id,
                    level,
                    message: Message {
                        text: format!("[{}] {}", harness.pretty_name, prop.description),
                    },
                    locations: vec![Location {
                        physical_location: PhysicalLocation {
                            artifact_location: ArtifactLocation { uri: file },
                            region: Region { start_line: line, start_column: column },
                        },
                    }],
                    properties: ResultProperties {
                        harness: harness.pretty_name.clone(),
                        property_name: Some(prop.property_name()),
                        verdict: verdict.label(),
                    },
                });
            }

            // A harness can fail as a WHOLE while no single property failed, and
            // the loop above -- which only ever reports properties -- then emits
            // nothing at all for it. Both vacuity gates in `harness_runner` land
            // here: `[AY:VACUOUS:unsat-assumption]` and its dead-check sibling
            // `[AY:VACUOUS:dead-checks]` leave every check
            // UNREACHABLE (never `Failure`), and `[AY:VACUOUS:no-checks]` leaves
            // `results` empty outright. The run printed a red verdict and exited
            // 1, but the machine-readable channel that CI actually gates on said
            // zero findings:
            //
            //     $ trust-mc --sarif out.sarif vacuous.rs   # exit 1
            //     $ jq '.runs[0].results | length' out.sarif
            //     0
            //
            // For code scanning that reads as a clean file. A failing harness has
            // to leave a finding behind, so synthesize one against the harness
            // itself when its properties produced none.
            if sarif_results.len() == results_before
                && result.status == VerificationStatus::Failure
            {
                let (rule_id, text) = harness_level_finding(verdict);
                rules.entry(rule_id.to_string()).or_insert_with(|| ReportingDescriptor {
                    id: rule_id.to_string(),
                    short_description: Message { text: harness_rule_description(rule_id) },
                });
                sarif_results.push(SarifResult {
                    rule_id: rule_id.to_string(),
                    level: "error",
                    message: Message { text: format!("[{}] {text}", harness.pretty_name) },
                    locations: vec![Location {
                        physical_location: PhysicalLocation {
                            artifact_location: ArtifactLocation {
                                uri: relativize_path(&harness.original_file),
                            },
                            region: Region {
                                start_line: harness.original_start_line as u32,
                                start_column: None,
                            },
                        },
                    }],
                    properties: ResultProperties {
                        harness: harness.pretty_name.clone(),
                        property_name: None,
                        verdict: verdict.label(),
                    },
                });
            }
        }

        SarifLog {
            version: SARIF_VERSION,
            schema: SARIF_SCHEMA,
            runs: vec![Run {
                tool: Tool {
                    driver: Driver {
                        name: TOOL_NAME,
                        version: env!("CARGO_PKG_VERSION"),
                        information_uri: TOOL_INFO_URI,
                        rules: rules.into_values().collect(),
                    },
                },
                results: sarif_results,
            }],
        }
    }
}

/// Rule id and message for a harness that failed without any failing property.
///
/// The distinction matters to whoever reads the report: "you assumed something
/// contradictory" and "you compiled to zero obligations" have different fixes,
/// and neither is the ordinary "this assertion can fail".
///
/// The split itself now comes from [`classify_harness_verdict`], which is the
/// console channel's own verdict chain — this used to be a second, hand-rolled
/// copy of it (`results.is_empty()` where the console counts NON-COVER checks,
/// and a vacuity test with no `should_panic` guard), and two copies of a rule
/// are two rules. The RULE IDS are deliberately unchanged: they are what CI
/// gates on, so the finer verdicts ride along in `properties.verdict` instead
/// of splitting an existing id into new ones.
fn harness_level_finding(verdict: HarnessVerdict) -> (&'static str, &'static str) {
    match verdict {
        HarnessVerdict::InconclusiveUndecided => {
            ("trust_mc.harness.undecided", verdict.description())
        }
        HarnessVerdict::InconclusiveNoChecks => {
            ("trust_mc.harness.no_checks", verdict.description())
        }
        // Both all-checks-unreachable shapes keep the ONE id they have always
        // had. The id is what CI gates on and the two are the same news to a
        // gate ("this harness established nothing"); which of them it was rides
        // along in `properties.verdict` and in the message, exactly as the
        // paragraph above says the finer verdicts should.
        HarnessVerdict::Vacuous | HarnessVerdict::InconclusiveDeadChecks => {
            ("trust_mc.harness.vacuous", verdict.description())
        }
        // Everything else keeps the one id that existed before, including the
        // uncertified-counterexample case: it is a failure with findings of its
        // own in the normal path, so it only reaches here in odd shapes.
        _ => ("trust_mc.harness.failed", "verification did not succeed for this harness"),
    }
}

fn harness_rule_description(rule_id: &str) -> String {
    match rule_id {
        "trust_mc.harness.no_checks" => "Harness produced no verification conditions",
        "trust_mc.harness.undecided" => "Harness could not be decided by the solver",
        "trust_mc.harness.vacuous" => "Harness proof is vacuous",
        _ => "Harness verification did not succeed",
    }
    .to_string()
}

fn sarif_level(status: &CheckStatus) -> Option<&'static str> {
    match status {
        CheckStatus::Failure => Some("error"),
        CheckStatus::Undetermined | CheckStatus::Unknown => Some("warning"),
        _ => None,
    }
}

fn best_location(prop: &Property) -> Option<(String, u32, Option<u32>)> {
    if let Some(loc) = location_from_raw_source_location(&prop.source_location) {
        return Some(loc);
    }

    prop.trace.as_ref().and_then(|trace| trace.iter().rev().find_map(trace_item_location))
}

fn trace_item_location(item: &TraceItem) -> Option<(String, u32, Option<u32>)> {
    let loc = item.source_location.as_ref()?;
    location_from_raw_source_location(loc)
}

fn location_from_raw_source_location(
    loc: &RawSourceLocation,
) -> Option<(String, u32, Option<u32>)> {
    let file = loc.file.as_deref()?;
    let line: u32 = loc.line.as_deref()?.parse().ok()?;
    let column = loc.column.as_deref().and_then(|c| c.parse().ok());
    Some((relativize_path(file), line, column))
}

fn relativize_path(file: &str) -> String {
    let file_path = PathBuf::from(file);
    let Ok(cur_dir) = env::current_dir() else { return file.to_string() };

    diff_paths(file_path, cur_dir)
        .unwrap_or_else(|| PathBuf::from(file))
        .to_string_lossy()
        .into_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::harness_runner::HarnessResult;
    use crate::property_model::{CheckStatus, Property, PropertyId, RawSourceLocation};
    use crate::test_support::{test_harness, test_result};
    use crate::verification_result::{FailedProperties, VerificationStatus};
    use std::borrow::Cow;

    fn failure_property() -> Property {
        Property {
            description: Cow::Borrowed("assertion failed: x == 0"),
            property_id: PropertyId {
                fn_name: Some("harness".to_string()),
                class: Cow::Borrowed("assertion"),
                id: 1,
            },
            source_location: RawSourceLocation {
                file: Some("src/lib.rs".to_string()),
                line: Some("12".to_string()),
                column: Some("3".to_string()),
                function: Some("harness".to_string()),
            },
            status: CheckStatus::Failure,
            trace: None,
        }
    }

    fn success_property() -> Property {
        Property {
            description: Cow::Borrowed("assertion x > 0"),
            property_id: PropertyId {
                fn_name: Some("harness".to_string()),
                class: Cow::Borrowed("assertion"),
                id: 2,
            },
            source_location: RawSourceLocation {
                file: Some("src/lib.rs".to_string()),
                line: Some("15".to_string()),
                column: None,
                function: Some("harness".to_string()),
            },
            status: CheckStatus::Success,
            trace: None,
        }
    }

    #[test]
    fn test_sarif_includes_failed_properties() {
        let harness = test_harness("my_harness", "test_crate");
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        result.results = vec![failure_property()];
        let harness_result = HarnessResult { harness: &harness, result };

        let log = SarifLog::from_harness_results(&[harness_result]);
        let v = serde_json::to_value(&log).expect("SARIF serialization should succeed");

        assert_eq!(v["version"], SARIF_VERSION);
        assert_eq!(v["runs"][0]["tool"]["driver"]["name"], TOOL_NAME);
        assert_eq!(v["runs"][0]["results"].as_array().unwrap().len(), 1);

        let r = &v["runs"][0]["results"][0];
        assert_eq!(r["ruleId"], "trust_mc.ay.assertion");
        assert_eq!(r["level"], "error");
        assert_eq!(r["locations"][0]["physicalLocation"]["artifactLocation"]["uri"], "src/lib.rs");
        assert_eq!(r["locations"][0]["physicalLocation"]["region"]["startLine"], 12);
        assert_eq!(r["locations"][0]["physicalLocation"]["region"]["startColumn"], 3);
    }

    #[test]
    fn test_sarif_skips_success_properties() {
        let harness = test_harness("my_harness", "test_crate");
        let mut result = test_result(VerificationStatus::Success, FailedProperties::None);
        result.results = vec![success_property()];
        let harness_result = HarnessResult { harness: &harness, result };

        let log = SarifLog::from_harness_results(&[harness_result]);
        let v = serde_json::to_value(&log).expect("SARIF serialization should succeed");

        // Success properties should not appear in SARIF results
        assert_eq!(v["runs"][0]["results"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn test_sarif_skips_expected_should_panic_failures() {
        let mut harness = test_harness("my_harness", "test_crate");
        harness.attributes.should_panic = true;
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        result.results = vec![failure_property()];
        let harness_result = HarnessResult { harness: &harness, result };

        let log = SarifLog::from_harness_results(&[harness_result]);
        let v = serde_json::to_value(&log).expect("SARIF serialization should succeed");

        assert_eq!(v["runs"][0]["results"].as_array().unwrap().len(), 0);
        assert_eq!(v["runs"][0]["tool"]["driver"]["rules"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn test_sarif_level_mapping() {
        assert_eq!(sarif_level(&CheckStatus::Failure), Some("error"));
        assert_eq!(sarif_level(&CheckStatus::Undetermined), Some("warning"));
        assert_eq!(sarif_level(&CheckStatus::Unknown), Some("warning"));
        assert_eq!(sarif_level(&CheckStatus::Success), None);
        assert_eq!(sarif_level(&CheckStatus::Unreachable), None);
        assert_eq!(sarif_level(&CheckStatus::Satisfied), None);
    }

    #[test]
    fn test_sarif_falls_back_to_harness_location() {
        let mut harness = test_harness("my_harness", "test_crate");
        harness.original_file = "src/main.rs".to_string();
        harness.original_start_line = 42;

        // Property with no source location
        let prop = Property {
            description: Cow::Borrowed("assertion failed"),
            property_id: PropertyId { fn_name: None, class: Cow::Borrowed("assertion"), id: 1 },
            source_location: RawSourceLocation {
                file: None,
                line: None,
                column: None,
                function: None,
            },
            status: CheckStatus::Failure,
            trace: None,
        };

        let mut result = test_result(VerificationStatus::Failure, FailedProperties::Other);
        result.results = vec![prop];
        let harness_result = HarnessResult { harness: &harness, result };

        let log = SarifLog::from_harness_results(&[harness_result]);
        let v = serde_json::to_value(&log).expect("SARIF serialization should succeed");

        let r = &v["runs"][0]["results"][0];
        // Should fall back to harness original_start_line
        assert_eq!(r["locations"][0]["physicalLocation"]["region"]["startLine"], 42);
    }

    /// Every finding says which VERDICT its harness got.
    ///
    /// `level` is per-finding severity: a check under a harness the solver
    /// never decided and a check under a genuinely refuted one both came back
    /// `"error"`, so code scanning could not tell "raise the budget" from
    /// "your code is wrong".
    #[test]
    fn test_sarif_results_carry_the_harness_verdict() {
        let harness = test_harness("my_harness", "test_crate");
        let mut result = test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        result.results = vec![failure_property()];
        let log = SarifLog::from_harness_results(&[HarnessResult { harness: &harness, result }]);
        let v = serde_json::to_value(&log).unwrap();
        assert_eq!(v["runs"][0]["results"][0]["properties"]["verdict"], "failed");
        // ...and the fields that were already there are untouched.
        assert_eq!(v["runs"][0]["results"][0]["properties"]["harness"], "my_harness");
        assert_eq!(v["runs"][0]["results"][0]["level"], "error");

        // A harness the solver could not decide is a different verdict on the
        // synthesized harness-level finding.
        let mut undecided = test_result(VerificationStatus::Failure, FailedProperties::Other);
        undecided.solver_unknown_reason =
            Some(crate::verification_provenance::SolverUnknownReason::UndecidedModel);
        let log = SarifLog::from_harness_results(&[HarnessResult {
            harness: &harness,
            result: undecided,
        }]);
        let v = serde_json::to_value(&log).unwrap();
        assert_eq!(v["runs"][0]["results"][0]["ruleId"], "trust_mc.harness.undecided");
        assert_eq!(v["runs"][0]["results"][0]["properties"]["verdict"], "inconclusive_undecided");
    }

    /// The rule ids are what CI gates on: the finer verdicts ride in
    /// `properties`, and these four ids keep their exact meaning.
    #[test]
    fn test_sarif_harness_rule_ids_are_stable() {
        assert_eq!(harness_level_finding(HarnessVerdict::Vacuous).0, "trust_mc.harness.vacuous");
        assert_eq!(
            harness_level_finding(HarnessVerdict::InconclusiveNoChecks).0,
            "trust_mc.harness.no_checks"
        );
        assert_eq!(
            harness_level_finding(HarnessVerdict::InconclusiveUndecided).0,
            "trust_mc.harness.undecided"
        );
        assert_eq!(harness_level_finding(HarnessVerdict::Failed).0, "trust_mc.harness.failed");
        assert_eq!(
            harness_level_finding(HarnessVerdict::UncertifiedCounterexample).0,
            "trust_mc.harness.failed",
            "a NEW rule id would break every consumer that enumerates them"
        );
        for verdict in [
            HarnessVerdict::Vacuous,
            HarnessVerdict::InconclusiveNoChecks,
            HarnessVerdict::InconclusiveUndecided,
            HarnessVerdict::Failed,
        ] {
            let (id, _) = harness_level_finding(verdict);
            assert_ne!(
                harness_rule_description(id),
                String::new(),
                "every rule id needs a description"
            );
        }
    }
}
