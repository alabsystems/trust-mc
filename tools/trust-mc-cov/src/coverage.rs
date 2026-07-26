// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module defines coverage-oriented data structures shared among
//! subcommands and other utilities like the Rust tree-sitter.

use console::style;
use serde_derive::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::{collections::HashMap, fmt::Display};
use std::{fmt, fs};
use tree_sitter::{Node, Parser};

pub(crate) type Function = String;
pub(crate) type Filename = String;
pub(crate) type LineNumber = usize;
pub(crate) type ColumnNumber = usize;

pub(crate) type LineResults = Vec<(LineNumber, Option<(usize, MarkerInfo)>)>;

/// The possible outcomes for a Kani check.
///
/// Note: This data structure should not be duplicated in Kani -
/// <https://github.com/model-checking/kani/issues/3541>
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "UPPERCASE")]
pub(crate) enum CheckStatus {
    Failure,
    Covered,   // for `code_coverage` properties only
    Satisfied, // for `cover` properties only
    Success,
    Undetermined,
    Unreachable,
    Uncovered,     // for `code_coverage` properties only
    Unsatisfiable, // for `cover` properties only
}

/// Kani coverage check.
///
/// Note: This data structure should not be duplicated in Kani -
/// <https://github.com/model-checking/kani/issues/3541>
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CoverageCheck {
    pub function: Filename,
    term: CoverageTerm,
    pub region: CoverageRegion,
    pub status: CheckStatus,
}

// Note: This `impl` should not be duplicated in Kani -
// <https://github.com/model-checking/kani/issues/3541>
impl std::fmt::Display for CheckStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let check_str = match self {
            CheckStatus::Satisfied => style("SATISFIED").green(),
            CheckStatus::Success => style("SUCCESS").green(),
            CheckStatus::Covered => style("COVERED").green(),
            CheckStatus::Uncovered => style("UNCOVERED").red(),
            CheckStatus::Failure => style("FAILURE").red(),
            CheckStatus::Unreachable => style("UNREACHABLE").yellow(),
            CheckStatus::Undetermined => style("UNDETERMINED").yellow(),
            CheckStatus::Unsatisfiable => style("UNSATISFIABLE").yellow(),
        };
        write!(f, "{check_str}")
    }
}

/// Raw Kani coverage results.
///
/// Note: This data structure should not be duplicated in Kani -
/// <https://github.com/model-checking/kani/issues/3541>
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CoverageResults {
    pub data: HashMap<Function, Vec<CoverageCheck>>,
}

/// Aggregated coverage results.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CombinedCoverageResults {
    pub data: HashMap<Filename, Vec<(Function, Vec<CovResult>)>>,
}

/// The coverage result associated to a particular coverage region.
///
/// Basically, this aggregates the information of one or more `CoverageCheck`
/// for a particular region. Thus, `total_times` represents the total number of
/// such checks, while `times_covered` keeps track of how many of those checks
/// had the `COVERED` status.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CovResult {
    pub function: Filename,
    pub region: CoverageRegion,
    pub times_covered: usize,
    pub total_times: usize,
}

/// A coverage region.
/// `start` and `end` are tuples containing the line and column numbers.
///
/// Note: This data structure should not be duplicated in Kani -
/// <https://github.com/model-checking/kani/issues/3541>
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct CoverageRegion {
    pub file: Filename,
    pub start: (LineNumber, ColumnNumber),
    pub end: (LineNumber, ColumnNumber),
}

impl Display for CoverageRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}:{} - {}:{}", self.file, self.start.0, self.start.1, self.end.0, self.end.1)
    }
}

/// A coverage term.
///
/// Note: This data structure should not be duplicated in Kani -
/// <https://github.com/model-checking/kani/issues/3541>
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum CoverageTerm {
    Counter(u32),
    Expression(u32),
}

/// The coverage information to produce for a particular file.
pub(crate) struct FileCoverageInfo {
    pub filename: Filename,
    pub function: CoverageMetric,
    pub line: CoverageMetric,
    pub region: CoverageMetric,
}

/// A coverage metric.
pub(crate) struct CoverageMetric {
    pub covered: usize,
    pub total: usize,
}

impl CoverageMetric {
    pub(crate) fn new(covered: usize, total: usize) -> Self {
        CoverageMetric { covered, total }
    }
}

/// Function information obtained through a tree-sitter
#[derive(Debug)]
pub(crate) struct FunctionInfo {
    pub name: Function,
    pub start: (LineNumber, ColumnNumber),
    pub end: (LineNumber, ColumnNumber),
}

/// Extract function information from a file using a tree-sitter
pub(crate) fn function_info_from_file(filepath: &PathBuf) -> Vec<FunctionInfo> {
    let source_code = fs::read_to_string(filepath).expect("could not read source file");
    let mut parser = Parser::new();
    parser.set_language(&tree_sitter_rust::LANGUAGE.into()).expect("Error loading Rust grammar");

    let tree = parser.parse(&source_code, None).expect("Failed to parse file");

    let source_code_bytes = source_code.as_bytes();
    let mut function_info: Vec<FunctionInfo> = Vec::new();
    let mut cursor = tree.walk();

    for node in tree.root_node().children(&mut cursor) {
        if node.kind() == "function_item" {
            function_info.push(function_info_from_node(node, source_code_bytes));
        }
    }

    function_info
}

/// Helper function to extract function information using a tree-sitter
fn function_info_from_node(node: Node, source: &[u8]) -> FunctionInfo {
    let name = node
        .child_by_field_name("name")
        .and_then(|name| name.utf8_text(source).ok())
        .expect("couldn't get function name")
        .to_string();
    let start = (node.start_position().row + 1, node.start_position().column + 1);
    let end = (node.end_position().row + 1, node.end_position().column + 1);
    FunctionInfo { name, start, end }
}

/// Extract the coverage results associated to a function
pub(crate) fn function_coverage_results(
    info: &FunctionInfo,
    file: &Path,
    results: &CombinedCoverageResults,
) -> Option<(Function, Vec<CovResult>)> {
    // The filenames in "kaniraw" files are not absolute, so we need to match
    // them with the ones we have in the aggregated results (i.e., the filenames
    // in the "kanimap" files).
    let filename = file.to_str()?;
    let right_filename = results.data.keys().find(|p| filename.ends_with(*p))?;
    // TODO(#451): The filenames in kaniraw files should be absolute, just like in metadata.
    // Otherwise the key for `results` just fails... (blocked by upstream kani#3542)
    let file_results = results.data.get(right_filename)?;
    let function = &info.name;
    let fun_results = file_results.iter().find(|(f, _)| *f == *function);
    fun_results.cloned()
}

/// Marker information, mainly useful for highlighting coverage
#[derive(Debug, Clone)]
pub(crate) enum MarkerInfo {
    FullLine,
    Markers(Vec<CovResult>),
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn test_check_status_serde() {
        // Test that CheckStatus serializes/deserializes correctly
        let status = CheckStatus::Covered;
        let json = serde_json::to_string(&status).unwrap();
        assert_eq!(json, r#""COVERED""#);

        let deserialized: CheckStatus = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, status);
    }

    #[test]
    fn test_check_status_all_variants() {
        // Verify all CheckStatus variants exist and serialize
        let variants = vec![
            (CheckStatus::Failure, "FAILURE"),
            (CheckStatus::Covered, "COVERED"),
            (CheckStatus::Satisfied, "SATISFIED"),
            (CheckStatus::Success, "SUCCESS"),
            (CheckStatus::Undetermined, "UNDETERMINED"),
            (CheckStatus::Unreachable, "UNREACHABLE"),
            (CheckStatus::Uncovered, "UNCOVERED"),
            (CheckStatus::Unsatisfiable, "UNSATISFIABLE"),
        ];
        for (status, expected) in variants {
            let json = serde_json::to_string(&status).unwrap();
            assert!(json.contains(expected));
        }
    }

    #[test]
    fn test_coverage_region_display() {
        let region =
            CoverageRegion { file: "src/main.rs".to_string(), start: (10, 5), end: (15, 20) };
        let display = format!("{}", region);
        assert_eq!(display, "src/main.rs:10:5 - 15:20");
    }

    #[test]
    fn test_coverage_region_ordering() {
        // CoverageRegion derives Ord, so verify ordering works
        let region1 = CoverageRegion { file: "a.rs".to_string(), start: (1, 1), end: (10, 1) };
        let region2 = CoverageRegion { file: "b.rs".to_string(), start: (1, 1), end: (10, 1) };
        assert!(region1 < region2, "ordering should be by file first");
    }

    #[test]
    fn test_coverage_metric_new() {
        let metric = CoverageMetric::new(5, 10);
        assert_eq!(metric.covered, 5);
        assert_eq!(metric.total, 10);
    }

    #[test]
    fn test_coverage_metric_edge_cases() {
        // Zero coverage
        let zero = CoverageMetric::new(0, 10);
        assert_eq!(zero.covered, 0);

        // Full coverage
        let full = CoverageMetric::new(10, 10);
        assert_eq!(full.covered, full.total);

        // Empty (no code)
        let empty = CoverageMetric::new(0, 0);
        assert_eq!(empty.covered, 0);
        assert_eq!(empty.total, 0);
    }

    #[test]
    fn test_coverage_region_serde() {
        let region = CoverageRegion { file: "lib.rs".to_string(), start: (1, 1), end: (5, 10) };
        let json = serde_json::to_string(&region).unwrap();
        let deserialized: CoverageRegion = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, region);
    }

    #[test]
    fn test_cov_result_serde() {
        let result = CovResult {
            function: "test_fn".to_string(),
            region: CoverageRegion { file: "test.rs".to_string(), start: (1, 1), end: (10, 1) },
            times_covered: 3,
            total_times: 5,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("test_fn"));
        assert!(json.contains("times_covered"));
    }
}
