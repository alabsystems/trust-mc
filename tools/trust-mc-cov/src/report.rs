// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module includes the implementation of the `report` subcommand.

use std::io::{BufRead, IsTerminal};
use std::{fs::File, io::BufReader, path::PathBuf};

use anyhow::{Context, Result};

use crate::args::ReportFormat;
use crate::coverage::{
    ColumnNumber, CovResult, LineNumber, LineResults, MarkerInfo, function_coverage_results,
    function_info_from_file,
};
use crate::summary::line_coverage_results;
use crate::{args::ReportArgs, coverage::CombinedCoverageResults};

/// Executes the `report` subcommand.
///
/// First, it loads the coverage metadata and results from the files passed as
/// arguments. Then, for each file referenced in the metadata, it computes its
/// associated coverage information on a per-function basis, producing a
/// human-readable report for each one of the files.
pub(crate) fn report_main(args: &ReportArgs) -> Result<()> {
    let mapfile = File::open(&args.mapfile)?;
    let reader = BufReader::new(mapfile);

    let covfile = File::open(&args.profile)?;
    let covreader = BufReader::new(covfile);
    let results: CombinedCoverageResults =
        serde_json::from_reader(covreader).expect("could not load coverage results");

    let source_files: Vec<PathBuf> =
        serde_json::from_reader(reader).expect("could not parse coverage metadata");

    let checked_format = check_format(&args.format);

    for file in source_files {
        let fun_info = function_info_from_file(&file);
        let mut file_cov_info = Vec::new();
        for info in fun_info {
            let cov_results = function_coverage_results(&info, &file, &results);
            let line_coverage = line_coverage_results(&info, &cov_results);
            let line_coverage_matched: LineResults =
                (info.start.0..=info.end.0).zip(line_coverage.clone()).collect();
            file_cov_info.push(line_coverage_matched);
        }
        output_coverage_results(&checked_format, file, file_cov_info)?;
    }

    Ok(())
}

/// Validate arguments to the `report` subcommand in addition to clap's
/// validation.
pub(crate) fn validate_report_args(_args: &ReportArgs) -> Result<()> {
    // No validation is done at the moment
    Ok(())
}

/// Checks the `format` argument for the `report` subcommand and selects to
/// another format if the one we are checking is not possible for any reason.
///
/// For example, if the `Terminal` format is specified but we are not writing to
/// a terminal, it will auto-select the `Escapes` format to avoid character
/// issues.
fn check_format(format: &ReportFormat) -> ReportFormat {
    let is_terminal = std::io::stdout().is_terminal();
    match format {
        ReportFormat::Terminal => {
            if is_terminal {
                ReportFormat::Terminal
            } else {
                ReportFormat::Escapes
            }
        }
        ReportFormat::Escapes => ReportFormat::Escapes,
    }
}

/// Output coverage results, and highlight regions or lines which are not
/// covered.
///
/// When highlighting the terminal, highlighted areas must be closed on the each
/// line to avoid highlighting beyond the source code area. Therefore, this
/// highlighting algorithm emits codes for both opening and closing the
/// highlighted area if any highlighting must be done for a line.
///
/// Therefore, a coverage region spanning multiple lines will be represented
/// with multiple highlighted lines. For example, let's take this uncovered
/// function:
///
/// fn _other_function() {
///     println!("Hello, world!");
/// }
///
/// It will be highlighted as follows:
///
/// ```fn _other_function() {'''
/// ```    println!("Hello, world!");'''
/// ```}'''
///
/// Note how there is always a corresponding escape for each line.
/// This is more sophisticated than the naive solution, which would simply emit two escapes
/// per region (one opening, one closing) as follows:
///
/// ```fn _other_function() {
///     println!("Hello, world!");
/// }'''
///
pub(crate) fn output_coverage_results(
    format: &ReportFormat,
    filepath: PathBuf,
    results: Vec<LineResults>,
) -> Result<()> {
    let flattened_results: LineResults = results.into_iter().flatten().collect();
    println!("{}", filepath.to_string_lossy());

    let file = File::open(filepath)?;
    let reader = BufReader::new(file);

    let mut must_highlight = false;

    for (i, line) in reader.lines().enumerate() {
        let idx: LineNumber = i.checked_add(1).context("line number does not fit in usize")?;
        let line = line?;

        let cur_line_result = flattened_results.iter().find(|(num, _)| *num == idx);

        let (max_times, line_fmt) = if let Some((_, Some((max, marker_info)))) = cur_line_result {
            match marker_info {
                MarkerInfo::FullLine => {
                    (Some(max), insert_escapes(&line, vec![(0, true), (line.len(), false)], format))
                }
                MarkerInfo::Markers(results) => {
                    // Escapes for the regions which start and finish in this line
                    let complete_escapes: Vec<(ColumnNumber, bool)> = results
                        .iter()
                        .filter(|m| {
                            m.times_covered == 0 && m.region.start.0 == idx && m.region.end.0 == idx
                        })
                        .flat_map(|m| {
                            vec![
                                (column_offset(m.region.start.1), true),
                                (column_offset(m.region.end.1), false),
                            ]
                        })
                        .collect();
                    // Escapes for the regions which only start in this line
                    let mut opening_escapes: Vec<(ColumnNumber, bool)> = results
                        .iter()
                        .filter(|m| {
                            m.times_covered == 0 && m.region.start.0 == idx && m.region.end.0 != idx
                        })
                        .flat_map(|m| vec![(column_offset(m.region.start.1), true)])
                        .collect();
                    // Escapes for the regions which only finish in this line
                    let mut closing_escapes: Vec<(ColumnNumber, bool)> = results
                        .iter()
                        .filter(|m| {
                            m.times_covered == 0 && m.region.start.0 != idx && m.region.end.0 == idx
                        })
                        .flat_map(|m| vec![(column_offset(m.region.end.1), false)])
                        .collect();

                    // Emit an opening escape if there was a closing one and we
                    // had to continue the highlight
                    if must_highlight && !closing_escapes.is_empty() {
                        closing_escapes.push((0, true));
                        must_highlight = false;
                    }
                    // Continue the highlight in the next lines if we had an
                    // opening escape
                    if !opening_escapes.is_empty() {
                        opening_escapes.push((line.len(), false));
                        must_highlight = true;
                    }

                    // Join all the escapes, then insert them
                    closing_escapes.extend(complete_escapes);
                    closing_escapes.extend(opening_escapes);

                    if must_highlight && closing_escapes.is_empty() {
                        closing_escapes.push((0, true));
                        closing_escapes.push((line.len(), false));
                    }

                    // If any result points to an out-of-bounds region after the
                    // end of the line (due to a known issue), we extend the
                    // line with a space to avoid crashing when drawing it.
                    let line = if results_with_nonexisting_regions_in_line(results, &line, idx) {
                        format!("{line} ")
                    } else {
                        line
                    };

                    (Some(max), insert_escapes(&line, closing_escapes, format))
                }
            }
        } else {
            (
                None,
                if !must_highlight {
                    line
                } else {
                    insert_escapes(&line, vec![(0, true), (line.len(), false)], format)
                },
            )
        };

        let max_fmt =
            if let Some(num) = max_times { format!("{num:4}") } else { format!("{:4}", " ") };

        println!("{idx:4}| {max_fmt}| {line_fmt}");
    }

    Ok(())
}

/// Returns whether any of the coverage results for a line point to out-of-bound
/// regions.
///
/// This is helpful to detect cases in which, for an unknown reason, the Rust
/// coverage instrumentation inserts a single-column code span after the end of
/// a line. More details in <https://github.com/model-checking/kani/issues/3543>
fn results_with_nonexisting_regions_in_line(
    results: &[CovResult],
    line: &str,
    idx: LineNumber,
) -> bool {
    let results_with_oob_regions = results.iter().filter(|m| {
        m.region.start.0 == idx
            && m.region.end.0 == idx
            && m.region.end.1.checked_sub(m.region.start.1) == Some(1)
            && (m.region.end.1) > line.len()
    });
    results_with_oob_regions.count() > 0
}

/// The 0-based byte offset of a 1-based coverage column.
///
/// Coverage columns start at 1. A column of 0 (malformed coverage data) is
/// clamped to the start of the line instead of underflowing: that was an
/// overflow panic, or without overflow checks an offset of `usize::MAX` that
/// `insert_escapes` then rejected with a panic.
fn column_offset(column: ColumnNumber) -> ColumnNumber {
    column.saturating_sub(1)
}

/// Inserts opening/closing escape strings into `str` given a set of `markers`.
/// Each marker is a tuple `(offset, type)` where:
///  * `offset` represents the offset in which the marker must be inserted, and
///  * `type` represents whether it is an opening (`true`) or closing (`false`)
///    escape.
///
/// The specific escape to be used are determined by the report format.
///
/// Markers are placed in offset order (at one offset, in the sort order of
/// their escape strings, as before). A marker past the end of `str` is placed at its end, and one that
/// is not on a UTF-8 character boundary is placed right after the text emitted
/// so far; both used to panic in `String::insert_str`.
fn insert_escapes(str: &str, markers: Vec<(ColumnNumber, bool)>, format: &ReportFormat) -> String {
    // Determine the escape strings based on the format
    let (open_escape, close_escape) = match format {
        ReportFormat::Terminal => ("\x1b[41m", "\x1b[0m"),
        ReportFormat::Escapes => ("```", "'''"),
    };

    let mut escape_markers: Vec<(&ColumnNumber, &str)> =
        markers.iter().map(|(i, b)| (i, if *b { open_escape } else { close_escape })).collect();
    escape_markers.sort();

    // Copy `str` segment by segment, emitting each escape at its offset. The
    // markers are sorted, so each segment starts where the previous one ended.
    let mut escaped_str = String::new();
    let mut copied = 0;
    for (i, escape) in escape_markers {
        let at = (*i).min(str.len());
        if let Some(segment) = str.get(copied..at) {
            escaped_str.push_str(segment);
            copied = at;
        }
        escaped_str.push_str(escape);
    }
    escaped_str.push_str(str.get(copied..).unwrap_or_default());
    escaped_str
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coverage::CoverageRegion;

    fn region(start: (LineNumber, ColumnNumber), end: (LineNumber, ColumnNumber)) -> CovResult {
        CovResult {
            function: "f".to_string(),
            region: CoverageRegion { file: "f.rs".to_string(), start, end },
            times_covered: 0,
            total_times: 1,
        }
    }

    #[test]
    fn insert_escapes_places_markers_at_their_offsets() {
        let escaped = insert_escapes(
            "let x = 1;",
            vec![(8, true), (9, false), (0, true), (3, false)],
            &ReportFormat::Escapes,
        );
        assert_eq!(escaped, "```let''' x = ```1''';");
    }

    #[test]
    fn insert_escapes_keeps_the_sorted_order_of_escapes_at_one_offset() {
        // Ties sort by escape string, as before: "'''" < "```".
        let escaped = insert_escapes("ab", vec![(1, true), (1, false)], &ReportFormat::Escapes);
        assert_eq!(escaped, "a'''```b");
    }

    #[test]
    fn insert_escapes_covers_the_whole_line() {
        let line = "fn f() {}";
        let escaped =
            insert_escapes(line, vec![(0, true), (line.len(), false)], &ReportFormat::Terminal);
        assert_eq!(escaped, "\x1b[41mfn f() {}\x1b[0m");
    }

    #[test]
    fn insert_escapes_places_a_marker_past_the_end_at_the_end() {
        let escaped = insert_escapes("ab", vec![(0, true), (7, false)], &ReportFormat::Escapes);
        assert_eq!(escaped, "```ab'''");
    }

    #[test]
    fn insert_escapes_places_a_marker_inside_a_character_after_the_emitted_text() {
        // 'é' is two bytes; offset 2 is inside it, and nothing was emitted yet.
        let escaped = insert_escapes("aé", vec![(2, true), (3, false)], &ReportFormat::Escapes);
        assert_eq!(escaped, "```aé'''");
    }

    #[test]
    fn column_offset_is_zero_based_and_clamps_column_zero() {
        assert_eq!(column_offset(1), 0);
        assert_eq!(column_offset(12), 11);
        assert_eq!(column_offset(0), 0);
    }

    #[test]
    fn nonexisting_region_detection_needs_one_column_past_the_line() {
        let line = "abc";
        assert!(results_with_nonexisting_regions_in_line(&[region((2, 4), (2, 5))], line, 2));
        assert!(!results_with_nonexisting_regions_in_line(&[region((2, 1), (2, 2))], line, 2));
        assert!(!results_with_nonexisting_regions_in_line(&[region((2, 4), (2, 5))], line, 3));
    }

    #[test]
    fn nonexisting_region_detection_rejects_a_region_ending_before_it_starts() {
        // end column < start column used to underflow `end - start`.
        assert!(!results_with_nonexisting_regions_in_line(&[region((2, 9), (2, 4))], "abc", 2));
    }
}
