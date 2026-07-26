// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Fail-closed unsoundness count extraction (Part of #3447).
//!
//! Extracts FAIL_CLOSED category counters (`assert_untranslatable`,
//! `heap_check_untranslatable`, `heap_check_unknown_layout`,
//! `iterator_unsoundness`, `bigint_unsoundness`) from project metadata.
//! These counters indicate the system deliberately forced failure via
//! injected `false` constraints or error rules.
//!
//! Split from `unsoundness_extract.rs` for 500-line file size compliance.

use std::collections::BTreeMap;

use crate::project::Project;

/// Extract assert_untranslatable counts by crate.
/// Fail-closed: injected error rules force CTREX on untranslatable assertions.
pub(crate) fn assert_untranslatable_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.assert_untranslatable.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

/// Extract heap_check_untranslatable counts by crate.
/// Fail-closed: conservative error rules for untranslatable heap safety checks.
pub(crate) fn heap_check_untranslatable_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.heap_check_untranslatable.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

/// Extract heap_check_unknown_layout counts by crate (#2501).
/// Fail-closed: injected failure for types without known layout.
pub(crate) fn heap_check_unknown_layout_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.heap_check_unknown_layout.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

/// Extract iterator fail-closed counts by crate.
/// Uses the combined CHC+BMC skip total because both indicate conservative,
/// forced-failure iterator handling.
pub(crate) fn iterator_unsoundness_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count =
                metadata.iterator_unsoundness.as_ref().map_or(0, |info| info.total_skip_count());
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

/// Extract iterator fail-closed per-harness maps by crate.
pub(crate) fn iterator_unsoundness_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.iterator_unsoundness.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

/// Extract BigInt fail-closed counts by crate.
pub(crate) fn bigint_unsoundness_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.bigint_unsoundness.as_ref().map_or(0, |info| info.chc_skip_count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

/// Extract BigInt fail-closed per-harness maps by crate.
pub(crate) fn bigint_unsoundness_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.bigint_unsoundness.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}
