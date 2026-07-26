// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Per-crate unsoundness count extraction from project metadata (#3458).
//!
//! These functions extract unsoundness counters from [`trust-mc_metadata::KaniMetadata`]
//! into per-crate maps consumed by [`crate::unsoundness_counts::UnsoundnessCounts::from_project`].

use std::collections::BTreeMap;

use crate::project::Project;
use crate::unsoundness_counts::SoundApproxPerHarnessMap;

// ─── Crate-level extraction functions ───

pub(crate) fn constant_zero_fallback_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.constant_zero_fallbacks.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn internal_workaround_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.internal_workarounds.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn chc_fallback_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.chc_fallbacks.as_ref().map_or(0, |info| info.total_count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn type_sort_fallback_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.type_sort_fallbacks.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn signedness_fallback_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.signedness_fallbacks.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn unsupported_construct_fallback_count_by_crate(
    project: &Project,
) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count =
                metadata.unsupported_construct_fallbacks.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

pub(crate) fn unconstrained_assignment_count_by_crate(project: &Project) -> BTreeMap<&str, usize> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            let count = metadata.unconstrained_assignments.as_ref().map_or(0, |info| info.count);
            (count > 0).then_some((metadata.crate_name.as_str(), count))
        })
        .collect()
}

// ─── Per-harness extraction functions ───

/// Extract per-harness CHC fallback maps by crate (#2959).
///
/// Returns a map of crate name -> per-harness fallback map. When the per-harness
/// map is non-empty, individual harness counts can be used instead of the crate total.
pub(crate) fn chc_fallback_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.chc_fallbacks.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

/// Extract per-harness signedness fallback maps by crate (#2959 Phase 2).
pub(crate) fn signedness_fallback_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.signedness_fallbacks.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

/// Extract per-harness type-sort fallback maps by crate (#2959 Phase 2).
pub(crate) fn type_sort_fallback_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.type_sort_fallbacks.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

pub(crate) fn constant_zero_fallback_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.constant_zero_fallbacks.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

pub(crate) fn internal_workaround_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.internal_workarounds.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

pub(crate) fn unsupported_construct_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.unsupported_construct_fallbacks.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

pub(crate) fn unconstrained_assignment_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.unconstrained_assignments.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

/// Per-harness kani::mem over-approximation counts by crate (Part of #3165).
pub(crate) fn kani_mem_overapprox_per_harness_by_crate(
    project: &Project,
) -> BTreeMap<&str, &BTreeMap<String, usize>> {
    project
        .metadata
        .iter()
        .filter_map(|metadata| {
            metadata.kani_mem_overapprox.as_ref().and_then(|info| {
                (!info.per_harness.is_empty())
                    .then_some((metadata.crate_name.as_str(), &info.per_harness))
            })
        })
        .collect()
}

/// Aggregate per-harness sound-approximation counts across all SOUND_APPROXIMATION
/// categories (#3303, #3715). Returns crate_name -> (harness_name -> [(category, count)]).
///
/// Built from the `UnsoundnessCategory` registry — a new sound-approximation category
/// added to `trust-mc_metadata` is automatically included here if it has `per_harness` data.
///
/// CTREX results from harnesses with nonzero sound-approximation counts are unreliable:
/// the over-approximation (unconstrained symbolic variables) allows the solver to find
/// counterexamples using values the real program can never produce.
pub(crate) fn sound_approximation_per_harness_by_crate(
    project: &Project,
) -> SoundApproxPerHarnessMap<'_> {
    use trust_mc_metadata::UnsoundnessClass;

    let mut result: SoundApproxPerHarnessMap<'_> = BTreeMap::new();

    for metadata in &project.metadata {
        let mut harness_cats: BTreeMap<String, Vec<(String, usize)>> = BTreeMap::new();

        for record in metadata.unsoundness_diagnostics() {
            if record.class != UnsoundnessClass::SoundApproximation {
                continue;
            }
            if let Some(ph_map) = record.per_harness {
                for (harness, count) in ph_map {
                    if *count > 0 {
                        harness_cats
                            .entry(harness.clone())
                            .or_default()
                            .push((record.json_key.to_string(), *count));
                    }
                }
            }
        }

        if !harness_cats.is_empty() {
            result.insert(metadata.crate_name.as_str(), harness_cats);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{test_metadata, test_metadata_full};
    use trust_mc_metadata::{ChcCoerceEqDropInfo, ChcTranslationDropInfo};

    #[test]
    fn test_constant_zero_fallback_count_by_crate_extracts_nonzero_only() {
        let mut project = Project::default();
        project.metadata = vec![
            test_metadata("crate_a", Some(2), None),
            test_metadata("crate_b", Some(0), None),
            test_metadata("crate_c", None, None),
        ];

        let counts = constant_zero_fallback_count_by_crate(&project);

        assert_eq!(counts.len(), 1);
        assert_eq!(counts.get("crate_a"), Some(&2));
        assert_eq!(counts.get("crate_b"), None);
        assert_eq!(counts.get("crate_c"), None);
    }

    #[test]
    fn test_chc_fallback_count_by_crate() {
        let mut project = Project::default();
        project.metadata = vec![
            test_metadata_full("crate_a", None, None, None, None, Some(7), None),
            test_metadata_full("crate_b", None, None, None, None, Some(0), None),
        ];

        let counts = chc_fallback_count_by_crate(&project);

        assert_eq!(counts.len(), 1);
        assert_eq!(counts.get("crate_a"), Some(&7));
    }

    #[test]
    fn test_chc_translation_drop_count_by_crate() {
        use crate::test_support::chc_translation_drop_count_by_crate;

        let mut project = Project::default();
        let mut md_a = test_metadata("crate_a", None, None);
        md_a.chc_translation_drops = Some(ChcTranslationDropInfo {
            place_count: 2,
            constant_count: 1,
            field_projection_count: 3,
            ..Default::default()
        });
        let mut md_b = test_metadata("crate_b", None, None);
        md_b.chc_translation_drops = Some(ChcTranslationDropInfo {
            place_count: 0,
            constant_count: 0,
            field_projection_count: 0,
            ..Default::default()
        });
        project.metadata = vec![md_a, md_b, test_metadata("crate_c", None, None)];

        let counts = chc_translation_drop_count_by_crate(&project);
        assert_eq!(counts.len(), 1);
        assert_eq!(counts.get("crate_a"), Some(&6));
        assert_eq!(counts.get("crate_b"), None);
    }

    #[test]
    fn test_chc_translation_drop_count_by_crate_includes_each_subfield() {
        use crate::test_support::chc_translation_drop_count_by_crate;

        let cases = [
            (
                "place_count",
                ChcTranslationDropInfo {
                    place_count: 1,
                    constant_count: 0,
                    field_projection_count: 0,
                    ..Default::default()
                },
            ),
            (
                "constant_count",
                ChcTranslationDropInfo {
                    place_count: 0,
                    constant_count: 1,
                    field_projection_count: 0,
                    ..Default::default()
                },
            ),
            (
                "field_projection_count",
                ChcTranslationDropInfo {
                    place_count: 0,
                    constant_count: 0,
                    field_projection_count: 1,
                    ..Default::default()
                },
            ),
        ];

        for (field_name, drop_info) in cases {
            let mut project = Project::default();
            let mut md = test_metadata("crate_a", None, None);
            md.chc_translation_drops = Some(drop_info);
            project.metadata = vec![md];

            let counts = chc_translation_drop_count_by_crate(&project);
            assert_eq!(
                counts.get("crate_a"),
                Some(&1),
                "nonzero {field_name} must contribute to chc_translation_drop_count_by_crate"
            );
        }
    }

    #[test]
    fn test_unhandled_call_count_by_crate() {
        use crate::test_support::unhandled_call_count_by_crate;

        let mut project = Project::default();
        project.metadata = vec![
            test_metadata_full("crate_a", None, None, None, None, None, Some(5)),
            test_metadata_full("crate_b", None, None, None, None, None, Some(0)),
            test_metadata_full("crate_c", None, None, None, None, None, None),
        ];

        let counts = unhandled_call_count_by_crate(&project);

        assert_eq!(counts.len(), 1);
        assert_eq!(counts.get("crate_a"), Some(&5));
    }

    #[test]
    fn test_chc_coerce_eq_drop_count_by_crate() {
        use crate::test_support::chc_coerce_eq_drop_count_by_crate;

        let mut project = Project::default();
        let mut md_a = test_metadata("crate_a", None, None);
        md_a.chc_coerce_eq_drops =
            Some(ChcCoerceEqDropInfo { total_count: 4, per_harness: Default::default() });
        let mut md_b = test_metadata("crate_b", None, None);
        md_b.chc_coerce_eq_drops =
            Some(ChcCoerceEqDropInfo { total_count: 0, per_harness: Default::default() });
        let md_c = test_metadata("crate_c", None, None);
        project.metadata = vec![md_a, md_b, md_c];

        let counts = chc_coerce_eq_drop_count_by_crate(&project);

        assert_eq!(counts.len(), 1);
        assert_eq!(counts.get("crate_a"), Some(&4));
        assert_eq!(counts.get("crate_b"), None);
    }

    /// inferable_predicate now hard-gates replacement-quality PROOFs instead
    /// of flowing through sound-approximation extraction.
    #[test]
    fn test_sound_approx_per_harness_excludes_inferable_predicate() {
        use crate::test_support::md_with;
        use trust_mc_metadata::InferablePredicateInfo;

        let mut project = Project::default();
        let mut ph = BTreeMap::new();
        ph.insert("harness_a".to_string(), 3usize);
        let md = md_with(|m| {
            m.crate_name = "crate_x".to_string();
            m.inferable_predicates = Some(InferablePredicateInfo {
                count: 3,
                per_harness: ph.clone(),
                ..Default::default()
            });
        });
        project.metadata = vec![md];

        let result = sound_approximation_per_harness_by_crate(&project);
        assert!(
            result.get("crate_x").is_none(),
            "inferable_predicate must not be classified as sound approximation: {result:?}"
        );
    }
}
