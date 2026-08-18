// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::BTreeSet;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

use anyhow::{Result, bail};
use serde::Deserialize;

use trust_mc_metadata::{HarnessAttributes, HarnessKind, HarnessMetadata, find_proof_harnesses};

use crate::session::KaniSession;
use crate::util::warning;

/// Deserialize a json file into a given structure
pub(crate) fn from_json<T: for<'a> Deserialize<'a>>(path: &Path) -> Result<T> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let obj = serde_json::from_reader(reader)?;
    Ok(obj)
}

impl KaniSession {
    /// Determine which function to use as entry point, based on command-line arguments and kani-metadata.
    pub(crate) fn determine_targets<'a>(
        &self,
        compiler_filtered_harnesses: Vec<&'a HarnessMetadata>,
    ) -> Result<Vec<&'a HarnessMetadata>> {
        let harness_filters: BTreeSet<_> =
            self.args.harnesses.iter().map(std::string::String::as_str).collect();

        // For dev builds, re-filter the harnesses to double check filtering in the compiler
        // and ensure we're doing the minimal harness codegen possible. That filtering happens in
        // the `kani-compiler/src/kani_middle/codegen_units.rs` file's `determine_targets` function.
        if cfg!(debug_assertions) && !harness_filters.is_empty() {
            let filtered_harnesses: Vec<&HarnessMetadata> = find_proof_harnesses(
                &harness_filters,
                compiler_filtered_harnesses.clone(),
                self.args.exact,
            );
            assert_eq!(compiler_filtered_harnesses, filtered_harnesses);
        }

        // If any of the `--harness` filters failed to find a harness (and thus the # of harnesses is less than the # of filters), report that to the user.
        if self.args.exact && (compiler_filtered_harnesses.len() < self.args.harnesses.len()) {
            let harness_found_names: BTreeSet<&str> =
                compiler_filtered_harnesses.iter().map(|h| h.pretty_name.as_str()).collect();

            // Check which harnesses are missing from the difference of targets and all_harnesses
            let harnesses_missing: Vec<&str> =
                harness_filters.difference(&harness_found_names).copied().collect();
            let joined_string = harnesses_missing.join("`, `");

            bail!(
                "Failed to match the following harness(es):\n{joined_string}\nPlease specify the fully-qualified name of a harness.",
            );
        }

        // Warn when substring matching selects more harnesses than filter patterns specified (#401).
        // This can be surprising when harness names have common prefixes (e.g., test_foo_1 matches test_foo_12).
        if !self.args.exact
            && !harness_filters.is_empty()
            && compiler_filtered_harnesses.len() > harness_filters.len()
        {
            let filter_patterns: Vec<&str> = harness_filters.iter().copied().collect();
            let harness_names: Vec<&str> =
                compiler_filtered_harnesses.iter().map(|h| h.pretty_name.as_str()).collect();
            warning(&format_args!(
                "Substring matching selected {} harnesses for {} filter(s).\n\
                 Filters: {}\n\
                 Selected: {}\n\
                 Use --exact for exact matching.",
                compiler_filtered_harnesses.len(),
                harness_filters.len(),
                filter_patterns.join(", "),
                harness_names.join(", ")
            ));
        }

        // Config-free selection (`--config-free`): run only harnesses that need
        // no per-harness configuration. This is the set executed BY DEFAULT
        // during Trust compilation — batteries-on Kani-style verification that
        // requires no manual tuning. We do NOT silently drop the
        // config-requiring harnesses: each is reported with the configuration it
        // needs, so coverage stays honest (a skipped proof is not a proved one).
        if self.args.config_free {
            let (config_free, needs_config): (Vec<_>, Vec<_>) =
                compiler_filtered_harnesses.into_iter().partition(|h| is_config_free(h));
            for h in &needs_config {
                warning(&format_args!(
                    "config-free run: skipping `{}` — needs {}; verify it explicitly with \
                     `--harness {}` (without --config-free)",
                    h.pretty_name,
                    describe_required_config(&h.attributes),
                    h.pretty_name,
                ));
            }
            return Ok(config_free);
        }

        Ok(compiler_filtered_harnesses)
    }
}

/// A "config-free" harness is a bare `#[kani::proof]` with no per-harness
/// configuration that would require manual tuning: no `#[kani::unwind]`, no
/// `#[kani::stub]`, no `#[kani::solver]`, no proof-for-contract target, and no
/// assigns-contract. (`should_panic` is an expected-OUTCOME marker, not a
/// configuration knob, so it does not disqualify a harness.) These verify with
/// trust-mc's defaults, which is exactly what makes them safe to run by default
/// during compilation.
pub(crate) fn is_config_free(h: &HarnessMetadata) -> bool {
    let a = &h.attributes;
    matches!(a.kind, HarnessKind::Proof)
        && a.solver.is_none()
        && a.unwind_value.is_none()
        && a.stubs.is_empty()
        && a.verified_stubs.is_empty()
        && h.contract.is_none()
}

/// Human-readable description of the configuration a non-config-free harness
/// requires, for the honest "skipped" report.
fn describe_required_config(a: &HarnessAttributes) -> String {
    let mut parts = Vec::new();
    if let Some(u) = a.unwind_value {
        parts.push(format!("#[kani::unwind({u})]"));
    }
    if !a.stubs.is_empty() {
        parts.push(format!("{} stub(s)", a.stubs.len()));
    }
    if !a.verified_stubs.is_empty() {
        parts.push(format!("{} verified-stub(s)", a.verified_stubs.len()));
    }
    if a.solver.is_some() {
        parts.push("a #[kani::solver] choice".to_string());
    }
    if let HarnessKind::ProofForContract { target_fn } = &a.kind {
        parts.push(format!("a proof-for-contract on `{target_fn}`"));
    }
    if parts.is_empty() { "manual configuration".to_string() } else { parts.join(", ") }
}

/// Sort harnesses such that for two harnesses in the same file, it is guaranteed that later
/// appearing harnesses get processed earlier.
/// This is necessary for the concrete playback feature (with in-place unit test modification)
/// because it guarantees that injected unit tests will not change the location of to-be-processed harnesses.
pub(crate) fn sort_harnesses_by_loc<'a>(
    harnesses: &[&'a HarnessMetadata],
) -> Vec<&'a HarnessMetadata> {
    let mut harnesses_clone = harnesses.to_vec();
    harnesses_clone.sort_unstable_by(|harness1, harness2| {
        harness1
            .original_file
            .cmp(&harness2.original_file)
            .then(harness1.original_start_line.cmp(&harness2.original_start_line).reverse())
    });
    harnesses_clone
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use trust_mc_metadata::{HarnessAttributes, HarnessKind};

    fn mock_proof_harness(
        name: &str,
        unwind_value: Option<u32>,
        krate: Option<&str>,
    ) -> HarnessMetadata {
        let mut attributes = HarnessAttributes::new(HarnessKind::Proof);
        attributes.unwind_value = unwind_value;
        HarnessMetadata {
            pretty_name: name.into(),
            mangled_name: name.into(),
            crate_name: krate.unwrap_or("<unknown>").into(),
            original_file: "<unknown>".into(),
            original_start_line: 0,
            original_end_line: 0,
            attributes,
            model_file: PathBuf::from("<mock>"),
            contract: Default::default(),
            has_loop_contracts: false,
            is_automatically_generated: false,
        }
    }

    #[test]
    fn config_free_selects_bare_proofs_only() {
        // Bare #[kani::proof] with no per-harness config → config-free.
        let bare = mock_proof_harness("bare", None, None);
        assert!(is_config_free(&bare), "bare #[kani::proof] is config-free");

        // #[kani::unwind(N)] → NOT config-free (needs a manual loop bound).
        let unwound = mock_proof_harness("unwound", Some(9), None);
        assert!(!is_config_free(&unwound), "an explicit unwind is configuration");

        // A #[kani::stub] → NOT config-free.
        let mut stubbed = mock_proof_harness("stubbed", None, None);
        stubbed.attributes.stubs =
            vec![trust_mc_metadata::Stub { original: "orig".into(), replacement: "repl".into() }];
        assert!(!is_config_free(&stubbed), "a stub is configuration");

        // A proof-for-contract harness → NOT config-free (needs a target_fn).
        let mut contract_harness = mock_proof_harness("contract", None, None);
        contract_harness.attributes.kind =
            HarnessKind::ProofForContract { target_fn: "tgt".into() };
        assert!(!is_config_free(&contract_harness), "proof-for-contract is configuration");

        // should_panic is an expected-OUTCOME marker, not configuration.
        let mut panics = mock_proof_harness("panics", None, None);
        panics.attributes.should_panic = true;
        assert!(is_config_free(&panics), "should_panic does not require tuning");
    }

    #[test]
    fn check_find_proof_harness_without_exact() {
        let harnesses = [
            mock_proof_harness("check_one", None, None),
            mock_proof_harness("module::check_two", None, None),
            mock_proof_harness("module::not_check_three", None, None),
        ];
        let ref_harnesses = harnesses.iter().collect::<Vec<_>>();

        // Check with harness filtering
        assert_eq!(
            find_proof_harnesses(&BTreeSet::from(["check_three"]), &ref_harnesses, false,).len(),
            1
        );
        assert!(
            find_proof_harnesses(&BTreeSet::from(["check_two"]), &ref_harnesses, false,)
                .first()
                .unwrap()
                .mangled_name
                == "module::check_two"
        );
        assert!(
            find_proof_harnesses(&BTreeSet::from(["check_one"]), &ref_harnesses, false,)
                .first()
                .unwrap()
                .mangled_name
                == "check_one"
        );
    }

    #[test]
    fn check_find_proof_harness_with_exact() {
        // Check with exact match

        let harnesses = [
            mock_proof_harness("check_one", None, None),
            mock_proof_harness("module::check_two", None, None),
            mock_proof_harness("module::not_check_three", None, None),
        ];
        let ref_harnesses = harnesses.iter().collect::<Vec<_>>();

        assert!(
            find_proof_harnesses(&BTreeSet::from(["check_three"]), &ref_harnesses, true,)
                .is_empty()
        );
        // Kani's `--exact` deliberately does NOT match the unqualified name; only
        // the fully-qualified name selects a harness. So unqualified "check_two"
        // must NOT match "module::check_two" in exact mode...
        assert!(
            find_proof_harnesses(&BTreeSet::from(["check_two"]), &ref_harnesses, true).is_empty()
        );
        // ...while the fully-qualified "module::check_two" does.
        assert_eq!(
            find_proof_harnesses(&BTreeSet::from(["module::check_two"]), &ref_harnesses, true)
                .first()
                .unwrap()
                .mangled_name,
            "module::check_two"
        );
        assert_eq!(
            find_proof_harnesses(&BTreeSet::from(["check_one"]), &ref_harnesses, true)
                .first()
                .unwrap()
                .mangled_name,
            "check_one"
        );
        assert_eq!(
            find_proof_harnesses(
                &BTreeSet::from(["module::not_check_three"]),
                &ref_harnesses,
                true,
            )
            .first()
            .unwrap()
            .mangled_name,
            "module::not_check_three"
        );
    }
}
