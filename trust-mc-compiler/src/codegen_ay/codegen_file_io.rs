// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! File I/O and codegen-results factory for the AY backend.

use ay_bindings::AYProgram;
use rustc_codegen_ssa::back::archive::{
    ArArchiveBuilder, ArchiveBuilder, ArchiveBuilderBuilder, DEFAULT_OBJECT_READER,
};
use rustc_codegen_ssa::{CodegenResults, CrateInfo};
use rustc_data_structures::fx::FxIndexMap;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::fs::File;
use std::io::BufWriter;
use std::path::Path;
use tracing::{debug, info};
use trust_mc_metadata::ArtifactType;
use trust_mc_metadata::artifact::convert_type;

pub(in crate::codegen_ay) fn codegen_results(tcx: TyCtxt) -> Box<dyn std::any::Any> {
    let work_products = FxIndexMap::<WorkProductId, WorkProduct>::default();
    Box::new((
        CodegenResults {
            modules: vec![],
            allocator_module: None,
            crate_info: CrateInfo::new(tcx, "ay".to_owned()),
        },
        work_products,
    ))
}

pub(super) struct ArArchiveBuilderBuilder;

impl ArchiveBuilderBuilder for ArArchiveBuilderBuilder {
    fn new_archive_builder<'a>(&self, sess: &'a Session) -> Box<dyn ArchiveBuilder + 'a> {
        Box::new(ArArchiveBuilder::new(sess, &DEFAULT_OBJECT_READER))
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(in crate::codegen_ay) enum JsonOutputStyle {
    Compact,
    Pretty,
}

/// Write a serializable value to a JSON file alongside the base path.
///
/// Returns `Err` on file creation or serialization failure so callers can
/// report the error through the compiler diagnostics pipeline (#3257).
pub(in crate::codegen_ay) fn write_file<T>(
    base_path: &Path,
    file_type: ArtifactType,
    source: &T,
    style: JsonOutputStyle,
) -> std::io::Result<()>
where
    T: serde::Serialize,
{
    let filename = convert_type(base_path, file_type);
    debug!(?filename, "write_json");
    let out_file = File::create(&filename)?;
    let writer = BufWriter::new(out_file);
    match style {
        JsonOutputStyle::Pretty => serde_json::to_writer_pretty(writer, &source),
        JsonOutputStyle::Compact => serde_json::to_writer(writer, &source),
    }
    .map_err(std::io::Error::other)
}

/// Format SMT-LIB2 text with compiler-emitted marker comments.
///
/// Appends `; DEMOTED_FALLBACK:` per demoted fallback (#3788) and
/// `; RECURSIVE_UNWIND_ASSERTION:` per recursive unwind exhaustion (#4058).
fn format_smt2_with_markers(
    program: &AYProgram,
    demoted_fallback_count: usize,
    recursive_unwind_count: usize,
) -> String {
    let mut smt = program.to_string();
    if demoted_fallback_count == 0 && recursive_unwind_count == 0 {
        return smt;
    }

    if !smt.is_empty() && !smt.ends_with('\n') {
        smt.push('\n');
    }
    for _ in 0..demoted_fallback_count {
        smt.push_str("; DEMOTED_FALLBACK: chc_fallback\n");
    }
    for _ in 0..recursive_unwind_count {
        smt.push_str("; RECURSIVE_UNWIND_ASSERTION: chc_recursive_unwind\n");
    }
    smt
}

/// Default fail-closed serialization budget, in distinct SMT-LIB term nodes.
///
/// Sized so any realistic harness serializes well under it, while a runaway
/// program is refused before it can exhaust memory. Each node serializes to a
/// handful of bytes and the share/serialize passes allocate a few node-keyed
/// maps, so ~20M nodes bounds peak serialization memory to a few GB — far below
/// the 26GB-class blowups that crashed the machine. Override with the env var
/// `TRUST_MC_SMT_NODE_BUDGET`.
const DEFAULT_SMT_NODE_BUDGET: usize = 20_000_000;

fn smt_node_budget() -> usize {
    std::env::var("TRUST_MC_SMT_NODE_BUDGET")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&b| b > 0)
        .unwrap_or(DEFAULT_SMT_NODE_BUDGET)
}

/// Whether `program` would exceed `budget` distinct serialized term nodes. Uses
/// the saturating, DAG-aware estimate, so it is cheap even on a program whose
/// unfolded form is astronomically large. Pure (no I/O / env) so it is unit-testable.
fn over_serialization_budget(program: &AYProgram, budget: usize) -> bool {
    program.serialized_node_estimate(budget) >= budget
}

/// Write an SMT-LIB2 file for the AY solver.
///
/// Appends `; DEMOTED_FALLBACK:` and `; RECURSIVE_UNWIND_ASSERTION:` comment
/// markers so the driver can trigger appropriate post-solving policy (#3788, #4058).
///
/// Returns `Err` on file creation or write failure (#3257), or when the program
/// exceeds the fail-closed serialization budget — see below.
pub(in crate::codegen_ay) fn write_smt2_file(
    path: &Path,
    program: &AYProgram,
    demoted_fallback_count: usize,
    recursive_unwind_count: usize,
) -> std::io::Result<()> {
    // Fail-closed serialization budget (OOM guard). Estimate the program's
    // serialized size in DISTINCT term nodes BEFORE materializing it; if it hits
    // the budget, refuse to serialize and return an error. The caller turns that
    // into a per-harness diagnostic, so the harness is reported inconclusive /
    // resource-exhausted — never SUCCESSFUL. This bounds compiler memory: the
    // 2026-06-12 OOM wrote a 3.6GB SMT2 and killed the machine before any
    // wall-clock cap. (With the ay DAG-share fix the common exponential case now
    // has a small distinct-node count and never trips this; the budget is the
    // backstop for a genuinely huge program or any future un-shared path.)
    let budget = smt_node_budget();
    if over_serialization_budget(program, budget) {
        return Err(std::io::Error::other(format!(
            "SMT serialization budget exceeded (>= {budget} distinct term nodes): refusing to \
             serialize to avoid OOM. This harness is resource-exhausted / INCONCLUSIVE, not \
             verified. Raise TRUST_MC_SMT_NODE_BUDGET to attempt it anyway."
        )));
    }
    let out_file = File::create(path)?;
    let mut writer = BufWriter::new(out_file);
    use std::io::Write;
    write!(
        writer,
        "{}",
        format_smt2_with_markers(program, demoted_fallback_count, recursive_unwind_count)
    )?;
    info!(?path, "Wrote SMT-LIB2 file");
    Ok(())
}

/// Write a VC artifact sidecar (`.vc.json`) alongside the SMT file.
///
/// The artifact contains property metadata (kind, location, violation variable name)
/// that the driver uses to map solver results back to source locations.
///
/// Returns `Err` on file creation or serialization failure (#3257).
pub(in crate::codegen_ay) fn write_vc_artifact(
    path: &Path,
    artifact: &trust_mc_core::artifact::VcArtifact,
) -> std::io::Result<()> {
    let out_file = File::create(path)?;
    let writer = BufWriter::new(out_file);
    serde_json::to_writer_pretty(writer, artifact).map_err(std::io::Error::other)?;
    info!(?path, "Wrote VC artifact");
    Ok(())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;
    use trust_mc_metadata::KaniMetadata;

    // --- write_smt2_file ---

    #[test]
    fn test_write_smt2_file_creates_file() {
        let dir = std::env::temp_dir().join("trust_mc_test_smt2");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test_output.smt2");

        let program = AYProgram::new();
        write_smt2_file(&path, &program, 0, 0).unwrap();

        assert!(path.exists());
        // Verify file is readable (read_to_string succeeds)
        let _content = std::fs::read_to_string(&path).unwrap();

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn test_over_serialization_budget_predicate() {
        // Empty program embeds no term nodes -> under any positive budget.
        assert!(!over_serialization_budget(&AYProgram::new(), 1));

        // A program with term nodes trips a budget of 1 (fail closed), but not a
        // generous budget.
        let mut program = AYProgram::new();
        program.assert(ay_bindings::Expr::var("p", ay_bindings::sort::Sort::bool()));
        assert!(
            over_serialization_budget(&program, 1),
            "a non-empty program must exceed a budget of 1 node"
        );
        assert!(
            !over_serialization_budget(&program, DEFAULT_SMT_NODE_BUDGET),
            "a tiny program must be well under the default budget"
        );
    }

    #[test]
    fn test_write_smt2_file_invalid_path_returns_err() {
        let dir = std::env::temp_dir().join("trust_mc_test_smt2_invalid_path");
        std::fs::create_dir_all(&dir).unwrap();
        let program = AYProgram::new();

        // Writing to a directory path should return Err (#3257).
        assert!(write_smt2_file(&dir, &program, 0, 0).is_err());
        assert!(dir.is_dir());

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn test_format_smt2_markers_skips_clean_program() {
        let program = AYProgram::new();
        assert_eq!(format_smt2_with_markers(&program, 0, 0), "");
    }

    #[test]
    fn test_format_smt2_markers_demoted_repeats_once_per_site() {
        let program = AYProgram::new();
        let smt = format_smt2_with_markers(&program, 2, 0);
        assert_eq!(smt, "; DEMOTED_FALLBACK: chc_fallback\n; DEMOTED_FALLBACK: chc_fallback\n");
    }

    #[test]
    fn test_format_smt2_markers_recursive_unwind() {
        let program = AYProgram::new();
        let smt = format_smt2_with_markers(&program, 0, 1);
        assert_eq!(smt, "; RECURSIVE_UNWIND_ASSERTION: chc_recursive_unwind\n");
    }

    #[test]
    fn test_format_smt2_markers_both() {
        let program = AYProgram::new();
        let smt = format_smt2_with_markers(&program, 1, 1);
        assert!(smt.contains("; DEMOTED_FALLBACK:"));
        assert!(smt.contains("; RECURSIVE_UNWIND_ASSERTION:"));
    }

    // --- write_vc_artifact ---

    #[test]
    fn test_write_vc_artifact_creates_json() {
        let dir = std::env::temp_dir().join("trust_mc_test_vc");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("test.vc.json");

        let harness_id = trust_mc_core::ident::HarnessId::new("test_harness", "test_harness");
        let artifact = trust_mc_core::artifact::VcArtifact::new(harness_id);
        write_vc_artifact(&path, &artifact).unwrap();

        assert!(path.exists());
        let content = std::fs::read_to_string(&path).unwrap();
        assert!(content.contains("test_harness"));

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn test_write_vc_artifact_invalid_path_returns_err() {
        let dir = std::env::temp_dir().join("trust_mc_test_vc_invalid_path");
        std::fs::create_dir_all(&dir).unwrap();

        let harness_id = trust_mc_core::ident::HarnessId::new("test_harness", "test_harness");
        let artifact = trust_mc_core::artifact::VcArtifact::new(harness_id);

        // Writing to a directory path should return Err (#3257).
        assert!(write_vc_artifact(&dir, &artifact).is_err());
        assert!(dir.is_dir());

        std::fs::remove_dir_all(&dir).unwrap();
    }

    // --- write_file ---

    #[test]
    fn test_write_file_json() {
        let dir = std::env::temp_dir().join("trust_mc_test_write_file");
        std::fs::create_dir_all(&dir).unwrap();
        let base = dir.join("output");

        let md = KaniMetadata {
            crate_name: "write_test".into(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            unconstrained_assignments: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        write_file(&base, ArtifactType::Metadata, &md, JsonOutputStyle::Compact).unwrap();

        let expected_path =
            trust_mc_metadata::artifact::convert_type(&base, ArtifactType::Metadata);
        assert!(expected_path.exists());
        let content = std::fs::read_to_string(&expected_path).unwrap();
        assert!(content.contains("write_test"));

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn test_write_file_pretty_json() {
        let dir = std::env::temp_dir().join("trust_mc_test_write_pretty");
        std::fs::create_dir_all(&dir).unwrap();
        let base = dir.join("output");

        let md = KaniMetadata {
            crate_name: "pretty_test".into(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            unconstrained_assignments: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };
        write_file(&base, ArtifactType::Metadata, &md, JsonOutputStyle::Pretty).unwrap();

        let expected_path =
            trust_mc_metadata::artifact::convert_type(&base, ArtifactType::Metadata);
        let content = std::fs::read_to_string(&expected_path).unwrap();
        // Pretty JSON has newlines and indentation
        assert!(content.contains('\n'));
        assert!(content.contains("pretty_test"));

        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn test_write_file_invalid_parent_returns_err() {
        let dir = std::env::temp_dir().join("trust_mc_test_write_file_invalid_parent");
        let nested = dir.join("missing").join("output");
        if dir.exists() {
            std::fs::remove_dir_all(&dir).unwrap();
        }

        let md = KaniMetadata {
            crate_name: "write_test_invalid".into(),
            proof_harnesses: vec![],
            unsupported_features: vec![],
            test_harnesses: vec![],
            contracted_functions: vec![],
            autoharness_md: None,
            iterator_unsoundness: None,
            bigint_unsoundness: None,
            chc_fallbacks: None,
            chc_translation_drops: None,
            chc_coerce_eq_drops: None,
            assume_dropped_transitions: None,
            store_dropped_transitions: None,
            constant_zero_fallbacks: None,
            unhandled_calls: None,
            error_blocked_fmt: None,
            known_stdlib_unconstrained: None,
            inferable_predicates: None,
            diverging_call_drops: None,
            assert_untranslatable: None,
            heap_check_untranslatable: None,
            heap_check_unknown_layout: None,
            type_sort_fallbacks: None,
            signedness_fallbacks: None,
            into_option_drops: None,
            internal_workarounds: None,
            abstracted_fallbacks: None,
            vec_field_fallbacks: None,
            pointee_synthesis_fallbacks: None,
            unsupported_construct_fallbacks: None,
            bmc_store_coercion_fallbacks: None,
            kani_mem_overapprox: None,
            offset_provenance_unresolved: None,
            sort_harmonize_fresh_var_fallbacks: None,
            unconstrained_assignments: None,
            ptr_metadata_unconstrained: None,
            static_init_incomplete: None,
            fp_bitvector_encoding: None,
            aggregate_encoding_gap: None,
            stub_approximation: None,
            rounding_assertion_bypass: None,
        };

        let expected_path =
            trust_mc_metadata::artifact::convert_type(&nested, ArtifactType::Metadata);
        // Missing parent directory should return Err (#3257).
        assert!(
            write_file(&nested, ArtifactType::Metadata, &md, JsonOutputStyle::Compact).is_err()
        );
        assert!(!expected_path.exists());
    }
}
