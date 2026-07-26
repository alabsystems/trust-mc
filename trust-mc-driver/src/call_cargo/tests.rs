// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::output::{
    cargo_message_format_arg, dev_dep_hint_json, dev_dep_hint_message,
    extract_unresolved_import_name, parse_cargo_message,
};
use super::targets::{VerificationTarget, filter_features_for_package, package_targets};
use crate::args::common::MessageFormat;
use cargo_metadata::diagnostic::Diagnostic;
use cargo_metadata::{CompilerMessage, Message, Package};
use clap::Parser;

fn make_package_with_features(features: &[&str]) -> Package {
    let features_map: serde_json::Map<String, serde_json::Value> =
        features.iter().map(|f| (f.to_string(), serde_json::Value::Array(vec![]))).collect();
    serde_json::from_value(serde_json::json!({
        "name": "test-pkg",
        "version": "0.1.0",
        "id": "test-pkg 0.1.0 (path+file:///tmp/test)",
        "source": null,
        "dependencies": [],
        "targets": [],
        "features": features_map,
        "manifest_path": "/tmp/test/Cargo.toml",
        "edition": "2021",
    }))
    .expect("valid test Package JSON")
}

fn make_package_with_targets(targets: serde_json::Value) -> Package {
    serde_json::from_value(serde_json::json!({
        "name": "target-pkg",
        "version": "0.1.0",
        "id": "target-pkg 0.1.0 (path+file:///tmp/target)",
        "source": null,
        "dependencies": [],
        "targets": targets,
        "features": {},
        "manifest_path": "/tmp/target/Cargo.toml",
        "edition": "2021",
    }))
    .expect("valid target Package JSON")
}

fn make_target(name: &str, kind: &str, crate_type: &str) -> serde_json::Value {
    serde_json::json!({
        "name": name,
        "kind": [kind],
        "crate_types": [crate_type],
        "src_path": format!("/tmp/target/{name}.rs"),
        "edition": "2021",
        "doctest": true,
        "test": true,
        "doc": true,
    })
}

fn parse_verify_args(args: &[&str]) -> crate::args::VerificationArgs {
    crate::args::CargoKaniArgs::try_parse_from(args).unwrap().verify_opts
}

fn target_args(targets: Vec<VerificationTarget>) -> Vec<Vec<String>> {
    targets.iter().map(VerificationTarget::to_args).collect()
}

#[test]
fn package_targets_selects_named_example_only() {
    let args = parse_verify_args(&["cargo-trust-mc", "--example", "demo"]);
    let package = make_package_with_targets(serde_json::json!([
        make_target("target_pkg", "lib", "lib"),
        make_target("app", "bin", "bin"),
        make_target("demo", "example", "bin"),
        make_target("other", "example", "bin"),
    ]));

    assert_eq!(
        target_args(package_targets(&args, &package)),
        vec![vec!["--example".to_string(), "demo".to_string()]]
    );
}

#[test]
fn package_targets_selects_test_without_tests_mode_when_explicit() {
    let args = parse_verify_args(&["cargo-trust-mc", "--test", "integ"]);
    let package = make_package_with_targets(serde_json::json!([
        make_target("target_pkg", "lib", "lib"),
        make_target("integ", "test", "bin"),
    ]));

    assert_eq!(
        target_args(package_targets(&args, &package)),
        vec![vec!["--test".to_string(), "integ".to_string()]]
    );
}

#[test]
fn package_targets_all_targets_includes_supported_kinds() {
    let args = parse_verify_args(&["cargo-trust-mc", "--all-targets"]);
    let package = make_package_with_targets(serde_json::json!([
        make_target("target_pkg", "lib", "lib"),
        make_target("app", "bin", "bin"),
        make_target("demo", "example", "bin"),
        make_target("integ", "test", "bin"),
        make_target("speed", "bench", "bin"),
    ]));

    assert_eq!(
        target_args(package_targets(&args, &package)),
        vec![
            vec!["--lib".to_string()],
            vec!["--bin".to_string(), "app".to_string()],
            vec!["--example".to_string(), "demo".to_string()],
            vec!["--test".to_string(), "integ".to_string()],
            vec!["--bench".to_string(), "speed".to_string()],
        ]
    );
}

#[test]
fn test_filter_features_keeps_matching() {
    let pkg = make_package_with_features(&["feat_a", "feat_b"]);
    let requested = vec!["feat_a".to_string(), "feat_b".to_string()];
    let result = filter_features_for_package(&requested, &pkg);
    assert_eq!(result, vec!["feat_a", "feat_b"]);
}

#[test]
fn test_filter_features_drops_undeclared() {
    let pkg = make_package_with_features(&["feat_a"]);
    let requested = vec!["feat_a".to_string(), "feat_c".to_string()];
    let result = filter_features_for_package(&requested, &pkg);
    assert_eq!(result, vec!["feat_a"]);
}

#[test]
fn test_filter_features_empty_when_none_match() {
    let pkg = make_package_with_features(&["feat_x"]);
    let requested = vec!["feat_a".to_string(), "feat_b".to_string()];
    let result = filter_features_for_package(&requested, &pkg);
    assert!(result.is_empty());
}

#[test]
fn test_filter_features_empty_request() {
    let pkg = make_package_with_features(&["feat_a"]);
    let requested: Vec<String> = vec![];
    let result = filter_features_for_package(&requested, &pkg);
    assert!(result.is_empty());
}

fn make_e0432_diagnostic(msg: &str) -> Diagnostic {
    serde_json::from_value(serde_json::json!({
        "message": msg,
        "code": {"code": "E0432", "explanation": null},
        "level": "error",
        "spans": [],
        "children": [],
        "rendered": null,
    }))
    .expect("valid diagnostic JSON")
}

fn make_compiler_message(message: &str, level: &str) -> CompilerMessage {
    serde_json::from_value(serde_json::json!({
        "package_id": "test-pkg 0.1.0 (path+file:///tmp/test)",
        "target": make_target("target_pkg", "lib", "lib"),
        "message": {
            "message": message,
            "code": null,
            "level": level,
            "spans": [],
            "children": [],
            "rendered": format!("{level}: {message}\n"),
        },
    }))
    .expect("valid compiler message JSON")
}

#[test]
fn test_parse_cargo_message_keeps_compiler_message() {
    let msg = make_compiler_message("ordinary warning", "warning");
    let raw = serde_json::to_string(&Message::CompilerMessage(msg.clone())).unwrap();

    assert_eq!(parse_cargo_message(&raw).unwrap(), Message::CompilerMessage(msg));
}

#[test]
fn test_parse_cargo_message_falls_back_to_text_line() {
    assert_eq!(parse_cargo_message("not json").unwrap(), Message::TextLine("not json".to_string()));
}

#[test]
fn test_cargo_message_format_arg_matches_requested_output() {
    assert_eq!(cargo_message_format_arg(MessageFormat::Human), "json-diagnostic-rendered-ansi");
    assert_eq!(cargo_message_format_arg(MessageFormat::Json), "json");
}

#[test]
fn test_dev_dep_hint_json_is_compiler_message() {
    let msg = make_compiler_message("unresolved import `some_dev_dep`", "error");
    let raw = dev_dep_hint_json(&msg, dev_dep_hint_message("some_dev_dep")).unwrap();
    let value: serde_json::Value = serde_json::from_str(&raw).unwrap();

    assert_eq!(value["reason"], "compiler-message");
    assert_eq!(value["message"]["level"], "help");
    assert!(value["message"]["message"].as_str().unwrap().contains("some_dev_dep"));
    assert!(value["message"]["rendered"].as_str().unwrap().starts_with("help: "));
}

#[test]
fn test_extract_unresolved_single_segment() {
    let diag = make_e0432_diagnostic("unresolved import `unicode_width`");
    assert_eq!(extract_unresolved_import_name(&diag), Some("unicode_width".to_string()));
}

#[test]
fn test_extract_unresolved_nested_path_first_segment() {
    let diag = make_e0432_diagnostic("unresolved import `anyhow::Result`");
    assert_eq!(extract_unresolved_import_name(&diag), Some("anyhow".to_string()));
}

#[test]
fn test_extract_unresolved_ignores_non_e0432() {
    let diag: Diagnostic = serde_json::from_value(serde_json::json!({
        "message": "unresolved import `anyhow`",
        "code": {"code": "E0277", "explanation": null},
        "level": "error",
        "spans": [],
        "children": [],
        "rendered": null,
    }))
    .expect("valid diagnostic JSON");
    assert_eq!(extract_unresolved_import_name(&diag), None);
}

#[test]
fn test_extract_unresolved_ignores_missing_code() {
    let mut diag = make_e0432_diagnostic("unresolved import `anyhow`");
    diag.code = None;
    assert_eq!(extract_unresolved_import_name(&diag), None);
}

#[test]
fn test_extract_unresolved_ignores_unrelated_message() {
    let diag = make_e0432_diagnostic("something else entirely");
    assert_eq!(extract_unresolved_import_name(&diag), None);
}
