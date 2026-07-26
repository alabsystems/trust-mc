// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::args::common::MessageFormat;
use crate::session::{DEFAULT_TOOL_TIMEOUT_SECS, KaniSession, wait_with_timeout};
use crate::util::args::CargoArg;
use anyhow::{Context, Result, bail};
use cargo_metadata::diagnostic::{Diagnostic, DiagnosticLevel};
use cargo_metadata::{
    Artifact as RustcArtifact, CompilerMessage, DependencyKind, Message, Metadata, PackageId,
};
use serde::Deserialize;
use std::io::{BufRead, BufReader, IsTerminal, Write};
use std::process::Command;
use std::time::Duration;

impl KaniSession {
    /// Run cargo and collect any error found.
    /// We also collect the metadata file generated during compilation if any.
    ///
    /// When `metadata` is provided, `unresolved import` errors referencing a crate listed in
    /// the emitting package's `[dev-dependencies]` are annotated with a hint pointing at the
    /// `--tests` + `#[cfg(all(kani, test))]` workaround (see `guide/src/usage.md`).
    pub(super) fn run_build(
        &self,
        cargo_cmd: Command,
        metadata: Option<&Metadata>,
    ) -> Result<Vec<RustcArtifact>> {
        let output_format = CargoBuildOutputFormat::new(self.args.common_args.message_format);
        let mut artifacts = vec![];
        let mut cargo_process = self.run_piped(cargo_cmd)?;
        let stdout = cargo_process.stdout.take().context("failed to capture cargo stdout")?;
        let mut reader = BufReader::new(stdout);
        let mut error_count = 0;
        let mut line = String::new();
        loop {
            line.clear();
            if reader.read_line(&mut line).context("failed to read cargo message")? == 0 {
                break;
            }

            let raw_message = line.trim_end_matches(['\r', '\n']);
            let message = parse_cargo_message(raw_message)?;
            match message {
                Message::CompilerMessage(msg) => match msg.message.level {
                    DiagnosticLevel::FailureNote => {
                        print_compiler_message(&msg, raw_message, output_format)?;
                    }
                    DiagnosticLevel::Error => {
                        error_count += 1;
                        print_compiler_message(&msg, raw_message, output_format)?;
                        maybe_print_dev_dep_hint(&msg, metadata, output_format)?;
                    }
                    DiagnosticLevel::Ice => {
                        print_compiler_message(&msg, raw_message, output_format)?;
                        // Don't wait - just return the error. Process will be cleaned up on drop.
                        return Err(anyhow::Error::msg(msg.message).context(format!(
                            "Failed to compile `{}` due to an internal compiler error.",
                            msg.target.name
                        )));
                    }
                    _ => {
                        if !self.args.common_args.quiet {
                            print_compiler_message(&msg, raw_message, output_format)?;
                        }
                    }
                },
                Message::CompilerArtifact(rustc_artifact) => {
                    // Compares two targets, and falls back to a weaker
                    // comparison where we avoid dashes in their names.
                    artifacts.push(rustc_artifact)
                }
                Message::BuildScriptExecuted(_) | Message::BuildFinished(_) => {
                    // do nothing
                }
                Message::TextLine(msg) => {
                    if !self.args.common_args.quiet && output_format.is_human() {
                        writeln!(std::io::stdout(), "{msg}")?;
                    }
                }

                // Non-exhaustive enum.
                _ => {
                    if !self.args.common_args.quiet && output_format.is_human() {
                        writeln!(std::io::stdout(), "{message:?}")?;
                    }
                }
            }
        }
        // Use timeout protection (#997)
        let timeout = self.tool_timeout().unwrap_or(Duration::from_secs(DEFAULT_TOOL_TIMEOUT_SECS));
        let status = wait_with_timeout(cargo_process, timeout, "cargo build")?;
        if !status.success() {
            bail!("Failed to execute cargo ({status}). Found {error_count} compilation errors.");
        }
        Ok(artifacts)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(super) enum CargoBuildOutputFormat {
    Human { support_color: bool },
    Json,
}

impl CargoBuildOutputFormat {
    fn new(message_format: MessageFormat) -> Self {
        match message_format {
            MessageFormat::Human => {
                CargoBuildOutputFormat::Human { support_color: std::io::stdout().is_terminal() }
            }
            MessageFormat::Json => CargoBuildOutputFormat::Json,
        }
    }

    fn is_human(self) -> bool {
        matches!(self, CargoBuildOutputFormat::Human { .. })
    }
}

pub(super) fn parse_cargo_message(raw_message: &str) -> Result<Message> {
    let mut deserializer = serde_json::Deserializer::from_str(raw_message);
    deserializer.disable_recursion_limit();
    Ok(Message::deserialize(&mut deserializer)
        .unwrap_or_else(|_| Message::TextLine(raw_message.to_string())))
}

fn print_compiler_message(
    msg: &CompilerMessage,
    raw_message: &str,
    output_format: CargoBuildOutputFormat,
) -> Result<()> {
    match output_format {
        CargoBuildOutputFormat::Human { support_color } => print_msg(&msg.message, support_color),
        CargoBuildOutputFormat::Json => {
            writeln!(std::io::stdout(), "{raw_message}")?;
            Ok(())
        }
    }
}

pub(super) fn cargo_message_format_arg(message_format: MessageFormat) -> &'static str {
    match message_format {
        MessageFormat::Human => "json-diagnostic-rendered-ansi",
        MessageFormat::Json => "json",
    }
}

pub(crate) fn cargo_config_args() -> Vec<CargoArg> {
    [
        "--target",
        env!("TARGET"),
        // Propagate `--cfg=kani_host` to build scripts.
        "-Zhost-config",
        "-Ztarget-applies-to-host",
        "--config=host.rustflags=[\"--cfg=kani_host\"]",
    ]
    .map(CargoArg::from)
    .to_vec()
}

/// Print the compiler message following the coloring schema.
fn print_msg(diagnostic: &Diagnostic, use_rendered: bool) -> Result<()> {
    if use_rendered {
        std::io::stdout().write_all(diagnostic.to_string().as_bytes())?;
    } else if let Some(rendered) = diagnostic.rendered.as_ref() {
        std::io::stdout().write_all(console::strip_ansi_codes(rendered).as_bytes())?;
    }
    Ok(())
}

/// Documentation URL for the dev-dependency workaround under `#[cfg(kani)]`.
///
/// Ships alongside `guide/src/usage.md`. Kept as a constant so the diagnostic and
/// the documentation never drift.
const DEV_DEPS_DOC_URL: &str =
    "https://model-checking.github.io/kani/usage.html#using-dev-dependencies-in-library-proofs";

/// If `diagnostic` is an `unresolved import` error (E0432) whose crate name matches a
/// `[dev-dependencies]` entry of the package that emitted it, print a hint pointing users
/// at the documented `#[cfg(all(kani, test))]` + `--tests` workaround.
///
/// No-op when any of the required context is missing (metadata absent, wrong code, crate
/// not in dev-deps), so we never mis-annotate unrelated resolution errors.
///
/// See `guide/src/usage.md` ("Using dev-dependencies in library proofs") and the
/// `tests/cargo-trust-mc/dev-depends-lib` regression for the failure mode this fires on.
pub(super) fn maybe_print_dev_dep_hint(
    msg: &CompilerMessage,
    metadata: Option<&Metadata>,
    output_format: CargoBuildOutputFormat,
) -> Result<()> {
    let Some(metadata) = metadata else { return Ok(()) };
    let Some(crate_name) = extract_unresolved_import_name(&msg.message) else { return Ok(()) };
    if !package_has_dev_dep(metadata, &msg.package_id, &crate_name) {
        return Ok(());
    }
    let hint = dev_dep_hint_message(&crate_name);
    match output_format {
        CargoBuildOutputFormat::Human { .. } => print_dev_dep_hint_text(&hint),
        CargoBuildOutputFormat::Json => {
            writeln!(std::io::stdout(), "{}", dev_dep_hint_json(msg, hint)?)?;
        }
    }
    Ok(())
}

pub(super) fn dev_dep_hint_message(crate_name: &str) -> String {
    format!(
        "`{crate_name}` is declared as a dev-dependency, which cargo does not resolve \
         when building the library target alone. Gate proofs that import it with \
         `#[cfg(all(kani, test))]` and invoke `cargo trust-mc --tests`. See {DEV_DEPS_DOC_URL}."
    )
}

fn print_dev_dep_hint_text(hint: &str) {
    // Note: stderr (eprintln) so it interleaves with rustc's diagnostic stream.
    let _ = writeln!(std::io::stderr(), "hint: {hint}");
}

pub(super) fn dev_dep_hint_json(msg: &CompilerMessage, hint: String) -> Result<String> {
    let mut hint_msg = msg.clone();
    let rendered = format!("help: {hint}\n");
    hint_msg.message = serde_json::from_value(serde_json::json!({
        "message": hint,
        "code": null,
        "level": "help",
        "spans": [],
        "children": [],
        "rendered": rendered,
    }))?;
    Ok(serde_json::to_string(&Message::CompilerMessage(hint_msg))?)
}

/// Extract the first path segment of an `unresolved import` error, if any.
///
/// Only returns `Some` when the diagnostic is the rustc `E0432` variant whose top-level
/// message is `unresolved import \`some::path\``. Returns the first `::`-separated
/// segment so we can match it against dev-dep crate names.
pub(super) fn extract_unresolved_import_name(diagnostic: &Diagnostic) -> Option<String> {
    let code = diagnostic.code.as_ref()?;
    if code.code != "E0432" {
        return None;
    }
    // rustc format: `unresolved import \`foo::bar\`` (or `unresolved imports \`a\`, \`b\``).
    // We only handle the single-import case, which is what users hit with missing dev-deps.
    let msg = &diagnostic.message;
    let prefix = "unresolved import `";
    let rest = msg.strip_prefix(prefix)?;
    let path = rest.strip_suffix('`')?;
    let first_segment = path.split("::").next()?.trim();
    if first_segment.is_empty() {
        return None;
    }
    Some(first_segment.to_string())
}

/// Returns true when `crate_name` appears in the `[dev-dependencies]` table of the package
/// identified by `package_id`.
///
/// Cargo records renamed dependencies under `Dependency::rename`; we check both the
/// original name and the renamed identifier so `foo = { package = "bar" }` still matches
/// when the error names `foo`.
fn package_has_dev_dep(metadata: &Metadata, package_id: &PackageId, crate_name: &str) -> bool {
    let Some(package) = metadata.packages.iter().find(|pkg| &pkg.id == package_id) else {
        return false;
    };
    package.dependencies.iter().filter(|dep| dep.kind == DependencyKind::Development).any(|dep| {
        let dep_ident = dep.rename.as_deref().unwrap_or(&dep.name);
        // rustc reports the crate identifier used in source, which matches the Rust
        // (underscore) form of the dependency name.
        dep_ident.replace('-', "_") == crate_name.replace('-', "_")
    })
}
