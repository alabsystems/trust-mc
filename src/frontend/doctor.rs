// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-mc doctor` and `trust-mc version`: what verification needs, whether
//! it is here, and the provenance of what is here.

use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use super::engine::{
    self, Engine, candidates, engine_authority, engine_version, library_dirs, mark, resolve_engine,
    solver_build_sha, solver_hint, solver_path, solver_version,
};
use super::{BUILD_CMD, COMPILER, EXIT_NOT_READY, Fail, Front, VERSION};

/// Set by our `build.rs`: the Rust target triple this front door was built for.
const TARGET: &str = env!("TARGET");

/// `trust-mc doctor [--verbose]`.
pub(crate) fn command(rest: &[OsString]) -> Front<ExitCode> {
    let mut verbose = false;
    let mut json = false;
    for arg in rest {
        match arg.to_str() {
            Some("--verbose" | "-v") => verbose = true,
            Some("--json") => json = true,
            Some(other) => {
                return Err(Fail::usage(format!(
                    "error: `doctor` takes no arguments other than --verbose and --json, got \
                     {other}\n       Usage: trust-mc doctor [--verbose] [--json]"
                )));
            }
            None => {
                return Err(Fail::usage(
                    "error: `doctor` takes no arguments other than --verbose and --json",
                ));
            }
        }
    }
    let report = examine(verbose);
    let code = if report.ready { ExitCode::SUCCESS } else { ExitCode::from(EXIT_NOT_READY) };
    if json {
        print!("{}", report.to_json());
    } else {
        print!("{}", report.text);
    }
    Ok(code)
}

/// `trust-mc version [--verbose]`.
pub(crate) fn version_command(rest: &[OsString]) -> Front<ExitCode> {
    let mut verbose = false;
    for arg in rest {
        match arg.to_str() {
            Some("--verbose" | "-v") => verbose = true,
            Some(other) => {
                return Err(Fail::usage(format!(
                    "error: `version` takes no arguments other than --verbose, got {other}\n       \
                     Usage: trust-mc version [--verbose]"
                )));
            }
            None => {
                return Err(Fail::usage(
                    "error: `version` takes no arguments other than --verbose",
                ));
            }
        }
    }
    println!("trust-mc {VERSION}");
    if !verbose {
        return Ok(ExitCode::SUCCESS);
    }
    println!("target:  {TARGET}");
    match resolve_engine() {
        None => println!("engine:  not installed (run `trust-mc doctor`)"),
        Some(engine) => {
            println!("engine:  {} ({})", engine.driver.display(), engine.source);
            if let Some(version) = engine_version(&engine) {
                println!("         {version}");
            }
            match engine_authority(&engine) {
                Ok(a) => println!(
                    "         linked AY {} @ {}{} (pinned {}{})",
                    a.ay_version,
                    short(&a.ay_linked_sha),
                    if a.matched { "" } else { " [NOT the pinned commit]" },
                    short(&a.ay_pin),
                    if a.trust_mc_dirty { "; engine built from a dirty tree" } else { "" }
                ),
                Err(e) => println!("         AY authority: {}", first_line(&e)),
            }
        }
    }
    match solver_path(resolve_engine().as_ref()) {
        None => println!("solver:  `ay` not on PATH"),
        Some(ay) => {
            println!("solver:  {}", ay.display());
            if let Some(line) = solver_version(&ay) {
                println!("         {line}");
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}

struct Report {
    text: String,
    ready: bool,
    fixes: Vec<String>,
    warnings: Vec<String>,
}

/// Examine the installation. Every check names the path it inspects; `verbose`
/// also shows the commands run.
fn examine(verbose: bool) -> Report {
    let mut out = String::new();
    let mut ready = true;
    let mut fixes: Vec<String> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();
    let line = |out: &mut String, s: String| {
        out.push_str(&s);
        out.push('\n');
    };

    line(&mut out, format!("trust-mc {VERSION} ({TARGET})\n"));

    // -- engine -----------------------------------------------------------
    line(&mut out, "verification engine".to_string());
    let engine = resolve_engine();
    for candidate in candidates() {
        line(
            &mut out,
            format!(
                "  [{}] {}  ({})",
                mark(candidate.found()),
                candidate.display,
                candidate.source
            ),
        );
    }
    let Some(engine) = engine else {
        ready = false;
        line(&mut out, "  using: none found\n".to_string());
        fixes.push(format!(
            "point at an engine you have already built:\n    \
             export TRUST_MC_SYSROOT=<checkout>/target/trust-mc\n  \
             ...or build one from a trust-mc checkout:\n    {BUILD_CMD}\n  \
             ...or install a release bundle:\n    trust-mc setup"
        ));
        finish_solver(&mut out, None, None, &mut ready, &mut fixes, &mut warnings, verbose);
        return finish(out, ready, fixes, warnings);
    };
    line(&mut out, format!("  using: {} ({})", engine.driver.display(), engine.source));

    let compiler = engine.compiler();
    let compiler_present = engine::is_executable(&compiler);
    line(&mut out, format!("  [{}] {COMPILER} beside it", mark(compiler_present)));
    if !compiler_present {
        ready = false;
        fixes.push(format!(
            "the engine needs {COMPILER} next to it; rebuild both:\n    {BUILD_CMD}"
        ));
    }

    if verbose {
        line(&mut out, format!("      $ {} --version", engine.driver.display()));
    }
    match engine_version(&engine) {
        Some(v) => {
            let expected = format!("trust-mc {VERSION}");
            if v.ends_with(&format!(" {VERSION}")) {
                line(&mut out, format!("  [x] engine reports: {v}"));
            } else {
                line(
                    &mut out,
                    format!("  [!] engine reports: {v} (this front door is {expected})"),
                );
                warnings.push(format!(
                    "engine and front door versions differ ({v} vs {expected}); one of them is a\n  \
                     stale build. Rebuild the engine ({BUILD_CMD})\n  \
                     or reinstall the front door (cargo install --path .)."
                ));
            }
        }
        None => {
            ready = false;
            line(&mut out, "  [ ] engine does not answer --version".to_string());
            fixes.push(format!("the engine binary is not runnable; rebuild it:\n    {BUILD_CMD}"));
        }
    }

    if verbose {
        line(&mut out, format!("      $ {} --version-authority", engine.driver.display()));
    }
    let authority = match engine_authority(&engine) {
        Ok(a) => {
            line(
                &mut out,
                format!(
                    "  [x] linked AY {} @ {} ({}{})",
                    a.ay_version,
                    short(&a.ay_linked_sha),
                    if a.matched { "the pinned commit" } else { "NOT the pinned commit" },
                    if a.trust_mc_dirty { ", engine built from a dirty tree" } else { "" }
                ),
            );
            Some(a)
        }
        Err(e) => {
            line(&mut out, format!("  [!] AY authority unavailable: {}", first_line(&e)));
            warnings.push(
                "the engine refuses to attest its linked AY revision (dirty or off-pin build);\n  \
                 verdicts are still produced, but their provenance cannot be quoted."
                    .to_string(),
            );
            None
        }
    };
    line(&mut out, String::new());

    // -- sysroot ----------------------------------------------------------
    line(&mut out, format!("library sysroot  {}", engine.sysroot.display()));
    let mut missing = Vec::new();
    for (label, purpose, dir) in library_dirs(&engine.sysroot) {
        let present = dir.is_dir();
        if !present {
            missing.push(label);
        }
        line(&mut out, format!("  [{}] {label:<13} {purpose}", mark(present)));
    }
    if !missing.is_empty() {
        ready = false;
        fixes.push(format!(
            "the sysroot is missing {}; rebuild it:\n    {BUILD_CMD}",
            missing.join(", ")
        ));
    }
    line(&mut out, String::new());

    // -- toolchain --------------------------------------------------------
    line(&mut out, "rust toolchain (the compiler is a rustc driver)".to_string());
    if compiler_present {
        if verbose {
            line(&mut out, format!("      $ {} --version", compiler.display()));
        }
        match engine::capture_either(&compiler, &["--version"]) {
            Ok(v) => line(&mut out, format!("  [x] {COMPILER} starts: {}", first_line(&v))),
            Err(e) => {
                ready = false;
                line(&mut out, format!("  [ ] {COMPILER} cannot start: {}", first_line(&e)));
                fixes.push(toolchain_fix(&engine));
            }
        }
    } else {
        line(&mut out, format!("  [ ] {COMPILER} missing (see above)"));
    }
    let toolchain_file = engine.sysroot.join("rust-toolchain-version");
    if let Ok(toolchain) = fs::read_to_string(&toolchain_file) {
        let toolchain = toolchain.trim();
        let link = engine.sysroot.join("toolchain");
        line(
            &mut out,
            format!(
                "  [{}] bundle toolchain {toolchain} linked at {}",
                mark(link.join("bin").join("cargo").exists()),
                link.display()
            ),
        );
    }
    line(&mut out, String::new());

    // -- solver -----------------------------------------------------------
    finish_solver(
        &mut out,
        Some(&engine),
        authority.as_ref(),
        &mut ready,
        &mut fixes,
        &mut warnings,
        verbose,
    );
    finish(out, ready, fixes, warnings)
}

fn finish_solver(
    out: &mut String,
    engine: Option<&Engine>,
    authority: Option<&engine::Authority>,
    ready: &mut bool,
    fixes: &mut Vec<String>,
    warnings: &mut Vec<String>,
    verbose: bool,
) {
    out.push_str("SMT solver (bounded runs shell out to it; CHC solves in-process)\n");
    match solver_path(engine) {
        None => {
            *ready = false;
            out.push_str("  [ ] ay  not on PATH\n");
            fixes.push(format!("put the solver on PATH:\n    {}", solver_hint()));
        }
        Some(ay) => {
            out.push_str(&format!("  [x] ay  {}\n", ay.display()));
            if verbose {
                out.push_str(&format!("      $ {} --version\n", ay.display()));
            }
            match solver_version(&ay) {
                None => out.push_str("  [!] ay does not answer --version\n"),
                Some(version) => {
                    out.push_str(&format!("      {version}\n"));
                    if let Some(pin) = authority.map(|a| a.ay_pin.as_str()) {
                        match solver_build_sha(&version) {
                            Some(sha) if sha == pin => out.push_str(
                                "  [x] the binary is the same AY commit the engine links\n",
                            ),
                            Some(sha) => {
                                out.push_str(&format!(
                                    "  [!] the binary is AY {} but the engine links {}\n",
                                    short(&sha),
                                    short(pin)
                                ));
                                warnings.push(format!(
                                    "`ay` on PATH ({}) is not the commit the engine links ({});\n  \
                                     bounded (BMC) verdicts come from that binary, so rebuild it at the\n  \
                                     pinned commit: cd ../ay && git checkout {} && cargo build --release -p ay --features cli",
                                    short(&sha),
                                    short(pin),
                                    pin
                                ));
                            }
                            None => out.push_str(
                                "  [!] the binary does not stamp its commit; cannot compare with the engine\n",
                            ),
                        }
                    }
                }
            }
        }
    }
    out.push('\n');
}

fn finish(mut out: String, ready: bool, fixes: Vec<String>, warnings: Vec<String>) -> Report {
    for w in &warnings {
        out.push_str(&format!("warning: {w}\n\n"));
    }
    if ready {
        out.push_str("ready. Try:\n\n    trust-mc example > demo.rs\n    trust-mc demo.rs\n");
    } else {
        out.push_str("not ready. To fix:\n\n");
        for fix in &fixes {
            out.push_str(&format!("  {fix}\n\n"));
        }
    }
    Report { text: out, ready, fixes, warnings }
}

impl Report {
    /// Render the report as JSON for CI.
    ///
    /// Only fields doctor already holds as DATA are emitted -- readiness, the
    /// exit code it will use, the resolved engine and solver, and the fix and
    /// warning lists. The human report's check lines are deliberately not
    /// scraped back out of `text`: a parser over our own output would be one
    /// formatting change away from lying, and the exit code is what a script
    /// actually gates on.
    fn to_json(&self) -> String {
        let engine = resolve_engine();
        let solver = solver_path(engine.as_ref());
        let mut s = String::from("{\n");
        let _ = writeln!(s, "  \"ready\": {},", self.ready);
        let _ = writeln!(s, "  \"exit_code\": {},", if self.ready { 0 } else { EXIT_NOT_READY });
        let _ = writeln!(s, "  \"version\": {},", json_string(VERSION));
        let _ = writeln!(s, "  \"target\": {},", json_string(TARGET));
        match &engine {
            Some(e) => {
                let _ = writeln!(s, "  \"engine\": {},", json_string(&e.driver.display().to_string()));
                let _ = writeln!(s, "  \"engine_source\": {},", json_string(e.source));
            }
            None => {
                s.push_str("  \"engine\": null,\n  \"engine_source\": null,\n");
            }
        }
        match &solver {
            Some(p) => {
                let _ = writeln!(s, "  \"solver\": {},", json_string(&p.display().to_string()));
            }
            None => s.push_str("  \"solver\": null,\n"),
        }
        let _ = writeln!(s, "  \"warnings\": {},", json_array(&self.warnings));
        let _ = writeln!(s, "  \"fixes\": {}", json_array(&self.fixes));
        s.push_str("}\n");
        s
    }
}

/// Minimal JSON string escaping -- doctor emits paths and prose, so quotes,
/// backslashes and newlines are the cases that actually occur.
fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_array(items: &[String]) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let rendered: Vec<String> = items.iter().map(|i| json_string(i)).collect();
    format!("[{}]", rendered.join(", "))
}

/// The fix when the compiler binary cannot load the rustc it was linked
/// against: name the pinned channel when we can find it.
fn toolchain_fix(engine: &Engine) -> String {
    let channel = engine
        .sysroot
        .parent()
        .and_then(Path::parent)
        .map(|repo| repo.join("rust-toolchain.toml"))
        .and_then(|p| fs::read_to_string(p).ok())
        .and_then(|text| pinned_channel(&text));
    match channel {
        Some(channel) => format!(
            "{COMPILER} cannot load its rustc; reinstall the pinned toolchain and rebuild:\n    \
             rustup toolchain install {channel} --component rustc-dev rust-src llvm-tools\n    \
             {BUILD_CMD}"
        ),
        None => format!(
            "{COMPILER} cannot load its rustc (the toolchain it was linked against is gone);\n  \
             rebuild it:\n    {BUILD_CMD}"
        ),
    }
}

/// `channel = "nightly-2025-12-03"` from a `rust-toolchain.toml`.
pub(crate) fn pinned_channel(toml: &str) -> Option<String> {
    toml.lines()
        .map(str::trim)
        .filter(|l| !l.starts_with('#'))
        .find_map(|l| l.strip_prefix("channel"))
        .and_then(|rest| rest.trim_start().strip_prefix('='))
        .map(|rest| rest.trim().trim_matches('"').to_string())
        .filter(|c| !c.is_empty())
}

fn short(sha: &str) -> &str {
    if sha.len() >= 12 { &sha[..12] } else { sha }
}

fn first_line(text: &str) -> &str {
    text.lines().next().unwrap_or("").trim()
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn the_pinned_channel_is_read_past_comments() {
        let toml = "# channel = \"trust\"\n#   channel = \"old\"\n[toolchain]\nchannel = \"nightly-2025-12-03\"\ncomponents = [\"rustc-dev\"]\n";
        assert_eq!(pinned_channel(toml).as_deref(), Some("nightly-2025-12-03"));
        assert_eq!(pinned_channel("[toolchain]\n"), None);
    }

    #[test]
    fn doctor_never_panics_and_names_the_three_sections() {
        // Whatever this machine has, the report must render.
        let report = examine(false);
        assert!(report.text.contains("verification engine"));
        assert!(report.text.contains("SMT solver"));
        assert!(report.text.contains("ready") || report.text.contains("not ready"));
    }

    #[test]
    fn doctor_and_version_reject_stray_arguments() {
        // `--json` used to stand in for "a flag doctor does not take"; it is a
        // real flag now, so the stray-argument case needs one that still is.
        let err = command(&[OsString::from("--nope")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        let err = command(&[OsString::from("extra")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        let err = version_command(&[OsString::from("extra")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
    }
}
