// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The `trust-mc` front door.
//!
//! This module is a **wrapper**. It contains no verification logic whatsoever:
//! every real action is performed by `trust-mc-driver` (the engine), which this
//! module locates, sanity-checks, and `exec`s with a translated argument list.
//! The three things it adds over the old ten-line proxy are:
//!
//! 1. `--version`, `--help`, `example` and `doctor` answer with **nothing
//!    installed** — no sysroot, no solver, no network. The old proxy resolved
//!    `${KANI_HOME:-~/.kani}/kani-<VERSION>` on every invocation, so even
//!    `--version` failed on a fresh machine.
//! 2. A zero-setup single-file path: `trust-mc example > demo.rs && trust-mc demo.rs`.
//! 3. Actionable diagnostics. A missing engine, an incomplete library sysroot,
//!    or a missing `ay` solver each print exactly what is absent and the exact
//!    command that fixes it, instead of a loader error or a clap backtrace.
//!
//! Flag names, output shape, and exit codes are deliberately familiar to people
//! coming from the academic bounded-model-checking tools for Rust; the mapping
//! onto the engine's real flags lives in [`translate`].

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::{env, fs};

use crate::setup;

/// Comes from our Cargo.toml manifest file.
const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The engine binary this front door drives. Everything real happens there.
const DRIVER: &str = "trust-mc-driver";

/// The exact command that builds the engine plus its library sysroot in place.
const BUILD_CMD: &str = "cargo run --release -p build-trust-mc -- build-dev --release";

/// Exit code for a usage error (bad or unsupported flag, missing input).
const EXIT_USAGE: u8 = 2;
/// Exit code for "the machine isn't ready" (engine, sysroot or solver missing).
const EXIT_NOT_READY: u8 = 3;

/// Subcommands that belong to the engine and are forwarded verbatim.
const ENGINE_SUBCOMMANDS: &[&str] = &["list", "autoharness", "playback", "verify-std"];

/// Flags we deliberately refuse, with the alternative to offer instead.
///
/// These are all flags a user of the comparable academic tool has muscle memory
/// for, and which trust-mc cannot honor because it solves with AY rather than a
/// CBMC/goto pipeline. Rejecting them here (loudly, by name, with the
/// replacement) beats the engine's drop-in behavior of warning and continuing:
/// a flag that silently does nothing is a wrong answer waiting to happen. The
/// engine keeps its permissive shims for `cargo-trust-mc` drop-in scripts.
const UNSUPPORTED: &[(&str, &str)] = &[
    (
        "--cbmc-args",
        "trust-mc has no CBMC backend, so there is nothing to pass CBMC arguments to.\n       \
         Tune the AY backend instead: --unwind <N>, --solver ay, or the engine's --ay-chc* flags.",
    ),
    (
        "--solver-args",
        "trust-mc has no CBMC backend. Tune the AY backend with --solver / the engine's --ay-* flags.",
    ),
    (
        "--gen-c",
        "trust-mc has no C code generator (that is a CBMC-pipeline feature). Drop the flag.",
    ),
    ("--print-llbc", "trust-mc has no Lean/LLBC backend. Drop the flag."),
    ("--write-json-symtab", "obsolete: trust-mc has no CBMC symbol table. Drop the flag."),
    (
        "--synthesize-loop-contracts",
        "trust-mc synthesizes loop invariants itself (PDR) and needs no CBMC loop-contract pass.\n       \
         Drop the flag, or bound the loops explicitly with --unwind <N>.",
    ),
    (
        "--no-slice-formula",
        "CBMC-only formula slicing; trust-mc builds no CBMC formula. Drop the flag.",
    ),
    (
        "--run-sanity-checks",
        "CBMC-only goto-program sanity checks; trust-mc builds no goto program. Drop the flag.",
    ),
    (
        "--visualize",
        "removed: use --coverage for coverage output, or --output-format terse for compact results.",
    ),
    (
        "--enable-unstable",
        "obsolete: enable one named feature with `-Z <feature>`, e.g. `-Z function-contracts`.",
    ),
    ("--dry-run", "obsolete: use --verbose to see the commands trust-mc runs."),
];

/// A front-door failure: a message already formatted for the user, and the exit
/// code to leave with.
#[derive(Debug)]
struct Fail {
    msg: String,
    code: u8,
}

impl Fail {
    fn usage(msg: impl Into<String>) -> Self {
        Fail { msg: msg.into(), code: EXIT_USAGE }
    }

    fn not_ready(msg: impl Into<String>) -> Self {
        Fail { msg: msg.into(), code: EXIT_NOT_READY }
    }
}

type Front<T> = Result<T, Fail>;

/// Entry point for the `trust-mc` binary.
pub fn front_door() -> ExitCode {
    let argv: Vec<OsString> = env::args_os().skip(1).collect();
    match run(&argv) {
        Ok(code) => code,
        Err(fail) => {
            eprintln!("{}", fail.msg);
            ExitCode::from(fail.code)
        }
    }
}

fn run(argv: &[OsString]) -> Front<ExitCode> {
    let first = argv.first().and_then(|a| a.to_str());
    let engine_sub = first.is_some_and(|s| ENGINE_SUBCOMMANDS.contains(&s));

    // `--help` / `--version` are answered here, before anything touches the
    // filesystem, so they work on a machine with no sysroot and no solver.
    // After an engine subcommand they belong to the engine's own parser.
    if !engine_sub {
        if argv.iter().any(|a| a == "--help" || a == "-h") || first == Some("help") {
            print!("{}", help_text());
            return Ok(ExitCode::SUCCESS);
        }
        if argv.iter().any(|a| a == "--version" || a == "-V") {
            println!("trust-mc {VERSION}");
            return Ok(ExitCode::SUCCESS);
        }
    }

    match first {
        None => Err(Fail::usage(format!(
            "error: no input file\n\n{}Try this, right now, with nothing else installed:\n\
             \n    trust-mc example > demo.rs\n    trust-mc demo.rs\n\n\
             `trust-mc --help` lists every option.",
            usage_lines()
        ))),
        Some("example") => write_example(&argv[1..]),
        Some("doctor") => Ok(doctor()),
        Some("setup") => run_setup(),
        Some(_) if engine_sub => {
            // `list` enumerates metadata and never calls the solver.
            let needs_solver = first != Some("list");
            let verbose = argv.iter().any(|a| a == "--verbose" || a == "-v" || a == "--debug");
            drive(argv.to_vec(), needs_solver, verbose)
        }
        Some(_) => {
            let plan = translate(argv)?;
            drive(plan.args, plan.needs_solver, plan.verbose)
        }
    }
}

// ---------------------------------------------------------------------------
// Argument translation
// ---------------------------------------------------------------------------

/// The translated engine invocation.
#[derive(Debug)]
struct Plan {
    /// Arguments for `trust-mc-driver`, input file first.
    args: Vec<OsString>,
    /// Whether this run will need the `ay` solver binary.
    needs_solver: bool,
    /// Whether the user asked for verbose output (we echo the engine command).
    verbose: bool,
}

/// Map the front door's familiar flag spellings onto the engine's real flags.
///
/// Everything not named here is forwarded unchanged, so the whole
/// `trust-mc-driver` surface (`-Z` features, `--output-format`, `--coverage`,
/// `--concrete-playback`, the `--ay-chc*` family, ...) stays reachable.
fn translate(argv: &[OsString]) -> Front<Plan> {
    let mut out: Vec<OsString> = Vec::new();
    let mut input: Option<OsString> = None;
    let mut harness_seen = false;
    let mut list_mode = false;
    let mut verbose = false;
    let mut unwind: Option<OsString> = None;

    let mut idx = 0;
    while idx < argv.len() {
        let raw = &argv[idx];
        idx += 1;

        let Some(text) = raw.to_str() else {
            // Not UTF-8: it can only be a path or an opaque value. Preserve it.
            if input.is_none() && Path::new(raw).extension().is_some_and(|e| e == "rs") {
                input = Some(raw.clone());
            } else {
                out.push(raw.clone());
            }
            continue;
        };

        if text == "--" {
            out.extend_from_slice(&argv[idx..]);
            break;
        }

        let (name, attached) = match text.split_once('=') {
            Some((n, v)) if n.starts_with('-') => (n, Some(OsString::from(v))),
            _ => (text, None),
        };

        if let Some((flag, why)) = UNSUPPORTED.iter().find(|(f, _)| *f == name) {
            return Err(Fail::usage(format!(
                "error: {flag} is not supported by trust-mc\n       {why}"
            )));
        }

        match name {
            "--harness" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                harness_seen = true;
                out.push(OsString::from("--harness"));
                out.push(value);
            }
            "--list" | "--harnesses" => list_mode = true,
            "--unwind" => unwind = Some(take_value(name, attached, argv, &mut idx)?),
            "--solver" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                out.push(OsString::from("--smt-solver"));
                out.push(check_solver(&value)?);
            }
            "--verbose" | "-v" => {
                verbose = true;
                out.push(OsString::from("--verbose"));
            }
            "--debug" => {
                verbose = true;
                out.push(raw.clone());
            }
            "--quiet" | "-q" => out.push(OsString::from("--quiet")),
            _ if !text.starts_with('-')
                && input.is_none()
                && Path::new(text).extension().is_some_and(|e| e == "rs") =>
            {
                input = Some(raw.clone());
            }
            // Unrecognized: hand it to the engine untouched, along with any
            // value it carries. The engine's parser is the authority on it.
            _ => out.push(raw.clone()),
        }
    }

    if list_mode {
        out.push(OsString::from("--harnesses"));
    }

    if let Some(bound) = unwind {
        // The engine's `--unwind` is per-harness and *requires* `--harness`;
        // its crate-wide bound is `--default-unwind`. Pick the one that fits so
        // a bare `--unwind 5` does not die on a missing-required-argument error.
        out.push(OsString::from(if harness_seen { "--unwind" } else { "--default-unwind" }));
        out.push(bound);
    }

    let Some(input) = input else {
        return Err(Fail::usage(format!(
            "error: no input file\n\n{}The input must be a path ending in `.rs`. To get one:\n\
             \n    trust-mc example > demo.rs\n    trust-mc demo.rs\n\n\
             To verify a Cargo package instead, use `cargo trust-mc`.",
            usage_lines()
        )));
    };

    let path = PathBuf::from(&input);
    if !path.is_file() {
        return Err(Fail::usage(format!(
            "error: no such file: {}\n       \
             trust-mc verifies one Rust source file. To get a sample you can run right now:\n\
             \n    trust-mc example > demo.rs\n    trust-mc demo.rs",
            path.display()
        )));
    }

    let mut args = vec![input];
    args.extend(out);
    Ok(Plan { args, needs_solver: !list_mode, verbose })
}

/// Pull the value of a flag, either from `--flag=value` or the next argument.
fn take_value(
    name: &str,
    attached: Option<OsString>,
    argv: &[OsString],
    idx: &mut usize,
) -> Front<OsString> {
    if let Some(value) = attached {
        return Ok(value);
    }
    if let Some(value) = argv.get(*idx) {
        *idx += 1;
        return Ok(value.clone());
    }
    Err(Fail::usage(format!("error: {name} needs a value, e.g. `{name} <VALUE>`")))
}

/// Solver names the AY backend understands. `direct` is a build-time feature of
/// the engine; we forward it and let the engine be the authority on whether it
/// was compiled in.
const SOLVERS: &[&str] = &["auto", "ay", "direct"];

fn check_solver(value: &OsString) -> Front<OsString> {
    let text = value.to_string_lossy().to_lowercase();
    if SOLVERS.contains(&text.as_str()) {
        return Ok(OsString::from(text));
    }
    Err(Fail::usage(format!(
        "error: --solver {}: not a trust-mc solver\n       \
         trust-mc discharges obligations with the AY solver; it has no CBMC SAT-solver\n       \
         selection, so names like `cadical`, `kissat`, `minisat`, `z3` or `bin=<PATH>`\n       \
         have no meaning here.\n       \
         Use `--solver ay`, or `--solver auto` (the default).",
        value.to_string_lossy()
    )))
}

// ---------------------------------------------------------------------------
// Engine discovery
// ---------------------------------------------------------------------------

/// A located engine: the sysroot that holds it and the driver binary itself.
struct Engine {
    sysroot: PathBuf,
    driver: PathBuf,
    source: &'static str,
}

/// One place the engine may live.
struct Candidate {
    source: &'static str,
    /// The sysroot to use, when we can name one.
    sysroot: Option<PathBuf>,
    /// Always printable, even when nothing is configured.
    display: String,
}

impl Candidate {
    fn driver(&self) -> Option<PathBuf> {
        self.sysroot.as_ref().map(|s| s.join("bin").join(DRIVER))
    }

    fn found(&self) -> bool {
        self.driver().is_some_and(|d| d.is_file())
    }
}

/// Where the engine may live, in resolution order.
fn candidates() -> Vec<Candidate> {
    let env_sysroot = env::var_os("TRUST_MC_SYSROOT").map(PathBuf::from);
    let env_display = env_sysroot.as_ref().map_or_else(
        || "$TRUST_MC_SYSROOT is not set".to_string(),
        |dir| format!("{}/bin/{DRIVER}", dir.display()),
    );

    // When no local build exists yet, still name where one would go, so the
    // build command we print lands somewhere the reader can see.
    let dev = dev_sysroot();
    let dev_display = dev
        .clone()
        .or_else(|| env::current_dir().ok().map(|cwd| cwd.join("target").join("trust-mc")));

    let bundle = setup::kani_dir().ok();
    let bundle_display = bundle.as_ref().map_or_else(
        || format!("${{KANI_HOME:-~/.kani}}/kani-{VERSION}/bin/{DRIVER}"),
        |dir| format!("{}/bin/{DRIVER}", dir.display()),
    );

    vec![
        Candidate { source: "TRUST_MC_SYSROOT", sysroot: env_sysroot, display: env_display },
        Candidate {
            source: "local build",
            sysroot: dev,
            display: dev_display.map_or_else(
                || format!("<repo>/target/trust-mc/bin/{DRIVER}"),
                |dir| format!("{}/bin/{DRIVER}", dir.display()),
            ),
        },
        Candidate { source: "release bundle", sysroot: bundle, display: bundle_display },
    ]
}

/// A sysroot produced by `build-trust-mc build-dev`, at `<repo>/target/trust-mc`.
///
/// Searched from the working directory upwards, then from the directory holding
/// this executable upwards, so both `trust-mc demo.rs` inside a checkout and
/// `target/release/trust-mc demo.rs` from anywhere find the build you just made.
fn dev_sysroot() -> Option<PathBuf> {
    let mut roots: Vec<PathBuf> = Vec::new();
    if let Ok(cwd) = env::current_dir() {
        roots.extend(cwd.ancestors().map(Path::to_path_buf));
    }
    if let Ok(exe) = env::current_exe() {
        if let Some(dir) = exe.parent() {
            roots.extend(dir.ancestors().map(Path::to_path_buf));
        }
    }
    roots
        .into_iter()
        .map(|root| root.join("target").join("trust-mc"))
        .find(|sysroot| sysroot.join("bin").join(DRIVER).is_file())
}

fn resolve_engine() -> Option<Engine> {
    for candidate in candidates() {
        if candidate.found() {
            let driver = candidate.driver()?;
            return Some(Engine { sysroot: candidate.sysroot?, driver, source: candidate.source });
        }
    }
    None
}

/// The library sysroot directories the engine fails closed without.
fn library_dirs(sysroot: &Path) -> [(&'static str, PathBuf); 3] {
    [
        ("lib", sysroot.join("lib")),
        ("no_core/lib", sysroot.join("no_core").join("lib")),
        ("playback/lib", sysroot.join("playback").join("lib")),
    ]
}

/// Is `name` runnable from `PATH` (or from an extra directory we prepend)?
fn find_on_path(name: &str, extra: &[PathBuf]) -> Option<PathBuf> {
    let mut dirs: Vec<PathBuf> = extra.to_vec();
    if let Some(path) = env::var_os("PATH") {
        dirs.extend(env::split_paths(&path));
    }
    dirs.into_iter().map(|dir| dir.join(name)).find(|candidate| is_executable(candidate))
}

fn is_executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

/// A sibling `ay` checkout whose solver binary is already built, if there is one.
fn nearby_ay_binary() -> Option<PathBuf> {
    let cwd = env::current_dir().ok()?;
    for ancestor in cwd.ancestors() {
        for profile in ["release", "debug"] {
            let candidate = ancestor.join("ay").join("target").join(profile).join("ay");
            if is_executable(&candidate) {
                return Some(candidate);
            }
        }
    }
    None
}

fn solver_hint() -> String {
    match nearby_ay_binary() {
        Some(binary) => {
            let dir = binary.parent().map(Path::to_path_buf).unwrap_or_default();
            format!("export PATH=\"{}:$PATH\"", dir.display())
        }
        None => "build the AY solver in your `ay` checkout (`cargo build --release`),\n    \
                 then put its `target/release` directory on PATH"
            .to_string(),
    }
}

// ---------------------------------------------------------------------------
// Running the engine
// ---------------------------------------------------------------------------

/// Check the environment, then hand off to the engine.
fn drive(args: Vec<OsString>, needs_solver: bool, verbose: bool) -> Front<ExitCode> {
    let Some(engine) = resolve_engine() else {
        return Err(Fail::not_ready(engine_missing_report()));
    };

    let missing: Vec<&str> = library_dirs(&engine.sysroot)
        .iter()
        .filter(|(_, dir)| !dir.is_dir())
        .map(|(label, _)| *label)
        .collect();
    if !missing.is_empty() {
        return Err(Fail::not_ready(format!(
            "error: the trust-mc library sysroot is incomplete\n\n  \
             found the engine:   {}\n  \
             but missing:        {}\n\n\
             The engine fails closed without its pre-compiled libraries. Rebuild them with:\n\n    \
             {BUILD_CMD}\n",
            engine.driver.display(),
            missing.join(", ")
        )));
    }

    let bin_dir = engine.sysroot.join("bin");
    if needs_solver && find_on_path("ay", std::slice::from_ref(&bin_dir)).is_none() {
        return Err(Fail::not_ready(format!(
            "error: the `ay` SMT solver is not on PATH\n\n\
             trust-mc discharges every proof obligation with AY; without it the engine\n\
             exits immediately on every harness. `trust-mc --version`, `--help`,\n\
             `example`, `doctor` and `trust-mc list <FILE.rs>` do not need it.\n\n\
             To fix:\n\n    {}\n",
            solver_hint()
        )));
    }

    exec_engine(&engine, &args, verbose)
}

/// `exec` the engine with our environment fixups, and adopt its exit code.
fn exec_engine(engine: &Engine, args: &[OsString], verbose: bool) -> Front<ExitCode> {
    let bin_dir = engine.sysroot.join("bin");
    let pyroot = engine.sysroot.join("pyroot");

    // Same environment preparation the historical proxy did: let the bundle's
    // own binaries and python packages win, and strip rustup's toolchain
    // library paths so the engine loads the rustc it was linked against.
    let pythonpath =
        crate::prepend_search_path(std::slice::from_ref(&pyroot), env::var_os("PYTHONPATH"))
            .map_err(|e| Fail { msg: format!("error: {e}"), code: 1 })?;
    let path = crate::prepend_search_path(&[bin_dir, pyroot.join("bin")], env::var_os("PATH"))
        .map_err(|e| Fail { msg: format!("error: {e}"), code: 1 })?;
    crate::fixup_dynamic_linking_environment();

    // Release bundles record the toolchain they link against; local builds do
    // not ship that file and must keep the caller's toolchain selection.
    let version_file = engine.sysroot.join("rust-toolchain-version");
    if let Ok(toolchain) = fs::read_to_string(&version_file) {
        crate::set_process_env_var("RUSTUP_TOOLCHAIN", toolchain.trim());
    }

    if verbose {
        eprintln!("[trust-mc] engine ({}): {}", engine.source, engine.driver.display());
        eprintln!(
            "[trust-mc] running: {} {}",
            DRIVER,
            args.iter().map(|a| a.to_string_lossy().into_owned()).collect::<Vec<_>>().join(" ")
        );
    }

    let mut cmd = Command::new(&engine.driver);
    cmd.args(args).env("PYTHONPATH", pythonpath).env("PATH", path);
    // The engine reads its invocation identity from argv[0].
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        cmd.arg0("trust-mc");
    }

    match cmd.status() {
        Ok(status) => Ok(status
            .code()
            .and_then(|c| u8::try_from(c).ok())
            .map_or(ExitCode::FAILURE, ExitCode::from)),
        Err(e) => Err(Fail {
            msg: format!(
                "error: could not run the verification engine\n  {}\n  {e}",
                engine.driver.display()
            ),
            code: EXIT_NOT_READY,
        }),
    }
}

fn run_setup() -> Front<ExitCode> {
    crate::proxy("trust-mc")
        .map(|()| ExitCode::SUCCESS)
        .map_err(|e| Fail { msg: format!("error: {e:#}"), code: 1 })
}

// ---------------------------------------------------------------------------
// Reports
// ---------------------------------------------------------------------------

fn engine_missing_report() -> String {
    let mut report = format!(
        "error: the trust-mc verification engine is not installed\n\n  \
         looked for `{DRIVER}`, in order:\n"
    );
    for candidate in candidates() {
        report.push_str(&format!(
            "    [{}] {}  ({})\n",
            mark(candidate.found()),
            candidate.display,
            candidate.source
        ));
    }
    report.push_str(&format!(
        "\n  `trust-mc --version`, `--help`, `example` and `doctor` work without it;\n  \
         verification needs the engine and its pre-compiled library sysroot.\n\n  \
         To build both from this repository (no network):\n\n      {BUILD_CMD}\n\n  \
         Or install a published release bundle:\n\n      trust-mc setup\n"
    ));
    report
}

/// Report what verification needs and whether it is here. Exits 0 when ready.
fn doctor() -> ExitCode {
    let mut ready = true;
    println!("trust-mc {VERSION}\n");

    println!("verification engine");
    let engine = resolve_engine();
    for candidate in candidates() {
        println!("  [{}] {}  ({})", mark(candidate.found()), candidate.display, candidate.source);
    }

    match &engine {
        Some(engine) => {
            println!("  using: {} ({})\n", engine.driver.display(), engine.source);
            println!("library sysroot");
            for (label, dir) in library_dirs(&engine.sysroot) {
                let present = dir.is_dir();
                ready &= present;
                println!("  [{}] {label:<13} {}", mark(present), dir.display());
            }
            println!();
        }
        None => {
            ready = false;
            println!("  using: none found\n");
        }
    }

    println!("SMT solver");
    let extra = engine.as_ref().map(|e| vec![e.sysroot.join("bin")]).unwrap_or_default();
    match find_on_path("ay", &extra) {
        Some(path) => println!("  [x] ay  {}", path.display()),
        None => {
            ready = false;
            println!("  [ ] ay  not on PATH");
        }
    }
    println!();

    if ready {
        println!("ready. Try:\n\n    trust-mc example > demo.rs\n    trust-mc demo.rs");
        ExitCode::SUCCESS
    } else {
        println!("not ready. To fix:\n");
        if engine.is_none() {
            println!("  build the engine and sysroot:\n    {BUILD_CMD}\n");
            println!("  ...or install a release bundle:\n    trust-mc setup\n");
        }
        println!("  put the solver on PATH:\n    {}", solver_hint());
        ExitCode::from(EXIT_NOT_READY)
    }
}

fn mark(present: bool) -> char {
    if present { 'x' } else { ' ' }
}

// ---------------------------------------------------------------------------
// The sample harness
// ---------------------------------------------------------------------------

/// A tiny, genuinely verifiable sample. Two loop-free harnesses so a first run
/// succeeds with no unwind bound, and two of them so `--harness` and `--list`
/// have something to select between.
const EXAMPLE: &str = r#"// A trust-mc sample. Verify every harness in this file with:
//
//     trust-mc demo.rs
//
// Then try:
//
//     trust-mc --list demo.rs                        # which harnesses are here?
//     trust-mc --harness double_never_shrinks demo.rs
//     trust-mc --unwind 4 demo.rs                    # bound loop unwinding
//     trust-mc --verbose demo.rs                     # show every stage
//
// `kani::any()` yields an unconstrained symbolic value, so each assertion below
// is proved for EVERY input, not sampled at a few of them.

fn double(x: u32) -> u32 {
    x.checked_mul(2).unwrap_or(u32::MAX)
}

#[kani::proof]
fn double_never_shrinks() {
    let x: u32 = kani::any();
    assert!(double(x) >= x);
}

#[kani::proof]
fn saturating_sub_is_bounded() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    assert!(a.saturating_sub(b) <= a);
}
"#;

fn write_example(rest: &[OsString]) -> Front<ExitCode> {
    let mut target: Option<&OsString> = None;
    for arg in rest {
        let text = arg.to_string_lossy();
        if text.starts_with('-') {
            return Err(Fail::usage(format!(
                "error: `example` takes no options, got {text}\n       \
                 Usage: trust-mc example [PATH]   (writes to stdout when PATH is omitted)"
            )));
        }
        if target.is_some() {
            return Err(Fail::usage(
                "error: `example` writes one file\n       Usage: trust-mc example [PATH]",
            ));
        }
        target = Some(arg);
    }

    match target {
        None => {
            print!("{EXAMPLE}");
            Ok(ExitCode::SUCCESS)
        }
        Some(path) => {
            let path = PathBuf::from(path);
            if path.exists() {
                return Err(Fail::usage(format!(
                    "error: {} already exists; refusing to overwrite it",
                    path.display()
                )));
            }
            fs::write(&path, EXAMPLE).map_err(|e| Fail {
                msg: format!("error: could not write {}: {e}", path.display()),
                code: 1,
            })?;
            println!(
                "wrote {}\n\nVerify it with:\n\n    trust-mc {}",
                path.display(),
                path.display()
            );
            Ok(ExitCode::SUCCESS)
        }
    }
}

// ---------------------------------------------------------------------------
// Help
// ---------------------------------------------------------------------------

fn usage_lines() -> String {
    "Usage:\n    trust-mc [OPTIONS] <FILE.rs>\n    trust-mc <COMMAND> [ARGS...]\n\n".to_string()
}

fn help_text() -> String {
    format!(
        "trust-mc {VERSION} — bounded model checking for Rust

Proves the assertions in a Rust source file for every possible input, rather
than testing a few of them.

{usage}First run — no project, no configuration, no network:

    trust-mc example > demo.rs
    trust-mc demo.rs

Commands:
    example [PATH]      write a small, verifiable sample harness (stdout by default)
    doctor              report what verification needs and whether it is present
    setup               install a published release bundle into ${{KANI_HOME:-~/.kani}}
    list | autoharness | playback | verify-std
                        forwarded verbatim to the verification engine

Options:
    --harness <NAME>    verify only harnesses matching NAME; repeatable
    --list              list the harnesses in FILE instead of verifying them
    --unwind <N>        bound loop unwinding. On its own this is the crate-wide
                        bound (engine flag --default-unwind); together with
                        --harness it bounds that harness (engine flag --unwind)
    --solver <NAME>     SMT solver for the AY backend: auto (default) or ay
    -v, --verbose       show each stage, and the engine command line
    -q, --quiet         print nothing but the exit code and requested artifacts
    -h, --help          print this message (works with nothing installed)
    -V, --version       print the version (works with nothing installed)
    --                  pass every remaining argument to the engine verbatim

Any other flag is forwarded to the engine unchanged, so its full surface
(-Z <feature>, --output-format, --coverage, --concrete-playback, --ay-chc, ...)
stays reachable. Flags that trust-mc genuinely cannot honor are rejected by
name, with the replacement to use. `trust-mc doctor` prints the engine's path;
run that binary with --help for its complete flag list.

Exit codes:
    0  verification succeeded          2  usage error
    1  verification failed             3  engine, sysroot or solver not installed

Flag names, output shape, and exit codes are deliberately familiar to users of
the Kani bounded model checker. trust-mc is a separate, independent tool: it is
not Kani, and it is not affiliated with or endorsed by that project.

To verify a Cargo package rather than a single file, use `cargo trust-mc`.
",
        usage = usage_lines()
    )
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<OsString> {
        list.iter().map(OsString::from).collect()
    }

    /// Translate without the "input must exist" check by pointing at this file.
    fn plan_for(list: &[&str]) -> Vec<String> {
        let plan = translate(&args(list)).expect("expected a valid plan");
        plan.args.iter().map(|a| a.to_string_lossy().into_owned()).collect()
    }

    /// A real `.rs` path that is guaranteed to exist while tests run.
    fn this_file() -> String {
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/frontend.rs").to_string()
    }

    #[test]
    fn bare_unwind_becomes_the_crate_wide_bound() {
        let file = this_file();
        let got = plan_for(&[&file, "--unwind", "5"]);
        assert_eq!(got, vec![file, "--default-unwind".to_string(), "5".to_string()]);
    }

    #[test]
    fn unwind_with_a_harness_stays_per_harness() {
        let file = this_file();
        let got = plan_for(&[&file, "--harness", "foo", "--unwind=5"]);
        assert_eq!(
            got,
            vec![
                file,
                "--harness".to_string(),
                "foo".to_string(),
                "--unwind".to_string(),
                "5".to_string(),
            ]
        );
    }

    #[test]
    fn list_maps_onto_the_engine_listing_shortcut() {
        let file = this_file();
        let plan = translate(&args(&[&file, "--list"])).unwrap();
        let got: Vec<String> = plan.args.iter().map(|a| a.to_string_lossy().into_owned()).collect();
        assert_eq!(got, vec![file, "--harnesses".to_string()]);
        assert!(!plan.needs_solver, "listing metadata must not require the solver");
    }

    #[test]
    fn solver_maps_onto_the_ay_selector() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--solver", "AY"]),
            vec![file, "--smt-solver".to_string(), "ay".to_string()]
        );
    }

    #[test]
    fn a_cbmc_solver_name_is_rejected_by_name() {
        let file = this_file();
        let err = translate(&args(&[&file, "--solver", "cadical"])).unwrap_err();
        assert_eq!(err.code, EXIT_USAGE);
        assert!(err.msg.contains("--solver cadical"), "{}", err.msg);
        assert!(err.msg.contains("--solver ay"), "{}", err.msg);
    }

    #[test]
    fn unsupported_flags_fail_loudly_with_an_alternative() {
        let file = this_file();
        for (flag, _) in UNSUPPORTED {
            let err = translate(&args(&[&file, flag])).unwrap_err();
            assert_eq!(err.code, EXIT_USAGE, "{flag}");
            assert!(err.msg.contains(flag), "{flag}: {}", err.msg);
        }
    }

    #[test]
    fn unknown_flags_and_their_values_pass_through_in_order() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--output-format", "terse", "-Z", "unstable-options"]),
            vec![
                file,
                "--output-format".to_string(),
                "terse".to_string(),
                "-Z".to_string(),
                "unstable-options".to_string(),
            ]
        );
    }

    #[test]
    fn double_dash_passes_the_remainder_verbatim() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--", "--cbmc-args", "--solver", "z3"]),
            vec![file, "--cbmc-args".to_string(), "--solver".to_string(), "z3".to_string(),]
        );
    }

    #[test]
    fn a_missing_input_is_a_usage_error_that_names_the_example_verb() {
        let err = translate(&args(&["--harness", "foo"])).unwrap_err();
        assert_eq!(err.code, EXIT_USAGE);
        assert!(err.msg.contains("trust-mc example"), "{}", err.msg);
    }

    #[test]
    fn a_nonexistent_input_names_the_file_and_the_way_out() {
        let err = translate(&args(&["definitely-not-here.rs"])).unwrap_err();
        assert_eq!(err.code, EXIT_USAGE);
        assert!(err.msg.contains("definitely-not-here.rs"), "{}", err.msg);
        assert!(err.msg.contains("trust-mc example"), "{}", err.msg);
    }

    #[test]
    fn help_and_version_need_no_filesystem() {
        assert!(help_text().contains("trust-mc example > demo.rs"));
        assert!(help_text().contains("Exit codes"));
    }

    #[test]
    fn the_example_is_a_pair_of_loop_free_harnesses() {
        assert_eq!(EXAMPLE.matches("#[kani::proof]").count(), 2);
        // A loop would need an unwind bound, and a first run passes no flags.
        let code: String = EXAMPLE
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        for loop_kw in ["for ", "while ", "loop {"] {
            assert!(!code.contains(loop_kw), "a first run must not need an unwind bound");
        }
    }
}
