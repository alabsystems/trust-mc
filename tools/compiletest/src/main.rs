// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Modifications Copyright Kani Contributors
// See GitHub history for details.

#![crate_name = "compiletest"]
// The `test` crate is the only unstable feature
// allowed here, just to share similar code.
#![feature(test)]
// Ported upstream Kani compiletest code uses fallible-value access patterns
// where panic is the intended error path. Suppressing clippy lints that fire
// across the entire crate of upstream code.
#![allow(
    clippy::unwrap_used,
    clippy::manual_assert,
    clippy::zombie_processes,
    clippy::implicit_clone,
    clippy::borrow_as_ptr,
    clippy::ptr_as_ptr,
    clippy::ref_as_ptr
)]

extern crate test;

use crate::common::{Config, Mode, TestPaths};
use crate::common::{output_base_dir, output_relative_path};
use crate::util::{logv, print_msg, top_level};
use getopts::Options;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::{Duration, SystemTime};
use test::ColorConfig;
use test::test::TestTimeOptions;
use tracing::*;
use walkdir::WalkDir;

use self::header::make_test_description;

pub mod common;
pub mod header;
mod json;
mod raise_fd_limit;
mod read2;
pub mod runtest;
pub mod util;

fn main() {
    tracing_subscriber::fmt::init();

    let config = parse_config(env::args().collect());

    log_config(&config);
    add_kani_to_path();
    run_tests(config);
}

/// THE single blessed env-mutation choke point for this harness: performs the
/// raw process-global `set_var` under a process-wide lock. Every env mutation
/// in this binary routes here. The three callers (`PATH`, `__COMPAT_LAYER`,
/// `TARGET`) set harness-startup values that must persist for the whole test
/// run and its child compiler/verifier processes, so the writes are
/// intentionally permanent. The lock serializes all mutation entrypoints, and
/// every caller runs before the test harness spawns worker threads. This is the
/// crate's one item-level `env_mutation` allow; `unknown_lints` keeps the
/// stock-rustc build green (the lint is defined only by the Trust toolchain).
#[allow(unknown_lints, env_mutation)]
fn set_process_env_var(key: &str, value: impl AsRef<std::ffi::OsStr>) {
    static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    // SAFETY: serialized by ENV_LOCK; harness startup runs single-threaded
    // before any test threads are spawned.
    unsafe {
        env::set_var(key, value);
    }
}

/// Adds Kani to the current `PATH` environment variable.
fn add_kani_to_path() {
    let cwd = env::current_dir().unwrap();
    let kani_bin = cwd.join("target").join("debug");
    let kani_scripts = cwd.join("scripts");
    set_process_env_var(
        "PATH",
        format!("{}:{}:{}", kani_scripts.display(), kani_bin.display(), env::var("PATH").unwrap()),
    );
}

pub fn parse_config(args: Vec<String>) -> Config {
    let mut opts = Options::new();
    opts
        .optopt("", "src-base", "directory to scan for test files", "PATH")
        .optopt("", "build-base", "directory to deposit test outputs", "PATH")
        .optopt(
            "",
            "mode",
            "which sort of compile tests to run",
            "run-pass-valgrind | pretty | debug-info | codegen | rustdoc \
            | rustdoc-json | codegen-units | incremental | run-make | ui | js-doc-test | mir-opt | assembly | trust_mc | cargo-trust_mc | expected",
        )
        .optopt(
            "",
            "suite",
            "which suite of compile tests to run. used for nicer error reporting.",
            "SUITE",
        )
        .optflag("", "exact", "filters match exactly")
        .optflag("", "verbose", "run tests verbosely, showing all output")
        .optflag("", "quiet", "print one character per test instead of one line")
        .optopt("", "color", "coloring: auto, always, never", "WHEN")
        .optopt("", "logfile", "file to log test execution to", "FILE")
        .optopt("", "target", "the target to build for", "TARGET")
        .optopt("", "host", "the host to build for", "HOST")
        .optflag("", "force-rerun", "rerun tests even if the inputs are unchanged")
        .optflag("h", "help", "show this message")
        .optopt("", "edition", "default Rust edition", "EDITION")
        .optopt("", "timeout", "the timeout for each test in seconds", "TIMEOUT")
        .optflag("", "no-fail-fast", "run all tests regardless of failure")
        .optflag("", "dry-run", "don't actually run the tests")
        .optflag("", "fix-expected",
        "override all expected files that did not match the output. Tests will NOT fail when there is a mismatch")
        .optflag("", "report-time",
                 "report the time of each test. Configuration is done via env variables, like \
                 rust unit tests.")
        .optmulti("", "trust_mc-flag",
                  "pass extra flags to trust_mc. Note that this may cause spurious failures if the \
                  passed flag conflicts with the test configuration. Only works for `trust_mc`, \
                  `cargo-trust_mc`, and `expected` modes."
                  , "ARG")
    ;

    let (argv0, args_) = args.split_first().unwrap();
    if args.len() == 1 || args[1] == "-h" || args[1] == "--help" {
        let message = format!("Usage: {argv0} [OPTIONS] [TESTNAME...]");
        println!("{}", opts.usage(&message));
        println!();
        std::process::exit(0);
    }

    let matches = &match opts.parse(args_) {
        Ok(m) => m,
        Err(f) => panic!("{f:?}"),
    };

    if matches.opt_present("h") || matches.opt_present("help") {
        let message = format!("Usage: {argv0} [OPTIONS]  [TESTNAME...]");
        println!("{}", opts.usage(&message));
        println!();
        std::process::exit(0);
    }

    fn opt_path(m: &getopts::Matches, nm: &str, default: &[&str]) -> PathBuf {
        match m.opt_str(nm) {
            Some(s) => PathBuf::from(&s),
            None => {
                let mut root_folder = top_level().unwrap_or_else(|| {
                    panic!("Cannot find root directory. Please provide --{nm} option.")
                });
                default.iter().for_each(|f| root_folder.push(f));
                root_folder
            }
        }
    }

    let target = opt_str2(matches.opt_str("target"));
    let color = match matches.opt_str("color").as_deref() {
        Some("auto") | None => ColorConfig::AutoColor,
        Some("always") => ColorConfig::AlwaysColor,
        Some("never") => ColorConfig::NeverColor,
        Some(x) => panic!("argument for --color must be auto, always, or never, but found `{x}`"),
    };

    let suite = matches.opt_str("suite").unwrap();
    let src_base = opt_path(matches, "src-base", &["tests", suite.as_str()]);
    let mode = matches.opt_str("mode").unwrap().parse().expect("invalid mode");
    let timeout = matches.opt_str("timeout").map(|val| {
        Duration::from_secs(u64::from_str(&val).unwrap_or_else(|_| {
            panic!("Unexpected timeout format. Expected a positive number but found {val}")
        }))
    });

    Config {
        src_base,
        build_base: opt_path(matches, "build-base", &["build", "tests", suite.as_str()]),
        mode,
        suite,
        filters: matches.free.clone(),
        filter_exact: matches.opt_present("exact"),
        logfile: matches.opt_str("logfile").map(|s| PathBuf::from(&s)),
        target,
        host: opt_str2(matches.opt_str("host")),
        verbose: matches.opt_present("verbose"),
        quiet: matches.opt_present("quiet"),
        color,
        edition: matches.opt_str("edition"),
        force_rerun: matches.opt_present("force-rerun"),
        fail_fast: !matches.opt_present("no-fail-fast"),
        dry_run: matches.opt_present("dry-run"),
        fix_expected: matches.opt_present("fix-expected"),
        timeout,
        time_opts: matches
            .opt_present("report-time")
            .then_some(TestTimeOptions::new_from_env(false)),
        extra_args: matches.opt_strs("trust_mc-flag"),
    }
}

pub fn log_config(config: &Config) {
    let c = config;
    logv(c, "configuration:".to_string());
    logv(c, format!("src_base: {:?}", config.src_base.display()));
    logv(c, format!("build_base: {:?}", config.build_base.display()));
    logv(c, format!("mode: {}", config.mode));
    logv(c, format!("filters: {:?}", config.filters));
    logv(c, format!("filter_exact: {}", config.filter_exact));
    logv(c, format!("target: {}", config.target));
    logv(c, format!("host: {}", config.host));
    logv(c, format!("verbose: {}", config.verbose));
    logv(c, format!("quiet: {}", config.quiet));
    logv(c, format!("timeout: {:?}", config.timeout));
    logv(c, format!("fail-fast: {:?}", config.fail_fast));
    logv(c, format!("dry-run: {:?}", config.dry_run));
    logv(c, format!("fix-expected: {:?}", config.fix_expected));
    logv(
        c,
        format!(
            "parallelism: RUST_TEST_THREADS={:?}, available_parallelism={}",
            env::var("RUST_TEST_THREADS").ok(),
            std::thread::available_parallelism().unwrap()
        ),
    );
    logv(c, "\n".to_string());
}

pub fn opt_str(maybestr: &Option<String>) -> &str {
    match *maybestr {
        None => "(none)",
        Some(ref s) => s,
    }
}

pub fn opt_str2(maybestr: Option<String>) -> String {
    match maybestr {
        None => "(none)".to_owned(),
        Some(s) => s,
    }
}

pub fn run_tests(config: Config) {
    // sadly osx needs some file descriptor limits raised for running tests in
    // parallel (especially when we have lots and lots of child processes).
    // For context, see #8904
    unsafe {
        raise_fd_limit::raise_fd_limit();
    }
    // Prevent issue #21352 UAC blocking .exe containing 'patch' etc. on Windows
    // If #11207 is resolved (adding manifest to .exe) this becomes unnecessary
    set_process_env_var("__COMPAT_LAYER", "RunAsInvoker");

    // Let tests know which target they're running as
    set_process_env_var("TARGET", &config.target);

    let opts = test_opts(&config);

    let configs = vec![config.clone()];

    let mut tests = Vec::new();
    for c in &configs {
        make_tests(c, &mut tests);
    }

    if config.dry_run {
        // libtest now takes a `TestList` (tests + a sortedness tag) rather than a
        // bare Vec: `filter_tests` uses binary search for `--exact` when the list
        // is known sorted. These tests come from `make_tests` above, not from
        // rustc's `--test` harness, so their order is NOT guaranteed and
        // `Unsorted` is the only sound tag -- claiming `Sorted` would let the
        // binary search miss tests. `filter_tests` still RETURNS a Vec, so the
        // uses below are unchanged.
        let tests = test::filter_tests(
            &opts,
            test::TestList::new(tests, test::TestListOrder::Unsorted),
        );
        print_msg(&config, format!("Number of Tests: {}", tests.len()));
        for test in tests {
            print_msg(&config, format!(" - {} ...", test.desc.name.as_slice()));
        }
        return;
    }

    let res = test::run_tests_console(
        &opts,
        test::TestList::new(tests, test::TestListOrder::Unsorted),
    );
    match res {
        Ok(true) => {}
        Ok(false) => {
            // We want to report that the tests failed, but we also want to give
            // some indication of just what tests we were running. Especially on
            // CI, where there can be cross-compiled tests for a lot of
            // architectures, without this critical information it can be quite
            // easy to miss which tests failed, and as such fail to reproduce
            // the failure locally.

            eprintln!(
                "Some tests failed in compiletest suite={} mode={} host={} target={}",
                config.suite, config.mode, config.host, config.target
            );

            std::process::exit(1);
        }
        Err(e) => {
            // We don't know if tests passed or not, but if there was an error
            // during testing we don't want to just succeed (we may not have
            // tested something), so fail.
            //
            // This should realistically "never" happen, so don't try to make
            // this a pretty error message.
            panic!("I/O failure during tests: {e:?}");
        }
    }
}

pub fn test_opts(config: &Config) -> test::TestOpts {
    test::TestOpts {
        exclude_should_panic: false,
        filters: config.filters.clone(),
        filter_exact: config.filter_exact,
        run_ignored: test::RunIgnored::No,
        format: if config.quiet { test::OutputFormat::Terse } else { test::OutputFormat::Pretty },
        logfile: config.logfile.clone(),
        run_tests: true,
        bench_benchmarks: true,
        nocapture: match env::var("RUST_TEST_NOCAPTURE") {
            Ok(val) => &val != "0",
            Err(_) => false,
        },
        color: config.color,
        shuffle: false,
        shuffle_seed: None,
        test_threads: None,
        skip: vec![],
        list: false,
        options: test::Options::new(),
        time_options: config.time_opts,
        fail_fast: config.fail_fast,
        force_run_in_process: false,
    }
}

pub fn make_tests(config: &Config, tests: &mut Vec<test::TestDescAndFn>) {
    debug!("making tests from {:?}", config.src_base.display());
    let inputs = inputs_stamp(config);
    collect_tests_from_dir(config, &config.src_base, &PathBuf::new(), &inputs, tests)
        .unwrap_or_else(|_| panic!("Could not read tests from {}", config.src_base.display()));
}

/// Returns a stamp constructed from input files common to all test cases.
fn common_inputs_stamp() -> Stamp {
    let rust_src_dir = top_level().expect("Could not find Rust source root");
    let kani_bin_path = &rust_src_dir.join("target/debug/trust-mc-compiler");

    // Create stamp based on the `trust-mc-compiler` binary
    let mut stamp = Stamp::from_path(kani_bin_path);

    // Add source and library directories
    stamp.add_dir(&rust_src_dir.join("src/"));
    stamp.add_dir(&rust_src_dir.join("trust-mc-compiler/"));
    stamp.add_dir(&rust_src_dir.join("trust-mc-driver/"));
    stamp.add_dir(&rust_src_dir.join("trust-mc-metadata/"));
    stamp.add_dir(&rust_src_dir.join("library/"));

    // Add relevant tools directories
    stamp.add_dir(&rust_src_dir.join("tools/compiletest/"));

    stamp
}

/// Returns a stamp that is sensitive to compiletest configuration changes.
///
/// This avoids "up to date" cache hits across runs with different Kani flags
/// (e.g., changing backends/solvers) and keeps test/metrics runs deterministic.
fn inputs_stamp(config: &Config) -> Stamp {
    let mut stamp = common_inputs_stamp();
    stamp.add_path(&config_stamp_path(config));
    stamp
}

fn config_stamp_path(config: &Config) -> PathBuf {
    let path = config.build_base.join("compiletest-config.txt");

    fs::create_dir_all(&config.build_base).unwrap();

    let contents = format!(
        "mode={}\n\
suite={}\n\
target={}\n\
host={}\n\
edition={:?}\n\
timeout={:?}\n\
extra_args={:?}\n",
        config.mode,
        config.suite,
        config.target,
        config.host,
        config.edition,
        config.timeout,
        config.extra_args
    );

    match fs::read_to_string(&path) {
        Ok(existing) if existing == contents => {}
        _ => fs::write(&path, contents).unwrap(),
    }

    path
}

fn collect_tests_from_dir(
    config: &Config,
    dir: &Path,
    relative_dir_path: &Path,
    inputs: &Stamp,
    tests: &mut Vec<test::TestDescAndFn>,
) -> io::Result<()> {
    match config.mode {
        Mode::CargoCoverage | Mode::CargoTrustMc | Mode::CargoTrustMcTest => {
            collect_expected_tests_from_dir(config, dir, relative_dir_path, inputs, tests)
        }
        Mode::Exec => collect_exec_tests_from_dir(config, dir, relative_dir_path, inputs, tests),
        _ => collect_rs_tests_from_dir(config, dir, relative_dir_path, inputs, tests),
    }
}

fn collect_expected_tests_from_dir(
    config: &Config,
    dir: &Path,
    relative_dir_path: &Path,
    inputs: &Stamp,
    tests: &mut Vec<test::TestDescAndFn>,
) -> io::Result<()> {
    // If we find a test foo/bar.rs, we have to build the
    // output directory `$build/foo` so we can write
    // `$build/foo/bar` into it. We do this *now* in this
    // sequential loop because otherwise, if we do it in the
    // tests themselves, they race for the privilege of
    // creating the directories and sometimes fail randomly.
    let build_dir = output_relative_path(config, relative_dir_path);
    fs::create_dir_all(&build_dir).unwrap();

    // If we find a `Cargo.toml` file in the current directory and we're in
    // Cargo-trust_mc mode, we should look for `*.expected` files and create an
    // output directory corresponding to each to avoid race conditions during
    // the testing phase. We immediately return after adding the tests to avoid
    // treating `*.rs` files as tests.
    assert!(
        config.mode == Mode::CargoCoverage
            || config.mode == Mode::CargoTrustMc
            || config.mode == Mode::CargoTrustMcTest
    );

    let has_cargo_toml = dir.join("Cargo.toml").exists();
    for file in fs::read_dir(dir)? {
        let file = file?;
        let file_path = file.path();
        if has_cargo_toml
            && (file_path.to_str().unwrap().ends_with(".expected")
                || "expected" == file_path.file_name().unwrap())
        {
            fs::create_dir_all(build_dir.join(file_path.file_stem().unwrap())).unwrap();
            let paths =
                TestPaths { file: file_path, relative_dir: relative_dir_path.to_path_buf() };
            tests.push(make_test(config, &paths, inputs));
        } else if file_path.is_dir() {
            // recurse on subdirectory
            let relative_file_path = relative_dir_path.join(file.file_name());
            debug!("found directory: {:?}", file_path.display());
            collect_expected_tests_from_dir(
                config,
                &file_path,
                &relative_file_path,
                inputs,
                tests,
            )?;
        }
    }
    Ok(())
}

/// Collect `exec` tests from a directory.
///
/// Note that this method isn't recursive like
/// `collect_expected_tests_from_dir`, as it allows us to ensure that newly
/// added tests are running. Hence, each test must be in its own folder.
fn collect_exec_tests_from_dir(
    config: &Config,
    dir: &Path,
    relative_dir_path: &Path,
    inputs: &Stamp,
    tests: &mut Vec<test::TestDescAndFn>,
) -> io::Result<()> {
    // If we find a test `foo/bar.rs`, we have to build the
    // output directory `$build/foo` so we can write
    // `$build/foo/bar` into it. We do this *now* in this
    // sequential loop because otherwise, if we do it in the
    // tests themselves, they race for the privilege of
    // creating the directories and sometimes fail randomly.
    let build_dir = output_relative_path(config, relative_dir_path);
    fs::create_dir_all(&build_dir).unwrap();

    // Ensure the mode we're running is `Mode::Exec`
    assert!(config.mode == Mode::Exec);

    // Each test is expected to be in its own folder (i.e., we don't do recursion)
    for file in fs::read_dir(dir)? {
        // Look for `config.yml` file in folder
        let file = file?;
        let file_path = file.path();
        let has_config_yml = file_path.join("config.yml").exists();
        if !has_config_yml {
            fatal_error(&format!(
                "couldn't find `config.yml` file for `exec` test in `{}`",
                file_path.display()
            ));
        }

        // Create directory for test and add it to the tests to be run
        fs::create_dir_all(build_dir.join(file_path.file_stem().unwrap())).unwrap();
        let paths = TestPaths { file: file_path, relative_dir: relative_dir_path.to_path_buf() };
        tests.push(make_test(config, &paths, inputs));
    }
    Ok(())
}

fn collect_rs_tests_from_dir(
    config: &Config,
    dir: &Path,
    relative_dir_path: &Path,
    inputs: &Stamp,
    tests: &mut Vec<test::TestDescAndFn>,
) -> io::Result<()> {
    // If we find a test foo/bar.rs, we have to build the
    // output directory `$build/foo` so we can write
    // `$build/foo/bar` into it. We do this *now* in this
    // sequential loop because otherwise, if we do it in the
    // tests themselves, they race for the privilege of
    // creating the directories and sometimes fail randomly.
    let build_dir = output_relative_path(config, relative_dir_path);
    fs::create_dir_all(build_dir).unwrap();

    // Add each `.rs` file as a test, and recurse further on any
    // subdirectories we find, except for `aux` directories.
    for file in fs::read_dir(dir)? {
        let file = file?;
        let file_path = file.path();
        let file_name = file.file_name();
        if is_test(&file_name) {
            debug!("found test file: {:?}", file_path.display());
            let paths =
                TestPaths { file: file_path, relative_dir: relative_dir_path.to_path_buf() };
            tests.push(make_test(config, &paths, inputs))
        } else if file_path.is_dir() {
            let relative_file_path = relative_dir_path.join(file.file_name());
            if &file_name != "auxiliary" {
                debug!("found directory: {:?}", file_path.display());
                collect_rs_tests_from_dir(config, &file_path, &relative_file_path, inputs, tests)?;
            }
        } else {
            debug!("found other file/directory: {:?}", file_path.display());
        }
    }
    Ok(())
}

/// Returns true if `file_name` looks like a proper test file name.
pub fn is_test(file_name: &OsString) -> bool {
    let file_name = file_name.to_str().unwrap();

    if !file_name.ends_with(".rs") {
        return false;
    }

    // `.`, `#`, and `~` are common temp-file prefixes.
    let invalid_prefixes = &[".", "#", "~"];
    !invalid_prefixes.iter().any(|p| file_name.starts_with(p))
}

fn make_test(config: &Config, testpaths: &TestPaths, inputs: &Stamp) -> test::TestDescAndFn {
    let test_path = PathBuf::from(&testpaths.file);

    let src_file = std::fs::File::open(&test_path).expect("open test file to parse ignores");
    let test_name = crate::make_test_name(config, testpaths);
    let desc = make_test_description(config, test_name, &test_path, src_file);

    let up_to_date = !config.force_rerun && is_up_to_date(config, testpaths, inputs);
    let testfn = if up_to_date {
        test::DynTestFn(Box::new(|| Ok(())))
    } else {
        make_test_closure(config, testpaths)
    };

    test::TestDescAndFn { desc, testfn }
}

fn stamp(config: &Config, testpaths: &TestPaths) -> PathBuf {
    output_base_dir(config, testpaths).join("stamp")
}

fn is_up_to_date(config: &Config, testpaths: &TestPaths, inputs: &Stamp) -> bool {
    let stamp_name = stamp(config, testpaths);
    // Check timestamps.
    let inputs = inputs.clone();

    inputs < Stamp::from_path(&stamp_name)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Stamp {
    time: SystemTime,
}

impl Stamp {
    fn from_path(path: &Path) -> Self {
        let mut stamp = Stamp { time: SystemTime::UNIX_EPOCH };
        stamp.add_path(path);
        stamp
    }

    fn add_path(&mut self, path: &Path) {
        let modified = fs::metadata(path)
            .and_then(|metadata| metadata.modified())
            .unwrap_or(SystemTime::UNIX_EPOCH);
        self.time = self.time.max(modified);
    }

    fn add_dir(&mut self, path: &Path) {
        // Tolerate missing directories: an absent input dir contributes nothing
        // to the stamp instead of aborting the whole run.
        for entry in WalkDir::new(path).into_iter().filter_map(Result::ok) {
            if entry.file_type().is_file() {
                let modified = entry
                    .metadata()
                    .ok()
                    .and_then(|metadata| metadata.modified().ok())
                    .unwrap_or(SystemTime::UNIX_EPOCH);
                self.time = self.time.max(modified);
            }
        }
    }
}

fn make_test_name(config: &Config, testpaths: &TestPaths) -> test::TestName {
    // Convert a complete path to something like
    //
    //    ui/foo/bar/baz.rs
    let path = PathBuf::from(config.src_base.file_name().unwrap())
        .join(&testpaths.relative_dir)
        .join(testpaths.file.file_name().unwrap());

    test::DynTestName(format!("[{}] {}", config.mode, path.display()))
}

fn make_test_closure(config: &Config, testpaths: &TestPaths) -> test::TestFn {
    let config = config.clone();
    let testpaths = testpaths.clone();
    test::DynTestFn(Box::new(move || {
        runtest::run(config, &testpaths);
        Ok(())
    }))
}

/// Print a message and error out without panicking
fn fatal_error(message: &str) {
    println!("error: {message}");
    // Use resume_unwind instead of panic!() to prevent a panic message + backtrace from
    // compiletest, which is unnecessary noise.
    std::panic::resume_unwind(Box::new(()));
}
