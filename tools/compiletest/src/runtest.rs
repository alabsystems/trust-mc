// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Modifications Copyright Kani Contributors
// See GitHub history for details.

use crate::common::KaniFailStep;
use crate::common::{
    CargoCoverage, CargoTrustMc, CargoTrustMcTest, CoverageBased, Exec, Expected, Stub, TrustMc,
};
use crate::common::{Config, TestPaths};
use crate::common::{output_base_dir, output_base_name};
use crate::header::TestProps;
use crate::read2::read2;
use crate::util::logv;
use crate::{fatal_error, json};

use std::env;
use std::ffi::OsString;
use std::fs::{self, create_dir_all};
use std::io;
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::str;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use tracing::*;
use wait_timeout::ChildExt;

const TRUST_MC_CHC_TIMEOUT_RETRY_MULTIPLIER: u32 = 5;
const TRUST_MC_CHC_TIMEOUT_NO_RETRY_MULTIPLIER: u32 = 1;
const DEFAULT_TRUST_MC_CHC_TIMEOUT_GRACE_SECS: u64 = 10;

// AY-CHC uses the requested timeout as a per-harness solver budget. compiletest
// still needs a larger outer watchdog so the retry ladder can finish.
fn trust_mc_chc_args_enabled(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--ay-chc" || arg.starts_with("--ay-chc="))
}

fn trust_mc_flags_specify_harness_timeout(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--harness-timeout" || arg.starts_with("--harness-timeout="))
}

fn trust_mc_chc_outer_timeout_from_parts(
    timeout: Duration,
    multiplier: u32,
    grace_secs: u64,
) -> Duration {
    let multiplied =
        timeout.checked_mul(multiplier).unwrap_or_else(|| Duration::from_secs(u64::MAX));
    multiplied
        .checked_add(Duration::from_secs(grace_secs))
        .unwrap_or_else(|| Duration::from_secs(u64::MAX))
}

fn trust_mc_chc_timeout_grace_secs() -> u64 {
    env::var("AY_SHELL_TIMEOUT_GRACE")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .unwrap_or(DEFAULT_TRUST_MC_CHC_TIMEOUT_GRACE_SECS)
}

fn trust_mc_chc_outer_timeout(timeout: Duration) -> Duration {
    let multiplier = if env::var_os("TRUST_MC_CHC_NO_RETRY").is_some() {
        TRUST_MC_CHC_TIMEOUT_NO_RETRY_MULTIPLIER
    } else {
        TRUST_MC_CHC_TIMEOUT_RETRY_MULTIPLIER
    };
    trust_mc_chc_outer_timeout_from_parts(timeout, multiplier, trust_mc_chc_timeout_grace_secs())
}

/// Isolate each test command in its own process group so an outer timeout can
/// terminate verifier and solver descendants together.
fn isolate_process_group(command: &mut Command) {
    #[cfg(unix)]
    {
        command.process_group(0);
    }
}

#[cfg(unix)]
fn kill_process_group(child: &mut Child) -> io::Result<()> {
    let process_group = i32::try_from(child.id())
        .map_err(|_| io::Error::other("child process id does not fit in i32"))?;
    // SAFETY: `process_group` is the positive PID returned by `Child::id`.
    // `isolate_process_group` made that PID the group leader before exec, and
    // `killpg` does not dereference memory or outlive this call.
    let result = unsafe { libc::killpg(process_group, libc::SIGKILL) };
    if result == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}

#[cfg(not(unix))]
fn kill_process_group(child: &mut Child) -> io::Result<()> {
    child.kill()
}

/// Configurations for `exec` tests
#[derive(Debug, Serialize, Deserialize)]
struct ExecConfig {
    // The path to the script to be executed
    script: String,
    // (Optional) The path to the `.expected` file to use for output comparison
    expected: Option<String>,
    // (Optional) The exit code to be returned by executing the script
    exit_code: Option<i32>,
}

#[cfg(not(windows))]
fn disable_error_reporting<F: FnOnce() -> R, R>(f: F) -> R {
    f()
}

/// The name of the environment variable that holds dynamic library locations.
pub fn dylib_env_var() -> &'static str {
    if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" }
}

pub fn run(config: Config, testpaths: &TestPaths) {
    if config.verbose {
        // We're going to be dumping a lot of info. Start on a new line.
        print!("\n\n");
    }
    debug!("running {:?}", testpaths.file.display());
    let props = TestProps::from_file(&testpaths.file, &config);

    let cx = TestCx { config: &config, props: &props, testpaths };
    create_dir_all(cx.output_base_dir()).unwrap();
    cx.run();
    cx.create_stamp();
}

#[derive(Copy, Clone)]
struct TestCx<'test> {
    config: &'test Config,
    props: &'test TestProps,
    testpaths: &'test TestPaths,
}

fn kani_test_bin() -> OsString {
    // Check TRUST_MC_TEST_BIN first, fall back to KANI_TEST_BIN for compatibility
    env::var_os("TRUST_MC_TEST_BIN")
        .or_else(|| env::var_os("KANI_TEST_BIN"))
        .unwrap_or_else(|| OsString::from("trust-mc"))
}

impl TestCx<'_> {
    /// Code executed
    fn run(&self) {
        match self.config.mode {
            TrustMc => self.run_kani_test(),
            CargoCoverage => self.run_cargo_coverage_test(),
            CargoTrustMc => self.run_cargo_kani_test(false),
            CargoTrustMcTest => self.run_cargo_kani_test(true),
            CoverageBased => self.run_expected_coverage_test(),
            Exec => self.run_exec_test(),
            Expected => self.run_expected_test(),
            Stub => self.run_stub_test(),
        }
    }

    fn compose_and_run(&self, mut command: Command) -> ProcRes {
        let cmdline = {
            let cmdline = format!("{command:?}");
            logv(self.config, format!("executing {cmdline}"));
            cmdline
        };

        command.stdout(Stdio::piped()).stderr(Stdio::piped()).stdin(Stdio::piped());

        let path =
            env::split_paths(&env::var_os(dylib_env_var()).unwrap_or_default()).collect::<Vec<_>>();

        // Add the new dylib search path var
        let newpath = env::join_paths(path).unwrap();
        command.env(dylib_env_var(), newpath);
        isolate_process_group(&mut command);

        let mut child = disable_error_reporting(|| command.spawn())
            .unwrap_or_else(|_| panic!("failed to exec `{:?}`", &command));

        // DRAIN THE PIPES CONCURRENTLY, from the instant the child exists.
        //
        // This previously called `wait_timeout()` and only `read2()` AFTER the
        // child exited — nobody consumed stdout/stderr while it ran. The OS pipe
        // buffer is 64 KiB, so as soon as a verbose harness filled it the child's
        // next write BLOCKED FOREVER and it could never exit. The outer wall then
        // ALWAYS expired regardless of size (a 900s wall timed out exactly like a
        // 310s one), the killed child's output was replaced with `Vec::new()`, and
        // `<name>.out` was written EMPTY — so scripts/ay-soundness-gate.sh, which
        // greps the artifact for `VERIFICATION:-`, reported "verifier never ran"
        // (VACUOUS) even though the verifier had decided and reported.
        //
        // Two ledgered soundness files hit it (memory_safety_uaf_fail,
        // realloc_stale_pointer_fail): their PDR/portfolio logging exceeds 64 KiB,
        // while every file that passed stayed under it. The smoking gun was a
        // `<name>.err` of exactly 65536 bytes — a full pipe buffer.
        //
        // Measured on memory_safety_uaf_fail: >900s deadlock with a 0-byte .out and
        // a 65536-byte .err  ->  118s, 2,204,627-byte .err, and a real
        // `VERIFICATION:- FAILED` + `Complete - ...` in .out.
        //
        // Reader threads own the pipes, so the child always makes progress and its
        // output survives even when we do have to kill it.
        let stdout_pipe = child.stdout.take();
        let stderr_pipe = child.stderr.take();
        let out_handle = std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut p) = stdout_pipe {
                use std::io::Read;
                let _ = p.read_to_end(&mut buf);
            }
            buf
        });
        let err_handle = std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut p) = stderr_pipe {
                use std::io::Read;
                let _ = p.read_to_end(&mut buf);
            }
            buf
        });

        let status = if let Some(timeout) = self.command_timeout() {
            match child.wait_timeout(timeout).unwrap() {
                Some(status) => status,
                None => {
                    println!("Process timed out after {timeout:?}s: {cmdline}");
                    kill_process_group(&mut child).unwrap();
                    child.wait().expect("invariant: killed child must be waitable")
                }
            }
        } else {
            child.wait().expect("failed to wait on child")
        };
        // Readers finish once every writer FD is closed, which exit/kill guarantees.
        let stdout = out_handle.join().unwrap_or_default();
        let stderr = err_handle.join().unwrap_or_default();

        let result = ProcRes {
            status,
            stdout: String::from_utf8_lossy(&stdout).into_owned(),
            stderr: String::from_utf8_lossy(&stderr).into_owned(),
            cmdline,
        };

        self.dump_output(&result.stdout, &result.stderr);

        result
    }

    fn trust_mc_chc_timeout_active(&self) -> bool {
        matches!(self.config.mode, TrustMc | Expected | CoverageBased | Stub)
            && trust_mc_chc_args_enabled(&self.props.kani_flags)
    }

    fn command_timeout(&self) -> Option<Duration> {
        let timeout = self.config.timeout?;
        if self.trust_mc_chc_timeout_active() {
            Some(trust_mc_chc_outer_timeout(timeout))
        } else {
            Some(timeout)
        }
    }

    fn maybe_add_trust_mc_harness_timeout(&self, command: &mut Command) {
        if !self.trust_mc_chc_timeout_active()
            || trust_mc_flags_specify_harness_timeout(&self.props.kani_flags)
        {
            return;
        }

        if let Some(timeout) = self.config.timeout {
            command.arg(format!("--harness-timeout={}s", timeout.as_secs()));
        }
    }

    fn dump_output(&self, out: &str, err: &str) {
        self.dump_output_file(out, "out");
        self.dump_output_file(err, "err");
        self.maybe_dump_to_stdout(out, err);
    }

    fn dump_output_file(&self, out: &str, extension: &str) {
        let outfile = self.make_out_name(extension);
        fs::write(outfile, out).unwrap();
    }

    /// Creates a filename for output with the given extension.
    /// E.g., `/.../testname.mode/testname.extension`.
    fn make_out_name(&self, extension: &str) -> PathBuf {
        self.output_base_name().with_extension(extension)
    }

    /// Gets the absolute path to the directory where all output for the given
    /// test should reside.
    /// E.g., `/path/to/build/host-triple/test/ui/relative/testname.mode/`.
    fn output_base_dir(&self) -> PathBuf {
        output_base_dir(self.config, self.testpaths)
    }

    /// Gets the absolute path to the base filename used as output for the given
    /// test.
    /// E.g., `/.../relative/testname.mode/testname`.
    fn output_base_name(&self) -> PathBuf {
        output_base_name(self.config, self.testpaths)
    }

    fn maybe_dump_to_stdout(&self, out: &str, err: &str) {
        if self.config.verbose {
            println!("------stdout------------------------------");
            println!("{out}");
            println!("------stderr------------------------------");
            println!("{err}");
            println!("------------------------------------------");
        }
    }

    fn error(&self, err: &str) {
        println!("\nerror: {err}");
    }

    fn fatal_proc_rec(&self, err: &str, proc_res: &ProcRes) -> ! {
        self.error(err);
        proc_res.fatal(None, || ());
    }

    /// Runs `trust-mc-compiler` on the test file specified by `self.testpaths.file`. An
    /// error message is printed to stdout if the check result is not expected.
    fn check(&self) {
        let mut rustc = Command::new("trust-mc-compiler");
        rustc
            .args(["--goto-c"])
            .args(self.props.compile_flags.clone())
            .args(["-Z", "no-codegen"])
            .arg(&self.testpaths.file);
        let proc_res = self.compose_and_run(rustc);
        if self.props.kani_panic_step == Some(KaniFailStep::Check) {
            if proc_res.status.success() {
                self.fatal_proc_rec("test failed: expected check failure, got success", &proc_res);
            }
        } else if !proc_res.status.success() {
            self.fatal_proc_rec("test failed: expected check success, got failure", &proc_res);
        }
    }

    /// Runs `trust-mc-compiler` on the test file specified by `self.testpaths.file`. An
    /// error message is printed to stdout if the codegen result is not
    /// expected.
    fn codegen(&self) {
        let mut rustc = Command::new("trust-mc-compiler");
        rustc
            .args(["--goto-c"])
            .args(self.props.compile_flags.clone())
            .args(["--out-dir"])
            .arg(self.output_base_dir())
            .arg(&self.testpaths.file);
        let proc_res = self.compose_and_run(rustc);
        if self.props.kani_panic_step == Some(KaniFailStep::Codegen) {
            if proc_res.status.success() {
                self.fatal_proc_rec(
                    "test failed: expected codegen failure, got success",
                    &proc_res,
                );
            }
        } else if !proc_res.status.success() {
            self.fatal_proc_rec("test failed: expected codegen success, got failure", &proc_res);
        }
    }

    /// Runs Kani on the test file specified by `self.testpaths.file`. An error
    /// message is printed to stdout if the verification result is not expected.
    fn verify(&self) {
        let proc_res = self.run_kani();
        // Print an error if the verification result is not expected.
        if self.props.kani_panic_step == Some(KaniFailStep::Verify) {
            if proc_res.status.success() {
                self.fatal_proc_rec(
                    "test failed: expected verification failure, got success",
                    &proc_res,
                );
            }
        } else if !proc_res.status.success() {
            self.fatal_proc_rec(
                "test failed: expected verification success, got failure",
                &proc_res,
            );
        }
    }

    /// Checks, codegens, and verifies the test file specified by
    /// `self.testpaths.file`. An error message is printed to stdout if a result
    /// is not expected.
    fn run_kani_test(&self) {
        match self.props.kani_panic_step {
            Some(KaniFailStep::Check) => {
                self.check();
            }
            Some(KaniFailStep::Codegen) => {
                self.codegen();
            }
            Some(KaniFailStep::Verify) | None => {
                self.verify();
            }
        }
    }

    /// Runs cargo-kani on the function specified by the stem of `self.testpaths.file`.
    /// The `test` parameter controls whether to specify `--tests` to `cargo kani`.
    /// An error message is printed to stdout if verification output does not
    /// contain the expected output in `self.testpaths.file`.
    fn run_cargo_kani_test(&self, test: bool) {
        // We create our own command for the same reasons listed in `run_kani_test` method.
        let mut cargo = Command::new("cargo");
        // We run `cargo` on the directory where we found the `*.expected` file
        let parent_dir = self.testpaths.file.parent().unwrap();
        // The name of the function to test is the same as the stem of `*.expected` file
        let function_name = self.testpaths.file.file_stem().unwrap().to_str().unwrap();
        cargo
            .arg("kani")
            .arg("--target-dir")
            .arg(self.output_base_dir().join("target"))
            .current_dir(parent_dir);
        if test {
            cargo.arg("--tests");
        }
        if "expected" != self.testpaths.file.file_name().unwrap() {
            cargo.args(["--harness", function_name]);
        }
        cargo.args(&self.config.extra_args);

        let proc_res = self.compose_and_run(cargo);
        self.verify_output(&proc_res, &self.testpaths.file);

        // TODO(#450): Check exit status (blocked by upstream kani#1895).
        // Unlike verify() which uses kani_panic_step, cargo tests don't have
        // a standard way to indicate expected failure vs unexpected failure.
    }

    /// Common method used to run Kani on a single file test.
    fn run_kani(&self) -> ProcRes {
        // Other modes call self.compile_test(...). However, we cannot call it here for two reasons:
        // 1. It calls rustc instead of Kani
        // 2. It may pass some options that do not make sense for Kani
        // So we create our own command to execute Kani and pass it to self.compose_and_run(...) directly.
        let mut kani = Command::new(kani_test_bin());
        // We cannot pass rustc flags directly to Kani. Instead, we add them
        // to the current environment through the `RUSTFLAGS` environment
        // variable. Kani recognizes the variable and adds those flags to its
        // internal call to rustc.
        if !self.props.compile_flags.is_empty() {
            kani.env("RUSTFLAGS", self.props.compile_flags.join(" "));
        }

        // Pass the test path along with Kani flags parsed from comments at the top of the test file.
        // Note: extra_args are already included in kani_flags via header.rs:50
        kani.arg(&self.testpaths.file).args(&self.props.kani_flags);
        self.maybe_add_trust_mc_harness_timeout(&mut kani);

        // Isolate compilation artifacts per-test to prevent parallel write
        // collisions when multiple tests share the same source directory.
        // Without this, all tests in a suite write rmeta/rlib/smt2 files to
        // the test source directory, causing failures under parallel execution.
        let target_dir = self.output_base_dir().join("target");
        kani.arg("--target-dir").arg(&target_dir);

        self.compose_and_run(kani)
    }

    /// Run Kani with coverage enabled on a single source file
    fn run_kani_with_coverage(&self) -> ProcRes {
        let mut kani = Command::new(kani_test_bin());
        if !self.props.compile_flags.is_empty() {
            kani.env("RUSTFLAGS", self.props.compile_flags.join(" "));
        }
        // Note: extra_args already included in kani_flags via header.rs:50
        kani.arg(&self.testpaths.file).args(&self.props.kani_flags);
        self.maybe_add_trust_mc_harness_timeout(&mut kani);
        kani.arg("--coverage").args(["-Z", "source-coverage"]);

        // Isolate compilation artifacts per-test (same as run_kani).
        let target_dir = self.output_base_dir().join("target");
        kani.arg("--target-dir").arg(&target_dir);

        self.compose_and_run(kani)
    }

    /// Run Kani with coverage enabled on a cargo package
    fn run_cargo_coverage_test(&self) {
        // We create our own command for the same reasons listed in `run_kani_test` method.
        let mut cargo = Command::new("cargo");
        // We run `cargo` on the directory where we found the `*.expected` file
        let parent_dir = self.testpaths.file.parent().unwrap();
        // The name of the function to test is the same as the stem of `*.expected` file
        let function_name = self.testpaths.file.file_stem().unwrap().to_str().unwrap();
        cargo
            .arg("kani")
            .arg("--coverage")
            .arg("-Zsource-coverage")
            .arg("--target-dir")
            .arg(self.output_base_dir().join("target"))
            .current_dir(parent_dir);

        if "expected" != self.testpaths.file.file_name().unwrap() {
            cargo.args(["--harness", function_name]);
        }
        cargo.args(&self.config.extra_args);

        let proc_res = self.compose_and_run(cargo);
        self.verify_output(&proc_res, &self.testpaths.file);

        // TODO(#450): Check exit status (blocked by upstream kani#1895).
        // Unlike verify() which uses kani_panic_step, cargo tests don't have
        // a standard way to indicate expected failure vs unexpected failure.
    }

    /// Runs an executable file and:
    ///  * Checks the expected output if an expected file is specified
    ///  * Checks the exit code (assumed to be 0 by default)
    fn run_exec_test(&self) {
        // Open the `config.yml` file and extract its values
        let path_yml = self.testpaths.file.join("config.yml");
        let config_file = std::fs::File::open(path_yml).expect("couldn't open `config.yml`");
        let exec_config_res = serde_yaml::from_reader(config_file);
        if let Err(error) = &exec_config_res {
            let err_msg = format!("couldn't parse `config.yml` file: {error}");
            fatal_error(&err_msg);
        }
        let exec_config: ExecConfig = exec_config_res.unwrap();

        // Check if the `script` file exists
        let script_rel_path = PathBuf::from(exec_config.script);
        let script_path = self.testpaths.file.join(script_rel_path);
        if !script_path.exists() {
            let err_msg = format!("test failed: couldn't find script in {}", script_path.display());
            fatal_error(&err_msg);
        }

        // Check if the `expected` file exists, and load its contents into `expected_output`
        let expected_path = if let Some(expected_path) = exec_config.expected {
            let expected_rel_path = PathBuf::from(expected_path);
            let expected_path = self.testpaths.file.join(expected_rel_path);
            if !expected_path.exists() {
                let err_msg = format!(
                    "test failed: couldn't find expected file in {}",
                    expected_path.display()
                );
                fatal_error(&err_msg);
            }
            Some(expected_path)
        } else {
            None
        };

        // Create the command `time script` and run it from the test directory
        let mut script_path_cmd = Command::new("time");
        script_path_cmd.arg(script_path).current_dir(&self.testpaths.file);
        let proc_res = self.compose_and_run(script_path_cmd);

        // Compare with expected output if it was provided
        if let Some(path) = expected_path {
            self.verify_output(&proc_res, &path);
        }

        // Compare with exit code (0 if it wasn't provided)
        let expected_code = exec_config.exit_code.or(Some(0));
        if proc_res.status.code() != expected_code {
            let err_msg = format!(
                "test failed: expected code {}, got code {}",
                expected_code.unwrap(),
                proc_res.status.code().unwrap()
            );
            self.fatal_proc_rec(&err_msg, &proc_res);
        }
    }

    /// Runs Kani on the test file specified by `self.testpaths.file`. An error
    /// message is printed to stdout if verification output does not contain the
    /// expected output.
    ///
    /// We read the expected output from the file
    /// `self.testpaths.file.with_extension("expected")` (same file name but
    /// extension replaced with `.expected`). For backwards compatibility, if we
    /// don't find this file, we will also try a file called `expected` in the
    /// same directory as `self.testpaths.file`.
    fn run_expected_test(&self) {
        let proc_res = self.run_kani();
        let dot_expected_path = self.testpaths.file.with_extension("expected");
        let expected_path = if dot_expected_path.exists() {
            dot_expected_path
        } else {
            self.testpaths.file.parent().unwrap().join("expected")
        };
        self.verify_output(&proc_res, &expected_path);
    }

    /// Runs Kani in coverage mode on the test file specified by `self.testpaths.file`.
    fn run_expected_coverage_test(&self) {
        let proc_res = self.run_kani_with_coverage();
        let cov_results_path = self.extract_cov_results_path(&proc_res);
        let (kanimap, kaniraws, kanicov) = self.find_cov_files(&cov_results_path);
        let kanicov_proc = self.run_kanicov_report(&kanimap, &kaniraws, &kanicov);
        let expected_path = self.testpaths.file.parent().unwrap().join("expected");
        self.verify_output(&kanicov_proc, &expected_path);
    }

    /// Runs Kani with stub implementations of various data structures.
    /// Currently, it only runs tests for the Vec module with the (Kani)Vec
    /// abstraction. At a later stage, it should be possible to add command-line
    /// arguments to test specific abstractions and modules.
    fn run_stub_test(&self) {
        let proc_res = self.run_kani();
        if !proc_res.status.success() {
            self.fatal_proc_rec(
                "test failed: expected verification success, got failure",
                &proc_res,
            );
        }
    }

    /// Print an error if the verification output does not contain the expected
    /// lines.
    fn verify_output(&self, proc_res: &ProcRes, expected_path: &Path) {
        // Include the output from stderr here for cases where there are exceptions
        let expected = fs::read_to_string(expected_path).unwrap();
        let output = proc_res.stdout.to_string() + &proc_res.stderr;
        let diff = TestCx::contains_lines(
            &output.split('\n').collect::<Vec<_>>(),
            expected.split('\n').collect(),
        );
        match (diff, self.config.fix_expected) {
            (None, _) => { /* Test passed. Do nothing*/ }
            (Some(_), true) => {
                // Fix output but still fail the test so users know which ones were updated
                fs::write(expected_path, output).unwrap_or_else(|_| {
                    panic!("Failed to update file {}", expected_path.display())
                });
                self.fatal_proc_rec(
                    &format!("updated `{}` file, please review", expected_path.display()),
                    proc_res,
                )
            }
            (Some(lines), false) => {
                // Throw an error
                self.fatal_proc_rec(
                    &format!(
                        "test failed: expected output to contain the line(s):\n{}",
                        lines.join("\n")
                    ),
                    proc_res,
                );
            }
        }
    }

    /// Looks for each line or set of lines in `str`. Returns `None` if all
    /// lines are in `str`.  Otherwise, it returns the first line not found in
    /// `str`.
    fn contains_lines<'a>(str: &[&str], lines: Vec<&'a str>) -> Option<Vec<&'a str>> {
        let mut consecutive_lines: Vec<&str> = Vec::new();
        for line in lines {
            // A line that ends in "\" indicates that the next line in the
            // expected file should appear on the consecutive line in the
            // output. This is a temporary mechanism until we have more robust
            // json-based checking of verification results
            if let Some(prefix) = line.strip_suffix('\\') {
                // accumulate the lines
                consecutive_lines.push(prefix);
            } else {
                consecutive_lines.push(line);
                if !TestCx::contains(str, &consecutive_lines) {
                    return Some(consecutive_lines);
                }
                consecutive_lines.clear();
            }
        }
        // Someone may add a `\` to the last line (probably by accident) but
        // that would mean this test would succeed without actually testing so
        // we add a check here again.
        (!consecutive_lines.is_empty() && !TestCx::contains(str, &consecutive_lines))
            .then_some(consecutive_lines)
    }

    /// Check if there is a set of consecutive lines in `str` where each line
    /// contains a line from `lines`
    fn contains(str: &[&str], lines: &[&str]) -> bool {
        // Does *any* subslice of length `lines.len()` satisfy the containment of
        // *all* `lines`?
        // `trim()` added to ignore trailing and preceding whitespace
        str.windows(lines.len()).any(|subslice| {
            subslice.iter().zip(lines).all(|(output, expected)| output.contains(expected.trim()))
        })
    }

    fn create_stamp(&self) {
        let stamp = crate::stamp(self.config, self.testpaths);
        fs::write(stamp, "we only support one configuration").unwrap();
    }

    /// Run `trust-mc-cov merge` and `trust-mc-cov report` to generate a text-based
    /// report and return the `ProcRes` associated to the `trust-mc-cov report`
    /// command.
    fn run_kanicov_report(
        &self,
        kanimap: &PathBuf,
        kaniraws: &[PathBuf],
        kanicov: &PathBuf,
    ) -> ProcRes {
        let mut kanicov_merge = Command::new("trust-mc-cov");
        kanicov_merge.arg("merge");
        kanicov_merge.args(kaniraws);
        kanicov_merge.arg("--output");
        kanicov_merge.arg(kanicov);
        let merge_cmd = self.compose_and_run(kanicov_merge);

        if !merge_cmd.status.success() {
            self.fatal_proc_rec(
                "test failed: could not run `trust-mc-cov merge` command",
                &merge_cmd,
            );
        }

        let mut kanicov_report = Command::new("trust-mc-cov");
        kanicov_report.arg("report").arg(kanimap).arg("--profile").arg(kanicov);
        let report_cmd = self.compose_and_run(kanicov_report);

        if !report_cmd.status.success() {
            self.fatal_proc_rec(
                "test failed: could not run `trust-mc-cov report` command",
                &report_cmd,
            );
        }
        report_cmd
    }

    /// Return the paths to the files to be used for the `trust-mc-cov` commands.
    /// Note that `kanimap` and `kaniraws` result from any coverage-enabled Kani
    /// run. `kanicov` is the name we will use for the output of the `trust-mc-cov
    /// merge` command.
    fn find_cov_files(&self, folder_path: &Path) -> (PathBuf, Vec<PathBuf>, PathBuf) {
        let folder_name = folder_path.file_name().unwrap();

        let kanimap = folder_path.join(format!("{}_kanimap.json", folder_name.to_string_lossy()));
        let kanicov = folder_path.join(format!("{}_kanicov.json", folder_name.to_string_lossy()));

        let kaniraw_glob = format!("{}/*_kaniraw.json", folder_path.display());
        let kaniraws: Vec<PathBuf> = glob::glob(&kaniraw_glob)
            .expect("Failed to read glob pattern")
            .filter_map(|entry| entry.ok())
            .collect();

        (kanimap, kaniraws, kanicov)
    }

    /// Find the path to the folder where the coverage results have been saved.
    ///
    /// The path is displayed in the output of a coverage-enabled Kani run like
    /// this:
    /// ```sh
    /// Verification Time: XX.XXXXXXXs
    ///
    /// [info] Coverage results saved to /path/to/cov/results/kanicov_<date>_<time>
    /// Summary:
    /// ```
    fn extract_cov_results_path(&self, proc_res: &ProcRes) -> PathBuf {
        let output_lines = proc_res.stdout.split('\n').collect::<Vec<&str>>();
        let coverage_info = output_lines.iter().find(|l| l.contains("Coverage results saved to"));
        if coverage_info.is_none() {
            self.fatal_proc_rec("failed to find the path to the coverage results", proc_res);
        }
        let coverage_path = coverage_info
            .unwrap()
            .split(' ')
            .next_back()
            .expect("couldn't retrieve path to the coverage results");
        PathBuf::from(coverage_path)
    }
}

/// Represents the result of executing the process `cmdline`
pub struct ProcRes {
    status: ExitStatus,
    pub stdout: String,
    stderr: String,
    cmdline: String,
}

impl ProcRes {
    pub fn fatal(&self, err: Option<&str>, on_failure: impl FnOnce()) -> ! {
        if let Some(e) = err {
            println!("\nerror: {e}");
        }
        print!(
            "\
             status: {}\n\
             command: {}\n\
             stdout:\n\
             ------------------------------------------\n\
             {}\n\
             ------------------------------------------\n\
             stderr:\n\
             ------------------------------------------\n\
             {}\n\
             ------------------------------------------\n\
             \n",
            self.status,
            self.cmdline,
            json::extract_rendered(&self.stdout),
            json::extract_rendered(&self.stderr),
        );
        on_failure();
        // Use resume_unwind instead of panic!() to prevent a panic message + backtrace from
        // compiletest, which is unnecessary noise.
        std::panic::resume_unwind(Box::new(()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trust_mc_chc_arg_detection_requires_chc_flag() {
        assert!(trust_mc_chc_args_enabled(&["--backend=ay".to_string(), "--ay-chc".to_string()]));
        assert!(!trust_mc_chc_args_enabled(&["--backend=ay".to_string()]));
    }

    #[test]
    fn harness_timeout_detection_accepts_split_and_equals_forms() {
        assert!(trust_mc_flags_specify_harness_timeout(&["--harness-timeout".to_string()]));
        assert!(trust_mc_flags_specify_harness_timeout(&["--harness-timeout=60s".to_string()]));
        assert!(!trust_mc_flags_specify_harness_timeout(&["--timeout".to_string()]));
    }

    #[test]
    fn trust_mc_chc_outer_timeout_keeps_retry_headroom_outside_harness_budget() {
        let timeout = Duration::from_secs(60);
        let expanded = trust_mc_chc_outer_timeout_from_parts(timeout, 5, 10);
        assert_eq!(expanded, Duration::from_secs(310));
    }
}
