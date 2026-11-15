// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The external `ay` solver binary, and the AY revision it must be.
//!
//! The bounded (BMC) lane, its cover and vacuity probes, the CHC cover check and
//! the proof-only external CHC fallback all spawn an `ay` subprocess, so their
//! verdicts are that binary's verdicts. Until 2026-09-11 the driver took
//! whatever `which ay` returned and never looked at its version; on the
//! measurement host that was an ay 0.13.0 from a package store while this build
//! pinned 0.26.0 (plan of record, M0: "the driver refuses off-pin subprocess
//! ay").
//!
//! Resolution is `$TRUST_MC_AY_BIN` when it is set — an explicit choice is never
//! silently replaced — then a release bundle's private `libexec/ay`; development
//! builds otherwise use `ay` on `PATH`. A missing or escaped bundled helper
//! refuses without a PATH fallback. The binary is
//! asked `ay --version` once per process, and the commit in its
//! `+build.<n>.<sha>` stamp must equal the pin declared in the root
//! `Cargo.toml` (`[workspace.dependencies]`, see [`crate::version`]). Anything
//! else — another commit, a dirty build, no stamp, no answer, a pin this build
//! cannot read — is refused with the binary, its version, the pin and the fix.
//!
//! `--allow-unpinned-ay` or `TRUST_MC_ALLOW_UNPINNED_AY=1` turns the refusal into
//! a warning. The run then proceeds, every harness prints
//! `[AY:SOLVER_PIN_MISMATCH:found=<commit>:pin=<commit>]`, and no success is
//! reported as a clean `SUCCESSFUL`: it goes through the existing unvalidated
//! path and renders as `SUCCESSFUL (UNVALIDATED)`, which
//! `--fail-on-unvalidated-success` turns into a failing exit code.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Once, OnceLock};
use std::time::Duration;

use crate::demotion::is_effective_manual_success;
use crate::verification_result::{ValidationStatus, VerificationResult};

mod bundled;

/// Names the `ay` binary to run, in preference to `PATH`.
pub(crate) const AY_BIN_ENV: &str = "TRUST_MC_AY_BIN";
/// `1` proceeds with an off-pin `ay`, exactly like `--allow-unpinned-ay`.
pub(crate) const ALLOW_UNPINNED_ENV: &str = "TRUST_MC_ALLOW_UNPINNED_AY";
/// The command-line spelling of the same escape hatch.
pub(crate) const ALLOW_UNPINNED_FLAG: &str = "--allow-unpinned-ay";

/// `ay --version` prints one line; a binary that takes longer than this to do
/// so is not answering the question.
const VERSION_PROBE_TIMEOUT: Duration = Duration::from_secs(30);

/// Mirror of `--allow-unpinned-ay`, set when a session is constructed. The
/// solver call sites are deep inside free functions and `&self` methods that do
/// not all see the arguments, which is the same reason `--quiet` is mirrored.
static ALLOW_UNPINNED_FROM_ARGS: AtomicBool = AtomicBool::new(false);
/// Set the first time an off-pin binary is actually handed to a caller.
static UNPINNED_ACCEPTED: AtomicBool = AtomicBool::new(false);
/// One `locate` + `ay --version` per process.
static INSPECTED: OnceLock<Result<ExternalAy, String>> = OnceLock::new();
static WARNED: Once = Once::new();

/// Where the binary came from, for messages.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AySource {
    Override,
    Bundled,
    Path,
}

impl AySource {
    fn describe(self) -> &'static str {
        match self {
            AySource::Override => "from $TRUST_MC_AY_BIN",
            AySource::Bundled => "from this bundle's private libexec/ay",
            AySource::Path => "found on PATH",
        }
    }
}

/// The `+build.<increment>.<commit>[-dirty]` stamp of an `ay --version` line,
/// e.g. `ay 0.26.0+build.9281.<40 hex>@2026-09-11T02:47:31Z`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BuildStamp<'a> {
    pub(crate) commit: &'a str,
    pub(crate) dirty: bool,
}

/// Parse the build stamp, strictly: a decimal increment, exactly 40 lowercase
/// hex digits, an optional `-dirty`, then the end, `@` or whitespace. Anything
/// looser could read a prefix of some other token as a commit.
pub(crate) fn parse_build_stamp(version_line: &str) -> Option<BuildStamp<'_>> {
    let (_, after) = version_line.split_once("+build.")?;
    let (increment, rest) = after.split_once('.')?;
    if increment.is_empty() || !increment.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    if rest.bytes().take_while(u8::is_ascii_hexdigit).count() != 40 {
        return None;
    }
    let (commit, tail) = rest.split_at(40);
    if !commit.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
        return None;
    }
    let (dirty, tail) = match tail.strip_prefix("-dirty") {
        Some(tail) => (true, tail),
        None => (false, tail),
    };
    if !(tail.is_empty() || tail.starts_with('@') || tail.starts_with(char::is_whitespace)) {
        return None;
    }
    Some(BuildStamp { commit, dirty })
}

/// How an `ay` binary relates to the pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PinStatus {
    Matched,
    OtherCommit { commit: String },
    DirtyBuild { commit: String },
    Unstamped,
    NoVersion,
    PinUnavailable { reason: String },
}

impl PinStatus {
    /// `version` is the first line of `ay --version` (`None`: no answer);
    /// `pin` is the declared AY revision or why it could not be read.
    pub(crate) fn evaluate(version: Option<&str>, pin: Result<&str, &str>) -> Self {
        let pin = match pin {
            Ok(pin) => pin,
            Err(reason) => return PinStatus::PinUnavailable { reason: reason.to_string() },
        };
        let Some(version) = version else {
            return PinStatus::NoVersion;
        };
        match parse_build_stamp(version) {
            None => PinStatus::Unstamped,
            Some(BuildStamp { commit, dirty: true }) => {
                PinStatus::DirtyBuild { commit: commit.to_string() }
            }
            Some(BuildStamp { commit, dirty: false }) if commit == pin => PinStatus::Matched,
            Some(BuildStamp { commit, dirty: false }) => {
                PinStatus::OtherCommit { commit: commit.to_string() }
            }
        }
    }

    fn problem(&self) -> String {
        match self {
            PinStatus::Matched => "none: it is the pinned commit".to_string(),
            PinStatus::OtherCommit { commit } => {
                format!("it was built from AY commit {commit}, not the pinned commit")
            }
            PinStatus::DirtyBuild { commit } => format!(
                "it was built from a dirty AY tree at {commit}, so it is not the pinned commit"
            ),
            PinStatus::Unstamped => "its version line carries no `+build.<n>.<commit>` stamp, \
                                     so its commit cannot be checked"
                .to_string(),
            PinStatus::NoVersion => {
                "it did not answer `ay --version`, so its commit cannot be checked".to_string()
            }
            PinStatus::PinUnavailable { reason } => {
                format!("this build cannot read its own pinned AY revision ({reason})")
            }
        }
    }
}

/// What to do with a binary, given its pin status and whether the user allowed
/// unpinned solvers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Decision {
    Use,
    UseUnpinned,
    Refuse,
}

pub(crate) fn decide(status: &PinStatus, allow_unpinned: bool) -> Decision {
    match (status, allow_unpinned) {
        (PinStatus::Matched, _) => Decision::Use,
        (_, true) => Decision::UseUnpinned,
        (_, false) => Decision::Refuse,
    }
}

/// The fix for an off-pin `ay`. `trust-mc doctor` prints the same text
/// (`src/frontend/engine.rs`, `unpinned_ay_fix`); `tests/cli.rs` holds the two
/// together.
pub(crate) fn unpinned_ay_fix(pin: &str) -> String {
    format!(
        "build `ay` at the pinned AY commit and point trust-mc at it:\n    \
         git -C <ay checkout> checkout {pin}\n    \
         targo --unverified build --release --manifest-path <ay checkout>/Cargo.toml -p ay --features cli\n    \
         export {AY_BIN_ENV}=<ay checkout>/target/release/ay\n  \
         ...or run anyway, with every success reported as SUCCESSFUL (UNVALIDATED):\n    \
         pass {ALLOW_UNPINNED_FLAG}, or set {ALLOW_UNPINNED_ENV}=1"
    )
}

/// A located, version-probed `ay` binary and its relation to the pin.
#[derive(Debug, Clone)]
pub(crate) struct ExternalAy {
    pub(crate) path: PathBuf,
    pub(crate) source: AySource,
    pub(crate) version: Option<String>,
    pub(crate) pin: Result<String, String>,
    pub(crate) status: PinStatus,
}

impl ExternalAy {
    fn decision(&self, allow_unpinned: bool) -> Decision {
        // A broken declared release closure must be repaired, never converted
        // into an accepted unpinned default. Explicit overrides retain their
        // existing visibly unvalidated policy.
        decide(&self.status, allow_unpinned && self.source != AySource::Bundled)
    }

    fn new(
        path: PathBuf,
        source: AySource,
        version: Option<String>,
        pin: Result<String, String>,
    ) -> Self {
        let status =
            PinStatus::evaluate(version.as_deref(), pin.as_deref().map_err(String::as_str));
        ExternalAy { path, source, version, pin, status }
    }

    fn found_label(&self) -> String {
        match self.version.as_deref() {
            None => "no-version".to_string(),
            Some(line) => match parse_build_stamp(line) {
                Some(BuildStamp { commit, dirty: true }) => format!("{commit}-dirty"),
                Some(BuildStamp { commit, dirty: false }) => commit.to_string(),
                None => "unstamped".to_string(),
            },
        }
    }

    fn pin_label(&self) -> &str {
        self.pin.as_deref().unwrap_or("unavailable")
    }

    /// The per-harness marker a run with an accepted off-pin binary prints.
    pub(crate) fn marker(&self) -> String {
        format!("[AY:SOLVER_PIN_MISMATCH:found={}:pin={}]", self.found_label(), self.pin_label())
    }

    fn version_label(&self) -> &str {
        self.version.as_deref().unwrap_or("(no answer to `ay --version`)")
    }

    /// The refusal: the binary, its version, the pin, and the fix.
    pub(crate) fn refusal(&self) -> String {
        let pin = match &self.pin {
            Ok(pin) => pin.clone(),
            Err(reason) => format!("unavailable ({reason})"),
        };
        format!(
            "the external `ay` solver is not the AY revision this trust-mc build pins\n\
             \n  binary:   {} ({})\
             \n  version:  {}\
             \n  pinned:   {pin}\
             \n  problem:  {}\n\
             \nIts verdicts could not be attributed to the pinned AY, so trust-mc refuses to run it.\n\
             \nTo fix:\n\n  {}\n",
            self.path.display(),
            self.source.describe(),
            self.version_label(),
            self.status.problem(),
            unpinned_ay_fix(self.pin.as_deref().unwrap_or("<pinned commit>")),
        )
    }

    fn warning(&self, allowed_by: &str) -> String {
        format!(
            "{} warning: running an off-pin `ay` because {allowed_by} is set\n  \
             binary:   {} ({})\n  version:  {}\n  pinned:   {}\n  problem:  {}\n  \
             No success from this run is reported as a clean SUCCESSFUL; each is \
             SUCCESSFUL (UNVALIDATED).",
            self.marker(),
            self.path.display(),
            self.source.describe(),
            self.version_label(),
            self.pin_label(),
            self.status.problem(),
        )
    }
}

fn is_executable_file(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::metadata(path).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

/// Resolve an explicit override, this release's private helper, or development PATH.
pub(crate) fn locate() -> Result<(PathBuf, AySource), String> {
    locate_selected(
        std::env::var_os(AY_BIN_ENV),
        || {
            if option_env!("MC_DRIVER_RELEASE_BUNDLE") == Some("1") {
                std::env::current_exe()
                    .map(Some)
                    .map_err(|e| format!("cannot locate bundled AY: {e}"))
            } else {
                Ok(None)
            }
        },
        || which::which("ay").ok(),
    )
}

fn locate_selected(
    override_path: Option<OsString>,
    executable: impl FnOnce() -> Result<Option<PathBuf>, String>,
    on_path: impl FnOnce() -> Option<PathBuf>,
) -> Result<(PathBuf, AySource), String> {
    if override_path.as_ref().is_some_and(|value| !value.is_empty()) {
        return locate_with(override_path, None, on_path);
    }
    let executable = executable()?;
    let bundle_root = executable.as_deref().map(bundled::root_from_executable).transpose()?;
    locate_with(None, bundle_root, on_path)
}

fn locate_with(
    override_path: Option<OsString>,
    bundle_root: Option<&Path>,
    on_path: impl FnOnce() -> Option<PathBuf>,
) -> Result<(PathBuf, AySource), String> {
    if let Some(value) = override_path.filter(|value| !value.is_empty()) {
        let path = PathBuf::from(value);
        return if is_executable_file(&path) {
            Ok((path, AySource::Override))
        } else {
            Err(format!(
                "{AY_BIN_ENV}={} is not an executable file. Point it at a built `ay` solver \
                 binary, or unset it to use `ay` from PATH.",
                path.display()
            ))
        };
    }
    if let Some(root) = bundle_root {
        return bundled::locate(root).map(|path| (path, AySource::Bundled));
    }
    on_path().map(|path| (path, AySource::Path)).ok_or_else(|| {
        format!(
            "AY solver not found in PATH ({AY_BIN_ENV} is not set). Install ay, or set \
             {AY_BIN_ENV} to a built `ay` binary."
        )
    })
}

fn probe_version(path: &Path) -> Option<String> {
    let mut cmd = Command::new(path);
    cmd.arg("--version");
    let output = crate::session::run_piped_with_timeout(cmd, VERSION_PROBE_TIMEOUT).ok()?;
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(str::to_string)
}

/// Locate and probe the binary, once per process.
pub(crate) fn inspect() -> Result<&'static ExternalAy, String> {
    INSPECTED
        .get_or_init(|| {
            let (path, source) = locate()?;
            let version = probe_version(&path);
            let pin = crate::version::ay_pinned_commit().map_err(|e| format!("{e:#}"));
            Ok(ExternalAy::new(path, source, version, pin))
        })
        .as_ref()
        .map_err(Clone::clone)
}

/// Mirror `--allow-unpinned-ay`. Called once per session construction.
pub(crate) fn set_allow_unpinned(allow: bool) {
    ALLOW_UNPINNED_FROM_ARGS.store(allow, Ordering::SeqCst);
}

fn env_allows_unpinned(value: Option<OsString>) -> bool {
    value.is_some_and(|value| value == "1")
}

/// Which spelling allowed an unpinned solver, if either did.
fn allowed_by() -> Option<&'static str> {
    if ALLOW_UNPINNED_FROM_ARGS.load(Ordering::SeqCst) {
        Some(ALLOW_UNPINNED_FLAG)
    } else if env_allows_unpinned(std::env::var_os(ALLOW_UNPINNED_ENV)) {
        Some("TRUST_MC_ALLOW_UNPINNED_AY=1")
    } else {
        None
    }
}

/// The `ay` binary to spawn: located, and either the pinned commit or
/// explicitly allowed. Every subprocess call site goes through here.
pub(crate) fn pinned_ay() -> anyhow::Result<PathBuf> {
    let ay = inspect().map_err(anyhow::Error::msg)?;
    let allowed_by = allowed_by();
    match ay.decision(allowed_by.is_some()) {
        Decision::Use => Ok(ay.path.clone()),
        Decision::UseUnpinned => {
            UNPINNED_ACCEPTED.store(true, Ordering::SeqCst);
            WARNED.call_once(|| eprintln!("{}", ay.warning(allowed_by.unwrap_or_default())));
            Ok(ay.path.clone())
        }
        Decision::Refuse => Err(anyhow::Error::msg(ay.refusal())),
    }
}

/// The `-t` (milliseconds) an `ay` child gets from the budget the driver kills
/// it at: the budget less a twentieth (at most 1 s), never zero (`ay` reads
/// `-t 0` as no limit).
///
/// It bounds an ORPHAN. Every timeout-guarded child leads its own process group
/// (`session::process`), so a SIGKILL of the driver's group -- the loop-contract
/// retry parent's timeout, an outer runner's `killpg` -- never reaches it. On
/// Linux the spawn's death signal kills it with its driver; elsewhere this
/// deadline is its only bound (measured 2026-10-01: an external CHC fallback
/// started without `-t` was alive 120 s after its driver, at 1.6 GB RSS; the
/// SMT cover check recorded an orphan at 2h22m before it got one).
///
/// On an undecided query the driver's kill at the budget still comes first:
/// `ay` stops about 2 s past `-t` (`ay help z3`: one wall-clock watchdog, then a
/// clean-shutdown grace before the hard exit; measured 2026-10-02, `ay --memory
/// 20654 -t 14250` on an undecided CHC input exited `unknown` at 17.5-18.8 s,
/// the grace plus a 12-16 GB worker's teardown). `-t` is not only a watchdog,
/// though: it arms ay's cooperative executor deadline, and on CHC input it sets
/// the adaptive portfolio's budget (95% of what is left of it, where no `-t`
/// means an unbudgeted portfolio).
pub(crate) fn orphan_deadline_ms(budget: Duration) -> u128 {
    let ms = budget.as_millis();
    ms.saturating_sub((ms / 20).min(1000)).max(1)
}

/// Has this process handed an off-pin `ay` to a caller (under
/// `--allow-unpinned-ay`)? From then on every harness is demoted and marked.
pub(crate) fn unpinned_solver_accepted() -> bool {
    UNPINNED_ACCEPTED.load(Ordering::SeqCst)
}

/// The marker to print for every harness once an off-pin binary was accepted.
fn accepted_unpinned_marker() -> Option<String> {
    if !unpinned_solver_accepted() {
        return None;
    }
    INSPECTED.get().and_then(|inspected| inspected.as_ref().ok()).map(ExternalAy::marker)
}

/// If this process accepted an off-pin `ay`, demote a success to UNVALIDATED
/// and return the marker line to print. Failures keep their verdict: the demotion
/// exists so that a clean `SUCCESSFUL` is never printed on an unattributable
/// solver, and a failing harness already exits non-zero.
pub(crate) fn demote_for_unpinned_solver(
    result: &mut VerificationResult,
    should_panic: bool,
) -> Option<String> {
    apply_unpinned_demotion(result, should_panic, accepted_unpinned_marker())
}

fn apply_unpinned_demotion(
    result: &mut VerificationResult,
    should_panic: bool,
    marker: Option<String>,
) -> Option<String> {
    let marker = marker?;
    if is_effective_manual_success(result.status, should_panic, result.failed_properties) {
        result.validation_status = ValidationStatus::Unvalidated;
    }
    Some(marker)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::test_result;
    use crate::verification_result::{
        FailedProperties, HarnessFeasibility, VerificationStatus, format_result,
    };

    /// The orphan bound sits inside the budget the driver kills the child at,
    /// and is never `-t 0` (which `ay` reads as no limit).
    #[test]
    fn the_orphan_deadline_sits_inside_its_budget() {
        assert_eq!(orphan_deadline_ms(Duration::from_secs(45)), 44_000);
        assert_eq!(orphan_deadline_ms(Duration::from_secs(10)), 9_500);
        assert_eq!(orphan_deadline_ms(Duration::from_millis(400)), 380);
        assert_eq!(orphan_deadline_ms(Duration::from_millis(1)), 1);
        assert_eq!(orphan_deadline_ms(Duration::ZERO), 1);
        for ms in [1u64, 19, 20, 999, 1_000, 20_000, 60_000, 600_000] {
            let limit = orphan_deadline_ms(Duration::from_millis(ms));
            assert!(limit >= 1 && limit <= u128::from(ms.max(1)), "{ms} -> {limit}");
        }
    }

    /// Every `ay` child the driver spawns carries a `-t` of its own, so none
    /// can outlive a SIGKILLed driver unbounded on a host without
    /// `PR_SET_PDEATHSIG` (see [`orphan_deadline_ms`]). Until 2026-10-02 the
    /// BMC lane's harness reachability probe and the CHC cover check had none,
    /// beside an external CHC fallback measured alive 120 s after its driver.
    ///
    /// Reads the source of every file that asks for the pinned binary: each
    /// `Command::new(` on the located `ay` path must be given a `"-t"` before
    /// the `run_piped_with_timeout(` that runs it.
    #[test]
    fn every_ay_subprocess_carries_its_own_deadline() {
        fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
            for entry in std::fs::read_dir(dir).expect("read src dir").flatten() {
                let path = entry.path();
                if path.is_dir() {
                    rust_files(&path, out);
                } else if path.extension().is_some_and(|ext| ext == "rs") {
                    out.push(path);
                }
            }
        }
        let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut files = Vec::new();
        rust_files(&src, &mut files);
        files.sort();
        let (mut sites, mut unbounded) = (0usize, Vec::new());
        for file in &files {
            let text = std::fs::read_to_string(file).expect("read source");
            if file.ends_with("ay_binary.rs") || !text.contains("ay_binary::pinned_ay()") {
                continue;
            }
            for (start, _) in text.match_indices("Command::new(") {
                let rest = &text[start..];
                let arg = &rest["Command::new(".len()..rest.find(')').expect("closing paren")];
                if !(arg.contains("ay_path") || arg.contains("solver_path")) {
                    continue;
                }
                sites += 1;
                let line = text[..start].matches('\n').count() + 1;
                match rest.find("run_piped_with_timeout(") {
                    Some(run) if rest[..run].contains("\"-t\"") => {}
                    _ => unbounded.push(format!("{}:{line}", file.display())),
                }
            }
        }
        assert!(sites >= 6, "only {sites} ay spawn sites found; the scan no longer sees them");
        assert!(unbounded.is_empty(), "ay children without their own -t: {unbounded:?}");
    }

    const PIN: &str = "94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322";
    const OLD: &str = "dd4de9e94e0bb94a458641c7e5aa814c8aeadf59";

    fn line(commit: &str) -> String {
        format!("ay 0.26.0+build.9281.{commit}@2026-09-11T02:47:31Z")
    }

    #[test]
    fn build_stamps_from_real_ay_version_lines_parse() {
        for (text, commit) in [
            (
                "ay 0.13.0+build.8256.dd4de9e94e0bb94a458641c7e5aa814c8aeadf59@2026-08-21T02:14:15Z",
                OLD,
            ),
            (
                "ay 0.23.0+build.9281.870b1be06a2452d9ae0c72f21cdfcc23b98a7b54@2026-09-08T22:41:00Z",
                "870b1be06a2452d9ae0c72f21cdfcc23b98a7b54",
            ),
            (&line(PIN), PIN),
        ] {
            assert_eq!(
                parse_build_stamp(text),
                Some(BuildStamp { commit, dirty: false }),
                "{text}"
            );
        }
        assert_eq!(
            parse_build_stamp(&format!("ay 0.26.0+build.1.{PIN}-dirty@now")),
            Some(BuildStamp { commit: PIN, dirty: true })
        );
        assert_eq!(
            parse_build_stamp(&format!("ay 0.26.0+build.1.{PIN}")),
            Some(BuildStamp { commit: PIN, dirty: false })
        );
    }

    #[test]
    fn malformed_build_stamps_do_not_parse() {
        let upper = PIN.to_ascii_uppercase();
        for text in [
            "ay 0.26.0".to_string(),
            "".to_string(),
            "ay 0.26.0+build.9281.abcdef@now".to_string(),
            format!("ay 0.26.0+build.{PIN}@now"),
            format!("ay 0.26.0+build.x1.{PIN}@now"),
            format!("ay 0.26.0+build..{PIN}@now"),
            format!("ay 0.26.0+build.1.{PIN}0@now"),
            format!("ay 0.26.0+build.1.{upper}@now"),
            format!("ay 0.26.0+build.1.{PIN}-dirtyish"),
            format!("ay 0.26.0+build.1.{PIN}zz"),
        ] {
            assert_eq!(parse_build_stamp(&text), None, "{text}");
        }
    }

    #[test]
    fn pin_status_covers_every_shape() {
        let pin = Ok(PIN);
        assert_eq!(PinStatus::evaluate(Some(&line(PIN)), pin), PinStatus::Matched);
        assert_eq!(
            PinStatus::evaluate(Some(&line(OLD)), pin),
            PinStatus::OtherCommit { commit: OLD.to_string() }
        );
        assert_eq!(
            PinStatus::evaluate(Some(&format!("ay 0.26.0+build.1.{PIN}-dirty@now")), pin),
            PinStatus::DirtyBuild { commit: PIN.to_string() }
        );
        assert_eq!(PinStatus::evaluate(Some("ay 0.26.0"), pin), PinStatus::Unstamped);
        assert_eq!(PinStatus::evaluate(None, pin), PinStatus::NoVersion);
        assert_eq!(
            PinStatus::evaluate(Some(&line(PIN)), Err("no manifest")),
            PinStatus::PinUnavailable { reason: "no manifest".to_string() }
        );
    }

    #[test]
    fn only_the_pinned_commit_is_used_without_permission() {
        let off_pin = [
            PinStatus::OtherCommit { commit: OLD.to_string() },
            PinStatus::DirtyBuild { commit: PIN.to_string() },
            PinStatus::Unstamped,
            PinStatus::NoVersion,
            PinStatus::PinUnavailable { reason: "x".to_string() },
        ];
        assert_eq!(decide(&PinStatus::Matched, false), Decision::Use);
        assert_eq!(decide(&PinStatus::Matched, true), Decision::Use);
        for status in &off_pin {
            assert_eq!(decide(status, false), Decision::Refuse, "{status:?}");
            assert_eq!(decide(status, true), Decision::UseUnpinned, "{status:?}");
        }
    }

    #[test]
    fn only_the_value_1_allows_an_unpinned_solver_from_the_environment() {
        assert!(env_allows_unpinned(Some(OsString::from("1"))));
        for value in ["", "0", "true", "yes", " 1"] {
            assert!(!env_allows_unpinned(Some(OsString::from(value))), "{value:?}");
        }
        assert!(!env_allows_unpinned(None));
    }

    pub(super) fn fake_binary(dir: &Path, name: &str) -> PathBuf {
        let path = dir.join(name);
        std::fs::write(&path, "#!/bin/sh\necho ay\n").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        path
    }

    #[test]
    fn the_override_wins_over_path_and_never_falls_back_to_it() {
        let dir = tempfile::TempDir::new().unwrap();
        let chosen = fake_binary(dir.path(), "chosen-ay");
        let on_path = fake_binary(dir.path(), "path-ay");

        let found =
            locate_with(Some(chosen.clone().into_os_string()), None, || Some(on_path.clone()));
        assert_eq!(found, Ok((chosen, AySource::Override)));

        // A broken override is an error naming the variable, not a quiet PATH lookup.
        let missing = dir.path().join("does-not-exist");
        let err =
            locate_with(Some(missing.clone().into_os_string()), None, || Some(on_path.clone()))
                .unwrap_err();
        assert!(err.contains(AY_BIN_ENV) && err.contains(&missing.display().to_string()), "{err}");

        let not_executable = dir.path().join("plain-file");
        std::fs::write(&not_executable, "").unwrap();
        #[cfg(unix)]
        assert!(locate_with(Some(not_executable.into_os_string()), None, || None).is_err());

        // Empty means unset.
        assert_eq!(
            locate_with(Some(OsString::new()), None, || Some(on_path.clone())),
            Ok((on_path.clone(), AySource::Path))
        );
        assert_eq!(
            locate_with(None, None, || Some(on_path.clone())),
            Ok((on_path, AySource::Path))
        );

        let err = locate_with(None, None, || None).unwrap_err();
        assert!(err.contains("not found in PATH") && err.contains(AY_BIN_ENV), "{err}");
    }

    #[test]
    fn the_refusal_names_the_binary_its_version_the_pin_and_the_fix() {
        let ay = ExternalAy::new(
            PathBuf::from("/opt/store/bin/ay"),
            AySource::Path,
            Some(line(OLD)),
            Ok(PIN.to_string()),
        );
        let text = ay.refusal();
        for needle in [
            "/opt/store/bin/ay (found on PATH)",
            &line(OLD),
            &format!("pinned:   {PIN}"),
            &format!("built from AY commit {OLD}"),
            &unpinned_ay_fix(PIN),
            "--allow-unpinned-ay",
            "TRUST_MC_ALLOW_UNPINNED_AY=1",
            "TRUST_MC_AY_BIN=<ay checkout>/target/release/ay",
        ] {
            assert!(text.contains(needle), "missing {needle:?} in:\n{text}");
        }
        assert_eq!(ay.marker(), format!("[AY:SOLVER_PIN_MISMATCH:found={OLD}:pin={PIN}]"));

        let silent =
            ExternalAy::new(PathBuf::from("ay"), AySource::Override, None, Ok(PIN.to_string()));
        assert!(silent.refusal().contains("(from $TRUST_MC_AY_BIN)"));
        assert!(silent.refusal().contains("did not answer `ay --version`"));
        assert_eq!(silent.marker(), format!("[AY:SOLVER_PIN_MISMATCH:found=no-version:pin={PIN}]"));

        let unstamped = ExternalAy::new(
            PathBuf::from("ay"),
            AySource::Path,
            Some("ay 0.26.0".to_string()),
            Err("parse error".to_string()),
        );
        assert!(unstamped.marker().ends_with("found=unstamped:pin=unavailable]"));
        assert!(unstamped.refusal().contains("unavailable (parse error)"));
    }

    #[test]
    fn an_accepted_unpinned_solver_never_leaves_a_clean_successful() {
        let marker = || Some("[AY:SOLVER_PIN_MISMATCH:found=x:pin=y]".to_string());

        let mut success = test_result(VerificationStatus::Success, FailedProperties::None);
        assert_eq!(apply_unpinned_demotion(&mut success, false, marker()), marker());
        assert_eq!(success.validation_status, ValidationStatus::Unvalidated);
        let rendered = format_result(
            &[],
            success.status,
            false,
            success.failed_properties,
            true,
            success.validation_status,
            None,
            HarnessFeasibility::Undetermined,
            false,
        );
        assert!(rendered.contains("SUCCESSFUL (UNVALIDATED)"), "{rendered}");

        // A should_panic harness that panicked as expected is a success too.
        let mut expected_panic =
            test_result(VerificationStatus::Failure, FailedProperties::PanicsOnly);
        apply_unpinned_demotion(&mut expected_panic, true, marker());
        assert_eq!(expected_panic.validation_status, ValidationStatus::Unvalidated);

        // A failure keeps its verdict but still carries the marker.
        let mut failure = test_result(VerificationStatus::Failure, FailedProperties::Other);
        assert_eq!(apply_unpinned_demotion(&mut failure, false, marker()), marker());
        assert_eq!(failure.validation_status, ValidationStatus::Validated);

        // Nothing accepted: nothing changes.
        let mut clean = test_result(VerificationStatus::Success, FailedProperties::None);
        assert_eq!(apply_unpinned_demotion(&mut clean, false, None), None);
        assert_eq!(clean.validation_status, ValidationStatus::Validated);
    }

    #[test]
    fn the_declared_pin_this_build_compares_against_is_a_full_commit() {
        let pin = crate::version::ay_pinned_commit().unwrap();
        assert_eq!(pin.len(), 40, "{pin}");
        assert!(pin.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)), "{pin}");
    }
}
