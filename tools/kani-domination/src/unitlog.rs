// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The per-unit driver log: everything a row was scored from, in one file,
//! so a row can be audited after the fact and re-scored (`rescore`) under a
//! newer scorer without re-running the corpus.
//!
//! Layout: a `key: value` header (the identity of the unit, the exact argv,
//! cwd and environment, the exit code and timings, and the byte length of
//! every section that follows), then the sections in a fixed order, each
//! introduced by its own `=== NAME ===` line and followed by exactly the
//! number of bytes the header declared:
//!
//! ```text
//! === EXPECTED ===          (only when the unit has an expected file)
//! === STDOUT ===
//! === STDERR ===
//! === FIRST ATTEMPT STDOUT (killed by outer watchdog) ===   (retried units)
//! === FIRST ATTEMPT STDERR (killed by outer watchdog) ===
//! === END ===
//! ```
//!
//! The declared lengths are what the reader trusts, so a driver that prints
//! a line looking like a separator cannot corrupt the split, and a truncated
//! file is refused rather than partially read.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::{Context, Result, bail};

use crate::model::{Engine, Verdict};

/// The log layout version; bumped when the header or section set changes.
pub const FORMAT_VERSION: u32 = 1;

const BANNER: &str = "# kani-domination unit log";

/// One unit's log, as written by `run` and read back by `rescore`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnitLog {
    /// The scorer the row was written under (`model::SCORER_VERSION`).
    pub scorer_version: u32,
    pub engine: Engine,
    /// The compiler route of a trust-mc unit (`dev-cli` / `trustc`, the row's
    /// `route`); absent on Kani units and on logs written before `--route`.
    pub route: Option<String>,
    pub suite: String,
    /// Suite-relative POSIX path (`TestResult::file`).
    pub file: String,
    pub oracle: Verdict,
    pub is_cargo: bool,
    pub check_fail: bool,
    /// Upstream compiletest never runs this unit (`TestResult::upstream_ignored`).
    /// Written since scorer version 4; a log without the key reads as
    /// compiletest's path rule on `suite`/`file`, so an older log tags exactly
    /// the units its run would have tagged had the field existed.
    pub upstream_ignored: bool,
    /// The program and every argument, in order.
    pub argv: Vec<String>,
    pub cwd: Option<String>,
    /// Variables set on the child, in the order the command set them.
    pub env_set: Vec<(String, String)>,
    /// Variables removed from the child's environment.
    pub env_removed: Vec<String>,
    /// The child could not be spawned; the sections are empty.
    pub spawn_error: Option<String>,
    /// `None` = died on a signal (a watchdog kill included).
    pub exit_code: Option<i32>,
    pub timed_out: bool,
    pub retried_after_outer_timeout: bool,
    pub wall_ms: u64,
    pub max_rss_kb: u64,
    pub tree_peak_rss_kb: Option<u64>,
    pub expected_path: Option<String>,
    /// The expected file's content as read at run time.
    pub expected: Option<String>,
    /// The classified attempt's output.
    pub stdout: String,
    pub stderr: String,
    /// The outer-watchdog-killed first attempt's `(stdout, stderr)`, kept
    /// after the classified attempt's when the unit was retried.
    pub first_attempt: Option<(String, String)>,
}

/// `<rel with every '/' as "__">.log`.
pub fn log_file_name(rel: &str) -> String {
    format!("{}.log", rel.replace('/', "__"))
}

fn kind_str(is_cargo: bool) -> &'static str {
    if is_cargo { "cargo" } else { "single-file" }
}

fn verdict_str(v: Verdict) -> &'static str {
    match v {
        Verdict::Success => "success",
        Verdict::Fail => "fail",
        Verdict::Unknown => "unknown",
    }
}

fn parse_verdict(s: &str) -> Result<Verdict> {
    Ok(match s {
        "success" => Verdict::Success,
        "fail" => Verdict::Fail,
        "unknown" => Verdict::Unknown,
        other => bail!("unknown oracle `{other}`"),
    })
}

fn parse_engine(s: &str) -> Result<Engine> {
    Ok(match s {
        "trust-mc" => Engine::TrustMc,
        "kani" => Engine::Kani,
        other => bail!("unknown engine `{other}`"),
    })
}

fn opt<T: std::fmt::Display>(v: Option<T>) -> String {
    v.map(|x| x.to_string()).unwrap_or_else(|| "none".into())
}

/// The log's bytes.
pub fn render(log: &UnitLog) -> Vec<u8> {
    let mut o = String::new();
    o.push_str(BANNER);
    o.push('\n');
    let mut line = |k: &str, v: String| {
        o.push_str(k);
        o.push_str(": ");
        o.push_str(&v);
        o.push('\n');
    };
    line("format", FORMAT_VERSION.to_string());
    line("scorer_version", log.scorer_version.to_string());
    line("engine", log.engine.as_str().to_string());
    if let Some(route) = &log.route {
        line("route", route.clone());
    }
    line("suite", log.suite.clone());
    line("file", log.file.clone());
    line("oracle", verdict_str(log.oracle).to_string());
    line("kind", kind_str(log.is_cargo).to_string());
    line("check_fail", log.check_fail.to_string());
    line("upstream_ignored", log.upstream_ignored.to_string());
    line("argv", serde_json::to_string(&log.argv).unwrap_or_default());
    line("cwd", opt(log.cwd.as_deref()));
    let env: BTreeMap<&str, &str> =
        log.env_set.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();
    line("env_set", serde_json::to_string(&env).unwrap_or_default());
    line("env_removed", serde_json::to_string(&log.env_removed).unwrap_or_default());
    if let Some(err) = &log.spawn_error {
        line("spawn_error", err.replace('\n', " "));
    }
    line("exit_code", log.exit_code.map(|c| c.to_string()).unwrap_or_else(|| "signal".into()));
    line("timed_out", log.timed_out.to_string());
    line("retried_after_outer_timeout", log.retried_after_outer_timeout.to_string());
    line("wall_ms", log.wall_ms.to_string());
    line("max_rss_kb", log.max_rss_kb.to_string());
    line("tree_peak_rss_kb", opt(log.tree_peak_rss_kb));
    line("expected_path", opt(log.expected_path.as_deref()));
    line("expected_bytes", opt(log.expected.as_ref().map(|e| e.len())));
    line("stdout_bytes", log.stdout.len().to_string());
    line("stderr_bytes", log.stderr.len().to_string());
    if let Some((so, se)) = &log.first_attempt {
        line("first_attempt_stdout_bytes", so.len().to_string());
        line("first_attempt_stderr_bytes", se.len().to_string());
    }
    let mut section = |name: &str, body: &str| {
        o.push_str("=== ");
        o.push_str(name);
        o.push_str(" ===\n");
        o.push_str(body);
        o.push('\n');
    };
    if let Some(exp) = &log.expected {
        section("EXPECTED", exp);
    }
    section("STDOUT", &log.stdout);
    section("STDERR", &log.stderr);
    if let Some((so, se)) = &log.first_attempt {
        section("FIRST ATTEMPT STDOUT (killed by outer watchdog)", so);
        section("FIRST ATTEMPT STDERR (killed by outer watchdog)", se);
    }
    o.push_str("=== END ===\n");
    o.into_bytes()
}

/// Write the log at `path`, creating its directories and overwriting an
/// earlier log of the same unit.
pub fn write(path: &Path, log: &UnitLog) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(path, render(log))
}

/// Read a log back; refuses anything whose sections do not match the lengths
/// its header declares.
pub fn read(path: &Path) -> Result<UnitLog> {
    let bytes = std::fs::read(path).with_context(|| format!("reading unit log {}", path.display()))?;
    parse(&bytes).with_context(|| format!("parsing unit log {}", path.display()))
}

/// Parse a rendered log.
pub fn parse(bytes: &[u8]) -> Result<UnitLog> {
    // Header: lines up to the first section marker.
    let mut header: BTreeMap<String, String> = BTreeMap::new();
    let mut pos = 0usize;
    let mut first = true;
    loop {
        let rest = &bytes[pos..];
        let Some(nl) = rest.iter().position(|b| *b == b'\n') else {
            bail!("unterminated header");
        };
        let line = std::str::from_utf8(&rest[..nl]).context("non-UTF-8 header line")?;
        if line.starts_with("=== ") {
            break;
        }
        pos += nl + 1;
        if first {
            first = false;
            if line != BANNER {
                bail!("not a unit log (banner `{line}`)");
            }
            continue;
        }
        let Some((k, v)) = line.split_once(": ") else {
            bail!("malformed header line `{line}`");
        };
        header.insert(k.to_string(), v.to_string());
    }
    let get = |k: &str| -> Result<&str> {
        header.get(k).map(String::as_str).with_context(|| format!("header lacks `{k}`"))
    };
    let num = |k: &str| -> Result<u64> {
        get(k)?.parse::<u64>().with_context(|| format!("header `{k}` is not a number"))
    };
    let opt_num = |k: &str| -> Result<Option<u64>> {
        match get(k)? {
            "none" => Ok(None),
            v => Ok(Some(v.parse::<u64>().with_context(|| format!("header `{k}` is not a number"))?)),
        }
    };
    let flag = |k: &str| -> Result<bool> {
        match get(k)? {
            "true" => Ok(true),
            "false" => Ok(false),
            v => bail!("header `{k}` is `{v}`, not true/false"),
        }
    };
    let format: u64 = num("format")?;
    if format != u64::from(FORMAT_VERSION) {
        bail!("unit log format {format}; this tool reads format {FORMAT_VERSION}");
    }

    // Sections, in order, each exactly as long as the header says.
    let mut take = |name: &str, len: usize| -> Result<String> {
        let marker = format!("=== {name} ===\n");
        let rest = &bytes[pos..];
        if !rest.starts_with(marker.as_bytes()) {
            bail!("expected section `{name}` at byte {pos}");
        }
        let start = pos + marker.len();
        let end = start + len;
        if end + 1 > bytes.len() || bytes[end] != b'\n' {
            bail!("section `{name}` is shorter than the {len} bytes declared");
        }
        pos = end + 1;
        Ok(String::from_utf8_lossy(&bytes[start..end]).into_owned())
    };
    let expected = match opt_num("expected_bytes")? {
        Some(n) => Some(take("EXPECTED", n as usize)?),
        None => None,
    };
    let stdout = take("STDOUT", num("stdout_bytes")? as usize)?;
    let stderr = take("STDERR", num("stderr_bytes")? as usize)?;
    let first_attempt = match header.get("first_attempt_stdout_bytes") {
        Some(_) => {
            let so = take(
                "FIRST ATTEMPT STDOUT (killed by outer watchdog)",
                num("first_attempt_stdout_bytes")? as usize,
            )?;
            let se = take(
                "FIRST ATTEMPT STDERR (killed by outer watchdog)",
                num("first_attempt_stderr_bytes")? as usize,
            )?;
            Some((so, se))
        }
        None => None,
    };
    if !bytes[pos..].starts_with(b"=== END ===\n") {
        bail!("missing `=== END ===` after the declared sections");
    }

    let env_set: BTreeMap<String, String> =
        serde_json::from_str(get("env_set")?).context("header `env_set` is not a JSON object")?;
    let suite = get("suite")?.to_string();
    let file = get("file")?.to_string();
    // Written since scorer version 4. An older log tags by compiletest's
    // path rule, the only source its run had.
    let upstream_ignored = match header.get("upstream_ignored") {
        Some(_) => flag("upstream_ignored")?,
        None => crate::discover::compiletest_ignores(&suite, &file),
    };
    Ok(UnitLog {
        scorer_version: num("scorer_version")? as u32,
        engine: parse_engine(get("engine")?)?,
        route: header.get("route").cloned(),
        suite,
        file,
        oracle: parse_verdict(get("oracle")?)?,
        is_cargo: match get("kind")? {
            "cargo" => true,
            "single-file" => false,
            k => bail!("unknown kind `{k}`"),
        },
        check_fail: flag("check_fail")?,
        upstream_ignored,
        argv: serde_json::from_str(get("argv")?).context("header `argv` is not a JSON array")?,
        cwd: match get("cwd")? {
            "none" => None,
            v => Some(v.to_string()),
        },
        env_set: env_set.into_iter().collect(),
        env_removed: serde_json::from_str(get("env_removed")?)
            .context("header `env_removed` is not a JSON array")?,
        spawn_error: header.get("spawn_error").cloned(),
        exit_code: match get("exit_code")? {
            "signal" => None,
            v => Some(v.parse::<i32>().context("header `exit_code` is not a number")?),
        },
        timed_out: flag("timed_out")?,
        retried_after_outer_timeout: flag("retried_after_outer_timeout")?,
        wall_ms: num("wall_ms")?,
        max_rss_kb: num("max_rss_kb")?,
        tree_peak_rss_kb: opt_num("tree_peak_rss_kb")?,
        expected_path: match get("expected_path")? {
            "none" => None,
            v => Some(v.to_string()),
        },
        expected,
        stdout,
        stderr,
        first_attempt,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> UnitLog {
        UnitLog {
            scorer_version: 2,
            engine: Engine::TrustMc,
            route: Some("trustc".into()),
            suite: "kani".into(),
            file: "Foo/bar.rs".into(),
            oracle: Verdict::Fail,
            is_cargo: false,
            check_fail: true,
            upstream_ignored: false,
            argv: vec!["/b/trust-mc-driver".into(), "tests/kani/Foo/bar.rs".into(), "-Z".into()],
            cwd: Some("/corpus".into()),
            env_set: vec![("PATH".into(), "/a:/b".into()), ("TRUST_MC_SYSROOT".into(), "/s".into())],
            env_removed: vec!["RUSTFLAGS".into()],
            spawn_error: None,
            exit_code: Some(1),
            timed_out: false,
            retried_after_outer_timeout: true,
            wall_ms: 1234,
            max_rss_kb: 5678,
            tree_peak_rss_kb: Some(9999),
            expected_path: Some("/corpus/tests/kani/Foo/expected".into()),
            expected: Some("VERIFICATION:- FAILED\n".into()),
            // A line that looks like a separator must survive the round trip.
            stdout: "Checking harness a...\n=== STDERR ===\n[AY:CTREX_CAT:Genuine]\nVERIFICATION:- FAILED\n".into(),
            stderr: "warning: x\n".into(),
            first_attempt: Some(("partial".into(), String::new())),
        }
    }

    /// Every field survives write -> read, section separators inside the
    /// output included, and the sections carry the exact bytes.
    #[test]
    fn round_trips_every_field() {
        let log = sample();
        let bytes = render(&log);
        let text = String::from_utf8(bytes.clone()).unwrap();
        assert!(text.starts_with("# kani-domination unit log"));
        assert!(text.contains("\n=== STDOUT ===\n"));
        assert!(text.contains("\n=== STDERR ===\n"));
        assert!(text.contains("\n=== EXPECTED ===\n"));
        assert!(text.ends_with("=== END ===\n"));
        assert_eq!(parse(&bytes).unwrap(), log);

        // No expected file, no retry, spawn failure, signal death.
        let mut bare = sample();
        bare.expected = None;
        bare.expected_path = None;
        bare.first_attempt = None;
        bare.retried_after_outer_timeout = false;
        bare.exit_code = None;
        bare.tree_peak_rss_kb = None;
        bare.cwd = None;
        bare.route = None;
        bare.spawn_error = Some("No such file".into());
        bare.stdout.clear();
        bare.stderr.clear();
        let bytes = render(&bare);
        assert!(!String::from_utf8_lossy(&bytes).contains("=== EXPECTED ==="));
        assert_eq!(parse(&bytes).unwrap(), bare);
    }

    /// A truncated or edited log is refused, never partially read.
    #[test]
    fn refuses_a_log_whose_sections_disagree_with_the_header() {
        let bytes = render(&sample());
        assert!(parse(&bytes[..bytes.len() - 20]).is_err());
        let edited = String::from_utf8(bytes).unwrap().replace("stdout_bytes: ", "stdout_bytes: 1");
        assert!(parse(edited.as_bytes()).is_err());
        assert!(parse(b"not a log\n").is_err());
    }

    /// `upstream_ignored` round-trips, and a log written before the header
    /// existed reads as compiletest's path rule on its own suite and file.
    #[test]
    fn upstream_ignored_reads_the_path_rule_on_an_older_log() {
        let mut log = sample();
        log.upstream_ignored = true;
        assert_eq!(parse(&render(&log)).unwrap(), log);
        let strip = |l: &UnitLog| {
            String::from_utf8(render(l)).unwrap().replace(&format!("upstream_ignored: {}\n", l.upstream_ignored), "")
        };
        let mut older = sample();
        older.file = "Foo/fixme_bar.rs".into();
        assert!(parse(strip(&older).as_bytes()).unwrap().upstream_ignored);
        assert!(!parse(strip(&sample()).as_bytes()).unwrap().upstream_ignored);
    }

    #[test]
    fn log_names_flatten_paths() {
        assert_eq!(log_file_name("Foo/bar/baz.rs"), "Foo__bar__baz.rs.log");
        assert_eq!(log_file_name("tokio-proofs/expected"), "tokio-proofs__expected.log");
    }

    #[test]
    fn write_creates_directories_and_overwrites() {
        let dir = std::env::temp_dir().join(format!("kd-unitlog-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let path = dir.join("logs/run/kani").join(log_file_name("Foo/bar.rs"));
        write(&path, &sample()).unwrap();
        let mut again = sample();
        again.stdout = "second run\n".into();
        write(&path, &again).unwrap();
        assert_eq!(read(&path).unwrap(), again);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
