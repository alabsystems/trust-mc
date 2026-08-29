// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-mc example [NAME] [PATH]`: sample harnesses that behave the way they
//! say. Every source below was run through the engine before it was added, and
//! its recorded outcome is part of the entry, so the catalog doubles as a
//! smoke suite for an installation.

use std::ffi::OsString;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use super::{Fail, Front};

/// What the engine reports for an example when everything is installed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// `VERIFICATION:- SUCCESSFUL` for every harness, exit 0.
    Proves,
    /// `VERIFICATION:- FAILED` with a genuine counterexample, exit 1.
    Fails,
}

impl Outcome {
    fn label(self) -> &'static str {
        match self {
            Outcome::Proves => "proves",
            Outcome::Fails => "FAILS (a real bug is found)",
        }
    }
}

pub(crate) struct Example {
    pub(crate) name: &'static str,
    /// One line for `example --list`.
    pub(crate) summary: &'static str,
    pub(crate) outcome: Outcome,
    /// Typical wall-clock on a laptop, to set expectations.
    pub(crate) seconds: &'static str,
    pub(crate) source: &'static str,
}

pub(crate) const DEFAULT: &str = "basic";

/// The catalog. Order is the order `--list` prints; `basic` is the default.
pub(crate) const EXAMPLES: &[Example] = &[
    Example {
        name: "basic",
        summary: "two loop-free harnesses over every u32 / every pair of u8",
        outcome: Outcome::Proves,
        seconds: "< 1",
        source: BASIC,
    },
    Example {
        name: "bug",
        summary: "u8 addition that can overflow — a counterexample with a location",
        outcome: Outcome::Fails,
        seconds: "< 1",
        source: BUG,
    },
    Example {
        name: "bounds",
        summary: "an off-by-one index into a 4-element array (safe code)",
        outcome: Outcome::Fails,
        seconds: "~1",
        source: BOUNDS,
    },
    Example {
        name: "unsafe",
        summary: "a raw-pointer read one past the end (unsafe code)",
        outcome: Outcome::Fails,
        seconds: "~5",
        source: UNSAFE,
    },
    Example {
        name: "assume",
        summary: "a precondition stated with kani::assume, then a postcondition",
        outcome: Outcome::Proves,
        seconds: "< 1",
        source: ASSUME,
    },
    Example {
        name: "cover",
        summary: "kani::cover! shows both branches of a clamp are reachable",
        outcome: Outcome::Proves,
        seconds: "< 1",
        source: COVER,
    },
    Example {
        name: "loop",
        summary: "a counting loop with an explicit #[kani::unwind] bound",
        outcome: Outcome::Proves,
        seconds: "~1",
        source: LOOP,
    },
];

pub(crate) fn find(name: &str) -> Option<&'static Example> {
    EXAMPLES.iter().find(|e| e.name == name)
}

/// `trust-mc example [NAME] [PATH] [--list] [--force]`.
pub(crate) fn command(rest: &[OsString]) -> Front<ExitCode> {
    let mut name: Option<String> = None;
    let mut target: Option<PathBuf> = None;
    let mut list = false;
    let mut force = false;

    for arg in rest {
        let text = arg.to_string_lossy();
        match text.as_ref() {
            "--list" | "-l" => list = true,
            "--force" | "-f" => force = true,
            other if other.starts_with('-') => {
                return Err(Fail::usage(format!(
                    "error: `example` does not take {other}\n       {USAGE}"
                )));
            }
            other if name.is_none() && find(other).is_some() => name = Some(other.to_string()),
            other if name.is_none() && target.is_none() && !other.ends_with(".rs") => {
                return Err(Fail::usage(format!(
                    "error: no example named `{other}`\n\n{}",
                    catalog()
                )));
            }
            _ if target.is_none() => target = Some(PathBuf::from(arg)),
            _ => {
                return Err(Fail::usage(format!(
                    "error: `example` writes one file, got a second path {text}\n       {USAGE}"
                )));
            }
        }
    }

    if list {
        print!("{}", catalog());
        return Ok(ExitCode::SUCCESS);
    }

    let name = name.unwrap_or_else(|| DEFAULT.to_string());
    let Some(example) = find(&name) else {
        return Err(Fail::usage(format!("error: no example named `{name}`\n\n{}", catalog())));
    };

    match target {
        None => {
            print!("{}", example.source);
            Ok(ExitCode::SUCCESS)
        }
        Some(path) => {
            if path.exists() && !force {
                return Err(Fail::usage(format!(
                    "error: {} already exists; pass --force to overwrite it",
                    path.display()
                )));
            }
            fs::write(&path, example.source).map_err(|e| {
                Fail::other(format!("error: could not write {}: {e}", path.display()))
            })?;
            println!(
                "wrote {} ({}: {}).\n\nVerify it with:\n\n    trust-mc {}",
                path.display(),
                example.name,
                example.outcome.label(),
                path.display()
            );
            Ok(ExitCode::SUCCESS)
        }
    }
}

const USAGE: &str = "Usage: trust-mc example [NAME] [PATH] [--list] [--force]";

/// The `--list` table.
pub(crate) fn catalog() -> String {
    let mut out = String::from(
        "Examples (trust-mc example <NAME> [PATH]; without PATH the file goes to stdout):\n\n",
    );
    for e in EXAMPLES {
        out.push_str(&format!(
            "  {:<8} {}\n  {:<8} → {}, about {} s{}\n",
            e.name,
            e.summary,
            "",
            e.outcome.label(),
            e.seconds,
            if e.name == DEFAULT { " (default)" } else { "" }
        ));
    }
    out.push_str(
        "\nEach file says at the top what to expect and which flags to try next.\n\
         Run them all, in order, to exercise an installation.\n",
    );
    out
}

// ---------------------------------------------------------------------------
// The sources. Keep each one short, self-explaining, and verified.
// ---------------------------------------------------------------------------

const BASIC: &str = r#"// trust-mc example: basic — PROVES (two harnesses, no loops).
//
//     trust-mc demo.rs                  verify every harness in this file
//     trust-mc --list demo.rs           which harnesses are here?
//     trust-mc --harness double_never_shrinks demo.rs
//     trust-mc --verbose demo.rs        show every stage and the engine command
//
// `kani::any()` yields a symbolic value: each assertion below is proved for
// EVERY input of its type, not for a few samples. Expect two
// "Checking harness ..." blocks ending in VERIFICATION:- SUCCESSFUL, exit 0.

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

const BUG: &str = r#"// trust-mc example: bug — FAILS (a genuine counterexample).
//
//     trust-mc bug.rs
//
// `a + b` overflows for some pair of u8 values. Expect a check
//   "attempt to add with overflow" with Status: FAILURE, located on the
// `a + b` line, the marker [AY:CTREX_CAT:Genuine] (a real counterexample, no
// encoding doubt), VERIFICATION:- FAILED, and exit status 1.
//
// Fix the code (e.g. `a.wrapping_add(b)` or `a.checked_add(b)`), or state the
// precondition in the harness with `kani::assume(a as u16 + b as u16 <= 255)`,
// and the harness turns SUCCESSFUL.

fn add(a: u8, b: u8) -> u8 {
    a + b
}

#[kani::proof]
fn add_never_overflows() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let _ = add(a, b);
}
"#;

const BOUNDS: &str = r#"// trust-mc example: bounds — FAILS (index out of bounds in safe code).
//
//     trust-mc bounds.rs
//
// `next_element` reads a[i + 1]; for i == 3 that is past the end of a
// 4-element array. Expect an "index out of bounds" check with Status: FAILURE,
// [AY:CTREX_CAT:Genuine], VERIFICATION:- FAILED, exit 1. Indexing, arithmetic,
// division and pointer checks are properties trust-mc adds for free — you did
// not have to write an assertion to find this.

/// Returns the element after `i`; off by one when `i` is the last index.
fn next_element(a: &[u32], i: usize) -> u32 {
    a[i + 1]
}

#[kani::proof]
fn next_element_is_in_bounds() {
    let a: [u32; 4] = kani::any();
    let i: usize = kani::any();
    kani::assume(i < a.len());
    let _ = next_element(&a, i);
}
"#;

const UNSAFE: &str = r#"// trust-mc example: unsafe — FAILS (a raw-pointer read past the end).
//
//     trust-mc unsafe.rs
//
// `read_next` reads one element past a 4-byte array when i == a.len() - 1.
// Expect two FAILURE checks — "pointer arithmetic overflow" and
// "dereference failure: pointer NULL" — the marker [AY:CTREX_CAT:Genuine]
// saying the counterexample is real, `** 2 of 6 failed`, and exit status 1.
// trust-mc checks every raw-pointer operation for validity: in bounds,
// aligned, non-null, not freed. You wrote no assertion; these came for free.
//
// This one takes a few seconds: the memory model reasons about every byte of
// the array and about a symbolic index at once.

/// Reads one past the end when `i == a.len() - 1`.
fn read_next(a: &[u8], i: usize) -> u8 {
    unsafe { *a.as_ptr().add(i + 1) }
}

#[kani::proof]
fn read_next_stays_in_bounds() {
    let a: [u8; 4] = kani::any();
    let i: usize = kani::any();
    kani::assume(i < a.len());
    let _ = read_next(&a, i);
}
"#;

const ASSUME: &str = r#"// trust-mc example: assume — PROVES (a precondition and a postcondition).
//
//     trust-mc assume.rs
//
// `estimate_size` asserts its own precondition; the harness assumes it with
// `kani::assume(x < 4096)`, so every remaining input is explored and the
// postcondition `y < 10` is proved. Expect VERIFICATION:- SUCCESSFUL, exit 0.
//
// Delete the `kani::assume` line and run again: the precondition check
// becomes a FAILURE (x >= 4096 is now a legal input), exit 1. That is what
// assumptions are for — and why too many of them prove nothing: see
// `trust-mc example cover`.

fn estimate_size(x: u32) -> u32 {
    assert!(x < 4096, "precondition: x must be below 4096");
    if x < 256 {
        if x < 128 { 1 } else { 3 }
    } else if x < 1024 {
        5
    } else if x < 2048 {
        7
    } else {
        9
    }
}

#[kani::proof]
fn estimate_size_within_bounds() {
    let x: u32 = kani::any();
    kani::assume(x < 4096);
    let y = estimate_size(x);
    assert!(y < 10);
}
"#;

const COVER: &str = r#"// trust-mc example: cover — PROVES, and shows both branches are reachable.
//
//     trust-mc cover.rs
//
// `kani::cover!(cond)` asks "can this condition ever hold here?". Expect the
// two cover checks to be SATISFIED (an input reaches each branch), the
// assertion SUCCESS, VERIFICATION:- SUCCESSFUL, exit 0. A cover that comes back
// UNSATISFIABLE or UNREACHABLE means the harness is over-constrained: the
// proof may be vacuous. Use covers to make sure your assumptions left
// something to verify.

fn clamp_to_byte(x: u32) -> u8 {
    if x > 255 { 255 } else { x as u8 }
}

#[kani::proof]
fn clamp_reaches_both_branches() {
    let x: u32 = kani::any();
    let y = clamp_to_byte(x);
    kani::cover!(y == 255, "the saturating branch is reachable");
    kani::cover!(y < 255, "the identity branch is reachable");
    assert!(u32::from(y) <= x);
}
"#;

const LOOP: &str = r#"// trust-mc example: loop — PROVES (a loop with an explicit unwind bound).
//
//     trust-mc loop.rs
//     trust-mc --unwind 5 loop.rs       the same bound from the command line
//
// By default trust-mc checks harnesses by bounded model checking: each loop is
// unrolled a fixed number of times. With no bound given, that number is 1,
// and an input that needs more iterations fails the "unwinding assertion".
// Here `n <= 4` means at most 4 iterations, so the bound must be 5 (iterations
// plus one for the final exit test). Expect VERIFICATION:- SUCCESSFUL, exit 0.
//
// Try `#[kani::unwind(3)]`: the harness FAILS at the loop header (the bound
// was too small — not a bug in count_up). For loops whose trip count has no
// small bound, see `trust-mc explain chc` (unbounded proofs with --ay-chc).

fn count_up(n: u8) -> u8 {
    let mut i: u8 = 0;
    while i < n {
        i += 1;
    }
    i
}

#[kani::proof]
#[kani::unwind(5)]
fn count_up_returns_n() {
    let n: u8 = kani::any();
    kani::assume(n <= 4);
    assert_eq!(count_up(n), n);
}
"#;

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn names_are_unique_and_the_default_exists() {
        let mut names: Vec<&str> = EXAMPLES.iter().map(|e| e.name).collect();
        names.sort_unstable();
        names.dedup();
        assert_eq!(names.len(), EXAMPLES.len(), "duplicate example names");
        assert!(find(DEFAULT).is_some());
    }

    #[test]
    fn every_example_is_a_self_describing_harness_file() {
        for e in EXAMPLES {
            assert!(e.source.starts_with("// trust-mc example: "), "{}", e.name);
            assert!(e.source.contains(&format!("example: {}", e.name)), "{}", e.name);
            assert!(e.source.contains("#[kani::proof]"), "{}", e.name);
            assert!(e.source.contains("kani::any()"), "{}", e.name);
            let word = match e.outcome {
                Outcome::Proves => "PROVES",
                Outcome::Fails => "FAILS",
            };
            assert!(e.source.contains(word), "{} must announce that it {word}", e.name);
            for line in e.source.lines() {
                assert!(line.len() <= 100, "{}: overlong line: {line}", e.name);
            }
        }
    }

    #[test]
    fn the_default_example_needs_no_unwind_bound() {
        // A first run passes no flags, so the default must be loop-free.
        let code: String = find(DEFAULT)
            .unwrap()
            .source
            .lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        for loop_kw in ["for ", "while ", "loop {"] {
            assert!(!code.contains(loop_kw), "a first run must not need an unwind bound");
        }
        assert_eq!(find(DEFAULT).unwrap().source.matches("#[kani::proof]").count(), 2);
    }

    #[test]
    fn the_loop_example_carries_its_own_bound() {
        let source = find("loop").unwrap().source;
        assert!(source.contains("#[kani::unwind("), "the loop example must be runnable bare");
    }

    #[test]
    fn the_catalog_lists_every_example_with_its_outcome() {
        let table = catalog();
        for e in EXAMPLES {
            assert!(table.contains(e.name), "{}", e.name);
        }
        assert!(table.contains("proves"));
        assert!(table.contains("FAILS"));
        assert!(table.contains("(default)"));
    }

    #[test]
    fn unknown_names_and_stray_flags_are_usage_errors() {
        let err = command(&[OsString::from("nonesuch")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("no example named `nonesuch`"), "{}", err.msg);
        assert!(err.msg.contains("basic"), "the error lists the catalog: {}", err.msg);
        let err = command(&[OsString::from("--bogus")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
    }

    #[test]
    fn writing_refuses_to_clobber_without_force() {
        let dir = std::env::temp_dir().join(format!("trust-mc-example-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("demo.rs");
        std::fs::write(&path, "// existing").unwrap();
        let err = command(&[OsString::from("bug"), path.clone().into_os_string()]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("--force"), "{}", err.msg);
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "// existing");
        command(&[OsString::from("bug"), path.clone().into_os_string(), OsString::from("--force")])
            .unwrap();
        assert!(std::fs::read_to_string(&path).unwrap().contains("add_never_overflows"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
