// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Engine-argument transport through `-Cllvm-args`: the `pct1` channel.
//!
//! # The hazard
//!
//! trust-mc-driver hands the engine its own argv (`--harness`, `--c-lib`, ...)
//! inside `-Cllvm-args=<value>`. rustc parses that option with `parse_list`,
//! which is `value.split_whitespace()` and which appends across repeated
//! `-Cllvm-args` (trust `45dc60873`, `compiler/rustc_session/src/options.rs`
//! lines 1260-1268 and 2702). A token that contains whitespace, such as any path
//! under `~/Library/Application Support`, reaches `sess.opts.cg.llvm_args` split
//! into pieces, and clap in the engine then parses a different command line.
//!
//! # The channel
//!
//! Producer (trust-mc-driver on the Trustc route):
//!
//! 1. The engine argv is a sequence of tokens, one clap argv element each.
//! 2. Each token is written with every character `c` for which
//!    `c == '%' || c.is_whitespace() || c.is_control()` replaced by `%XX`
//!    for each byte of its UTF-8 encoding (uppercase hex).
//! 3. The empty token is written as a lone `%`.
//! 4. The option value is one *group*: the header token
//!    `--trust-mc-engine-args=pct1:<n>` ([`group_header`]), where `<n>` is the
//!    number of engine argv tokens in decimal, followed by exactly those `n`
//!    encoded tokens, joined by single ASCII spaces ([`encode_llvm_args`]).
//!
//! Consumer (the engine, in `CodegenBackend::init`): pass all of
//! `sess.opts.cg.llvm_args` to [`decode_llvm_args`].
//!
//! - A header token claims the `n` tokens after it; only those are decoded,
//!   and the header is dropped. Because rustc concatenates repeated
//!   `-Cllvm-args`, this covers the cargo route, where dependency and
//!   package-local arguments arrive as separate groups, each with its own
//!   header.
//! - Every token outside a group comes back byte for byte. That is the legacy
//!   form (the DevCli route, which never encodes), and it is also any foreign
//!   `-Cllvm-args` token, for example one forwarded from ambient `RUSTFLAGS`: a
//!   literal `%41` in such a token must reach the engine as `%41`, never as `A`.
//! - Anything that starts like a header but is not `pct1:<n>` in canonical
//!   decimal, a group with fewer than `n` tokens left, and a token inside a
//!   group that is not valid `pct1` are all errors. The engine must refuse the
//!   compile rather than guess.
//!
//! Properties the tests pin: an encoded token contains no whitespace, no
//! control character and is never empty, so it survives `split_whitespace` and
//! the `0x1f` separator of `CARGO_ENCODED_RUSTFLAGS`; and
//! `decode(split_whitespace(encode(tokens))) == tokens` for every token list,
//! with foreign tokens before, between and after groups left untouched.
//!
//! An arguments file was considered and rejected. Cargo fingerprints rustflags,
//! so arguments carried inline force a rebuild when they change; a file would
//! need a content-derived name to keep that property. It would also need a
//! lifetime owner, and its own path would have to cross the same
//! whitespace-splitting option.

use std::fmt;

/// Environment variables the trust-mc engine reads from its own process
/// environment that change what it generates: the generation knobs.
///
/// Taken from the `"TRUST_MC_*"` literals in `trust-mc-compiler/src`; the driver
/// test `compiler_route_engine_env_knobs_cover_the_engine_sources` rescans those
/// sources and fails when this list drifts. On the Trustc route no knob may
/// reach the engine: the driver refuses while one is set in its own environment
/// and removes every `TRUST_MC_*` variable from its children, and the
/// trustc-hosted backend refuses to initialize while one is set in *its*
/// environment, whatever put it there (a cargo `[env]` table, a wrapper, a
/// shell). `loop_two_lane` sets one of them (`TRUST_MC_COMPOUND_DECREASES`) on
/// its DevCli retry lane child, so dropping it silently would change what the
/// lane proves; it also sets `TRUST_MC_LOOP_LANE`, which the compiler reads to
/// waive design 5 when its value is `properties` (a value the retry no longer
/// sets; the retry does not run on the Trustc route).
pub const ENGINE_ENV_KNOBS: &[&str] = &[
    "TRUST_MC_CHC_ADMISSION_STATS",
    "TRUST_MC_CHC_MAX_SCALARS_PER_ARRAY",
    "TRUST_MC_CHC_PRUNE_DATATYPES",
    "TRUST_MC_CHC_UNCONSTRAINED_ARGS",
    "TRUST_MC_CHECK_SLOT_LAYOUT",
    "TRUST_MC_COMPOUND_DECREASES",
    "TRUST_MC_FRAME_NARROWING",
    "TRUST_MC_FRAME_STATS",
    "TRUST_MC_LOOP_LANE",
    "TRUST_MC_NO_CALL_UF_TABLE",
    "TRUST_MC_NO_CONST_PROP",
    "TRUST_MC_NO_LOOP_RULE",
    "TRUST_MC_NO_LOST_OBLIGATION_RECOVERY",
    "TRUST_MC_NO_STRAIGHTLINE_DISCHARGE",
    "TRUST_MC_PHASE_TIMING",
    "TRUST_MC_REACH_DEBUG",
    "TRUST_MC_SMT_NODE_BUDGET",
    "TRUST_MC_STRIP_DEAD_ARGS",
    "TRUST_MC_SWITCHINT_WALK_NODE_BUDGET",
];

/// The knobs among `keys` that are set, sorted and deduplicated: what an engine
/// hosted in trustc must refuse, and what the driver refuses before any probe.
pub fn set_engine_env_knobs<I, K>(keys: I) -> Vec<String>
where
    I: IntoIterator<Item = K>,
    K: AsRef<std::ffi::OsStr>,
{
    let mut vars: Vec<String> = keys
        .into_iter()
        .filter_map(|key| key.as_ref().to_str().map(str::to_string))
        .filter(|key| ENGINE_ENV_KNOBS.contains(&key.as_str()))
        .collect();
    vars.sort();
    vars.dedup();
    vars
}

/// Prefix of the header token that opens every `-Cllvm-args` group.
///
/// An engine that does not know the channel rejects the header as an unknown
/// argument, so a stale engine fails closed instead of misreading encoded tokens.
/// Every token with this prefix must be a well-formed header.
pub const LLVM_ARGS_GROUP_PREFIX: &str = "--trust-mc-engine-args=";

/// The only encoding a group header may name, followed by its token count.
pub const LLVM_ARGS_PCT1_SCHEME: &str = "pct1:";

/// The header token of a `pct1` group of `count` engine argv tokens.
pub fn group_header(count: usize) -> String {
    format!("{LLVM_ARGS_GROUP_PREFIX}{LLVM_ARGS_PCT1_SCHEME}{count}")
}

/// The encoding of the empty token.
const EMPTY_TOKEN: &str = "%";

const HEX_UPPER: &[u8; 16] = b"0123456789ABCDEF";

fn needs_escape(c: char) -> bool {
    c == '%' || c.is_whitespace() || c.is_control()
}

/// Encode one engine argv token.
pub fn encode_token(token: &str) -> String {
    if token.is_empty() {
        return EMPTY_TOKEN.to_string();
    }
    let mut out = String::with_capacity(token.len());
    let mut utf8 = [0u8; 4];
    for c in token.chars() {
        if needs_escape(c) {
            for byte in c.encode_utf8(&mut utf8).bytes() {
                out.push('%');
                out.push(char::from(HEX_UPPER[usize::from(byte >> 4)]));
                out.push(char::from(HEX_UPPER[usize::from(byte & 0x0f)]));
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// The `-Cllvm-args` value for an engine argv: the group header naming the token
/// count, then each token encoded.
pub fn encode_llvm_args<I, S>(tokens: I) -> String
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let encoded: Vec<String> = tokens.into_iter().map(|t| encode_token(t.as_ref())).collect();
    let mut value = group_header(encoded.len());
    for token in &encoded {
        value.push(' ');
        value.push_str(token);
    }
    value
}

/// Why an `llvm_args` token is not valid `pct1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineArgsError {
    /// A `%` without two following bytes.
    TruncatedEscape { token: String, offset: usize },
    /// A `%` followed by something other than two hex digits.
    InvalidEscape { token: String, offset: usize },
    /// The decoded bytes are not UTF-8.
    InvalidUtf8 { token: String },
    /// A raw character the producer always escapes.
    UnescapedCharacter { token: String, offset: usize },
    /// A token with [`LLVM_ARGS_GROUP_PREFIX`] that is not `pct1:<n>` in canonical
    /// decimal.
    MalformedGroupHeader { token: String, index: usize },
    /// A group header claims more tokens than follow it.
    TruncatedGroup { header: String, index: usize, expected: usize, available: usize },
}

impl fmt::Display for EngineArgsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TruncatedEscape { token, offset } => {
                write!(f, "pct1 engine argument {token:?}: truncated escape at byte {offset}")
            }
            Self::InvalidEscape { token, offset } => {
                write!(f, "pct1 engine argument {token:?}: invalid escape at byte {offset}")
            }
            Self::InvalidUtf8 { token } => {
                write!(f, "pct1 engine argument {token:?}: escapes do not decode to UTF-8")
            }
            Self::UnescapedCharacter { token, offset } => write!(
                f,
                "pct1 engine argument {token:?}: unescaped whitespace or control character at \
                 byte {offset}"
            ),
            Self::MalformedGroupHeader { token, index } => write!(
                f,
                "engine argument group header {token:?} at llvm-args index {index} is not \
                 {LLVM_ARGS_GROUP_PREFIX}{LLVM_ARGS_PCT1_SCHEME}<count>"
            ),
            Self::TruncatedGroup { header, index, expected, available } => write!(
                f,
                "engine argument group {header:?} at llvm-args index {index} claims {expected} \
                 tokens but only {available} follow it"
            ),
        }
    }
}

impl std::error::Error for EngineArgsError {}

fn hex_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

/// Decode one `pct1` token.
pub fn decode_token(token: &str) -> Result<String, EngineArgsError> {
    if token == EMPTY_TOKEN {
        return Ok(String::new());
    }
    if let Some((offset, _)) = token.char_indices().find(|&(_, c)| c != '%' && needs_escape(c)) {
        return Err(EngineArgsError::UnescapedCharacter { token: token.to_string(), offset });
    }
    let bytes = token.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let (Some(&hi), Some(&lo)) = (bytes.get(i + 1), bytes.get(i + 2)) else {
                return Err(EngineArgsError::TruncatedEscape {
                    token: token.to_string(),
                    offset: i,
                });
            };
            let (Some(hi), Some(lo)) = (hex_value(hi), hex_value(lo)) else {
                return Err(EngineArgsError::InvalidEscape { token: token.to_string(), offset: i });
            };
            out.push((hi << 4) | lo);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).map_err(|_| EngineArgsError::InvalidUtf8 { token: token.to_string() })
}

/// The token count of a group header's text after [`LLVM_ARGS_GROUP_PREFIX`]:
/// `pct1:` then a decimal with no sign and no leading zero.
fn parse_group_count(rest: &str) -> Option<usize> {
    let digits = rest.strip_prefix(LLVM_ARGS_PCT1_SCHEME)?;
    let canonical = !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && (digits == "0" || !digits.starts_with('0'));
    if canonical { digits.parse().ok() } else { None }
}

/// Recover the engine argv from `sess.opts.cg.llvm_args`.
///
/// Each group header is dropped and the `n` tokens it claims are decoded; every
/// token outside a group is returned unchanged, in order. A list with no header
/// is therefore the legacy form and comes back as it is.
pub fn decode_llvm_args(llvm_args: &[String]) -> Result<Vec<String>, EngineArgsError> {
    let mut argv = Vec::with_capacity(llvm_args.len());
    let mut index = 0;
    while let Some(token) = llvm_args.get(index) {
        let Some(rest) = token.strip_prefix(LLVM_ARGS_GROUP_PREFIX) else {
            argv.push(token.clone());
            index += 1;
            continue;
        };
        let expected = parse_group_count(rest)
            .ok_or_else(|| EngineArgsError::MalformedGroupHeader { token: token.clone(), index })?;
        let available = llvm_args.len() - index - 1;
        if expected > available {
            return Err(EngineArgsError::TruncatedGroup {
                header: token.clone(),
                index,
                expected,
                available,
            });
        }
        for encoded in &llvm_args[index + 1..index + 1 + expected] {
            argv.push(decode_token(encoded)?);
        }
        index += 1 + expected;
    }
    Ok(argv)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What rustc's `parse_list` does to one `-Cllvm-args` value.
    fn rustc_parse_list(slot: &mut Vec<String>, value: &str) {
        slot.extend(value.split_whitespace().map(str::to_string));
    }

    fn strings(tokens: &[&str]) -> Vec<String> {
        tokens.iter().map(|t| (*t).to_string()).collect()
    }

    const TRICKY: &[&str] = &[
        "",
        "%",
        "%%",
        "%25",
        "a b",
        " leading",
        "trailing ",
        "tab\there",
        "new\nline",
        "cr\r",
        "unit\u{1f}sep",
        "nul\u{0}",
        "nbsp\u{a0}x",
        "ideographic\u{3000}space",
        "line\u{2028}sep",
        "nel\u{85}",
        "e\u{301}",
        "\u{1F980}",
        "--c-lib",
        "$HOME/Library/Application Support/aterm/pkg/store/trust/8571/lib/stub.o",
        "--harness",
        "mod::check_add",
        "-Z",
        "ghost-state",
        "--ay-logic=QF_BV",
    ];

    #[test]
    fn encoded_tokens_survive_split_whitespace_and_cargo_separator() {
        for token in TRICKY {
            let encoded = encode_token(token);
            assert!(!encoded.is_empty(), "{token:?}");
            assert!(!encoded.chars().any(char::is_whitespace), "{token:?} -> {encoded:?}");
            assert!(!encoded.chars().any(char::is_control), "{token:?} -> {encoded:?}");
            assert!(!encoded.contains('\u{1f}'), "{token:?} -> {encoded:?}");
            assert_eq!(decode_token(&encoded).as_deref(), Ok(*token), "{encoded:?}");
        }
    }

    #[test]
    fn whole_argv_round_trips_through_rustc_parse_list() {
        let argv = strings(TRICKY);
        let mut llvm_args = Vec::new();
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&argv));
        assert_eq!(llvm_args[0], group_header(TRICKY.len()));
        assert_eq!(llvm_args.len(), TRICKY.len() + 1);
        assert_eq!(decode_llvm_args(&llvm_args).unwrap(), argv);
    }

    #[test]
    fn every_pair_of_tricky_tokens_round_trips() {
        for a in TRICKY {
            for b in TRICKY {
                let argv = strings(&[a, b]);
                let mut llvm_args = Vec::new();
                rustc_parse_list(&mut llvm_args, &encode_llvm_args(&argv));
                assert_eq!(decode_llvm_args(&llvm_args).unwrap(), argv, "{argv:?}");
            }
        }
    }

    #[test]
    fn repeated_groups_concatenate_like_the_cargo_route() {
        let dependency = strings(&["--check-version=0.6.0"]);
        let local = strings(&["--reachability=harnesses", "--c-lib", "/a b/c.o"]);
        let mut llvm_args = Vec::new();
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&dependency));
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&local));
        let mut expected = dependency;
        expected.extend(local);
        assert_eq!(decode_llvm_args(&llvm_args).unwrap(), expected);
    }

    #[test]
    fn the_space_in_application_support_is_the_measured_hazard() {
        let path = "$HOME/Library/Application Support/stub.o";
        let mut legacy = Vec::new();
        rustc_parse_list(&mut legacy, &format!("--c-lib {path}"));
        assert_eq!(legacy, strings(&["--c-lib", "$HOME/Library/Application", "Support/stub.o"]));

        assert_eq!(
            encode_llvm_args(["--c-lib", path]),
            "--trust-mc-engine-args=pct1:2 --c-lib $HOME/Library/Application%20Support/stub.o"
        );
    }

    #[test]
    fn legacy_lists_without_a_group_pass_through_unchanged() {
        let legacy = strings(&["--harness", "a%zz", "--log-level=warn", "%", "%41"]);
        assert_eq!(decode_llvm_args(&legacy).unwrap(), legacy);
    }

    #[test]
    fn foreign_tokens_outside_groups_are_never_decoded() {
        // A foreign `-Cllvm-args` value (ambient RUSTFLAGS, say) carrying a literal
        // `%41`, a bare `%` and an invalid escape, before, between and after groups.
        let dependency = strings(&["--check-version=0.6.0"]);
        let local = strings(&["--c-lib", "/a b/%41.o", ""]);
        let mut llvm_args = Vec::new();
        rustc_parse_list(&mut llvm_args, "--foreign=%41 %");
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&dependency));
        rustc_parse_list(&mut llvm_args, "-x=100%zz");
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&local));
        rustc_parse_list(&mut llvm_args, "--after=%41");
        assert_eq!(
            decode_llvm_args(&llvm_args).unwrap(),
            strings(&[
                "--foreign=%41",
                "%",
                "--check-version=0.6.0",
                "-x=100%zz",
                "--c-lib",
                "/a b/%41.o",
                "",
                "--after=%41",
            ])
        );
    }

    #[test]
    fn an_empty_group_is_a_header_alone() {
        let empty: [&str; 0] = [];
        assert_eq!(encode_llvm_args(empty), "--trust-mc-engine-args=pct1:0");
        let llvm_args = strings(&["--trust-mc-engine-args=pct1:0", "%41"]);
        assert_eq!(decode_llvm_args(&llvm_args).unwrap(), strings(&["%41"]));
    }

    #[test]
    fn malformed_group_headers_are_refused() {
        for header in [
            "--trust-mc-engine-args=pct1",
            "--trust-mc-engine-args=pct1:",
            "--trust-mc-engine-args=pct1:x",
            "--trust-mc-engine-args=pct1:01",
            "--trust-mc-engine-args=pct1:+1",
            "--trust-mc-engine-args=pct1:-1",
            "--trust-mc-engine-args=pct1: 1",
            "--trust-mc-engine-args=pct2:1",
            "--trust-mc-engine-args=",
            "--trust-mc-engine-args=pct1:99999999999999999999999999",
        ] {
            let llvm_args = strings(&["--foreign", header, "a"]);
            assert_eq!(
                decode_llvm_args(&llvm_args),
                Err(EngineArgsError::MalformedGroupHeader { token: header.into(), index: 1 }),
                "{header:?}"
            );
        }
    }

    #[test]
    fn a_group_claiming_more_tokens_than_follow_is_refused() {
        let llvm_args = strings(&["--trust-mc-engine-args=pct1:3", "--harness", "a"]);
        assert_eq!(
            decode_llvm_args(&llvm_args),
            Err(EngineArgsError::TruncatedGroup {
                header: "--trust-mc-engine-args=pct1:3".into(),
                index: 0,
                expected: 3,
                available: 2,
            })
        );
        let huge = group_header(usize::MAX);
        assert!(matches!(
            decode_llvm_args(&strings(&[&huge])),
            Err(EngineArgsError::TruncatedGroup { expected: usize::MAX, available: 0, .. })
        ));
        let error = decode_llvm_args(&llvm_args).unwrap_err().to_string();
        assert!(error.contains("claims 3") && error.contains("only 2"), "{error}");
    }

    #[test]
    fn a_header_inside_a_group_is_data() {
        let argv = strings(&["--trust-mc-engine-args=pct1:5", "x"]);
        let mut llvm_args = Vec::new();
        rustc_parse_list(&mut llvm_args, &encode_llvm_args(&argv));
        assert_eq!(decode_llvm_args(&llvm_args).unwrap(), argv);
    }

    #[test]
    fn malformed_tokens_inside_a_group_are_refused() {
        let with = |token: &str| strings(&[&group_header(1), token]);
        assert_eq!(
            decode_llvm_args(&with("ab%4")),
            Err(EngineArgsError::TruncatedEscape { token: "ab%4".into(), offset: 2 })
        );
        assert_eq!(
            decode_llvm_args(&with("%zz")),
            Err(EngineArgsError::InvalidEscape { token: "%zz".into(), offset: 0 })
        );
        assert_eq!(
            decode_llvm_args(&with("%FF")),
            Err(EngineArgsError::InvalidUtf8 { token: "%FF".into() })
        );
        assert_eq!(
            decode_llvm_args(&with("unit\u{1f}sep")),
            Err(EngineArgsError::UnescapedCharacter { token: "unit\u{1f}sep".into(), offset: 4 })
        );
    }

    #[test]
    fn lowercase_escapes_decode_and_encoding_is_uppercase() {
        assert_eq!(decode_token("a%20b%2fc").unwrap(), "a b/c");
        assert_eq!(encode_token("a b\u{a0}"), "a%20b%C2%A0");
    }

    #[test]
    fn set_engine_env_knobs_names_only_the_knobs_sorted_and_once() {
        let keys = [
            "TRUST_MC_SMT_NODE_BUDGET",
            "TRUST_MC_SYSROOT",
            "TRUST_MC_REACH_DEBUG",
            "AY_TIMEOUT",
            "TRUST_MC_REACH_DEBUG",
            "PATH",
        ];
        assert_eq!(
            set_engine_env_knobs(keys),
            vec!["TRUST_MC_REACH_DEBUG".to_string(), "TRUST_MC_SMT_NODE_BUDGET".to_string()]
        );
        assert!(set_engine_env_knobs(["PATH", "TRUST_MC_SYSROOT"]).is_empty());
        assert!(ENGINE_ENV_KNOBS.windows(2).all(|w| w[0] < w[1]), "sorted, no duplicates");
    }
}
