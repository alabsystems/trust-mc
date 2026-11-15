// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Build-time frontend identity, shared with its policy tests.

pub(crate) fn classify(
    verbose: &str,
    channel: Option<&str>,
    host: &str,
    sysroot: Option<&std::path::Path>,
) -> &'static str {
    let field =
        |name: &str| verbose.lines().find_map(|line| line.strip_prefix(name).map(str::trim));
    if host.is_empty() || field("host:") != Some(host) {
        return "unknown";
    }
    if field("binary:") == Some("trustc") && field("trust:").is_some_and(|v| !v.is_empty()) {
        return "trust";
    }
    // The one advisory stock oracle, never a fallback for a damaged Trust seal.
    let frozen = "nightly-2025-12-03";
    let selected = channel.is_some_and(|c| c == frozen || c == format!("{frozen}-{host}"));
    let official_sysroot = sysroot
        .and_then(|p| p.file_name())
        .and_then(|n| n.to_str())
        .is_some_and(|n| n == frozen || n == format!("{frozen}-{host}"));
    if selected
        && official_sysroot
        && field("binary:") == Some("rustc")
        && field("trust:").is_none()
        && field("release:") == Some("1.93.0-nightly")
        && field("commit-hash:") == Some("646a3f8c15baefb98dc6e0c1c1ba3356db702d2a")
    {
        "frozen-kani-oracle"
    } else {
        "unknown"
    }
}

#[cfg(test)]
mod tests {
    use super::classify as classify_facts;
    use std::path::Path;
    fn classify(verbose: &str, channel: Option<&str>, host: &str) -> &'static str {
        classify_facts(
            verbose,
            channel,
            host,
            Some(Path::new("/toolchains/nightly-2025-12-03-aarch64-apple-darwin")),
        )
    }
    const STOCK: &str = "binary: rustc\nhost: aarch64-apple-darwin\nrelease: 1.93.0-nightly\ncommit-hash: 646a3f8c15baefb98dc6e0c1c1ba3356db702d2a\n";

    #[test]
    fn trust_facts_win_over_an_ambient_oracle_name() {
        let trust = "binary: trustc\nhost: aarch64-apple-darwin\ntrust: 0.12.0+g29ebb403d\n";
        assert_eq!(classify(trust, None, "aarch64-apple-darwin"), "trust");
        assert_eq!(classify(trust, Some("nightly-2025-12-03"), "aarch64-apple-darwin"), "trust");
        assert_eq!(classify("binary: rustc\ntrust: 0.12.0\n", None, "host"), "unknown");
    }

    #[test]
    fn incomplete_or_mismatched_compiler_facts_are_not_oracle_authority() {
        for (facts, host, root) in [
            (STOCK, "wrong-host", "/toolchains/nightly-2025-12-03-aarch64-apple-darwin"),
            (STOCK, "aarch64-apple-darwin", "/arbitrary/compiler"),
            (
                "binary: rustc\nhost: aarch64-apple-darwin\ntrust:\n",
                "aarch64-apple-darwin",
                "/toolchains/nightly-2025-12-03",
            ),
        ] {
            assert_eq!(
                classify_facts(facts, Some("nightly-2025-12-03"), host, Some(Path::new(root))),
                "unknown"
            );
        }
        assert_eq!(
            classify_facts(STOCK, Some("nightly-2025-12-03"), "aarch64-apple-darwin", None),
            "unknown"
        );
    }

    #[test]
    fn only_the_exact_explicit_frozen_oracle_is_recognized() {
        for channel in ["nightly-2025-12-03", "nightly-2025-12-03-aarch64-apple-darwin"] {
            assert_eq!(
                classify(STOCK, Some(channel), "aarch64-apple-darwin"),
                "frozen-kani-oracle"
            );
        }
        for channel in [
            None,
            Some("stable"),
            Some("nightly-2025-12-04"),
            Some("nightly-2025-12-03-wrong-host"),
        ] {
            assert_eq!(classify(STOCK, channel, "aarch64-apple-darwin"), "unknown");
        }
        assert_eq!(
            classify(&STOCK.replace("646a3f8c", "00000000"), Some("nightly-2025-12-03"), "host"),
            "unknown"
        );
        assert_eq!(classify("", Some("nightly-2025-12-03"), "host"), "unknown");
    }
}
