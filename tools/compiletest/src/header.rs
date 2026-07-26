// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Modifications Copyright Kani Contributors
// See GitHub history for details.

use std::fs::File;
use std::io::BufReader;
use std::io::prelude::*;
use std::path::Path;

use tracing::*;

use crate::common::{Config, KaniFailStep, Mode};

#[derive(Clone, Debug)]
pub struct TestProps {
    // Extra flags to pass to the compiler
    pub compile_flags: Vec<String>,
    // Extra flags to pass to Kani
    pub kani_flags: Vec<String>,
    // The step where Kani is expected to fail
    pub kani_panic_step: Option<KaniFailStep>,
}

impl Default for TestProps {
    fn default() -> Self {
        Self::new()
    }
}

impl TestProps {
    pub fn new() -> Self {
        TestProps { compile_flags: vec![], kani_flags: vec![], kani_panic_step: None }
    }

    pub fn from_file(testfile: &Path, config: &Config) -> Self {
        let mut props = TestProps::new();
        props.load_from(testfile, config);
        props.kani_flags.extend(config.extra_args.iter().cloned());
        props
    }

    /// Loads properties from `testfile` into `props`.
    fn load_from(&mut self, testfile: &Path, config: &Config) {
        let mut has_edition = false;
        if !testfile.is_dir() {
            let file = File::open(testfile).unwrap();

            iter_header(testfile, file, &mut |ln| {
                if let Some(flags) = config.parse_compile_flags(ln) {
                    self.compile_flags.extend(flags.split_whitespace().map(|s| s.to_owned()));
                }

                if let Some(flags) = config.parse_kani_flags(ln) {
                    self.kani_flags.extend(flags.split_whitespace().map(|s| s.to_owned()));
                }

                if let Some(edition) = config.parse_edition(ln) {
                    self.compile_flags.push(format!("--edition={edition}"));
                    has_edition = true;
                }

                self.update_kani_fail_mode(ln, config);
            });
        }

        if let (Some(edition), false) = (&config.edition, has_edition) {
            self.compile_flags.push(format!("--edition={edition}"));
        }
    }

    /// Checks if `ln` specifies which stage the test should fail on and updates
    /// Kani fail mode accordingly.
    fn update_kani_fail_mode(&mut self, ln: &str, config: &Config) {
        let kani_fail_step = config.parse_kani_step_fail_directive(ln);
        match (self.kani_panic_step, kani_fail_step) {
            (None, Some(_)) => self.kani_panic_step = kani_fail_step,
            (Some(_), Some(_)) => panic!("multiple `kani-*-fail` headers in a single test"),
            (_, None) => {}
        }
    }
}

fn iter_header<R: Read>(testfile: &Path, rdr: R, it: &mut dyn FnMut(&str)) {
    if testfile.is_dir() {
        return;
    }

    let comment = if testfile.extension().map(|e| e == "rs") == Some(true) { "//" } else { "#" };

    let mut rdr = BufReader::new(rdr);
    let mut ln = String::new();

    loop {
        ln.clear();
        if rdr.read_line(&mut ln).unwrap() == 0 {
            break;
        }

        // Assume that any directives will be found before the first
        // module or function. This doesn't seem to be an optimization
        // with a warm page cache. Maybe with a cold one.
        let ln = ln.trim();
        if ln.starts_with("fn") || ln.starts_with("mod") {
            return;
        } else if let Some(rest) = ln.strip_prefix(comment) {
            it(rest.trim_start());
        }
    }
}

impl Config {
    fn parse_compile_flags(&self, line: &str) -> Option<String> {
        self.parse_name_value_directive(line, "compile-flags")
    }

    /// Parses strings of the form `kani-*-fail` and returns the step at which
    /// Kani is expected to panic.
    fn parse_kani_step_fail_directive(&self, line: &str) -> Option<KaniFailStep> {
        let check_kani = |mode: &str| {
            if self.mode != Mode::TrustMc {
                panic!("`kani-{mode}-fail` header is only supported in trust_mc tests");
            }
        };
        if self.parse_name_directive(line, "kani-check-fail") {
            check_kani("check");
            Some(KaniFailStep::Check)
        } else if self.parse_name_directive(line, "kani-codegen-fail") {
            check_kani("codegen");
            Some(KaniFailStep::Codegen)
        } else if self.parse_name_directive(line, "kani-verify-fail") {
            check_kani("verify");
            Some(KaniFailStep::Verify)
        } else {
            None
        }
    }

    /// Parses strings of the form `// kani-flags: ...` and returns the options listed after `kani-flags:`
    fn parse_kani_flags(&self, line: &str) -> Option<String> {
        self.parse_name_value_directive(line, "kani-flags")
    }

    fn parse_name_directive(&self, line: &str, directive: &str) -> bool {
        // Ensure the directive is a whole word. Do not match "ignore-x86" when
        // the line says "ignore-x86_64".
        line.starts_with(directive)
            && matches!(line.as_bytes().get(directive.len()), None | Some(&b' ') | Some(&b':'))
    }

    pub fn parse_name_value_directive(&self, line: &str, directive: &str) -> Option<String> {
        let colon = directive.len();
        if line.starts_with(directive) && line.as_bytes().get(colon) == Some(&b':') {
            let value = line[(colon + 1)..].trim().to_owned();
            debug!("{}: {}", directive, value);
            Some(value)
        } else {
            None
        }
    }

    fn parse_edition(&self, line: &str) -> Option<String> {
        self.parse_name_value_directive(line, "edition")
    }
}

pub fn make_test_description<R: Read>(
    config: &Config,
    name: test::TestName,
    path: &Path,
    src: R,
) -> test::TestDesc {
    let mut should_fail = false;

    iter_header(path, src, &mut |ln| {
        should_fail |= config.parse_name_directive(ln, "should-fail");
    });

    // The `should-fail` annotation doesn't apply to pretty tests,
    // since we run the pretty printer across all tests by default.
    // If desired, we could add a `should-fail-pretty` annotation.
    let should_panic = match config.mode {
        _ if should_fail => test::ShouldPanic::Yes,
        _ => test::ShouldPanic::No,
    };

    test::TestDesc {
        name,
        ignore: false,
        ignore_message: None,
        should_panic,
        compile_fail: false,
        no_run: false,
        test_type: test::TestType::Unknown,
        // Enter dummy values since the test doesn't have a line per-se.
        source_file: "unknown_file",
        start_line: 0,
        start_col: 0,
        end_line: 0,
        end_col: 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::Mode;
    use std::path::PathBuf;
    use std::time::Duration;
    use test::ColorConfig;

    /// Creates a minimal Config for testing directive parsing.
    fn test_config(mode: Mode) -> Config {
        Config {
            src_base: PathBuf::from("tests"),
            build_base: PathBuf::from("build"),
            mode,
            suite: "test".to_string(),
            filters: vec![],
            filter_exact: false,
            logfile: None,
            target: "x86_64-unknown-linux-gnu".to_string(),
            host: "x86_64-unknown-linux-gnu".to_string(),
            verbose: false,
            quiet: false,
            color: ColorConfig::AutoColor,
            edition: None,
            force_rerun: false,
            timeout: Some(Duration::from_secs(30)),
            fail_fast: false,
            dry_run: false,
            fix_expected: false,
            time_opts: None,
            extra_args: vec![],
        }
    }

    #[test]
    fn test_parse_name_directive_exact_match() {
        let config = test_config(Mode::TrustMc);
        assert!(config.parse_name_directive("should-fail", "should-fail"));
        assert!(config.parse_name_directive("kani-verify-fail", "kani-verify-fail"));
    }

    #[test]
    fn test_parse_name_directive_with_space() {
        let config = test_config(Mode::TrustMc);
        // Directive followed by space should match
        assert!(config.parse_name_directive("should-fail ignored", "should-fail"));
    }

    #[test]
    fn test_parse_name_directive_with_colon() {
        let config = test_config(Mode::TrustMc);
        // Directive followed by colon should match (for value directives)
        assert!(config.parse_name_directive("edition: 2021", "edition"));
    }

    #[test]
    fn test_parse_name_directive_prefix_mismatch() {
        let config = test_config(Mode::TrustMc);
        // "ignore-x86" should not match "ignore-x86_64"
        assert!(!config.parse_name_directive("ignore-x86_64", "ignore-x86"));
    }

    #[test]
    fn test_parse_name_directive_no_match() {
        let config = test_config(Mode::TrustMc);
        assert!(!config.parse_name_directive("something-else", "should-fail"));
    }

    #[test]
    fn test_parse_name_value_directive_basic() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_name_value_directive("compile-flags: -O", "compile-flags");
        assert_eq!(result, Some("-O".to_string()));
    }

    #[test]
    fn test_parse_name_value_directive_kani_flags() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_name_value_directive("kani-flags: --unwind 10", "kani-flags");
        assert_eq!(result, Some("--unwind 10".to_string()));
    }

    #[test]
    fn test_parse_name_value_directive_edition() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_name_value_directive("edition: 2021", "edition");
        assert_eq!(result, Some("2021".to_string()));
    }

    #[test]
    fn test_parse_name_value_directive_no_colon() {
        let config = test_config(Mode::TrustMc);
        // Without colon, should return None
        let result = config.parse_name_value_directive("compile-flags -O", "compile-flags");
        assert_eq!(result, None);
    }

    #[test]
    fn test_parse_name_value_directive_wrong_name() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_name_value_directive("kani-flags: --unwind 10", "compile-flags");
        assert_eq!(result, None);
    }

    #[test]
    fn test_parse_kani_step_fail_verify() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_kani_step_fail_directive("kani-verify-fail");
        assert_eq!(result, Some(KaniFailStep::Verify));
    }

    #[test]
    fn test_parse_kani_step_fail_codegen() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_kani_step_fail_directive("kani-codegen-fail");
        assert_eq!(result, Some(KaniFailStep::Codegen));
    }

    #[test]
    fn test_parse_kani_step_fail_check() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_kani_step_fail_directive("kani-check-fail");
        assert_eq!(result, Some(KaniFailStep::Check));
    }

    #[test]
    fn test_parse_kani_step_fail_none() {
        let config = test_config(Mode::TrustMc);
        let result = config.parse_kani_step_fail_directive("something-else");
        assert_eq!(result, None);
    }

    #[test]
    fn test_iter_header_rust_comments() {
        let content = "// compile-flags: -O\n// kani-flags: --unwind 5\nfn main() {}";
        let path = Path::new("test.rs");
        let mut lines = vec![];
        iter_header(path, content.as_bytes(), &mut |ln| {
            lines.push(ln.to_string());
        });
        assert_eq!(lines, vec!["compile-flags: -O", "kani-flags: --unwind 5"]);
    }

    #[test]
    fn test_iter_header_stops_at_fn() {
        let content = "// first\nfn main() {}\n// after fn";
        let path = Path::new("test.rs");
        let mut lines = vec![];
        iter_header(path, content.as_bytes(), &mut |ln| {
            lines.push(ln.to_string());
        });
        assert_eq!(lines, vec!["first"]);
    }

    #[test]
    fn test_iter_header_stops_at_mod() {
        let content = "// first\nmod foo;\n// after mod";
        let path = Path::new("test.rs");
        let mut lines = vec![];
        iter_header(path, content.as_bytes(), &mut |ln| {
            lines.push(ln.to_string());
        });
        assert_eq!(lines, vec!["first"]);
    }

    #[test]
    fn test_iter_header_shell_comments() {
        let content = "# compile-flags: -O\n# kani-flags: --unwind 5";
        let path = Path::new("test.sh");
        let mut lines = vec![];
        iter_header(path, content.as_bytes(), &mut |ln| {
            lines.push(ln.to_string());
        });
        assert_eq!(lines, vec!["compile-flags: -O", "kani-flags: --unwind 5"]);
    }

    #[test]
    fn test_file_name_never_changes_selection() {
        let config = test_config(Mode::Expected);
        for path in ["case.rs", "case_fixme.rs", "case_ignore.rs"] {
            let desc = make_test_description(
                &config,
                test::DynTestName(path.to_string()),
                Path::new(path),
                &b""[..],
            );
            assert!(!desc.ignore, "{path} must run");
            assert!(desc.ignore_message.is_none());
        }
    }

    #[test]
    fn test_test_props_default() {
        let props = TestProps::new();
        assert!(props.compile_flags.is_empty());
        assert!(props.kani_flags.is_empty());
        assert!(props.kani_panic_step.is_none());
    }
}
