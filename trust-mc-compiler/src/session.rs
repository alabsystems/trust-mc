// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Module used to configure a compiler session.

use crate::args::Arguments;
use rustc_driver::default_translator;
use rustc_errors::{
    ColorConfig, DiagInner, emitter::Emitter, emitter::HumanReadableErrorType, json::JsonEmitter,
    registry::Registry as ErrorRegistry,
};
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::ErrorOutputType;
use rustc_span::source_map::FilePathMapping;
use rustc_span::source_map::SourceMap;
use std::io;
use std::io::IsTerminal;
use std::panic;
use std::sync::Arc;
use std::sync::LazyLock;
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt};
use tracing_tree::HierarchicalLayer;

/// Environment variable used to control this session log tracing.
const LOG_ENV_VAR: &str = "TRUST_MC_LOG";
const LOG_ENV_VAR_LEGACY: &str = "KANI_LOG";

// Bug reporting URL.
const BUG_REPORT_URL: &str = "https://github.com/alabsystems/trust_mc/issues/new?labels=bug";

// Custom panic hook when running under user friendly message format.
#[allow(clippy::type_complexity)]
static PANIC_HOOK: LazyLock<Box<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static>> =
    LazyLock::new(|| {
        let hook = panic::take_hook();
        panic::set_hook(Box::new(|info| {
            // Print stack trace.
            (*PANIC_HOOK)(info);
            eprintln!();

            // Print the panic banner. The wording deliberately matches Kani's
            // ("Kani unexpectedly panicked during compilation.") so that Kani's
            // `expected` UI tests which assert on this banner — e.g. the rustc
            // ZST-intrinsic diagnostic in `sub_with_overflow_diagnostic` (kani #2121),
            // an ICE inside rustc that trust-mc can only gracefully report —
            // still match. This follows the same Kani-compat-string convention
            // as "not currently supported by Kani" and "[Kani] info:".
            eprintln!("Kani unexpectedly panicked during compilation.");
            eprintln!("Please file an issue here: {BUG_REPORT_URL}");
        }));
        hook
    });

// Custom panic hook when executing under json error format `--error-format=json`.
// The emitter call is wrapped in catch_unwind because JsonEmitter::emit_diagnostic
// can itself panic (e.g., on empty SourceMap span lookups), which would cause a
// double-panic → abort(). This was the root cause of SIGABRT crashes (2026-03-01).
#[allow(clippy::type_complexity)]
static JSON_PANIC_HOOK: LazyLock<Box<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static>> =
    LazyLock::new(|| {
        let hook = panic::take_hook();
        panic::set_hook(Box::new(|info| {
            let msg = format!("trust_mc unexpectedly panicked at {info}.");
            // Attempt JSON-formatted output, but catch any panic to prevent
            // double-panic → abort(). Falls back to plain stderr on failure.
            let json_ok = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                let mut emitter = JsonEmitter::new(
                    Box::new(io::BufWriter::new(io::stderr())),
                    #[allow(clippy::arc_with_non_send_sync)]
                    Some(Arc::new(SourceMap::new(FilePathMapping::empty()))),
                    default_translator(),
                    false,
                    HumanReadableErrorType::Default { short: false },
                    ColorConfig::Never,
                );
                let registry = ErrorRegistry::new(&[]);
                let diagnostic = DiagInner::new(rustc_errors::Level::Bug, msg.clone());
                emitter.emit_diagnostic(diagnostic, &registry);
            }));
            if json_ok.is_err() {
                // JSON emitter panicked — write plain text so the error is not lost.
                // Uses write! instead of eprintln! because tracing may be unavailable
                // inside a panic hook, and this is a last-resort fallback.
                let _ = io::Write::write_all(
                    &mut io::stderr(),
                    format!("{msg}\n(JSON error emitter panicked; falling back to plain text)\n")
                        .as_bytes(),
                );
            }
            (*JSON_PANIC_HOOK)(info);
        }));
        hook
    });

/// Initialize compiler session.
pub(crate) fn init_session(args: &Arguments, json_hook: bool) {
    // Initialize the rustc logger using value from RUSTC_LOG. We keep the log control separate
    // because we cannot control the RUSTC log format unless if we match the exact tracing
    // version used by RUSTC.
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);

    // Install Kani panic hook.
    if json_hook {
        json_panic_hook();
    }

    // Kani logger initialization.
    init_logger(args);
}

/// Resolve which environment variable to use for log filtering.
/// Prefers TRUST_MC_LOG; falls back to the deprecated KANI_LOG.
/// Returns `(env_var_name, is_legacy)`.
fn resolve_log_env_var() -> (&'static str, bool) {
    if std::env::var(LOG_ENV_VAR).is_ok() {
        return (LOG_ENV_VAR, false);
    }
    if std::env::var(LOG_ENV_VAR_LEGACY).is_ok() {
        return (LOG_ENV_VAR_LEGACY, true);
    }
    (LOG_ENV_VAR, false)
}

/// Initialize the logger using the TRUST_MC_LOG environment variable and the --log-level argument.
/// Falls back to the deprecated KANI_LOG if TRUST_MC_LOG is not set.
fn init_logger(args: &Arguments) {
    let (log_var, is_legacy) = resolve_log_env_var();
    let filter = EnvFilter::from_env(log_var);
    let filter = if let Some(log_level) = &args.log_level {
        filter.add_directive(log_level.clone())
    } else {
        filter
    };

    if args.json_output {
        json_logs(filter);
    } else {
        hier_logs(args, filter);
    }
    if is_legacy {
        tracing::warn!("{} is deprecated, use {} instead", LOG_ENV_VAR_LEGACY, LOG_ENV_VAR);
    }
}

/// Configure global logger to use a json logger.
fn json_logs(filter: EnvFilter) {
    use tracing_subscriber::fmt::layer;
    let subscriber = Registry::default().with(filter).with(layer().json());
    tracing::subscriber::set_global_default(subscriber).expect("failed to set global logger");
}

/// Configure global logger to use a hierarchical view.
fn hier_logs(args: &Arguments, filter: EnvFilter) {
    let use_colors = std::io::stdout().is_terminal() || args.color_output;
    let subscriber = Registry::default().with(filter);
    let subscriber = subscriber.with(
        HierarchicalLayer::default()
            .with_writer(std::io::stderr)
            .with_indent_lines(true)
            .with_ansi(use_colors)
            .with_targets(true)
            .with_verbose_exit(true)
            .with_indent_amount(4),
    );
    tracing::subscriber::set_global_default(subscriber).expect("failed to set global logger");
}

pub(crate) fn init_panic_hook() {
    // Install panic hook
    LazyLock::force(&PANIC_HOOK); // Install ice hook
}

fn json_panic_hook() {
    // Install panic hook
    LazyLock::force(&JSON_PANIC_HOOK); // Install ice hook
}
