// Copyright Kani Contributors
// Modifications Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Module used to configure a compiler session.

use crate::args::Arguments;
#[cfg(not(trust_toolchain))]
use rustc_driver::default_translator;
#[cfg(not(trust_toolchain))]
use rustc_errors::registry::Registry as ErrorRegistry;
use rustc_errors::{
    ColorConfig, DiagInner, emitter::Emitter, emitter::HumanReadableErrorType, json::JsonEmitter,
};
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::ErrorOutputType;
use rustc_span::source_map::FilePathMapping;
use rustc_span::source_map::SourceMap;
use std::io;
use std::io::IsTerminal;
use std::panic;
use std::sync::Arc;
use std::sync::{Once, OnceLock};
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt};
use tracing_tree::HierarchicalLayer;

/// Environment variable used to control this session log tracing.
const LOG_ENV_VAR: &str = "TRUST_MC_LOG";
const LOG_ENV_VAR_LEGACY: &str = "KANI_LOG";

// Bug reporting URL.
const BUG_REPORT_URL: &str = "https://github.com/alabsystems/trust_mc/issues/new?labels=bug";

/// A process panic hook, as `panic::take_hook` returns it.
type PanicHook = Box<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static>;

/// Install `hook` as the process panic hook, once per `installed`, after storing
/// the hook it replaces in `replaced`.
///
/// Storing first means the installed hook always finds its predecessor through
/// `OnceLock::get`, which never waits. The previous form kept the replaced hook
/// in a lazy static whose initializer installed a hook that forces that same
/// static: a re-entrant initializer, which the Trust compiler rejects. The
/// behaviour is unchanged. The first call replaces the hook and keeps the old
/// one, the installed hook calls the old one first, and every later call is a
/// no-op, as a second force of the lazy static was.
fn install_panic_hook(
    installed: &'static Once,
    replaced: &'static OnceLock<PanicHook>,
    hook: fn(&panic::PanicHookInfo<'_>),
) {
    installed.call_once(|| {
        let _ = replaced.set(panic::take_hook());
        panic::set_hook(Box::new(hook));
    });
}

/// Call the panic hook [`install_panic_hook`] replaced and stored in `replaced`.
fn call_replaced_panic_hook(replaced: &OnceLock<PanicHook>, info: &panic::PanicHookInfo<'_>) {
    if let Some(hook) = replaced.get() {
        hook(info);
    }
}

// Custom panic hook when running under user friendly message format.
// `PANIC_HOOK` holds the hook it replaced.
static PANIC_HOOK: OnceLock<PanicHook> = OnceLock::new();

fn ice_hook(info: &panic::PanicHookInfo<'_>) {
    // Print stack trace.
    call_replaced_panic_hook(&PANIC_HOOK, info);
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
}

// Custom panic hook when executing under json error format `--error-format=json`.
// The emitter call is wrapped in catch_unwind because JsonEmitter::emit_diagnostic
// can itself panic (e.g., on empty SourceMap span lookups), which would cause a
// double-panic → abort(). This was the root cause of SIGABRT crashes (2026-03-01).
// `JSON_PANIC_HOOK` holds the hook it replaced.
static JSON_PANIC_HOOK: OnceLock<PanicHook> = OnceLock::new();

fn json_ice_hook(info: &panic::PanicHookInfo<'_>) {
    let msg = format!("trust_mc unexpectedly panicked at {info}.");
    // Attempt JSON-formatted output, but catch any panic to prevent
    // double-panic → abort(). Falls back to plain stderr on failure.
    let json_ok = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        #[cfg(not(trust_toolchain))]
        let mut emitter = JsonEmitter::new(
            Box::new(io::BufWriter::new(io::stderr())),
            #[allow(clippy::arc_with_non_send_sync)]
            Some(Arc::new(SourceMap::new(FilePathMapping::empty()))),
            default_translator(),
            false,
            HumanReadableErrorType::Default { short: false },
            ColorConfig::Never,
        );
        // Trust: `JsonEmitter::new` takes no translator, the human
        // renderer is the `{ short, unicode }` struct (the nightly
        // `Default { short }` variant is its non-unicode form), and
        // `emit_diagnostic` takes no error-code registry.
        #[cfg(trust_toolchain)]
        let mut emitter = JsonEmitter::new(
            Box::new(io::BufWriter::new(io::stderr())),
            #[allow(clippy::arc_with_non_send_sync)]
            Some(Arc::new(SourceMap::new(FilePathMapping::empty()))),
            false,
            HumanReadableErrorType { short: false, unicode: false },
            ColorConfig::Never,
        );
        #[cfg(not(trust_toolchain))]
        let registry = ErrorRegistry::new(&[]);
        let diagnostic = DiagInner::new(rustc_errors::Level::Bug, msg.clone());
        #[cfg(not(trust_toolchain))]
        emitter.emit_diagnostic(diagnostic, &registry);
        #[cfg(trust_toolchain)]
        emitter.emit_diagnostic(diagnostic);
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
    call_replaced_panic_hook(&JSON_PANIC_HOOK, info);
}

/// Initialize rustc's own logger from `RUSTC_LOG`. Embedded binary only.
///
/// We keep the log control separate because we cannot control the RUSTC log
/// format unless we match the exact tracing version used by RUSTC. Only the
/// `trust-mc-compiler` binary may call this: it runs
/// `rustc_driver::run_compiler` itself, which installs no logger. Inside
/// canonical trustc, `main` has already installed rustc_log's global
/// subscriber, and a second `set_global_default` is an `early_fatal`. Trust's
/// rustc_log installs that subscriber even when `RUSTC_LOG` is unset.
pub(crate) fn init_embedded_rustc_logger() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
}

/// Initialize the trust-mc session, hosted form.
///
/// Called from `CodegenBackend::init` for the embedded binary and for trustc
/// loading `librustc_codegen_trust_mc.dylib` alike. It never touches rustc's
/// logger (see [`init_embedded_rustc_logger`]): it installs the JSON panic hook
/// when rustc emits JSON diagnostics, and trust-mc's own crates.io `tracing`
/// logger once per process.
pub(crate) fn init_session(args: &Arguments, json_hook: bool) {
    // Install Kani panic hook.
    if json_hook {
        json_panic_hook();
    }

    // Kani logger initialization.
    static LOGGER: Once = Once::new();
    LOGGER.call_once(|| init_logger(args));
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
    static INSTALLED: Once = Once::new();
    install_panic_hook(&INSTALLED, &PANIC_HOOK, ice_hook); // Install ice hook
}

fn json_panic_hook() {
    // Install panic hook
    static INSTALLED: Once = Once::new();
    install_panic_hook(&INSTALLED, &JSON_PANIC_HOOK, json_ice_hook); // Install ice hook
}
