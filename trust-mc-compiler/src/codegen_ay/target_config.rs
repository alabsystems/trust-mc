// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Target platform validation and feature selection for the AY backend.

use rustc_session::Session;
use rustc_span::Symbol;
use rustc_target::spec::{Arch, Os};

/// Check that the compilation target is one we support.
pub(super) fn check_target(session: &Session) {
    if !is_supported_target_triple(&session.target.llvm_target) {
        let mut err_msg = String::from(
            "trust_mc AY backend requires target platform to be `x86_64-unknown-linux-gnu`, \
            `aarch64-unknown-linux-gnu`, `x86_64-apple-*` or `arm64-apple-*`, but it is ",
        );
        err_msg.push_str(&session.target.llvm_target);
        session.dcx().err(err_msg);
    }

    session.dcx().abort_if_errors();
}

pub(super) fn is_supported_target_triple(triple: &str) -> bool {
    triple == "x86_64-unknown-linux-gnu"
        || triple == "aarch64-unknown-linux-gnu"
        || triple.starts_with("x86_64-apple-")
        || triple.starts_with("arm64-apple-")
}

/// Target feature selection for the AY backend.
pub(super) fn select_target_features(arch: &Arch, os: &Os) -> Vec<Symbol> {
    use rustc_span::sym;

    if *arch == Arch::X86_64 && *os != Os::None {
        vec![sym::sse, sym::sse2, Symbol::intern("x87")]
    } else if *arch == Arch::AArch64 {
        match os {
            Os::None => vec![],
            Os::MacOs => vec![sym::neon, sym::aes, sym::sha2, sym::sha3],
            _ => vec![sym::neon], // external enum: Os
        }
    } else {
        vec![]
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;

    // --- select_target_features ---

    #[test]
    fn test_select_target_features_x86_64_linux() {
        use rustc_span::{Symbol, sym};

        rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2024,
            |_| {
                let features = select_target_features(&Arch::X86_64, &Os::Linux);
                assert_eq!(features, vec![sym::sse, sym::sse2, Symbol::intern("x87")]);
            },
        );
    }

    #[test]
    fn test_select_target_features_x86_64_none_os() {
        let features = select_target_features(&Arch::X86_64, &Os::None);
        assert!(features.is_empty());
    }

    #[test]
    fn test_select_target_features_x86_64_macos() {
        use rustc_span::{Symbol, sym};

        rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2024,
            |_| {
                let features = select_target_features(&Arch::X86_64, &Os::MacOs);
                assert_eq!(features, vec![sym::sse, sym::sse2, Symbol::intern("x87")]);
            },
        );
    }

    #[test]
    fn test_select_target_features_aarch64_macos() {
        use rustc_span::sym;

        let features = select_target_features(&Arch::AArch64, &Os::MacOs);
        assert_eq!(features, vec![sym::neon, sym::aes, sym::sha2, sym::sha3]);
    }

    #[test]
    fn test_select_target_features_aarch64_linux() {
        use rustc_span::sym;

        let features = select_target_features(&Arch::AArch64, &Os::Linux);
        assert_eq!(features, vec![sym::neon]);
    }

    #[test]
    fn test_select_target_features_aarch64_ios() {
        use rustc_span::sym;

        let features = select_target_features(&Arch::AArch64, &Os::IOs);
        assert_eq!(features, vec![sym::neon]);
    }

    #[test]
    fn test_select_target_features_aarch64_none_os() {
        let features = select_target_features(&Arch::AArch64, &Os::None);
        assert!(features.is_empty());
    }

    #[test]
    fn test_select_target_features_non_tier1_arch() {
        let features = select_target_features(&Arch::X86, &Os::Linux);
        assert!(features.is_empty());
    }

    // --- is_supported_target_triple ---

    #[test]
    fn test_is_supported_target_triple_accepts_allowed_targets() {
        assert!(is_supported_target_triple("x86_64-unknown-linux-gnu"));
        assert!(is_supported_target_triple("aarch64-unknown-linux-gnu"));
        assert!(is_supported_target_triple("x86_64-apple-darwin"));
        assert!(is_supported_target_triple("x86_64-apple-ios"));
        assert!(is_supported_target_triple("arm64-apple-darwin"));
        assert!(is_supported_target_triple("arm64-apple-ios"));
        assert!(is_supported_target_triple("arm64-apple-watchos"));
    }

    #[test]
    fn test_is_supported_target_triple_rejects_unsupported_targets() {
        assert!(!is_supported_target_triple("wasm32-unknown-unknown"));
        assert!(!is_supported_target_triple("x86_64-pc-windows-msvc"));
        assert!(!is_supported_target_triple("aarch64-apple-darwin"));
    }

    #[test]
    fn test_is_supported_target_triple_rejects_near_misses() {
        assert!(!is_supported_target_triple("x86_64-apple"));
        assert!(!is_supported_target_triple("arm64_apple_darwin"));
    }
}
