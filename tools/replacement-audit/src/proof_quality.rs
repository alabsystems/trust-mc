// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

pub(crate) const CLEAN_PROOF_QUALIFIER: &str = "clean";
pub(crate) const SHOULD_PANIC_PROOF_QUALIFIER: &str = "should_panic";
pub(crate) const TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER: &str = "trivial_safe=no_error_rule";

pub(crate) fn proof_qualifier_non_quality_reason(qualifiers: &str) -> Option<&'static str> {
    if qualifiers == CLEAN_PROOF_QUALIFIER {
        return None;
    }
    if proof_qualifier_tokens(qualifiers).any(|token| token == SHOULD_PANIC_PROOF_QUALIFIER) {
        return Some("proof_qualifiers_should_panic");
    }
    if proof_qualifier_tokens(qualifiers).any(|token| token == TRIVIAL_SAFE_NO_ERROR_RULE_QUALIFIER)
    {
        return Some("proof_qualifiers_trivial_safe_no_error_rule");
    }
    Some("proof_qualifiers_not_clean")
}

pub(crate) fn proof_qualifier_failure_message(qualifiers: &str) -> String {
    match proof_qualifier_non_quality_reason(qualifiers) {
        None => String::new(),
        Some("proof_qualifiers_should_panic") => format!(
            "{qualifiers:?} is should-panic evidence, not replacement-quality; expected {CLEAN_PROOF_QUALIFIER:?}"
        ),
        Some("proof_qualifiers_trivial_safe_no_error_rule") => format!(
            "{qualifiers:?} is no-error-rule evidence, not replacement-quality; expected {CLEAN_PROOF_QUALIFIER:?}"
        ),
        Some(_) => format!("{qualifiers:?} is not clean"),
    }
}

fn proof_qualifier_tokens(qualifiers: &str) -> impl Iterator<Item = &str> {
    qualifiers.split(',').map(str::trim).filter(|token| !token.is_empty())
}
