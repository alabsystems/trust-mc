// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Implements the logic related to concrete playback

pub(crate) mod playback;
pub(crate) mod test_generator;

/// Only a validated, decided model of the supported encoding can be used as a
/// reproduction. Covers in an otherwise successful run have no CTREX category.
pub(crate) fn witness_is_usable(
    validation: crate::verification_result::ValidationStatus,
    category: Option<&crate::verification_result::CtrexCategory>,
    solver_undecided: bool,
    encoding_debt: bool,
) -> bool {
    use crate::verification_result::{CtrexCategory, ValidationStatus};
    validation == ValidationStatus::Validated
        && !solver_undecided
        && !encoding_debt
        && matches!(category, None | Some(CtrexCategory::Genuine))
}

#[cfg(test)]
mod tests {
    use super::witness_is_usable;
    use crate::verification_result::{CtrexCategory as C, ValidationStatus as V};

    #[test]
    fn playback_requires_a_validated_decided_supported_witness() {
        for category in [None, Some(C::Genuine)] {
            assert!(witness_is_usable(V::Validated, category.as_ref(), false, false));
            assert!(!witness_is_usable(V::Unvalidated, category.as_ref(), false, false));
            assert!(!witness_is_usable(V::Validated, category.as_ref(), true, false));
        }
        // A demoted proof can retain category=None. Sound over-approximation
        // can preserve its proof while inventing a reachable cover witness.
        assert!(!witness_is_usable(V::Validated, None, false, true));
        assert!(!witness_is_usable(V::Validated, Some(&C::Genuine), false, true));
        for category in [
            C::Unknown,
            C::EncodingGap { categories: vec!["unsupported".into()] },
            C::OverApproximation { categories: vec!["havoc".into()] },
        ] {
            assert!(!witness_is_usable(V::Validated, Some(&category), false, false));
        }
    }
}
