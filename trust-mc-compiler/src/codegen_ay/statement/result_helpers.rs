// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Result base-name lookup helpers for AY codegen.
//!
//! Extracted from `result.rs`. These helpers resolve operands to their
//! environment base names for Result values (both direct/owned and reference).

use rustc_public::mir::Operand;
use std::sync::Arc;
use tracing::{debug, warn};

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Get the base name of a Result from a direct (owned) operand.
    ///
    /// For unwrap_or(self, default) which takes ownership, the operand IS the Result value.
    pub(super) fn get_result_base_direct(&mut self, operand: &Operand) -> Option<Arc<str>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let base_name = self.ssa_base_name(place);

                // Check flattened: base_name.0 exists
                let discrim_name = crate::codegen_ay::names::discrim_name(&base_name);
                if self.env_lookup(&discrim_name).is_some() {
                    debug!("Result::unwrap_or: found flattened Result at {}", base_name);
                    return Some(base_name.into());
                }

                // Check native SMT datatype
                if self.env_lookup(&base_name).is_some() {
                    debug!("Result::unwrap_or: found native SMT Result at {}", base_name);
                    return Some(base_name.into());
                }

                debug!("Result::unwrap_or: direct lookup failed for '{}'", base_name);
                None
            }
            _ => {
                // external enum: Operand
                debug!("Result::unwrap_or: expected Copy/Move operand, got {:?}", operand);
                None
            }
        }
    }

    /// Get the base name of a Result from a reference operand.
    ///
    /// Uses `ref_pointees` to find the actual pointee base name.
    pub(super) fn get_result_base_from_ref(&mut self, operand: &Operand) -> Option<Arc<str>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ref_base = self.ssa_base_name(place);
                if let Some(pointee) = self.ref_pointees.get(ref_base.as_str()) {
                    Some(Arc::clone(pointee))
                } else {
                    warn!(
                        "Result method: ref_pointees lookup failed for '{}' - reference was not tracked",
                        ref_base
                    );
                    None
                }
            }
            _ => {
                // external enum: Operand
                warn!("Result method: expected Copy/Move operand, got {:?}", operand);
                None
            }
        }
    }
}
