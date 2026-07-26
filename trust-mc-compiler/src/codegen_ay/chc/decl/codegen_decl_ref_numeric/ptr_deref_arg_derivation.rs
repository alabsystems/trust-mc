// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pass 6: Pointer-cast-from-arg-ref derivation map.
//!
//! Traces AddressOf + Cast chains from argument reference locals to build
//! `ptr_deref_to_arg_pointee`. This enables referent resolution to follow
//! patterns like `as_array(&self)` where a raw pointer is created from
//! `&raw const (*self)`, cast to a different pointer type, then dereferenced.
//!
//! Part of #3596: portable/repr SIMD boundary recovery.

use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Build derivation map from pointer locals to argument reference pointees.
    ///
    /// Traces two patterns through MIR:
    /// 1. `_x = &raw const (*_arg)` where `_arg` is in `ref_arg_pointee_idx`
    ///    → `_x` maps to the same pointee state var index
    /// 2. `_x = cast(_y)` or `_x = Copy/Move(_y)` where `_y` is already in
    ///    the derivation map → `_x` inherits the same pointee
    ///
    /// This enables referent resolution to follow the `as_array` pattern:
    /// `self → &raw const (*self) → cast to *const [T; N] → deref`.
    pub(in crate::codegen_ay::chc) fn build_ptr_deref_to_arg_pointee(&mut self) {
        let mut derivation: HashMap<usize, usize> = HashMap::new();

        // Step 1: Seed from AddressOf patterns where source is an arg ref.
        // Pattern: _x = &raw const (*_arg) where _arg has ref_arg_pointee_idx entry.
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && let Rvalue::AddressOf(_, place) = rhs
                    && place.projection.len() == 1
                    && matches!(place.projection[0], ProjectionElem::Deref)
                    && let Some(&pointee_idx) =
                        self.ref_resolution.ref_arg_pointee_idx.get(&place.local)
                {
                    derivation.insert(lhs.local, pointee_idx);
                }
            }
        }

        if derivation.is_empty() {
            return;
        }

        // Step 2: Propagate through Cast and Copy/Move chains.
        let mut changed = true;
        while changed {
            changed = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && !derivation.contains_key(&lhs.local)
                    {
                        let src_local = match rhs {
                            Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                                if p.projection.is_empty() =>
                            {
                                Some(p.local)
                            }
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.projection.is_empty() =>
                            {
                                Some(p.local)
                            }
                            _ => None,
                        };
                        if let Some(src) = src_local
                            && let Some(&pointee_idx) = derivation.get(&src)
                        {
                            derivation.insert(lhs.local, pointee_idx);
                            changed = true;
                        }
                    }
                }
            }
        }

        debug!(
            count = derivation.len(),
            "CHC: built ptr_deref_to_arg_pointee derivation map (#3596)"
        );
        self.ref_resolution.ptr_deref_to_arg_pointee = derivation;
    }
}
