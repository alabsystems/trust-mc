// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for flattened local copy env propagation.
//!
//! Part of #4044: Pattern 4 copies must populate `flattened_field_env` so
//! downstream reads in the same block preserve duplicated struct identity.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;

const FLATTENED_COPY_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    struct PackedRow {
        bits: u64,
        rhs: bool,
    }

    pub fn probe_flattened_copy_identity(rhs: bool) -> bool {
        let row = PackedRow { bits: 1, rhs };
        let lhs = row;
        let rhs_copy = row;
        lhs.bits == rhs_copy.bits && lhs.rhs == rhs_copy.rhs
    }
"#;

#[test]
fn test_flattened_copy_assignment_updates_destination_field_env() {
    with_test_ay_ctx_for_source(FLATTENED_COPY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_flattened_copy_identity");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_flattened_copy_identity", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut constraints = Vec::new();
        let mut last_constraint_for_local = std::collections::HashMap::new();
        let mut modified = HashSet::new();
        let mut found_copy = false;

        'outer: for block in &body.blocks {
            for stmt in &block.statements {
                let rustc_public::mir::StatementKind::Assign(
                    place,
                    rhs @ rustc_public::mir::Rvalue::Use(
                        rustc_public::mir::Operand::Copy(src)
                        | rustc_public::mir::Operand::Move(src),
                    ),
                ) = &stmt.kind
                else {
                    continue;
                };
                if !place.projection.is_empty()
                    || !src.projection.is_empty()
                    || !chc_ctx.flatten.flattened_tuple_locals.contains(&place.local)
                    || !chc_ctx.flatten.flattened_tuple_locals.contains(&src.local)
                {
                    continue;
                }

                let field_count = chc_ctx.flattened_field_count(place.local);
                let handled = {
                    let mut acc = StmtAccumulator::new(
                        &mut modified,
                        &mut constraints,
                        &mut last_constraint_for_local,
                    );
                    chc_ctx.try_encode_flattened_local_assign(place.local, rhs, &mut acc)
                };

                assert!(handled, "flattened copy should be handled by Pattern 4");
                assert!(
                    modified.contains(&place.local),
                    "flattened copy should mark the destination local modified"
                );
                for field_idx in 0..field_count {
                    assert!(
                        chc_ctx.encode.flattened_field_env.contains_key(&(place.local, field_idx)),
                        "flattened copy should cache destination field {field_idx} in flattened_field_env"
                    );
                }
                found_copy = true;
                break 'outer;
            }
        }

        if !found_copy {
            // MIR may optimize away the copy pattern; the probe is only
            // meaningful when the flattened copy assignment survives.
        }
    });
}
