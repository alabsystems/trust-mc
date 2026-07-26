// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven assignment codegen tests.
//!
//! 63 trivial AY-only expression tests deleted per rule #2312 and #2482
//! (tested AY Expr/Sort construction, not production codegen_assign paths).
//! Remaining tests use with_test_ay_ctx_for_source to exercise the MIR pipeline.

use super::*;

// =============================================================================
// MIR-driven assignment translation
// =============================================================================

#[test]
fn test_codegen_statement_assign_updates_env_mapping() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn assign_from_copy(input: u32) -> u32 {
            let tmp = input;
            tmp
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "assign_from_copy");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let assign_stmt = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find(|stmt| {
                    matches!(
                        &stmt.kind,
                        StatementKind::Assign(_, Rvalue::Use(Operand::Copy(_) | Operand::Move(_)))
                    )
                })
                .expect("expected copy assignment");

            let lhs = match &assign_stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!("filtered to assign"),
            };
            let lhs_base = codegen.ssa_base_name(lhs);
            assert!(
                codegen.env_lookup(&lhs_base).is_none(),
                "lhs should be absent before codegen_statement"
            );

            codegen.codegen_statement(assign_stmt);
            let updated = codegen.env_lookup(&lhs_base).cloned().expect("lhs env entry");
            assert!(updated.sort().is_bitvec());
        },
    );
}

#[test]
fn test_codegen_statement_array_index_assignment_updates_array_env() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn assign_array_slot(mut arr: [u32; 4], idx: usize, val: u32) -> [u32; 4] {
            arr[idx] = val;
            arr
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "assign_array_slot");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let array_assign_stmt = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find(|stmt| {
                    matches!(
                        &stmt.kind,
                        StatementKind::Assign(
                            Place { projection, .. },
                            _
                        ) if projection.len() == 1
                            && matches!(projection.first(), Some(ProjectionElem::Index(_)))
                    )
                })
                .expect("expected arr[idx] assignment");

            let lhs = match &array_assign_stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!("filtered to assign"),
            };
            let mut base_place = lhs.clone();
            base_place.projection.clear();
            let lhs_base = codegen.ssa_base_name(&base_place);
            assert!(
                codegen.env_lookup(&lhs_base).is_none(),
                "array base should start unset in env"
            );

            if let Some(ProjectionElem::Index(idx_local)) = lhs.projection.first() {
                // Seed idx local so codegen_assign can find index expression.
                let idx_place = Place { local: *idx_local, projection: vec![] };
                let _ = codegen.codegen_place(&idx_place).expect("idx place");
            }
            codegen.codegen_statement(array_assign_stmt);

            let updated = codegen
                .env_lookup(&lhs_base)
                .cloned()
                .expect("array base should be updated after arr[idx] assignment");
            assert!(updated.sort().is_array());
        },
    );
}

/// Test that ZST assignments are skipped (codegen_assign.rs:18-25).
/// Unit type `()` has zero size and should not produce any env update.
#[test]
fn test_codegen_statement_zst_assignment_skipped() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn zst_assign() {
            let _x: () = ();
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "zst_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            // Get fn_name before codegen borrows ctx
            let fn_name = ctx.current_fn().map(|f| f.name.clone()).unwrap();
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements in the function
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // ZST locals should NOT appear in the environment
            // (codegen_assign returns early for ZSTs)
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_none(), "ZST local should not have env entry, but found {:?}", entry);
        },
    );
}

/// Test checked binary op through MIR: addition with overflow check.
/// codegen_assign_checked_binary_op produces field_0 (result) and field_1 (overflow).
/// Note: plain `a + b` reliably produces CheckedBinaryOp in debug MIR;
/// `.overflowing_add()` may be lowered to an intrinsic call instead.
#[test]
fn test_codegen_statement_checked_add_produces_fields() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn checked_add_mir(a: u32, b: u32) -> u32 {
            a + b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "checked_add_mir");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let checked_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::CheckedBinaryOp(..)))
                });

            let stmt = checked_stmt
                .expect("MIR for checked_add_mir should contain a CheckedBinaryOp statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            // CheckedBinaryOp should produce field_0 (result) and field_1 (overflow)
            let field_0_key = format!("{}_field_0", lhs_base);
            let field_1_key = format!("{}_field_1", lhs_base);
            let result_expr = codegen
                .env_lookup(&field_0_key)
                .expect("CheckedBinaryOp add should produce field_0 (result)");
            let overflow_expr = codegen
                .env_lookup(&field_1_key)
                .expect("CheckedBinaryOp add should produce field_1 (overflow)");

            assert!(result_expr.sort().is_bitvec());
            assert!(overflow_expr.sort().is_bool());
        },
    );
}

/// Test reference assignment tracking: `_ref = &_local` populates ref_pointees.
/// codegen_assign.rs:741-783.
#[test]
fn test_codegen_statement_ref_populates_ref_pointees() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn ref_tracking(x: u32) -> u32 {
            let r = &x;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "ref_tracking");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements to populate ref_pointees
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // After processing, at least one ref_pointees entry should exist
            // (from the `let r = &x` assignment)
            assert!(
                !codegen.ref_pointees.is_empty(),
                "ref_pointees should have entries after processing Ref assignment"
            );
        },
    );
}

/// Test constant assignment: `let x = 42u32` produces bitvec in env.
#[test]
fn test_codegen_statement_const_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn const_assign() -> u32 {
            42u32
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "const_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a constant assignment
            let const_stmt = body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Use(Operand::Constant(_))))
            });

            let stmt =
                const_stmt.expect("MIR for const_assign should contain a Use(Constant) assignment");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let expr = codegen
                .env_lookup(&lhs_base)
                .expect("constant assignment should produce env entry");
            assert!(expr.sort().is_bitvec());
        },
    );
}

/// Test bool assignment: `let flag = true` produces bool in env.
#[test]
fn test_codegen_statement_bool_const_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn bool_assign() -> bool {
            true
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "bool_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let fn_name = ctx.current_fn().map(|f| f.name.clone()).unwrap();
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // The return place should have an entry (bool)
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "bool const assignment should produce env entry");
            if let Some(expr) = entry {
                assert!(expr.sort().is_bool());
            }
        },
    );
}

/// Test Rvalue::Use(Copy) assignment with multiple locals.
#[test]
fn test_codegen_statement_copy_chain() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn copy_chain(a: u64) -> u64 {
            let b = a;
            let c = b;
            c
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "copy_chain");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let fn_name = ctx.current_fn().map(|f| f.name.clone()).unwrap();
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // At least the return place and one intermediate should have entries
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "copy chain return place should have env entry");
        },
    );
}

/// Test that processing all statements in a multi-block function
/// doesn't panic and populates env entries.
#[test]
fn test_codegen_statement_multi_block_function() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn multi_block(x: u32) -> u32 {
            if x > 10 {
                x + 1
            } else {
                x + 2
            }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "multi_block");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Should have multiple basic blocks due to the if/else
            assert!(body.blocks.len() >= 2, "multi_block should have at least 2 basic blocks");

            // Process all statements without panic
            let mut stmt_count = 0;
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                    stmt_count += 1;
                }
            }
            assert!(stmt_count > 0, "should process at least one statement");
        },
    );
}

/// Test Repeat rvalue through MIR: `[0u32; 4]` produces array in env.
#[test]
fn test_codegen_statement_repeat_array_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn repeat_assign() -> [u32; 4] {
            [0u32; 4]
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "repeat_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a Repeat assignment
            let repeat_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Repeat(..)))
                });

            let stmt = repeat_stmt.expect("MIR for repeat_array should contain a Repeat statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let entry =
                codegen.env_lookup(&lhs_base).expect("Repeat assignment should produce env entry");
            assert!(entry.sort().is_array(), "Repeat should produce array sort");
        },
    );
}

/// Test Cast assignment through MIR: u32 -> u64 widening.
#[test]
fn test_codegen_statement_cast_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn cast_assign(x: u32) -> u64 {
            x as u64
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "cast_assign");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a Cast assignment
            let cast_stmt = body
                .blocks
                .iter()
                .flat_map(|bb| bb.statements.iter())
                .find(|stmt| matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::Cast(..))));

            let stmt = cast_stmt.expect("MIR for cast_assign should contain a Cast statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let entry =
                codegen.env_lookup(&lhs_base).expect("Cast assignment should produce env entry");
            assert!(entry.sort().is_bitvec(), "u32->u64 cast should produce bitvec");
        },
    );
}

/// Test binary op (non-checked) through MIR: `a & b` (bitwise AND).
/// Note: `wrapping_add` may be lowered to an intrinsic call rather than
/// a BinaryOp rvalue. Bitwise ops reliably produce BinaryOp in MIR.
#[test]
fn test_codegen_statement_binary_op_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn bitwise_and(a: u32, b: u32) -> u32 {
            a & b
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "bitwise_and");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a BinaryOp assignment
            let binop_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::BinaryOp(..)))
                });

            let stmt = binop_stmt.expect("MIR for bitwise_and should contain a BinaryOp statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let entry = codegen
                .env_lookup(&lhs_base)
                .expect("BinaryOp assignment should produce env entry");
            assert!(entry.sort().is_bitvec(), "u32 add should produce bitvec");
        },
    );
}

/// Test UnaryOp through MIR: bitwise not.
#[test]
fn test_codegen_statement_unary_op_assignment() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn unary_not(x: u32) -> u32 {
            !x
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "unary_not");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find a UnaryOp assignment
            let unop_stmt =
                body.blocks.iter().flat_map(|bb| bb.statements.iter()).find(|stmt| {
                    matches!(&stmt.kind, StatementKind::Assign(_, Rvalue::UnaryOp(..)))
                });

            let stmt = unop_stmt.expect("MIR for unary_not should contain a UnaryOp statement");
            let lhs = match &stmt.kind {
                StatementKind::Assign(lhs, _) => lhs,
                _ => unreachable!(),
            };
            let lhs_base = codegen.ssa_base_name(lhs);

            codegen.codegen_statement(stmt);

            let entry =
                codegen.env_lookup(&lhs_base).expect("UnaryOp assignment should produce env entry");
            assert!(entry.sort().is_bitvec(), "u32 bitwise not should produce bitvec");
        },
    );
}
