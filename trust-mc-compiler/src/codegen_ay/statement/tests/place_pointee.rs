// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for place_pointee.rs: pointee tracking and derived name resolution.
//!
//! Covers:
//! - `ensure_ref_pointee_for_place`: Derive ref_pointees from deref chains
//! - `ensure_derived_pointee_in_env`: Parse and resolve derived names
//!   (e.g., `fn::local_30_deref_field_0`)
//! - `synthesize_pointee_expr`: Create symbolic values for untracked pointees
//!
//! Part of #2016.

use super::*;

// =============================================================================
// ensure_ref_pointee_for_place — MIR-driven tests
// =============================================================================

/// Test that simple reference creates ref_pointees entry.
#[test]
fn test_ensure_ref_pointee_simple_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn simple_ref(x: u32) -> u32 {
            let r = &x;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "simple_ref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // After processing, ref_pointees should map the reference to its pointee
            assert!(
                !codegen.ref_pointees.is_empty(),
                "simple reference should create ref_pointees mapping"
            );
        },
    );
}

/// Test that nested reference (`&&x`) produces ref_pointees entries.
#[test]
fn test_ensure_ref_pointee_nested_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn nested_ref(x: u32) -> u32 {
            let r = &x;
            let rr = &r;
            **rr
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "nested_ref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // Should have at least 2 entries: r -> x, rr -> r
            assert!(
                codegen.ref_pointees.len() >= 2,
                "nested references should create multiple ref_pointees entries, got {}",
                codegen.ref_pointees.len()
            );
        },
    );
}

/// Test that reference to struct field creates ref_pointees entry.
#[test]
fn test_ensure_ref_pointee_struct_field() {
    with_test_ay_ctx_for_source(
        r#"
        pub struct Pair { a: u32, b: u32 }
        pub fn field_ref(p: Pair) -> u32 {
            let r = &p.a;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "field_ref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            assert!(
                !codegen.ref_pointees.is_empty(),
                "reference to struct field should create ref_pointees entry"
            );
        },
    );
}

/// Test that mutable reference creates ref_pointees entry.
#[test]
fn test_ensure_ref_pointee_mut_ref() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn mut_ref(mut x: u32) -> u32 {
            let r = &mut x;
            *r = 42;
            *r
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "mut_ref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            assert!(
                !codegen.ref_pointees.is_empty(),
                "mutable reference should create ref_pointees entry"
            );
        },
    );
}

// =============================================================================
// ensure_derived_pointee_in_env — name parsing tests
// =============================================================================

/// Test derived name parsing: fn::local_5_field_0.
#[test]
fn test_derived_name_parse_field() {
    let name = "my_fn::local_5_field_0";

    // Extract fn prefix
    let local_pos = name.find("::local_").unwrap();
    let fn_prefix = &name[..local_pos + 8]; // includes "::local_"
    assert_eq!(fn_prefix, "my_fn::local_");

    // Extract local number
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    assert_eq!(local_num_str, "5");

    // Get suffix
    let suffix_start = local_pos + 8 + local_num_str.len();
    let suffix = &name[suffix_start..];
    assert_eq!(suffix, "_field_0");
}

/// Test derived name parsing: fn::local_10_deref_field_2.
#[test]
fn test_derived_name_parse_deref_field() {
    let name = "my_fn::local_10_deref_field_2";

    let local_pos = name.find("::local_").unwrap();
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    assert_eq!(local_num_str, "10");

    let suffix_start = local_pos + 8 + local_num_str.len();
    let suffix = &name[suffix_start..];
    assert_eq!(suffix, "_deref_field_2");

    // Parse suffix components
    let rest = suffix.strip_prefix("_deref").unwrap();
    assert_eq!(rest, "_field_2");

    let field_rest = rest.strip_prefix("_field_").unwrap();
    let field_idx: usize = field_rest.parse().unwrap();
    assert_eq!(field_idx, 2);
}

/// Test derived name parsing: fn::local_3_variant_1_field_0.
#[test]
fn test_derived_name_parse_variant_field() {
    let name = "my_fn::local_3_variant_1_field_0";

    let local_pos = name.find("::local_").unwrap();
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    assert_eq!(local_num_str, "3");

    let suffix_start = local_pos + 8 + local_num_str.len();
    let suffix = &name[suffix_start..];
    assert_eq!(suffix, "_variant_1_field_0");

    let rest = suffix.strip_prefix("_variant_").unwrap();
    let variant_num: String = rest.chars().take_while(char::is_ascii_digit).collect();
    assert_eq!(variant_num, "1");
}

/// Test derived name parsing: name without ::local_ returns early.
#[test]
fn test_derived_name_parse_no_local_prefix() {
    let name = "some_global_var_field_0";
    let result = name.find("::local_");
    assert!(result.is_none(), "should not find ::local_ in non-local name");
}

/// Test derived name parsing: fn::local_ with non-numeric suffix.
#[test]
fn test_derived_name_parse_non_numeric_local() {
    let name = "my_fn::local_abc";
    let local_pos = name.find("::local_").unwrap();
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    assert!(local_num_str.is_empty(), "non-numeric local should produce empty string");
}

/// Test derived name with cast suffix: fn::local_5_cast_field_0.
#[test]
fn test_derived_name_parse_cast() {
    let name = "my_fn::local_5_cast_field_0";
    let local_pos = name.find("::local_").unwrap();
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    let suffix_start = local_pos + 8 + local_num_str.len();
    let suffix = &name[suffix_start..];
    assert_eq!(suffix, "_cast_field_0");

    let rest = suffix.strip_prefix("_cast").unwrap();
    assert_eq!(rest, "_field_0");
}

/// Test derived name with index by: fn::local_5_idx_by_3.
#[test]
fn test_derived_name_parse_idx_by() {
    let name = "my_fn::local_5_idx_by_3";
    let local_pos = name.find("::local_").unwrap();
    let after_local = &name[local_pos + 8..];
    let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
    let suffix_start = local_pos + 8 + local_num_str.len();
    let suffix = &name[suffix_start..];
    assert_eq!(suffix, "_idx_by_3");

    let rest = suffix.strip_prefix("_idx_by_").unwrap();
    let idx: usize = rest.parse().unwrap();
    assert_eq!(idx, 3);
}

// =============================================================================
// ensure_derived_pointee_in_env — MIR-driven tests
// =============================================================================

/// Test that field access through reference resolves the value in env.
#[test]
fn test_derived_pointee_env_resolution() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn deref_and_use(x: u32) -> u32 {
            let r = &x;
            let val = *r;
            val + 1
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "deref_and_use");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // The return place should have a value (from val + 1)
            let fn_name =
                codegen.ctx.current_fn().map_or_else(|| "unknown".to_string(), |f| f.name.clone());
            let return_base = format!("{}::local_0", fn_name);
            let entry = codegen.env_lookup(&return_base);
            assert!(entry.is_some(), "return place should have value after deref + add");
        },
    );
}

/// Test that multiple deref chains in one function are resolved.
#[test]
fn test_derived_pointee_multiple_chains() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn multi_deref(a: u32, b: u32) -> u32 {
            let ra = &a;
            let rb = &b;
            *ra + *rb
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "multi_deref");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // Should have at least 2 ref_pointees entries (ra -> a, rb -> b)
            assert!(
                codegen.ref_pointees.len() >= 2,
                "should track both reference chains, got {}",
                codegen.ref_pointees.len()
            );
        },
    );
}

// =============================================================================
// synthesize_pointee_expr — MIR-driven tests
// =============================================================================

/// Test that synthesize works for untracked references by creating symbolic values.
#[test]
fn test_synthesize_pointee_creates_symbolic() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn synth_target(x: u32) -> u32 { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "synth_target");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Call synthesize_pointee_expr for a place (arg 0)
            let place = Place { local: Local::from(1usize), projection: vec![] };
            let result = codegen.synthesize_pointee_expr("fn::synthetic_test", &place);

            assert!(result.is_some(), "synthesize_pointee_expr should create a symbolic value");
            if let Some(expr) = result {
                // Should be a variable (symbolic)
                assert!(
                    matches!(expr.value(), ExprValue::Var { .. }),
                    "synthesized value should be a symbolic variable"
                );
            }

            // The env should now have an entry for the synthesized name
            let env_entry = codegen.env_lookup("fn::synthetic_test");
            assert!(env_entry.is_some(), "synthesize should store result in env");
        },
    );
}

/// Test that repeated synthesize calls return consistent values.
#[test]
fn test_synthesize_pointee_consistent() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn synth_consistent(x: u32) -> u32 { x }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "synth_consistent");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let place = Place { local: Local::from(1usize), projection: vec![] };
            let result1 = codegen.synthesize_pointee_expr("fn::synth_test_2", &place);
            let result2 = codegen.synthesize_pointee_expr("fn::synth_test_2", &place);

            assert!(result1.is_some(), "first synthesize should succeed");
            assert!(result2.is_some(), "second synthesize should succeed");

            // Both should have the same sort
            if let (Some(e1), Some(e2)) = (&result1, &result2) {
                assert_eq!(*e1.sort(), *e2.sort(), "repeated synthesize should produce same sort");
            }
        },
    );
}

// =============================================================================
// slice::get durable pointee recovery — regression for the
// pointee_synthesis_fallback EncodingGap (r2_slice_get_probe)
// =============================================================================

/// A slice::get pointee published durably into `heap_pointees` (as
/// `codegen_slice_get` now does) must be recovered by
/// `ensure_derived_pointee_in_env` instead of falling through to
/// `synthesize_pointee_expr`.
///
/// The synthetic pointee name (`::slice_get_pointee_N`) is opaque: it carries no
/// `::local_` structure to reparse, so the derived-name parse path below the
/// recovery branch bails immediately (the `find("::local_")` guard returns
/// `None`). BASELINE (pre-fix) behaviour: this method returns `None` for such a
/// name and the caller synthesizes a fresh UNCONSTRAINED symbolic — incrementing
/// the `pointee_synthesis_fallback` telemetry and classifying the
/// r2_slice_get_probe counterexample as `EncodingGap` rather than `Genuine`.
/// POST-FIX: the exact constrained value stored in `heap_pointees` is recovered
/// and returned (and republished into env), so no synthesis occurs.
///
/// This drives the recovery branch directly (the full `a.get(i).copied()`
/// codegen path is exercised end-to-end only under the stage2 solve, which is
/// operator-run). Asserting the returned expr is *identical* to the stored
/// constant proves recovery fired: a synthesized value would be a freshly
/// declared `Var`, never this `bitvec_const`.
#[test]
fn test_slice_get_pointee_recovered_from_heap_pointees() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn get_copied_or(a: &[u8], i: usize, d: u8) -> u8 {
            a.get(i).copied().unwrap_or(d)
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "get_copied_or");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Mimic what codegen_slice_get publishes: a CONSTRAINED pointee value
            // stored in the durable heap_pointees map under an opaque synthetic
            // name (no `::local_` structure).
            let pointee_base = "get_copied_or::slice_get_pointee_0";
            let key: std::sync::Arc<str> = std::sync::Arc::from(pointee_base);
            // A distinctive constrained expression — never what synthesize returns
            // (synthesize hands back a freshly declared Var, not a constant).
            let constrained = Expr::bitvec_const(0xABu64, 8);
            codegen.heap_pointees.insert(key, constrained.clone());

            // Precondition: the opaque name is not already in env, so resolution
            // must fall to the heap_pointees recovery branch rather than the
            // fast-path env hit.
            assert!(
                codegen.env_lookup(pointee_base).is_none(),
                "precondition: synthetic pointee must not already be in env"
            );

            let resolved = codegen.ensure_derived_pointee_in_env(pointee_base);

            // Must recover the EXACT durable value — not None (pre-fix) and not a
            // fresh synthesized symbolic.
            assert!(resolved.is_some(), "recovery must not return None (pre-fix behaviour)");
            assert!(
                resolved.as_ref() == Some(&constrained),
                "ensure_derived_pointee_in_env must recover the constrained \
                 slice::get pointee from heap_pointees, not synthesize a fresh symbolic"
            );

            // And it must be republished into env for later lookups.
            assert!(
                codegen.env_lookup(pointee_base) == Some(&constrained),
                "recovered pointee must be republished into env"
            );
        },
    );
}

// =============================================================================
// Projection suffix naming — expression-level tests
// =============================================================================

/// Test projection suffix for Field.
#[test]
fn test_projection_suffix_field() {
    let base = "fn::local_5";
    let field_suffix = format!("{}_field_2", base);
    assert_eq!(field_suffix, "fn::local_5_field_2");
}

/// Test projection suffix for Deref.
#[test]
fn test_projection_suffix_deref() {
    let base = "fn::local_5";
    let deref_suffix = format!("{}_deref", base);
    assert_eq!(deref_suffix, "fn::local_5_deref");
}

/// Test projection suffix for Downcast (variant).
#[test]
fn test_projection_suffix_downcast() {
    let base = "fn::local_5";
    let variant_idx: usize = 1;
    let variant_suffix = format!("{}_variant_{}", base, variant_idx);
    assert_eq!(variant_suffix, "fn::local_5_variant_1");
}

/// Test projection suffix for Index.
#[test]
fn test_projection_suffix_index() {
    let base = "fn::local_5";
    let local_idx: usize = 3;
    let idx_suffix = format!("{}_idx_by_{}", base, local_idx);
    assert_eq!(idx_suffix, "fn::local_5_idx_by_3");
}

/// Test projection suffix for ConstantIndex.
#[test]
fn test_projection_suffix_constant_index() {
    let base = "fn::local_5";
    let offset: usize = 2;
    let cidx_suffix = format!("{}_cidx_{}", base, offset);
    assert_eq!(cidx_suffix, "fn::local_5_cidx_2");

    let cidx_end_suffix = format!("{}_cidx_end_{}", base, offset);
    assert_eq!(cidx_end_suffix, "fn::local_5_cidx_end_2");
}

/// Test projection suffix for Subslice.
#[test]
fn test_projection_suffix_subslice() {
    let base = "fn::local_5";
    let from: usize = 1;
    let to: usize = 3;
    let subslice_suffix = format!("{}_subslice_{}_{}", base, from, to);
    assert_eq!(subslice_suffix, "fn::local_5_subslice_1_3");

    let subslice_end_suffix = format!("{}_subslice_end_{}_{}", base, from, to);
    assert_eq!(subslice_end_suffix, "fn::local_5_subslice_end_1_3");
}

/// Test projection suffix for OpaqueCast.
#[test]
fn test_projection_suffix_cast() {
    let base = "fn::local_5";
    let cast_suffix = format!("{}_cast", base);
    assert_eq!(cast_suffix, "fn::local_5_cast");
}

/// Test compound projection suffix chain.
#[test]
fn test_projection_suffix_compound() {
    let mut base = "fn::local_5".to_string();
    base.push_str("_deref");
    base.push_str("_field_0");
    base.push_str("_variant_1");
    base.push_str("_field_2");
    assert_eq!(base, "fn::local_5_deref_field_0_variant_1_field_2");
}

// =============================================================================
// Helper
// =============================================================================
