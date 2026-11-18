// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual Rust String definitions and declared foreign payload bytes.

use super::*;
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

const SOURCE: &str = r#"
#![allow(dead_code)]
use std::string::String as Alias;
mod exported { pub use std::string::String as Reexport; }
mod foreign { #[repr(C)] pub struct String { pub payload:usize } }
mod mimic { pub mod std { pub mod string {
    #[repr(C)] pub struct String { pub first:u32, pub second:u64 }
} } }
pub fn identities(_:std::string::String,_:Alias,_:exported::Reexport,_:foreign::String,_:mimic::std::string::String) {}
pub fn construct_foreign(payload:usize)->foreign::String { foreign::String{payload} }
pub fn construct_mimic(first:u32,second:u64)->mimic::std::string::String { mimic::std::string::String{first,second} }
"#;

#[test]
fn native_string_bmc_definition_and_alias_sorts_are_exact() {
    let completed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&completed);
    with_test_ay_ctx_for_source(SOURCE, move |ctx| {
        let body = find_instance_by_suffix(&ctx, "identities").body().unwrap();
        assert_eq!(body.arg_locals().len(), 5);
        let mut native = None;
        for (index, local) in body.arg_locals().iter().enumerate() {
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = local.ty.kind() else {
                panic!("actual ADT")
            };
            assert_eq!(StatementCodegen::is_native_string_adt(def), index < 3);
            let sort = StatementCodegen::infer_sort_from_ty(local.ty).unwrap();
            let fields = &sort.datatype_sort().unwrap().constructors[0].fields;
            if index < 3 {
                assert_eq!(fields.len(), 4);
                if let Some(expected) = &native {
                    assert_eq!(&sort, expected);
                } else {
                    native = Some(sort);
                }
            } else {
                assert_ne!(Some(&sort), native.as_ref());
                let widths = if index == 3 { vec![64] } else { vec![32, 64] };
                assert_eq!(fields.len(), widths.len());
                for (field, width) in fields.iter().zip(widths) {
                    assert_eq!(field.sort, Sort::bitvec(width));
                }
            }
        }
        observed.store(true, Ordering::SeqCst);
    });
    assert!(completed.load(Ordering::SeqCst), "actual compiler callback must complete");
}

#[test]
fn native_foreign_string_aggregate_and_bytes_preserve_declared_payloads() {
    let completed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&completed);
    with_test_ay_ctx_for_source(SOURCE, move |mut ctx| {
        ctx.init_memory();
        for (ordinal, suffix) in ["construct_foreign", "construct_mimic"].iter().enumerate() {
            let instance = find_instance_by_suffix(&ctx, suffix);
            let body = instance.body().unwrap();
            assert_eq!(body.blocks.len(), 1, "actual straight-line constructor");
            assert!(matches!(body.blocks[0].terminator.kind, TerminatorKind::Return));
            let ty = body.locals()[0].ty;
            ctx.set_current_fn(instance);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            for (index, local) in body.arg_locals().iter().enumerate() {
                let sort = StatementCodegen::infer_sort_from_ty(local.ty).unwrap();
                let value = Expr::bitvec_const(
                    if index == 0 { 3 } else { 7 },
                    sort.bitvec_width().unwrap(),
                );
                let base = cg.ssa_base_name(&local_place(index + 1));
                cg.env_update(base, value);
            }
            for statement in &body.blocks[0].statements {
                cg.codegen_statement(statement);
            }
            let base = format!("{}::local_0", cg.ctx.current_fn_name());
            let value = cg.env_lookup(&base).cloned().expect("actual returned aggregate");
            assert_eq!(
                value.sort().datatype_sort().unwrap().constructors[0].fields.len(),
                body.arg_locals().len()
            );
            let address = 4096 + ordinal as u128 * 64;
            cg.store_typed_value_to_memory(Expr::bitvec_const(address, POINTER_WIDTH), value, ty);
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
                panic!("actual declared ADT")
            };
            let fields = def.variants()[0].fields();
            assert_eq!(fields.len(), body.arg_locals().len());
            let mut wrong = Expr::bool_const(false);
            for (index, field) in fields.iter().enumerate() {
                let field_ty = crate::codegen_ay::shared::mono_ty::field_ty(field, &args).unwrap();
                let offset = LayoutOf::new(ty).field_offset(index).unwrap();
                let size = LayoutOf::new(field_ty).size_of().unwrap();
                let expected: u128 = if index == 0 { 3 } else { 7 };
                for byte in 0..size {
                    let actual = cg.ctx.memory().clone().select(Expr::bitvec_const(
                        address + (offset + byte) as u128,
                        POINTER_WIDTH,
                    ));
                    wrong = wrong
                        .or(actual.eq(Expr::bitvec_const((expected >> (byte * 8)) & 255, 8)).not());
                }
            }
            assert_unsat_for_violation(cg.ctx, wrong, "foreign_string_byte", suffix);
            let mut live = cg.ctx.bmc_vc.clone();
            live.violations.clear();
            live.model_queries.clear();
            live.add_violation(
                Violation::new(PropertyId::new(0), PropertyKind::Assertion, Expr::bool_const(true))
                    .with_smt_var(format!("foreign_string_live_{suffix}")),
            );
            assert_eq!(
                run_ay_on_smt2_with_timeout(&emit_bmc(live).to_string(), AY_TEST_TIMEOUT_SECS)
                    .unwrap(),
                "sat"
            );
            let debt = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            assert_eq!(
                debt.get(cg.ctx.current_fn_name()).copied().unwrap_or(0),
                0,
                "foreign payload bytes need no native String assumptions"
            );
        }
        observed.store(true, Ordering::SeqCst);
    });
    assert!(completed.load(Ordering::SeqCst), "actual compiler callback must complete");
}
