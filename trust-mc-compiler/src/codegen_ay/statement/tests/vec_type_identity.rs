// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Foreign Vec fields must survive BMC aggregate construction and byte storage.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

use super::*;
use crate::kani_middle::abi::LayoutOf;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::vec::Vec as Alias;
    mod exported { pub use std::vec::Vec as Reexport; }
    mod plain { #[repr(C)] pub struct Vec { pub value: u64, pub other: u64 } }
    mod generic { #[repr(C)] pub struct Vec<T> { pub value: T, pub other: u16 } }
    mod mimic { pub mod alloc { pub mod vec {
        #[repr(C)] pub struct Vec { pub value: u32, pub other: u64 }
    } } }
    pub fn identity(_: std::vec::Vec<u64>, _: Alias<u64>, _: exported::Reexport<u64>,
        _: plain::Vec, _: generic::Vec<u8>, _: mimic::alloc::vec::Vec) {}
    pub fn references(_: &std::vec::Vec<u64>, _: &mut Alias<u64>,
        _: &exported::Reexport<u64>, _: &plain::Vec, _: &mut generic::Vec<u8>,
        _: &mimic::alloc::vec::Vec) {}
    pub fn construct_plain(value: u64, other: u64) -> plain::Vec {
        plain::Vec { value, other }
    }
    pub fn construct_generic(value: u8, other: u16) -> generic::Vec<u8> {
        generic::Vec { value, other }
    }
    pub fn construct_mimic(value: u32, other: u64) -> mimic::alloc::vec::Vec {
        mimic::alloc::vec::Vec { value, other }
    }
"#;

#[test]
fn native_vec_bmc_representation_uses_actual_definition() {
    let completed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&completed);
    with_test_ay_ctx_for_source(SOURCE, move |ctx| {
        let body = find_instance_by_suffix(&ctx, "identity").body().expect("actual MIR");
        assert_eq!(body.arg_locals().len(), 6);
        let sorts: Vec<_> = body
            .arg_locals()
            .iter()
            .enumerate()
            .map(|(index, local)| {
                let TyKind::RigidTy(RigidTy::Adt(def, _)) = local.ty.kind() else {
                    panic!("actual ADT parameter required");
                };
                assert_eq!(StatementCodegen::is_native_vec_adt(def), index < 3);
                StatementCodegen::infer_sort_from_ty(local.ty).expect("actual ADT sort")
            })
            .collect();
        assert_eq!(sorts[0], sorts[1]);
        assert_eq!(sorts[0], sorts[2]);
        assert_eq!(sorts[0].datatype_sort().unwrap().constructors[0].fields.len(), 4);
        for (sort, widths) in sorts[3..].iter().zip([[64, 64], [8, 16], [32, 64]]) {
            assert_ne!(*sort, sorts[0]);
            let fields = &sort.datatype_sort().unwrap().constructors[0].fields;
            assert_eq!(fields.len(), 2, "foreign Vec retains exactly its declared fields");
            for (field, width) in fields.iter().zip(widths) {
                assert_eq!(field.sort, Sort::bitvec(width));
            }
        }
        let references = find_instance_by_suffix(&ctx, "references").body().unwrap();
        assert_eq!(references.arg_locals().len(), 6);
        for (index, local) in references.arg_locals().iter().enumerate() {
            assert_eq!(StatementCodegen::is_slice_or_array_ref_ty(local.ty), index < 3);
        }
        observed.store(true, Ordering::SeqCst);
    });
    assert!(completed.load(Ordering::SeqCst), "compiler callback must complete");
}

#[test]
fn native_foreign_vec_bmc_aggregate_preserves_declared_bytes() {
    let completed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&completed);
    with_test_ay_ctx_for_source(SOURCE, move |mut ctx| {
        ctx.init_memory();
        for (ordinal, suffix) in
            ["construct_plain", "construct_generic", "construct_mimic"].iter().enumerate()
        {
            let instance = find_instance_by_suffix(&ctx, suffix);
            let body = instance.body().expect("actual constructor MIR");
            let ty = body.locals()[0].ty;
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
            assert_eq!(body.arg_locals().len(), 2);
            for (index, local) in body.arg_locals().iter().enumerate() {
                let sort = StatementCodegen::infer_sort_from_ty(local.ty).unwrap();
                let value = Expr::bitvec_const(
                    if index == 0 { 3 } else { 7 },
                    sort.bitvec_width().unwrap(),
                );
                let base = codegen.ssa_base_name(&local_place(index + 1));
                codegen.env_update(base, value);
            }
            for block in &body.blocks {
                for statement in &block.statements {
                    codegen.codegen_statement(statement);
                }
            }
            let return_base = format!("{}::local_0", codegen.ctx.current_fn_name());
            let value = codegen.env_lookup(&return_base).cloned().expect("actual aggregate result");
            assert_eq!(value.sort().datatype_sort().unwrap().constructors[0].fields.len(), 2);
            let base = 4096 + ordinal as u128 * 64;
            codegen.store_typed_value_to_memory(Expr::bitvec_const(base, POINTER_WIDTH), value, ty);
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { panic!("actual ADT") };
            let fields = def.variants()[0].fields();
            assert_eq!(fields.len(), 2);
            let mut wrong_byte = Expr::bool_const(false);
            for (index, field) in fields.iter().enumerate() {
                let field_ty = crate::codegen_ay::shared::mono_ty::field_ty(field, &args).unwrap();
                let offset = LayoutOf::new(ty).field_offset(index).unwrap();
                let size = LayoutOf::new(field_ty).size_of().unwrap();
                let expected: u128 = if index == 0 { 3 } else { 7 };
                for byte in 0..size {
                    let actual = codegen
                        .ctx
                        .memory()
                        .clone()
                        .select(Expr::bitvec_const(base + (offset + byte) as u128, POINTER_WIDTH));
                    let expected = Expr::bitvec_const((expected >> (byte * 8)) & 255, 8);
                    wrong_byte = wrong_byte.or(actual.eq(expected).not());
                }
            }
            assert_unsat_for_violation(codegen.ctx, wrong_byte, "foreign_vec_byte", suffix);
            // The same real constraints must be satisfiable: byte equality
            // cannot pass only because aggregate construction became inconsistent.
            let mut live = codegen.ctx.bmc_vc.clone();
            live.violations.clear();
            live.model_queries.clear();
            live.add_violation(
                Violation::new(PropertyId::new(0), PropertyKind::Assertion, Expr::bool_const(true))
                    .with_smt_var(format!("foreign_vec_live_{suffix}")),
            );
            assert_eq!(
                run_ay_on_smt2_with_timeout(&emit_bmc(live).to_string(), AY_TEST_TIMEOUT_SECS)
                    .unwrap(),
                "sat"
            );
            let debt = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
            assert_eq!(
                debt.get(codegen.ctx.current_fn_name()).copied().unwrap_or(0),
                0,
                "foreign declared fields need no invented Vec data or undetermined byte store"
            );
        }
        observed.store(true, Ordering::SeqCst);
    });
    assert!(completed.load(Ordering::SeqCst), "compiler callback must complete");
}
