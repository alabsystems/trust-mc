// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::Sort;
use rustc_public::mir::{Body, TerminatorKind};
use std::collections::{HashMap, HashSet};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn none() -> bool { let value = &(123u64, (9u8, None::<bool>)); value.1.1.is_none() }
    pub fn some_false() -> bool { let value = &(123u64, (9u8, Some(false))); value.1.1.is_none() }
    pub fn some_true() -> bool { let value = &(123u64, (9u8, Some(true))); value.1.1.is_some() }
    pub fn tuple_payload() -> bool {
        let value = &(123u64, (9u8, Some((257u16, false)))); value.1.1.is_some()
    }
    pub fn character() -> bool { let value = &(123u64, (9u8, Some('é'))); value.1.1.is_none() }
    pub fn joined(choose: bool) -> bool {
        let value = if choose { &(123u64, (9u8, None::<bool>)) }
            else { &(123u64, (9u8, Some(false))) };
        value.1.1.is_none()
    }
    pub fn reborrow() -> bool {
        let value = &(123u64, (9u8, None::<bool>)); let alias = &*value;
        let option = &alias.1.1; let again = &*option; again.is_none()
    }
    pub fn erased() -> bool {
        let value = &(123u64, (9u8, None::<bool>));
        let erased = value as *const _ as *const ();
        let restored = unsafe { &*(erased as *const (u64, (u8, Option<bool>))) };
        restored.1.1.is_none()
    }
    static STATIC_VALUE: (u64, (u8, Option<bool>)) = (123, (9, None));
    pub fn static_ref() -> bool { let value = &STATIC_VALUE; value.1.1.is_none() }
    pub mod lookalike {
        pub enum Option<T> { None, Some(T) }
        impl<T> Option<T> { pub fn is_none(&self) -> bool { panic!("custom method must run") } }
    }
    pub fn custom() -> bool {
        let value = &(123u64, (9u8, lookalike::Option::<bool>::None)); value.1.1.is_none()
    }
    pub fn other_method() -> bool {
        trait Other { fn is_none(&self) -> bool; }
        impl Other for Option<bool> { fn is_none(&self) -> bool { panic!("override") } }
        let value = &(123u64, (9u8, None::<bool>)); Other::is_none(&value.1.1)
    }
    pub fn rewritten_alias() -> bool {
        let mut value = &(123u64, (9u8, None::<bool>));
        let alias = &mut value; *alias = &(123u64, (9u8, Some(false)));
        value.1.1.is_none()
    }
"#;

fn call(body: &Body) -> (Operand, Vec<Operand>) {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).ok()?.kind()
            else {
                return None;
            };
            let name = def.name();
            (name.ends_with("::is_none")
                || name.ends_with("::is_some")
                || name.ends_with("::custom_is_none"))
            .then(|| (func.clone(), args.clone()))
        })
        .expect("predicate call in compiler-produced MIR")
}

fn declarations(sort: &Sort, seen: &mut HashSet<String>, output: &mut String) {
    if let Some(dt) = sort.datatype_sort()
        && seen.insert(dt.name.to_string())
    {
        for ctor in &dt.constructors {
            for field in &ctor.fields {
                declarations(&field.sort, seen, output);
            }
        }
        output.push_str(&ay_bindings::Constraint::declare_datatype(dt.clone()).to_string());
        output.push('\n');
    }
}

fn check_truth(formula: Expr, sort: &Sort, expected: bool) {
    let mut defs = String::new();
    declarations(sort, &mut HashSet::new(), &mut defs);
    let negated = if expected { formula.not() } else { formula };
    let input = format!("(set-logic ALL)\n{defs}(assert {negated})\n(check-sat)\n");
    let commands = ay_frontend::parse(&input).unwrap();
    let output = ay_dpll::Executor::new().execute_all(&commands).unwrap();
    assert!(output.iter().any(|line| line.trim() == "unsat"), "{input}\n{output:?}");
}

#[test]
fn native_nested_option_predicates_preserve_none_and_active_payload_values() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, expected) in [
            ("none", true),
            ("some_false", false),
            ("some_true", true),
            ("tuple_payload", true),
            ("reborrow", true),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (func, args) = call(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let (ty, _) = chc.promoted_option_predicate_identity(&func).unwrap();
            let before = chc.ref_resolution.const_ref_memory_inits.clone();
            let objects = chc.ref_resolution.const_ref_objects.clone();
            let value =
                chc.promoted_option_predicate(&func, &args).unwrap_or_else(|| panic!("{name}"));
            assert!(value.sort().is_bool());
            check_truth(value, &ChcCtx::translate_ty(ty).unwrap(), expected);
            assert_eq!(before, chc.ref_resolution.const_ref_memory_inits, "no new late seeds");
            assert_eq!(
                objects, chc.ref_resolution.const_ref_objects,
                "reference identity unchanged"
            );
        }
    });
}

#[test]
fn native_nested_option_refuses_joins_erasure_wrong_width_and_custom_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "joined",
            "erased",
            "character",
            "static_ref",
            "custom",
            "other_method",
            "rewritten_alias",
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (func, args) = call(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            assert!(chc.promoted_option_predicate(&func, &args).is_none(), "{name}");
        }
    });
}

#[test]
fn native_nested_option_requires_closed_seeded_origin_and_actual_receiver_type() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "none").callee_body().unwrap();
        let (func, args) = call(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "none", ChcConfig::default());
        chc.declare_block_relations();
        assert!(chc.promoted_option_predicate(&func, &args).is_some());
        chc.ref_resolution.object_seeding_closed = false;
        assert!(chc.promoted_option_predicate(&func, &args).is_none());
        chc.ref_resolution.object_seeding_closed = true;
        let types = std::mem::take(&mut chc.ref_resolution.seeded_object_types);
        assert!(chc.promoted_option_predicate(&func, &args).is_none());
        chc.ref_resolution.seeded_object_types = types;
        let values = std::mem::take(&mut chc.ref_resolution.const_ref_values);
        assert!(chc.promoted_option_predicate(&func, &args).is_none());
        chc.ref_resolution.const_ref_values = values;
        let source = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(local, decl)| {
                shared_pointee(decl.ty)
                    .filter(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(_))))
                    .map(|_| local)
            })
            .unwrap();
        let wrong = Operand::Copy(Place { local: source, projection: vec![] });
        assert!(chc.promoted_option_predicate(&func, &[wrong]).is_none());
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func.ty(body.locals()).unwrap().kind() else {
            panic!("function")
        };
        let _stubs =
            crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from([(def, def)]));
        assert!(chc.promoted_option_predicate(&func, &args).is_none());
    });
}
