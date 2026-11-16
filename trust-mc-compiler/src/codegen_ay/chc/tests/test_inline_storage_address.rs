// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Storage custody, native encoding, and bounded AY semantic controls.
#![cfg(trust_toolchain)]

use super::common::*;
use super::test_trust_box_new::mem_config;
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, ProjectionElem, StatementKind, TerminatorKind};
use std::collections::{BTreeMap, BTreeSet};

const SOURCE: &str = r#"
#![allow(dead_code, unused_assignments)]
#[repr(C)] pub struct Pair { first: u64, second: u64 }
impl Pair {
    #[inline(never)] pub fn mutable_first(&mut self) -> *mut u64 { &raw mut self.first }
    #[inline(never)] pub fn shared_first(&self) -> *const u64 { &raw const self.first }
    #[inline(never)] pub fn mutable_second(&mut self) -> *mut u64 { &raw mut self.second }
    #[inline(never)] pub fn shared_second(&self) -> *const u64 { &raw const self.second }
    #[inline(never)] pub fn effectful(&mut self) -> *mut u64 {
        self.first = 42; &raw mut self.second
    }
    #[inline(never)] pub fn branching(&self) -> *const u64 {
        if self.first == 0 { &raw const self.first } else { &raw const self.second }
    }
    #[inline(never)] pub fn numeric(&self) -> *mut u64 { self.second as *mut u64 }
    #[inline(never)] pub fn expired_local(&self) -> *const u64 {
        let local = 7u64; &raw const local
    }
}
pub fn address_evidence() -> (*mut u64, *const u64, *mut u64, *const u64,
                             *mut u64, *const u64, *mut u64, *const u64) {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    (a.mutable_first(), a.shared_first(), a.mutable_second(), a.shared_second(),
     b.mutable_first(), b.shared_first(), b.mutable_second(), b.shared_second())
}
pub fn retargeted_carrier() -> *mut u64 {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    let mut carrier = &mut a; carrier = &mut b; carrier.mutable_second()
}
pub fn exposed_carrier() -> *mut u64 {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    let mut carrier = &mut a;
    let slot = &raw mut carrier;
    unsafe { *slot = &mut b; }
    carrier.mutable_second()
}
pub fn effectful_getter() -> *mut u64 {
    let mut value = Pair { first: 7, second: 7 }; value.effectful()
}
pub fn branching_getter() -> *const u64 {
    let value = Pair { first: 7, second: 7 }; value.branching()
}
pub fn numeric_pointer_value() -> *mut u64 {
    let value = Pair { first: 7, second: 7 }; value.numeric()
}
pub fn expired_local_getter() -> *const u64 {
    let value = Pair { first: 7, second: 7 }; value.expired_local()
}
pub fn retargeted_result() -> *mut u64 {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    let mut pointer = a.mutable_second(); pointer = b.mutable_second(); pointer
}
pub fn exposed_result() -> *mut u64 {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    let mut pointer = a.mutable_second();
    let slot = &raw mut pointer;
    unsafe { *slot = &raw mut b.second; }
    pointer
}
pub fn copied_exposed_result() -> *mut u64 {
    let mut a = Pair { first: 7, second: 7 };
    let mut b = Pair { first: 7, second: 7 };
    let pointer = a.mutable_second(); let mut alias = pointer;
    let slot = &raw mut alias;
    unsafe { *slot = &raw mut b.second; }
    alias
}
pub fn shared_capability_upgrade() -> *mut u64 {
    let value = Pair { first: 7, second: 7 }; value.shared_second() as *mut u64
}
pub fn store_second_preserves_first() {
    let mut value = Pair { first: 7, second: 1 };
    unsafe { *value.mutable_second() = 9; }
    assert!(unsafe { *value.shared_second() } == 9);
    assert!(unsafe { *value.shared_first() } == 7);
}
pub fn equal_owners_keep_distinct_storage() {
    let mut a = Pair { first: 7, second: 1 };
    let b = Pair { first: 7, second: 1 };
    unsafe { *a.mutable_second() = 9; }
    assert!(unsafe { *a.shared_second() } == 9);
    assert!(unsafe { *b.shared_second() } == 1);
    assert!(unsafe { *a.shared_first() } == 7);
}
pub fn store_second_bug() {
    let mut value = Pair { first: 7, second: 1 };
    unsafe { *value.mutable_second() = 9; }
    assert!(unsafe { *value.shared_second() } == 1);
}
pub fn copied_second_preserves_first() {
    let mut value = Pair { first: 7, second: 1 };
    let pointer = value.mutable_second(); let copied = pointer;
    unsafe { *copied = 9; }
    assert!(unsafe { *value.shared_second() } == 9);
    assert!(unsafe { *value.shared_first() } == 7);
}
pub fn dangling_field_store() {
    let pointer;
    { let mut value = Pair { first: 7, second: 1 }; pointer = value.mutable_second(); }
    unsafe { *pointer = 9; }
}
"#;

// Match the actual driver/SDK MIR policy. The generic native test context
// strips storage markers at its default MIR opt level and cannot witness the
// end of the inner Pair's storage. Do not manufacture markers in the body.
fn with_storage_address_ctx<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(crate::codegen_ay::context::AYCtx<'tcx, 'static>) + Send,
{
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags(
        source,
        &["-Cpanic=abort", "-Zmir-enable-passes=-RemoveStorageMarkers", "-Zinline-mir=no"],
        callback,
    );
}

fn retain_storage_artifact(label: &str, extension: &str, text: &str) {
    use std::io::Write;
    let Some(directory) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") else { return };
    let directory = std::path::PathBuf::from(directory);
    std::fs::create_dir_all(&directory).expect("native storage artifact directory");
    let path = directory.join(format!("storage_{label}.{extension}"));
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap_or_else(|error| panic!("retain {}: {error}", path.display()));
    output.write_all(text.as_bytes()).expect("retain complete native storage artifact");
}

fn retain_storage_body(label: &str, body: &Body) {
    retain_storage_artifact(label, "mir", &format!("{body:#?}\n"));
}

fn resolve_call(body: &Body, bb: usize) -> Option<(Instance, &[Operand])> {
    let TerminatorKind::Call { func, args, .. } = &body.blocks[bb].terminator.kind else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(body.locals()).ok()?.kind() else {
        return None;
    };
    Some((Instance::resolve(def, &generics).ok()?, args))
}

fn install_call_liveness(context: &mut ChcCtx<'_, '_>, bb: usize) {
    let before = context.body.blocks[bb].statements.len();
    install_statement_liveness(context, bb, before);
}

fn install_statement_liveness(context: &mut ChcCtx<'_, '_>, bb: usize, before: usize) {
    context.current_encode_bb = bb;
    context.liveness.dead_locals = context.liveness.dead_locals_at_entry[bb].clone();
    context.liveness.maybe_dead_locals = context.liveness.maybe_dead_locals_at_entry[bb].clone();
    for statement in context.body.blocks[bb].statements.iter().take(before) {
        match &statement.kind {
            StatementKind::StorageLive(local) => {
                context.liveness.dead_locals.remove(local);
                context.liveness.maybe_dead_locals.remove(local);
            }
            StatementKind::StorageDead(local) => {
                context.liveness.dead_locals.insert(*local);
                context.liveness.maybe_dead_locals.insert(*local);
            }
            _ => {}
        }
    }
}

fn retain_exact_native_assertions(
    tcx: TyCtxt<'_>,
    body: &Body,
    vc: &trust_mc_core::chc::ChcVc,
    name: &str,
    label: &str,
) -> Vec<String> {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
    use trust_mc_core::violation::PropertyKind;
    let messages: &[&str] = match name {
        "store_second_preserves_first" | "copied_second_preserves_first" => &[
            "assertion failed: unsafe { *value.shared_second() } == 9",
            "assertion failed: unsafe { *value.shared_first() } == 7",
        ],
        "equal_owners_keep_distinct_storage" => &[
            "assertion failed: unsafe { *a.shared_second() } == 9",
            "assertion failed: unsafe { *b.shared_second() } == 1",
            "assertion failed: unsafe { *a.shared_first() } == 7",
        ],
        "store_second_bug" => &["assertion failed: unsafe { *value.shared_second() } == 1"],
        _ => panic!("unregistered assertion fixture {label}: {name}"),
    };
    let mut relations = Vec::new();
    for expected in messages {
        let mut sites = Vec::new();
        for bb in 0..body.blocks.len() {
            let TerminatorKind::Call { target: None, .. } = &body.blocks[bb].terminator.kind else {
                continue;
            };
            let Some((instance, args)) = resolve_call(body, bb) else { continue };
            if crate::kani_middle::transform::instance_has_unit_stub(&instance)
                || !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                    tcx,
                    rustc_internal::internal(tcx, instance.def.def_id()),
                    &["panicking", "panic"],
                )
            {
                continue;
            }
            let [Operand::Constant(message)] = args else { continue };
            let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = message.const_.ty().kind() else {
                continue;
            };
            if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
                continue;
            }
            let text = const_pointer::const_bytes(&message.const_).and_then(|bytes| {
                let (_, window) = const_pointer::fixed_pointee(tcx, &bytes, 0, pointee)?;
                String::from_utf8(window.read_data_bytes(0, window.len())?).ok()
            });
            if text.as_deref() == Some(*expected) {
                sites.push(bb);
            }
        }
        assert_eq!(
            sites.len(),
            1,
            "retain exact native assertion {label} ({name}): {expected}; MIR={body:#?}"
        );
        let properties: Vec<_> = vc
            .properties
            .iter()
            .filter(|property| property.bb == sites[0] && property.kind == PropertyKind::Panic)
            .collect();
        assert_eq!(properties.len(), 1, "assertion {label} ({name}): {expected}");
        let property = properties[0];
        if name.ends_with("bug") {
            assert!(
                property.discharged_at_encode.is_none(),
                "the exact Bug assertion cannot disappear: {label} ({name})"
            );
        }
        assert!(
            vc.rules.iter().any(|rule| rule.head.name.as_str() == property.relation.as_str()
                && rule.body.relation.is_some()),
            "retain the assertion's guarded error rule: {label} ({name}): {expected}"
        );
        relations.push(property.relation.clone());
    }
    relations
}

#[test]
fn native_inline_storage_address_shared_mut_layout_and_owner_identity() {
    with_storage_address_ctx(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "address_evidence").body().unwrap();
        retain_storage_body("address_evidence_native", &body);
        let mut context = ChcCtx::new(ctx.tcx, &body, "address_evidence", mem_config());
        context.declare_block_relations();
        let mut owners: BTreeMap<usize, (u32, BTreeSet<(usize, u32)>)> = BTreeMap::new();
        let mut inspected = 0;
        for bb in 0..body.blocks.len() {
            let Some((instance, args)) = resolve_call(&body, bb) else { continue };
            let path = instance.def.name();
            let (field, offset) =
                if path.ends_with("mutable_first") || path.ends_with("shared_first") {
                    (0, 0)
                } else if path.ends_with("mutable_second") || path.ends_with("shared_second") {
                    (1, 8)
                } else {
                    continue;
                };
            install_call_liveness(&mut context, bb);
            let callee = instance.callee_body().unwrap();
            let (address, target) =
                context.inline_storage_address_for_test(&callee, args).unwrap_or_else(|| {
                    panic!("exact caller storage required: {path} bb{bb}: {body:#?}")
                });
            if inspected == 0 {
                context.with_inline_walk_frame(&callee, |context| {
                    assert!(!context.inline_walk_frames.is_empty());
                    assert!(
                        context.inline_storage_address_for_test(&callee, args).is_none(),
                        "frame-local numbers cannot acquire host storage authority"
                    );
                });
                context.with_inline_walk_write_mark(|context| {
                    assert!(context.inline_walk_frames.is_empty());
                    assert!(context.inline_walk_write_mark.is_some());
                    assert!(
                        context.inline_storage_address_for_test(&callee, args).is_none(),
                        "an outer walk scope cannot acquire host-only storage authority"
                    );
                });
                assert!(
                    context.inline_storage_address_for_test(&callee, args).is_some(),
                    "leaving inline scope restores the original proved host path"
                );
            }
            assert!(
                matches!(target.projections.as_slice(), [ProjectionElem::Field(index, _)] if *index == field)
            );
            let (object, actual_offset) =
                ChcCtx::try_extract_constant_addr(&address.into_expr()).unwrap();
            assert_eq!(actual_offset, offset, "real repr(C) layout offset");
            assert_eq!(context.heap_state.local_idx_for_obj_id(object), Some(target.local));
            let entry = owners.entry(target.local).or_insert_with(|| (object, BTreeSet::new()));
            assert_eq!(entry.0, object, "shared and mutable getters retain the same owner");
            entry.1.insert((field, offset));
            inspected += 1;
        }
        assert_eq!(inspected, 8, "both fields, both capabilities, both equal-valued owners");
        assert_eq!(owners.len(), 2);
        let objects: BTreeSet<_> = owners.values().map(|(object, _)| *object).collect();
        assert_eq!(objects.len(), 2, "equal values must not merge storage");
        for (_, fields) in owners.values() {
            assert_eq!(fields, &BTreeSet::from([(0, 0), (1, 8)]));
        }
    });
}

#[test]
fn native_inline_storage_address_refuses_uncustodied_and_effectful_producers() {
    with_storage_address_ctx(SOURCE, |ctx| {
        for (host, method) in [
            ("retargeted_carrier", "mutable_second"),
            ("exposed_carrier", "mutable_second"),
            ("effectful_getter", "effectful"),
            ("branching_getter", "branching"),
            ("numeric_pointer_value", "numeric"),
            ("expired_local_getter", "expired_local"),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, host).body().unwrap();
            retain_storage_body(&format!("producer_decline_{host}_native"), &body);
            let mut context = ChcCtx::new(ctx.tcx, &body, host, mem_config());
            context.declare_block_relations();
            let mut inspected = 0;
            for bb in 0..body.blocks.len() {
                let Some((instance, args)) = resolve_call(&body, bb) else { continue };
                if !instance.def.name().ends_with(method) {
                    continue;
                }
                install_call_liveness(&mut context, bb);
                assert!(
                    context
                        .inline_storage_address_for_test(&instance.callee_body().unwrap(), args)
                        .is_none(),
                    "unsupported producer cannot acquire storage authority: {host} bb{bb}"
                );
                inspected += 1;
            }
            assert_eq!(inspected, 1, "retain the exact negative getter site: {host}");
        }
        for (host, method, expected) in [
            ("retargeted_result", "mutable_second", 2),
            ("exposed_result", "mutable_second", 1),
            ("copied_exposed_result", "mutable_second", 1),
            ("shared_capability_upgrade", "shared_second", 1),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, host).body().unwrap();
            retain_storage_body(&format!("result_decline_{host}_native"), &body);
            let mut context = ChcCtx::new(ctx.tcx, &body, host, mem_config());
            context.declare_block_relations();
            let mut inspected = 0;
            for bb in 0..body.blocks.len() {
                let Some((instance, _)) = resolve_call(&body, bb) else { continue };
                if !instance.def.name().ends_with(method) {
                    continue;
                }
                let TerminatorKind::Call { destination, .. } = &body.blocks[bb].terminator.kind
                else {
                    unreachable!()
                };
                assert!(
                    !context.inline_storage_result_custody_for_test(destination.local),
                    "result aliases cannot retain authority after carrier exposure/retarget: {host} bb{bb}"
                );
                inspected += 1;
            }
            assert_eq!(inspected, expected, "retain result-custody negative sites: {host}");
        }
    });
}

#[test]
fn native_inline_storage_address_field_stores_keep_full_encoding() {
    with_storage_address_ctx(SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for name in [
                "store_second_preserves_first",
                "equal_owners_keep_distinct_storage",
                "store_second_bug",
                "copied_second_preserves_first",
            ] {
                let label = format!("{name}_storage_d{depth}");
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let original = instance.callee_body().unwrap();
                retain_storage_body(&format!("{label}_native"), &original);
                let (_, body) = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                })
                .transform_with_body_provider(
                    ctx.tcx,
                    original,
                    instance,
                    |callee| {
                        let path = callee.def.name();
                        if native_assertion_panic_boundary(ctx.tcx, callee)
                            || abstraction.abstracts_public_instance(ctx.tcx, callee)
                            || ["mutable_first", "shared_first", "mutable_second", "shared_second"]
                                .iter()
                                .any(|method| path.ends_with(method))
                        {
                            None
                        } else {
                            callee.callee_body()
                        }
                    },
                );
                retain_storage_body(&label, &body);
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                        .translate_with_diagnostics();
                retain_storage_artifact(
                    &label,
                    "smt2",
                    &crate::codegen_ay::emit_chc(&vc).to_string(),
                );
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(&label)
                    .unwrap_or_default();
                assert!(reasons.is_empty(), "{label}: {reasons:?}");
                assert_eq!(diagnostics.place_translation_drop.get(), 0, "{label}");
                assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{label}");
                assert!(vc.approximation_identity_complete, "{label}");
                let assertions = retain_exact_native_assertions(ctx.tcx, &body, &vc, name, &label);
                if depth == 0 && matches!(name, "store_second_preserves_first" | "store_second_bug")
                {
                    let mut semantic_vc = vc.clone();
                    let expected = if name.ends_with("bug") {
                        // SAT must reach this source-bound assertion, rather
                        // than an unrelated memory-safety property.
                        semantic_vc.query =
                            trust_mc_core::chc::ChcQuery::new().with_target(assertions[0].clone());
                        "sat"
                    } else {
                        "unsat"
                    };
                    let smt = crate::codegen_ay::emit_chc(&semantic_vc).to_string();
                    retain_storage_artifact(&format!("{label}_checked_query"), "smt2", &smt);
                    // The legacy helper name executes AY. Keep the existing
                    // 30-second overall budget; no external Z3 process.
                    assert_z3_result_with_timeout(&smt, expected, 30);
                }
            }
        }
    });
}

#[test]
fn native_inline_storage_address_keeps_dead_owner_store_obligation() {
    with_storage_address_ctx(SOURCE, |ctx| {
        use trust_mc_core::violation::PropertyKind;
        let label = "dangling_field_store_storage_native";
        let body = find_instance_by_suffix(ctx.tcx, "dangling_field_store").body().unwrap();
        retain_storage_body(label, &body);
        let stores: Vec<_> = body
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(bb, block)| {
                block.statements.iter().enumerate().filter_map(move |(index, statement)| {
                    matches!(&statement.kind, StatementKind::Assign(lhs, _)
                    if lhs.projection.as_slice() == [ProjectionElem::Deref])
                    .then_some((bb, index))
                })
            })
            .collect();
        assert_eq!(stores.len(), 1, "retain the actual dangling dereference store: {body:#?}");
        let (store_bb, store_index) = stores[0];

        // Obtain the owner from the real getter's typed storage plan while its
        // borrow is live, then inspect the original storage events at use.
        let getters: Vec<_> = (0..body.blocks.len())
            .filter_map(|bb| {
                let (instance, args) = resolve_call(&body, bb)?;
                instance.def.name().ends_with("mutable_second").then_some((bb, instance, args))
            })
            .collect();
        assert_eq!(getters.len(), 1, "{label}: retain the original getter: {body:#?}");
        let (getter_bb, getter, args) = &getters[0];
        let callee = getter.callee_body().expect("native getter body");
        retain_storage_body("dangling_field_store_getter_native", &callee);
        let mut witness = ChcCtx::new(ctx.tcx, &body, label, mem_config());
        witness.declare_block_relations();
        install_call_liveness(&mut witness, *getter_bb);
        let (address, target) = witness
            .inline_storage_address_for_test(&callee, args)
            .unwrap_or_else(|| panic!("{label}: exact original caller storage: {body:#?}"));
        let owner = target.local;
        assert_eq!(witness.stack_local_is_live(owner), Some(true), "{label}: live getter prefix");
        assert!(matches!(target.projections.as_slice(), [ProjectionElem::Field(1, _)]));
        let (_, offset) = ChcCtx::try_extract_constant_addr(&address.into_expr()).unwrap();
        assert_eq!(offset, 8, "{label}: original second-field address");
        assert_eq!(body.locals()[owner].ty.layout().unwrap().shape().size.bytes(), 16);
        let mut expiries = Vec::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            for (index, statement) in block.statements.iter().enumerate() {
                if matches!(statement.kind, StatementKind::StorageDead(local) if local == owner) {
                    expiries.push((bb, index));
                }
            }
        }
        install_statement_liveness(&mut witness, store_bb, store_index);
        retain_storage_artifact(
            &format!("{label}_liveness"),
            "log",
            &format!(
                "owner={owner}\ngetter_bb={getter_bb}\nstore=({store_bb},{store_index})\nactual_storage_dead={expiries:?}\nmust_dead={:?}\nmay_dead={:?}\nowner_live={:?}\n",
                witness.liveness.dead_locals,
                witness.liveness.maybe_dead_locals,
                witness.stack_local_is_live(owner),
            ),
        );
        assert_eq!(
            expiries.len(),
            1,
            "{label}: real source StorageDead is required, not inserted: {body:#?}"
        );
        assert!(
            witness.liveness.dead_locals.contains(&owner),
            "{label}: owner must be storage-dead at this actual store"
        );
        assert_eq!(
            witness.stack_local_is_live(owner),
            Some(false),
            "{label}: source lifetime evidence"
        );

        let (vc, _, diagnostics) =
            ChcCtx::new(ctx.tcx, &body, label, mem_config()).translate_with_diagnostics();
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(label)
            .unwrap_or_default();
        retain_storage_artifact(label, "smt2", &crate::codegen_ay::emit_chc(&vc).to_string());
        retain_storage_artifact(
            &format!("{label}_diagnostics"),
            "log",
            &format!(
                "reasons={reasons:#?}\nplace_translation_drop={}\nsound_havoc_drop={}\nheap_check_untranslatable={}\nidentity_complete={}\n",
                diagnostics.place_translation_drop.get(),
                diagnostics.sound_havoc_drop.get(),
                diagnostics.heap_check_untranslatable.get(),
                vc.approximation_identity_complete,
            ),
        );
        assert!(reasons.is_empty(), "{label}: {reasons:?}");
        assert_eq!(diagnostics.place_translation_drop.get(), 0, "{label}");
        assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{label}");
        assert_eq!(diagnostics.heap_check_untranslatable.get(), 0, "{label}");
        assert!(vc.approximation_identity_complete, "{label}");

        let store_relation = format!("{label}__bb{store_bb}");
        let properties: Vec<_> = vc
            .properties
            .iter()
            .filter(|property| {
                property.bb == store_bb
                    && property.kind == PropertyKind::MemorySafety
                    && property.discharged_at_encode.is_none()
                    && property.approximation_dependent == Some(false)
                    && vc.rules.iter().any(|rule| {
                        rule.head.name.as_str() == property.relation.as_str()
                            && rule
                                .body
                                .relation
                                .as_ref()
                                .is_some_and(|from| from.name.as_str() == store_relation)
                            // The error builder appends the negated check
                            // after the statement frame. AY's raw not(false)
                            // constructor is not necessarily folded yet.
                            && (rule.body.constraints.iter().last().is_some_and(|condition| {
                                matches!(condition.value(), ExprValue::Not(value)
                                    if matches!(value.value(), ExprValue::BoolConst(false)))
                            }) || rule.body.constraints.iter().all(|condition| {
                                matches!(condition.value(), ExprValue::BoolConst(true))
                            }))
                    })
            })
            .collect();
        assert!(
            !properties.is_empty(),
            "{label}: retain the actual store's unconditional lifetime failure; alignment/bounds guards cannot substitute"
        );
        for property in &properties {
            assert!(
                vc.rules.iter().any(|rule| rule.head.name.as_str() == "error"
                    && rule
                        .body
                        .relation
                        .as_ref()
                        .is_some_and(|from| from.name.as_str() == property.relation)
                    && rule.body.constraints.is_empty()),
                "{label}: every lifetime failure must still reach the original aggregate error"
            );
        }
        let lifetime = properties[0].relation.clone();
        // Pointer validity and the physical memory store can independently
        // check this same source lifetime. Either original failing property
        // suffices; their number is not part of the semantic contract.
        // Target this source-bound lifetime failure, not any of the store's
        // valid alignment/bounds checks. Its retained bridge makes reachability
        // sufficient for the original aggregate query too. Keep three total AY
        // queries in this module, each at the existing fixed30-second limit.
        let mut semantic_vc = vc.clone();
        semantic_vc.query = trust_mc_core::chc::ChcQuery::new().with_target(lifetime);
        let smt = crate::codegen_ay::emit_chc(&semantic_vc).to_string();
        retain_storage_artifact(&format!("{label}_checked_query"), "smt2", &smt);
        assert_z3_result_with_timeout(&smt, "sat", 30);
    });
}
