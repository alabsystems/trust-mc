// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::Sort;

#[test]
fn event_time_chains_refuse_unknown_alias_merge_havoc_and_exhaustion() {
    with_test_ay_ctx_for_source("pub fn probe() {}", |context| {
        let body = find_instance_by_suffix(context.tcx, "probe").body().unwrap();
        let mut ctx = ChcCtx::new(context.tcx, &body, "probe", ChcConfig::default());
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        let before = Expr::var("actual_entry_chain", sort.clone());
        ctx.heap_state.store_chains.clear();
        ctx.heap_state.drained_store_chain_seeds.clear();
        ctx.native_drop_memory = Some(NativeDropMemory {
            allocation: 33,
            budget: Cell::new(16_384),
            entry_chains: HashMap::from([(
                std::ptr::from_ref(before.value()) as usize,
                before.clone(),
            )]),
            exact: Cell::new(true),
            store_authorized: Cell::new(false),
        });
        let known = Expr::bitvec_const(33u32, 32).concat(Expr::bitvec_const(4u32, 32));
        let after = before.clone().store(known, Expr::bitvec_const(7u32, 32));
        for (name, chain, expected) in [
            ("ordered_known_cell", after.clone(), true),
            (
                "unknown_alias",
                before
                    .clone()
                    .store(Expr::var("address", Sort::bitvec(64)), Expr::bitvec_const(0u32, 32)),
                false,
            ),
            (
                "branch_order",
                Expr::ite(Expr::var("branch", Sort::bool()), after, before.clone()),
                false,
            ),
            ("havoc", Expr::var("fresh_unregistered_array", sort), false),
        ] {
            ctx.heap_state.store_chains.insert("u32".into(), ("actual_output".into(), chain));
            assert_eq!(ctx.native_drop_store_order_is_known(), expected, "{name}");
        }
        ctx.heap_state.store_chains.insert("u32".into(), ("actual_output".into(), before));
        ctx.native_drop_memory.as_ref().unwrap().budget.set(0);
        assert!(!ctx.native_drop_store_order_is_known());
        assert!(!ctx.native_drop_memory.as_ref().unwrap().exact.get());
        assert!(ctx.diagnostics.place_translation_drop.get() > 0);
    });
}

#[test]
fn observations_cannot_contain_mutable_final_outputs_or_binders() {
    assert!(has_output_or_binder(&Expr::var("observed__out", Sort::bitvec(32))));
    let bound = Expr::var("index", Sort::bitvec(32));
    assert!(has_output_or_binder(&Expr::forall(
        vec![("index".to_owned(), Sort::bitvec(32))],
        bound.clone().eq(Expr::bitvec_const(0u32, 32))
    )));
    assert!(has_output_or_binder(&Expr::exists(
        vec![("index".to_owned(), Sort::bitvec(32))],
        bound.eq(Expr::bitvec_const(0u32, 32))
    )));
    let before = Expr::var("entry", Sort::array(Sort::bitvec(64), Sort::bitvec(32)));
    let cell = Expr::bitvec_const(33u32, 32).concat(Expr::bitvec_const(0u32, 32));
    let frozen = before.store(cell.clone(), Expr::bitvec_const(11u32, 32)).select(cell);
    assert!(!has_output_or_binder(&frozen));
}
