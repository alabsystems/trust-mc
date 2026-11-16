// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule C's backstop (design trust-mc-reds-final §4.3,
//! `heap/memory_cell_backstop.rs`): a constant-address read of a cell under a
//! key no store wrote it under is booked, with the cell, as an audited sound
//! havoc; a read under a key that was written is not.

#![allow(clippy::unwrap_used, clippy::panic)]

use std::sync::Arc;

use super::common::*;
use crate::codegen_ay::chc::heap::heap_state::ConstantCellLoad;
use crate::codegen_ay::chc::heap::memory_cell_backstop::cells_read_under_unwritten_key;

fn load(addr: u64, key: &str, array: &str) -> ConstantCellLoad {
    ConstantCellLoad { addr, type_key: Arc::from(key), array: Arc::from(array) }
}

#[test]
fn a_read_under_a_key_nothing_wrote_there_is_reported_once() {
    let stores = vec![(0x1_0000_0000, Arc::from("box_i128")), (0x2_0000_0000, Arc::from("u8"))];
    let loads = vec![
        load(0x1_0000_0000, "nonnull_i128", "mem_nonnull_i128"),
        load(0x1_0000_0000, "nonnull_i128", "mem_nonnull_i128"),
        load(0x1_0000_0000, "box_i128", "mem_box_i128"),
        load(0x2_0000_0000, "u8", "mem_u8"),
        // No store at this address under any key: not judged (residual 5).
        load(0x3_0000_0000, "u16", "mem_u16"),
    ];
    assert_eq!(
        cells_read_under_unwritten_key(&stores, &loads),
        vec![(0x1_0000_0000, Arc::from("mem_nonnull_i128"))]
    );
}

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_cell_backstop(a: u32) -> u32 { a }
"#;

#[derive(Clone, Copy)]
enum ReadUse {
    Array,
    Scalarized,
    Discarded,
    OtherCell,
    ThreadedOnly,
    StoredSameCell,
    StoredOtherCell,
    StoredUnknownCell,
    WalkLimit,
}

/// `(sound havocs, fail-closed, accounted identities, recorded identities,
/// identity complete)` after the post-pass and identity finalization.
fn backstop_after(
    stored_key: &str,
    loaded_key: &str,
    read_use: ReadUse,
) -> (usize, usize, usize, Vec<String>, bool) {
    let (stored_key, loaded_key) = (stored_key.to_owned(), loaded_key.to_owned());
    let mut out = None;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cell_backstop");
        let body = instance.body().expect("body");
        let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_cell_backstop", ChcConfig::default());
        let addr = Expr::bitvec_const(7i128, 32).concat(Expr::bitvec_const(8i128, 32));
        let value = Expr::bitvec_const(5i128, 32);
        let _ = chc.store_to_type_array(
            addr.clone(),
            value,
            &stored_key,
            ay_bindings::Sort::bitvec(32),
            false,
        );
        let loaded = chc
            .load_from_type_array(addr, &loaded_key, ay_bindings::Sort::bitvec(32), None)
            .expect("the select is built");
        let array = chc.heap_state.constant_cell_loads.last().unwrap().array.to_string();
        // Supply the declaration a final emitted VC needs for this array.
        chc.vc.add_var(trust_mc_core::chc::VarDecl::new(
            array.clone(),
            ay_bindings::Sort::array(ay_bindings::Sort::bitvec(64), ay_bindings::Sort::bitvec(32)),
        ));
        let mut args = vec![];
        let guard = match read_use {
            ReadUse::Array | ReadUse::WalkLimit => {
                if matches!(read_use, ReadUse::WalkLimit) {
                    // Find the exact read first, then exceed the walk limit:
                    // a partial walk must not authorize its identity.
                    args.resize(100_001, Expr::bool_const(true));
                }
                loaded.eq(Expr::bitvec_const(7u64, 32))
            }
            ReadUse::StoredSameCell | ReadUse::StoredOtherCell | ReadUse::StoredUnknownCell => {
                let array_expr = Expr::var(
                    &array,
                    ay_bindings::Sort::array(
                        ay_bindings::Sort::bitvec(64),
                        ay_bindings::Sort::bitvec(32),
                    ),
                );
                let index = match read_use {
                    ReadUse::StoredSameCell => Expr::bitvec_const(0x7_0000_0008u64, 64),
                    ReadUse::StoredOtherCell => Expr::bitvec_const(0x7_0000_0009u64, 64),
                    _ => Expr::var("unknown_store_index", ay_bindings::Sort::bitvec(64)),
                };
                let selected = array_expr
                    .store(index, Expr::bitvec_const(5u64, 32))
                    .select(Expr::bitvec_const(0x7_0000_0008u64, 64));
                assert!(
                    matches!(selected.value(), ExprValue::Select { .. }),
                    "control must reach the Select(Store(..)) path"
                );
                selected.eq(Expr::bitvec_const(7u64, 32))
            }
            ReadUse::Scalarized => {
                let cell = crate::codegen_ay::chc::scalarize_arrays::scalarized_cell_name(
                    &array,
                    &0x7_0000_0008u64,
                    64,
                );
                chc.vc.add_var(trust_mc_core::chc::VarDecl::new(
                    cell.clone(),
                    ay_bindings::Sort::bitvec(32),
                ));
                Expr::var(cell, ay_bindings::Sort::bitvec(32)).eq(Expr::bitvec_const(7u64, 32))
            }
            ReadUse::OtherCell => Expr::var(
                &array,
                ay_bindings::Sort::array(
                    ay_bindings::Sort::bitvec(64),
                    ay_bindings::Sort::bitvec(32),
                ),
            )
            .select(Expr::bitvec_const(0x7_0000_0009u64, 64))
            .eq(Expr::bitvec_const(7u64, 32)),
            ReadUse::ThreadedOnly => {
                args.push(Expr::var(
                    &array,
                    ay_bindings::Sort::array(
                        ay_bindings::Sort::bitvec(64),
                        ay_bindings::Sort::bitvec(32),
                    ),
                ));
                Expr::bool_const(true)
            }
            ReadUse::Discarded => Expr::bool_const(true),
        };
        chc.vc.rules.push(trust_mc_core::chc::Rule::init(
            guard,
            trust_mc_core::chc::RelationApp::new("observe", args),
        ));
        let before = (
            chc.diagnostics.sound_havoc_drop.get(),
            chc.diagnostics.place_translation_drop.get(),
            chc.vc.accounted_approximations,
        );
        chc.book_cells_read_under_unwritten_key();
        chc.vc.finalize_approximation_identity(chc.diagnostics.sound_havoc_drop.get());
        out = Some((
            chc.diagnostics.sound_havoc_drop.get() - before.0,
            chc.diagnostics.place_translation_drop.get() - before.1,
            chc.vc.accounted_approximations - before.2,
            chc.vc.approximated_vars.clone(),
            chc.vc.approximation_identity_complete,
        ));
    });
    out.expect("the probe compiled")
}

#[test]
fn a_key_split_books_the_cell_as_an_identified_sound_havoc() {
    for read_use in [ReadUse::Array, ReadUse::Scalarized, ReadUse::StoredOtherCell] {
        let (havoc, fail_closed, accounted, vars, complete) =
            backstop_after("box_u32", "nonnull_u32", read_use);
        assert_eq!((havoc, fail_closed, accounted, complete), (1, 0, 1, true));
        assert!(
            vars.iter().any(|var| var.contains("nonnull_u32")),
            "the live missing cell is the identity: {vars:?}"
        );
    }
}

#[test]
fn a_read_under_the_written_key_books_nothing() {
    let (havoc, fail_closed, accounted, _, complete) =
        backstop_after("box_u32", "box_u32", ReadUse::Array);
    assert_eq!((havoc, fail_closed, accounted, complete), (0, 0, 0, true));
}

/// Neither a declared array nor an unrelated read or a threaded relation
/// argument proves the missing cell's identity survived constant folding.
#[test]
fn a_folded_away_key_split_remains_unaccounted() {
    for read_use in [
        ReadUse::Discarded,
        ReadUse::OtherCell,
        ReadUse::ThreadedOnly,
        ReadUse::StoredSameCell,
        ReadUse::StoredUnknownCell,
        ReadUse::WalkLimit,
    ] {
        let (havoc, fail_closed, accounted, vars, complete) =
            backstop_after("u8", "bool", read_use);
        assert_eq!((havoc, fail_closed, accounted, complete), (1, 0, 0, false));
        assert!(vars.is_empty(), "a lost read has no referenceable identity: {vars:?}");
    }
}
