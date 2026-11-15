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

/// `(sound havocs, fail-closed, accounted identities, recorded identities)`
/// after a store under `stored_key` and a load under `loaded_key` at one
/// constant address, and the post-pass.
fn backstop_after(stored_key: &str, loaded_key: &str) -> (usize, usize, usize, Vec<String>) {
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
        let _ = chc
            .load_from_type_array(addr, &loaded_key, ay_bindings::Sort::bitvec(32), None)
            .expect("the select is built");
        let before = (
            chc.diagnostics.sound_havoc_drop.get(),
            chc.diagnostics.place_translation_drop.get(),
            chc.vc.accounted_approximations,
        );
        chc.book_cells_read_under_unwritten_key();
        out = Some((
            chc.diagnostics.sound_havoc_drop.get() - before.0,
            chc.diagnostics.place_translation_drop.get() - before.1,
            chc.vc.accounted_approximations - before.2,
            chc.vc.approximated_vars.clone(),
        ));
    });
    out.expect("the probe compiled")
}

/// A key split books one identified sound havoc. No scalarization ran, so the
/// cell is not a variable and the array read stands for it.
#[test]
fn a_key_split_books_the_cell_as_an_identified_sound_havoc() {
    let (havoc, fail_closed, accounted, vars) = backstop_after("box_u32", "nonnull_u32");
    assert_eq!((havoc, fail_closed, accounted), (1, 0, 1));
    assert!(
        vars.iter().any(|var| var.contains("nonnull_u32")),
        "the array read under the unwritten key is the identity: {vars:?}"
    );
}

#[test]
fn a_read_under_the_written_key_books_nothing() {
    let (havoc, fail_closed, accounted, _) = backstop_after("box_u32", "box_u32");
    assert_eq!((havoc, fail_closed, accounted), (0, 0, 0));
}
