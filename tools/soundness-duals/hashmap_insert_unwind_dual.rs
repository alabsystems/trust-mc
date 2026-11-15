// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- Kani's unwinding assertion on the
//! loops of `HashMap::insert`, a call both lanes model, under a declared
//! unwind bound (fix/chc-walker-fail-closed, walker fail-closed repair round
//! 5, review finding 8, the corpus unit `bounded-arbitrary/hash/hash.rs`).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-10-01 to
//! 2026-10-02):
//!   hm1_four_inserts_u2_bug -> VERIFICATION:- FAILED  ('unwinding assertion loop 0')
//!   hm2_one_insert_u5_safe  -> VERIFICATION:- SUCCESSFUL
//!
//! MECHANISM UNDER TEST. Repair round 4 made a modelled call whose callee
//! may loop state Kani's unwinding assertion (`codegen_call_model_unwind.rs`,
//! BMC `bmc_model_call_unwinding_check`). Main's CHC lane proved
//! `hm1_four_inserts_u2_bug`, where the fourth insert's resize loop runs
//! three passes under `unwind(2)` and Kani fails. hashbrown's loops are
//! bounded by the table's bucket count and its tombstones (the probe loop
//! visits groups until one holds an EMPTY byte, the resize loop scans every
//! group), which follow the map's history, not its length, and neither lane
//! tracks them, so the check has no trip bound and `hm2` (the shape of
//! `hash.rs`), which Kani proves, is the measured cost on both lanes.
//!
//! Lane scope: BMC and CHC.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s hashmap_insert_unwind_dual.rs

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, DefaultHasher};

type M = HashMap<u8, bool, BuildHasherDefault<DefaultHasher>>;

#[kani::proof]
#[kani::unwind(2)]
fn hm1_four_inserts_u2_bug() {
    let mut m: M = HashMap::default();
    m.insert(1, true);
    m.insert(2, true);
    m.insert(3, true);
    m.insert(4, true);
    assert!(m.len() == 4);
}

#[kani::proof]
#[kani::unwind(5)]
fn hm2_one_insert_u5_safe() {
    let mut m: M = HashMap::default();
    if kani::any() {
        m.insert(kani::any(), kani::any());
    }
    assert!(m.len() <= 1);
}
