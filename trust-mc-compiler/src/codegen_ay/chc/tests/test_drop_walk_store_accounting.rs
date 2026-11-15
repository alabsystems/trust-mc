// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A walked `Drop::drop` body that writes through `self` and then checks is
//! accounted as an approximation (`walk_drop_body`, `call/inline_body.rs`).
//!
//! The walker answers `self.a` from the snapshot taken when the walk began, so
//! after `self.a = self.a.wrapping_add(self.c)` the body's `unchecked_add`
//! check tests the ENTRY `a`. Before the fix the drop consumers emitted that
//! check with nothing recorded: a correct program whose entry value overflows
//! got a counterexample certified Genuine
//! (`tools/soundness-duals/walker_drop_body_state_dual.rs`,
//! `safe_single_drop_entry_overflows`), and a buggy one whose written value
//! overflows was proved. The check must still be emitted; the record makes the
//! harness fail closed instead.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

/// Spelled out rather than imported, so this file compiles, and fails, against
/// an encoder that never records it.
const REASON: &str = "drop_body_check_after_walk_store";
const UNCHECKED_ADD: &str = "attempt to compute `unchecked_add` which would overflow";

const DROP_WALK_PROBE: &str = r#"
    #![allow(dead_code)]

    #[inline(never)]
    fn sink<T>(_value: T) {}

    pub trait Writes {
        fn id(&self) -> u8;
    }
    pub struct SW {
        a: u8,
        b: u8,
        c: u8,
    }
    impl Drop for SW {
        fn drop(&mut self) {
            self.a = self.a.wrapping_add(self.c);
            sink(unsafe { self.a.unchecked_add(self.b) });
        }
    }
    impl Writes for SW {
        fn id(&self) -> u8 {
            3
        }
    }

    pub trait Reads {
        fn id(&self) -> u8;
    }
    pub struct SR {
        a: u8,
        b: u8,
    }
    impl Drop for SR {
        fn drop(&mut self) {
            sink(unsafe { self.a.unchecked_add(self.b) });
        }
    }
    impl Reads for SR {
        fn id(&self) -> u8 {
            4
        }
    }

    pub trait ChecksFirst {
        fn id(&self) -> u8;
    }
    pub struct SC {
        a: u8,
        b: u8,
    }
    impl Drop for SC {
        fn drop(&mut self) {
            sink(unsafe { self.a.unchecked_add(self.b) });
            self.a = 0;
        }
    }
    impl ChecksFirst for SC {
        fn id(&self) -> u8 {
            5
        }
    }

    pub fn probe_drop_writes_then_checks(x: u8) {
        let o: Box<dyn Writes> = Box::new(SW { a: x, b: 1, c: 1 });
        sink(o.id());
    }

    pub fn probe_drop_checks_without_write(x: u8) {
        let o: Box<dyn Reads> = Box::new(SR { a: x, b: 1 });
        sink(o.id());
    }

    pub fn probe_drop_checks_then_writes(x: u8) {
        let o: Box<dyn ChecksFirst> = Box::new(SC { a: x, b: 1 });
        sink(o.id());
    }
"#;

/// Encode `fn_name` from the probe crate and return the messages of its
/// properties and its translation-drop site reasons.
fn encode_probe(fn_name: &str) -> (Vec<String>, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let ran = AtomicBool::new(false);
    let mut messages = Vec::new();
    with_test_ay_ctx_for_source(DROP_WALK_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        messages = vc.properties.iter().filter_map(|p| p.message.clone()).collect();
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and {fn_name} was encoded");
    let sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (messages, sites)
}

/// The walked drop body writes `self.a` before its check: the check is still
/// emitted, and the approximation is recorded, not blessed.
#[test]
fn test_drop_body_check_after_store_is_emitted_and_fails_closed() {
    let fn_name = "probe_drop_writes_then_checks";
    let (messages, sites) = encode_probe(fn_name);
    assert!(
        messages.iter().any(|m| m == UNCHECKED_ADD),
        "{fn_name}: the drop body's unchecked_add check must still be emitted, got {messages:?}"
    );
    assert!(
        sites.get(REASON).copied().unwrap_or(0) >= 1,
        "{fn_name}: a drop body that writes self and then checks must record {REASON}, \
         got sites {sites:?}"
    );
    assert_eq!(
        fallback_soundness(REASON),
        FallbackSoundness::FailClose,
        "{REASON} must not be blessed: its checks may read entry values"
    );
}

/// A drop body that only reads `self` keeps its check certifiable: nothing is
/// recorded, so the accounting costs no precision where no store happened.
#[test]
fn test_drop_body_check_without_store_records_nothing() {
    let fn_name = "probe_drop_checks_without_write";
    let (messages, sites) = encode_probe(fn_name);
    assert!(
        messages.iter().any(|m| m == UNCHECKED_ADD),
        "{fn_name}: the drop body's unchecked_add check must be emitted, got {messages:?}"
    );
    assert!(
        !sites.contains_key(REASON),
        "{fn_name}: a drop body with no store must not record {REASON}, got sites {sites:?}"
    );
}

/// The check comes BEFORE the body's store, so it reads what the body saw:
/// only checks recorded after a store are accounted.
#[test]
fn test_drop_body_check_before_store_records_nothing() {
    let fn_name = "probe_drop_checks_then_writes";
    let (messages, sites) = encode_probe(fn_name);
    assert!(
        messages.iter().any(|m| m == UNCHECKED_ADD),
        "{fn_name}: the drop body's unchecked_add check must be emitted, got {messages:?}"
    );
    assert!(
        !sites.contains_key(REASON),
        "{fn_name}: a check recorded before the store must not record {REASON}, got sites {sites:?}"
    );
}
