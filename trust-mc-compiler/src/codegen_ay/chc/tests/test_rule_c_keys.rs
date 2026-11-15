// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule C (design trust-mc-reds-final §4.3): memory cells are keyed by
//! representation, and a type's key and its SMT sort move together
//! (`ChcCtx::representation_peel`).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]
    #[repr(transparent)]
    pub struct W(u32);
    pub fn probe_keys(
        boxed: Box<u8>,
        raw: *const u8,
        nonnull: std::ptr::NonNull<u8>,
        manual: std::mem::ManuallyDrop<Box<u8>>,
        newtype: W,
        word: u32,
    ) {
    }
    pub fn probe_dyn_keys(boxed_dyn: Box<dyn Fn() -> u8>, boxed_byte: Box<u8>, raw: *const u8) {}
"#;

#[test]
fn test_box_nonnull_and_raw_pointer_share_one_key() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_keys");
        let key = |i: usize| ChcCtx::type_key_for_ty(sig.inputs()[i]).into_owned();
        let raw = key(1);
        assert_eq!(key(0), raw, "Box<u8> (zero-sized Global) is a *const u8");
        assert_eq!(key(2), raw, "NonNull<u8> is its pattern-typed *const u8");
        assert_eq!(key(3), raw, "ManuallyDrop<Box<u8>> is a *const u8");
    });
}

#[test]
fn test_a_datatype_newtype_keeps_its_own_key() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_keys");
        let (newtype, word) = (sig.inputs()[4], sig.inputs()[5]);
        assert_ne!(
            ChcCtx::translate_ty(newtype),
            ChcCtx::translate_ty(word),
            "the guard's premise: W is a datatype sort, u32 a bitvector"
        );
        assert!(ChcCtx::representation_peel(newtype).is_none(), "no peel across sorts");
        assert_ne!(ChcCtx::type_key_for_ty(newtype), ChcCtx::type_key_for_ty(word));
    });
}

/// Every peel the predicate admits keeps the sort: key and sort move together.
#[test]
fn test_every_admitted_peel_keeps_the_sort() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let inputs: Vec<_> = ["probe_keys", "probe_dyn_keys"]
            .into_iter()
            .flat_map(|f| fn_sig_by_suffix(ctx.tcx, f).inputs().to_vec())
            .collect();
        for ty in &inputs {
            let mut cur = *ty;
            while let Some(peeled) = ChcCtx::representation_peel(cur) {
                assert_eq!(ChcCtx::translate_ty(cur), ChcCtx::translate_ty(peeled), "{cur:?}");
                cur = peeled;
            }
        }
    });
}

/// `dyn Trait` is keyed as `u8` (#3608), so `Box<dyn Trait>` keeps sharing
/// `Box<u8>`'s cell once Rule C keys that as `*const u8`.
#[test]
fn test_box_dyn_shares_the_erased_box_key() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_dyn_keys");
        let key = |i: usize| ChcCtx::type_key_for_ty(sig.inputs()[i]).into_owned();
        assert_eq!(key(0), key(1), "Box<dyn Fn() -> u8> and Box<u8> are one cell key");
        assert_eq!(key(1), key(2), "Box<u8> is a *const u8");
    });
}
