// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused CHC pipeline tests for `kani_str_{chars,bytes}_nth` backing recovery.

#![allow(clippy::unwrap_used)]

use super::common::*;

fn reset_string_nth_diagnostics() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

fn assert_no_string_nth_reason(reason: &str) {
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let count: usize =
        translation_sites.values().map(|reasons| reasons.get(reason).copied().unwrap_or(0)).sum();
    assert_eq!(
        count, 0,
        "no function in this source should record {reason}, sites={translation_sites:?}"
    );
}

fn assert_zero_chc_fallbacks(fn_name: &str) {
    let fallback_counts = crate::codegen_ay::chc::get_chc_fallback_counts();
    let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        fallback_count, 0,
        "{fn_name} should stay on the precise CHC path, fallback map={fallback_counts:?}"
    );
}

#[test]
fn test_str_chars_nth_borrowed_literal_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_str_chars_nth_borrowed() -> Option<char> {
            let s = "foo";
            s.chars().nth(1)
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_chars_nth_borrowed");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_str_chars_nth_borrowed", ChcConfig::default());
        assert_vc_structure(&vc, "probe_str_chars_nth_borrowed", body.blocks.len());
        assert_no_string_nth_reason("str_chars_nth_no_backing");
    });
}

#[test]
fn test_str_chars_nth_to_string_receiver_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::ToString;

        pub fn probe_str_chars_nth_owned() -> Option<char> {
            let s = "foo";
            let owned = s.to_string();
            owned.chars().nth(1)
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_chars_nth_owned");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_str_chars_nth_owned", ChcConfig::default());
        assert_vc_structure(&vc, "probe_str_chars_nth_owned", body.blocks.len());
        assert_no_string_nth_reason("str_chars_nth_no_backing");
    });
}

#[test]
fn test_str_chars_nth_proof_body_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kani)]
        extern crate alloc;
        use alloc::string::ToString;

        fn test1() {
            let s = "foo";
            let owned = s.to_string();
            assert!(s.chars().nth(1) == Some('o'));
            assert!(owned.chars().nth(1) == Some('o'));
            assert!(owned.len() == 3);
        }

        #[kani::proof]
        fn main() {
            test1();
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "test1");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "test1", ChcConfig::default());
        assert_vc_structure(&vc, "test1", body.blocks.len());
        assert_zero_chc_fallbacks("test1");
        assert_no_string_nth_reason("str_chars_nth_no_backing");
    });
}

#[test]
fn test_str_chars_nth_after_string_get_mut_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;

        pub fn probe_str_chars_nth_after_get_mut() -> Option<char> {
            let mut owned = String::from("foo");
            let s = owned.get_mut(..).unwrap();
            s.chars().nth(1)
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_chars_nth_after_get_mut");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_str_chars_nth_after_get_mut", ChcConfig::default());
        assert_vc_structure(&vc, "probe_str_chars_nth_after_get_mut", body.blocks.len());
        assert_no_string_nth_reason("str_chars_nth_no_backing");
    });
}

#[test]
fn test_str_chars_nth_after_custom_dst_field_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::string::String;
        use core::mem::size_of_val;

        struct MyStr {
            header_0: u8,
            header_1: u8,
            data: str,
        }

        impl MyStr {
            fn new(original: &mut String) -> &mut Self {
                let buf = original.get_mut(..).unwrap();
                assert!(size_of_val(buf) > 2);
                let unsized_len = buf.len() - 2;
                let ptr = std::ptr::slice_from_raw_parts_mut(buf.as_mut_ptr(), unsized_len);
                unsafe { &mut *(ptr as *mut Self) }
            }
        }

        pub fn probe_str_chars_nth_after_custom_dst_field() -> Option<char> {
            let mut buf = String::from("123456");
            let my_str = MyStr::new(&mut buf);
            my_str.data.chars().nth(0)
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_str_chars_nth_after_custom_dst_field");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_str_chars_nth_after_custom_dst_field",
            ChcConfig::default(),
        );
        assert_vc_structure(&vc, "probe_str_chars_nth_after_custom_dst_field", body.blocks.len());
        assert_no_string_nth_reason("str_chars_nth_no_backing");
    });
}

#[test]
fn test_str_bytes_nth_from_utf8_vec_avoids_no_backing_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        extern crate alloc;
        use alloc::vec;
        use core::str;

        pub fn probe_str_bytes_nth_from_utf8_vec() -> Option<u8> {
            let bytes = vec![240u8, 159u8, 146u8, 150u8];
            match str::from_utf8(&bytes) {
                Ok(s) => s.bytes().nth(0),
                Err(_) => None,
            }
        }
    "#;

    reset_string_nth_diagnostics();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_str_bytes_nth_from_utf8_vec");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_str_bytes_nth_from_utf8_vec", ChcConfig::default());
        assert_vc_structure(&vc, "probe_str_bytes_nth_from_utf8_vec", body.blocks.len());
        assert_no_string_nth_reason("str_bytes_nth_no_backing");
    });
}
