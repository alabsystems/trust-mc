// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

const INLINE_OPTION_BOOL_AGGREGATE_PROBE: &str = r#"
    #![allow(dead_code)]

    struct Wrapper;

    impl Wrapper {
        fn wrap(flag: bool) -> Option<bool> {
            Some(flag)
        }
    }

    pub fn probe_inline_option_bool_aggregate(flag: bool) {
        let wrapped = Wrapper::wrap(flag);
        assert!(wrapped == Some(flag));
    }
"#;

const INLINE_VEC_POP_BOOL_UNWRAP_PROBE: &str = r#"
    #![allow(dead_code)]

    extern crate alloc;

    use alloc::vec::Vec;

    pub fn probe_inline_vec_pop_bool_unwrap(flag: bool) {
        let mut values: Vec<bool> = Vec::new();
        values.push(flag);
        let popped = values.pop().unwrap();
        assert!(popped == flag);
    }
"#;

const INLINE_STRUCT_VEC_POP_BOOL_UNWRAP_PROBE: &str = r#"
    #![allow(dead_code)]

    extern crate alloc;

    use alloc::vec::Vec;

    struct Wrapper {
        values: Vec<bool>,
    }

    pub fn probe_inline_struct_vec_pop_bool_unwrap(flag: bool) {
        let mut wrapper = Wrapper { values: Vec::new() };
        wrapper.values.push(flag);
        let popped = wrapper.values.pop().unwrap();
        assert!(popped == flag);
    }
"#;

const INLINE_OPTION_BOOL_UNWRAP_OR_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_inline_option_bool_unwrap_or(flag: bool, choose_some: bool) {
        let previous = if choose_some { Some(flag) } else { None };
        let restored = previous.unwrap_or(false);
        assert!(restored == if choose_some { flag } else { false });
    }
"#;

#[test]
fn test_inline_option_bool_aggregate_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        INLINE_OPTION_BOOL_AGGREGATE_PROBE,
        "probe_inline_option_bool_aggregate",
    );
}

#[test]
fn test_inline_vec_pop_bool_unwrap_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        INLINE_VEC_POP_BOOL_UNWRAP_PROBE,
        "probe_inline_vec_pop_bool_unwrap",
    );
}

#[test]
fn test_inline_struct_vec_pop_bool_unwrap_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        INLINE_STRUCT_VEC_POP_BOOL_UNWRAP_PROBE,
        "probe_inline_struct_vec_pop_bool_unwrap",
    );
}

#[test]
fn test_inline_option_bool_unwrap_or_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        INLINE_OPTION_BOOL_UNWRAP_OR_PROBE,
        "probe_inline_option_bool_unwrap_or",
    );
}
