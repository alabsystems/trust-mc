// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Range element signedness is read from the static type, through references.
//!
//! `Iterator::next(&mut self)` passes the `&mut Range<T>` reference local to the
//! RangeSpecNext stub. Reading only a bare `Range<T>` declared type made every
//! such advance take the arithmetic signedness fallback.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_variables)]
pub fn probe_ranges(
    a: &mut core::ops::Range<i32>,
    b: core::ops::Range<u8>,
    c: &core::ops::Range<usize>,
    d: &&mut core::ops::Range<i64>,
    e: u32,
) {}
"#;

#[test]
fn range_signedness_peels_references() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ranges");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ranges", ChcConfig::default());
        // Locals 1..=5 are the arguments in order.
        assert_eq!(chc_ctx.range_local_element_signedness(Some(1)), Some(true), "&mut Range<i32>");
        assert_eq!(chc_ctx.range_local_element_signedness(Some(2)), Some(false), "Range<u8>");
        assert_eq!(chc_ctx.range_local_element_signedness(Some(3)), Some(false), "&Range<usize>");
        assert_eq!(
            chc_ctx.range_local_element_signedness(Some(4)),
            Some(true),
            "&&mut Range<i64>"
        );
        assert_eq!(chc_ctx.range_local_element_signedness(Some(5)), None, "u32 is not a range");
        assert_eq!(chc_ctx.range_local_element_signedness(None), None);
    });
}
