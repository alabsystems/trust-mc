// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real adapter MIR reads these exact fields; opaque handles cannot carry them.

use super::common::*;

const SOURCE: &str = r#"
pub fn take(x: std::iter::Take<std::slice::Iter<'_, u8>>) { let _ = x; }
pub fn reverse(x: std::iter::Rev<std::slice::Iter<'_, u8>>) { let _ = x; }
pub fn copied(x: std::iter::Copied<std::slice::Iter<'_, u8>>) { let _ = x; }
pub fn cloned(x: std::iter::Cloned<std::slice::Iter<'_, u8>>) { let _ = x; }
pub fn mapped(x: std::iter::Map<std::slice::Iter<'_, u8>, fn(&u8) -> u8>) { let _ = x; }
mod user {
    pub struct Map { pub payload: u32, pub seen: bool }
}
pub fn user_map(x: user::Map) { let _ = x; }
"#;

#[test]
fn adapter_bodies_keep_inner_iterator_count_and_callable_fields() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (function, expected_fields) in [
            ("take", vec!["fld_iter", "fld_n"]),
            ("reverse", vec!["fld_iter"]),
            ("copied", vec!["fld_it"]),
            ("cloned", vec!["fld_it"]),
            ("mapped", vec!["fld_iter", "fld_f"]),
            ("user_map", vec!["fld_payload", "fld_seen"]),
        ] {
            let ty = fn_sig_by_suffix(ctx.tcx, function).inputs()[0];
            let sort = ChcCtx::translate_ty(ty).expect("structural adapter sort");
            let datatype = sort.datatype_sort().expect("adapter must retain fields");
            assert_eq!(datatype.constructors.len(), 1);
            let fields: Vec<_> =
                datatype.constructors[0].fields.iter().map(|f| f.name.as_str()).collect();
            assert_eq!(fields, expected_fields, "{function}: {sort}");
        }
    });
}
