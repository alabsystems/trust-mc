// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused regression for HashMap `get().copied()` flattening into Option fields.
//! Part of #3057: DT-free encoding — the flattened discriminant slot `_fld0`
//! receives a Bool from `present.select(key)`, no DatatypeTester needed.

#![allow(clippy::unwrap_used)]

use super::common::*;

const HASHMAP_INSERT_GET_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_insert_get_flatten() -> Option<u32> {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let key1 = 1u32;
        let key2 = 2u32;
        let value1 = 100u32;
        let value2 = 200u32;
        map.insert(key1, value1);
        map.insert(key2, value2);
        map.get(&key1).copied()
    }
"#;

fn is_field_var(expr: &Expr, field_suffix: &str) -> bool {
    matches!(expr.value(), ExprValue::Var { name } if name.contains(field_suffix))
}

#[test]
fn test_hashmap_get_flattened_option_uses_scalar_field_constraints() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();

    with_test_ay_ctx_for_source(HASHMAP_INSERT_GET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_get_flatten");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_hashmap_insert_get_flatten", ChcConfig::default());

        // Part of #3057: DT-free encoding — _fld0 is the is_some Bool from
        // present.select(key). No DatatypeTester involved.
        let mut has_fld0_bool_constraint = false;
        let mut has_fld0_datatype_rhs = false;
        for rule in &vc.rules {
            for constraint in &rule.body.constraints {
                let ExprValue::Eq(lhs, rhs) = constraint.value() else {
                    continue;
                };
                if is_field_var(lhs, "_fld0") {
                    has_fld0_bool_constraint |= rhs.sort().is_bool();
                    has_fld0_datatype_rhs |= rhs.sort().is_datatype();
                }
                if is_field_var(rhs, "_fld0") {
                    has_fld0_bool_constraint |= lhs.sort().is_bool();
                    has_fld0_datatype_rhs |= lhs.sort().is_datatype();
                }
            }
        }

        assert!(
            has_fld0_bool_constraint,
            "HashMap::get flattened Option _fld0 should be constrained with a Bool (#3057 DT-free)"
        );
        assert!(
            !has_fld0_datatype_rhs,
            "HashMap::get flattened Option must not assign datatype expression directly to _fld0"
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
    let constant_drop_count = crate::codegen_ay::take_constant_translation_drop_count();
    let field_projection_drop_count = crate::codegen_ay::take_unsupported_field_projection_count();
    let fn_name = "probe_hashmap_insert_get_flatten";
    let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
    assert_eq!(
        drop_count, 0,
        "{fn_name} should not record translation drops, drops={translation_drops:?}, sound_fallback_reasons={drop_fallback_reasons:?}, sites={translation_sites:?}, place_count={place_drop_count}, constant_count={constant_drop_count}, field_projection_count={field_projection_drop_count}"
    );
}
