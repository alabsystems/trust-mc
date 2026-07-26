// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::call::inline_body::{
    extract_inline_assume_guard, strip_inline_assume_pruned, translate_inline_body,
};
use ay_bindings::Sort;
use num_bigint::BigInt;

const NESTED_ASSUME_USED_AFTER_CALL_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    #[inline(never)]
    pub fn inner_assume_zero(x: u32) -> u32 {
        kani::assume(x == 0);
        x
    }

    pub fn outer_uses_assumed_return(x: u32) -> bool {
        let y = inner_assume_zero(x);
        y == 0
    }
"#;

const INLINE_ENUM_ANY_MODIFIES_ASSUME_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani_intrinsics {
        #[kanitool::fn_marker = "AnyModifiesIntrinsic"]
        pub fn any_modifies<T>() -> T {
            panic!("model-only marker function")
        }
    }

    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    #[derive(Copy, Clone)]
    pub enum Foo {
        A,
        B,
    }

    pub fn inline_enum_any_modifies_assume() -> Foo {
        let value: Foo = kani_intrinsics::any_modifies();
        let ok = match value {
            Foo::A => true,
            Foo::B => false,
        };
        kani::assume(ok);
        value
    }
"#;

#[test]
fn test_inline_any_modifies_enum_assume_uses_destination_sort() {
    with_test_ay_ctx_for_source(INLINE_ENUM_ANY_MODIFIES_ASSUME_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "inline_enum_any_modifies_assume");
        let body = instance.body().expect("function body");
        assert!(
            body.blocks.iter().any(|bb| matches!(bb.terminator.kind, TerminatorKind::Call { .. })),
            "probe must contain an inline AnyModifies call"
        );

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "inline_enum_any_modifies_assume", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let inline_result =
            translate_inline_body(&mut chc_ctx, &body, &[], 0, &HashMap::new(), Some(instance), 0)
                .expect("inline body should translate");

        assert_eq!(
            inline_result.value.sort().bitvec_width(),
            Some(32),
            "unit enum AnyModifies result should use the enum destination sort, got {:?}",
            inline_result.value
        );
        let guard = extract_inline_assume_guard(&inline_result.value)
            .expect("postcondition assume should constrain the fresh enum result");
        assert!(
            constraint_tree_contains(&guard, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.contains("__kani_any_inline"))
            }),
            "assume guard should mention the fresh AnyModifies value, got {guard:?}"
        );
        let stripped = strip_inline_assume_pruned(&inline_result.value)
            .expect("assume-pruned fallback should strip to success value");
        assert_eq!(
            stripped.sort().bitvec_width(),
            Some(32),
            "stripped enum return should keep destination width, got {stripped:?}"
        );
        assert!(
            matches!(
                stripped.value(),
                ExprValue::BitVecConst { value, width } if *value == BigInt::from(0u8) && *width == 32
            ),
            "assume refinement should apply the postcondition to the inline return, got {stripped:?}"
        );
    });
}

#[test]
fn test_nested_inline_assume_lifted_before_later_use() {
    with_test_ay_ctx_for_source(NESTED_ASSUME_USED_AFTER_CALL_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "outer_uses_assumed_return");
        let body = instance.body().expect("function body");
        assert!(
            body.blocks.iter().any(|bb| matches!(bb.terminator.kind, TerminatorKind::Call { .. })),
            "probe must contain a nested call"
        );

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "outer_uses_assumed_return", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let params = vec![Expr::var("x", Sort::bitvec(32))];
        chc_ctx.mark_inline_field_reads(&body, &params, 0);
        let inline_result = translate_inline_body(
            &mut chc_ctx,
            &body,
            &params,
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .expect("inline body should translate");

        assert!(
            extract_inline_assume_guard(&inline_result.value).is_some(),
            "nested assume guard should survive after the nested return is used, got {:?}",
            inline_result.value
        );
        let stripped = strip_inline_assume_pruned(&inline_result.value)
            .expect("assume-pruned fallback should strip to success value");
        assert!(
            !constraint_tree_contains(&stripped, &|expr| {
                matches!(expr.value(), ExprValue::Var { name } if name.contains("__assume_pruned_inline"))
            }),
            "stripped success value should not retain assume-pruned fallback, got {stripped:?}"
        );
    });
}
