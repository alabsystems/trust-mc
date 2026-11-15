// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The float-binop table select is an IDENTIFIED sound approximation.
//!
//! `float_binop_table_overapprox` used to be recorded without a freed-var
//! identity, which leaves `approximation_identity_complete` false for every
//! harness with a symbolic float op, so the driver could never certify a
//! counterexample there — not even the fast-math operand-finiteness failures
//! that read only the operands (kani/Intrinsics/FastMath/*_overflow_*, ledger
//! row 72). With the table named, the operand checks come out independent of
//! it while the table stays the freed variable.

use super::common::*;

const FAST_ADD_SOURCE: &str = r#"
    #![allow(dead_code, internal_features)]
    #![feature(core_intrinsics)]

    pub fn float_table_probe(x: f32, y: f32) -> bool {
        let z = unsafe { std::intrinsics::fadd_fast(x, y) };
        z > 1.0
    }
"#;

#[test]
fn float_table_select_records_the_table_as_its_identity() {
    with_test_ay_ctx_for_source(FAST_ADD_SOURCE, |ctx| {
        let fn_name = "float_table_probe";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_with_instance(ctx.tcx, &body, instance, fn_name, ChcConfig::default());

        assert!(
            vc_rules_contain_var(&vc, trust_mc_core::chc::FLOAT_BINOP_TABLE_F32),
            "the symbolic fadd_fast must go through the congruent table"
        );
        assert_eq!(
            vc.approximated_vars,
            vec![trust_mc_core::chc::FLOAT_BINOP_TABLE_F32.to_string()],
            "the table select must name the table as the freed variable"
        );
        assert!(vc.accounted_approximations >= 1);
        assert!(
            vc.approximation_identity_complete,
            "every approximation in this body is the identified table select"
        );
        let independent =
            vc.properties.iter().filter(|p| p.approximation_dependent == Some(false)).count();
        assert!(
            independent >= 2,
            "both operand-finiteness checks read only the operands: {:?}",
            vc.properties
                .iter()
                .map(|p| (&p.relation, p.approximation_dependent))
                .collect::<Vec<_>>()
        );
    });
}
