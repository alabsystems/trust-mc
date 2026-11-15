// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

#[test]
fn closure_rustcall_producers_are_unique_unescaped_and_bounded() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn plain(value: &u64) -> (&u64,) { (value,) }
        pub fn joined<'a>(flag: bool, left: &'a u64, right: &'a u64) -> (&'a u64,) {
            let mut pair=(left,); if flag {pair=(right,);} pair
        }
        pub fn escaped<'a>(left: &'a u64, right: &'a u64) -> (&'a u64,) {
            let mut pair=(left,); let alias=&mut pair; alias.0=right; pair
        }
    "#,
        |ctx| {
            for (name, expected) in [("plain", true), ("joined", false), ("escaped", false)] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                let returned = Operand::Copy(Place { local: 0, projection: vec![] });
                let validated = chc.validated_closure_arg_fields(&returned);
                assert_eq!(validated.is_some(), expected, "{name}: {body:#?}");
                let fields = chc.extract_closure_call_arg_operands(&returned);
                assert_eq!(fields.len(), 1);
                if !expected {
                    assert!(
                        matches!(&fields[0],Operand::Copy(place) if place.local==0 && matches!(place.projection.as_slice(),[ProjectionElem::Field(0,_)])),
                        "{name}: stale producer reused: {fields:?}"
                    );
                }
                assert!(single_producer(&body, 0, &mut 0).is_err());
                if name == "plain" {
                    let mut first = body.blocks[0].clone();
                    first.terminator.kind = TerminatorKind::Goto { target: 2 };
                    let mut exit = body.blocks[0].clone();
                    exit.statements.clear();
                    exit.terminator.kind = TerminatorKind::Return;
                    let mut back = exit.clone();
                    back.terminator.kind = TerminatorKind::Goto { target: 1 };
                    let mut reordered = Body::new(
                        vec![first, exit, back],
                        body.locals().to_vec(),
                        body.arg_locals().len(),
                        body.var_debug_info.clone(),
                        None,
                        body.span,
                    );
                    assert!(single_producer(&reordered, 0, &mut 16_384).is_ok());
                    reordered.blocks[2].terminator.kind = TerminatorKind::Goto { target: 0 };
                    assert!(single_producer(&reordered, 0, &mut 16_384).is_err());
                }
            }
        },
    );
}
