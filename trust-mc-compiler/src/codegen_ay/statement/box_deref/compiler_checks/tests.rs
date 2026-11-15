// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::transform::body::MutableBody;
use rustc_public::mir::{Mutability, Place};

const SOURCE: &str = r#"
pub fn read(value: Box<u32>) -> u32 { *value }
pub fn observed(value: Box<u32>) -> usize { core::ptr::addr_of!(*value) as usize }
"#;

#[test]
fn compiler_pointer_checks_authenticate_actual_assertions_and_refuse_user_numeric_return() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "read").body().unwrap();
        assert!(!compiler_pointer_check_casts(&body).is_empty(), "actual compiler guard casts");
        let observed = find_instance_by_suffix(ctx.tcx, "observed").body().unwrap();
        assert!(
            compiler_pointer_check_casts(&observed).is_empty(),
            "a user address observation is not a guard"
        );
    });
}

#[test]
fn compiler_pointer_checks_refuse_transitive_alias_escape_and_rebinding() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "read").body().unwrap();
        let casts = compiler_pointer_check_casts(&body);
        let original = *casts.keys().next().unwrap();
        let decl = body.locals()[original].clone();
        let mut mutable = MutableBody::from(body);
        let alias = mutable.new_local(decl.ty, decl.span, Mutability::Mut);
        let user = mutable.new_local(decl.ty, decl.span, Mutability::Mut);
        let mut body = mutable.into();
        let mut definition = None;
        let rename = |operand: &mut Operand| {
            if let Operand::Copy(p) | Operand::Move(p) = operand
                && p.local == original
                && p.projection.is_empty()
            {
                p.local = alias;
            }
        };
        for (bb, block) in body.blocks.iter_mut().enumerate() {
            for (si, statement) in block.statements.iter_mut().enumerate() {
                if let StatementKind::Assign(place, rhs) = &mut statement.kind {
                    if place.local == original && place.projection.is_empty() {
                        definition = Some((bb, si));
                        continue;
                    }
                    match rhs {
                        Rvalue::BinaryOp(_, a, b) => {
                            rename(a);
                            rename(b);
                        }
                        Rvalue::UnaryOp(_, a) | Rvalue::Use(a, ..) | Rvalue::Cast(_, a, _) => {
                            rename(a)
                        }
                        _ => {}
                    }
                }
            }
            if let TerminatorKind::Assert { cond, msg, .. } = &mut block.terminator.kind {
                rename(cond);
                if let AssertMessage::MisalignedPointerDereference { found, .. } = msg {
                    rename(found);
                }
            }
        }
        let (bb, si) = definition.unwrap();
        body.blocks[bb].statements.insert(
            si + 1,
            crate::rustc_compat::mir_statement(
                StatementKind::Assign(
                    Place::from(alias),
                    rvalue_use!(Rvalue::Use(Operand::Copy(Place::from(original)))),
                ),
                decl.span,
            ),
        );
        assert!(
            compiler_pointer_check_casts(&body).contains_key(&original),
            "a confined alias keeps its check-only role"
        );
        body.blocks[bb].statements.insert(
            si + 2,
            crate::rustc_compat::mir_statement(
                StatementKind::Assign(
                    Place::from(user),
                    rvalue_use!(Rvalue::Use(Operand::Copy(Place::from(alias)))),
                ),
                decl.span,
            ),
        );
        assert!(
            compiler_pointer_check_casts(&body).is_empty(),
            "a downstream alias use is an escape"
        );
        body.blocks[bb].statements.remove(si + 2);
        body.blocks[bb].statements.insert(
            si + 2,
            crate::rustc_compat::mir_statement(
                StatementKind::Assign(
                    Place::from(original),
                    rvalue_use!(Rvalue::Use(Operand::Copy(Place::from(alias)))),
                ),
                decl.span,
            ),
        );
        assert!(
            compiler_pointer_check_casts(&body).is_empty(),
            "rebound locals have no unique check definition"
        );
    });
}
