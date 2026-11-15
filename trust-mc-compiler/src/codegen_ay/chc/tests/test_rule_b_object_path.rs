// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule B (design trust-mc-reds-final §4.2, C5a): a pointer is (object,
//! offset, pointee type), and the part of a value it names is found by the one
//! object-path rule (`decl::static_path`, rustc's layout).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::expr::codegen_expr_deref_field_offset::object_path_projections;
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]
    use std::mem::ManuallyDrop;
    pub struct R2 { r0: u8, r1: u8 }
    pub struct Q2 { a: R2, b: u8 }
    pub struct PM { m: ManuallyDrop<Q2>, c: u8 }
    pub fn probe_paths(pm: PM, q: Q2) {}
"#;

#[test]
fn test_object_path_through_manually_drop() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_paths");
        let (pm, q2) = (sig.inputs()[0], sig.inputs()[1]);
        let m_offset = LayoutOf::new(pm).field_offset(0).unwrap() as u64;
        let path = object_path_projections(pm, m_offset, q2).expect("Q2 is a unique part of PM");
        // Read core's actual field types. Native core now uses value: T;
        // older Trust seals inserted one MaybeDangling<T> level instead.
        // Both paths must still land exactly on Q2 at the same byte offset.
        let field0 = |ty: rustc_public::ty::Ty| {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
                panic!("a native wrapper must be an ADT");
            };
            crate::codegen_ay::shared::mono_ty::field_ty(&def.variants()[0].fields()[0], &args)
                .unwrap()
        };
        let manually_drop = field0(pm);
        assert_eq!(LayoutOf::new(manually_drop).field_offset(0), Some(0));
        let payload = field0(manually_drop);
        let expected = if payload == q2 {
            vec![0, 0]
        } else {
            assert_eq!(LayoutOf::new(payload).field_offset(0), Some(0));
            assert_eq!(field0(payload), q2, "the former carrier contains Q2");
            vec![0, 0, 0]
        };
        assert_eq!(path.iter().map(|p| p.field_idx).collect::<Vec<_>>(), expected);
        assert_eq!(path.last().and_then(|p| p.field_ty), Some(q2));
        // The whole value is the empty path.
        assert!(object_path_projections(pm, 0, pm).unwrap().is_empty());
    });
}

#[test]
fn test_object_path_refuses_a_window_that_is_no_part() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_paths");
        let (pm, q2) = (sig.inputs()[0], sig.inputs()[1]);
        let size = LayoutOf::new(pm).size_of().unwrap() as u64;
        let m_offset = LayoutOf::new(pm).field_offset(0).unwrap() as u64;
        // A Q2-sized window past the end, and one shifted by a byte into PM.m.
        assert!(object_path_projections(pm, size, q2).is_none());
        assert!(object_path_projections(pm, m_offset + 1, q2).is_none());
    });
}
