// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! ADT sort names are injective across definitions (design
//! trust-mc-reds-final §7.2, T3-2), and the naming module's recognizers name
//! the definitions rustc actually prints (T3-1).
//!
//! `names::adt_sort_name` used the trimmed name as its base, so
//! `std::collections::HashMap<i32, i32, RandomState, Global>` and the
//! `hashbrown::HashMap` it wraps, at the same arguments, were the one name
//! `HashMap_i32_i32_std_hash_RandomState_std_alloc_Global` with two
//! definitions, and ay refused the program (`conflicting datatype definitions
//! under one name`): 17 engine tests failed on it.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::names;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

/// Red on main: the two `HashMap`s shared one sort name.
#[test]
fn std_and_hashbrown_hashmap_have_distinct_sort_names() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_hashmap(m: std::collections::HashMap<i32, i32>) {}
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_hashmap");
        let TyKind::RigidTy(RigidTy::Adt(std_def, std_args)) = sig.inputs()[0].kind() else {
            panic!("std HashMap is an ADT");
        };
        let variants = std_def.variants();
        let base_field = variants[0].fields().into_iter().next().expect("HashMap has a field");
        let base_ty = crate::codegen_ay::shared::mono_ty::field_ty(&base_field, &std_args)
            .expect("the base field instantiates");
        let TyKind::RigidTy(RigidTy::Adt(inner_def, inner_args)) = base_ty.kind() else {
            panic!("HashMap's base is an ADT, got {base_ty:?}");
        };
        assert_ne!(std_def, inner_def, "the probe must reach a second definition");
        assert_eq!(
            std_def.trimmed_name(),
            inner_def.trimmed_name(),
            "the probe must reach a definition of the same last segment"
        );
        let std_name = ChcCtx::adt_sort_name(std_def, &std_args);
        let inner_name = ChcCtx::adt_sort_name(inner_def, &inner_args);
        assert_ne!(
            std_name, inner_name,
            "two definitions named `HashMap` must not share a sort name"
        );
        assert!(names::adt_sort_is(&std_name, &[&std_def.name()]));
        assert!(names::adt_sort_is(&inner_name, &[&inner_def.name()]));
        assert!(!names::adt_sort_is(&std_name, &[&inner_def.name()]));
    });
}

/// The `known_adt` path lists name the definitions rustc prints, so each
/// recognizer accepts the sort of the real type. A recognizer whose paths
/// drifted from rustc's spelling would read every such sort as foreign.
#[test]
fn known_adt_paths_recognize_the_real_types() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(allocator_api)]
        pub fn probe_known(
            o: Option<u32>,
            r: Result<u8, u16>,
            c: std::iter::Copied<std::slice::Iter<'static, u32>>,
            k: std::iter::Cloned<std::slice::Iter<'static, u32>>,
            t: std::any::TypeId,
            s: std::str::Chars<'static>,
            a: std::alloc::AllocError,
        ) {}
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_known");
        let name_of = |i: usize| {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = sig.inputs()[i].kind() else {
                panic!("input {i} is an ADT");
            };
            ChcCtx::adt_sort_name(def, &args)
        };
        let expectations: [(usize, &[&str], &str); 7] = [
            (0, names::known_adt::OPTION, "Option"),
            (1, names::known_adt::RESULT, "Result"),
            (2, names::known_adt::COPIED, "Copied"),
            (3, names::known_adt::CLONED, "Cloned"),
            (4, names::known_adt::TYPE_ID, "TypeId"),
            (5, names::known_adt::CHARS, "Chars"),
            (6, names::known_adt::ALLOC_ERROR, "AllocError"),
        ];
        for (i, paths, what) in expectations {
            let name = name_of(i);
            assert!(
                names::adt_sort_is(&name, paths),
                "{what}: {name} is not recognized by {paths:?}"
            );
        }
        assert!(names::is_option_sort_name(&name_of(0)));
        assert!(names::is_copied_or_cloned_sort_name(&name_of(2)));
        assert!(names::is_copied_or_cloned_sort_name(&name_of(3)));
        assert!(names::is_type_id_sort_name(&name_of(4)));
        assert!(!names::is_option_sort_name(&name_of(1)));
    });
}

/// `adt_sort_is` reads a whole path segment: a longer last segment that starts
/// with the path's is another definition.
#[test]
fn adt_sort_is_matches_the_whole_definition_path() {
    let option = names::known_adt::OPTION;
    assert!(names::adt_sort_is("std_option_Option", option));
    assert!(names::adt_sort_is("std_option_Option_u32", option));
    assert!(names::adt_sort_is("core_option_Option_bool", option));
    assert!(!names::adt_sort_is("std_option_OptionExt_u32", option));
    assert!(!names::adt_sort_is("Option_u32", option));
    assert!(!names::adt_sort_is("testcrate_3_std_option_Option", option));
}
