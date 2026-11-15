// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::kani_middle::resolve::{ResolveError, resolve_fn};

#[test]
fn defaults_select_the_same_impl_as_explicit_arguments_and_missing_args_refuse() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub trait Defaulted<Rhs=Self> { fn tag() -> u8; }
        impl Defaulted<u8> for u8 { fn tag() -> u8 { 1 } }
        impl Defaulted<u16> for u8 { fn tag() -> u8 { 2 } }
        pub trait Cascade<A=u16, B=A> { fn cascade() -> u8; }
        impl Cascade<u16, u16> for u8 { fn cascade() -> u8 { 3 } }
        pub trait Required<Rhs> { fn required(); }
        impl Required<u16> for u8 { fn required() {} }
        pub trait Consty<const N:usize=1> { fn constant(); }
        impl Consty<1> for u8 { fn constant() {} }
        pub trait MethodGeneric<Rhs=Self> { fn generic<T>(); }
        impl MethodGeneric<u8> for u8 { fn generic<T>() {} }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let module = rustc_hir::def_id::CRATE_DEF_ID;
        let resolve = |path| resolve_fn(ctx.tcx, module, path);
        let defaulted = resolve("<u8 as Defaulted>::tag").expect("Self default");
        let explicit = resolve("<u8 as Defaulted<u8>>::tag").expect("explicit Self");
        let different = resolve("<u8 as Defaulted<u16>>::tag").expect("explicit other RHS");
        assert_eq!(defaulted, explicit);
        assert_ne!(defaulted, different);
        assert_eq!(
            resolve("<u8 as Cascade>::cascade").expect("dependent defaults"),
            resolve("<u8 as Cascade<u16, u16>>::cascade").expect("explicit defaults"),
        );
        assert!(resolve("u8::eq").is_ok(), "primitive PartialEq defaults Rhs to Self");
        assert!(resolve("<u8 as Required>::required").is_err());
        assert!(resolve("<u8 as Defaulted<u8, u16>>::tag").is_err());
        assert!(resolve("<u8 as Consty<2>>::constant").is_err());
        assert!(resolve("<u8 as MethodGeneric<u8, u16>>::generic").is_err());
    });
}

#[test]
fn primitive_function_candidates_ignore_associated_constants_and_types() {
    const SOURCE: &str = r#"
        #![allow(dead_code, non_upper_case_globals, non_camel_case_types)]
        use core::cmp::PartialEq;
        pub trait ConstantNoise { const eq: bool; }
        pub trait TypeNoise { type eq; }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let module = rustc_hir::def_id::CRATE_DEF_ID;
        let resolve = |path| resolve_fn(ctx.tcx, module, path);
        assert_eq!(
            resolve("u8::eq").expect("same-name non-functions are not method candidates"),
            resolve("<u8 as PartialEq<u8>>::eq").expect("actual primitive equality impl"),
        );
        assert!(resolve("<u8 as ConstantNoise>::eq").is_err());
        assert!(resolve("<u8 as TypeNoise>::eq").is_err());
    });
}

#[test]
fn qualified_selectors_require_a_trait_prefix_and_its_own_method() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub mod fake {
            pub fn target() {}
            pub mod nested { pub fn target() {} }
        }
        pub struct Inherent;
        impl Inherent { pub fn target() {} }
        pub trait Actual { fn target(); }
        impl Actual for u8 { fn target() {} }
        use Actual as Alias;
        pub trait Outer { type Inner; }
        impl Outer for u8 { type Inner = Inherent; }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let module = rustc_hir::def_id::CRATE_DEF_ID;
        let resolve = |path| resolve_fn(ctx.tcx, module, path);
        for path in [
            "<u8 as fake>::target",
            "<u8 as fake>::nested::target",
            "<u8 as Inherent>::target",
            "<u8 as fake::target>::target",
        ] {
            assert!(
                matches!(
                    resolve(path),
                    Err(ResolveError::UnexpectedType { expected: "trait", .. })
                ),
                "non-trait qualified prefix must refuse: {path}",
            );
        }
        assert!(
            resolve("<u8 as Outer>::Inner::target").is_err(),
            "a nested item cannot become the named trait's method",
        );
        assert_eq!(
            resolve("<u8 as Actual>::target").expect("actual trait-owned method"),
            resolve("<u8 as Alias>::target").expect("a trait import alias retains ownership"),
        );
        assert!(resolve("fake::target").is_ok(), "ordinary free-function selection remains valid");
        assert!(resolve("Inherent::target").is_ok(), "ordinary inherent selection remains valid");
    });
}

#[test]
fn concrete_selectors_refuse_shared_bodies_but_whole_definitions_remain_available() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub trait Shared<Rhs=Self> { fn tag() -> u8 { 1 } }
        impl Shared for u8 {}
        impl Shared<u16> for u8 {}
        impl Shared for u16 {}
        impl Shared for i8 { fn tag() -> u8 { 2 } }
        pub trait Other { fn tag() -> u8; }
        impl Other for u8 { fn tag() -> u8 { 5 } }
        pub trait Single { fn single() -> u8 { 3 } }
        impl Single for bool {}
        pub trait Blanket { fn broad() -> u8; }
        impl<T> Blanket for T { fn broad() -> u8 { 4 } }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let module = rustc_hir::def_id::CRATE_DEF_ID;
        let resolve = |path| resolve_fn(ctx.tcx, module, path);
        for path in [
            "<u8 as Shared>::tag",
            "<u8 as Shared<u8>>::tag",
            "<u8 as Shared<u16>>::tag",
            "<u16 as Shared>::tag",
            "<bool as Single>::single",
            "<u8 as Blanket>::broad",
        ] {
            assert!(
                matches!(resolve(path), Err(ResolveError::InvalidPath { .. })),
                "a DefId-only map cannot preserve concrete selection of {path}",
            );
        }
        assert!(
            resolve("u8::tag").is_err(),
            "primitive syntax must not bypass shared-body refusal"
        );
        assert!(resolve("u8::broad").is_err(), "blanket impls also share their generic body");
        assert!(resolve("<u8 as Other>::tag").is_ok(), "a distinct trait impl remains selectable");
        let shared = resolve("Shared::tag").expect("explicit whole-definition default body");
        assert!(resolve("Single::single").is_ok(), "whole-definition non-generic trait default");
        assert_ne!(
            resolve("<i8 as Shared>::tag").expect("distinct non-generic impl override"),
            shared,
        );
    });
}
