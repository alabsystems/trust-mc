// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_has_special_codegen_handler_slice_contains() {
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::slice::<impl [char]>::contains"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("<[char]>::contains"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::str::<impl str>::contains"));
}

#[test]
fn test_has_special_codegen_handler_range_contains() {
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::ops::RangeInclusive::<u8>::contains::<u8>"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<std::ops::RangeInclusive<u8> as std::ops::RangeBounds<u8>>::contains"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::ops::range::Range::<usize>::contains"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_crate::RangeBag::contains"));
}

#[test]
fn test_inline_pass_preserves_same_allocation_for_semantic_dispatch() {
    const LIBRARY: &str = r#"
        pub mod mem {
            #[inline(never)]
            pub fn same_allocation<T: ?Sized>(a: *const T, b: *const T) -> bool {
                a as *const () == b as *const ()
            }
            #[inline(never)]
            pub fn same_allocation_internal<T: ?Sized>(a: *const T, b: *const T) -> bool {
                same_allocation(a, b)
            }
        }
    "#;
    const SOURCE: &str = r#"
        extern crate kani as renamed_kani;
        pub use renamed_kani::mem as public_memory;
        extern crate boundary_support;
        mod nested {
            pub mod kani {
                pub mod mem {
                    #[inline(never)]
                    pub fn same_allocation(a: *const u8, b: *const u8) -> bool { a == b }
                }
            }
        }
        pub fn probe_public(a: *const u8, b: *const u8) -> bool {
            renamed_kani::mem::same_allocation(a, b)
        }
        pub fn probe_alias(a: *const u8, b: *const u8) -> bool {
            renamed_kani::mem::same_allocation(a, b)
        }
        pub fn probe_reexport(a: *const u8, b: *const u8) -> bool {
            public_memory::same_allocation(a, b)
        }
        pub fn probe_internal(a: *const u8, b: *const u8) -> bool {
            renamed_kani::mem::same_allocation_internal(a, b)
        }
        pub fn probe_fat(a: *const [u8], b: *const [u8]) -> bool {
            renamed_kani::mem::same_allocation(a, b)
        }
        pub fn probe_local_lookalike(a: *const u8, b: *const u8) -> bool {
            nested::kani::mem::same_allocation(a, b)
        }
        pub fn probe_external_lookalike(a: *const u8, b: *const u8) -> bool {
            boundary_support::kani::mem::same_allocation(a, b)
        }
    "#;
    let temp = TempDir::new().expect("create crate fixture");
    for (name, source) in [
        ("kani", LIBRARY.to_owned()),
        ("boundary_support", format!("pub mod kani {{ {LIBRARY} }}")),
    ] {
        let path = temp.path().join(format!("{name}.rs"));
        fs::write(&path, source).expect("write dependency");
        let args = vec![
            "rustc".to_owned(),
            path.to_string_lossy().into_owned(),
            "--crate-type=rlib".to_owned(),
            format!("--crate-name={name}"),
            "--out-dir".to_owned(),
            temp.path().to_string_lossy().into_owned(),
            "--edition=2024".to_owned(),
            "-Zalways-encode-mir".to_owned(),
        ];
        let result = run_with_tcx!(&args, |_tcx| std::ops::ControlFlow::<(), ()>::Continue(()));
        assert!(result.is_ok(), "dependency compilation failed: {result:?}");
        assert!(temp.path().join(format!("lib{name}.rlib")).is_file());
    }
    let path = temp.path().join("caller.rs");
    fs::write(&path, SOURCE).expect("write caller");
    let mut args = vec![
        "rustc".to_owned(),
        path.to_string_lossy().into_owned(),
        "--crate-type=lib".to_owned(),
        "--crate-name=inline_boundary_caller".to_owned(),
        "--out-dir".to_owned(),
        temp.path().to_string_lossy().into_owned(),
        "--edition=2024".to_owned(),
        "-Copt-level=0".to_owned(),
        "-Zinline-mir=no".to_owned(),
    ];
    for name in ["kani", "boundary_support"] {
        args.push("--extern".to_owned());
        args.push(format!("{name}={}", temp.path().join(format!("lib{name}.rlib")).display()));
    }
    let result = run_with_tcx!(&args, |tcx| {
        for name in ["probe_public", "probe_alias", "probe_reexport", "probe_internal", "probe_fat"]
        {
            let instance = find_instance_by_suffix(tcx, name);
            let body = instance.body().expect("probe body");
            let original_calls = collect_call_defs(&body);
            let identities: Vec<_> = original_calls
                .iter()
                .map(|(path, def, _)| {
                    (
                        path.clone(),
                        def.krate(),
                        handler_boundaries::is_kani_mem_stub_boundary(tcx, *def),
                    )
                })
                .collect();
            assert!(
                identities.iter().any(|(_, _, boundary)| *boundary),
                "{name} has no recognized input call: {identities:?}"
            );
            let inlined = apply_codegen_inline_pass(tcx, instance, body);
            let calls = collect_call_defs(&inlined);
            assert!(
                calls
                    .iter()
                    .any(|(_, def, _)| handler_boundaries::is_kani_mem_stub_boundary(tcx, *def)),
                "{name} lost its lifetime-aware handler: {calls:?}"
            );
        }
        for name in ["probe_local_lookalike", "probe_external_lookalike"] {
            let instance = find_instance_by_suffix(tcx, name);
            let body = instance.body().expect("lookalike probe body");
            assert!(
                collect_call_defs(&body)
                    .iter()
                    .all(|(_, def, _)| !handler_boundaries::is_kani_mem_stub_boundary(tcx, *def)),
                "{name} was mistaken for the Kani API"
            );
            let inlined = apply_codegen_inline_pass(tcx, instance, body);
            let calls = collect_call_names(&inlined);
            assert!(
                !calls.iter().any(|path| path.contains("kani::mem::same_allocation")),
                "{name} must inline its own body: {calls:?}"
            );
        }
        std::ops::ControlFlow::<(), ()>::Continue(())
    });
    assert!(result.is_ok(), "caller compilation failed: {result:?}");
}
