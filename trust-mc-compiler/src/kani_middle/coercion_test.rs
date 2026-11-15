// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unsized coercions through the smart pointers and wrappers Kani harnesses use.
//!
//! Trust core stores `NonNull<T>`'s pointer as `pattern_type!(*const T is !null)`, so on the
//! Trust toolchain every coercion through `Box`, `Rc`, `Arc` or `NonNull` walks through a
//! pattern type; the frozen nightly core stores a plain `*const T`. These tests compile real
//! sources against the toolchain's own std and check both the coercion base and the walk.

#![allow(clippy::unwrap_used)]

use super::coercion::{
    CoerceUnsizedIterator, PATTERN_TYPE_BASE_FIELD, extract_unsize_casting,
    pointer_refinement_bases,
};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{CastKind, PointerCoercion, Rvalue, StatementKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, Ty as TyStable, TyKind};
use rustc_public::{CompilerError, CrateDef, run_with_tcx};
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;

const SMART_POINTER_COERCIONS: &str = r#"
#![feature(coerce_unsized, unsize)]
#![allow(dead_code)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;

pub trait Shape { fn area(&self) -> u32; }
pub struct Square(pub u32);
impl Shape for Square { fn area(&self) -> u32 { self.0 * self.0 } }

/// A user smart pointer over `NonNull`, coercing through its own `CoerceUnsized` impl.
pub struct MyNonNullPtr<T: ?Sized> { tag: (), ptr: NonNull<T> }
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyNonNullPtr<U>> for MyNonNullPtr<T> {}

/// A user smart pointer over a raw pointer.
pub struct MyRawPtr<T: ?Sized>(*const T);
impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyRawPtr<U>> for MyRawPtr<T> {}

pub fn coerce_box(b: Box<Square>) -> Box<dyn Shape> { b }
pub fn coerce_rc(r: Rc<Square>) -> Rc<dyn Shape> { r }
pub fn coerce_arc(a: Arc<Square>) -> Arc<dyn Shape> { a }
pub fn coerce_nonnull_slice(p: NonNull<[u8; 4]>) -> NonNull<[u8]> { p }
pub fn coerce_mut_dyn(s: &mut Square) -> &mut dyn Shape { s }
pub fn coerce_custom_nonnull(p: MyNonNullPtr<Square>) -> MyNonNullPtr<dyn Shape> { p }
pub fn coerce_custom_raw(p: MyRawPtr<[u8; 4]>) -> MyRawPtr<[u8]> { p }
"#;

const RANGE_PATTERN_TYPES: &str = r#"
#![feature(pattern_types, pattern_type_macro)]
#![allow(dead_code, incomplete_features)]
use std::pat::pattern_type;

pub fn signature(
    _: pattern_type!(u32 is 1..),
    _: pattern_type!(u32 is 2..),
    _: *const u8,
    _: *const [u8],
) {}
"#;

#[cfg(trust_toolchain)]
const NOT_NULL_PATTERN_TYPES: &str = r#"
#![feature(pattern_types, pattern_type_macro)]
#![allow(dead_code, incomplete_features)]
use std::pat::pattern_type;

pub fn signature(
    _: pattern_type!(*const [u8; 4] is !null),
    _: pattern_type!(*const [u8] is !null),
    _: pattern_type!(u32 is 1..),
    _: *const [u8; 4],
) {}
"#;

fn with_test_tcx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let temp_dir = TempDir::new().expect("create temp dir");
    let src_path: PathBuf = temp_dir.path().join("lib.rs");
    fs::write(&src_path, source).expect("write test source");

    let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
    let crate_name = format!("coercion_test_crate_{unique_id}");
    let out_dir = temp_dir.path().join("out");
    fs::create_dir_all(&out_dir).expect("create output dir");

    let args = vec![
        "rustc".to_string(),
        src_path.to_string_lossy().into_owned(),
        "--crate-type=lib".to_string(),
        format!("--crate-name={crate_name}"),
        "--out-dir".to_string(),
        out_dir.to_string_lossy().into_owned(),
        "--edition=2024".to_string(),
        "-C".to_string(),
        "opt-level=0".to_string(),
    ];
    let result = run_with_tcx!(&args, |tcx| {
        callback(tcx);
        std::ops::ControlFlow::<(), ()>::Continue(())
    });
    assert!(
        result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
        "rustc_public run failed: {result:?}"
    );
}

fn find_instance(tcx: TyCtxt<'_>, name: &str) -> Instance {
    rustc_public::all_local_items()
        .into_iter()
        .find_map(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            (tcx.def_path_str(def_id) == name).then(|| Instance::try_from(item).ok()).flatten()
        })
        .unwrap_or_else(|| panic!("no local fn named {name}"))
}

/// The one `PointerCoercion::Unsize` cast in `name`'s body, as (source, target).
fn only_unsize_cast(tcx: TyCtxt<'_>, name: &str) -> (TyStable, TyStable) {
    let body = find_instance(tcx, name).body().expect("fn body");
    let casts: Vec<_> = body
        .blocks
        .iter()
        .flat_map(|block| block.statements.iter())
        .filter_map(|statement| match &statement.kind {
            StatementKind::Assign(
                _,
                Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, target),
            ) => Some((operand.ty(body.locals()).unwrap(), *target)),
            _ => None,
        })
        .collect();
    assert_eq!(casts.len(), 1, "{name} should unsize exactly once, found {casts:?}");
    casts[0]
}

fn signature_inputs(tcx: TyCtxt<'_>) -> Vec<TyStable> {
    let instance = find_instance(tcx, "signature");
    let sig = instance.ty().kind().fn_sig().expect("fn signature").skip_binder();
    sig.inputs().to_vec()
}

fn is_pattern_type(ty: TyStable) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Pat(..)))
}

/// What the coercion base must be: the concrete sized type and what it unsizes to.
#[derive(Clone, Copy, Debug)]
enum Base {
    SquareToDynShape,
    ArrayToSlice,
}

const SMART_POINTER_CASES: &[(&str, Base, bool)] = &[
    // (fn, expected base, whether Trust core routes the coercion through NonNull)
    ("coerce_box", Base::SquareToDynShape, true),
    ("coerce_rc", Base::SquareToDynShape, true),
    ("coerce_arc", Base::SquareToDynShape, true),
    ("coerce_nonnull_slice", Base::ArrayToSlice, true),
    ("coerce_mut_dyn", Base::SquareToDynShape, false),
    ("coerce_custom_nonnull", Base::SquareToDynShape, true),
    ("coerce_custom_raw", Base::ArrayToSlice, false),
];

#[test]
fn unsize_coercion_base_is_the_pointee_pair_for_every_smart_pointer() {
    with_test_tcx_for_source(SMART_POINTER_COERCIONS, |tcx| {
        for &(name, expected, _) in SMART_POINTER_CASES {
            let (src, dst) = only_unsize_cast(tcx, name);
            let base = extract_unsize_casting(
                tcx,
                rustc_internal::internal(tcx, src),
                rustc_internal::internal(tcx, dst),
            );
            match expected {
                Base::SquareToDynShape => {
                    let rustc_middle::ty::Adt(def, _) = base.src_ty.kind() else {
                        panic!("{name}: source base should be Square, got {:?}", base.src_ty)
                    };
                    assert!(
                        tcx.def_path_str(def.did()).ends_with("Square"),
                        "{name}: source base should be Square, got {:?}",
                        base.src_ty
                    );
                    assert!(
                        base.dst_ty.is_trait(),
                        "{name}: target base should be dyn Shape, got {:?}",
                        base.dst_ty
                    );
                }
                Base::ArrayToSlice => {
                    assert!(
                        matches!(base.src_ty.kind(), rustc_middle::ty::Array(..)),
                        "{name}: source base should be [u8; 4], got {:?}",
                        base.src_ty
                    );
                    assert!(
                        base.dst_ty.is_slice(),
                        "{name}: target base should be [u8], got {:?}",
                        base.dst_ty
                    );
                }
            }
        }
    });
}

#[test]
fn unsize_walk_crosses_a_pointer_refinement_only_where_trust_core_has_one() {
    with_test_tcx_for_source(SMART_POINTER_COERCIONS, |tcx| {
        for &(name, _, through_non_null) in SMART_POINTER_CASES {
            let (src, dst) = only_unsize_cast(tcx, name);
            let walk: Vec<_> = CoerceUnsizedIterator::new(tcx, src, dst).collect();
            let refinement_steps: Vec<_> =
                walk.iter().filter(|step| is_pattern_type(step.src_ty)).collect();
            let expected = if through_non_null && cfg!(trust_toolchain) { 1 } else { 0 };
            assert_eq!(refinement_steps.len(), expected, "{name}: pattern-type steps in {walk:?}");
            for step in refinement_steps {
                assert!(is_pattern_type(step.dst_ty), "{name}: {step:?}");
                assert_eq!(step.field.as_deref(), Some(PATTERN_TYPE_BASE_FIELD), "{name}");
            }
            let last = walk.last().expect("the walk yields at least its start");
            assert_eq!(last.field, None, "{name}: the walk ends at the base pointer");
            assert!(
                last.src_ty.kind().is_any_ptr() && last.dst_ty.kind().is_any_ptr(),
                "{name}: the walk should end at builtin pointers, got {last:?}"
            );
        }
    });
}

#[test]
fn pointer_refinement_bases_fails_closed_on_patterns_that_do_not_refine_a_pointer() {
    with_test_tcx_for_source(RANGE_PATTERN_TYPES, |tcx| {
        let inputs = signature_inputs(tcx);
        let (from_one, from_two, thin, slice) = (inputs[0], inputs[1], inputs[2], inputs[3]);
        assert!(is_pattern_type(from_one) && is_pattern_type(from_two));

        let err = pointer_refinement_bases(from_one, from_one).unwrap_err();
        assert!(err.contains("does not refine a pointer"), "{err}");
        let err = pointer_refinement_bases(from_one, from_two).unwrap_err();
        assert!(err.contains("differ"), "{err}");
        let err = pointer_refinement_bases(from_one, thin).unwrap_err();
        assert!(err.contains("the source is a pattern type"), "{err}");
        let err = pointer_refinement_bases(thin, from_one).unwrap_err();
        assert!(err.contains("the target is a pattern type"), "{err}");
        assert_eq!(pointer_refinement_bases(thin, slice), Ok(None));
    });
}

#[cfg(trust_toolchain)]
#[test]
fn pointer_refinement_bases_peels_not_null_pointers_and_nothing_else() {
    with_test_tcx_for_source(NOT_NULL_PATTERN_TYPES, |tcx| {
        let inputs = signature_inputs(tcx);
        let (array_ptr, slice_ptr, range, raw_array_ptr) =
            (inputs[0], inputs[1], inputs[2], inputs[3]);

        let (src_base, dst_base) =
            pointer_refinement_bases(array_ptr, slice_ptr).unwrap().expect("a pointer refinement");
        assert_eq!(src_base, raw_array_ptr);
        assert!(dst_base.kind().is_raw_ptr(), "{dst_base:?}");

        let err = pointer_refinement_bases(array_ptr, range).unwrap_err();
        assert!(err.contains("differ"), "{err}");
        let err = pointer_refinement_bases(array_ptr, raw_array_ptr).unwrap_err();
        assert!(err.contains("the source is a pattern type"), "{err}");
    });
}
