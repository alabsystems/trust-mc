// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for function inlining pass.
//! Extracted from mod.rs (Part of #2204).

use super::remap::remap_block;
use super::*;
use crate::kani_middle::reachability::is_prefix_abstracted;
use crate::rustc_public_bridge::IndexedVal;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlock, BinOp, Operand, Place, ProjectionElem, Rvalue, Statement, StatementKind,
    Terminator, TerminatorKind, UnwindAction,
};
use rustc_public::rustc_internal;
use rustc_public::ty::Span;
use rustc_public::{CompilerError, run_with_tcx};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tempfile::TempDir;
use trust_mc_codegen_stubs::{StubKind, StubRegistry};

mod handler_boundaries_tests;
mod variadic_tests;

fn dummy_span() -> Span {
    Span::to_val(0)
}

fn mk_place(local: usize) -> Place {
    Place { local, projection: vec![] }
}

fn mk_local_map(pairs: &[(usize, usize)]) -> HashMap<usize, usize> {
    pairs.iter().copied().collect()
}

const STDLIB_STUB_BOUNDARY_SOURCE: &str = r#"
#![allow(dead_code)]
use std::str::FromStr;

pub fn probe_from_utf8(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
    std::str::from_utf8(bytes)
}

pub fn probe_vec_from(bytes: &[u8]) -> Vec<u8> {
    Vec::from(bytes)
}

pub fn probe_from_str(s: &str) -> Result<i32, std::num::ParseIntError> {
    i32::from_str(s)
}

pub fn probe_rc_clone(rc: &std::rc::Rc<i32>) -> std::rc::Rc<i32> {
    std::rc::Rc::clone(rc)
}

pub fn probe_arc_new(val: u32) -> std::sync::Arc<u32> { std::sync::Arc::new(val) }
pub fn probe_rc_new(val: u32) -> std::rc::Rc<u32> { std::rc::Rc::new(val) }
"#;

const SLICE_CONTAINS_HANDLER_BOUNDARY_SOURCE: &str = r#"
#![allow(dead_code)]

pub static DAYS_OF_WEEK: [char; 7] = ['s', 'm', 't', 'w', 't', 'f', 's'];

pub fn probe_slice_contains_boundary(day: usize) -> bool {
    ['s', 'm', 't', 'w', 'f'].contains(&DAYS_OF_WEEK[day])
}
"#;

const ALLOC_STUB_BOUNDARY_SOURCE: &str = r#"
#![allow(dead_code)]
use std::alloc::{Layout, alloc, dealloc, realloc};

pub unsafe fn probe_alloc_dealloc_boundary() {
    let layout = Layout::from_size_align(64, 8).unwrap();
    let ptr = unsafe { alloc(layout) };
    if !ptr.is_null() {
        unsafe { dealloc(ptr, layout) };
    }
}

pub unsafe fn probe_realloc_boundary() {
    let layout = Layout::from_size_align(8, 8).unwrap();
    let ptr = unsafe { alloc(layout) };
    let _new_ptr = unsafe { realloc(ptr, layout, 16) };
}
"#;

const ORD_MIN_MAX_CLAMP_BOUNDARY_SOURCE: &str = r#"
#![allow(dead_code)]

pub fn probe_integer_ord_min_max_clamp(a: i32, b: i32, c: usize, d: usize) -> (i32, usize, i32) {
    let lo = a.min(b);
    let hi = c.max(d);
    let bounded = a.clamp(-5, 5);
    (lo, hi, bounded)
}

pub fn probe_string_ord_min(a: String, b: String) -> String {
    a.min(b)
}
"#;

// === remap tests ===

fn with_test_tcx_for_source<F>(source: &str, callback: F)
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
{
    static CRATE_COUNTER: AtomicU64 = AtomicU64::new(0);
    let temp_dir = TempDir::new().expect("create temp dir");
    let src_path: PathBuf = temp_dir.path().join("lib.rs");
    fs::write(&src_path, source).expect("write test source");

    let unique_id = CRATE_COUNTER.fetch_add(1, Ordering::SeqCst);
    let crate_name = format!("inline_test_crate_{unique_id}");
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
        "-Z".to_string(),
        "inline-mir=no".to_string(),
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

fn find_instance_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> Instance {
    rustc_public::all_local_items()
        .into_iter()
        .find_map(|item| {
            let def_id = rustc_internal::internal(tcx, item.def_id());
            tcx.def_path_str(def_id)
                .ends_with(suffix)
                .then(|| Instance::try_from(item).ok())
                .flatten()
        })
        .expect("missing item with requested suffix")
}

fn collect_call_names(body: &Body) -> Vec<String> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let ty = func.ty(body.locals()).ok()?;
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else {
                return None;
            };
            Some(def.0.name())
        })
        .collect()
}

fn collect_call_defs(body: &Body) -> Vec<(String, FnDef, GenericArgs)> {
    body.blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                return None;
            };
            let ty = func.ty(body.locals()).ok()?;
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
                return None;
            };
            Some((def.0.name(), def, args))
        })
        .collect()
}

fn collect_stub_calls(call_names: &[String]) -> Vec<(String, StubKind)> {
    let registry = StubRegistry::new();
    call_names
        .iter()
        .filter_map(|name| registry.lookup(name).map(|stub| (name.clone(), stub)))
        .collect()
}

fn apply_codegen_inline_pass(tcx: TyCtxt<'_>, instance: Instance, body: Body) -> Body {
    let mut pass = FunctionInlinePass::new(InlineConfig::default());
    let (_, body) = pass.transform_with_body_provider(tcx, body, instance, |callee_instance| {
        if !callee_instance.has_body() {
            return None;
        }
        let callee_name = callee_instance.name();
        if is_prefix_abstracted(&callee_name) {
            return None;
        }
        callee_instance.body()
    });
    body
}

#[test]
fn test_remap_block_empty_no_mapping() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb + 10, Some(99));
    assert!(result.statements.is_empty());
    // Return should become Goto to call_target
    assert!(matches!(result.terminator.kind, TerminatorKind::Goto { target: 99 }));
}

#[test]
fn test_remap_block_return_without_call_target_becomes_unreachable() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb, None);
    assert!(matches!(result.terminator.kind, TerminatorKind::Unreachable));
}

#[test]
fn test_remap_block_goto_remaps_target() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator { kind: TerminatorKind::Goto { target: 3 }, span: dummy_span() },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb + 100, None);
    assert!(matches!(result.terminator.kind, TerminatorKind::Goto { target: 103 }));
}

#[test]
fn test_remap_block_storage_live_remaps_local() {
    let block = BasicBlock {
        statements: vec![Statement { kind: StatementKind::StorageLive(5), span: dummy_span() }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(5, 42)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert_eq!(result.statements.len(), 1);
    assert!(matches!(result.statements[0].kind, StatementKind::StorageLive(42)));
}

#[test]
fn test_remap_block_storage_dead_remaps_local() {
    let block = BasicBlock {
        statements: vec![Statement { kind: StatementKind::StorageDead(3), span: dummy_span() }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(3, 77)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(result.statements[0].kind, StatementKind::StorageDead(77)));
}

#[test]
fn test_remap_block_assign_remaps_both_place_and_operand() {
    let block = BasicBlock {
        statements: vec![Statement {
            kind: StatementKind::Assign(mk_place(1), Rvalue::Use(Operand::Copy(mk_place(2)))),
            span: dummy_span(),
        }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(1, 10), (2, 20)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    let StatementKind::Assign(place, Rvalue::Use(Operand::Copy(src))) = &result.statements[0].kind
    else {
        unreachable!("expected Assign(Place, Use(Copy(Place)))");
    };
    assert_eq!(place.local, 10);
    assert_eq!(src.local, 20);
}

#[test]
fn test_remap_block_unmapped_locals_pass_through() {
    let block = BasicBlock {
        statements: vec![Statement { kind: StatementKind::StorageLive(99), span: dummy_span() }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(1, 10)]); // 99 not in map
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(result.statements[0].kind, StatementKind::StorageLive(99)));
}

#[test]
fn test_remap_block_nop_passes_through() {
    let block = BasicBlock {
        statements: vec![Statement { kind: StatementKind::Nop, span: dummy_span() }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(result.statements[0].kind, StatementKind::Nop));
}

#[test]
fn test_remap_block_drop_remaps_place_and_target() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator {
            kind: TerminatorKind::Drop {
                place: mk_place(4),
                target: 7,
                unwind: UnwindAction::Continue,
            },
            span: dummy_span(),
        },
    };
    let local_map = mk_local_map(&[(4, 40)]);
    let result = remap_block(&block, &local_map, &|bb| bb + 100, None);
    assert!(matches!(&result.terminator.kind, TerminatorKind::Drop { .. }));
    let TerminatorKind::Drop { place, target, .. } = &result.terminator.kind else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert_eq!(place.local, 40);
    assert_eq!(*target, 107);
}

#[test]
fn test_remap_block_binary_op_remaps_operands() {
    let block = BasicBlock {
        statements: vec![Statement {
            kind: StatementKind::Assign(
                mk_place(0),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(mk_place(1)),
                    Operand::Move(mk_place(2)),
                ),
            ),
            span: dummy_span(),
        }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(0, 100), (1, 101), (2, 102)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(
        &result.statements[0].kind,
        StatementKind::Assign(_, Rvalue::BinaryOp(BinOp::Add, ..))
    ));
    let StatementKind::Assign(dest, Rvalue::BinaryOp(BinOp::Add, lhs, rhs)) =
        &result.statements[0].kind
    else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert_eq!(dest.local, 100);
    assert!(matches!(lhs, Operand::Copy(p) if p.local == 101));
    assert!(matches!(rhs, Operand::Move(p) if p.local == 102));
}

#[test]
fn test_remap_block_projection_index_remapped() {
    let block = BasicBlock {
        statements: vec![Statement {
            kind: StatementKind::Assign(
                Place { local: 0, projection: vec![ProjectionElem::Index(5)] },
                Rvalue::Use(Operand::Copy(mk_place(1))),
            ),
            span: dummy_span(),
        }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(0, 10), (5, 50), (1, 11)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(&result.statements[0].kind, StatementKind::Assign(..)));
    let StatementKind::Assign(place, _) = &result.statements[0].kind else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert_eq!(place.local, 10);
    assert_eq!(place.projection.len(), 1);
    assert!(matches!(place.projection[0], ProjectionElem::Index(50)));
}

#[test]
fn test_remap_block_unwind_cleanup_remapped() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator {
            kind: TerminatorKind::Drop {
                place: mk_place(0),
                target: 1,
                unwind: UnwindAction::Cleanup(5),
            },
            span: dummy_span(),
        },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb + 10, None);
    assert!(matches!(&result.terminator.kind, TerminatorKind::Drop { .. }));
    let TerminatorKind::Drop { unwind, .. } = &result.terminator.kind else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert!(matches!(unwind, UnwindAction::Cleanup(15)));
}

#[test]
fn test_remap_block_unwind_continue_unchanged() {
    let block = BasicBlock {
        statements: vec![],
        terminator: Terminator {
            kind: TerminatorKind::Drop {
                place: mk_place(0),
                target: 1,
                unwind: UnwindAction::Continue,
            },
            span: dummy_span(),
        },
    };
    let local_map = mk_local_map(&[]);
    let result = remap_block(&block, &local_map, &|bb| bb + 10, None);
    assert!(matches!(&result.terminator.kind, TerminatorKind::Drop { .. }));
    let TerminatorKind::Drop { unwind, .. } = &result.terminator.kind else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert!(matches!(unwind, UnwindAction::Continue));
}

#[test]
fn test_remap_block_discriminant_remaps_place() {
    let block = BasicBlock {
        statements: vec![Statement {
            kind: StatementKind::Assign(mk_place(0), Rvalue::Discriminant(mk_place(3))),
            span: dummy_span(),
        }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(0, 10), (3, 30)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(
        &result.statements[0].kind,
        StatementKind::Assign(_, Rvalue::Discriminant(_))
    ));
    let StatementKind::Assign(dest, Rvalue::Discriminant(place)) = &result.statements[0].kind
    else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert_eq!(dest.local, 10);
    assert_eq!(place.local, 30);
}

#[test]
fn test_remap_block_copy_for_deref_remaps_place() {
    let block = BasicBlock {
        statements: vec![Statement {
            kind: StatementKind::Assign(mk_place(0), Rvalue::CopyForDeref(mk_place(7))),
            span: dummy_span(),
        }],
        terminator: Terminator { kind: TerminatorKind::Return, span: dummy_span() },
    };
    let local_map = mk_local_map(&[(0, 10), (7, 70)]);
    let result = remap_block(&block, &local_map, &|bb| bb, Some(0));
    assert!(matches!(
        &result.statements[0].kind,
        StatementKind::Assign(_, Rvalue::CopyForDeref(_))
    ));
    let StatementKind::Assign(dest, Rvalue::CopyForDeref(place)) = &result.statements[0].kind
    else {
        unreachable!("preceding assert confirmed the pattern match");
    };
    assert_eq!(dest.local, 10);
    assert_eq!(place.local, 70);
}

#[test]
fn test_inline_config_default() {
    let config = InlineConfig::default();
    assert_eq!(config.max_depth, 10);
    assert!(config.enabled);
}

#[test]
fn test_inline_config_custom() {
    let config = InlineConfig { max_depth: 5, enabled: false };
    assert_eq!(config.max_depth, 5);
    assert!(!config.enabled);
}

#[test]
fn test_function_inline_pass_new() {
    let config = InlineConfig { max_depth: 20, enabled: true };
    let pass = FunctionInlinePass::new(config);
    assert_eq!(pass.config.max_depth, 20);
    assert!(pass.config.enabled);
}

#[test]
fn test_has_special_codegen_handler_option() {
    // Option methods should have special handlers
    assert!(FunctionInlinePass::has_special_codegen_handler("Option::is_none"));
    assert!(FunctionInlinePass::has_special_codegen_handler("Option::is_some"));
    assert!(FunctionInlinePass::has_special_codegen_handler("Option::unwrap"));
}

#[test]
fn test_has_special_codegen_handler_arithmetic() {
    // Checked/wrapping arithmetic should have special handlers
    assert!(FunctionInlinePass::has_special_codegen_handler("u32::checked_add"));
    assert!(FunctionInlinePass::has_special_codegen_handler("i64::wrapping_mul"));
    assert!(FunctionInlinePass::has_special_codegen_handler("u8::saturating_sub"));
}

#[test]
fn test_has_special_codegen_handler_regular() {
    // Regular functions should not have special handlers
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_function"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("foo::bar::baz"));
}

#[test]
fn test_has_special_codegen_handler_cell_quarantine_is_exact() {
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::Cell::<u32>::get"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::cell::Cell::<u32>::set"));
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::Cell::<u8>::replace"));
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::Cell::take"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::cell::Cell::<u8>::swap"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("std::cell::Cell::<u8>::new"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_crate::cell::Cellar::get"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::cell::Cellar::set"));
    // Canonical RefCell semantic-lane boundary trio: replace/replace_with/
    // as_ptr stay call-boundary-visible for codegen_call_cell.rs; everything
    // else on RefCell (borrow/borrow_mut/new/...) still deep-inlines, and
    // user types must not inherit the boundary.
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::RefCell::replace"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::cell::RefCell::<u32>::replace_with"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::RefCell::<u32>::as_ptr"));
    assert!(FunctionInlinePass::has_special_codegen_handler("core::cell::Cell::<u32>::as_ptr"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::cell::RefCell::borrow_mut"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::cell::RefCell::<u8>::new"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my::cell::RefCellish::replace"));
}

#[test]
fn test_has_special_codegen_handler_string() {
    // String operations should have special handlers (#1691)
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "alloc::string::String::from_utf8_lossy"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::string::String::new"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::string::String::len"));
}

#[test]
fn test_has_special_codegen_handler_core_stub_boundaries() {
    assert!(FunctionInlinePass::has_special_codegen_handler("core::str::converts::from_utf8"));
    // from_utf8_lossy remains blocked via the broader String stub path; this
    // boundary test only checks the new core::str-specific matcher.
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::str::converts::from_utf8_unchecked"
    ));
    // Vec::from is handled by has_stubbed_trait_impl (instance resolution),
    // not has_special_codegen_handler (string matching). The def-path name
    // "std::convert::From::from" doesn't contain "Vec" (#3679).
    assert!(!FunctionInlinePass::has_special_codegen_handler("std::convert::From::from"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<i32 as core::str::traits::FromStr>::from_str"
    ));
}

#[test]
fn test_has_special_codegen_handler_cow() {
    // Cow operations should have special handlers (#1691)
    assert!(FunctionInlinePass::has_special_codegen_handler("std::borrow::Cow::to_string"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::borrow::Cow::into_owned"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<std::borrow::Cow<str> as alloc::string::ToString>::to_string"
    ));
}

#[test]
fn test_has_special_codegen_handler_to_string() {
    // ToString trait should have special handlers (#1691)
    assert!(FunctionInlinePass::has_special_codegen_handler("<T as ToString>::to_string"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::string::ToString::to_string"));
}

#[test]
fn test_has_special_codegen_handler_slice_first() {
    assert!(FunctionInlinePass::has_special_codegen_handler("core::slice::<impl [T]>::first"));
    assert!(FunctionInlinePass::has_special_codegen_handler("<[u8]>::first"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_struct::first"));
}
#[test]
fn test_has_special_codegen_handler_hashmap() {
    assert!(FunctionInlinePass::has_special_codegen_handler("std::collections::HashMap::insert"));
    assert!(FunctionInlinePass::has_special_codegen_handler("hashbrown::raw::RawTable::find"));
    assert!(FunctionInlinePass::has_special_codegen_handler("HashMap::new"));
    // Part of #3057: module-path iterator types must also be blocked
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::collections::hash_map::IntoIter::<i32, i32>::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::collections::hash_set::IntoIter::<i32>::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<std::collections::hash_map::IntoIter<i32, i32> as core::iter::Iterator>::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("HashSet::iter"));
}

#[test]
fn test_has_special_codegen_handler_trust_mcmap() {
    // TrustMcMap is the verification-friendly HashMap — its marker methods must
    // not be inlined so CHC codegen can intercept them via StubRegistry (#788).
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::default"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::insert"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::contains_key"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::new"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMapIntoIter::<u32, u32>::next"
    ));
}

#[test]
fn test_has_special_codegen_handler_trust_mcmap_unstubbed_methods() {
    // Guard against over-broad TrustMcMap matching: only methods with concrete
    // CHC handlers should be forced to stay as Call terminators.
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::iter"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "kani::hashmap::TrustMcMap::<u32, u32>::values"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_crate::TrustMcMapHelper::new"));
}

#[test]
fn test_has_special_codegen_handler_btree() {
    assert!(FunctionInlinePass::has_special_codegen_handler("BTreeSet::insert"));
    assert!(FunctionInlinePass::has_special_codegen_handler("BTreeMap::get"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "alloc::collections::btree::node::search"
    ));
}

#[test]
fn test_has_special_codegen_handler_vec_stubs() {
    // Vec stub methods should have special handlers
    assert!(FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::push"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::vec::Vec::<T>::pop"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::len"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::new"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::vec::Vec::<T>::with_capacity"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::is_empty"));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::vec::Vec::<T>::clear"));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::as_slice"));
}

#[test]
fn test_has_special_codegen_handler_vec_rawvec_excluded() {
    // The RawVec guard prevents matching when a Vec path also contains "RawVec".
    // In practice this guards against inlined paths like "alloc::vec::Vec::<T>::reserve::RawVec..."
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "alloc::vec::Vec::<T>::reserve::alloc::raw_vec::RawVec::<T,A>::grow_amortized"
    ));
    // Real standalone RawVec paths don't contain "std::vec::Vec" at all,
    // so they skip the Vec block entirely and also return false.
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "alloc::raw_vec::RawVec::<T,A>::grow_amortized"
    ));
}

#[test]
fn test_has_special_codegen_handler_vec_non_stub() {
    // Vec method not in stub list — should NOT match
    assert!(!FunctionInlinePass::has_special_codegen_handler("std::vec::Vec::<T>::sort"));
}

#[test]
fn test_has_special_codegen_handler_allocator() {
    assert!(FunctionInlinePass::has_special_codegen_handler("exchange_malloc"));
    assert!(FunctionInlinePass::has_special_codegen_handler("__rust_alloc"));
    assert!(FunctionInlinePass::has_special_codegen_handler("__rust_dealloc"));
    assert!(FunctionInlinePass::has_special_codegen_handler("__rust_realloc"));
}

#[test]
fn test_has_special_codegen_handler_overflowing_unchecked() {
    // overflowing_ and unchecked_ branches
    assert!(FunctionInlinePass::has_special_codegen_handler("u32::overflowing_add"));
    assert!(FunctionInlinePass::has_special_codegen_handler("i64::unchecked_mul"));
}

#[test]
fn test_has_special_codegen_handler_pow() {
    // Plain pow must be caught (Part of #3402) — wrapping_pow is already caught
    // by the wrapping_ prefix, but pow has its own CHC handler via is_pow_method.
    assert!(FunctionInlinePass::has_special_codegen_handler("i64::pow"));
    assert!(FunctionInlinePass::has_special_codegen_handler("u32::pow"));
    assert!(FunctionInlinePass::has_special_codegen_handler("core::num::<impl i64>::pow"));
    // wrapping_pow still works via prefix match
    assert!(FunctionInlinePass::has_special_codegen_handler("i32::wrapping_pow"));
    // Non-pow suffix should not match
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_module::empower"));
}

#[test]
fn test_has_special_codegen_handler_does_not_block_ord_by_name_only() {
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::cmp::Ord::min"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("<i32 as core::cmp::Ord>::max"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::cmp::Ord::clamp"));
}

#[test]
fn test_has_special_codegen_handler_option_non_matching() {
    // Option method that doesn't match is_none/is_some/unwrap → falls through
    // to subsequent checks. "map" is not in the Option filter list.
    assert!(!FunctionInlinePass::has_special_codegen_handler("Option::map"));
}

#[test]
fn test_has_special_codegen_handler_stable_atomic() {
    // Stable atomic API methods — preserved for CHC atomic stubs (Part of #3452)
    assert!(FunctionInlinePass::has_special_codegen_handler("std::sync::atomic::AtomicBool::load"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicIsize::fetch_add"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("std::sync::atomic::AtomicU32::store"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::sync::atomic::AtomicPtr::<i32>::swap"
    ));
    // Non-atomic "sync" paths should NOT match
    assert!(!FunctionInlinePass::has_special_codegen_handler("std::sync::Mutex::lock"));
}

#[test]
fn test_has_special_codegen_handler_allocator_layout_boundaries() {
    assert!(FunctionInlinePass::has_special_codegen_handler("std::alloc::dealloc"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<std::alloc::Global as std::alloc::Allocator>::deallocate"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("alloc::alloc::realloc"));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::alloc::Layout::from_size_align"
    ));
}

#[test]
fn test_inline_pass_preserves_from_utf8_call_boundary() {
    with_test_tcx_for_source(STDLIB_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_from_utf8");
        let body = instance.body().expect("probe_from_utf8 should have a body");
        let original_calls = collect_call_names(&body);
        assert!(
            original_calls.iter().any(|name| name.contains("from_utf8")),
            "expected probe_from_utf8 to start with a from_utf8 call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        assert!(
            inlined_calls.iter().any(|name| name.contains("from_utf8")),
            "FunctionInlinePass should preserve from_utf8 for stub dispatch, got {inlined_calls:?}"
        );
    });
}

#[test]
fn test_inline_pass_preserves_vec_from_call_boundary() {
    with_test_tcx_for_source(STDLIB_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_vec_from");
        let body = instance.body().expect("probe_vec_from should have a body");
        let original_calls = collect_call_names(&body);
        assert!(
            original_calls.iter().any(|name| name.contains("From") && name.ends_with("::from")),
            "expected probe_vec_from to start with a From::from call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        assert!(
            inlined_calls.iter().any(|name| name.contains("From") && name.ends_with("::from")),
            "FunctionInlinePass should preserve From::from (Vec impl) for stub dispatch, got {inlined_calls:?}"
        );
    });
}

#[test]
fn test_inline_pass_preserves_from_str_call_boundary() {
    with_test_tcx_for_source(STDLIB_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_from_str");
        let body = instance.body().expect("probe_from_str should have a body");
        let original_calls = collect_call_names(&body);
        assert!(
            original_calls
                .iter()
                .any(|name| name.contains("FromStr") && name.ends_with("::from_str")),
            "expected probe_from_str to start with a FromStr::from_str call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        assert!(
            inlined_calls
                .iter()
                .any(|name| name.contains("FromStr") && name.ends_with("::from_str")),
            "FunctionInlinePass should preserve FromStr::from_str for stub dispatch, got {inlined_calls:?}"
        );
    });
}

#[test]
fn test_inline_pass_preserves_integer_ord_min_max_clamp_boundaries() {
    with_test_tcx_for_source(ORD_MIN_MAX_CLAMP_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_integer_ord_min_max_clamp");
        let body = instance.body().expect("probe_integer_ord_min_max_clamp should have a body");
        let original_calls = collect_call_names(&body);
        for method in ["::min", "::max", "::clamp"] {
            assert!(
                original_calls
                    .iter()
                    .any(|name| name.contains("cmp::Ord") && name.ends_with(method)),
                "expected integer Ord{method} call before inline, got {original_calls:?}"
            );
        }

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        for method in ["::min", "::max", "::clamp"] {
            assert!(
                inlined_calls
                    .iter()
                    .any(|name| name.contains("cmp::Ord") && name.ends_with(method)),
                "FunctionInlinePass should preserve integer Ord{method} for CHC cmp dispatch, got {inlined_calls:?}"
            );
        }
    });
}

#[test]
fn test_inline_pass_does_not_preserve_string_ord_min_boundary() {
    with_test_tcx_for_source(ORD_MIN_MAX_CLAMP_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_string_ord_min");
        let body = instance.body().expect("probe_string_ord_min should have a body");
        let call_defs = collect_call_defs(&body);
        let (_, fn_def, fn_args) = call_defs
            .iter()
            .find(|(name, _, _)| name.contains("cmp::Ord") && name.ends_with("::min"))
            .expect("expected String Ord::min call before inline");
        assert!(
            !FunctionInlinePass::is_integer_ord_min_max_clamp_resolved(*fn_def, fn_args),
            "String Ord::min must not match the integer-only inline boundary policy"
        );
    });
}

#[test]
fn test_inline_pass_preserves_rc_clone_call_boundary() {
    with_test_tcx_for_source(STDLIB_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_rc_clone");
        let body = instance.body().expect("probe_rc_clone should have a body");
        let original_calls = collect_call_names(&body);
        // MIR def-path for Rc::clone is "std::clone::Clone::clone" (trait method).
        // The resolved instance name would show Rc, but collect_call_names returns
        // the unresolved def-path name.
        assert!(
            original_calls.iter().any(|name| name.contains("Clone") && name.ends_with("::clone")),
            "expected probe_rc_clone to contain a Clone::clone call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        // After inlining, the Clone::clone call for Rc should be preserved (not
        // expanded into stdlib Cell/NonNull internals). Part of #3978.
        assert!(
            inlined_calls.iter().any(|name| name.contains("Clone") && name.ends_with("::clone")),
            "FunctionInlinePass should preserve Rc::clone for CHC dispatch, got {inlined_calls:?}"
        );
    });
}

/// Part of #4067: Arc/Rc::new preserved for CHC `codegen_rc_arc_new`.
#[test]
fn test_inline_pass_preserves_rc_arc_new_call_boundary() {
    with_test_tcx_for_source(STDLIB_STUB_BOUNDARY_SOURCE, |tcx| {
        for (probe, kind) in [("probe_arc_new", "Arc"), ("probe_rc_new", "Rc")] {
            let inst = find_instance_by_suffix(tcx, probe);
            let body = inst.body().unwrap_or_else(|| panic!("{probe} needs body"));
            let has_new =
                |calls: &[String]| calls.iter().any(|n| n.contains(kind) && n.ends_with("::new"));
            assert!(has_new(&collect_call_names(&body)), "{kind}::new missing before inline");
            let inlined = apply_codegen_inline_pass(tcx, inst, body);
            assert!(has_new(&collect_call_names(&inlined)), "{kind}::new removed by inline pass");
        }
    });
}

#[test]
fn test_inline_pass_preserves_dealloc_stub_boundary() {
    with_test_tcx_for_source(ALLOC_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_alloc_dealloc_boundary");
        let body = instance.body().expect("probe_alloc_dealloc_boundary should have a body");
        let original_calls = collect_call_names(&body);
        let original_stubs = collect_stub_calls(&original_calls);
        assert!(
            original_stubs.iter().any(|(_, stub)| matches!(stub, StubKind::RustDealloc)),
            "expected probe_alloc_dealloc_boundary to start with a RustDealloc-reachable call, got calls={original_calls:?}, stubs={original_stubs:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        let inlined_stubs = collect_stub_calls(&inlined_calls);
        assert!(
            inlined_stubs.iter().any(|(_, stub)| matches!(stub, StubKind::RustDealloc)),
            "FunctionInlinePass should preserve RustDealloc call boundaries for CHC stub dispatch, got calls={inlined_calls:?}, stubs={inlined_stubs:?}"
        );
    });
}

#[test]
fn test_inline_pass_preserves_realloc_stub_boundary() {
    with_test_tcx_for_source(ALLOC_STUB_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_realloc_boundary");
        let body = instance.body().expect("probe_realloc_boundary should have a body");
        let original_calls = collect_call_names(&body);
        let original_stubs = collect_stub_calls(&original_calls);
        assert!(
            original_stubs.iter().any(|(_, stub)| matches!(stub, StubKind::RustRealloc)),
            "expected probe_realloc_boundary to start with a RustRealloc-reachable call, got calls={original_calls:?}, stubs={original_stubs:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        let inlined_stubs = collect_stub_calls(&inlined_calls);
        assert!(
            inlined_stubs.iter().any(|(_, stub)| matches!(stub, StubKind::RustRealloc)),
            "FunctionInlinePass should preserve RustRealloc call boundaries for CHC stub dispatch, got calls={inlined_calls:?}, stubs={inlined_stubs:?}"
        );
    });
}

const USER_BLOCK_ON_SOURCE: &str = r#"
#![allow(dead_code)]
use std::{
    future::Future,
    pin::Pin,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};

fn probe_manual_block_on() {
    block_on(async { 42 });
}

pub fn block_on<T>(mut fut: impl Future<Output = T>) -> T {
    let waker = unsafe { Waker::from_raw(NOOP_RAW_WAKER) };
    let cx = &mut Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(cx) {
            std::task::Poll::Ready(res) => return res,
            std::task::Poll::Pending => continue,
        }
    }
}

const NOOP_RAW_WAKER: RawWaker = {
    unsafe fn clone_waker(_: *const ()) -> RawWaker { NOOP_RAW_WAKER }
    unsafe fn noop(_: *const ()) {}
    RawWaker::new(std::ptr::null(), &RawWakerVTable::new(clone_waker, noop, noop, noop))
};
"#;

/// Part of #3988: user-defined `block_on` must be preserved as a call boundary
/// so the CHC block_on specializer can rewrite the poll loop. Before this fix,
/// only `kani::block_on` was preserved — the user-defined version was inlined,
/// destroying the call site the specializer needs.
#[test]
fn test_inline_pass_preserves_user_block_on_call_boundary() {
    with_test_tcx_for_source(USER_BLOCK_ON_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_manual_block_on");
        let body = instance.body().expect("probe_manual_block_on should have a body");
        let original_calls = collect_call_names(&body);
        assert!(
            original_calls.iter().any(|name| name.contains("block_on")),
            "expected probe_manual_block_on to contain a block_on call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        assert!(
            inlined_calls.iter().any(|name| name.contains("block_on")),
            "FunctionInlinePass should preserve user-defined block_on call for CHC specializer, \
             got {inlined_calls:?}"
        );
    });
}

#[test]
fn test_inline_pass_preserves_slice_contains_call_boundary() {
    with_test_tcx_for_source(SLICE_CONTAINS_HANDLER_BOUNDARY_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_slice_contains_boundary");
        let body = instance.body().expect("probe_slice_contains_boundary should have a body");
        let original_calls = collect_call_names(&body);
        assert!(
            original_calls.iter().any(|name| name.ends_with("::contains")),
            "expected probe_slice_contains_boundary to contain a slice::contains call, got {original_calls:?}"
        );

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        assert!(
            inlined_calls.iter().any(|name| name.ends_with("::contains")),
            "FunctionInlinePass should preserve slice::contains for CHC direct dispatch, got {inlined_calls:?}"
        );
    });
}

// Part of #4000: Source fixture for dyn_fn_mut wrapper-forwarded two-call localizer.
// Tests whether FunctionInlinePass preserves actionable call boundaries for
// Box<dyn FnMut> wrapper forwarding (the exact shape from dyn_fn_mut.rs).
const DYN_FN_MUT_WRAPPER_SOURCE: &str = r#"
#![allow(dead_code)]

fn takes_dyn_fun(mut fun: Box<dyn FnMut(&mut i32)>, x_ptr: &mut i32) {
    fun(x_ptr)
}

fn mut_i32_ptr(x: &mut i32) {
    *x = *x + 1;
}

fn probe_dyn_fn_mut_wrapper() {
    let mut x: i32 = 1;
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 2);
    takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
    assert!(x == 3);
}
"#;

/// D2 localizer: inspect post-inline call list for the dyn_fn_mut wrapper shape.
/// If the inline pass erases both the wrapper call (`takes_dyn_fun`) and any
/// inner FnMut/call_mut boundary, the fix must go in FunctionInlinePass.
/// If an actionable boundary survives, the fix belongs in the CHC layer.
/// Part of #4000.
#[test]
fn test_inline_pass_dyn_fn_mut_wrapper_localizer() {
    with_test_tcx_for_source(DYN_FN_MUT_WRAPPER_SOURCE, |tcx| {
        let instance = find_instance_by_suffix(tcx, "probe_dyn_fn_mut_wrapper");
        let body = instance.body().expect("probe_dyn_fn_mut_wrapper should have a body");
        let original_calls = collect_call_names(&body);
        eprintln!("=== dyn_fn_mut wrapper: pre-inline calls ===\n{original_calls:?}");

        let inlined = apply_codegen_inline_pass(tcx, instance, body);
        let inlined_calls = collect_call_names(&inlined);
        eprintln!("=== dyn_fn_mut wrapper: post-inline calls ===\n{inlined_calls:?}");

        // Diagnostic: report whether actionable boundaries survive.
        // An actionable boundary is one CHC can dispatch on:
        // - takes_dyn_fun (the wrapper itself)
        // - FnMut::call_mut or similar trait call
        // - Box::new (allocation boundary)
        let has_wrapper_call = inlined_calls.iter().any(|name| name.contains("takes_dyn_fun"));
        let has_fn_trait_call =
            inlined_calls.iter().any(|name| name.contains("call_mut") || name.contains("FnMut"));
        let has_box_new = inlined_calls.iter().any(|name| {
            name.contains("box_alloc") || (name.contains("Box") && name.contains("new"))
        });

        eprintln!(
            "=== boundary survival: wrapper={has_wrapper_call}, fn_trait={has_fn_trait_call}, \
             box_new={has_box_new} ==="
        );

        // At minimum, the post-inline body should retain SOME call structure.
        // If everything is inlined away, the CHC layer has nothing to dispatch on.
        assert!(
            !inlined_calls.is_empty(),
            "FunctionInlinePass produced an empty call list for dyn_fn_mut wrapper — \
             all boundaries erased, CHC cannot dispatch"
        );
    });
}

#[test]
fn test_has_special_codegen_handler_iterator_adapter_next() {
    // Part of #4112: Iterator adapter next() calls must NOT be inlined.
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::flatten::FlatMap::<I, U, F>::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<core::iter::adapters::flatten::FlatMap<std::slice::Iter<&[u8]>, std::str::Chars, closure> as Iterator>::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::map::Map::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::filter::Filter::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::filter_map::FilterMap::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::zip::Zip::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::chain::Chain::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::flatten::Flatten::next"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::flatten::FlattenCompat::next"
    ));
    // Non-adapter next() should NOT match
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::slice::iter::Iter::next"));
    // Non-next methods on adapters should NOT match
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::iter::adapters::map::Map::size_hint"
    ));
}
