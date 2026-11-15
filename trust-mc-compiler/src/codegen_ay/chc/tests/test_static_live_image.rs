// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A LIVE static's pointee is the lane's live state
//! (`shared/const_pointer.rs`). In the CHC lane a static lives in two places,
//! its state variable and its memory image, and the entry rule seeds the image
//! under every typed view its type decomposes into: an `AtomicU32` under
//! `AtomicU32` and under `u32`. A raw read through a pointer a call returns
//! (`A.as_ptr()`) or a cast makes selects the image.
//!
//! A store wrote one view and left the others at the initializer: after
//! `A.store(7)` the `u32` view still held 5, and `assert!(*A.as_ptr() == 5)`
//! was PROVED in 2 ms (const_pointer_live_raw_read_dual.rs,
//! `bug_atomic_as_ptr_after_store`, main ed592ea3d), while Kani and the BMC
//! lane fail it. Every store into a static now rewrites the whole image from
//! the static's new state (`sync_static_image`), or havocs it with the state.
//! Each bug probe must reach its error, and each safe twin must prove with no
//! drop reason.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

#[test]
fn test_static_image_decomposes_erased_carrier_without_erasing_datatypes() {
    let mut source = String::from(
        r#"
        use std::cell::UnsafeCell;
        use std::sync::atomic::AtomicU32;
        #[repr(transparent)] pub struct Kept { pub payload: u32 }
        #[repr(C, align(8))] pub struct Padded(pub u32);
        type C0 = AtomicU32;
        "#,
    );
    for index in 1..=13 {
        source.push_str(&format!("type C{index} = UnsafeCell<C{}>;\n", index - 1));
    }
    source.push_str("pub fn carriers(a: AtomicU32, b: Kept, c: Padded, d: C13) {}\n");
    with_test_ay_ctx_for_source(&source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "carriers").body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "carriers", ChcConfig::default());
        let atomic = body.locals()[1].ty;
        let atomic_sort = ChcCtx::translate_ty(atomic).unwrap();
        let fields = chc.static_image_field_views(atomic, &atomic_sort).unwrap();
        assert_eq!(fields.len(), 1);
        let (storage, storage_sort, offset) = &fields[0];
        assert_eq!(*offset, 0);
        assert!(storage_sort.is_datatype(), "the alignment storage remains a datatype");
        let payload = chc
            .static_image_field_views(*storage, storage_sort)
            .expect("the erased UnsafeCell layer must not hide the alignment storage's fields");
        assert_eq!(payload.len(), 1);
        assert_eq!(payload[0].1.bitvec_width(), Some(32));
        assert_eq!(payload[0].2, 0);

        let kept = body.locals()[2].ty;
        let kept_sort = ChcCtx::translate_ty(kept).unwrap();
        assert!(kept_sort.is_datatype());
        assert_eq!(chc.static_image_field_views(kept, &kept_sort).unwrap().len(), 1);
        assert!(
            chc.static_image_field_views(kept, storage_sort).is_none(),
            "a different datatype's field names must not bypass the validator"
        );

        let padded = body.locals()[3].ty;
        let padded_sort = ChcCtx::translate_ty(padded).unwrap();
        assert!(padded_sort.is_datatype());
        assert_eq!(chc.static_image_field_views(padded, &padded_sort).unwrap().len(), 1);

        let deep = body.locals()[4].ty;
        assert!(
            chc.static_image_field_views(deep, &ChcCtx::translate_ty(deep).unwrap()).is_none(),
            "erased-carrier normalization must retain its depth refusal"
        );
    });
}

#[test]
fn test_static_initializer_decodes_erased_struct_fields_by_layout() {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget};

    let source = r#"
        use std::cell::UnsafeCell;
        #[derive(Clone, Copy)]
        pub struct Pt { pub x: u16, pub y: u32 }
        struct SyncCell<T>(UnsafeCell<T>);
        unsafe impl<T> Sync for SyncCell<T> {}
        static CELL: SyncCell<Pt> = SyncCell(UnsafeCell::new(Pt { x: 1, y: 0x0102_0304 }));
        pub fn cell_ptr(_: Pt) -> *mut Pt { CELL.0.get() }
    "#;
    with_test_ay_ctx_for_source(source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "cell_ptr").body().unwrap();
        let constants = const_pointer::body_constants_read(&body, &[], &|_| false);
        let statics: Vec<_> = constants
            .iter()
            .filter_map(|(bytes, _)| {
                let pointer = bytes.stored_pointer(0)?;
                let ConstTarget::Static(def) = pointer.kind() else { return None };
                Some((def.ty(), pointer.key()?))
            })
            .collect();
        let [(static_ty, key)] = statics.as_slice() else {
            panic!("expected exactly the CELL static, found {statics:?}");
        };
        let (bytes, _) = const_pointer::target_bytes(ctx.tcx, key).unwrap();
        let sort = ChcCtx::translate_ty(*static_ty).unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "cell_ptr", ChcConfig::default());
        let decoded = chc.read_static_value_by_layout(&bytes, 0, *static_ty, &sort, 0).unwrap();
        let wrapper = chc.static_image_fields(*static_ty, &decoded).unwrap();
        assert_eq!(wrapper.len(), 1);
        let fields = chc.static_image_fields(wrapper[0].0, &wrapper[0].1).unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].1.to_string(), Expr::bitvec_const(1u64, 16).to_string());
        assert_eq!(fields[1].1.to_string(), Expr::bitvec_const(0x0102_0304u64, 32).to_string());
        let layout = crate::kani_middle::abi::LayoutOf::new(body.locals()[1].ty);
        assert_eq!(fields[0].2, layout.field_offset(0).unwrap() as u64);
        assert_eq!(fields[1].2, layout.field_offset(1).unwrap() as u64);
        assert!(
            chc.read_static_value_by_layout(&bytes, bytes.len(), *static_ty, &sort, 0).is_none(),
            "carrier normalization must not admit reads beyond the allocation"
        );
    });
}

#[test]
fn test_static_initializer_retains_deep_scalar_field_reads() {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget};

    let mut source = String::from("use std::cell::UnsafeCell; type C0 = u32;\n");
    let mut value = "42u32".to_string();
    for depth in 1..=13 {
        source.push_str(&format!("type C{depth} = UnsafeCell<C{}>;\n", depth - 1));
        value = format!("UnsafeCell::new({value})");
    }
    source.push_str(&format!(
        "pub struct Outer {{ pub tag: u8, pub deep: C13 }}\n\
         unsafe impl Sync for Outer {{}}\n\
         static CELL: Outer = Outer {{ tag: 7, deep: {value} }};\n\
         pub fn deep_ptr(_: Outer) -> *const Outer {{ &CELL }}\n"
    ));
    with_test_ay_ctx_for_source(&source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "deep_ptr").body().unwrap();
        let constants = const_pointer::body_constants_read(&body, &[], &|_| false);
        let statics: Vec<_> = constants
            .iter()
            .filter_map(|(bytes, _)| {
                let pointer = bytes.stored_pointer(0)?;
                let ConstTarget::Static(def) = pointer.kind() else { return None };
                Some((def.ty(), pointer.key()?))
            })
            .collect();
        let [(static_ty, key)] = statics.as_slice() else {
            panic!("expected exactly the CELL static, found {statics:?}");
        };
        let (bytes, _) = const_pointer::target_bytes(ctx.tcx, key).unwrap();
        let sort = ChcCtx::translate_ty(*static_ty).unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "deep_ptr", ChcConfig::default());
        let decoded = chc
            .read_static_value_by_layout(&bytes, 0, *static_ty, &sort, 0)
            .expect("a scalar field needs no composite wrapper peeling");
        let fields = chc.static_image_fields(*static_ty, &decoded).unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].1.to_string(), Expr::bitvec_const(7u64, 8).to_string());
        assert_eq!(fields[1].1.to_string(), Expr::bitvec_const(42u64, 32).to_string());
    });
}

#[test]
fn test_static_initializer_retains_deep_array_field_reads() {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget};

    let mut source = String::from("use std::cell::UnsafeCell; type C0 = [u32; 2];\n");
    let mut value = "[3u32, 5u32]".to_string();
    for depth in 1..=13 {
        source.push_str(&format!("type C{depth} = UnsafeCell<C{}>;\n", depth - 1));
        value = format!("UnsafeCell::new({value})");
    }
    source.push_str(&format!(
        "pub struct Outer {{ pub tag: u8, pub deep: C13 }}\n\
         unsafe impl Sync for Outer {{}}\n\
         static CELL: Outer = Outer {{ tag: 7, deep: {value} }};\n\
         pub fn deep_array_ptr(_: Outer) -> *const Outer {{ &CELL }}\n"
    ));
    with_test_ay_ctx_for_source(&source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "deep_array_ptr").body().unwrap();
        let constants = const_pointer::body_constants_read(&body, &[], &|_| false);
        let statics: Vec<_> = constants
            .iter()
            .filter_map(|(bytes, _)| {
                let pointer = bytes.stored_pointer(0)?;
                let ConstTarget::Static(def) = pointer.kind() else { return None };
                Some((def.ty(), pointer.key()?))
            })
            .collect();
        let [(static_ty, key)] = statics.as_slice() else {
            panic!("expected exactly the CELL static, found {statics:?}");
        };
        let (bytes, _) = const_pointer::target_bytes(ctx.tcx, key).unwrap();
        let sort = ChcCtx::translate_ty(*static_ty).unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &body, "deep_array_ptr", ChcConfig::default());
        let decoded = chc
            .read_static_value_by_layout(&bytes, 0, *static_ty, &sort, 0)
            .expect("a primitive array field needs no composite wrapper peeling");
        let fields = chc.static_image_fields(*static_ty, &decoded).unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].1.to_string(), Expr::bitvec_const(7u64, 8).to_string());
        let array = &fields[1].1;
        let index_width = array.sort().array_sort().unwrap().index_sort.bitvec_width().unwrap();
        let first = array.clone().select(Expr::bitvec_const(0u64, index_width));
        let second = array.clone().select(Expr::bitvec_const(1u64, index_width));
        // Check the two logical elements, independently of any trailing
        // allocation padding that the existing raw-array reader can retain.
        let query = format!(
            "(set-logic QF_ABV)\n(assert (not (and (= {first} {}) (= {second} {}))))\n(check-sat)\n",
            Expr::bitvec_const(3u64, 32),
            Expr::bitvec_const(5u64, 32),
        );
        assert_eq!(
            run_z3_on_smt2_with_timeout(&query, z3_test_timeout_secs_or(30)).unwrap(),
            "unsat"
        );
    });
}

/// The erased wrapper retains its enum's tag decoder. Reading the wider
/// bitvector directly would absorb the following nonzero bytes, and would
/// lose sign extension for `Ordering::Less`.
#[test]
fn test_erased_fieldless_enum_reads_its_tag_without_neighbor_bytes() {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget};

    let source = r#"
        use std::cell::UnsafeCell;
        use std::cmp::Ordering;
        #[repr(C)]
        pub struct Image {
            tag: UnsafeCell<UnsafeCell<Ordering>>,
            following: [u8; 3],
        }
        unsafe impl Sync for Image {}
        static LESS: Image = Image {
            tag: UnsafeCell::new(UnsafeCell::new(Ordering::Less)),
            following: [0x12, 0x34, 0x56],
        };
        static EQUAL: Image = Image {
            tag: UnsafeCell::new(UnsafeCell::new(Ordering::Equal)),
            following: [0x23, 0x45, 0x67],
        };
        static GREATER: Image = Image {
            tag: UnsafeCell::new(UnsafeCell::new(Ordering::Greater)),
            following: [0x34, 0x56, 0x78],
        };
        pub fn less_ptr(_: Image) -> *const Image { &LESS }
        pub fn equal_ptr(_: Image) -> *const Image { &EQUAL }
        pub fn greater_ptr(_: Image) -> *const Image { &GREATER }
    "#;
    with_test_ay_ctx_for_source(source, |ctx| {
        for (name, expected) in [("less_ptr", u32::MAX), ("equal_ptr", 0), ("greater_ptr", 1)] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let constants = const_pointer::body_constants_read(&body, &[], &|_| false);
            let statics: Vec<_> = constants
                .iter()
                .filter_map(|(bytes, _)| {
                    let pointer = bytes.stored_pointer(0)?;
                    let ConstTarget::Static(def) = pointer.kind() else { return None };
                    Some((def.ty(), pointer.key()?))
                })
                .collect();
            let [(static_ty, key)] = statics.as_slice() else {
                panic!("expected one static for {name}, found {statics:?}");
            };
            assert_eq!(crate::kani_middle::abi::LayoutOf::new(*static_ty).field_offset(1), Some(1));
            let (bytes, _) = const_pointer::target_bytes(ctx.tcx, key).unwrap();
            let sort = ChcCtx::translate_ty(*static_ty).unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let value = chc.read_static_value_by_layout(&bytes, 0, *static_ty, &sort, 0).unwrap();
            let fields = chc.static_image_fields(*static_ty, &value).unwrap();
            assert_eq!(fields[0].1, Expr::bitvec_const(expected as u64, 32), "{name}");
        }
    });
}

const LIVE_IMAGE_PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use std::sync::atomic::{AtomicU32, Ordering};

    static A_BUG: AtomicU32 = AtomicU32::new(5);
    static A_SAFE: AtomicU32 = AtomicU32::new(5);
    static W_BUG: AtomicU32 = AtomicU32::new(5);
    static W_SAFE: AtomicU32 = AtomicU32::new(5);
    static AS_BUG: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static AS_SAFE: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static AS_SYM: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static CH: [AtomicU32; 2] = [AtomicU32::new(1), AtomicU32::new(2)];
    static COUNTER_BUG: AtomicU32 = AtomicU32::new(10);
    static COUNTER_SAFE: AtomicU32 = AtomicU32::new(10);

    trait Bump {
        fn bump(&self) -> u64;
    }
    impl Bump for AtomicU32 {
        fn bump(&self) -> u64 {
            self.fetch_add(1, Ordering::SeqCst) as u64
        }
    }
    fn bump<T: Bump>(t: &T) -> u64 {
        t.bump()
    }

    pub fn probe_store_as_ptr_bug() {
        A_BUG.store(7, Ordering::SeqCst);
        let p = A_BUG.as_ptr();
        kani::assert(unsafe { *p } == 5, "the initializer read after the store");
    }

    pub fn probe_store_as_ptr_safe() {
        A_SAFE.store(7, Ordering::SeqCst);
        let p = A_SAFE.as_ptr();
        kani::assert(unsafe { *p } == 7, "the stored value read through as_ptr");
    }

    pub fn probe_as_ptr_write_load_bug() {
        unsafe { *W_BUG.as_ptr() = 9 };
        kani::assert(W_BUG.load(Ordering::SeqCst) == 5, "the initializer loaded after the write");
    }

    pub fn probe_as_ptr_write_load_safe() {
        unsafe { *W_SAFE.as_ptr() = 9 };
        kani::assert(W_SAFE.load(Ordering::SeqCst) == 9, "the written value loaded");
    }

    pub fn probe_elem_store_cast_read_bug() {
        AS_BUG[1].store(7, Ordering::SeqCst);
        let p = (&AS_BUG as *const [AtomicU32; 2] as *const u32).wrapping_add(1);
        kani::assert(unsafe { *p } == 2, "the initializer read after the element store");
    }

    pub fn probe_elem_store_cast_read_safe() {
        AS_SAFE[1].store(7, Ordering::SeqCst);
        let p = (&AS_SAFE as *const [AtomicU32; 2] as *const u32).wrapping_add(1);
        kani::assert(unsafe { *p } == 7, "the stored element read through a cast");
    }

    pub fn probe_choice_store_load_bug(c: bool) {
        let r = if c { &CH[0] } else { &CH[1] };
        r.store(7, Ordering::SeqCst);
        kani::assert(c || CH[1].load(Ordering::SeqCst) == 2, "a joined receiver may write CH[1]");
    }

    pub fn probe_trait_bump_as_ptr_bug() {
        bump(&COUNTER_BUG);
        kani::assert(unsafe { *COUNTER_BUG.as_ptr() } == 10, "the initializer after an inlined bump");
    }

    pub fn probe_trait_bump_as_ptr_safe() {
        bump(&COUNTER_SAFE);
        kani::assert(unsafe { *COUNTER_SAFE.as_ptr() } == 11, "the bumped value through as_ptr");
    }

    pub fn probe_symbolic_store_load_bug(i: usize) {
        if i == 1 {
            AS_SYM[i].store(7, Ordering::SeqCst);
            kani::assert(AS_SYM[1].load(Ordering::SeqCst) == 2, "a symbolic store may hit it");
        }
    }
"#;

/// Reasons a placed, exact store must not record.
const UNPLACED: [&str; 3] =
    ["static_store_unrouted", "static_image_unsynced", "static_elem_store_unplaced"];

/// Encode `fn_name`, solve it, and return the verdict with the drop reasons.
fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(LIVE_IMAGE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

fn assert_bug_reached(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "sat",
        "{fn_name}: the assertion over the initializer must be refutable; reasons {reasons:?}"
    );
}

fn assert_safe_exact(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "unsat",
        "{fn_name}: the live value must be read back; reasons {reasons:?}"
    );
    for lost in UNPLACED {
        assert!(!reasons.contains_key(lost), "{fn_name}: the store must be exact, got {reasons:?}");
    }
}

/// The reported row: an atomic store, then a raw read through `as_ptr`.
#[test]
fn test_atomic_store_reaches_the_as_ptr_view() {
    assert_bug_reached("probe_store_as_ptr_bug");
}

#[test]
fn test_atomic_store_as_ptr_view_safe_twin_proves_exactly() {
    assert_safe_exact("probe_store_as_ptr_safe");
}

/// A raw write through `as_ptr`, then `load`: the `AtomicU32` view of the
/// image was the stale one.
#[test]
fn test_as_ptr_write_reaches_the_atomic_view() {
    assert_bug_reached("probe_as_ptr_write_load_bug");
}

#[test]
fn test_as_ptr_write_atomic_view_safe_twin_proves_exactly() {
    assert_safe_exact("probe_as_ptr_write_load_safe");
}

/// `AS[1].store(7)`: the receiver's translated address is `_3 + 4` with `_3`
/// a relation variable, so only its MIR names the static
/// (`static_of_pointer_operand`).
#[test]
fn test_atomic_element_store_reaches_a_cast_read() {
    assert_bug_reached("probe_elem_store_cast_read_bug");
}

#[test]
fn test_atomic_element_store_cast_read_safe_twin_proves_exactly() {
    assert_safe_exact("probe_elem_store_cast_read_safe");
}

/// A closed symbolic index updates only the addressed cell and its image.
/// The stale-initializer assertion must still be refuted.
#[test]
fn test_symbolic_atomic_store_updates_the_static() {
    let (verdict, reasons) = solve_probe("probe_symbolic_store_load_bug");
    assert_eq!(verdict, "sat", "a store at AS_SYM[i] may write AS_SYM[1]; reasons {reasons:?}");
    assert!(
        !reasons.contains_key("static_store_unrouted"),
        "closed array address producers must update the static exactly: {reasons:?}"
    );
}

/// `r = if c { &CH[0] } else { &CH[1] }`: both producers establish storage
/// addresses. The runtime reference chooses the cell; no arm is selected by
/// the producer scan. Unknown producers retain separate havoc controls.
#[test]
fn test_joined_receiver_store_updates_the_static() {
    let (verdict, reasons) = solve_probe("probe_choice_store_load_bug");
    assert_eq!(verdict, "sat", "the joined receiver may write CH[1]; reasons {reasons:?}");
    assert!(
        !reasons.contains_key("static_store_unrouted"),
        "closed array address producers must update the static exactly: {reasons:?}"
    );
}

/// A trait method inlined by the walker: its atomic model wrote the
/// `AtomicU32` cell only, and the `u32` view `as_ptr` reads kept 10.
#[test]
fn test_inlined_atomic_store_reaches_the_as_ptr_view() {
    assert_bug_reached("probe_trait_bump_as_ptr_bug");
}

/// The walker's store havocs the static and writes the stored value's own
/// views back, so the read through `as_ptr` is the bumped value.
#[test]
fn test_inlined_atomic_store_as_ptr_view_safe_twin_proves() {
    let (verdict, reasons) = solve_probe("probe_trait_bump_as_ptr_safe");
    assert_eq!(verdict, "unsat", "the bumped value must be read back; reasons {reasons:?}");
    assert!(!reasons.contains_key("static_image_unsynced"), "the image is written: {reasons:?}");
}

/// Erased wrappers retain their declared storage aliases through canonical
/// memory keys. Normalized decomposition selects the real payload constructor
/// exactly once, and actual initializer entries preserve each alias's value.
#[test]
fn transparent_static_image_wrappers_share_the_payloads_typed_field_views() {
    use crate::codegen_ay::chc::decl::global_objects::object_base_for;
    use crate::codegen_ay::provenance::{Loc, Val};
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::cell::UnsafeCell;
        pub struct Payload { word: u32 }
        pub struct Pair { first: u32, second: u32 }
        pub fn probe_image_views(cell: UnsafeCell<Payload>, payload: Payload, scalar: u32, pair: Pair, nested: UnsafeCell<UnsafeCell<Payload>>) {}
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_image_views").body().unwrap();
        let (cell, payload, scalar, pair, nested) = (
            body.locals()[1].ty,
            body.locals()[2].ty,
            body.locals()[3].ty,
            body.locals()[4].ty,
            body.locals()[5].ty,
        );
        let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_image_views", ChcConfig::default());
        let sort = ChcCtx::translate_ty(payload).expect("payload datatype");
        assert!(sort.is_datatype());
        assert_eq!(ChcCtx::translate_ty(cell), Some(sort.clone()));
        let value = Expr::var("image_payload", sort.clone());
        let payload_views = chc.static_image_field_views(payload, &sort).expect("payload views");
        assert_eq!(payload_views, vec![(scalar, ay_bindings::Sort::bitvec(32), 0)]);
        let payload_fields = chc.static_image_fields(payload, &value).expect("payload fields");
        assert_eq!(payload_fields.len(), 1);
        assert_eq!((payload_fields[0].0, payload_fields[0].2), (scalar, 0));
        assert_eq!(payload_fields[0].1.sort(), &ay_bindings::Sort::bitvec(32));
        assert_ne!(
            payload_fields[0].1.to_string(),
            value.to_string(),
            "datatype selector is retained"
        );
        let datatype = sort.datatype_sort().expect("the real payload constructor");
        let [constructor] = datatype.constructors.as_slice() else { panic!("one constructor") };
        let [field] = constructor.fields.as_slice() else { panic!("one scalar field") };
        let scalar_value = value.clone().field_select(&datatype.name, &field.name, field.sort.clone());
        assert_eq!(payload_fields[0].1, scalar_value, "the declared selector is preserved exactly");
        for (wrapper, contents) in [(cell, vec![payload]), (nested, vec![cell, payload])] {
            assert_eq!(ChcCtx::translate_ty(wrapper), Some(sort.clone()));
            let mut current = wrapper;
            for content in contents {
                let TyKind::RigidTy(RigidTy::Adt(def, args)) = current.kind() else {
                    panic!("a declared UnsafeCell storage layer");
                };
                assert_eq!(
                    crate::codegen_ay::shared::mono_ty::single_field_storage_ty(def, &args),
                    Some(content),
                    "each declared storage layer remains in the type model"
                );
                assert_eq!(chc.type_key_for_body_ty(current), chc.type_key_for_body_ty(content));
                assert_eq!(chc.static_image_field_views(current, &sort), Some(payload_views.clone()));
                assert_eq!(chc.static_image_fields(current, &value), Some(payload_fields.clone()));
                assert!(chc.static_image_field_views(current, &ay_bindings::Sort::bitvec(17)).is_none());
                current = content;
            }
            assert_eq!(current, payload);
            let address = object_base_for(42);
            chc.ref_resolution.static_memory_inits.clear();
            chc.register_static_memory_init_entries(
                wrapper, Val::of_value(value.clone()), Loc::of_address(address.clone()), false,
            );
            // Typed memory stores the flattened bits of this one-field
            // datatype, independently of the type key's spelling.
            for alias in [wrapper, cell, payload, scalar] {
                let key = chc.type_key_for_body_ty(alias);
                let entries: Vec<_> = chc.ref_resolution.static_memory_inits.iter()
                    .filter(|(entry_key, ..)| entry_key.as_ref() == key.as_ref()).collect();
                assert!(!entries.is_empty(), "the real image must seed {key}");
                for (_, entry_sort, entry_value, entry_address) in entries {
                    assert_eq!(entry_sort, scalar_value.sort(), "{key}");
                    assert_eq!(entry_value, &scalar_value, "{key}: preserve its actual value");
                    assert_eq!(entry_address, &address, "{key}: preserve the original window");
                }
            }
        }
        let pair_sort = ChcCtx::translate_ty(pair).expect("two-field datatype");
        assert_eq!(chc.static_image_field_views(pair, &pair_sort).unwrap().len(), 2);
        assert!(chc.static_image_field_views(cell, &pair_sort).is_none());
    });
}
