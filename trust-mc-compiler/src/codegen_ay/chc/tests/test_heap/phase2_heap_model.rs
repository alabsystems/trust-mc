// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =========================================================================
// Phase 2 Abstract Heap Model Unit Tests (#904)
// =========================================================================
//
// Tests for the abstract heap model methods from commit 3ea81359.
// Methods requiring rustc types (Place, Ty) need integration tests.
// These tests verify the pure logic without rustc dependencies.

#[test]
fn test_detect_collection_type_for_std_collections() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

        fn takes_collections(
            hm: HashMap<u8, u16>,
            hs: HashSet<u8>,
            bm: BTreeMap<u8, u16>,
            bs: BTreeSet<u8>,
        ) {
            let _ = (hm, hs, bm, bs);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_collections");
        let args = fn_sig.inputs();

        let hm_ty = args[0];
        let hs_ty = args[1];
        let bm_ty = args[2];
        let bs_ty = args[3];

        let (kind, name) =
            ChcCtx::detect_collection_type(hm_ty).expect("HashMap should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("HashMap"), "unexpected name: {}", name);

        let (kind, name) =
            ChcCtx::detect_collection_type(hs_ty).expect("HashSet should be detected");
        assert_eq!(kind, "hashset");
        assert!(name.ends_with("HashSet"), "unexpected name: {}", name);

        let (kind, name) =
            ChcCtx::detect_collection_type(bm_ty).expect("BTreeMap should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("BTreeMap"), "unexpected name: {}", name);

        let (kind, name) =
            ChcCtx::detect_collection_type(bs_ty).expect("BTreeSet should be detected");
        assert_eq!(kind, "hashset");
        assert!(name.ends_with("BTreeSet"), "unexpected name: {}", name);
    });
}

#[test]
fn test_detect_collection_type_for_trust_mcmap_aliases() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub mod hashmap {
                use std::marker::PhantomData;

                pub struct TrustMcMap<K, V>(PhantomData<(K, V)>);
            }
        }

        use kani::hashmap::TrustMcMap as MyMap;
        type AliasMap<K, V> = kani::hashmap::TrustMcMap<K, V>;

        fn takes_trust_mcmap_aliases(
            direct: MyMap<u8, u16>,
            alias: AliasMap<u32, u64>,
            direct_ref: &MyMap<u8, u16>,
            alias_mut: &mut AliasMap<u32, u64>,
        ) {
            let _ = (direct, alias, direct_ref, alias_mut);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_trust_mcmap_aliases");
        let args = fn_sig.inputs();

        let direct_ty = args[0];
        let alias_ty = args[1];
        let direct_ref_ty = args[2];
        let alias_mut_ty = args[3];

        let (kind, name) =
            ChcCtx::detect_collection_type(direct_ty).expect("TrustMcMap alias should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("TrustMcMap"), "unexpected name: {}", name);
        assert!(
            name.contains("kani::hashmap::TrustMcMap"),
            "expected kani::hashmap path, got: {}",
            name
        );
        let direct_name = name;

        let (kind, name) = ChcCtx::detect_collection_type(alias_ty)
            .expect("TrustMcMap type alias should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("TrustMcMap"), "unexpected name: {}", name);
        assert_eq!(name, direct_name, "alias should resolve to same TrustMcMap def");

        let (kind, name) =
            ChcCtx::detect_collection_type(direct_ref_ty).expect("&TrustMcMap should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("TrustMcMap"), "unexpected name: {}", name);
        assert_eq!(name, direct_name, "ref alias should resolve to same TrustMcMap def");

        let (kind, name) = ChcCtx::detect_collection_type(alias_mut_ty)
            .expect("&mut TrustMcMap should be detected");
        assert_eq!(kind, "hashmap");
        assert!(name.ends_with("TrustMcMap"), "unexpected name: {}", name);
        assert_eq!(name, direct_name, "mut alias should resolve to same TrustMcMap def");
    });
}

#[test]
fn test_detect_collection_type_ignores_non_collections() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        fn takes_non_collections(a: u8, b: &u8, c: Vec<u8>) {
            let _ = (a, b, c);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_non_collections");
        let args = fn_sig.inputs();

        assert!(ChcCtx::detect_collection_type(args[0]).is_none()); // u8
        assert!(ChcCtx::detect_collection_type(args[1]).is_none()); // &u8
        // Vec is now a tracked collection type (Part of #1632)
        let vec_result = ChcCtx::detect_collection_type(args[2]);
        assert!(vec_result.is_some(), "Vec should be detected as a collection");
        assert_eq!(vec_result.unwrap().0, "vec");
    });
}

#[test]
fn test_deref_pointee_ty_for_ref_raw_box_rc_and_arc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::rc::Rc;
        use std::sync::Arc;

        fn takes_ptrs(a: &u8, b: *const u16, c: *mut u32, d: Box<u64>, e: Rc<u128>, f: Arc<usize>) {
            let _ = (a, b, c, d, e, f);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_ptrs");
        let args = fn_sig.inputs();

        let ref_ty = args[0];
        let const_ptr_ty = args[1];
        let mut_ptr_ty = args[2];
        let box_ty = args[3];
        let rc_ty = args[4];
        let arc_ty = args[5];

        let ref_inner = ChcCtx::deref_pointee_ty(ref_ty).expect("ref pointee should resolve");
        assert!(matches!(ref_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))));

        let const_inner =
            ChcCtx::deref_pointee_ty(const_ptr_ty).expect("const ptr pointee should resolve");
        assert!(matches!(const_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U16))));

        let mut_inner =
            ChcCtx::deref_pointee_ty(mut_ptr_ty).expect("mut ptr pointee should resolve");
        assert!(matches!(mut_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U32))));

        let box_inner = ChcCtx::deref_pointee_ty(box_ty).expect("Box pointee should resolve");
        assert!(matches!(box_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U64))));

        let rc_inner = ChcCtx::deref_pointee_ty(rc_ty).expect("Rc pointee should resolve");
        assert!(matches!(rc_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U128))));

        let arc_inner = ChcCtx::deref_pointee_ty(arc_ty).expect("Arc pointee should resolve");
        assert!(matches!(arc_inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))));
    });
}

#[test]
fn test_chc_heap_state_alloc_id_sequence() {
    // (#904, #2958) Verify allocation IDs are assigned sequentially starting from 2
    // (0 = null, 1 = promoted constants, normal allocs start at 2)
    let mut heap = ChcHeapState::new();

    let id1 = heap.next_alloc_id().unwrap();
    let id2 = heap.next_alloc_id().unwrap();
    let id3 = heap.next_alloc_id().unwrap();

    assert_eq!(id1, 2, "First allocation should get ID 2 (0=null, 1=promoted constants)");
    assert_eq!(id2, 3, "Second allocation should get ID 3");
    assert_eq!(id3, 4, "Third allocation should get ID 4");
}

#[test]
fn test_chc_heap_state_type_array_creation() {
    // (#904) Verify type-indexed arrays are created correctly
    let mut heap = ChcHeapState::new();

    let elem_sort = Sort::bitvec(32);
    let (arr_in, arr_out, sort, _) =
        heap.get_or_create_type_array("i32", elem_sort.clone(), "test_fn");

    assert_eq!(&*arr_in, "_test_fn_mem_i32");
    assert_eq!(arr_out, "_test_fn_mem_i32__out");
    assert_eq!(sort, elem_sort);
}

#[test]
fn test_chc_heap_state_type_array_caching() {
    // (#904) Verify type arrays are cached and reused
    let mut heap = ChcHeapState::new();

    let elem_sort = Sort::bitvec(64);
    let (arr_in1, arr_out1, _, _) = heap.get_or_create_type_array("u64", elem_sort.clone(), "fn_a");
    let (arr_in2, arr_out2, _, _) = heap.get_or_create_type_array("u64", elem_sort, "fn_a");

    // Should return same cached array
    assert_eq!(arr_in1, arr_in2, "Same type key should return cached array");
    assert_eq!(arr_out1, arr_out2, "Same type key should return cached output array");
}

#[test]
fn test_chc_heap_state_modified_array_tracking() {
    // (#904) Verify modified array tracking for SSA semantics
    let mut heap = ChcHeapState::new();

    // Initially no arrays are modified
    assert!(!heap.is_array_modified("i32"), "No arrays modified initially");

    // Mark array as modified
    heap.mark_array_modified("i32");
    assert!(heap.is_array_modified("i32"), "i32 should be marked modified");
    assert!(!heap.is_array_modified("u64"), "u64 should NOT be modified");

    // Mark another array
    heap.mark_array_modified("u64");
    assert!(heap.is_array_modified("i32"), "i32 still modified");
    assert!(heap.is_array_modified("u64"), "u64 now modified");

    // Reset at block boundary
    heap.reset_modified_arrays();
    assert!(!heap.is_array_modified("i32"), "i32 reset after block boundary");
    assert!(!heap.is_array_modified("u64"), "u64 reset after block boundary");
}

#[test]
fn test_chc_heap_state_region_array_creation() {
    // (#1443) Verify region arrays are created for heap allocations
    let mut heap = ChcHeapState::new();

    // Allocate first object and assign region
    let obj_id1 = heap.next_alloc_id().unwrap();
    let (region_in1, region_out1) = heap.assign_region_array(obj_id1, Sort::bitvec(8), "fn_test");

    // Verify naming convention
    assert!(region_in1.contains("region_2"), "obj_id=2 (first alloc after null+promoted)");
    assert!(region_out1.contains("__out"));
    assert_eq!(region_out1, format!("{region_in1}__out"));

    // Allocate second object - should get different region
    let obj_id2 = heap.next_alloc_id().unwrap();
    let (region_in2, _) = heap.assign_region_array(obj_id2, Sort::bitvec(32), "fn_test");

    assert_ne!(region_in1, region_in2, "Different allocations should have different regions");
    assert!(region_in2.contains("region_3"), "obj_id=3 (second alloc)");
}

#[test]
fn test_chc_heap_state_region_array_caching() {
    // (#1443) Verify region arrays are cached per obj_id
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();

    // First call creates the region
    let (region_in1, _) = heap.assign_region_array(obj_id, Sort::bitvec(8), "fn_test");

    // Second call should return same region (cached)
    let (region_in2, _) = heap.assign_region_array(obj_id, Sort::bitvec(8), "fn_test");

    assert_eq!(region_in1, region_in2, "Region should be cached per obj_id");
}

#[test]
fn test_chc_heap_state_region_array_type_suffix() {
    // (#1443) Verify region array names include type suffix
    let mut heap = ChcHeapState::new();

    let obj_id1 = heap.next_alloc_id().unwrap();
    let (region_bv8, _) = heap.assign_region_array(obj_id1, Sort::bitvec(8), "fn_test");
    assert!(region_bv8.contains("bv8"), "Region name should include bv8 suffix");

    let obj_id2 = heap.next_alloc_id().unwrap();
    let (region_bv64, _) = heap.assign_region_array(obj_id2, Sort::bitvec(64), "fn_test");
    assert!(region_bv64.contains("bv64"), "Region name should include bv64 suffix");

    let obj_id3 = heap.next_alloc_id().unwrap();
    let (region_int, _) = heap.assign_region_array(obj_id3, Sort::int(), "fn_test");
    assert!(region_int.contains("int"), "Region name should include int suffix");

    // Test Bool sort (#1443 self-audit)
    let obj_id4 = heap.next_alloc_id().unwrap();
    let (region_bool, _) = heap.assign_region_array(obj_id4, Sort::bool(), "fn_test");
    assert!(region_bool.contains("bool"), "Region name should include bool suffix");

    // Test Real sort for BigRational (#911)
    let obj_id5 = heap.next_alloc_id().unwrap();
    let (region_real, _) = heap.assign_region_array(obj_id5, Sort::real(), "fn_test");
    assert!(region_real.contains("real"), "Region name should include real suffix");

    // Test Array sort (#1443 self-audit round 1)
    let obj_id6 = heap.next_alloc_id().unwrap();
    let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let (region_arr, _) = heap.assign_region_array(obj_id6, arr_sort, "fn_test");
    assert!(region_arr.contains("arr"), "Region name should include arr suffix for Array sort");
}

#[test]
fn test_chc_heap_state_get_region_array() {
    // (#1443 self-audit) Verify get_region_array returns assigned region
    let mut heap = ChcHeapState::new();

    let obj_id = heap.next_alloc_id().unwrap();
    let elem_sort = Sort::bitvec(32);

    // Before assignment, get should return None
    assert!(heap.get_region_array(obj_id).is_none(), "Unassigned region should return None");

    // Assign region
    let (expected_in, expected_out) = heap.assign_region_array(obj_id, elem_sort, "fn_test");

    // After assignment, get should return the region
    let result = heap.get_region_array(obj_id);
    assert!(result.is_some(), "Assigned region should be retrievable");

    let (in_name, out_name, sort) = result.unwrap();
    assert_eq!(in_name, expected_in, "Input names should match");
    assert_eq!(out_name, expected_out, "Output names should match");
    assert_eq!(sort.bitvec_width(), Some(32), "Sort should match assigned sort");
}

#[test]
fn test_chc_heap_state_region_array_datatype_suffix() {
    // (#1444) Test datatype/struct sorts for sort_to_type_suffix
    let mut heap = ChcHeapState::new();

    // Test normal struct datatype
    let obj_id1 = heap.next_alloc_id().unwrap();
    let struct_sort =
        struct_sort("MyStruct", [("field1", Sort::bitvec(32)), ("field2", Sort::bool())]);
    let (region_struct, _) = heap.assign_region_array(obj_id1, struct_sort, "fn_test");
    assert!(
        region_struct.contains("MyStruct"),
        "Region name should include datatype name: {region_struct}"
    );

    // Test tuple datatype (uses "TupleN" naming)
    let obj_id2 = heap.next_alloc_id().unwrap();
    let tuple_sort = Sort::tuple(vec![Sort::int(), Sort::bool()]);
    let (region_tuple, _) = heap.assign_region_array(obj_id2, tuple_sort, "fn_test");
    assert!(
        region_tuple.contains("Tuple"),
        "Region name should include Tuple prefix: {region_tuple}"
    );
}
