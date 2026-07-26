// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

#[test]
fn test_hashmap_iter_next_emits_membership_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::HashMap;

        pub fn probe_hashmap_iter_next() {
            let mut map: HashMap<u8, u16> = HashMap::new();
            map.insert(1, 10);
            let mut iter = map.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_next");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_next", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified_locals: HashSet<usize> = HashSet::new();
        let mut found = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_iter_stub(func)
                && stub == StubKind::HashMapIterNext
            {
                let result = chc_ctx
                    .translate_hashmap_iter_call(stub, args, &modified_locals, None)
                    .expect("HashMapIterNext translation");
                let has_membership =
                    result.constraints.iter().any(is_hashmap_iter_membership_constraint);
                assert!(
                    has_membership,
                    "expected membership constraint, got: {:?}",
                    result.constraints
                );
                found = true;
            }
        }

        assert!(found, "HashMapIterNext call not found in MIR");
    });
}

#[test]
fn test_trust_mcmap_iter_stubs_map_to_hashmap_iter_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub mod hashmap {
                use std::marker::PhantomData;

                pub struct TrustMcMap<K, V>(PhantomData<(K, V)>);
                pub struct TrustMcMapIntoIter<K, V>(PhantomData<(K, V)>);

                impl<K, V> TrustMcMap<K, V> {
                    pub fn new() -> Self {
                        Self(PhantomData)
                    }

                    pub fn insert(&mut self, _k: K, _v: V) {}

                    pub fn into_iter(self) -> TrustMcMapIntoIter<K, V> {
                        TrustMcMapIntoIter(PhantomData)
                    }
                }

                impl<K, V> TrustMcMapIntoIter<K, V> {
                    pub fn next(&mut self) -> Option<(K, V)> {
                        None
                    }
                }
            }
        }

        use kani::hashmap::TrustMcMap;

        pub fn probe_trust_mcmap_iter_next() {
            let mut map: TrustMcMap<u8, u16> = TrustMcMap::new();
            map.insert(1, 10);
            let mut iter = map.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_trust_mcmap_iter_next");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_trust_mcmap_iter_next", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut saw_into_iter = false;
        let mut saw_next = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_iter_stub(func)
            {
                if stub == StubKind::HashMapIntoIter {
                    saw_into_iter = true;
                }
                if stub == StubKind::HashMapIterNext {
                    saw_next = true;
                }
            }
        }

        assert!(saw_into_iter, "expected TrustMcMap::into_iter to map to HashMapIntoIter");
        assert!(saw_next, "expected TrustMcMapIntoIter::next to map to HashMapIterNext");
    });
}

#[test]
fn test_hashset_iter_next_emits_membership_constraint() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::HashSet;

        pub fn probe_hashset_iter_next() {
            let mut set: HashSet<u8> = HashSet::new();
            set.insert(1);
            let mut iter = set.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_iter_next");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_iter_next", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified_locals: HashSet<usize> = HashSet::new();
        let mut found = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                && stub == StubKind::HashSetIterNext
            {
                let result = chc_ctx
                    .translate_hashset_call(stub, args, &modified_locals, None)
                    .expect("HashSetIterNext translation");
                let has_membership =
                    result.constraints.iter().any(is_hashset_iter_membership_constraint);
                assert!(
                    has_membership,
                    "expected membership constraint, got: {:?}",
                    result.constraints
                );
                found = true;
            }
        }

        assert!(found, "HashSetIterNext call not found in MIR");
    });
}

// =============================================================================
// HashMap iterator translation — skip path (Part of #2187)
// Exercises ITERATOR_UNSOUND_SKIP_COUNT for HashMap into_iter construction
// (stubs_iterators.rs:551) and HashMapIterNext (stubs_iterators.rs:579).
// =============================================================================

#[test]
fn test_hashmap_into_iter_translation_skip_path() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashmap_skip() {
            let mut m: HashMap<u8, u16> = HashMap::new();
            m.insert(1, 10);
            let mut iter = m.into_iter();
            let _ = iter.next();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_skip");
        let body = instance.body().expect("function body");

        // No declare_block_relations() — forces sort mismatches
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_skip", ChcConfig::default());

        let skip_before = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        let modified_locals: HashSet<usize> = HashSet::new();
        let mut found_skip = false;
        let mut saw_iter_stub_call = false;
        let mut saw_none_result = false;

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_iter_stub(func)
                && matches!(
                    stub,
                    StubKind::HashMapIntoIter
                        | StubKind::HashMapIter
                        | StubKind::HashMapKeys
                        | StubKind::HashMapValues
                        | StubKind::HashMapIterNext
                )
            {
                saw_iter_stub_call = true;
                let result =
                    chc_ctx.translate_hashmap_iter_call(stub, args, &modified_locals, None);
                match result {
                    Some(r) => {
                        let has_false = r
                            .constraints
                            .iter()
                            .any(|c| matches!(c.value(), ExprValue::BoolConst(false)));
                        if has_false {
                            found_skip = true;
                        }
                    }
                    None => saw_none_result = true,
                }
            }
        }

        let skip_after = GLOBAL_COUNTERS.iterator_unsound_skip.load(Ordering::Relaxed);
        assert!(
            saw_iter_stub_call,
            "probe_hashmap_skip should include at least one HashMap iterator stub call"
        );
        assert!(
            found_skip || saw_none_result,
            "HashMap iterator skip-path test expected either false-constraint skip or None result"
        );
        if found_skip {
            assert!(
                skip_after > skip_before,
                "Skip path should have incremented ITERATOR_UNSOUND_SKIP_COUNT"
            );
        }
    });
}

#[test]
fn test_hashmap_iter_sort_structure() {
    // (#1828, #3057) Verify HashMapIntoIter sort has correct DT-free field structure.
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let iter_sort = hashmap_iter_sort(key_sort, value_sort);

    assert!(iter_sort.is_datatype(), "HashMapIntoIter should be a datatype");
    let dt = iter_sort.datatype_sort().unwrap();
    assert_eq!(dt.constructors.len(), 1, "Struct should have one constructor");
    let ctor = &dt.constructors[0];
    assert_eq!(ctor.fields.len(), 5, "Should have 5 fields (data, present, keys, pos, len)");

    let field_names: Vec<&str> = ctor.fields.iter().map(|f| f.name.as_str()).collect();
    assert!(field_names.contains(&"fld_data"), "Should have fld_data field");
    assert!(field_names.contains(&"fld_present"), "Should have fld_present field");
    assert!(field_names.contains(&"fld_keys"), "Should have fld_keys field");
    assert!(field_names.contains(&"fld_pos"), "Should have fld_pos field");
    assert!(field_names.contains(&"fld_len"), "Should have fld_len field");
}

#[test]
fn test_hashmap_iter_data_and_present_sorts() {
    // (#1828, #3057) Verify fld_data is Array<K, V> and fld_present is Array<K, Bool>.
    // DT-free encoding: no Option Datatype in the map array.
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let iter_sort = hashmap_iter_sort(key_sort.clone(), value_sort.clone());

    let dt = iter_sort.datatype_sort().unwrap();
    // Check fld_data: Array<K, V> — direct value sort, no Option wrapper.
    let data_field = dt.constructors[0].fields.iter().find(|f| f.name == "fld_data").unwrap();
    let data_arr = data_field.sort.array_sort();
    assert!(data_arr.is_some(), "fld_data should be an array");
    let data_arr = data_arr.unwrap();
    assert_eq!(data_arr.index_sort, key_sort, "fld_data index should be key sort");
    assert_eq!(
        data_arr.element_sort, value_sort,
        "fld_data element should be value sort directly (DT-free)"
    );

    // Check fld_present: Array<K, Bool> — membership tracking.
    let present_field = dt.constructors[0].fields.iter().find(|f| f.name == "fld_present").unwrap();
    let present_arr = present_field.sort.array_sort();
    assert!(present_arr.is_some(), "fld_present should be an array");
    let present_arr = present_arr.unwrap();
    assert_eq!(present_arr.index_sort, key_sort, "fld_present index should be key sort");
    assert!(present_arr.element_sort.is_bool(), "fld_present element should be Bool");
}

#[test]
fn test_hashmap_iter_keys_sort_is_array() {
    // (#1828) Verify fld_keys is Array<usize, K>
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let iter_sort = hashmap_iter_sort(key_sort.clone(), value_sort);

    let dt = iter_sort.datatype_sort().unwrap();
    let keys_field = dt.constructors[0].fields.iter().find(|f| f.name == "fld_keys").unwrap();
    let arr = keys_field.sort.array_sort();
    assert!(arr.is_some(), "fld_keys should be an array");
    let arr = arr.unwrap();
    assert_eq!(arr.index_sort, Sort::bitvec(64), "Keys index should be usize (bv64)");
    assert_eq!(arr.element_sort, key_sort, "Keys element should be key sort");
}

#[test]
fn test_hashset_iter_sort_structure() {
    // (#1828) Verify HashSetIntoIter sort has correct field structure.
    let key_sort = Sort::bitvec(32);
    let iter_sort = hashset_iter_sort(key_sort.clone());

    assert!(iter_sort.is_datatype(), "HashSetIntoIter should be a datatype");
    let dt = iter_sort.datatype_sort().unwrap();
    assert_eq!(dt.constructors.len(), 1, "Struct should have one constructor");
    let ctor = &dt.constructors[0];
    assert_eq!(ctor.fields.len(), 4, "Should have 4 fields (set, keys, pos, len)");

    let set_field = ctor.fields.iter().find(|f| f.name == "fld_set").unwrap();
    let arr = set_field.sort.array_sort().unwrap();
    assert_eq!(arr.index_sort, key_sort, "Set index should be key sort");
    assert!(arr.element_sort.is_bool(), "Set element should be Bool");
}

#[test]
fn test_option_datatype_has_some_none() {
    // (#1828) Verify Option<V> datatype has correct constructors.
    let value_sort = Sort::bitvec(64);
    let option_sort = option_datatype_sort(value_sort.clone());

    let dt = option_sort.datatype_sort();
    assert!(dt.is_some(), "Option should be a datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 2, "Option should have 2 constructors");

    let none_ctor =
        dt.constructors.iter().find(|c| crate::codegen_ay::names::is_none_constructor(&c.name));
    assert!(none_ctor.is_some(), "Option should have None constructor");
    assert!(none_ctor.unwrap().fields.is_empty(), "None should have no fields");

    let some_ctor =
        dt.constructors.iter().find(|c| crate::codegen_ay::names::is_some_constructor(&c.name));
    assert!(some_ctor.is_some(), "Option should have Some constructor");
    let some_ctor = some_ctor.unwrap();
    assert_eq!(some_ctor.fields.len(), 1, "Some should have 1 field");
    assert_eq!(some_ctor.fields[0].name, "value", "Some field should be named 'value'");

    // (#1828) Self-audit: verify field sort matches input
    assert_eq!(some_ctor.fields[0].sort, value_sort, "Some field sort should match value_sort");
}

#[test]
fn test_tuple_sort_structure() {
    // (#1828) Verify Tuple<K, V> sort for iterator results.
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let tup_sort = tuple_sort(key_sort.clone(), value_sort.clone());

    let dt = tup_sort.datatype_sort();
    assert!(dt.is_some(), "Tuple should be a datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 1, "Tuple should have 1 constructor");
    let ctor = &dt.constructors[0];
    assert_eq!(ctor.fields.len(), 2, "Tuple should have 2 fields");

    let fld_0 = ctor.fields.iter().find(|f| f.name == "fld_0");
    let fld_1 = ctor.fields.iter().find(|f| f.name == "fld_1");
    assert!(fld_0.is_some() && fld_1.is_some(), "Tuple should have fld_0 and fld_1");

    // (#1828) Self-audit: verify field sorts match inputs
    assert_eq!(fld_0.unwrap().sort, key_sort, "fld_0 should have key sort");
    assert_eq!(fld_1.unwrap().sort, value_sort, "fld_1 should have value sort");
}

#[test]
fn test_iterator_position_increment_semantics() {
    // (#1828) Verify iterator position increment: new_pos = old_pos + 1 when in_bounds.
    let pos = Expr::var("pos", Sort::bitvec(64));
    let len = Expr::var("len", Sort::bitvec(64));
    let one = Expr::bitvec_const(1u64, 64);

    let in_bounds = pos.clone().bvult(len);
    assert!(in_bounds.sort().is_bool(), "in_bounds should be Bool");

    let incremented = pos.clone().bvadd(one);
    let new_pos = Expr::ite(in_bounds, incremented, pos);
    assert_eq!(new_pos.sort(), &Sort::bitvec(64), "new_pos should be bv64");
}

#[test]
fn test_iterator_result_option_construction() {
    // (#1828) Verify iterator result: Option<T> = ite(in_bounds, Some(elem), None).
    let elem_sort = Sort::bitvec(32);
    let option_sort = option_datatype_sort(elem_sort.clone());

    let in_bounds = Expr::var("in_bounds", Sort::bool());
    let elem = Expr::var("elem", elem_sort);

    let option_name =
        option_sort.datatype_name().expect("Option datatype name should exist").to_string();
    let some_ctor = crate::codegen_ay::names::option_some_constructor_name(&option_name);
    let none_ctor = crate::codegen_ay::names::option_none_constructor_name(&option_name);
    let some_elem =
        Expr::datatype_constructor(&option_name, some_ctor, vec![elem], option_sort.clone());
    let none_val = Expr::datatype_constructor(&option_name, none_ctor, vec![], option_sort.clone());
    let result = Expr::ite(in_bounds, some_elem, none_val);
    assert_eq!(result.sort(), &option_sort, "Result should be Option type");
}

#[test]
fn test_hashmap_iter_keys_array_element_access() {
    // (#1828) Verify keys[pos] access pattern for iterator.next().
    let key_sort = Sort::bitvec(32);
    let keys_sort = Sort::array(Sort::bitvec(64), key_sort.clone());

    let keys = Expr::var("keys", keys_sort);
    let pos = Expr::var("pos", Sort::bitvec(64));
    let key = keys.select(pos);
    assert_eq!(key.sort(), &key_sort, "keys[pos] should have key sort");
}

#[test]
fn test_hashmap_iter_map_value_lookup() {
    // (#1828) Verify map[key] access pattern for HashMap iterator.
    let key_sort = Sort::bitvec(32);
    let value_sort = Sort::bitvec(64);
    let option_sort = option_datatype_sort(value_sort);
    let map_sort = Sort::array(key_sort.clone(), option_sort.clone());

    let map = Expr::var("map", map_sort);
    let key = Expr::var("key", key_sort);
    let value_opt = map.select(key);
    assert_eq!(value_opt.sort(), &option_sort, "map[key] should have Option<V> sort");
}

#[test]
fn test_hashset_membership_from_set_select() {
    // (#1828) Verify set[key] returns Bool for HashSet membership.
    let key_sort = Sort::bitvec(32);
    let set_sort = Sort::array(key_sort.clone(), Sort::bool());

    let set = Expr::var("set", set_sort);
    let key = Expr::var("key", key_sort);
    let is_member = set.select(key);
    assert!(is_member.sort().is_bool(), "set[key] should be Bool");
}

// =========================================================================
// Entry datatype tests (Part of #1830)
// =========================================================================

#[test]
fn test_entry_sort_has_vacant_and_occupied_variants() {
    // (#1830) Verify Entry enum has Vacant and Occupied variants.
    use crate::codegen_ay::test_fixtures::entry_sort;

    let entry = entry_sort();
    let dt = entry.datatype_sort();
    assert!(dt.is_some(), "Entry should be a datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 2, "Entry should have 2 variants");

    let vacant = dt.constructors.iter().find(|c| c.name == "Vacant");
    let occupied = dt.constructors.iter().find(|c| c.name == "Occupied");
    assert!(vacant.is_some(), "Entry should have Vacant variant");
    assert!(occupied.is_some(), "Entry should have Occupied variant");
}

#[test]
fn test_entry_vacant_contains_vacant_entry_struct() {
    // (#1830) Verify Entry::Vacant contains VacantEntry struct.
    use crate::codegen_ay::test_fixtures::{entry_sort, vacant_entry_sort};

    let entry = entry_sort();
    let dt = entry.datatype_sort().unwrap();
    let vacant = dt.constructors.iter().find(|c| c.name == "Vacant").unwrap();

    assert_eq!(vacant.fields.len(), 1, "Vacant should have 1 field");
    assert_eq!(vacant.fields[0].name, "Vacant_field_0");

    // Verify the field sort matches VacantEntry struct
    let expected_sort = vacant_entry_sort();
    assert_eq!(vacant.fields[0].sort, expected_sort, "Vacant_field_0 should be VacantEntry struct");
}

#[test]
fn test_entry_occupied_contains_occupied_entry_struct() {
    // (#1830) Verify Entry::Occupied contains OccupiedEntry struct.
    use crate::codegen_ay::test_fixtures::{entry_sort, occupied_entry_sort};

    let entry = entry_sort();
    let dt = entry.datatype_sort().unwrap();
    let occupied = dt.constructors.iter().find(|c| c.name == "Occupied").unwrap();

    assert_eq!(occupied.fields.len(), 1, "Occupied should have 1 field");
    assert_eq!(occupied.fields[0].name, "Occupied_field_0");

    // Verify the field sort matches OccupiedEntry struct
    let expected_sort = occupied_entry_sort();
    assert_eq!(
        occupied.fields[0].sort, expected_sort,
        "Occupied_field_0 should be OccupiedEntry struct"
    );
}

#[test]
fn test_vacant_entry_has_key_and_map_fields() {
    // (#1830) Verify VacantEntry struct has fld_key and fld_map fields.
    use crate::codegen_ay::test_fixtures::vacant_entry_sort;

    let vacant = vacant_entry_sort();
    let dt = vacant.datatype_sort();
    assert!(dt.is_some(), "VacantEntry should be a struct/datatype");
    let dt = dt.unwrap();
    assert_eq!(dt.constructors.len(), 1, "VacantEntry should have 1 constructor");

    let ctor = &dt.constructors[0];
    let fld_key = ctor.fields.iter().find(|f| f.name == "fld_key");
    let fld_map = ctor.fields.iter().find(|f| f.name == "fld_map");
    assert!(fld_key.is_some(), "VacantEntry should have fld_key");
    assert!(fld_map.is_some(), "VacantEntry should have fld_map");
}

#[test]
fn test_deref_pointee_ty_rejects_non_box_adts_with_box_in_name() {
    // (#1904) Verify ADTs with "Box" substring in name (but not ending with "::Box")
    // are NOT treated as dereferenceable types.
    //
    // The implementation checks for names ending with "::Box" to match std::boxed::Box.
    // These test cases have "Box" as prefix/middle/substring but not as the final
    // path component, so they should NOT be treated as Box<T>.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        struct BoxedIterator<T> { inner: T }

        struct MyBoxWrapper {
            value: u32,
        }

        struct SandboxConfig {
            enabled: bool,
        }

        fn takes_non_box_adts(
            a: BoxedIterator<u8>,
            b: MyBoxWrapper,
            c: SandboxConfig,
            d: u8,
        ) {
            let _ = (a, b, c, d);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_non_box_adts");
        let args = fn_sig.inputs();

        let boxed_iter_ty = args[0];
        let my_box_ty = args[1];
        let sandbox_ty = args[2];
        let plain_u8_ty = args[3];

        // BoxedIterator<u8> should NOT be treated as Box<T>
        // (has "Box" prefix, but full name doesn't end with "::Box")
        assert!(
            ChcCtx::deref_pointee_ty(boxed_iter_ty).is_none(),
            "BoxedIterator should not be treated as dereferenceable Box"
        );

        // MyBoxWrapper should NOT be treated as Box<T>
        // (has "Box" in middle, but full name doesn't end with "::Box")
        assert!(
            ChcCtx::deref_pointee_ty(my_box_ty).is_none(),
            "MyBoxWrapper should not be treated as dereferenceable Box"
        );

        // SandboxConfig should NOT be treated as Box<T>
        // (has "box" substring, but full name doesn't end with "::Box")
        assert!(
            ChcCtx::deref_pointee_ty(sandbox_ty).is_none(),
            "SandboxConfig should not be treated as dereferenceable Box"
        );

        // Plain u8 should NOT be dereferenceable
        assert!(
            ChcCtx::deref_pointee_ty(plain_u8_ty).is_none(),
            "u8 should not be dereferenceable"
        );
    });
}

#[test]
fn test_detect_collection_type_through_references() {
    // (#1903) Verify detect_collection_type correctly unwraps references.
    //
    // The implementation recurses through Ref types to find the underlying
    // collection. This tests that &HashMap, &mut HashSet, &BTreeMap, and
    // &mut BTreeSet are detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

        fn takes_ref_collections(
            hm_ref: &HashMap<u8, u16>,
            hs_mut: &mut HashSet<u32>,
            bm_ref: &BTreeMap<u8, u16>,
            bs_mut: &mut BTreeSet<u32>,
            nested_ref: &&HashMap<u8, u8>,
        ) {
            let _ = (hm_ref, hs_mut, bm_ref, bs_mut, nested_ref);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_ref_collections");
        let args = fn_sig.inputs();

        let hm_ref_ty = args[0];
        let hs_mut_ty = args[1];
        let bm_ref_ty = args[2];
        let bs_mut_ty = args[3];
        let nested_ref_ty = args[4];

        // &HashMap should detect as hashmap
        let (kind, name) =
            ChcCtx::detect_collection_type(hm_ref_ty).expect("&HashMap should be detected");
        assert_eq!(kind, "hashmap", "&HashMap should be detected as hashmap");
        assert!(name.ends_with("HashMap"), "unexpected name: {}", name);

        // &mut HashSet should detect as hashset
        let (kind, name) =
            ChcCtx::detect_collection_type(hs_mut_ty).expect("&mut HashSet should be detected");
        assert_eq!(kind, "hashset", "&mut HashSet should be detected as hashset");
        assert!(name.ends_with("HashSet"), "unexpected name: {}", name);

        // &BTreeMap should detect as hashmap
        let (kind, name) =
            ChcCtx::detect_collection_type(bm_ref_ty).expect("&BTreeMap should be detected");
        assert_eq!(kind, "hashmap", "&BTreeMap should be detected as hashmap");
        assert!(name.ends_with("BTreeMap"), "unexpected name: {}", name);

        // &mut BTreeSet should detect as hashset
        let (kind, name) =
            ChcCtx::detect_collection_type(bs_mut_ty).expect("&mut BTreeSet should be detected");
        assert_eq!(kind, "hashset", "&mut BTreeSet should be detected as hashset");
        assert!(name.ends_with("BTreeSet"), "unexpected name: {}", name);

        // &&HashMap (double reference) should also detect
        let (kind, name) =
            ChcCtx::detect_collection_type(nested_ref_ty).expect("&&HashMap should be detected");
        assert_eq!(kind, "hashmap", "&&HashMap should be detected as hashmap");
        assert!(name.ends_with("HashMap"), "unexpected name: {}", name);
    });
}

// =========================================================================
// HashMap Type-Based Detection Tests (Part of #1674)
// =========================================================================

#[test]
fn test_detect_collection_type_std_collections() {
    // Verify detect_collection_type correctly identifies std collection types.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};

        fn takes_std_collections(
            hm: HashMap<u8, u16>,
            hs: HashSet<u32>,
            bm: BTreeMap<u8, u16>,
            bs: BTreeSet<u32>,
        ) {
            let _ = (hm, hs, bm, bs);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_std_collections");
        let args = fn_sig.inputs();

        // HashMap -> ("hashmap", ...)
        let (kind, _) =
            ChcCtx::detect_collection_type(args[0]).expect("HashMap should be detected");
        assert_eq!(kind, "hashmap");

        // HashSet -> ("hashset", ...)
        let (kind, _) =
            ChcCtx::detect_collection_type(args[1]).expect("HashSet should be detected");
        assert_eq!(kind, "hashset");

        // BTreeMap -> ("hashmap", ...)
        let (kind, _) =
            ChcCtx::detect_collection_type(args[2]).expect("BTreeMap should be detected");
        assert_eq!(kind, "hashmap");

        // BTreeSet -> ("hashset", ...)
        let (kind, _) =
            ChcCtx::detect_collection_type(args[3]).expect("BTreeSet should be detected");
        assert_eq!(kind, "hashset");
    });
}

#[test]
fn test_detect_collection_type_non_collections_rejected() {
    // Verify non-collection types are not falsely detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn takes_non_collections(a: Vec<u8>, b: String, c: u32, d: bool) {
            let _ = (a, b, c, d);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_non_collections");
        let args = fn_sig.inputs();

        // Vec is now a tracked collection type (Part of #1632)
        let vec_result = ChcCtx::detect_collection_type(args[0]);
        assert!(vec_result.is_some(), "Vec should be detected as a collection");
        assert_eq!(vec_result.unwrap().0, "vec");
        // String is now a tracked collection type (Part of #3684, W4:3781)
        let string_result = ChcCtx::detect_collection_type(args[1]);
        assert!(string_result.is_some(), "String should be detected as a collection");
        assert_eq!(string_result.unwrap().0, "string");
        assert!(
            ChcCtx::detect_collection_type(args[2]).is_none(),
            "u32 should not be detected as a collection"
        );
        assert!(
            ChcCtx::detect_collection_type(args[3]).is_none(),
            "bool should not be detected as a collection"
        );
    });
}

#[test]
fn test_detect_hashmap_stub_phase1_registry_path_match() {
    // Test Phase 1 (registry path-based) HashMap stub detection.
    // Local struct named "HashMap" yields callee paths that contain "HashMap",
    // so stub_registry.lookup (lookup_hashmap_suffix) matches directly.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        impl<K, V> HashMap<K, V> {
            pub fn new() -> Self where K: Default, V: Default {
                HashMap { _k: K::default(), _v: V::default() }
            }
            pub fn insert(&mut self, _k: K, _v: V) {}
            pub fn get(&self, _k: &K) -> Option<&V> { None }
            pub fn len(&self) -> usize { 0 }
            pub fn is_empty(&self) -> bool { true }
            pub fn contains_key(&self, _k: &K) -> bool { false }
        }

        pub fn probe_hashmap_ops() {
            let mut m: HashMap<u8, u16> = HashMap::new();
            m.insert(1, 10);
            let _ = m.get(&1);
            let _ = m.len();
            let _ = m.is_empty();
            let _ = m.contains_key(&1);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_ops");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_ops", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        // Phase 1 (stub_registry) detects HashMap::new via path matching,
        // even though it's a static method with no HashMap-typed arg.
        // Phase 2 alone cannot detect static methods, but Phase 1 handles them.
        assert!(
            detected.contains(&StubKind::HashMapNew),
            "HashMap::new should be detected via Phase 1 registry path match; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapInsert),
            "HashMap::insert should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapGet),
            "HashMap::get should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapLen),
            "HashMap::len should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapIsEmpty),
            "HashMap::is_empty should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapContainsKey),
            "HashMap::contains_key should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_hashmap_stub_type_based_fallback() {
    // Test Phase 2 fallback by calling free functions named like HashMap methods.
    // The callee paths do not contain "HashMap", so Phase 1 registry lookup will not match.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct HashMap<K, V> { _k: K, _v: V }

        pub fn insert<K, V>(_m: &mut HashMap<K, V>, _k: K, _v: V) {}
        pub fn get<'a, K, V>(_m: &'a HashMap<K, V>, _k: &K) -> Option<&'a V> { None }
        pub fn len<K, V>(_m: &HashMap<K, V>) -> usize { 0 }
        pub fn is_empty<K, V>(_m: &HashMap<K, V>) -> bool { true }
        pub fn contains_key<K, V>(_m: &HashMap<K, V>, _k: &K) -> bool { false }

        pub fn probe_hashmap_fallback_ops() {
            let mut m = HashMap { _k: 0u8, _v: 0u16 };
            insert(&mut m, 1, 10);
            let _ = get(&m, &1);
            let _ = len(&m);
            let _ = is_empty(&m);
            let _ = contains_key(&m, &1);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_fallback_ops");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_fallback_ops", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        assert!(
            !detected.contains(&StubKind::HashMapNew),
            "HashMapNew should not be detected without a new/default call; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapInsert),
            "insert(HashMap, ..) should be detected via type-based fallback; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapGet),
            "get(HashMap, ..) should be detected via type-based fallback; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapLen),
            "len(HashMap) should be detected via type-based fallback; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapIsEmpty),
            "is_empty(HashMap) should be detected via type-based fallback; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapContainsKey),
            "contains_key(HashMap, ..) should be detected via type-based fallback; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_hashmap_stub_ignores_non_hashmap_types() {
    // Verify types not named HashMap/BTreeMap/TrustMcMap don't trigger detection.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MyMap<K, V> { _k: K, _v: V }

        impl<K, V> MyMap<K, V> {
            pub fn new() -> Self where K: Default, V: Default {
                MyMap { _k: K::default(), _v: V::default() }
            }
            pub fn insert(&mut self, _k: K, _v: V) {}
        }

        pub fn probe_non_hashmap() {
            let mut m: MyMap<u8, u16> = MyMap::new();
            m.insert(1, 10);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_hashmap");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_hashmap", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        assert!(
            detected.is_empty(),
            "MyMap should not trigger HashMap detection; got: {:?}",
            detected
        );
    });
}

// =============================================================================
// Part of #2255: Hashbrown internal function mapping tests
// =============================================================================

/// Verify that hashbrown::map insert/find_or_find_insert_slot internals map to
/// HashMapInsert when the receiver is a HashMap type.
#[test]
fn test_detect_hashmap_stub_hashbrown_insert_mapping() {
    // We compile real HashMap code — rustc may inline into hashbrown internals.
    // The detect_hashbrown_stub path matches fn_name containing "hashbrown::" plus
    // patterns like "find_or_find_insert_slot", "insert_at_index", etc.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashbrown_insert() {
            let mut m: HashMap<u32, u32> = HashMap::new();
            // Multiple inserts to increase chance of seeing hashbrown internals
            m.insert(1, 10);
            m.insert(2, 20);
            m.insert(3, 30);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashbrown_insert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashbrown_insert", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        // At minimum, HashMap::new + insert×3 should be detected
        // (via either Phase 1 registry or Phase 1.5 hashbrown)
        assert!(
            detected.contains(&StubKind::HashMapNew),
            "HashMap::new should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::HashMapInsert),
            "HashMap::insert (possibly via hashbrown) should be detected; got: {:?}",
            detected
        );
    });
}

/// Verify detect_hashbrown_stub maps hashbrown iter/into_iter patterns to
/// HashMapIntoIter and HashMapIterNext.
#[test]
fn test_detect_hashmap_stub_hashbrown_iter_next_mapping() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::collections::HashMap;

        pub fn probe_hashbrown_iter() {
            let mut m: HashMap<u32, u32> = HashMap::new();
            m.insert(1, 10);
            // into_iter may get inlined to hashbrown iter internals
            for (k, v) in m.into_iter() {
                let _ = k + v;
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashbrown_iter");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashbrown_iter", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        // The into_iter call should be detected (via Phase 1 or Phase 1.5 hashbrown)
        let has_iter_stub = detected.contains(&StubKind::HashMapIntoIter)
            || detected.contains(&StubKind::HashMapIter);
        assert!(
            has_iter_stub,
            "HashMap into_iter should detect IntoIter or Iter stub; got: {:?}",
            detected
        );
    });
}

/// Verify that non-HashMap receivers prevent hashbrown stub detection even when
/// the function name contains hashbrown patterns.
#[test]
fn test_detect_hashmap_stub_hashbrown_rejects_non_receiver() {
    // Use a non-HashMap type that won't have hashbrown internal calls.
    // The detect_hashbrown_stub requires is_hashmap_receiver to return true.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct NotAMap {
            data: Vec<u32>,
        }

        impl NotAMap {
            pub fn new() -> Self { NotAMap { data: Vec::new() } }
            pub fn insert(&mut self, v: u32) { self.data.push(v); }
            pub fn get(&self, idx: usize) -> Option<&u32> { self.data.get(idx) }
        }

        pub fn probe_non_hashmap_receiver() {
            let mut m = NotAMap::new();
            m.insert(42);
            let _ = m.get(0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_hashmap_receiver");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_non_hashmap_receiver", ChcConfig::default());

        let detected = collect_detected_hashmap_stubs(&chc_ctx, &body);

        assert!(
            detected.is_empty(),
            "NotAMap methods should not trigger hashbrown detection; got: {:?}",
            detected
        );
    });
}
