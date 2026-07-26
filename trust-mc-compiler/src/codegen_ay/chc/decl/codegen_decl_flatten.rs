// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Recursive Datatype flattening helpers for CHC state variable collection.
//!
//! Extracted from codegen_decl_state_vars.rs to stay under the 500-line limit.
//! Part of #2989: Recursive Datatype flattening in collect_state_vars.

use ay_bindings::Sort;

/// Maximum recursion depth for recursive Datatype flattening.
/// Prevents infinite recursion on malformed/cyclic Datatype sorts.
const MAX_FLATTEN_DEPTH: usize = 4;

/// Check if a sort can be recursively decomposed into leaf scalar sorts.
///
/// A sort is "recursively flattenable" if it is:
/// - A scalar sort (BV, Bool, Int, Real, Array), OR
/// - A single-constructor Datatype whose fields are all recursively flattenable.
///
/// This generalizes the previous single-level `all_scalar` check to handle
/// nested single-constructor ADTs like `PolymorphicIter(IndexRange, Array)`.
///
/// Part of #2989: Recursive Datatype flattening in collect_state_vars.
pub(in crate::codegen_ay::chc) fn is_recursively_flattenable(sort: &Sort, depth: usize) -> bool {
    if sort.is_bitvec() || sort.is_bool() || sort.is_int() || sort.is_real() || sort.is_array() {
        return true;
    }
    if depth >= MAX_FLATTEN_DEPTH {
        return false;
    }
    if let Some(dt) = sort.datatype_sort() {
        if dt.constructors.len() == 1 {
            let fields = &dt.constructors[0].fields;
            return !fields.is_empty()
                && fields.iter().all(|f| is_recursively_flattenable(&f.sort, depth + 1));
        }
    }
    false
}

/// Recursively collect all leaf scalar sorts from a (possibly nested) Datatype sort.
///
/// For a single-constructor Datatype with nested Datatypes, this recursively
/// extracts the leaf BV/Bool/Int/Real/Array sorts. For non-Datatype sorts,
/// returns the sort itself.
///
/// Part of #2989: Recursive Datatype flattening in collect_state_vars.
pub(in crate::codegen_ay::chc) fn collect_leaf_sorts(sort: &Sort, depth: usize) -> Vec<Sort> {
    if sort.is_bitvec() || sort.is_bool() || sort.is_int() || sort.is_real() || sort.is_array() {
        return vec![sort.clone()];
    }
    if depth >= MAX_FLATTEN_DEPTH {
        return vec![sort.clone()];
    }
    if let Some(dt) = sort.datatype_sort() {
        if dt.constructors.len() == 1 {
            return dt.constructors[0]
                .fields
                .iter()
                .flat_map(|f| collect_leaf_sorts(&f.sort, depth + 1))
                .collect();
        }
    }
    vec![sort.clone()]
}

/// Compute the leaf slot offset for a chain of field projections on a
/// recursively flattened single-constructor Datatype.
///
/// For a type like `Outer { inner: Inner { a: i32, b: i32 }, z: u64 }`
/// flattened to `[bv32, bv32, bv64]`:
/// - `[0, 0]` → `Some(0)`  (inner.a)
/// - `[0, 1]` → `Some(1)`  (inner.b)
/// - `[1]`    → `Some(2)`  (z, a leaf scalar)
///
/// Returns `None` if the projection chain doesn't resolve to a leaf scalar,
/// the sort isn't a single-constructor Datatype, or field indices are out of
/// bounds.
///
/// Part of #2989: Fix multi-level MIR projection on recursively flattened locals.
pub(in crate::codegen_ay::chc) fn compute_nested_flat_slot(
    sort: &Sort,
    field_indices: &[usize],
) -> Option<usize> {
    if field_indices.is_empty() {
        return None;
    }

    let mut offset = 0;
    let mut current_sort = sort.clone();

    for (i, &field_idx) in field_indices.iter().enumerate() {
        let (leaf_offset, target_sort, is_leaf) = {
            let dt = current_sort.datatype_sort()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let fields = &dt.constructors[0].fields;
            if field_idx >= fields.len() {
                return None;
            }

            let mut leaf_offset = 0;
            for f in &fields[..field_idx] {
                leaf_offset += collect_leaf_sorts(&f.sort, 0).len();
            }

            let target = &fields[field_idx].sort;
            let is_leaf = target.is_bitvec()
                || target.is_bool()
                || target.is_int()
                || target.is_real()
                || target.is_array();

            (leaf_offset, target.clone(), is_leaf)
        };

        offset += leaf_offset;

        if i == field_indices.len() - 1 {
            if is_leaf {
                return Some(offset);
            }
            return None;
        }

        current_sort = target_sort;
    }

    None
}

/// Compute the flattened slot span for a field projection chain.
///
/// Returns `(offset, leaf_count)` for the terminal field, even when that field
/// is itself a recursively flattenable Datatype. This is the write-path
/// companion to `compute_nested_flat_slot`, which only succeeds when the final
/// target is already a leaf sort.
pub(in crate::codegen_ay::chc) fn compute_nested_flat_span(
    sort: &Sort,
    field_indices: &[usize],
) -> Option<(usize, usize)> {
    if field_indices.is_empty() {
        return None;
    }

    let mut offset = 0;
    let mut current_sort = sort.clone();

    for (i, &field_idx) in field_indices.iter().enumerate() {
        let (leaf_offset, target_sort) = {
            let dt = current_sort.datatype_sort()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let fields = &dt.constructors[0].fields;
            if field_idx >= fields.len() {
                return None;
            }

            let mut leaf_offset = 0;
            for f in &fields[..field_idx] {
                leaf_offset += collect_leaf_sorts(&f.sort, 0).len();
            }

            (leaf_offset, fields[field_idx].sort.clone())
        };

        offset += leaf_offset;

        if i == field_indices.len() - 1 {
            return Some((offset, collect_leaf_sorts(&target_sort, 0).len()));
        }

        current_sort = target_sort;
    }

    None
}

/// Check if a multi-constructor enum Datatype is BV-flattenable.
///
/// Returns true when all constructors have fields that recursively resolve
/// to BV/Bool/Int scalar sorts. Unit constructors (no fields) are always OK.
///
/// Part of #3215: BV-only enum encoding to bypass Z3 PDR ADT accessor limitation.
pub(in crate::codegen_ay::chc) fn is_multi_ctor_flattenable(
    dt: &ay_bindings::DatatypeSort,
) -> bool {
    if dt.constructors.len() < 2 {
        return false;
    }
    dt.constructors
        .iter()
        .all(|ctor| ctor.fields.iter().all(|f| is_recursively_flattenable(&f.sort, 0)))
}

/// Unified leaf sort result: (ctor_field_slots, ctor_leaf_counts, unified_payload_sorts).
///
/// - `ctor_field_slots[ctor_idx][field_idx]` = payload slot index for that field
/// - `ctor_leaf_counts[ctor_idx]` = number of leaf sorts for that constructor
/// - `unified_payload_sorts` = the unified sort at each payload position
type UnifiedLeafSorts = (Vec<Vec<usize>>, Vec<usize>, Vec<Sort>);

/// Compute unified leaf sorts across all constructors of a multi-constructor enum.
///
/// Returns `None` if sorts are incompatible at any payload position.
///
/// Part of #3215: BV-only enum encoding to bypass Z3 PDR ADT accessor limitation.
pub(in crate::codegen_ay::chc) fn unify_multi_ctor_leaf_sorts(
    dt: &ay_bindings::DatatypeSort,
) -> Option<UnifiedLeafSorts> {
    let mut ctor_field_slots: Vec<Vec<usize>> = Vec::new();
    let mut ctor_leaf_counts: Vec<usize> = Vec::new();
    let mut all_ctor_leaves: Vec<Vec<Sort>> = Vec::new();

    for ctor in &dt.constructors {
        let mut field_slots = Vec::new();
        let mut ctor_leaves = Vec::new();
        for field in &ctor.fields {
            field_slots.push(ctor_leaves.len());
            let leaves = collect_leaf_sorts(&field.sort, 0);
            ctor_leaves.extend(leaves);
        }
        ctor_leaf_counts.push(ctor_leaves.len());
        ctor_field_slots.push(field_slots);
        all_ctor_leaves.push(ctor_leaves);
    }

    let max_leaves = ctor_leaf_counts.iter().copied().max().unwrap_or(0);

    // Unify: for each position, all constructors that have a sort must agree
    // (with BV width widening: BV32 + BV64 → BV64).
    let mut unified_sorts = Vec::with_capacity(max_leaves);
    for pos in 0..max_leaves {
        let mut sort_at_pos: Option<Sort> = None;
        for ctor_leaves in &all_ctor_leaves {
            if pos < ctor_leaves.len() {
                match &sort_at_pos {
                    None => sort_at_pos = Some(ctor_leaves[pos].clone()),
                    Some(existing) => {
                        if *existing != ctor_leaves[pos] {
                            let unified = unify_bv_sorts(existing, &ctor_leaves[pos])?;
                            sort_at_pos = Some(unified);
                        }
                    }
                }
            }
        }
        unified_sorts.push(sort_at_pos?);
    }

    Some((ctor_field_slots, ctor_leaf_counts, unified_sorts))
}

/// Minimum tag bits for N constructors: 1 for 2, ceil(log2(N)) for N > 2.
pub(in crate::codegen_ay::chc) fn enum_tag_bits(n: usize) -> u32 {
    if n <= 2 { 1 } else { (n as f64).log2().ceil() as u32 }
}

/// Attempt to unify two sorts for the same payload position.
/// BV + BV → wider BV. Bool + BV1 → Bool. Otherwise incompatible.
fn unify_bv_sorts(a: &Sort, b: &Sort) -> Option<Sort> {
    if a.is_bitvec() && b.is_bitvec() {
        let wa = a.bitvec_width()?;
        let wb = b.bitvec_width()?;
        return Some(Sort::bitvec(wa.max(wb)));
    }
    if a.is_bool() && b.is_bool() {
        return Some(Sort::bool());
    }
    if a.is_int() && b.is_int() {
        return Some(Sort::int());
    }
    // Bool ↔ BV1 compatibility
    if (a.is_bool() && b.is_bitvec() && b.bitvec_width() == Some(1))
        || (b.is_bool() && a.is_bitvec() && a.bitvec_width() == Some(1))
    {
        return Some(Sort::bool());
    }
    None
}

/// Convert a byte size to a bitvec width in bits.
///
/// Accepts both `usize` and `u64` callers to match the mixed byte-size APIs
/// exposed by rustc layout helpers while still defending against silent
/// truncation when lowering to a Z3 bit-width.
///
/// Part of #4128: systematic `(byte_size as u32) * 8` truncation risk.
pub(in crate::codegen_ay) fn byte_size_to_bv_width<T>(byte_size: T) -> u32
where
    T: TryInto<u64>,
    T::Error: std::fmt::Debug,
{
    let byte_size: u64 = byte_size.try_into().expect("byte size should fit into u64");
    let bits = byte_size.checked_mul(8).expect("byte_size overflow in bit-width calculation");
    u32::try_from(bits).expect("bit width exceeds u32::MAX")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_dt_sort(name: &str, fields: Vec<(&str, Sort)>) -> Sort {
        Sort::struct_type(
            name,
            fields.into_iter().map(|(n, s)| (n.to_string(), s)).collect::<Vec<_>>(),
        )
    }

    #[test]
    fn test_compute_nested_flat_slot_simple_struct() {
        // Struct { a: bv32, b: bv64 } — flat, single-level
        let sort = make_dt_sort("Simple", vec![("a", Sort::bitvec(32)), ("b", Sort::bitvec(64))]);
        assert_eq!(compute_nested_flat_slot(&sort, &[0]), Some(0)); // a
        assert_eq!(compute_nested_flat_slot(&sort, &[1]), Some(1)); // b
    }

    #[test]
    fn test_compute_nested_flat_slot_nested_struct() {
        // Outer { inner: Inner { a: bv32, b: bv32 }, z: bv64 }
        let inner = make_dt_sort("Inner", vec![("a", Sort::bitvec(32)), ("b", Sort::bitvec(32))]);
        let outer = make_dt_sort("Outer", vec![("inner", inner), ("z", Sort::bitvec(64))]);

        // Outer.inner is not a leaf — should return None
        assert_eq!(compute_nested_flat_slot(&outer, &[0]), None);
        // Outer.inner.a → leaf slot 0
        assert_eq!(compute_nested_flat_slot(&outer, &[0, 0]), Some(0));
        // Outer.inner.b → leaf slot 1
        assert_eq!(compute_nested_flat_slot(&outer, &[0, 1]), Some(1));
        // Outer.z → leaf slot 2
        assert_eq!(compute_nested_flat_slot(&outer, &[1]), Some(2));
    }

    #[test]
    fn test_compute_nested_flat_span_nested_struct() {
        let inner = make_dt_sort("Inner", vec![("a", Sort::bitvec(32)), ("b", Sort::bitvec(32))]);
        let outer = make_dt_sort("Outer", vec![("inner", inner), ("z", Sort::bitvec(64))]);

        assert_eq!(compute_nested_flat_span(&outer, &[0]), Some((0, 2)));
        assert_eq!(compute_nested_flat_span(&outer, &[0, 0]), Some((0, 1)));
        assert_eq!(compute_nested_flat_span(&outer, &[0, 1]), Some((1, 1)));
        assert_eq!(compute_nested_flat_span(&outer, &[1]), Some((2, 1)));
    }

    #[test]
    fn test_compute_nested_flat_slot_three_level() {
        // A { b: B { c: C { x: bv8 }, y: bv16 }, z: bv32 }
        let c = make_dt_sort("C", vec![("x", Sort::bitvec(8))]);
        let b = make_dt_sort("B", vec![("c", c), ("y", Sort::bitvec(16))]);
        let a = make_dt_sort("A", vec![("b", b), ("z", Sort::bitvec(32))]);

        assert_eq!(compute_nested_flat_slot(&a, &[0, 0, 0]), Some(0)); // b.c.x
        assert_eq!(compute_nested_flat_slot(&a, &[0, 1]), Some(1)); // b.y
        assert_eq!(compute_nested_flat_slot(&a, &[1]), Some(2)); // z
    }

    #[test]
    fn test_compute_nested_flat_slot_empty_indices() {
        let sort = make_dt_sort("S", vec![("a", Sort::bitvec(32))]);
        assert_eq!(compute_nested_flat_slot(&sort, &[]), None);
    }

    #[test]
    fn test_compute_nested_flat_slot_out_of_bounds() {
        let sort = make_dt_sort("S", vec![("a", Sort::bitvec(32))]);
        assert_eq!(compute_nested_flat_slot(&sort, &[5]), None);
    }
}
