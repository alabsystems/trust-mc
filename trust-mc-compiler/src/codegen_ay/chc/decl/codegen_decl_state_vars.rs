// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! State variable collection from MIR locals.
//! Extracted from codegen_decl.rs (#2246). Part of #2306: proper module migration.
//!
//! Section helpers:
//! - `codegen_decl_state_vars_locals.rs`: Section 1 — scalar local dispatch (Part of #3199, D1)
//! - `codegen_decl_state_vars_arg_pointees.rs`: Section 1.25 — ref pointee state
//! - `codegen_decl_state_vars_collections.rs`: Section 1.5 — collection aux

use ay_bindings::Sort;
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{bv8_sort, ptr_sort};

use super::ChcCtx;
use super::codegen_ctx::CollectionProjectionKind;
use super::codegen_expr_heap::{obj_size_sort, obj_valid_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Collects state variables from MIR locals.
    ///
    /// Translates Rust types to AY sorts for each local variable.
    /// At Ptr/Mem levels, also adds heap state arrays for memory modeling.
    pub(in crate::codegen_ay::chc) fn collect_state_vars(&mut self) {
        // 1. Scalar locals (existing behavior)
        self.collect_state_vars_scalar_locals();

        // 1.25. Auxiliary pointee state variables for &T/&mut T function arguments (#2496).
        self.collect_state_vars_ref_pointees();

        // 1.5. Auxiliary length variables for HashMap/HashSet locals (#1814).
        self.collect_state_vars_collection_aux();

        // 2. Heap metadata arrays — declared at non-int-lift track levels
        // (Part of #869, #890, #2736, #112)
        if !self.int_lift {
            let ov_sort = obj_valid_sort();
            self.push_state_var_pair("obj_valid", "obj_valid__out", ov_sort);

            let os_sort = obj_size_sort();
            self.push_state_var_pair("obj_size", "obj_size__out", os_sort);

            debug!(
                track_level = ?self.track_level,
                "CHC: added object metadata arrays (obj_valid, obj_size)"
            );
        } else {
            debug!(
                track_level = ?self.track_level,
                "CHC int-lift: skipped object metadata arrays (Array sorts block PDR)"
            );
        }

        // 3. Full memory array at Mem level (Part of #869, #890)
        if self.track_level >= ChcTrackLevel::Mem {
            let mem_sort = Sort::array(ptr_sort(), bv8_sort());
            self.push_state_var_pair("mem", "mem__out", mem_sort);

            debug!(
                track_level = ?self.track_level,
                "CHC: added flat memory array (mem)"
            );
        }

        // 4. Scalar shadow-memory state for `-Z uninit-checks` (MEMUB-24/25/27).
        // One nondeterministically tracked byte (obj, off) with its init bit,
        // plus the cross-function argument buffer used by Load/StoreArgument.
        // Only threaded when the uninit instrumentation ran, so relations for
        // ordinary harnesses keep their arity. Requires the split-pointer
        // model, which int-lift disables.
        if self.uninit_checks && !self.int_lift {
            for (in_name, out_name, sort) in
                crate::codegen_ay::chc::shadow_mem_state::SHADOW_MEM_STATE_VARS
            {
                self.push_state_var_pair(*in_name, *out_name, sort());
            }
            debug!("CHC: added shadow-memory init state vars (-Z uninit-checks)");
        }

        // 5. Congruent float-binop tables for symbolic f32/f64 arithmetic
        // (see float_binop_table.rs). Read-only and unconstrained; declared
        // only when the pre-scan finds a float value binop with potentially-
        // symbolic operands, so ordinary harnesses keep their relation arity.
        // Skipped under int-lift (Array sorts block PDR, matching the heap
        // metadata gate above); the float lane then fails closed as before.
        if !self.int_lift {
            self.collect_float_binop_table_state_vars();
        }

        // 6. Frozen congruent call-summary table for ESTABLISHED-pure scalar
        // callees the precise inline lane refused by size (see
        // call_uf_table.rs). Read-only and unconstrained, and declared only
        // when the pre-scan finds such a call, so ordinary harnesses keep
        // their relation arity. Skipped under int-lift for the same reason as
        // the float tables above: Array sorts block PDR there, and the call
        // lane then keeps its pre-existing sound havoc.
        if !self.int_lift {
            self.collect_call_uf_table_state_vars();
        }
    }

    /// Classify a Datatype sort name as a collection/iterator projection kind.
    ///
    /// Returns `Some(kind)` for types that were previously excluded from
    /// flattening by the `is_stub_type` gate (#2241). These types now get
    /// flattened into scalar/array state vars and need bridge logic at stub
    /// call sites (Step 2 of #2874).
    ///
    /// `adt_name` is the MIR type's `trimmed_name()` when available. When
    /// present, classification uses an allow-list of known collection type
    /// names instead of fragile AY sort-name substring matching. The
    /// catch-all heuristic only applies to synthetic sorts without MIR type
    /// info. Part of #3387: structural fix for #3382 recurrence.
    pub(in crate::codegen_ay::chc) fn classify_collection_projection(
        dt_name: &str,
        adt_name: Option<&str>,
    ) -> Option<CollectionProjectionKind> {
        // Phase 1: AY sort-name prefix matching for known collection sorts.
        // These are constructed by codegen with unambiguous prefixes.
        if dt_name.starts_with("VecIntoIter") {
            return Some(CollectionProjectionKind::VecIntoIter);
        }
        if dt_name.starts_with("HashMapIntoIter") {
            return Some(CollectionProjectionKind::HashMapIntoIter);
        }
        if dt_name.starts_with("HashSetIntoIter") {
            return Some(CollectionProjectionKind::HashSetIntoIter);
        }
        if dt_name.starts_with("Vec_") {
            return Some(CollectionProjectionKind::Vec);
        }
        if dt_name.starts_with("SliceIter_") {
            return Some(CollectionProjectionKind::VecIntoIter);
        }

        // Phase 2: When MIR type info is available, use allow-list matching.
        // Only known collection iterator types get classified. All other ADTs
        // (iterator adapters like Enumerate, Zip, Map, Filter, etc.) return
        // None — no deny-list needed. Part of #3387.
        if let Some(name) = adt_name {
            return match name {
                "IntoIter" => {
                    // IntoIter is shared by Vec, HashMap, HashSet, array — disambiguate
                    // via the AY sort name which encodes the source collection.
                    if dt_name.contains("HashMap") {
                        Some(CollectionProjectionKind::HashMapIntoIter)
                    } else if dt_name.contains("HashSet") {
                        Some(CollectionProjectionKind::HashSetIntoIter)
                    } else if dt_name == "IntoIter" || dt_name.contains("PolymorphicIter") {
                        // Part of #3711: array IntoIter wraps PolymorphicIter,
                        // not a Vec carrier. Bare "IntoIter" without collection
                        // prefix is the array variant.
                        Some(CollectionProjectionKind::ArrayIntoIter)
                    } else {
                        Some(CollectionProjectionKind::VecIntoIter)
                    }
                }
                "Iter" | "IterMut" => Some(CollectionProjectionKind::VecIntoIter),
                "Vec" => Some(CollectionProjectionKind::Vec),
                _ => None,
            };
        }

        // Phase 3: Fallback for synthetic sorts without MIR type info.
        // Uses substring heuristic — only reachable for sorts not backed
        // by a MIR ADT (e.g., stubs that construct sorts programmatically).
        if dt_name.contains("IntoIter") || dt_name.contains("Iter_") || dt_name.ends_with("Iter") {
            return Some(CollectionProjectionKind::VecIntoIter);
        }
        None
    }

    /// Classify a single-constructor wrapper datatype as an iterator wrapper projection.
    ///
    /// Returns `IteratorWrapper` when the sort is a single-constructor datatype
    /// whose nested field structure contains a recognized iterator projection sort.
    /// This catches types like `Chars { fld_iter: SliceIter_bv8 }` that are
    /// recursively flattenable but whose top-level name is not in the iterator
    /// allow-list.
    ///
    /// Part of #4114: prevents wrapper iterator locals from falling through to
    /// BV coercion at stub boundaries.
    pub(in crate::codegen_ay::chc) fn classify_wrapper_projection(
        sort: &Sort,
    ) -> Option<CollectionProjectionKind> {
        let dt = sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = &dt.constructors[0];
        // Wrapper types are thin newtypes (1-3 fields). Structs with many
        // fields (e.g. ArraySolver with 7 fields) are user-domain types that
        // happen to contain Vec/iterator fields — not iterator wrappers.
        // Part of #4050: prevents ArraySolver misclassification.
        if ctor.fields.len() > 3 {
            return None;
        }
        // Check if any nested field is a recognized iterator projection sort.
        for field in &ctor.fields {
            if Self::has_nested_iterator_sort(&field.sort) {
                return Some(CollectionProjectionKind::IteratorWrapper);
            }
        }
        None
    }

    /// Check whether a sort is (or transitively contains) a recognized iterator sort.
    fn has_nested_iterator_sort(sort: &Sort) -> bool {
        let Some(dt) = sort.datatype_sort() else {
            return false;
        };
        // Check if this sort itself is a known iterator projection.
        if Self::classify_collection_projection(&dt.name, None).is_some() {
            return true;
        }
        // Recurse into single-constructor fields.
        if dt.constructors.len() == 1 {
            for field in &dt.constructors[0].fields {
                if Self::has_nested_iterator_sort(&field.sort) {
                    return true;
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_array_into_iter_by_sort_name() {
        // Bare "IntoIter" sort name with adt_name="IntoIter" → ArrayIntoIter (not VecIntoIter).
        let result = ChcCtx::classify_collection_projection("IntoIter", Some("IntoIter"));
        assert_eq!(result, Some(CollectionProjectionKind::ArrayIntoIter));
    }

    #[test]
    fn test_classify_array_into_iter_polymorphic() {
        // Sort name containing "PolymorphicIter" → ArrayIntoIter.
        let result =
            ChcCtx::classify_collection_projection("IntoIter_PolymorphicIter_u8", Some("IntoIter"));
        assert_eq!(result, Some(CollectionProjectionKind::ArrayIntoIter));
    }

    #[test]
    fn test_classify_vec_into_iter_with_prefix() {
        // Sort name starting with "VecIntoIter" → VecIntoIter (Phase 1 prefix match).
        let result = ChcCtx::classify_collection_projection("VecIntoIter_u32", Some("IntoIter"));
        assert_eq!(result, Some(CollectionProjectionKind::VecIntoIter));
    }

    #[test]
    fn test_classify_hashmap_into_iter() {
        // Sort name containing "HashMap" with adt_name "IntoIter" → HashMapIntoIter.
        let result =
            ChcCtx::classify_collection_projection("HashMapIntoIter_u32_u64", Some("IntoIter"));
        assert_eq!(result, Some(CollectionProjectionKind::HashMapIntoIter));
    }

    #[test]
    fn test_classify_vec_by_adt_name() {
        let result = ChcCtx::classify_collection_projection("SomeSort", Some("Vec"));
        assert_eq!(result, Some(CollectionProjectionKind::Vec));
    }

    #[test]
    fn test_classify_vec_prefix() {
        // Sort name starting with "Vec_" → Vec (Phase 1 prefix match).
        let result = ChcCtx::classify_collection_projection("Vec_u32", None);
        assert_eq!(result, Some(CollectionProjectionKind::Vec));
    }

    #[test]
    fn test_classify_wrapper_chars_like() {
        // Chars_lt { fld_iter: SliceIter_bv8 { fld_vec: ..., fld_pos: bv64 } }
        // → IteratorWrapper because nested field is SliceIter_* (recognized iterator).
        let slice_iter_sort = Sort::struct_type(
            "SliceIter_bv8",
            [("fld_vec", Sort::bitvec(64)), ("fld_pos", Sort::bitvec(64))],
        );
        let chars_sort = Sort::struct_type("Chars_lt", [("fld_iter", slice_iter_sort)]);
        let result = ChcCtx::classify_wrapper_projection(&chars_sort);
        assert_eq!(result, Some(CollectionProjectionKind::IteratorWrapper));
    }

    #[test]
    fn test_classify_wrapper_non_iterator_struct() {
        // Regular struct with no nested iterator sort → None.
        let plain_struct = Sort::struct_type(
            "MyStruct",
            [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(64))],
        );
        let result = ChcCtx::classify_wrapper_projection(&plain_struct);
        assert_eq!(result, None);
    }

    #[test]
    fn test_classify_wrapper_multi_ctor_not_wrapper() {
        // Multi-constructor enum with an iterator field → None (not single-constructor).
        let slice_iter_sort = Sort::struct_type(
            "SliceIter_bv8",
            [("fld_vec", Sort::bitvec(64)), ("fld_pos", Sort::bitvec(64))],
        );
        let enum_sort = Sort::enum_type(
            "OptionIter",
            vec![("None", vec![]), ("Some", vec![("fld_iter", slice_iter_sort)])],
        );
        let result = ChcCtx::classify_wrapper_projection(&enum_sort);
        assert_eq!(result, None);
    }

    #[test]
    fn test_classify_wrapper_nested_two_levels() {
        // Wrapper around wrapper around SliceIter → IteratorWrapper.
        let slice_iter_sort = Sort::struct_type(
            "SliceIter_bv32",
            [("fld_vec", Sort::bitvec(64)), ("fld_pos", Sort::bitvec(64))],
        );
        let inner_wrapper = Sort::struct_type("InnerWrapper", [("fld_inner", slice_iter_sort)]);
        let outer_wrapper = Sort::struct_type("OuterWrapper", [("fld_wrapped", inner_wrapper)]);
        let result = ChcCtx::classify_wrapper_projection(&outer_wrapper);
        assert_eq!(result, Some(CollectionProjectionKind::IteratorWrapper));
    }
}
