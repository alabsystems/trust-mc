// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Datatype sort declaration for CHC encoding.
//!
//! Declares AY Datatype sorts used by state variables and flattened locals.
//! Extracted from codegen_decl.rs per 500-line file size limit.

use std::collections::HashSet;

use ay_bindings::{Sort, SortInner};
use tracing::debug;
use trust_mc_core::chc::VarDecl;
use trust_mc_core::decl::Decl;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Declares datatype sorts (tuples) used by state variables.
    ///
    /// Recursively walks sorts to find nested datatypes (Part of #653).
    pub(in crate::codegen_ay::chc) fn declare_datatype_sorts(&mut self) {
        let mut declared_datatypes: HashSet<String> = HashSet::new();
        let mut datatypes_to_declare: Vec<ay_bindings::DatatypeSort> = Vec::new();

        // Collect all datatypes from all state variable sorts
        for (_, sort) in &self.state_var_mgr.state_vars {
            Self::collect_nested_datatypes(
                sort,
                &mut declared_datatypes,
                &mut datatypes_to_declare,
            );
        }

        // Declare all collected datatypes (consume Vec to avoid deep clones)
        for dt_sort in datatypes_to_declare {
            debug!(name = %dt_sort.name, "declared datatype for CHC");
            self.vc.add_decl(Decl::datatype(dt_sort));
        }
    }

    /// Declares Datatype sorts for locals that were flattened during state var collection.
    ///
    /// Part of #2970: Flattened locals (Vec, Option, structs with all-scalar fields) have
    /// their original Datatype sort eliminated from `state_vars` by `collect_state_vars()`.
    /// When `translate_place` reconstructs a Datatype from flattened fields, it uses
    /// `Expr::datatype_constructor` which requires the sort to be declared. Since
    /// `translate_place` takes `&self`, it cannot call `declare_datatype_sort_if_needed`.
    /// This pre-declaration pass covers the gap.
    pub(in crate::codegen_ay::chc) fn declare_flattened_datatype_sorts(&mut self) {
        let mut declared_datatypes: HashSet<String> = HashSet::new();
        let mut datatypes_to_declare: Vec<ay_bindings::DatatypeSort> = Vec::new();

        // Collect already-declared names to avoid duplicates
        for decl in &self.vc.decls {
            if let Decl::Datatype { datatype } = decl {
                declared_datatypes.insert(datatype.name.clone());
            }
        }

        // Iterate flattened locals and declare the same resolved Datatype sorts
        // used during state-var collection and flattened-root reconstruction.
        let flattened_locals: Vec<usize> =
            self.flatten.flattened_local_field_count.keys().copied().collect();
        for local_idx in flattened_locals {
            if let Some(local_decl) = self.body.locals().get(local_idx) {
                let local_ty = self
                    .resolve_inline_local_ty(self.body, local_idx)
                    .unwrap_or_else(|| self.resolve_body_ty(local_decl.ty));
                let Some(sort) = Self::translate_ty(local_ty) else {
                    continue;
                };
                Self::collect_nested_datatypes(
                    &sort,
                    &mut declared_datatypes,
                    &mut datatypes_to_declare,
                );
            }
        }

        for dt_sort in datatypes_to_declare {
            debug!(
                name = %dt_sort.name,
                "declared flattened-local datatype for CHC (#2970)"
            );
            self.vc.add_decl(Decl::datatype(dt_sort));
        }
    }

    /// Declares datatype sorts referenced only by promoted constant-reference
    /// facts in `const_ref_values`.
    ///
    /// Part of #3930: promoted `&RangeInclusive<u32>` values can be decoded to
    /// datatype expressions for deref/field resolution even when no state var
    /// carries the corresponding datatype sort. Without this pass, emitted SMT
    /// can mention constructors like `RangeInclusive_u32_mk` with no matching
    /// datatype declaration.
    pub(in crate::codegen_ay::chc) fn declare_const_ref_value_datatype_sorts(&mut self) {
        let mut declared_datatypes: HashSet<String> = HashSet::new();
        let mut datatypes_to_declare: Vec<ay_bindings::DatatypeSort> = Vec::new();

        for decl in &self.vc.decls {
            if let Decl::Datatype { datatype } = decl {
                declared_datatypes.insert(datatype.name.clone());
            }
        }

        for expr in self.ref_resolution.const_ref_values.values() {
            Self::collect_nested_datatypes(
                expr.sort(),
                &mut declared_datatypes,
                &mut datatypes_to_declare,
            );
        }

        for dt_sort in datatypes_to_declare {
            debug!(
                name = %dt_sort.name,
                "declared const-ref datatype for CHC (#3930)"
            );
            self.vc.add_decl(Decl::datatype(dt_sort));
        }
    }

    /// Declares datatype sorts referenced by pending fresh vars before they are
    /// drained into `vc.vars()` as SMT `declare-var` commands.
    ///
    /// Part of #3945: inline-call fallback can synthesize fresh vars for
    /// hashbrown internal datatypes (`Bucket`, `RawIter`, `Group`, etc.) that
    /// never appear in state variables, so the regular declaration passes miss
    /// them unless we scan the pending-var sorts directly.
    pub(in crate::codegen_ay::chc) fn declare_pending_var_datatype_sorts(
        &mut self,
        pending_vars: &[VarDecl],
    ) {
        let mut declared_datatypes: HashSet<String> = HashSet::new();
        let mut datatypes_to_declare: Vec<ay_bindings::DatatypeSort> = Vec::new();

        for decl in &self.vc.decls {
            if let Decl::Datatype { datatype } = decl {
                declared_datatypes.insert(datatype.name.clone());
            }
        }

        for var in pending_vars {
            Self::collect_nested_datatypes(
                &var.sort,
                &mut declared_datatypes,
                &mut datatypes_to_declare,
            );
        }

        for dt_sort in datatypes_to_declare {
            debug!(
                name = %dt_sort.name,
                "declared pending-var datatype for CHC (#3945)"
            );
            self.vc.add_decl(Decl::datatype(dt_sort));
        }
    }

    /// Lazily declare a Datatype sort that was discovered during encoding
    /// (e.g., from bare-read Datatype reconstruction of a flattened local).
    ///
    /// Part of #2876: Flattened locals' original Datatype sorts are not
    /// in state variables, so `declare_datatype_sorts()` doesn't discover them.
    /// This method registers them on-demand when reconstruction occurs.
    pub(in crate::codegen_ay::chc) fn declare_datatype_sort_if_needed(&mut self, sort: &Sort) {
        if let Some(dt) = sort.datatype_sort() {
            // Check if already declared by scanning existing decls
            let already_declared = self
                .vc
                .decls
                .iter()
                .any(|d| matches!(d, Decl::Datatype { datatype } if datatype.name == dt.name));
            if !already_declared {
                // Declare field sorts first (dependencies)
                for ctor in &dt.constructors {
                    for field in &ctor.fields {
                        self.declare_datatype_sort_if_needed(&field.sort);
                    }
                }
                self.vc.add_decl(Decl::datatype(dt.clone()));
                debug!(name = %dt.name, "declared deferred datatype for flattened reconstruction");
            }
        }
    }

    /// Recursively collects all datatypes from a sort, including nested ones.
    ///
    /// Handles:
    /// - Direct Datatype sorts
    /// - Array element and index sorts
    /// - Datatype field sorts (nested structs/tuples)
    pub(in crate::codegen_ay::chc) fn collect_nested_datatypes(
        sort: &Sort,
        seen: &mut HashSet<String>,
        collected: &mut Vec<ay_bindings::DatatypeSort>,
    ) {
        match sort.inner() {
            SortInner::Datatype(dt_sort) => {
                // Only process if not already seen
                if seen.insert(dt_sort.name.clone()) {
                    // Recursively collect from field sorts first (dependencies)
                    for constructor in &dt_sort.constructors {
                        for field in &constructor.fields {
                            Self::collect_nested_datatypes(&field.sort, seen, collected);
                        }
                    }
                    // Then add this datatype
                    collected.push(dt_sort.clone());
                }
            }
            SortInner::Array(array_sort) => {
                // Check both element and index sorts for nested datatypes
                Self::collect_nested_datatypes(&array_sort.element_sort, seen, collected);
                Self::collect_nested_datatypes(&array_sort.index_sort, seen, collected);
            }
            // Primitive and theory sorts don't contain nested datatypes
            SortInner::Bool
            | SortInner::BitVec(_)
            | SortInner::Int
            | SortInner::Real
            | SortInner::String
            | SortInner::FloatingPoint(_, _)
            | SortInner::Uninterpreted(_)
            | SortInner::RegLan => {}
            _ => {}
        }
    }
}
