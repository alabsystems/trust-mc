// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Section 1.5: Collection auxiliary state variables.
//!
//! Extracted from `codegen_decl_state_vars.rs` for 500-LOC compliance (Part of #3199, D1).
//! - Section 1.5: Collection auxiliary variables (HashMap/Vec length, capacity, presence).

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::mir::{AggregateKind, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::types::ptr_sort;

use super::ChcCtx;
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Section 1.5: Create auxiliary length/capacity/presence variables for collection locals.
    ///
    /// CHC represents HashMap/Vec as arrays without embedded length, so track length
    /// separately. Part of #1814.
    pub(in crate::codegen_ay::chc) fn collect_state_vars_collection_aux(&mut self) {
        for (local_idx, local_decl) in self.body.local_decls() {
            if let Some((collection_kind, _)) = Self::detect_collection_type(local_decl.ty) {
                let len_var_name = crate::codegen_ay::names::collection_len_var_name(
                    collection_kind,
                    &self.fn_name,
                    local_idx,
                );
                let len_out_name = crate::codegen_ay::names::out_name(&len_var_name);

                let len_sort = ptr_sort();

                debug!(
                    local_idx,
                    len_var = %len_var_name,
                    kind = %collection_kind,
                    "CHC: added collection length state variable"
                );

                self.push_state_var_pair_arc(
                    std::sync::Arc::clone(&len_var_name),
                    &len_out_name,
                    len_sort,
                );

                self.collections.len_state.len_var_names.insert(local_idx, len_var_name);

                // Vec locals also get a capacity state variable (#2877).
                if collection_kind == "vec" {
                    let cap_var_name = crate::codegen_ay::names::collection_cap_var_name(
                        collection_kind,
                        &self.fn_name,
                        local_idx,
                    );
                    let cap_out_name = crate::codegen_ay::names::out_name(&cap_var_name);
                    let cap_sort = ptr_sort();

                    debug!(
                        local_idx,
                        cap_var = %cap_var_name,
                        "CHC: added Vec capacity state variable (#2877)"
                    );

                    self.push_state_var_pair_arc(
                        std::sync::Arc::clone(&cap_var_name),
                        &cap_out_name,
                        cap_sort,
                    );
                    self.collections.len_state.cap_var_names.insert(local_idx, cap_var_name);
                }

                // HashMap/BTreeMap/TrustMcMap locals get a presence-array state variable (#3057).
                if collection_kind == "hashmap"
                    || collection_kind == "btreemap"
                    || collection_kind == "trust_mcmap"
                {
                    // Part of #3348: Extract key sort from MIR type's generic arguments,
                    // not from the state var sort. For reference-typed locals (&mut BTreeMap),
                    // the state var sort is BV64 (pointer), not Array(K,V), causing the old
                    // fallback to ptr_sort() and a key sort mismatch between data and presence
                    // arrays. Unwrap references first, then extract from the ADT generics.
                    let key_sort = {
                        let mut ty = local_decl.ty;
                        // Peel references to reach the underlying map type.
                        while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
                            ty = inner;
                        }
                        Self::extract_hashmap_sorts(ty)
                            .map(|(ks, _)| ks)
                            .or_else(|| {
                                // Fallback: try state var sort (works for non-flattened map locals).
                                self.try_state_idx_for_local(local_idx)
                                    .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                                    .and_then(|(_, sort)| {
                                        sort.array_sort().map(|arr| arr.index_sort.clone())
                                    })
                            })
                            .unwrap_or_else(ptr_sort)
                    };

                    let present_var_name = crate::codegen_ay::names::collection_present_var_name(
                        collection_kind,
                        &self.fn_name,
                        local_idx,
                    );
                    let present_out_name = crate::codegen_ay::names::out_name(&present_var_name);
                    let present_sort = Sort::array(key_sort, Sort::bool());

                    debug!(
                        local_idx,
                        present_var = %present_var_name,
                        "CHC: added HashMap presence-array state variable (#3057)"
                    );

                    self.push_state_var_pair_arc(
                        std::sync::Arc::clone(&present_var_name),
                        &present_out_name,
                        present_sort,
                    );
                    self.collections
                        .len_state
                        .present_var_names
                        .insert(local_idx, present_var_name);
                }
            }
        }

        // Part of #4050: Declare shadow auxiliary state variables for ArraySolver locals.
        // The shadow state (assign_present, assign_value, scope_snap_present, scope_snap_value)
        // enables the pre-inline ArraySolver method dispatcher to replace loop-based methods
        // (get_assignment, pop, record_assignment) with single SMT array operations.
        self.declare_array_solver_aux_vars();

        // Part of #3348: Pre-register presence/len/cap aliases for struct locals
        // that embed collection fields via ADT Aggregate construction. Without this
        // pre-scan, the alias is only set during codegen of the Aggregate statement,
        // which may be too late if a later block (e.g., get() call) is processed
        // before the Aggregate's block.
        self.pre_register_aggregate_collection_aliases();

        // Part of #3348: Pre-declare present/len for struct locals returned from
        // constructor calls (e.g., `let s = MyStruct::new(default)`). The aggregate
        // lives in the callee body — the caller only sees a Call terminator — so the
        // aggregate-based alias scan above misses them.
        self.predeclare_struct_constructor_collection_aux();
    }

    /// Scan all blocks for ADT Aggregate statements and register presence/len/cap
    /// aliases from collection operands to struct destination locals.
    ///
    /// Part of #3348: This runs during declaration phase (before block codegen) so
    /// that `get_hashmap_present_arg` can resolve presence through struct locals
    /// regardless of block processing order.
    fn pre_register_aggregate_collection_aliases(&mut self) {
        // Fixed-point loop: propagate aliases through ADT Aggregates and Copy/Move
        // until no new aliases are discovered. Handles chains like:
        //   BTreeMap local _22 → Aggregate → struct _6 → Move → struct _7
        // In practice, 2-3 iterations suffice (chain depth ≤ 3).
        for _round in 0..5 {
            let before = self.collections.len_state.present_var_names.len()
                + self.collections.len_state.len_var_names.len()
                + self.collections.len_state.cap_var_names.len();

            self.propagate_aliases_one_round();

            let after = self.collections.len_state.present_var_names.len()
                + self.collections.len_state.len_var_names.len()
                + self.collections.len_state.cap_var_names.len();
            if after == before {
                break;
            }
        }
    }

    /// One round of alias propagation through ADT Aggregates, Copy/Move/Ref, and Clone.
    fn propagate_aliases_one_round(&mut self) {
        self.propagate_aliases_from_statements();
        self.propagate_aliases_from_clone_calls();
    }

    /// Propagate collection aliases through ADT Aggregate, Copy/Move, and Ref statements.
    fn propagate_aliases_from_statements(&mut self) {
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                let dest_local = place.local;
                match rvalue {
                    Rvalue::Aggregate(AggregateKind::Adt(_, _, _, _, _), operands) => {
                        for operand in operands {
                            let src_local = match operand {
                                Operand::Copy(p) | Operand::Move(p) => p.local,
                                _ => continue,
                            };
                            self.propagate_collection_aliases(src_local, dest_local);
                        }
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                        self.propagate_collection_aliases(src.local, dest_local);
                    }
                    // Part of #3348: `_9 = &_7` or `_9 = &_7.stores` propagates
                    // aliases from the referent to the reference local.
                    Rvalue::Ref(_, _, src) => {
                        self.propagate_collection_aliases(src.local, dest_local);
                    }
                    _ => {}
                }
            }
        }
    }

    /// Part of #3348: Propagate collection aliases through Clone::clone call terminators.
    ///
    /// When `_39 = Clone::clone(&_36)` is called, resolves the ref chain from _36
    /// to the underlying struct local, then propagates aux vars to the clone
    /// destination. Without this, clone destinations get fresh unconstrained
    /// present/len vars, breaking read-over-write reasoning for different-key lookups.
    fn propagate_aliases_from_clone_calls(&mut self) {
        for block in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            let func_ty = match func.ty(self.body.locals()) {
                Ok(ty) => ty,
                Err(_) => continue,
            };
            let fn_def = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
                _ => continue,
            };
            // Part of #3348: trimmed_name() returns "Clone::clone" (with trait prefix)
            // for derived Clone impls, not bare "clone". Match both forms.
            let trimmed = fn_def.trimmed_name();
            if trimmed != "clone" && trimmed != "Clone::clone" {
                continue;
            }
            let Some(arg0) = args.first() else { continue };
            let ref_local = match arg0 {
                Operand::Copy(p) | Operand::Move(p) => p.local,
                _ => continue,
            };
            let dest_local = destination.local;
            let actual_source = self.resolve_ref_target_from_mir(ref_local).unwrap_or(ref_local);
            self.propagate_collection_aliases(actual_source, dest_local);
        }
    }

    /// Resolve a local to the ultimate source by following Ref, Copy, and Move
    /// chains in the MIR. E.g., `_36 = Copy(_9), _9 = &_7` resolves to `_7`.
    /// Used during declaration phase before ref_resolution is populated.
    fn resolve_ref_target_from_mir(&self, start_local: usize) -> Option<usize> {
        let mut current = start_local;
        let mut best = None;
        // Follow chains up to 5 deep to avoid infinite loops.
        for _ in 0..5 {
            let mut found_next = false;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                        continue;
                    };
                    if place.local != current || !place.projection.is_empty() {
                        continue;
                    }
                    match rvalue {
                        // Part of #3348: Allow Ref targets with projections.
                        // `_9 = &_7.stores` has target.local = 7 — use the base
                        // local so the chain resolves through projected refs.
                        Rvalue::Ref(_, _, target) => {
                            best = Some(target.local);
                            current = target.local;
                            found_next = true;
                        }
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.projection.is_empty() =>
                        {
                            best = Some(p.local);
                            current = p.local;
                            found_next = true;
                        }
                        _ => {}
                    }
                    if found_next {
                        break;
                    }
                }
                if found_next {
                    break;
                }
            }
            if !found_next {
                break;
            }
        }
        best
    }

    /// Propagate presence/len/cap aliases from src_local to dest_local (Part of #3348).
    fn propagate_collection_aliases(&mut self, src_local: usize, dest_local: usize) {
        if let Some(pvar) = self.collections.len_state.get_present_var(src_local).cloned() {
            if self.collections.len_state.get_present_var(dest_local).is_none() {
                self.collections.len_state.present_var_names.insert(dest_local, pvar.clone());
                debug!(dest_local, src_local, %pvar, "alias propagation (#3348)");
            }
        }
        if let Some(lvar) = self.collections.len_state.get_len_var(src_local).cloned() {
            if self.collections.len_state.get_len_var(dest_local).is_none() {
                self.collections.len_state.len_var_names.insert(dest_local, lvar);
            }
        }
        if let Some(cvar) = self.collections.len_state.get_cap_var(src_local).cloned() {
            if self.collections.len_state.get_cap_var(dest_local).is_none() {
                self.collections.len_state.cap_var_names.insert(dest_local, cvar);
            }
        }
        // Part of #4050: Propagate ArraySolver aux state aliases on Copy/Move.
        // When `_5 = ArraySolver::new()` is moved to `_1 = move _5`, the shadow
        // dispatcher for `new()` initializes `_5`'s aux state. Subsequent method
        // calls on `_1` need to find the same aux state. Aliasing the aux entry
        // ensures the dispatcher's `collections.array_solver_aux.get(&receiver_local)`
        // lookup resolves for the destination local.
        if let Some(src_aux) = self.collections.array_solver_aux.get(&src_local).cloned() {
            self.collections.array_solver_aux.entry(dest_local).or_insert_with(|| {
                debug!(dest_local, src_local, "ArraySolver aux alias propagation (#4050)");
                src_aux
            });
        }
    }

    /// Pre-declare present/len state vars for struct locals returned from constructor
    /// calls whose return type contains an embedded map field.
    ///
    /// Part of #3348: When `let s = MyStruct::new(default)` creates a struct with an
    /// embedded BTreeMap, the caller MIR shows a Call terminator with destination `s`.
    /// The aggregate statement lives in the callee body, so the aggregate-based alias
    /// scan (`pre_register_aggregate_collection_aliases`) cannot detect the embedded
    /// map. Without pre-declaring, the constructor bridge must late-declare present/len
    /// during codegen, but late-declared vars miss the `compute_live_state_indices`
    /// pass and are excluded from relation signatures.
    fn predeclare_struct_constructor_collection_aux(&mut self) {
        let fn_name = self.fn_name.clone();
        for block in &self.body.blocks {
            let TerminatorKind::Call { destination, .. } = &block.terminator.kind else {
                continue;
            };
            let dest_local: usize = destination.local;
            let dest_ty = self.body.locals()[dest_local].ty;
            if Self::type_is_hashmap(&dest_ty) {
                continue; // Bare collections handled by detect_collection_type.
            }
            let (adt_def, adt_args) = match dest_ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) => (def, args),
                _ => continue,
            };
            let variants = adt_def.variants();
            if variants.is_empty() {
                continue;
            }
            let fields = variants[0].fields();
            let map_field =
                fields.iter().find(|f| Self::type_is_hashmap(&f.ty_with_args(&adt_args)));
            let Some(map_field) = map_field else { continue };

            // Extract key sort from the map field's type.
            let key_sort = Self::extract_hashmap_sorts(map_field.ty_with_args(&adt_args))
                .map(|(ks, _)| ks)
                .unwrap_or_else(ptr_sort);
            let present_sort = Sort::array(key_sort, Sort::bool());

            // Always pre-declare a dest-specific present/len pair. This covers:
            // 1. Constructor returns (MyStruct::new()) — the destination has no
            //    alias from aggregate scan, so these become the primary names.
            // 2. Clone/passthrough returns — the alias propagation may have set
            //    the dest's present to the source's name (shared). The clone
            //    dispatcher will later switch to the dest-specific name for
            //    independence. Pre-declaring it ensures it's in the live set.
            let fresh_present: std::sync::Arc<str> =
                std::sync::Arc::from(format!("hashmap_{}_present_{}", fn_name, dest_local));
            let fresh_present_out = crate::codegen_ay::names::out_name(&fresh_present);
            self.push_state_var_pair_arc(
                std::sync::Arc::clone(&fresh_present),
                &fresh_present_out,
                present_sort,
            );
            // Only register the name if the dest doesn't already have one from aliasing.
            if self.collections.len_state.get_present_var(dest_local).is_none() {
                self.collections
                    .len_state
                    .present_var_names
                    .insert(dest_local, fresh_present.clone());
            }

            let fresh_len: std::sync::Arc<str> =
                std::sync::Arc::from(format!("hashmap_{}_len_{}", fn_name, dest_local));
            let fresh_len_out = crate::codegen_ay::names::out_name(&fresh_len);
            self.push_state_var_pair_arc(
                std::sync::Arc::clone(&fresh_len),
                &fresh_len_out,
                ptr_sort(),
            );
            if self.collections.len_state.get_len_var(dest_local).is_none() {
                self.collections.len_state.len_var_names.insert(dest_local, fresh_len.clone());
            }

            debug!(
                dest_local,
                present = %fresh_present,
                "pre-declared struct-embedded map present/len for call dest (#3348)"
            );
        }
    }
}
