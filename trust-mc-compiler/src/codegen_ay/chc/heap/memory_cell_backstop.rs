// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule C's backstop (design trust-mc-reds-final §4.3): a read of a memory cell
//! under a key no store wrote it under is a booked havoc.
//!
//! Typed memory is one array per type key. A value stored under one key and
//! read under another reads a cell nothing wrote: the array's initial state,
//! which the entry rule leaves unconstrained, so the read is an arbitrary
//! value. That is an over-approximation of the real one (a proof stands), but
//! a counterexample through it is not evidence, and before Rule C keyed cells
//! by representation it was certified Genuine (`box_i128_read_safe`,
//! `pair_no_store_safe`: stored under `Box<i128>`, read under `NonNull<i128>`).
//! Rule C removed the splits it knows; this catches the ones it does not, at
//! the cells it can see.
//!
//! After the translation (so every block's stores are in), each type-indexed
//! select at a constant address whose key is absent from the non-empty set of
//! keys stored, or initialized by the entry rule, at that address books the
//! audited sound havoc `memory_cell_unwritten_under_key` with the cell's
//! identity: the scalarized cell (`<array>_at_0x<addr>_bv64`) when
//! scalarization made it a variable, else the array itself (every read of it
//! then counts as tainted). If neither survives in the final rules, the
//! approximation remains unaccounted: a folded-away load must not acquire a
//! phantom identity that certifies an unrelated-looking failing guard.
//!
//! Not covered: a read at a symbolic address, and a cell no store at a
//! constant address wrote under any key (design §10, residual 5).

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::ExprValue;
use trust_mc_core::chc::normalize_approx_var;

use super::ChcCtx;
use super::heap_state::ConstantCellLoad;
use crate::codegen_ay::chc::codegen_ctx::sound_havoc;
use crate::codegen_ay::chc::scalarize_arrays::scalarized_cell_name;
use crate::codegen_ay::types::POINTER_WIDTH;

// A bookkeeping guard, not a solver budget. Exhaustion leaves all affected
// approximations unaccounted; it must never authorize independence.
const IDENTITY_WALK_LIMIT: usize = 100_000;

/// The cells read under a key nothing wrote them under: `(address, array)`
/// for each load whose type key is absent from the keys stored at its address,
/// once per cell, in load order. An address with no recorded store is not
/// judged.
pub(in crate::codegen_ay::chc) fn cells_read_under_unwritten_key(
    stores: &[(u64, Arc<str>)],
    loads: &[ConstantCellLoad],
) -> Vec<(u64, Arc<str>)> {
    let mut written: HashMap<u64, BTreeSet<&str>> = HashMap::new();
    for (addr, key) in stores {
        written.entry(*addr).or_default().insert(key);
    }
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for load in loads {
        let Some(keys) = written.get(&load.addr) else { continue };
        if keys.contains(&*load.type_key) {
            continue;
        }
        if seen.insert((load.addr, Arc::clone(&load.array))) {
            out.push((load.addr, Arc::clone(&load.array)));
        }
    }
    out
}

impl ChcCtx<'_, '_> {
    /// Book every constant-address read of a cell under a key nothing wrote it
    /// under (see the module docs). Runs after scalarization, before the
    /// approximation identities are finalized.
    pub(in crate::codegen_ay::chc) fn book_cells_read_under_unwritten_key(&mut self) {
        let mut stores = self.heap_state.constant_cell_stores.clone();
        stores.extend(self.entry_initialized_constant_cells());
        let unwritten =
            cells_read_under_unwritten_key(&stores, &self.heap_state.constant_cell_loads);
        if unwritten.is_empty() {
            return;
        }
        let declared: HashSet<&str> =
            self.vc.vars().iter().map(|decl| normalize_approx_var(&decl.name)).collect();
        let mut referenced = HashSet::new();
        let mut selected_cells = HashSet::new();
        let mut seen = HashSet::new();
        let mut steps = 0usize;
        let mut complete_walk = true;
        let roots = self.vc.rules.iter().flat_map(|rule| {
            rule.body
                .constraints
                .iter()
                .chain(rule.head.args.iter())
                .chain(rule.body.relation.iter().flat_map(|relation| relation.args.iter()))
        });
        'roots: for root in roots {
            let mut stack = vec![root];
            while let Some(expr) = stack.pop() {
                steps += 1;
                if steps > IDENTITY_WALK_LIMIT {
                    complete_walk = false;
                    break 'roots;
                }
                if !seen.insert(std::ptr::from_ref(expr.value())) {
                    continue;
                }
                if let ExprValue::Var { name } = expr.value() {
                    referenced.insert(normalize_approx_var(name));
                }
                if let ExprValue::Select { array, index } = expr.value()
                    && let Some((obj, offset)) = Self::try_extract_constant_addr(index)
                {
                    let address = (u64::from(obj) << 32) | u64::from(offset);
                    let mut base = Some(array);
                    while let Some(current) = base {
                        steps += 1;
                        if steps > IDENTITY_WALK_LIMIT {
                            complete_walk = false;
                            break 'roots;
                        }
                        match current.value() {
                            ExprValue::Store { array, index, .. } => {
                                // A same-cell or possibly-aliasing write masks
                                // the base cell; it cannot authenticate a lost
                                // earlier read of that cell.
                                let different = Self::try_extract_constant_addr(index).is_some_and(
                                    |(obj, offset)| {
                                        ((u64::from(obj) << 32) | u64::from(offset)) != address
                                    },
                                );
                                base = different.then_some(array);
                            }
                            ExprValue::Var { name } => {
                                selected_cells.insert((address, normalize_approx_var(name)));
                                break;
                            }
                            _ => break,
                        }
                    }
                }
                for child in expr.children() {
                    if stack.len() >= IDENTITY_WALK_LIMIT {
                        complete_walk = false;
                        break 'roots;
                    }
                    stack.push(child);
                }
            }
        }
        let identities: Vec<Option<String>> = unwritten
            .iter()
            .map(|(addr, array)| {
                if !complete_walk {
                    return None;
                }
                let array = normalize_approx_var(array);
                let cell = scalarized_cell_name(array, addr, POINTER_WIDTH);
                if declared.contains(cell.as_str()) && referenced.contains(cell.as_str()) {
                    Some(cell)
                } else if selected_cells.contains(&(*addr, array)) {
                    Some(array.to_string())
                } else {
                    None
                }
            })
            .collect();
        for identity in identities {
            tracing::debug!(
                fn_name = %self.fn_name,
                identity = ?identity,
                "CHC: a cell is read under a type key no store wrote it under (Rule C backstop)"
            );
            match identity {
                Some(identity) => {
                    let _ = self.record_sound_fallback_reason_identified(
                        sound_havoc::MEMORY_CELL_UNWRITTEN_UNDER_KEY.as_str(),
                        Some(&identity),
                    );
                }
                None => {
                    // None in the identified API means *proven dead*. A lost
                    // read has no such proof, so keep this event unaccounted.
                    let _ = self.record_sound_fallback_reason(
                        sound_havoc::MEMORY_CELL_UNWRITTEN_UNDER_KEY.as_str(),
                    );
                }
            }
        }
    }

    /// The constant-address cells the entry rule initializes: static memory
    /// and promoted constants, each under its type key.
    fn entry_initialized_constant_cells(&self) -> Vec<(u64, Arc<str>)> {
        let statics =
            self.ref_resolution.static_memory_inits.iter().filter_map(|(type_key, _, _, addr)| {
                let (obj_id, offset) = Self::try_extract_constant_addr(addr)?;
                Some(((u64::from(obj_id) << 32) | u64::from(offset), Arc::clone(type_key)))
            });
        let promoted = self.ref_resolution.const_ref_memory_inits.iter().map(
            |(type_key, _, _, obj_id, offset)| {
                ((u64::from(*obj_id) << 32) | *offset, Arc::clone(type_key))
            },
        );
        statics.chain(promoted).collect()
    }
}
