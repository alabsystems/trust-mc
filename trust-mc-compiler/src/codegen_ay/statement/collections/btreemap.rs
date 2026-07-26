// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BTreeMap internal operation semantic model for AY codegen.
//!
//! These stubs handle the internal BTreeMap Entry API operations that MIR inlines
//! when BTreeSet operations are used. BTreeSet uses BTreeMap<K, SetValZST> internally,
//! where SetValZST is a zero-sized type representing set membership.
//!
//! Model:
//! - BTreeSet is modeled as Array<Key, Bool> (presence map, same as btreeset.rs)
//! - Entry<K, V> is represented symbolically as it doesn't directly map to SMT
//! - The actual map state is tracked through the Array operations
//!
//! Operations:
//! - `BTreeMap::entry(key)` - Symbolic Entry return, key stored for later operations
//! - `VacantEntry::insert_entry(value)` - Store to array, return reference
//! - `OccupiedEntry::get_mut()` - Select from array, return reference
//! - `OccupiedEntry::into_mut()` - Select from array, return reference
//!
//! Part of #1622: BTree internal operation stubs.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::ptr_sort;
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen BTreeMap internal operations (Part of #1622).
    ///
    /// These operations are triggered when MIR inlines BTreeSet operations to
    /// internal BTreeMap Entry API calls. We model them to work with the
    /// Array<Key, Bool> representation used by BTreeSet stubs.
    pub(in crate::codegen_ay::statement) fn codegen_btreemap_internal_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            BTreeHandleIntoKv, BTreeMapEntry, BTreeMapEntryOrInsert, BTreeMapEntryOrInsertWith,
            BTreeMapEntryOrInsertWithKey, BTreeMapOccupiedGetMut, BTreeMapOccupiedInsert,
            BTreeMapOccupiedIntoMut, BTreeMapVacantInsert, BTreeMapVacantInsertEntry,
            BTreeNodeReborrow, BTreeSearchTree,
        };

        debug!(?stub_kind, %callee_path, "codegen_btreemap_internal_stub");

        match stub_kind {
            // BTreeMap::entry(&mut self, key) -> Entry<K, V>
            // For BTreeSet, this checks if the key exists in the set.
            // We model Entry as a symbolic value and track the key for later use.
            BTreeMapEntry => {
                if args.len() < 2 {
                    warn!("BTreeMap::entry requires 2 args (self, key) — fail-closed (#2497)");
                    return None;
                }

                // Get map base and expression
                let resolved = self.resolve_collection_base(&args[0]);
                let key = self.codegen_operand(&args[1]);

                // Store the map base for later Entry operations
                // We track this in a separate map keyed by the entry's SSA name
                let (Some((base, _map)), Some(k)) = (resolved, key) else {
                    warn!("BTreeMap::entry: cannot resolve map/key — fail-closed (#2497)");
                    return None;
                };

                let entry_base = std::sync::Arc::<str>::from(self.ssa_base_name(destination));
                self.entry_map_bases.insert(std::sync::Arc::clone(&entry_base), base);
                self.entry_keys.insert(entry_base, k);

                // Return a symbolic Entry value so verification can proceed without
                // committing to a specific Occupied/Vacant variant (matches #1624).
                self.codegen_symbolic_result(destination);

                target
            }

            // VacantEntry::insert(self, value) -> &mut V
            // For BTreeSet, this marks the key as present in the set and returns &mut V.
            // Semantically identical to insert_entry for BTreeSet purposes.
            BTreeMapVacantInsert => {
                if args.is_empty() {
                    warn!(
                        "VacantEntry::insert requires at least 1 arg (self) — fail-closed (#2497)"
                    );
                    return None;
                }

                // Get the entry and its associated map/key — fail-closed on any missing link (#2497)
                let eb = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) => self.ssa_base_name(place),
                    _ => {
                        // external enum: Operand
                        warn!("VacantEntry::insert: non-place operand — fail-closed (#2497)");
                        return None;
                    }
                };

                let Some(base) = self.entry_map_bases.get(eb.as_str()).cloned() else {
                    warn!("VacantEntry::insert: no map base for entry — fail-closed (#2497)");
                    return None;
                };
                let Some(k) = self.entry_keys.get(eb.as_str()).cloned() else {
                    warn!("VacantEntry::insert: no key for entry — fail-closed (#2497)");
                    return None;
                };
                let Some(map) = self.env_lookup(base.as_ref()).cloned() else {
                    warn!("VacantEntry::insert: map not in env — fail-closed (#2497)");
                    return None;
                };

                // Insert: set' = store(set, key, true)
                let new_map = map.store(k, Expr::bool_const(true));
                self.env_update(std::sync::Arc::clone(&base), new_map);

                // Return &mut V - for BTreeSet this is &mut ()
                let name = self.ctx.fresh_name("vacant_insert_ref");
                let result = self.ctx.declare_var(&name, ptr_sort());
                let ref_base = self.ssa_base_name(destination);
                self.ref_pointees
                    .insert(std::sync::Arc::from(ref_base), std::sync::Arc::clone(&base));
                self.assign_value_to_place(destination, result);

                target
            }

            // VacantEntry::insert_entry(self, value) -> &mut V
            // For BTreeSet, this marks the key as present in the set.
            // Note: The Rust signature takes (self, value), but for BTreeSet the value
            // is SetValZST (zero-sized type). MIR may optimize away the value argument,
            // so we only require the self argument to be present.
            BTreeMapVacantInsertEntry => {
                if args.is_empty() {
                    warn!(
                        "VacantEntry::insert_entry requires at least 1 arg (self) — fail-closed (#2497)"
                    );
                    return None;
                }

                // Get the entry and its associated map/key — fail-closed on any missing link (#2497)
                let eb = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) => self.ssa_base_name(place),
                    _ => {
                        // external enum: Operand
                        warn!("VacantEntry::insert_entry: non-place operand — fail-closed (#2497)");
                        return None;
                    }
                };

                let Some(base) = self.entry_map_bases.get(eb.as_str()).cloned() else {
                    warn!("VacantEntry::insert_entry: no map base — fail-closed (#2497)");
                    return None;
                };
                let Some(k) = self.entry_keys.get(eb.as_str()).cloned() else {
                    warn!("VacantEntry::insert_entry: no key — fail-closed (#2497)");
                    return None;
                };
                let Some(map) = self.env_lookup(base.as_ref()).cloned() else {
                    warn!("VacantEntry::insert_entry: map not in env — fail-closed (#2497)");
                    return None;
                };

                // Insert: set' = store(set, key, true)
                let new_map = map.store(k.clone(), Expr::bool_const(true));
                self.env_update(std::sync::Arc::clone(&base), new_map);

                // Return OccupiedEntry; model as symbolic entry value
                let dest_base = std::sync::Arc::<str>::from(self.ssa_base_name(destination));
                self.entry_map_bases.insert(std::sync::Arc::clone(&dest_base), base);
                self.entry_keys.insert(dest_base, k);
                self.codegen_symbolic_result(destination);

                target
            }

            // OccupiedEntry::insert(&mut self, value) -> V
            // For BTreeSet, replaces the value (always true) and returns the old value.
            // Since BTreeSet values are Bool, this is essentially a no-op (true -> true).
            BTreeMapOccupiedInsert => {
                if args.is_empty() {
                    warn!(
                        "OccupiedEntry::insert requires at least 1 arg (self) — fail-closed (#2497)"
                    );
                    return None;
                }

                // Get the entry and its associated map/key — fail-closed on any missing link (#2497)
                let eb = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) => self.ssa_base_name(place),
                    _ => {
                        // external enum: Operand
                        warn!("OccupiedEntry::insert: non-place operand — fail-closed (#2497)");
                        return None;
                    }
                };

                let Some(base) = self.entry_map_bases.get(eb.as_str()).cloned() else {
                    warn!("OccupiedEntry::insert: no map base — fail-closed (#2497)");
                    return None;
                };
                let Some(k) = self.entry_keys.get(eb.as_str()).cloned() else {
                    warn!("OccupiedEntry::insert: no key — fail-closed (#2497)");
                    return None;
                };
                let Some(map) = self.env_lookup(base.as_ref()).cloned() else {
                    warn!("OccupiedEntry::insert: map not in env — fail-closed (#2497)");
                    return None;
                };

                // Get old value: select(map, key) - for BTreeSet this is true
                let old_value = map.clone().select(k.clone());

                // Store new value: for BTreeSet, always true
                let new_map = map.store(k, Expr::bool_const(true));
                self.env_update(base, new_map);

                // Return old value (Bool for BTreeSet)
                self.assign_value_to_place(destination, old_value);

                target
            }

            // OccupiedEntry::get_mut(&mut self) -> &mut V
            // For BTreeSet, this returns a reference to the unit value (presence marker).
            BTreeMapOccupiedGetMut => {
                if args.is_empty() {
                    warn!("OccupiedEntry::get_mut requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Get the entry and its associated map/key — fail-closed on any missing link (#2497)
                let eb = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) => self.ssa_base_name(place),
                    _ => {
                        // external enum: Operand
                        warn!("OccupiedEntry::get_mut: non-place operand — fail-closed (#2497)");
                        return None;
                    }
                };

                let Some(base) = self.entry_map_bases.get(eb.as_str()).cloned() else {
                    warn!("OccupiedEntry::get_mut: no map base — fail-closed (#2497)");
                    return None;
                };
                let Some(_k) = self.entry_keys.get(eb.as_str()).cloned() else {
                    warn!("OccupiedEntry::get_mut: no key — fail-closed (#2497)");
                    return None;
                };
                let Some(_map) = self.env_lookup(base.as_ref()).cloned() else {
                    warn!("OccupiedEntry::get_mut: map not in env — fail-closed (#2497)");
                    return None;
                };

                // For BTreeSet (Bool value), return symbolic reference
                // The actual value (true) is already in the map.
                // Note: We don't need to select the value here - the reference
                // returned is to the map entry, and actual reads/writes go
                // through the map's Array model.
                let name = self.ctx.fresh_name("occupied_get_mut_ref");
                let result = self.ctx.declare_var(&name, ptr_sort());

                // Track that this reference points to the map value
                let ref_base = self.ssa_base_name(destination);
                debug!("OccupiedEntry::get_mut: tracking ref_base={}", ref_base);
                self.ref_pointees
                    .insert(std::sync::Arc::from(ref_base), std::sync::Arc::clone(&base));

                self.assign_value_to_place(destination, result);

                target
            }

            // OccupiedEntry::into_mut(self) -> &mut V
            // Same as get_mut but consumes the Entry.
            BTreeMapOccupiedIntoMut => {
                // Delegate to get_mut - same semantics, just consumes self
                self.codegen_btreemap_internal_stub(
                    BTreeMapOccupiedGetMut,
                    args,
                    destination,
                    target,
                    callee_path,
                )
            }

            // Entry::or_insert(self, default) -> &mut V
            // Entry::or_insert_with(self, default) -> &mut V
            // Entry::or_insert_with_key(self, default) -> &mut V
            // For BTreeSet, this marks the key as present and returns &mut V.
            BTreeMapEntryOrInsert | BTreeMapEntryOrInsertWith | BTreeMapEntryOrInsertWithKey => {
                if args.is_empty() {
                    warn!("Entry::or_insert requires at least 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Fail-closed on any missing link (#2497)
                let eb = match &args[0] {
                    Operand::Copy(place) | Operand::Move(place) => self.ssa_base_name(place),
                    _ => {
                        // external enum: Operand
                        warn!("Entry::or_insert: non-place operand — fail-closed (#2497)");
                        return None;
                    }
                };

                let Some(base) = self.entry_map_bases.get(eb.as_str()).cloned() else {
                    warn!("Entry::or_insert: no map base — fail-closed (#2497)");
                    return None;
                };
                let Some(k) = self.entry_keys.get(eb.as_str()).cloned() else {
                    warn!("Entry::or_insert: no key — fail-closed (#2497)");
                    return None;
                };
                let Some(map) = self.env_lookup(base.as_ref()).cloned() else {
                    warn!("Entry::or_insert: map not in env — fail-closed (#2497)");
                    return None;
                };

                let new_map = map.store(k, Expr::bool_const(true));
                self.env_update(std::sync::Arc::clone(&base), new_map);

                let name = self.ctx.fresh_name("entry_or_insert_ref");
                let result = self.ctx.declare_var(&name, ptr_sort());
                let ref_base = self.ssa_base_name(destination);
                self.ref_pointees
                    .insert(std::sync::Arc::from(ref_base), std::sync::Arc::clone(&base));
                self.assign_value_to_place(destination, result);

                target
            }

            // Internal BTree node operations (Part of #1622, #1627)
            // search_tree(key) -> SearchResult (Found/GoDown)
            // For BTreeSet with Array<Key, Bool> model, we return Found if key exists.
            // Internal BTree node operations — not modeled, fail-closed (#2497).
            // These return None to signal untranslatable operations rather than
            // silently producing unconstrained symbolic values.
            BTreeSearchTree | BTreeNodeReborrow | BTreeHandleIntoKv => {
                debug!(
                    ?stub_kind,
                    "BTree internal node operation not modeled — fail-closed (#2497)"
                );
                None
            }

            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // BTreeMap internal variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_btreemap_internal_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }
}
