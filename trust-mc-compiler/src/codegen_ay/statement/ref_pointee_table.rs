// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Path-sensitive reference-pointee table for the BMC lane.
//!
//! `ref_pointees` maps a pointer's storage NAME to the storage NAME it points
//! at, and store and read handlers resolve `*p` through it. The map used to be
//! one flow-insensitive table written in block codegen order, so after
//!
//! ```text
//! let p: &mut u32 = if c { &mut b } else { &mut a };
//! *p = 1;
//! ```
//!
//! it named whichever arm was encoded LAST, and `*p = 1` wrote `a` on both
//! paths: `assert!(a == 1)` verified SUCCESSFUL (a false proof), and the safe
//! `if c { b == 1 } else { a == 1 }` failed with a Genuine certificate. A
//! sibling block encoded earlier leaked its entry the same way, and a
//! reassignment the handlers did not track left the previous pointee behind.
//!
//! This table makes the mapping follow the control flow the environment
//! already follows:
//! - every outgoing edge snapshots the table (copy on write), a block with one
//!   predecessor inherits that snapshot, and a join keeps an entry only when
//!   every incoming edge names the same pointee;
//! - an entry the incoming edges disagree on, or that some edge lacks, stays in
//!   place (so the encoding is unchanged) but is POISONED with the per-edge
//!   alternatives `(edge predicate, pointee)`;
//! - a whole-storage reassignment that no handler re-inserted poisons the
//!   entries left over from the previous value (no alternatives: unknown).
//!
//! Reading a poisoned entry through [`RefPointees::get`] or
//! [`RefPointees::range`] (or the corpus tests' `contains_key`) records a hit, and
//! the statement or terminator that read it fails closed
//! (`bmc_ref_pointee_path_ambiguous`, an `unsupported_with_fallback`
//! demotion). A consumer that can use the alternatives precisely asks
//! [`RefPointees::merged_alternatives`], which records no hit.

use std::cell::RefCell;
use std::collections::btree_map;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Deref, RangeFrom};
use std::sync::Arc;

use ay_bindings::Expr;

/// Read-only pointee lookup shared by the production table and the plain maps
/// unit tests build (`StatementCodegen::resolve_ref_chain_target`).
pub(in crate::codegen_ay) trait PointeeLookup {
    fn lookup_pointee(&self, key: &str) -> Option<&Arc<str>>;
}

impl PointeeLookup for BTreeMap<Arc<str>, Arc<str>> {
    fn lookup_pointee(&self, key: &str) -> Option<&Arc<str>> {
        self.get(key)
    }
}

impl PointeeLookup for RefPointees {
    /// Records a hit for a poisoned entry, like [`RefPointees::get`].
    fn lookup_pointee(&self, key: &str) -> Option<&Arc<str>> {
        self.get(key)
    }
}

/// One incoming edge's view of a poisoned entry.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay) struct MergedAlternative {
    /// The edge's path predicate (`None` = unconditional).
    pub(in crate::codegen_ay) edge_predicate: Option<Expr>,
    /// The pointee that edge names, or `None` when the edge carries no entry.
    pub(in crate::codegen_ay) pointee: Option<Arc<str>>,
}

#[derive(Clone, Debug, Default)]
struct Table {
    entries: BTreeMap<Arc<str>, Arc<str>>,
    /// Insertion generation of every entry, for staleness after reassignment.
    generations: BTreeMap<Arc<str>, u64>,
    next_generation: u64,
    /// Entries that do not name one pointee on every path. `Some` carries the
    /// per-edge alternatives of a join; `None` means unknown (stale, or a join
    /// of an already-unknown entry).
    poisoned: BTreeMap<Arc<str>, Option<Vec<MergedAlternative>>>,
}

/// The BMC reference-pointee table. See the module documentation.
pub(in crate::codegen_ay) struct RefPointees {
    table: Arc<Table>,
    /// Poisoned keys read since the last [`RefPointees::take_hits`].
    hits: RefCell<BTreeSet<Arc<str>>>,
}

impl Default for RefPointees {
    fn default() -> Self {
        Self { table: Arc::new(Table::default()), hits: RefCell::new(BTreeSet::new()) }
    }
}

impl Clone for RefPointees {
    /// A snapshot: shares the table until either side writes; pending hits stay
    /// with the original (they belong to the statement that read them).
    fn clone(&self) -> Self {
        Self { table: Arc::clone(&self.table), hits: RefCell::new(BTreeSet::new()) }
    }
}

impl std::fmt::Debug for RefPointees {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RefPointees")
            .field("entries", &self.table.entries)
            .field("poisoned", &self.table.poisoned.keys().collect::<Vec<_>>())
            .finish()
    }
}

/// Read-only map views (`values`, `len`, `is_empty`, `iter`) see every entry,
/// poisoned or not, exactly as the flow-insensitive map did.
impl Deref for RefPointees {
    type Target = BTreeMap<Arc<str>, Arc<str>>;

    fn deref(&self) -> &Self::Target {
        &self.table.entries
    }
}

fn and_predicates(a: &Option<Expr>, b: &Option<Expr>) -> Option<Expr> {
    match (a, b) {
        (None, other) | (other, None) => other.clone(),
        (Some(a), Some(b)) => Some(a.clone().and(b.clone())),
    }
}

impl RefPointees {
    pub(in crate::codegen_ay) fn new() -> Self {
        Self::default()
    }

    fn record_hit(&self, key: &Arc<str>) {
        self.hits.borrow_mut().insert(Arc::clone(key));
    }

    /// The pointee `key` names. A poisoned entry is still returned (the
    /// encoding does not change) but the read is recorded as a hit.
    pub(in crate::codegen_ay) fn get<Q>(&self, key: &Q) -> Option<&Arc<str>>
    where
        Arc<str>: std::borrow::Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some((poisoned_key, _)) = self.table.poisoned.get_key_value(key) {
            self.record_hit(poisoned_key);
        }
        self.table.entries.get(key)
    }

    /// `get(key).is_some()`, recording the same hit. Production code asks
    /// `has_entry`, which records none; only the corpus tests use this.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Arc<str>: std::borrow::Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// Whether `key` has an entry, poisoned or not. Records no hit.
    pub(in crate::codegen_ay) fn has_entry(&self, key: &str) -> bool {
        self.table.entries.contains_key(key)
    }

    /// Bind `key` to the pointee `source` names, carrying `source`'s poison
    /// (its per-edge alternatives, or unknown).
    ///
    /// A copy of a pointer names the same storage on the same paths, and the
    /// copy reads no pointee, so no hit is recorded; a later read through `key`
    /// records one. Copying with `get` + `insert` recorded a hit on the copy
    /// itself, demoting harnesses that only copy a path-merged reference
    /// (`let full = &source[..]; assert!(full.len() == 4)`), and the insert then
    /// cleared the poison on `key`.
    pub(in crate::codegen_ay) fn copy_entry(
        &mut self,
        key: Arc<str>,
        source: &str,
    ) -> Option<Arc<str>> {
        let pointee = self.table.entries.get(source).cloned()?;
        let poison = self.table.poisoned.get(source).cloned();
        let table = Arc::make_mut(&mut self.table);
        table.next_generation += 1;
        table.generations.insert(Arc::clone(&key), table.next_generation);
        match poison {
            Some(poison) => {
                table.poisoned.insert(Arc::clone(&key), poison);
            }
            None => {
                table.poisoned.remove(&key);
            }
        }
        table.entries.insert(key, Arc::clone(&pointee));
        Some(pointee)
    }

    /// The keys of every entry under `prefix` (for example `"f::local_4_"`),
    /// poisoned or not. Records no hit.
    pub(in crate::codegen_ay) fn nested_keys(&self, prefix: &str) -> Vec<Arc<str>> {
        self.table
            .entries
            .range(Arc::<str>::from(prefix)..)
            .take_while(|(key, _)| key.starts_with(prefix))
            .map(|(key, _)| Arc::clone(key))
            .collect()
    }

    /// Prefix scan (`range(prefix..)` followed by `take_while(starts_with)` at
    /// every call site): a poisoned key under the prefix is recorded as a hit.
    pub(in crate::codegen_ay) fn range(
        &self,
        range: RangeFrom<Arc<str>>,
    ) -> btree_map::Range<'_, Arc<str>, Arc<str>> {
        let prefix = Arc::clone(&range.start);
        for (key, _) in self
            .table
            .poisoned
            .range(Arc::clone(&prefix)..)
            .take_while(|(key, _)| key.starts_with(prefix.as_ref()))
        {
            self.record_hit(key);
        }
        self.table.entries.range(range)
    }

    /// Bind `key` to `pointee`: a fresh definition, so any poison is cleared.
    pub(in crate::codegen_ay) fn insert(
        &mut self,
        key: Arc<str>,
        pointee: Arc<str>,
    ) -> Option<Arc<str>> {
        let table = Arc::make_mut(&mut self.table);
        table.next_generation += 1;
        let generation = table.next_generation;
        table.generations.insert(Arc::clone(&key), generation);
        table.poisoned.remove(&key);
        table.entries.insert(key, pointee)
    }

    /// Withdraw the entry named `base` and every entry nested under it
    /// (`base_…`), as a whole-local write to a local with several producers
    /// must (`forget_joined_ref_pointees`): the map is not path-sensitive, so a
    /// surviving entry would name one producer's referent on every path.
    /// Returns how many entries were withdrawn.
    ///
    /// EVERY withdrawn key keeps a poison mark, downgraded to unknown.
    /// Withdrawal must not turn a key the table can no longer answer for into a
    /// key that reads CLEAN: without the mark a read through the withdrawn name
    /// found nothing, took a fallback and recorded no hit, so
    /// `let r: &u32 = if c { &b } else { &a }; assert!(*r == if c { b } else { a })`
    /// was FAILED [AY:CTREX_CAT:Genuine] on a program with no bug (fourth
    /// adversarial review of m3/soundness-fixes-2, 2026-09-14, defect M6/D7 —
    /// negative/merged_ref_store.rs::merged_read_safe, the row that gated the
    /// BMC lane over every dual file the branch changes). An unknown mark still
    /// records a hit and denies every per-edge alternative, so the read fails
    /// closed instead.
    pub(in crate::codegen_ay) fn forget_rooted_at(&mut self, base: &str) -> usize {
        let prefix = format!("{base}_");
        let mut withdrawn: Vec<Arc<str>> = Vec::new();
        if let Some((key, _)) = self.table.entries.get_key_value(base) {
            withdrawn.push(Arc::clone(key));
        }
        for (key, _) in self
            .table
            .entries
            .range(Arc::<str>::from(prefix.as_str())..)
            .take_while(|(key, _)| key.starts_with(prefix.as_str()))
        {
            withdrawn.push(Arc::clone(key));
        }
        if withdrawn.is_empty() {
            return 0;
        }
        let table = Arc::make_mut(&mut self.table);
        for key in &withdrawn {
            table.entries.remove(key);
            table.generations.remove(key);
            table.poisoned.insert(Arc::clone(key), None);
        }
        withdrawn.len()
    }

    /// Forget every entry, generation and poison mark. Only the corpus tests
    /// reset a table in place, so the method exists only where they compile.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn clear(&mut self) {
        self.table = Arc::new(Table::default());
    }

    /// Carry another table's entries (and their poison) into this one: used
    /// when a mini-inlined body inherits its caller's table.
    pub(in crate::codegen_ay) fn extend(&mut self, other: RefPointees) {
        if other.table.entries.is_empty() && other.table.poisoned.is_empty() {
            self.absorb_hits(&other);
            return;
        }
        self.absorb_hits(&other);
        let table = Arc::make_mut(&mut self.table);
        for (key, pointee) in &other.table.entries {
            table.next_generation += 1;
            table.generations.insert(Arc::clone(key), table.next_generation);
            table.entries.insert(Arc::clone(key), Arc::clone(pointee));
            match other.table.poisoned.get(key) {
                Some(poison) => {
                    table.poisoned.insert(Arc::clone(key), poison.clone());
                }
                None => {
                    table.poisoned.remove(key);
                }
            }
        }
    }

    /// Move another table's pending hits into this one.
    pub(in crate::codegen_ay) fn absorb_hits(&self, other: &RefPointees) {
        let taken = std::mem::take(&mut *other.hits.borrow_mut());
        self.hits.borrow_mut().extend(taken);
    }

    /// Generation counter, read before a statement to find the entries it did
    /// not re-insert.
    pub(in crate::codegen_ay) fn generation(&self) -> u64 {
        self.table.next_generation
    }

    /// After a reassignment of the storage named `key`: `key` and every entry
    /// nested under it (`key_…`) that was not inserted since `since` still
    /// describes the PREVIOUS value, so it is poisoned as unknown.
    pub(in crate::codegen_ay) fn poison_stale_since(&mut self, key: &str, since: u64) {
        let prefix = format!("{key}_");
        let is_stale = |table: &Table, entry: &Arc<str>| {
            table.generations.get(entry).is_none_or(|generation| *generation <= since)
                && !matches!(table.poisoned.get(entry), Some(None))
        };
        let mut stale: Vec<Arc<str>> = Vec::new();
        if let Some((entry, _)) = self.table.entries.get_key_value(key)
            && is_stale(&self.table, entry)
        {
            stale.push(Arc::clone(entry));
        }
        for (entry, _) in self
            .table
            .entries
            .range(Arc::<str>::from(prefix.as_str())..)
            .take_while(|(entry, _)| entry.starts_with(prefix.as_str()))
        {
            if is_stale(&self.table, entry) {
                stale.push(Arc::clone(entry));
            }
        }
        if stale.is_empty() {
            return;
        }
        let table = Arc::make_mut(&mut self.table);
        for entry in stale {
            table.poisoned.insert(entry, None);
        }
    }

    /// The per-edge alternatives of a poisoned join entry, without recording a
    /// hit. `None` when `key` is not poisoned or its alternatives are unknown.
    pub(in crate::codegen_ay) fn merged_alternatives(
        &self,
        key: &str,
    ) -> Option<&[MergedAlternative]> {
        self.table.poisoned.get(key).and_then(|poison| poison.as_deref())
    }

    /// Whether `key` is poisoned (no hit recorded).
    pub(in crate::codegen_ay) fn is_poisoned(&self, key: &str) -> bool {
        self.table.poisoned.contains_key(key)
    }

    /// Drain the poisoned keys read since the last call.
    pub(in crate::codegen_ay) fn take_hits(&self) -> Vec<Arc<str>> {
        std::mem::take(&mut *self.hits.borrow_mut()).into_iter().collect()
    }

    /// The table at a join, from each incoming edge's `(predicate, snapshot)`.
    pub(in crate::codegen_ay) fn merge_incoming(edges: Vec<(Option<Expr>, RefPointees)>) -> Self {
        let mut edges = edges;
        if edges.len() <= 1 {
            return edges.pop().map(|(_, table)| table).unwrap_or_default();
        }
        let merged = Self::default();
        for (_, table) in &edges {
            merged.absorb_hits(table);
        }
        let first = Arc::clone(&edges[0].1.table);
        if edges.iter().all(|(_, table)| Arc::ptr_eq(&table.table, &first)) {
            return Self { table: first, hits: merged.hits };
        }

        let mut keys: BTreeSet<Arc<str>> = BTreeSet::new();
        for (_, table) in &edges {
            keys.extend(table.table.entries.keys().cloned());
        }
        // A key an edge POISONED but holds no entry for — the shape
        // `forget_rooted_at` leaves behind when a local has several producers —
        // is still a key this join cannot answer for. Collecting only the
        // ENTRY keys dropped that mark at the join, so a read through
        // `let r: &u32 = if c { &b } else { &a };` found nothing, took a
        // fallback and recorded NO hit: `assert!(*r == if c { b } else { a })`
        // was FAILED [AY:CTREX_CAT:Genuine] on a program with no bug (fourth
        // adversarial review of m3/soundness-fixes-2, 2026-09-14, defect
        // M6/D7). Such a key is carried through as poisoned-unknown below.
        let mut entryless_poison: BTreeSet<Arc<str>> = BTreeSet::new();
        for (_, table) in &edges {
            for key in table.table.poisoned.keys() {
                if !keys.contains(key) {
                    entryless_poison.insert(Arc::clone(key));
                }
            }
        }
        let mut out = Table {
            next_generation: edges.iter().map(|(_, t)| t.table.next_generation).max().unwrap_or(0),
            ..Table::default()
        };
        for key in keys {
            let mut agreed: Option<&Arc<str>> = None;
            let mut agree = true;
            let mut last_present: Option<&Arc<str>> = None;
            let mut generation = 0u64;
            let mut unknown = false;
            let mut alternatives: Vec<MergedAlternative> = Vec::new();
            for (predicate, table) in &edges {
                let entry = table.table.entries.get(&key);
                if let Some(g) = table.table.generations.get(&key) {
                    generation = generation.max(*g);
                }
                match (entry, table.table.poisoned.get(&key)) {
                    (_, Some(None)) => {
                        unknown = true;
                        agree = false;
                        last_present = entry.or(last_present);
                    }
                    (_, Some(Some(nested))) => {
                        agree = false;
                        last_present = entry.or(last_present);
                        alternatives.extend(nested.iter().map(|alt| MergedAlternative {
                            edge_predicate: and_predicates(predicate, &alt.edge_predicate),
                            pointee: alt.pointee.clone(),
                        }));
                    }
                    (Some(pointee), None) => {
                        last_present = Some(pointee);
                        match agreed {
                            None => agreed = Some(pointee),
                            Some(previous) if previous == pointee => {}
                            Some(_) => agree = false,
                        }
                        alternatives.push(MergedAlternative {
                            edge_predicate: predicate.clone(),
                            pointee: Some(Arc::clone(pointee)),
                        });
                    }
                    (None, None) => {
                        agree = false;
                        alternatives.push(MergedAlternative {
                            edge_predicate: predicate.clone(),
                            pointee: None,
                        });
                    }
                }
            }
            let Some(pointee) = last_present else { continue };
            out.entries.insert(Arc::clone(&key), Arc::clone(pointee));
            out.generations.insert(Arc::clone(&key), generation);
            if !agree {
                out.poisoned.insert(key, (!unknown).then_some(alternatives));
            }
        }
        for key in entryless_poison {
            out.poisoned.insert(key, None);
        }
        Self { table: Arc::new(out), hits: merged.hits }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(s: &str) -> Arc<str> {
        Arc::from(s)
    }

    #[test]
    fn join_keeps_an_entry_every_edge_agrees_on() {
        let mut left = RefPointees::new();
        left.insert(name("f::local_4"), name("f::local_1"));
        let right = left.clone();
        let merged = RefPointees::merge_incoming(vec![(None, left), (None, right)]);
        assert_eq!(merged.get("f::local_4").map(|p| p.as_ref()), Some("f::local_1"));
        assert!(!merged.is_poisoned("f::local_4"));
        assert!(merged.take_hits().is_empty());
    }

    #[test]
    fn join_poisons_an_entry_the_edges_disagree_on() {
        let base = RefPointees::new();
        let mut then_arm = base.clone();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        let mut else_arm = base.clone();
        else_arm.insert(name("f::local_4"), name("f::local_1"));
        let c = Expr::var("c", ay_bindings::Sort::bool());
        let merged = RefPointees::merge_incoming(vec![
            (Some(c.clone()), then_arm),
            (Some(c.not()), else_arm),
        ]);
        let alternatives = merged.merged_alternatives("f::local_4").expect("alternatives");
        assert_eq!(alternatives.len(), 2);
        assert_eq!(alternatives[0].pointee.as_deref(), Some("f::local_2"));
        assert_eq!(alternatives[1].pointee.as_deref(), Some("f::local_1"));
        assert!(merged.take_hits().is_empty(), "merged_alternatives records no hit");
        assert!(merged.get("f::local_4").is_some(), "the entry stays for the encoding");
        assert_eq!(merged.take_hits(), vec![name("f::local_4")]);
    }

    #[test]
    fn an_entry_missing_on_one_edge_is_poisoned_with_an_unknown_alternative() {
        let mut then_arm = RefPointees::new();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        let else_arm = RefPointees::new();
        let merged = RefPointees::merge_incoming(vec![(None, then_arm), (None, else_arm)]);
        let alternatives = merged.merged_alternatives("f::local_4").expect("alternatives");
        assert!(alternatives.iter().any(|alt| alt.pointee.is_none()));
    }

    #[test]
    fn withdrawal_drops_the_entry_its_nested_keys_and_nothing_else() {
        let mut table = RefPointees::new();
        table.insert(name("f::local_5"), name("f::local_1"));
        table.insert(name("f::local_5_field_0"), name("f::local_2"));
        table.insert(name("f::local_50"), name("f::local_3"));
        table.insert(name("f::local_6"), name("f::local_4"));
        assert_eq!(table.forget_rooted_at("f::local_5"), 2);
        assert!(table.get("f::local_5").is_none());
        assert!(table.get("f::local_5_field_0").is_none());
        assert_eq!(table.get("f::local_50").map(|p| p.as_ref()), Some("f::local_3"));
        assert_eq!(table.get("f::local_6").map(|p| p.as_ref()), Some("f::local_4"));
        assert_eq!(table.forget_rooted_at("f::local_9"), 0);
        // A withdrawn key reads as POISONED even though it was clean before:
        // a read through it must fail closed, not find nothing and take a
        // fallback silently (defect M6/D7).
        assert!(table.is_poisoned("f::local_5"), "withdrawal poisons the key it withdraws");
        assert!(table.is_poisoned("f::local_5_field_0"), "and every nested key");
        assert!(!table.is_poisoned("f::local_50"), "and nothing else");
        assert!(!table.is_poisoned("f::local_6"), "and nothing else");
        assert!(
            table.merged_alternatives("f::local_5").is_none(),
            "a withdrawn key keeps no per-edge alternative"
        );
    }

    /// A key withdrawn on both edges has no entry to merge, and the JOIN must
    /// still refuse it: without the mark the read after the join finds nothing
    /// and records no hit (defect M6/D7).
    #[test]
    fn a_join_keeps_the_poison_of_a_key_no_edge_has_an_entry_for() {
        let mut then_arm = RefPointees::new();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        assert_eq!(then_arm.forget_rooted_at("f::local_4"), 1);
        let mut else_arm = RefPointees::new();
        else_arm.insert(name("f::local_4"), name("f::local_1"));
        assert_eq!(else_arm.forget_rooted_at("f::local_4"), 1);
        let merged = RefPointees::merge_incoming(vec![(None, then_arm), (None, else_arm)]);
        assert!(merged.get("f::local_4").is_none(), "no edge has an entry");
        assert!(merged.is_poisoned("f::local_4"), "the join keeps the refusal");
        let hits = merged.take_hits();
        assert!(
            hits.iter().any(|hit| hit.as_ref() == "f::local_4"),
            "and a read through it records a hit"
        );
    }

    /// The hit a read of a withdrawn key records is what demotes the harness:
    /// `flush_ref_pointee_path_ambiguity` turns it into a fail-closed reason.
    #[test]
    fn reading_a_withdrawn_key_records_a_hit() {
        let mut table = RefPointees::new();
        table.insert(name("f::local_4"), name("f::local_1"));
        assert_eq!(table.forget_rooted_at("f::local_4"), 1);
        assert!(table.take_hits().is_empty(), "withdrawal itself records no hit");
        assert!(table.get("f::local_4").is_none());
        let hits = table.take_hits();
        assert_eq!(hits.len(), 1, "the read of a withdrawn key is a hit");
        assert_eq!(hits[0].as_ref(), "f::local_4");
    }

    #[test]
    fn a_withdrawn_key_that_was_poisoned_still_reads_as_poisoned() {
        let mut then_arm = RefPointees::new();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        let mut else_arm = RefPointees::new();
        else_arm.insert(name("f::local_4"), name("f::local_1"));
        let mut merged = RefPointees::merge_incoming(vec![(None, then_arm), (None, else_arm)]);
        assert!(merged.merged_alternatives("f::local_4").is_some());
        assert_eq!(merged.forget_rooted_at("f::local_4"), 1);
        assert!(merged.get("f::local_4").is_none(), "the entry is withdrawn");
        assert!(merged.is_poisoned("f::local_4"), "withdrawal does not clear the poison");
        assert!(
            merged.merged_alternatives("f::local_4").is_none(),
            "a withdrawn key keeps no per-edge alternative"
        );
        assert_eq!(merged.take_hits(), vec![name("f::local_4")], "a read still records a hit");
    }

    #[test]
    fn a_fresh_insert_clears_poison() {
        let mut then_arm = RefPointees::new();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        let mut else_arm = RefPointees::new();
        else_arm.insert(name("f::local_4"), name("f::local_1"));
        let mut merged = RefPointees::merge_incoming(vec![(None, then_arm), (None, else_arm)]);
        merged.insert(name("f::local_4"), name("f::local_7"));
        assert!(!merged.is_poisoned("f::local_4"));
        assert!(merged.get("f::local_4").is_some());
        assert!(merged.take_hits().is_empty());
    }

    #[test]
    fn reassignment_without_a_new_entry_poisons_the_old_one_and_its_nested_keys() {
        let mut table = RefPointees::new();
        table.insert(name("f::local_5"), name("f::local_1"));
        table.insert(name("f::local_5_field_0"), name("f::local_2"));
        table.insert(name("f::local_50"), name("f::local_3"));
        let before = table.generation();
        table.poison_stale_since("f::local_5", before);
        assert!(table.is_poisoned("f::local_5"));
        assert!(table.is_poisoned("f::local_5_field_0"));
        assert!(!table.is_poisoned("f::local_50"), "a different local is untouched");
        let _ = table.range(name("f::local_5_")..).count();
        assert_eq!(table.take_hits(), vec![name("f::local_5_field_0")]);
    }

    #[test]
    fn a_reinsert_during_the_statement_is_not_stale() {
        let mut table = RefPointees::new();
        table.insert(name("f::local_5"), name("f::local_1"));
        let before = table.generation();
        table.insert(name("f::local_5"), name("f::local_1"));
        table.poison_stale_since("f::local_5", before);
        assert!(!table.is_poisoned("f::local_5"));
    }

    #[test]
    fn nested_joins_conjoin_the_predicates() {
        let a = Expr::var("a", ay_bindings::Sort::bool());
        let b = Expr::var("b", ay_bindings::Sort::bool());
        let mut x = RefPointees::new();
        x.insert(name("f::local_4"), name("f::local_1"));
        let mut y = RefPointees::new();
        y.insert(name("f::local_4"), name("f::local_2"));
        let inner = RefPointees::merge_incoming(vec![(Some(a.clone()), x), (Some(a.not()), y)]);
        let mut z = RefPointees::new();
        z.insert(name("f::local_4"), name("f::local_3"));
        let outer = RefPointees::merge_incoming(vec![(Some(b.clone()), inner), (Some(b.not()), z)]);
        let alternatives = outer.merged_alternatives("f::local_4").expect("alternatives");
        assert_eq!(alternatives.len(), 3);
        assert!(alternatives.iter().all(|alt| alt.edge_predicate.is_some()));
    }

    #[test]
    fn a_stale_entry_poisons_every_join_it_reaches() {
        let mut stale = RefPointees::new();
        stale.insert(name("f::local_4"), name("f::local_1"));
        stale.poison_stale_since("f::local_4", stale.generation());
        let mut fresh = RefPointees::new();
        fresh.insert(name("f::local_4"), name("f::local_1"));
        let merged = RefPointees::merge_incoming(vec![(None, stale), (None, fresh)]);
        assert!(merged.is_poisoned("f::local_4"));
        assert!(merged.merged_alternatives("f::local_4").is_none(), "unknown, not alternatives");
    }

    #[test]
    fn a_copy_carries_the_poison_and_reads_nothing() {
        let c = Expr::var("c", ay_bindings::Sort::bool());
        let mut then_arm = RefPointees::new();
        then_arm.insert(name("f::local_4"), name("f::local_2"));
        let mut else_arm = RefPointees::new();
        else_arm.insert(name("f::local_4"), name("f::local_1"));
        let mut merged = RefPointees::merge_incoming(vec![
            (Some(c.clone()), then_arm),
            (Some(c.not()), else_arm),
        ]);
        assert!(merged.has_entry("f::local_4"));
        assert!(merged.copy_entry(name("f::local_8"), "f::local_4").is_some());
        assert!(merged.nested_keys("f::local_4_").is_empty());
        assert!(merged.take_hits().is_empty(), "copying a reference reads no pointee");
        assert!(merged.is_poisoned("f::local_8"));
        assert_eq!(merged.merged_alternatives("f::local_8").map(<[_]>::len), Some(2));
        let _ = merged.get("f::local_8");
        assert_eq!(merged.take_hits(), vec![name("f::local_8")]);
    }

    #[test]
    fn a_copy_of_a_clean_entry_clears_the_destination_poison() {
        let mut table = RefPointees::new();
        table.insert(name("f::local_8"), name("f::local_3"));
        table.poison_stale_since("f::local_8", table.generation());
        assert!(table.is_poisoned("f::local_8"));
        table.insert(name("f::local_4"), name("f::local_1"));
        assert_eq!(table.copy_entry(name("f::local_8"), "f::local_4"), Some(name("f::local_1")));
        assert!(!table.is_poisoned("f::local_8"));
        assert!(table.copy_entry(name("f::local_9"), "f::local_missing").is_none());
        assert!(table.take_hits().is_empty());
    }
}

impl<'a, 'tcx, 't> super::StatementCodegen<'a, 'tcx, 't> {
    /// Fail closed when the statement or terminator just encoded read a pointee
    /// entry that is not the same on every incoming path, or that is left over
    /// from a previous value. The encoding it produced stands (it is exact on the
    /// last-encoded path), but neither a proof nor a counterexample may rest on it.
    pub(in crate::codegen_ay::statement) fn flush_ref_pointee_path_ambiguity(&mut self) {
        let hits = self.ref_pointees.take_hits();
        if hits.is_empty() {
            return;
        }
        let keys = hits.iter().map(|key| key.as_ref()).collect::<Vec<_>>().join(", ");
        let detail = match self.current_source_location() {
            Some(location) => format!("{location}: {keys}"),
            None => keys,
        };
        tracing::debug!(%detail, "bmc: path-ambiguous reference pointee read (fail-closed)");
        self.ctx.unsupported_with_fallback("bmc_ref_pointee_path_ambiguous", detail);
    }
}
