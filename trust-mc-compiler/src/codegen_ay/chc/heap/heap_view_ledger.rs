// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Which views of a heap object a read can trust.
//!
//! Typed memory keeps one array per type key (`mem_u16`, `mem_slice_u16`,
//! `mem_u32`, ...) and one region array per heap object. The same bytes of an
//! object therefore live in several arrays, and they agree only as far as the
//! stores keep them in step. Stores that write every view a reader may consult
//! do: `Box::new([1u16, 2])` writes each element under the array key, the
//! element key and the region; an element store through a pointer
//! (`deref_elem_store.rs`) writes the same three. A store under any other key
//! writes that key alone: `*(addr_of_mut!(*bx) as *mut u32) = v` leaves the
//! array key, the element key and the region at their old values, so a later
//! `bx[1]` read the initializer's element (a clean missed bug on main and on
//! fix/chc-lost-writes), and a read under a key nothing wrote (`*(p as *const
//! u32)` over a `Box<[u16; 2]>`) selected a cell no rule constrains, which was
//! certified Genuine (review of fix/chc-lost-writes, lostwrite round 1,
//! finding 3).
//!
//! The ledger records, while the body is encoded, every typed-memory write and
//! read of an address whose object half is a constant: its object, its byte
//! span (open-ended when the offset is not a constant), its key, and for a
//! write its GROUP, the source-level store it belongs to: every write one MIR
//! statement or terminator makes, a walked callee's statements and terminators
//! counting as statements of their own. One store writes its value under its
//! own key, its elements and fields under theirs (`Box::new(S { a, b })`
//! writes the struct key and each field's key), its region and its pointer
//! aliases, all in one group; grouping by the value TERM split such a store
//! (a field's term is not the whole value's) and failed coherent field reads
//! closed. The zero fill of `alloc_zeroed` and the copy of a `realloc` are
//! one group each, writing every key they fill.
//!
//! When every block is encoded, each read of a heap object is judged at every
//! byte it may cover (`classify_read`). Where every group covering the byte
//! wrote the read's key, the read is exact. Where some did and some did not,
//! the read may return a value another store made stale: FailClose,
//! [`HEAP_VIEW_READ_STALE`]. Where groups cover the byte and none wrote the
//! key, the read selects a free cell: SoundHavoc, [`HEAP_VIEW_READ_UNWRITTEN`]
//! (a proof over a free value is a proof; a counterexample resting on it is
//! not evidence). Only the groups that may run before the read count: those
//! in a block that reaches the read's block, and in the read's own block
//! those encoded no later than it (statements are encoded in order), or all
//! of them when the block lies on a cycle. Counting later ones too failed a
//! `Box<dyn Trait>` closed whose coercion read the struct before a method
//! stored one of its fields (kani/FatPointers/boxtrait.rs).
//!
//! A group that wrote the read's key over the byte masks every group it
//! definitely follows on the way to the read (`shadows`): the later store
//! made the read's view current again, whatever an earlier store left stale.
//! It must be a store of a harness statement (a terminator's stub or a walked
//! callee may store conditionally) at a constant address covering the byte
//! (an element at a constant index folds to one), and every path from
//! the earlier store to the read must run it after that store: in the read's
//! block before the read, or in a block every such path passes. Without it, a
//! `realloc` copy that did not copy the array key made the element just
//! stored at that key stale (`safe_elem_store_after_realloc_fresh`,
//! lostwrite track round 1, finding 3).
//!
//! A read whose offset is not a constant (an index) is judged only at the
//! bytes some group wrote under its key (where such a read can land without
//! failing a bounds check of its own view). A read whose object is not a
//! constant is judged against every heap object for staleness, and is
//! UNWRITTEN when some heap object's bytes were written but nothing that may
//! run before the read wrote its key at all, in any object or through any
//! store the encoder marks (`write_used_type_arrays`, where the static images
//! count as written at entry): wherever it lands, it selects a cell no rule
//! constrains, which is not the bytes where it lands on written ones (where it
//! can land only on memory nothing wrote, a fresh buffer or an invalid
//! address, the free cell is what the real read returns, and the read is not
//! flagged: `uninit/vec-read-uninit`). `*(bx.as_ptr() as *const u32)` over a
//! `Box<[u8; 4]>` read such a cell through a pointer the slice stub returned,
//! and the wrong value was certified Genuine on a program Kani proves
//! (lostwrite track round 1, finding 10). A stack slot is judged only for a
//! pointer read under a key nothing wrote there. A write whose object is not
//! a constant is not recorded: the store paths that make one record their own
//! fail-closed reason (`deref_store_referent_unresolved` and its kin), which
//! the ledger does not replace.
//!
//! A read the ledger would flag is held against the rules first: a load whose
//! value no rule mentions (a coercion's republishing load whose alias store is
//! declined, a comparison's deref level the reconstruction lane answers
//! instead) read nothing the program uses, and is not judged (`rule_uses`).
//! Judging such loads failed `Box<dyn Tv>` closed after an element store the
//! method read exactly (q3 `safe_elem_store_then_dyn_read`) and cost a
//! must-fail comparison its certificate (`double_ref_eq_must_fail`, lostwrite
//! track round 1, findings 3 and 4).
//!
//! Statics and promoted constants are not judged here: their typed views are
//! judged by untyped-view net 2 and the static image.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};
use tracing::debug;

use super::ChcCtx;

/// FailClose: a read of a heap object under a key some store of the object's
/// bytes did not write.
pub(in crate::codegen_ay::chc) const HEAP_VIEW_READ_STALE: &str = "heap_view_read_stale";
/// SoundHavoc (accounted, its arrays the freed identities): a read of a heap
/// object under a key no store of those bytes wrote.
pub(in crate::codegen_ay::chc) const HEAP_VIEW_READ_UNWRITTEN: &str = "heap_view_read_unwritten";
/// The key the ledger files a heap object's region array under.
pub(in crate::codegen_ay::chc) const REGION_VIEW_KEY: &str = "@region";

/// End of an open-ended span.
const OPEN: u64 = u64::MAX;

/// A byte span `[lo, hi)` of one object; `hi == OPEN` runs to its end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct ViewSpan {
    lo: u64,
    hi: u64,
}

impl ViewSpan {
    pub(in crate::codegen_ay::chc) fn new(lo: u64, hi: Option<u64>) -> Self {
        let hi = hi.filter(|h| *h > lo).unwrap_or(OPEN);
        Self { lo, hi }
    }

    fn whole() -> Self {
        Self { lo: 0, hi: OPEN }
    }

    /// The span's first byte.
    pub(in crate::codegen_ay::chc) fn lo(&self) -> u64 {
        self.lo
    }
}

#[derive(Clone, Debug)]
struct ViewWrite {
    obj: u32,
    span: ViewSpan,
    key: Arc<str>,
    group: (u64, u64),
    /// The block being encoded when the write was made.
    bb: usize,
    /// The bytes the write definitely writes, when it may mask earlier writes
    /// (`shadows`): a store of a harness statement, outside any walk, at a
    /// constant address.
    mask_span: Option<ViewSpan>,
}

#[derive(Clone, Debug)]
struct ViewRead {
    /// `None`: an address whose object half is not a constant.
    obj: Option<u32>,
    /// `None`: an offset that is not a constant.
    span: Option<ViewSpan>,
    key: Arc<str>,
    /// The block being encoded, and the statement counter, when the read was
    /// made.
    bb: usize,
    seq: u64,
    /// The term the load returned, for the use check (`rule_uses`).
    value: Option<Expr>,
}

/// The ledger itself (see the module documentation).
#[derive(Debug, Default)]
pub(in crate::codegen_ay::chc) struct HeapViewLedger {
    statement: u64,
    fresh: u64,
    writes: Vec<ViewWrite>,
    reads: Vec<ViewRead>,
    /// A reference's logical value was deliberately not serialized as native
    /// bytes. Monotone, like writes/reads: speculative rollback or allocation
    /// ID reuse cannot turn an unavailable physical image into authority.
    unbacked_reference_images: HashSet<(u32, Arc<str>)>,
    /// While set, a write whose offset is not a constant covers this span of
    /// its object instead of the whole object (an element store at a symbolic
    /// index covers its array, `deref_elem_store.rs`).
    write_extent: Option<ViewSpan>,
    /// Set while a terminator is encoded (`next_terminator`).
    in_terminator: bool,
    /// While set, the bytes a write of the current store writes, where its
    /// address does not say (an element store at an index the MIR fixes,
    /// `deref_elem_store.rs`): its span, and the bytes it masks.
    write_exact: Option<ViewSpan>,
}

/// How a read fares (`classify_read`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum ViewReadClass {
    Exact,
    Unwritten,
    Stale,
}

impl HeapViewLedger {
    /// A new MIR statement begins: its writes form new groups.
    pub(in crate::codegen_ay::chc) fn next_statement(&mut self) {
        self.statement += 1;
        self.in_terminator = false;
    }

    /// A new MIR terminator begins: its writes form new groups, none of which
    /// masks an earlier store (a call's model may store conditionally).
    pub(in crate::codegen_ay::chc) fn next_terminator(&mut self) {
        self.statement += 1;
        self.in_terminator = true;
    }

    /// The group of a write in the current statement. Every write one MIR
    /// statement makes belongs to one source-level store: the value under its
    /// own key, its elements or fields decomposed under theirs (whose terms
    /// differ from the whole value's), the region, the pointer-wrapper aliases.
    /// A walked callee's statements are statements of their own.
    pub(in crate::codegen_ay::chc) fn group_for(&self, _value: &Expr) -> (u64, u64) {
        (self.statement, 0)
    }

    /// A group no other write shares (a havoc, a zero fill, a copy).
    pub(in crate::codegen_ay::chc) fn fresh_group(&mut self) -> (u64, u64) {
        self.fresh += 1;
        (self.statement, (1u64 << 63) | self.fresh)
    }

    pub(in crate::codegen_ay::chc) fn set_write_extent(&mut self, extent: Option<ViewSpan>) {
        self.write_extent = extent;
    }

    pub(in crate::codegen_ay::chc) fn set_write_exact(&mut self, exact: Option<ViewSpan>) {
        self.write_exact = exact;
    }

    fn push_write(
        &mut self,
        obj: u32,
        span: Option<ViewSpan>,
        key: &str,
        group: (u64, u64),
        bb: usize,
        walked: bool,
        exact: Option<ViewSpan>,
    ) {
        let mask_span =
            exact.or(self.write_exact).filter(|s| !walked && !self.in_terminator && s.hi != OPEN);
        let span = span.or(self.write_exact).or(self.write_extent).unwrap_or_else(ViewSpan::whole);
        self.writes.push(ViewWrite { obj, span, key: Arc::from(key), group, bb, mask_span });
    }

    fn push_read(
        &mut self,
        obj: Option<u32>,
        span: Option<ViewSpan>,
        key: &str,
        bb: usize,
        value: Option<Expr>,
    ) {
        let seq = self.statement;
        self.reads.push(ViewRead { obj, span, key: Arc::from(key), bb, seq, value });
    }
}

/// Bytes a cell of `sort` occupies, when the sort says.
pub(in crate::codegen_ay::chc) fn view_sort_bytes(sort: &Sort) -> Option<u64> {
    if sort.is_bool() {
        return Some(1);
    }
    if let Some(width) = sort.bitvec_width() {
        return Some(u64::from(width).div_ceil(8));
    }
    if sort.is_datatype() {
        return ChcCtx::sum_datatype_field_bits(sort).map(|bits| u64::from(bits).div_ceil(8));
    }
    None
}

/// The object an address names and its constant byte offset, as far as the
/// address says: `(Some(obj), Some(offset))` for a constant address,
/// `(Some(obj), None)` for a constant object half over a symbolic offset (an
/// element at an index: `concat(obj, 0) + i * size`), `None` otherwise.
pub(in crate::codegen_ay::chc) fn view_object_of(addr: &Expr) -> Option<(u32, Option<u64>)> {
    if let Some((obj, offset)) = ChcCtx::try_extract_constant_addr(addr) {
        return Some((obj, Some(u64::from(offset))));
    }
    if addr.sort().bitvec_width() != Some(64) {
        return None;
    }
    if let Some(obj) = ChcCtx::const_obj_id_u32(&addr.clone().extract(63, 32)) {
        return Some((obj, None));
    }
    match addr.value() {
        ExprValue::BvConcat(high, _) => ChcCtx::const_obj_id_u32(high).map(|obj| (obj, None)),
        // An in-bounds step from a base whose object is a constant stays in
        // that object; an out-of-bounds one fails its own access check.
        ExprValue::BvAdd(a, b) => {
            view_object_of(a).or_else(|| view_object_of(b)).map(|(obj, _)| (obj, None))
        }
        _ => None,
    }
}

/// The offset in `obj` of an address that folds to a constant in that object
/// (an element at a constant index: `concat(obj, 0) + 2`).
fn constant_offset_in(addr: &Expr, obj: u32) -> Option<u64> {
    let (value, 64) =
        crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value(addr)?
    else {
        return None;
    };
    let value = u64::try_from(value).ok()?;
    ((value >> 32) as u32 == obj).then_some(value & 0xffff_ffff)
}

/// Judge one read of `key` over `span` (`None`: unknown offset) against the
/// writes of its object (see the module documentation).
pub(in crate::codegen_ay::chc) fn classify_read(
    writes: &[(ViewSpan, &str, (u64, u64))],
    span: Option<ViewSpan>,
    key: &str,
) -> ViewReadClass {
    classify_read_masked(writes, span, key, &|_, _, _, _| false)
}

/// [`classify_read`], where `masks(w, x, lo, hi)` says that write `w` (by
/// index into `writes`) masks write `x` over the bytes `[lo, hi)` on the way
/// to the read (`shadows`): a group of writes is not counted at a byte where
/// another group's write of the read's key masks it.
pub(in crate::codegen_ay::chc) fn classify_read_masked(
    writes: &[(ViewSpan, &str, (u64, u64))],
    span: Option<ViewSpan>,
    key: &str,
    masks: &dyn Fn(usize, usize, u64, u64) -> bool,
) -> ViewReadClass {
    if writes.is_empty() {
        return ViewReadClass::Exact;
    }
    let mut points: BTreeSet<u64> = BTreeSet::new();
    for (w, _, _) in writes {
        points.insert(w.lo);
        if w.hi != OPEN {
            points.insert(w.hi);
        }
    }
    if let Some(s) = span {
        points.insert(s.lo);
        if s.hi != OPEN {
            points.insert(s.hi);
        }
    }
    let points: Vec<u64> = points.into_iter().collect();
    let mut unwritten = false;
    for (i, &lo) in points.iter().enumerate() {
        let hi = points.get(i + 1).copied().unwrap_or(OPEN);
        if let Some(s) = span
            && (hi <= s.lo || lo >= s.hi)
        {
            continue;
        }
        let covers = |w: &ViewSpan| w.lo <= lo && (w.hi == OPEN || hi <= w.hi) && w.lo < w.hi;
        let covering: Vec<usize> = (0..writes.len()).filter(|&i| covers(&writes[i].0)).collect();
        let key_writers: Vec<usize> =
            covering.iter().copied().filter(|&i| writes[i].1 == key).collect();
        let mut groups: BTreeSet<(u64, u64)> = BTreeSet::new();
        let mut with_key: BTreeSet<(u64, u64)> = BTreeSet::new();
        for &i in &covering {
            let (_, k, g) = writes[i];
            let masked =
                key_writers.iter().any(|&w| writes[w].2 != g && k != key && masks(w, i, lo, hi));
            if masked {
                continue;
            }
            groups.insert(g);
            if k == key {
                with_key.insert(g);
            }
        }
        if groups.is_empty() {
            continue;
        }
        if with_key.is_empty() {
            // An unknown offset lands where its own view was written.
            if span.is_some() {
                unwritten = true;
            }
            continue;
        }
        if with_key.len() != groups.len() {
            return ViewReadClass::Stale;
        }
    }
    if unwritten { ViewReadClass::Unwritten } else { ViewReadClass::Exact }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether `obj_id` names a heap allocation: not null, and neither a stack
    /// slot nor a global object (`obj_id_is_heap_allocation`), nor an object a
    /// static's state variable or layout record names.
    pub(in crate::codegen_ay::chc) fn is_heap_object_id(&self, obj_id: u32) -> bool {
        obj_id >= 2
            && self.obj_id_is_heap_allocation(obj_id)
            && !self.ref_resolution.static_state_idx_by_obj.contains_key(&obj_id)
            && !self.ref_resolution.static_alloc_sizes.iter().any(|(id, _, _)| *id == obj_id)
    }

    /// Record a write of `value` under `key` at `addr` (a cell of `sort`).
    pub(in crate::codegen_ay::chc) fn note_view_write(
        &mut self,
        addr: &Expr,
        value: &Expr,
        key: &str,
        sort: &Sort,
    ) {
        let group = self.heap_state.view_ledger.group_for(value);
        self.note_view_write_in_group(addr, key, sort, group);
    }

    /// [`Self::note_view_write`] into a group the caller chose.
    pub(in crate::codegen_ay::chc) fn note_view_write_in_group(
        &mut self,
        addr: &Expr,
        key: &str,
        sort: &Sort,
        group: (u64, u64),
    ) {
        let Some((obj, offset)) = view_object_of(addr) else { return };
        let bytes = view_sort_bytes(sort);
        let span = offset.map(|lo| ViewSpan::new(lo, bytes.map(|n| lo + n)));
        // The bytes the store definitely writes: its span, or the folded
        // constant address of an element at a constant index (`base + 2`).
        let exact = span.or_else(|| {
            constant_offset_in(addr, obj).map(|lo| ViewSpan::new(lo, bytes.map(|n| lo + n)))
        });
        let walked = self.inline_walk_write_mark.is_some();
        self.heap_state.view_ledger.push_write(
            obj,
            span,
            key,
            group,
            self.current_encode_bb,
            walked,
            exact,
        );
    }

    /// Defer an unused reference-to-dyn byte alias only after a real typed
    /// write of this heap object. Any used read of a different physical view (including
    /// a symbolic offset or escaped object) must fail closed: existing cells
    /// might be constrained by an older byte store, so SoundHavoc alone is
    /// insufficient. No native pointer bytes are produced here.
    pub(in crate::codegen_ay::chc) fn defer_reference_byte_view(
        &mut self,
        obj: u32,
        concrete_key: &str,
    ) -> bool {
        if !self.is_heap_object_id(obj)
            || self.heap_state.heap_alloc_size(obj).is_none()
            || !self
                .heap_state
                .view_ledger
                .writes
                .iter()
                .any(|w| w.obj == obj && &*w.key == concrete_key)
        {
            return false;
        }
        self.heap_state
            .view_ledger
            .unbacked_reference_images
            .insert((obj, Arc::from(concrete_key)));
        true
    }

    /// Record a havoc of `key`'s cells at `addr` (the whole object when the
    /// offset is unknown; nothing when the object is).
    pub(in crate::codegen_ay::chc) fn note_view_havoc(&mut self, addr: Option<&Expr>, key: &str) {
        let Some((obj, offset)) = addr.and_then(view_object_of) else { return };
        let group = self.heap_state.view_ledger.fresh_group();
        let span = offset.map(|lo| ViewSpan::new(lo, None));
        let walked = self.inline_walk_write_mark.is_some();
        self.heap_state.view_ledger.push_write(
            obj,
            span,
            key,
            group,
            self.current_encode_bb,
            walked,
            None,
        );
    }

    /// Record one store that writes each of `keys` over `span` of `obj` (a
    /// zero fill, a reallocation's copy).
    pub(in crate::codegen_ay::chc) fn note_view_fill(
        &mut self,
        obj: u32,
        span: ViewSpan,
        keys: &[&str],
    ) {
        let group = self.heap_state.view_ledger.fresh_group();
        let walked = self.inline_walk_write_mark.is_some();
        for key in keys {
            self.heap_state.view_ledger.push_write(
                obj,
                Some(span),
                key,
                group,
                self.current_encode_bb,
                walked,
                Some(span),
            );
        }
    }

    /// Record a read under `key` at `addr` (a cell of `sort`) that returned
    /// `value`.
    pub(in crate::codegen_ay::chc) fn note_view_read(
        &mut self,
        addr: &Expr,
        key: &str,
        sort: &Sort,
        value: Option<&Expr>,
    ) {
        let bb = self.current_encode_bb;
        let value = value.cloned();
        match view_object_of(addr) {
            Some((obj, offset)) => {
                let bytes = view_sort_bytes(sort);
                let span = offset
                    .or_else(|| constant_offset_in(addr, obj))
                    .map(|lo| ViewSpan::new(lo, bytes.map(|n| lo + n)));
                self.heap_state.view_ledger.push_read(Some(obj), span, key, bb, value);
            }
            None => self.heap_state.view_ledger.push_read(None, None, key, bb, value),
        }
    }

    /// Judge every recorded read (see the module documentation) and record
    /// the reasons. Called once the body's blocks are encoded.
    pub(in crate::codegen_ay::chc) fn record_heap_view_ledger_reasons(&mut self) {
        let ledger = &self.heap_state.view_ledger;
        if ledger.reads.is_empty() {
            return;
        }
        // Heap objects are judged in full. A stack slot is judged only for a
        // POINTER read under a key nothing wrote there (`*(&a as *const usize
        // as *const *const u16)`): its memory mirrors a state variable its own
        // lanes keep current, and its scalar puns have their own lanes
        // (`valid-value-checks`), but a free pointer value read out of it is
        // dereferenced with nothing to say it is free.
        let mut kind: HashMap<u32, Option<bool>> = HashMap::new();
        let mut by_obj: HashMap<u32, Vec<&ViewWrite>> = HashMap::new();
        for w in &ledger.writes {
            let judged = *kind.entry(w.obj).or_insert_with(|| {
                if self.is_heap_object_id(w.obj) {
                    Some(true)
                } else if self.heap_state.local_idx_for_obj_id(w.obj).is_some() {
                    Some(false)
                } else {
                    None
                }
            });
            if judged.is_some() {
                by_obj.entry(w.obj).or_default().push(w);
            }
        }
        let is_heap = |obj: &u32| kind.get(obj).copied().flatten() == Some(true);
        // Encoding order is not program order across blocks: a write may run
        // before a read when its block reaches the read's block, or in the same
        // block when it was encoded first (statements are encoded in order) or
        // the block lies on a cycle.
        let mut reach: HashMap<usize, Vec<bool>> = HashMap::new();
        let mut reaches = |from: usize, to: usize| -> bool {
            let row = reach.entry(from).or_insert_with(|| self.blocks_reached_after_an_edge(from));
            row.get(to).copied().unwrap_or(true)
        };
        // The blocks the ledger itself saw write a key: there it knows the
        // order of the writes and the reads.
        let ledger_blocks = |key: &str| -> HashSet<usize> {
            ledger.writes.iter().filter(|w| *w.key == *key).map(|w| w.bb).collect()
        };
        let mut flagged: Vec<(usize, ViewReadClass)> = Vec::new();
        for (read_idx, read) in ledger.reads.iter().enumerate() {
            // The offset of a raw byte read is not restricted to offsets
            // some byte store wrote. The legacy view classifier uses that
            // restriction for ordinary unknown-index views, so a deliberately
            // omitted reference image needs this explicit read-time boundary.
            // Only the exact concrete reference-value key remains supported;
            // a different scalar key or a same-width region is not evidence
            // of a native pointer representation.
            // Mark the entire object conservatively; an unknown object can
            // alias it. An unused load is still filtered by rule_uses below.
            if ledger.unbacked_reference_images.iter().any(|(obj, concrete_key)| {
                **concrete_key != *read.key && read.obj.is_none_or(|read_obj| read_obj == *obj)
            }) {
                flagged.push((read_idx, ViewReadClass::Stale));
                continue;
            }
            let mut prior = |writes: &[&ViewWrite]| -> Vec<ViewWrite> {
                writes
                    .iter()
                    .filter(|w| {
                        if w.bb == read.bb {
                            w.group.0 <= read.seq || reaches(w.bb, read.bb)
                        } else {
                            reaches(w.bb, read.bb)
                        }
                    })
                    .map(|w| (*w).clone())
                    .collect()
            };
            // A `Vec::with_capacity` buffer whose `Vec` may change keeps the
            // `Vec`'s contents in the `Vec`'s own model, not in these cells:
            // a `push` writes no store the ledger sees, so a read through the
            // buffer pointer is free, not the pushed value, and was certified
            // Genuine on a program Kani proves (`with_capacity(4)`, two
            // pushes, `*v.as_ptr().add(1) == 8`; lostwrite track round 2,
            // finding 5's class). Such a read is unwritten wherever it may
            // land on one.
            let lands_on_untracked_buffer = match read.obj {
                Some(obj) => self.heap_state.vec_capacity_size_taints.contains_key(&obj),
                None => !self.heap_state.vec_capacity_size_taints.is_empty(),
            };
            if lands_on_untracked_buffer {
                flagged.push((read_idx, ViewReadClass::Unwritten));
                continue;
            }
            match read.obj {
                Some(obj) => {
                    let Some(writes) = by_obj.get(&obj) else { continue };
                    let heap = is_heap(&obj);
                    if !heap && !key_holds_pointer(&read.key) {
                        continue;
                    }
                    let prior = prior(writes);
                    match self.classify_ledger_read(&prior, read) {
                        ViewReadClass::Stale if !heap => {}
                        ViewReadClass::Exact => {}
                        class => flagged.push((read_idx, class)),
                    }
                }
                None => {
                    let mut class = ViewReadClass::Exact;
                    let mut key_written = false;
                    // Whether the read may land on a heap object whose bytes a
                    // store wrote (under any key), where a free cell is not
                    // the bytes. A read that can land only on memory nothing
                    // wrote (a fresh buffer, an invalid address) reads what
                    // the real program reads: anything.
                    let mut heap_written = false;
                    for (obj, writes) in &by_obj {
                        let prior = prior(writes);
                        heap_written |= is_heap(obj) && !prior.is_empty();
                        // A write of the read's own statement (its destination's
                        // mirror) comes after the read.
                        key_written |= prior.iter().any(|w| {
                            *w.key == *read.key && !(w.bb == read.bb && w.group.0 == read.seq)
                        });
                        if is_heap(obj)
                            && !prior.is_empty()
                            && self.classify_ledger_read(&prior, read) == ViewReadClass::Stale
                        {
                            debug!(obj, key = %read.key, "CHC: unplaced read may see a stale heap view");
                            class = ViewReadClass::Stale;
                            break;
                        }
                    }
                    if class == ViewReadClass::Exact && !key_written && heap_written {
                        let written_before = self.type_array_written_before(
                            &read.key,
                            read.bb,
                            &ledger_blocks(&read.key),
                            &mut reaches,
                        );
                        debug!(
                            key = %read.key,
                            written_before,
                            "CHC: unplaced read of a view the ledger saw no write of"
                        );
                        if !written_before {
                            class = ViewReadClass::Unwritten;
                        }
                    }
                    if class != ViewReadClass::Exact {
                        flagged.push((read_idx, class));
                    }
                }
            }
        }
        if flagged.is_empty() {
            return;
        }
        let used = self.rule_uses(
            &flagged.iter().filter_map(|(i, _)| ledger.reads[*i].value.clone()).collect::<Vec<_>>(),
        );
        let mut stale = 0usize;
        let mut unwritten = 0usize;
        // The arrays an unwritten read selected from: the read's value is one
        // of their cells no rule constrains, so they are the approximation's
        // freed identities, and a counterexample that never reads them (a
        // memory-safety or initialization check of the same access) is still
        // certified.
        let mut freed_arrays: Vec<String> = Vec::new();
        for (read_idx, class) in flagged {
            let read = &ledger.reads[read_idx];
            // Only a select term is looked for: a load the array builder folded
            // to another term (a forwarded store's value) is always judged.
            if let Some(value) = &read.value
                && matches!(value.value(), ExprValue::Select { .. })
                && !used.contains(value)
            {
                debug!(obj = ?read.obj, key = %read.key, "CHC: flagged heap view read is unused");
                continue;
            }
            debug!(
                obj = ?read.obj,
                key = %read.key,
                span = ?read.span,
                ?class,
                "CHC: heap view read judged"
            );
            match class {
                ViewReadClass::Stale => stale += 1,
                ViewReadClass::Unwritten => {
                    unwritten += 1;
                    let array = if *read.key == *REGION_VIEW_KEY {
                        read.obj.and_then(|obj| self.heap_state.region_arrays.get(&obj))
                    } else {
                        self.heap_state.type_arrays.get(&*read.key)
                    };
                    match array {
                        Some((name, _)) => freed_arrays.push(name.to_string()),
                        // No array to name: the reason stays unaccounted.
                        None => freed_arrays.push(String::new()),
                    }
                }
                ViewReadClass::Exact => {}
            }
        }
        if stale > 0 {
            self.record_sound_fallback_reason(HEAP_VIEW_READ_STALE);
        }
        if unwritten > 0 {
            if freed_arrays.iter().any(String::is_empty) {
                self.record_sound_fallback_reason(HEAP_VIEW_READ_UNWRITTEN);
            } else {
                freed_arrays.sort();
                freed_arrays.dedup();
                self.record_sound_fallback_reason_identified(
                    HEAP_VIEW_READ_UNWRITTEN,
                    freed_arrays.first().map(String::as_str),
                );
                for name in freed_arrays.iter().skip(1) {
                    self.vc.note_additional_freed_var(name);
                }
            }
        }
    }

    /// Judge `read` against the writes of its object that may run before it,
    /// with the masking of `shadows`.
    fn classify_ledger_read(&self, prior: &[ViewWrite], read: &ViewRead) -> ViewReadClass {
        let rows: Vec<(ViewSpan, &str, (u64, u64))> =
            prior.iter().map(|w| (w.span, &*w.key, w.group)).collect();
        classify_read_masked(&rows, read.span, &read.key, &|w, x, lo, hi| {
            prior[w].mask_span.is_some_and(|m| m.lo <= lo && hi <= m.hi && hi != OPEN)
                && self.shadows(&prior[w], &prior[x], read)
        })
    }

    /// Whether the write `w` runs after the write `x` on every path from `x`
    /// to `read` (see the module documentation).
    fn shadows(&self, w: &ViewWrite, x: &ViewWrite, read: &ViewRead) -> bool {
        if w.mask_span.is_none() || w.group == x.group {
            return false;
        }
        let (w_seq, x_seq) = (w.group.0, x.group.0);
        if w.bb == read.bb {
            if w_seq >= read.seq {
                return false;
            }
            // `x` between `w` and the read in that block survives `w`.
            return !(x.bb == read.bb && x_seq >= w_seq && x_seq <= read.seq);
        }
        if x.bb == w.bb && x_seq < w_seq {
            return true;
        }
        if x.bb == read.bb && x_seq <= read.seq {
            return false;
        }
        !self.block_reaches_avoiding(x.bb, read.bb, w.bb)
    }

    /// Whether some path leaves block `from` and reaches block `to` without
    /// entering block `avoid`.
    fn block_reaches_avoiding(&self, from: usize, to: usize, avoid: usize) -> bool {
        let blocks = &self.body.blocks;
        let mut seen = vec![false; blocks.len()];
        let mut stack: Vec<usize> =
            blocks.get(from).map(|b| b.terminator.successors()).unwrap_or_default();
        while let Some(bb) = stack.pop() {
            if bb >= seen.len() {
                return true;
            }
            if bb == avoid || std::mem::replace(&mut seen[bb], true) {
                continue;
            }
            if bb == to {
                return true;
            }
            stack.extend(blocks[bb].terminator.successors());
        }
        false
    }

    /// Whether a store the ledger did not see may have written `key`'s type
    /// array before block `bb`: a static's image (seeded at entry), or a store
    /// the encoder marks (`write_used_type_arrays`) in a block that may run
    /// first and that no recorded write of the key is in (`ledger_blocks`;
    /// in those the ledger's own order of writes and reads decides). An
    /// unmarked store the ledger does not see either is not counted, which
    /// only ever withholds a certificate.
    fn type_array_written_before(
        &self,
        key: &str,
        bb: usize,
        ledger_blocks: &HashSet<usize>,
        reaches: &mut impl FnMut(usize, usize) -> bool,
    ) -> bool {
        if self.ref_resolution.static_memory_inits.iter().any(|(k, _, _, _)| **k == *key) {
            return true;
        }
        let Some((arr_name, _)) = self.heap_state.type_arrays.get(key) else { return true };
        let Some(blocks) = self.heap_state.write_used_type_arrays.get(arr_name) else {
            return false;
        };
        blocks.iter().any(|&wb| !ledger_blocks.contains(&wb) && (wb == bb || reaches(wb, bb)))
    }

    /// The terms of `values` some rule's constraints or relation arguments
    /// mention, by term identity or by structure.
    fn rule_uses(&self, values: &[Expr]) -> HashSet<Expr> {
        let mut found: HashSet<Expr> = HashSet::new();
        if values.is_empty() {
            return found;
        }
        let wanted: HashSet<*const ExprValue> =
            values.iter().map(|v| std::ptr::from_ref(v.value())).collect();
        let mut seen: HashSet<*const ExprValue> = HashSet::new();
        let mut selects: Vec<Expr> = Vec::new();
        let mut stack: Vec<&Expr> = Vec::new();
        for rule in &self.vc.rules {
            stack.extend(rule.body.constraints.iter());
            stack.extend(rule.head.args.iter());
            if let Some(app) = &rule.body.relation {
                stack.extend(app.args.iter());
            }
        }
        while let Some(e) = stack.pop() {
            let ptr = std::ptr::from_ref(e.value());
            if !seen.insert(ptr) {
                continue;
            }
            if wanted.contains(&ptr) {
                found.insert(e.clone());
            }
            if matches!(e.value(), ExprValue::Select { .. }) {
                selects.push(e.clone());
            }
            stack.extend(e.children());
        }
        for v in values {
            if !found.contains(v) && selects.iter().any(|s| s == v) {
                found.insert(v.clone());
            }
        }
        found
    }

    /// The blocks reachable from `from` over at least one edge.
    pub(in crate::codegen_ay::chc) fn blocks_reached_after_an_edge(
        &self,
        from: usize,
    ) -> Vec<bool> {
        let blocks = &self.body.blocks;
        let mut seen = vec![false; blocks.len()];
        let mut stack: Vec<usize> =
            blocks.get(from).map(|b| b.terminator.successors()).unwrap_or_default();
        while let Some(bb) = stack.pop() {
            if bb >= seen.len() || std::mem::replace(&mut seen[bb], true) {
                continue;
            }
            stack.extend(blocks[bb].terminator.successors());
        }
        seen
    }
}

/// Whether a type key names a type that holds a pointer (the encoder's spelling
/// of a reference, a raw pointer, or a pointer wrapper).
fn key_holds_pointer(key: &str) -> bool {
    key.starts_with("ptr_")
        || key.starts_with("ref_")
        || key.contains("NonNull")
        || key.contains("Unique")
        || key.starts_with("std_boxed_Box")
        || key.starts_with("std_rc_Rc")
        || key.starts_with("std_sync_Arc")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn w(lo: u64, hi: u64, key: &'static str, g: u64) -> (ViewSpan, &'static str, (u64, u64)) {
        (ViewSpan::new(lo, Some(hi)), key, (g, 0))
    }

    #[test]
    fn coherent_element_views_are_exact() {
        // Box::new([1u16, 2]): each element under the array key, the element
        // key and the region, one group per element.
        let writes = [
            w(0, 2, "slice_u16", 1),
            w(0, 2, "u16", 1),
            w(0, 2, REGION_VIEW_KEY, 1),
            w(2, 4, "slice_u16", 2),
            w(2, 4, "u16", 2),
            w(2, 4, REGION_VIEW_KEY, 2),
            // An element store `bx[1] = 5`.
            w(2, 4, "slice_u16", 3),
            w(2, 4, "u16", 3),
            w(2, 4, REGION_VIEW_KEY, 3),
        ];
        let read = |lo, hi, key| classify_read(&writes, Some(ViewSpan::new(lo, Some(hi))), key);
        assert_eq!(read(2, 4, "slice_u16"), ViewReadClass::Exact);
        assert_eq!(read(0, 2, "u16"), ViewReadClass::Exact);
        assert_eq!(classify_read(&writes, None, "slice_u16"), ViewReadClass::Exact);
    }

    #[test]
    fn a_wide_read_of_narrow_stores_is_unwritten() {
        let writes = [w(0, 2, "u16", 1), w(2, 4, "u16", 2)];
        let span = Some(ViewSpan::new(0, Some(4)));
        assert_eq!(classify_read(&writes, span, "u32"), ViewReadClass::Unwritten);
    }

    #[test]
    fn a_wide_store_makes_the_element_view_stale() {
        let writes = [w(0, 2, "slice_u16", 1), w(2, 4, "slice_u16", 2), w(0, 4, "u32", 3)];
        let span = Some(ViewSpan::new(2, Some(4)));
        assert_eq!(classify_read(&writes, span, "slice_u16"), ViewReadClass::Stale);
        // An index read lands somewhere its own view was written, and there
        // the wide store overlaps it.
        assert_eq!(classify_read(&writes, None, "slice_u16"), ViewReadClass::Stale);
    }

    #[test]
    fn disjoint_fields_do_not_interfere() {
        // A struct `{ n: u8, b: u32 }`: the field stores do not overlap.
        let writes = [w(0, 1, "u8", 1), w(4, 8, "u32", 2), w(4, 8, "u32", 3)];
        assert_eq!(
            classify_read(&writes, Some(ViewSpan::new(4, Some(8))), "u32"),
            ViewReadClass::Exact
        );
        assert_eq!(classify_read(&writes, None, "u32"), ViewReadClass::Exact);
    }

    #[test]
    fn a_zero_fill_then_a_typed_store_makes_bytes_stale() {
        let writes = [
            w(0, 4, "u8", 1),
            w(0, 4, "u16", 1),
            w(0, 4, REGION_VIEW_KEY, 1),
            w(2, 4, "u16", 2),
            w(2, 4, "slice_u16", 2),
        ];
        assert_eq!(
            classify_read(&writes, Some(ViewSpan::new(2, Some(3))), "u8"),
            ViewReadClass::Stale
        );
        assert_eq!(
            classify_read(&writes, Some(ViewSpan::new(0, Some(2))), "slice_u16"),
            ViewReadClass::Unwritten
        );
    }

    #[test]
    fn a_later_store_of_the_key_masks_an_earlier_one() {
        // A realloc's copy (group 1) that did not copy `slice_u16`, then an
        // element store (group 2) writing it: stale unless the store masks
        // the copy on the way to the read.
        let writes = [
            w(0, 4, "u16", 1),
            w(0, 4, REGION_VIEW_KEY, 1),
            w(2, 4, "slice_u16", 2),
            w(2, 4, "u16", 2),
            w(2, 4, REGION_VIEW_KEY, 2),
        ];
        let span = Some(ViewSpan::new(2, Some(4)));
        assert_eq!(classify_read(&writes, span, "slice_u16"), ViewReadClass::Stale);
        // Write 2 (the element store's `slice_u16`) masks the copy's writes.
        let masks = |w: usize, x: usize, _lo: u64, _hi: u64| w == 2 && writes[x].2 == (1, 0);
        assert_eq!(classify_read_masked(&writes, span, "slice_u16", &masks), ViewReadClass::Exact);
        // Masking never applies to bytes the masking store does not cover.
        let span = Some(ViewSpan::new(0, Some(2)));
        assert_eq!(
            classify_read_masked(&writes, span, "slice_u16", &masks),
            ViewReadClass::Unwritten
        );
    }

    #[test]
    fn an_open_ended_write_covers_the_rest() {
        let writes = [w(0, 2, "slice_u16", 1), (ViewSpan::new(0, None), "u8", (2, 0))];
        assert_eq!(
            classify_read(&writes, Some(ViewSpan::new(0, Some(2))), "slice_u16"),
            ViewReadClass::Stale
        );
    }
}
