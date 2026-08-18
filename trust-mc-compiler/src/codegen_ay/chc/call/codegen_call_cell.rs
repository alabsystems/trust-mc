// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `Cell`/`RefCell` interior-mutability method handlers for CHC encoding.
//!
//! `Cell<T>` and `RefCell<T>` are `#[repr(transparent)]` over `UnsafeCell<T>`,
//! so `&Cell<T>` / `&RefCell<T>` and `&UnsafeCell<T>` share an address. Their
//! accessor methods (`get`/`set`/`replace`/`take`/`replace_with`) deep-inline
//! their std bodies (`Cell::set` -> `replace` -> `mem::replace` -> `ptr` ops)
//! into a large memory query that the solver returns UNKNOWN/fabricated-CTREX
//! on. This module intercepts those methods and emits a *direct* load/store at
//! the referent's real memory-mirror address, so constant-address
//! store-to-load forwarding prunes the memory array and the solver proves fast.
//!
//! Address recovery has two routes and they do NOT carry the same evidence.
//! Route 1 reuses [`ChcCtx::recover_unsafe_cell_referent_address`] (the shipped
//! fc-interior-mut cascade), which mints a real `(obj_id, offset)` — a
//! [`crate::codegen_ay::provenance::Loc`] from a producer, reported as
//! [`MaybeLoc::Known`]. Route 2 is the closure-inlined-contract fallback and
//! takes whatever `translate_operand_with_modified` returned for a
//! pointer-TYPED operand; that function reports nothing about what it produced,
//! so route 2 answers [`MaybeLoc::Unknown`] and its load/store go through the
//! `#[deprecated]` untyped shims. The module used to claim "the address is
//! always a real `(obj_id, offset)` or the handler FAILS CLOSED"; that is true
//! of route 1 and was never established for route 2, whose filters (MIR type
//! denotes an address, `T` narrower than a pointer, not a widened narrow datum)
//! exclude every non-address lane known here but are not a producer's report.
//! See `recover_cell_referent_address` for the exact split.
//!
//! REPRESENTATION COHERENCE (the vacuous-ensures trap): every access this
//! module models — the mutating stores (`set`/`replace`/`take`/`replace_with`),
//! the value reads (`get`), and the pointer identity (`as_ptr`, whose `*dest`
//! deref is the contract read) — lands on the SAME memory-mirror lane at the
//! SAME recovered `(obj_id, offset)`. `as_ptr` deliberately binds its result as
//! a plain split-pointer VALUE (never a `call_forwarded_raw_ptr`), so the
//! contract's deref cannot escape to the flattened state-var lane the store
//! never updates. Interception is all-or-nothing per call: a declined call does
//! NOT fall to deep-inline — the dispatch layer routes declines to the
//! fail-closed Cell quarantine (`cell_accessor_semantics_quarantined`), which
//! havocs the destination and forces any solver Success to Unknown at the
//! publication boundary.
//!
//! REFCELL BORROW STATE: the borrow flag is NOT modeled here. `replace` and
//! `replace_with` panic when a borrow is live, so intercepting them (skipping
//! the flag check) is only sound when no borrow guard can exist in the modeled
//! execution. Guards are only ever produced by `borrow`/`borrow_mut`/
//! `try_borrow*`, whose (deep-inlined) bodies materialize guard-typed locals
//! (`core::cell::Ref`/`RefMut`/`BorrowRef`/`BorrowRefMut`) in the translated
//! body. [`ChcCtx::body_has_refcell_borrow_guards`] scans for those locals;
//! when any exist, `refcell_mutator_must_fail_close` declines the interception
//! and the call fails closed at the quarantine (never a silently-skipped
//! borrow panic).
//!
//! Sibling of `codegen_call_unsafe_cell.rs`. Part of the fc-interior-mut
//! cluster (whole-struct/cell, api/cell, whole-struct/refcell).

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::provenance::{MaybeLoc, Val, mir_ty_denotes_address};
use crate::codegen_ay::ptr_repr::PtrSlot;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::heap::is_value_widened_into_address;
use super::ChcCtx;
use super::chc_call_context::CallEmitContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::ptr_receiver_mem;

/// Split a canonical standard-library `cell` path into its post-type suffix.
/// Returns `(suffix, is_refcell)` for `core::cell::Cell`/`std::cell::Cell` and
/// `core::cell::RefCell`/`std::cell::RefCell` paths ONLY — user types whose
/// path merely contains `cell::Cell` (e.g. `my_crate::cell::Cellar`) never
/// match (the quarantine session's exact-matching hygiene).
fn canonical_cell_suffix(path: &str) -> Option<(&str, bool)> {
    const PREFIXES: [(&str, bool); 4] = [
        ("core::cell::RefCell", true),
        ("std::cell::RefCell", true),
        ("core::cell::Cell", false),
        ("std::cell::Cell", false),
    ];
    for (prefix, is_refcell) in PREFIXES {
        if let Some(suffix) = path.strip_prefix(prefix)
            && (suffix.starts_with("::") || suffix.starts_with('<'))
        {
            return Some((suffix, is_refcell));
        }
    }
    None
}

/// The interior-mutability method being modeled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum CellMethod {
    /// `Cell::get(&self) -> T` — `load(addr)`.
    Get,
    /// `Cell::set(&self, v)` — `store(addr, v)`.
    Set,
    /// `Cell::replace(&self, v) -> T` / `RefCell::replace(&self, v) -> T` —
    /// `old = load(addr); store(addr, v); old`.
    Replace,
    /// `Cell::take(&self) -> T` (T: Default) — for integer/bool T only:
    /// `old = load(addr); store(addr, 0); old`.
    Take,
    /// `RefCell::replace_with(&self, f) -> T` —
    /// `old = load(addr); new = f(&mut old); store(addr, new); old`.
    ReplaceWith,
    /// `Cell::as_ptr(&self) -> *mut T` / `RefCell::as_ptr(&self) -> *mut T` —
    /// pointer-to-interior identity: `dest = recovered referent address`. The
    /// subsequent `*dest` contract read then loads from the SAME memory-mirror
    /// address the `set`/`replace`/`replace_with` store wrote to
    /// (read-observes-store). Unlike the `UnsafeCell::get` handler, the result
    /// is a plain split-pointer value — NOT a `call_forwarded_raw_ptr` — so its
    /// deref stays on the memory lane (where the Cell store lands) rather than
    /// the register/state-var lane.
    AsPtr,
}

/// Extension trait for Cell/RefCell method call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallCell {
    /// Detect a supported `Cell`/`RefCell` accessor method by callee def-path.
    fn detect_cell_method(&self, func: &Operand) -> Option<CellMethod>;

    /// Whether an intercepted `RefCell` mutator must be declined because the
    /// skipped borrow-flag panic check could hide a real `already borrowed`
    /// panic (a borrow guard exists somewhere in the translated body).
    fn refcell_mutator_must_fail_close(&self, func: &Operand, method: CellMethod) -> bool;

    /// Model a `Cell`/`RefCell` accessor as a direct load/store at the recovered
    /// referent address. Returns `true` when handled; `false` to FAIL CLOSED
    /// (address unrecoverable / operand unresolved) so the caller falls through
    /// to the fail-closed Cell quarantine.
    fn codegen_call_cell_method(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        method: CellMethod,
    ) -> bool;
}

impl<'tcx, 'body> CallCell for ChcCtx<'tcx, 'body> {
    fn detect_cell_method(&self, func: &Operand) -> Option<CellMethod> {
        let p = self.resolve_callee_path(func)?;
        let (_, is_refcell) = canonical_cell_suffix(&p)?;
        let is_cell = !is_refcell;
        // Order matters: `::replace_with` must be checked before `::replace`.
        if p.ends_with("::replace_with") {
            // Only RefCell::replace_with exists in std; accept for either
            // wrapper defensively.
            Some(CellMethod::ReplaceWith)
        } else if p.ends_with("::replace") {
            Some(CellMethod::Replace)
        } else if p.ends_with("::as_ptr") {
            // Both `Cell::as_ptr` and `RefCell::as_ptr` exist; the interior
            // address is identical (repr(transparent) over UnsafeCell).
            Some(CellMethod::AsPtr)
        } else if is_cell && p.ends_with("::get") {
            Some(CellMethod::Get)
        } else if is_cell && p.ends_with("::set") {
            Some(CellMethod::Set)
        } else if is_cell && p.ends_with("::take") {
            Some(CellMethod::Take)
        } else {
            None
        }
    }

    fn refcell_mutator_must_fail_close(&self, func: &Operand, method: CellMethod) -> bool {
        if !matches!(method, CellMethod::Replace | CellMethod::ReplaceWith) {
            return false;
        }
        let is_refcell = self
            .resolve_callee_path(func)
            .and_then(|p| canonical_cell_suffix(&p).map(|(_, is_refcell)| is_refcell))
            .unwrap_or(false);
        is_refcell && self.body_has_refcell_borrow_guards()
    }

    fn codegen_call_cell_method(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        method: CellMethod,
    ) -> bool {
        let Some(self_arg) = ecx.args.first() else {
            return false;
        };

        // REGISTER-MIRROR MOVE HAZARD (the quarantine's coherence trap,
        // empirically confirmed by the move-after-set dual): this lane stores
        // on the memory-mirror lane only, while a BY-VALUE move of the cell
        // (or its containing struct) copies the local's register mirror —
        // stale after an intercepted store — and re-materializes it as a new
        // object the moved-to reads observe. Any body where a cell-carrying
        // value is both address-exposed (so cell ops target its memory
        // mirror) and moved by value must fail closed entirely.
        if self.cell_lane_register_move_hazard() {
            debug!(bb_idx, ?method, "cell: register-move hazard in body — fail-closed");
            return false;
        }

        // The wrapped value type `T` drives the memory-array type key AND the
        // address-recovery width gate. For value-taking methods it is the
        // argument type; for value-returning methods it is the destination type.
        let value_ty = match method {
            CellMethod::Set | CellMethod::Replace => {
                ecx.args.get(1).and_then(|a| a.ty(self.body.locals()).ok())
            }
            CellMethod::Get | CellMethod::Take | CellMethod::ReplaceWith => {
                ecx.destination.ty(self.body.locals()).ok()
            }
            // `as_ptr` returns `*mut T`; the wrapped value type `T` (the pointee)
            // drives the address-recovery width gate.
            CellMethod::AsPtr => ecx.destination.ty(self.body.locals()).ok().and_then(|dest_ty| {
                match dest_ty.kind() {
                    TyKind::RigidTy(RigidTy::RawPtr(t, _) | RigidTy::Ref(_, t, _)) => Some(t),
                    _ => None,
                }
            }),
        };
        let Some(value_ty) = value_ty else {
            debug!(bb_idx, ?method, "cell: value type unresolved — fail-closed");
            return false;
        };

        // Recover the referent's REAL memory-mirror address. This is the sole
        // fail-closed gate: an unrecoverable address means we decline the call
        // (return false) so the fail-closed quarantine runs — never a store
        // to a fabricated address.
        let Some(addr) =
            self.recover_cell_referent_address(self_arg, ecx.modified_locals, value_ty)
        else {
            debug!(bb_idx, ?method, "cell: address unrecoverable — fail-closed");
            return false;
        };

        match method {
            CellMethod::Get => self.emit_cell_get(bb_idx, ecx, addr, value_ty),
            CellMethod::Set => self.emit_cell_set(bb_idx, ecx, addr, value_ty),
            CellMethod::Replace => self.emit_cell_replace(bb_idx, ecx, addr, value_ty),
            CellMethod::Take => self.emit_cell_take(bb_idx, ecx, addr, value_ty),
            CellMethod::ReplaceWith => self.emit_cell_replace_with(bb_idx, ecx, addr, value_ty),
            CellMethod::AsPtr => self.emit_cell_as_ptr(bb_idx, ecx, addr),
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether any local in the translated body has a type mentioning a
    /// `RefCell` borrow-guard (`core::cell::Ref`/`RefMut`/`BorrowRef`/
    /// `BorrowRefMut`), including nested inside references, tuples, arrays or
    /// generic arguments (e.g. `Result<RefMut<T>, BorrowMutError>` from
    /// `try_borrow_mut`).
    ///
    /// Guards can only be created by `borrow`/`borrow_mut`/`try_borrow*`,
    /// whose deep-inlined bodies materialize guard-typed locals in this body.
    /// If none exist, no borrow can be live at any intercepted
    /// `replace`/`replace_with` call, so skipping the borrow-flag panic check
    /// is sound. Conservative in the fail-closed direction: any mention —
    /// live or not — declines the interception.
    pub(in crate::codegen_ay::chc) fn body_has_refcell_borrow_guards(&self) -> bool {
        fn is_guard_adt_name(name: &str) -> bool {
            let canonical =
                name.strip_prefix("core::cell::").or_else(|| name.strip_prefix("std::cell::"));
            matches!(canonical, Some("Ref" | "RefMut" | "BorrowRef" | "BorrowRefMut"))
        }
        fn ty_mentions_guard(ty: Ty, depth: u8) -> bool {
            if depth == 0 {
                // Unresolvably deep nesting: fail closed (treat as guard).
                return true;
            }
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                    if is_guard_adt_name(&def.name()) {
                        return true;
                    }
                    args.0.iter().any(|arg| match arg {
                        GenericArgKind::Type(t) => ty_mentions_guard(*t, depth - 1),
                        _ => false,
                    })
                }
                TyKind::RigidTy(
                    RigidTy::Ref(_, t, _) | RigidTy::RawPtr(t, _) | RigidTy::Slice(t),
                ) => ty_mentions_guard(t, depth - 1),
                TyKind::RigidTy(RigidTy::Array(t, _)) => ty_mentions_guard(t, depth - 1),
                TyKind::RigidTy(RigidTy::Tuple(ts)) => {
                    ts.iter().any(|t| ty_mentions_guard(*t, depth - 1))
                }
                _ => false,
            }
        }
        self.body.locals().iter().any(|decl| ty_mentions_guard(decl.ty, 8))
    }

    /// Whether the translated body both address-exposes and MOVES (by value)
    /// some `Cell`/`RefCell`-carrying local — the register-mirror coherence
    /// hazard for the memory-lane cell handlers.
    ///
    /// An intercepted store writes ONLY the memory mirror at the referent's
    /// `(obj_id, offset)`. A subsequent by-value move of the cell (or a struct
    /// containing it) copies the local's REGISTER mirror — still holding the
    /// pre-store value — and the moved-to local's reads observe that stale
    /// copy: a false Safe (`move_after_set` dual). Construction shapes
    /// (`Cell::new` temp moved into an aggregate) are unaffected: the moved
    /// temp is never address-exposed, so no intercepted op ever targeted its
    /// memory mirror.
    ///
    /// Conservative in the fail-closed direction: ANY (exposed ∧ moved)
    /// cell-carrying local declines the whole body's cell interceptions
    /// (dispatch then routes every canonical cell op to the quarantine).
    pub(in crate::codegen_ay::chc) fn cell_lane_register_move_hazard(&self) -> bool {
        use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};

        /// Whether moving a value of `ty` relocates `Cell`/`RefCell` payload
        /// BYTES (as opposed to copying a pointer to them). Stops at
        /// references/raw pointers: moving `&Cell<T>` copies an address, the
        /// cell stays put. Recurses through value containers (ADT generic
        /// args, tuples, arrays); over-approximates for pointer-like ADTs
        /// (e.g. `Box<Cell<T>>`), which only costs a sound decline.
        fn ty_moves_cell_payload(ty: Ty, depth: u8) -> bool {
            if depth == 0 {
                return true; // unresolvably deep: fail closed
            }
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                    let name = def.name();
                    let canonical = name
                        .strip_prefix("core::cell::")
                        .or_else(|| name.strip_prefix("std::cell::"));
                    if matches!(canonical, Some("Cell" | "RefCell")) {
                        return true;
                    }
                    args.0.iter().any(|arg| match arg {
                        GenericArgKind::Type(t) => ty_moves_cell_payload(*t, depth - 1),
                        _ => false,
                    })
                }
                TyKind::RigidTy(RigidTy::Tuple(ts)) => {
                    ts.iter().any(|t| ty_moves_cell_payload(*t, depth - 1))
                }
                TyKind::RigidTy(RigidTy::Array(t, _) | RigidTy::Slice(t)) => {
                    ty_moves_cell_payload(t, depth - 1)
                }
                // Moving a reference/raw pointer copies the ADDRESS; the
                // pointee cell does not relocate.
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => false,
                _ => false,
            }
        }

        let locals = self.body.locals();
        let mut exposed: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut moved_cell_locals: std::collections::HashSet<usize> =
            std::collections::HashSet::new();
        let note_moved_operand = |op: &Operand, moved: &mut std::collections::HashSet<usize>| {
            if let Operand::Move(p) = op
                && let Ok(ty) = p.ty(locals)
                && ty_moves_cell_payload(ty, 8)
            {
                moved.insert(p.local);
            }
        };

        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else {
                    continue;
                };
                match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        exposed.insert(place.local);
                    }
                    Rvalue::Use(op)
                    | Rvalue::Repeat(op, _)
                    | Rvalue::Cast(_, op, _)
                    | Rvalue::ShallowInitBox(op, _) => {
                        note_moved_operand(op, &mut moved_cell_locals);
                    }
                    Rvalue::Aggregate(_, operands) => {
                        for op in operands {
                            note_moved_operand(op, &mut moved_cell_locals);
                        }
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { args, .. } = &block.terminator.kind {
                for op in args {
                    note_moved_operand(op, &mut moved_cell_locals);
                }
            }
        }
        moved_cell_locals.iter().any(|local| exposed.contains(local))
    }

    /// Recover the referent address for a `Cell`/`RefCell` `&self` receiver.
    ///
    /// Two sound routes, tried in order:
    /// 1. The canonical `(obj_id, offset)` memory-mirror address via
    ///    ref-resolution ([`ChcCtx::recover_unsafe_cell_referent_address`]).
    ///    The method body's `set`/`replace` store uses this route.
    /// 2. Fallback for closure-inlined contract reads (the `ensures`/`requires`
    ///    `im.x.get()`): those live in a separately-inlined closure body whose
    ///    internal `&self` reference has NO `ref_targets` entry, so route 1
    ///    fails. Here the reference's own translated value IS a genuine
    ///    pointer-width address, so use it directly — but ONLY when the wrapped
    ///    value type `T` is strictly narrower than a pointer. That width gate is
    ///    the soundness guarantee: for `T` narrower than `POINTER_WIDTH`, a
    ///    dematerialized `bvN` payload (the fc-interior-mut hazard) can never be
    ///    `bv64`, so anything passing the `== POINTER_WIDTH` filter is a real
    ///    reference value, never a value-as-address fabrication. For `T` at or
    ///    above pointer width, route 2 is skipped (recover-only, else
    ///    fail-closed) since payload and address become width-indistinguishable.
    ///
    /// Address-vs-value refactor: route 1 threads a [`Loc`] straight through
    /// from the producer, so it answers [`MaybeLoc::Known`]. Route 2 has no
    /// producer to thread from and answers [`MaybeLoc::Unknown`] — see the
    /// comment on the `.map(MaybeLoc::Unknown)` below for exactly what it does
    /// and does not establish.
    fn recover_cell_referent_address(
        &mut self,
        arg: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
        value_ty: Ty,
    ) -> Option<MaybeLoc> {
        if let Some(addr) = self.recover_unsafe_cell_referent_address(arg, modified_locals) {
            // Route 1 is an address PRODUCER: `(obj_id, offset)` built by the
            // encoder's own ref-resolution cascade, threaded through as a `Loc`.
            return Some(MaybeLoc::Known(addr));
        }
        // Route 2 width gate.
        let t_width = Self::translate_ty(value_ty).and_then(|s| s.bitvec_width());
        if t_width.is_none_or(|w| w >= POINTER_WIDTH) {
            return None;
        }
        // Route 2 MIR-TYPE PREMISE. The doc above has always *claimed* that the
        // operand is "address-BY-TYPE" — a `&Cell<T>` receiver — but nothing
        // checked it, so the tag below rested on a width test alone for any
        // operand shape the dispatcher happened to route here. The claim is
        // decidable at exactly this point: the operand's own Rust type either is
        // a reference / raw pointer / pointer wrapper or it is not, and
        // `mir_ty_denotes_address` is the whitelist that says so (`provenance.rs`).
        // A non-pointer operand has no address anywhere in it, and no width test
        // on its translation could have found one.
        let arg_ty = arg.ty(self.body.locals()).ok().map(|ty| self.resolve_body_ty(ty))?;
        if !mir_ty_denotes_address(arg_ty) {
            debug!(?arg_ty, "cell referent recovery: operand is not pointer-typed — declined");
            return None;
        }
        // Shape half: one machine word, and not a narrow datum that some
        // earlier coercion widened into that slot. `PtrSlot` states the first
        // (a classification of the sort, `ptr_repr.rs`) and
        // `is_value_widened_into_address` the second; neither decides
        // provenance, which the MIR-type requirement above supplies.
        let is_thin_ptr = |expr: &Expr| {
            PtrSlot::of_sort(expr.sort()) == Some(PtrSlot::Thin)
                && !is_value_widened_into_address(expr)
        };
        // WHY THIS IS `Unknown` AND NOT A `Loc`.
        //
        // Established here: (1) the operand's MIR type denotes an address (just
        // required above); (2) `T` is strictly narrower than `POINTER_WIDTH`
        // (the gate above), so the two known ways this path can be handed a
        // NON-address are excluded by shape — the fc-interior-mut lane
        // dematerializes `&Cell<T>` into the referent's flattened `bvN` payload,
        // and `resolve_ref_operand` returns the REFERENT (`Cell<T>`, i.e. that
        // same `bvN`), neither of which can be `bv64` when `T` is narrower;
        // (3) the term is not a widened narrow datum (`is_value_widened_into_address`).
        //
        // NOT established, and not establishable at this site:
        // `translate_operand_with_modified` serves every operand in the encoder
        // and reports nothing about what it returned, so a lane other than those
        // two that yields a pointer-width non-address from a pointer-TYPED
        // operand still passes. Three facts and a shape test are a strong
        // *filter*; they are not a producer's report, and `Loc::of_address` here
        // would assert one — the laundering this campaign exists to remove. The
        // answer is therefore `MaybeLoc::Unknown`: the caller gets exactly the
        // term it got before and the encoding is unchanged, but the doubt now
        // travels with it and its load/store sit on the `#[deprecated]` untyped
        // shims, which is the campaign's marker for "no honest `Loc` exists
        // here" (see `codegen_ay/provenance.rs`, "Two shims are alive on
        // purpose" — this operand-translator tail is named there).
        //
        // Closing it needs the operand translator itself to return a `MaybeLoc`
        // (§4 item 10), not a wider guard here. Refusing instead is a coverage
        // change, not a retyping: `recover_cell_referent_address` returning
        // `None` declines the whole interception into the fail-closed Cell
        // quarantine, so it has to be measured against the burndown.
        self.translate_operand_with_modified(arg, modified_locals)
            .filter(is_thin_ptr)
            .or_else(|| self.resolve_ref_operand(arg, modified_locals).filter(is_thin_ptr))
            .map(MaybeLoc::Unknown)
    }

    /// Load a cell referent through an address whose provenance may be
    /// unreported.
    ///
    /// Route 1 ([`MaybeLoc::Known`]) takes the typed keystone. Route 2
    /// ([`MaybeLoc::Unknown`]) stays on the `#[deprecated]` untyped entry on
    /// purpose: re-tagging it as a [`Loc`] would launder a claim
    /// `translate_operand_with_modified` never made.
    fn cell_load_through(&mut self, addr: &MaybeLoc, value_ty: Ty) -> Option<Expr> {
        match addr {
            MaybeLoc::Known(loc) => {
                self.load_from_memory(loc.clone(), value_ty).map(Val::into_expr)
            }
            MaybeLoc::Unknown(expr) =>
            {
                #[allow(deprecated)]
                self.load_from_memory_untyped(expr.clone(), value_ty)
            }
        }
    }

    /// Store to a cell referent through an address whose provenance may be
    /// unreported. Same split, and same reason, as [`Self::cell_load_through`].
    fn cell_store_through(&mut self, addr: &MaybeLoc, value: Expr, value_ty: Ty) -> Option<Expr> {
        match addr {
            MaybeLoc::Known(loc) => self.build_memory_store(loc.clone(), value, value_ty),
            MaybeLoc::Unknown(expr) =>
            {
                #[allow(deprecated)]
                self.build_memory_store_untyped(expr.clone(), value, value_ty)
            }
        }
    }

    /// Drain the heap-access checks queued by a call-terminator load/store into
    /// per-property error rules (call terminators bypass the statement-level
    /// drain — mirrors `ptr_receiver_mem::drain_pending_checks`).
    fn drain_cell_pending_checks(&mut self, ecx: &CallEmitContext<'_>) {
        for check in self.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
            self.emit_error_rule_for_condition(
                ecx.from_app,
                check,
                ecx.stmt_constraints,
                ecx.target,
            );
        }
    }

    /// `Cell::get(&self) -> T` — dest = load(addr) as T.
    fn emit_cell_get(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value_ty: Ty,
    ) -> bool {
        let dest_local = ecx.destination.local;
        let Some(loaded) = self.cell_load_through(&addr, value_ty) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::get load failed — fail-closed");
            return false;
        };
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            self.drain_cell_pending_checks(ecx);
            return false;
        };
        let s = dest_var.sort().clone();
        let eq = self.make_coerced_eq_constraint(&dest_var, loaded, &s, dest_local, "cell::get");
        let out = self.build_output_args(ecx.modified_locals, &[dest_local]);
        self.drain_cell_pending_checks(ecx);
        if let Some(eq) = eq {
            self.emit_goto_rule_extra(ecx.from_app, ecx.target, &out, ecx.stmt_constraints, [eq]);
        } else {
            self.emit_goto_rule(ecx.from_app, ecx.target, &out, ecx.stmt_constraints);
        }
        debug!(bb_idx, dest_local, "cell::get modeled as direct load(addr)");
        true
    }

    /// `Cell::as_ptr(&self) -> *mut T` / `RefCell::as_ptr(&self) -> *mut T` —
    /// `dest = recovered referent address`.
    ///
    /// The result is the referent's real memory-mirror `(obj_id, offset)`
    /// address — the SAME address `set`/`replace`/`replace_with` store to. The
    /// subsequent `*dest` contract read then loads from that memory address and
    /// observes the interior-mutable store (read-observes-store).
    ///
    /// Soundness: `dest` is bound as a plain split-pointer VALUE (not forwarded
    /// through `ref_targets` / `call_forwarded_raw_ptrs`), so its deref stays on
    /// the memory lane — the lane the Cell store writes — rather than the
    /// register/state-var lane (which the store never updates, the vacuous-proof
    /// trap). `record_known_stack_addr_expr` pins the concrete stack provenance
    /// so the deref resolves the identical `(obj_id, offset)` when the address is
    /// a constant stack pointer; if the bind is refused (narrow-to-pointer
    /// widening guard), the destination stays havoced and downstream checks
    /// remain fail-closed — never a value-as-address fabrication.
    fn emit_cell_as_ptr(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
    ) -> bool {
        let dest_local = ecx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let s = dest_var.sort().clone();
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            addr.as_addr_expr().clone(),
            &s,
            dest_local,
            "cell::as_ptr",
        ) else {
            debug!(bb_idx, "cell::as_ptr address bind refused — fail-closed");
            return false;
        };
        // Pin concrete stack provenance (no-op unless `addr` is a constant naming
        // a tracked stack object) so the `*dest` deref resolves the identical
        // (obj_id, offset) instead of re-deriving it symbolically.
        self.record_known_stack_addr_expr(
            dest_local,
            addr.into_addr_expr(),
            "cell_as_ptr_referent_recovery",
        );
        let out = self.build_output_args(ecx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(ecx.from_app, ecx.target, &out, ecx.stmt_constraints, [eq]);
        debug!(bb_idx, dest_local, "cell::as_ptr modeled as referent-address identity");
        true
    }

    /// `Cell::set(&self, v)` — store(addr, v). Returns unit.
    fn emit_cell_set(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value_ty: Ty,
    ) -> bool {
        let Some(value) = ecx
            .args
            .get(1)
            .and_then(|arg| self.translate_operand_with_modified(arg, ecx.modified_locals))
        else {
            debug!(bb_idx, "cell::set value unresolved — fail-closed");
            return false;
        };
        self.emit_cell_store_and_return(bb_idx, ecx, addr, value, value_ty, None, "cell::set")
    }

    /// `Cell::replace(&self, v) -> T` / `RefCell::replace(&self, v) -> T` —
    /// old = load(addr); store(addr, v); dest = old.
    fn emit_cell_replace(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value_ty: Ty,
    ) -> bool {
        let Some(value) = ecx
            .args
            .get(1)
            .and_then(|arg| self.translate_operand_with_modified(arg, ecx.modified_locals))
        else {
            debug!(bb_idx, "cell::replace value unresolved — fail-closed");
            return false;
        };
        // Load the OLD value BEFORE accumulating the store, so the returned
        // value reflects pre-store memory.
        let Some(old) = self.cell_load_through(&addr, value_ty) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::replace old-load failed — fail-closed");
            return false;
        };
        self.emit_cell_store_and_return(
            bb_idx,
            ecx,
            addr,
            value,
            value_ty,
            Some(old),
            "cell::replace",
        )
    }

    /// `Cell::take(&self) -> T` (T: Default) — integer/bool T only:
    /// old = load(addr); store(addr, 0); dest = old.
    fn emit_cell_take(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value_ty: Ty,
    ) -> bool {
        // `Default::default()` is `0` only for integer/bool T. Any other T is
        // not soundly zeroable here — FAIL CLOSED to the quarantine.
        let Some(zero) = self.zeroable_default_expr(value_ty) else {
            debug!(bb_idx, "cell::take non-zeroable T — fail-closed");
            return false;
        };
        let Some(old) = self.cell_load_through(&addr, value_ty) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::take old-load failed — fail-closed");
            return false;
        };
        self.emit_cell_store_and_return(bb_idx, ecx, addr, zero, value_ty, Some(old), "cell::take")
    }

    /// `RefCell::replace_with(&self, f) -> T` —
    /// old = load(addr); new = f(&mut old); store(addr, new); dest = old.
    ///
    /// The borrow-flag runtime check is not modeled HERE; instead the dispatch
    /// gate (`refcell_mutator_must_fail_close`) declines the interception
    /// whenever any borrow guard exists in the translated body, so a skipped
    /// `already borrowed` panic is unreachable in every intercepted execution.
    /// `f` is resolved via the shared closure inline lane; if it cannot be
    /// resolved/inlined, FAIL CLOSED.
    fn emit_cell_replace_with(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value_ty: Ty,
    ) -> bool {
        let Some(closure_arg) = ecx.args.get(1) else {
            return false;
        };
        // Load OLD before the store; it is both the closure's `&mut T` argument
        // (Deref-as-identity in the inline walker) and the returned value.
        let Some(old) = self.cell_load_through(&addr, value_ty) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::replace_with old-load failed — fail-closed");
            return false;
        };
        let Some(closure_body) = super::codegen_call_closure::resolve_closure_body_for_operand(
            self.tcx,
            closure_arg,
            self.body.locals(),
        ) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::replace_with closure body unresolved — fail-closed");
            return false;
        };
        let captures = self.extract_closure_env_captures(closure_arg, ecx.modified_locals);
        let Some(new_value) = super::inline_body::translate_closure_inline_body(
            self,
            &closure_body,
            &[old.clone()],
            &captures,
            bb_idx,
            0,
        ) else {
            self.drain_cell_pending_checks(ecx);
            debug!(bb_idx, "cell::replace_with closure inline failed — fail-closed");
            return false;
        };
        self.emit_cell_store_and_return(
            bb_idx,
            ecx,
            addr,
            new_value,
            value_ty,
            Some(old),
            "cell::replace_with",
        )
    }

    /// Shared store-and-emit epilogue: accumulate `store(addr, value)` into the
    /// heap store chains, optionally bind `dest = old`, thread the modified
    /// arrays through the output args, drain heap-access checks, and emit the
    /// goto rule. Mirrors `ptr_receiver_mem::emit_mem_store_transition`.
    fn emit_cell_store_and_return(
        &mut self,
        bb_idx: usize,
        ecx: &CallEmitContext<'_>,
        addr: MaybeLoc,
        value: Expr,
        value_ty: Ty,
        old: Option<Expr>,
        site: &'static str,
    ) -> bool {
        let dest_local = ecx.destination.local;
        // Accumulate the store into heap store chains (returns None on success;
        // constraints are flushed via drain_pending_updates below).
        // `build_memory_store` is still `(Expr, Expr)` — wave 13 retypes it to
        // `(Loc, Val)`, which is what makes the address/value swap at this
        // adjacent-argument site a compile error instead of a silent defect.
        self.cell_store_through(&addr, value, value_ty);

        let mut extra = Vec::new();
        // Bind the value-returning result (`dest = old`) for replace/take/
        // replace_with. `set` returns `()` and passes `old = None`.
        if let Some(old) = old
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            let s = dest_var.sort().clone();
            if let Some(eq) = self.make_coerced_eq_constraint(&dest_var, old, &s, dest_local, site)
            {
                extra.push(eq);
            }
        }
        ptr_receiver_mem::drain_pending_updates(self, &mut extra);
        let out = self.build_output_args(ecx.modified_locals, &[dest_local]);
        self.drain_cell_pending_checks(ecx);
        self.emit_goto_rule_extra(ecx.from_app, ecx.target, &out, ecx.stmt_constraints, extra);
        debug!(bb_idx, dest_local, site, "cell: modeled as direct store(addr, value)");
        true
    }

    /// Zero-value expression for `Default::default()` of an integer/bool
    /// pointee type. Returns `None` for any other type (not soundly zeroable).
    fn zeroable_default_expr(&self, value_ty: Ty) -> Option<Expr> {
        let value_ty = self.resolve_body_ty(value_ty);
        match value_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(Expr::bool_const(false)),
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Char) => {
                let sort = Self::translate_ty(value_ty)?;
                let width = sort.bitvec_width()?;
                Some(Expr::bitvec_const(0u128, width))
            }
            _ => None,
        }
    }
}
