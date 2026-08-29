// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static variable state-var collection for CHC encoding.
//!
//! Part of #428: Scans the MIR body for constant operands with
//! `GlobalAlloc::Static` provenance and creates auxiliary state
//! variables for mutable statics. This enables CHC to model reads
//! and writes through `static mut` references.

use rustc_public::CrateDef;
use rustc_public::mir::alloc::{AllocId, GlobalAlloc};
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use tracing::debug;

use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};

use super::ChcCtx;
use super::codegen_decl_static_alloc::AllocScalar;
use super::codegen_types::CodegenTypes;

/// Part of #4066: Returns true when a static name belongs to the
/// uninit-check shadow memory infrastructure (`-Z uninit-checks`).
///
/// These statics are:
/// - `MEM_INIT_STATE`: Global `MemoryInitializationState` that tracks
///   non-deterministic byte initialization. Since `Is*PtrInitialized`
///   always returns true in trust_mc's CHC encoding, this state is dead.
/// - `ARGUMENT_BUFFER`: Union initialization state tracking across
///   function boundaries. Also dead for the same reason.
///
/// Encoding these statics drags in BV192 typed memory arrays and
/// complex entry-rule constraints that cause the CHC solver to
/// struggle with invariant synthesis (~20s overhead on trivial
/// harnesses like `access_padding_init`).
pub(in crate::codegen_ay::chc) fn is_uninit_shadow_static(name: &str) -> bool {
    name.contains("MEM_INIT_STATE") || name.contains("ARGUMENT_BUFFER")
}

/// Part of #4066: Returns true when a type key identifies an uninit-check
/// shadow memory type that should not generate a typed memory array.
///
/// Type keys matched:
/// - `MemoryInitializationState`: The shadow state tracking type.
/// - Keys containing `kani__mem_init__` or `kani::mem_init::`: ZST function
///   definition types for model functions like `initialize_memory_initialization_state`,
///   `set_ptr_initialized`, `is_ptr_initialized`, etc.
///
/// These types exist only because `-Z uninit-checks` instrumentation adds
/// locals and function references to the MIR. Since the model calls are
/// intercepted as no-ops (Is*PtrInitialized->true, Set*PtrInitialized->noop),
/// their typed memory arrays are dead state.
pub(in crate::codegen_ay::chc) fn is_uninit_shadow_type_key(type_key: &str) -> bool {
    type_key.contains("MemoryInitializationState")
        || type_key.contains("kani__mem_init__")
        || type_key.contains("kani::mem_init::")
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Scans the MIR body for `GlobalAlloc::Static` references and creates
    /// CHC state variables for each unique static found.
    ///
    /// After this pass, `static_ref_to_state_idx` maps each local that holds
    /// a pointer to a static to the state variable vec index for that static's
    /// value. The entry rule initializes these state variables from
    /// `StaticDef::eval_initializer()`.
    ///
    /// Part of #428: Enable CHC encoding of `static mut` accesses.
    pub(in crate::codegen_ay::chc) fn collect_static_state_vars(&mut self) {
        use rustc_public::ty::{ConstantKind, TyConstKind};

        // Part of #3496 Bug C: Dedup by alloc_id, not static_name.
        // Two named statics (FOO, BAR) may alias the same underlying allocation.
        // Using alloc_id as key ensures they share one state variable, so writes
        // through one are visible to reads through the other.
        let mut discovered_statics: Vec<(String, rustc_public::ty::Ty, usize)> = Vec::new(); // (name, ty, vec_idx)
        let mut alloc_to_vec_idx: std::collections::HashMap<AllocId, usize> =
            std::collections::HashMap::new();

        // Collect (dest_local, alloc_id) tuples for second-pass local mapping.
        let mut local_to_alloc: Vec<(usize, AllocId)> = Vec::new();

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                // Match: _N = Use(Constant(ptr_with_static_provenance))
                let const_op = match rhs {
                    Rvalue::Use(Operand::Constant(c)) => c,
                    _ => continue, // external enum: Rvalue
                };

                let mir_const = &const_op.const_;
                // Extract provenance from the constant allocation.
                // We need to handle both ConstantKind variants that can contain allocations.
                let alloc_provenance = match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => {
                        if alloc.provenance.ptrs.is_empty() {
                            continue;
                        }
                        alloc.provenance.clone()
                    }
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(_, alloc) => {
                            if alloc.provenance.ptrs.is_empty() {
                                continue;
                            }
                            alloc.provenance.clone()
                        }
                        _ => continue, // external enum: TyConstKind
                    },
                    _ => continue, // external enum: ConstantKind
                };

                // Check if the provenance points to a GlobalAlloc::Static
                let alloc_id = alloc_provenance.ptrs[0].1.0;
                let GlobalAlloc::Static(static_def) = GlobalAlloc::from(alloc_id) else {
                    continue;
                };

                let static_name = static_def.name();
                let static_ty = static_def.ty();
                let static_def_id =
                    rustc_public::rustc_internal::internal(self.tcx, static_def.def_id());
                let is_mutable_static = self.tcx.is_mutable_static(static_def_id);

                // Part of #4066: skip uninit-check shadow statics entirely.
                // Their model calls are intercepted as no-ops, so the state
                // variables would be dead weight that bloats the encoding.
                if is_uninit_shadow_static(&static_name) {
                    debug!(
                        dest_local = lhs.local,
                        static_name = %static_name,
                        "CHC: skipping uninit-check shadow static (#4066)"
                    );
                    continue;
                }

                debug!(
                    dest_local = lhs.local,
                    static_name = %static_name,
                    ?static_ty,
                    "CHC: found static reference in MIR (#428)"
                );

                // Create state variable if we haven't seen this alloc_id yet.
                // Part of #3496 Bug C: dedup by alloc_id so aliased statics share one var.
                if let std::collections::hash_map::Entry::Vacant(e) =
                    alloc_to_vec_idx.entry(alloc_id)
                {
                    let Some(sort) = Self::translate_ty(static_ty) else {
                        debug!(
                            ?static_ty,
                            static_name = %static_name,
                            "CHC: cannot translate static type, skipping (#428)"
                        );
                        continue;
                    };

                    let vec_idx = self.state_var_mgr.state_vars.len();
                    let in_name =
                        crate::codegen_ay::names::static_var_name(&self.fn_name, &static_name);
                    let out_name = crate::codegen_ay::names::out_name(&in_name);

                    self.push_state_var_pair(&in_name, &out_name, sort.clone());
                    if is_mutable_static {
                        self.ref_resolution.mutable_static_state_idxs.insert(vec_idx);
                    }
                    // A linked C definition can reach an EXPORTED static by
                    // symbol without Rust ever passing it a pointer, so the
                    // foreign-call effect frame has to havoc these. Interior
                    // mutability (`!Freeze`) makes an *immutable* static
                    // writable too, hence the wider predicate.
                    if is_mutable_static
                        || (crate::codegen_ay::foreign_defs::any_c_definitions()
                            && self.ty_has_interior_mut(static_ty))
                    {
                        self.ref_resolution.c_writable_static_state_idxs.insert(vec_idx);
                    }
                    // A `--c-lib` translation unit names an exported object by
                    // LINKER SYMBOL. Record it so the C front-end can resolve
                    // `S` to this slot without matching on the Rust path,
                    // which `#[link_name]` is free to differ from.
                    let foreign_symbol = self.tcx.is_foreign_item(static_def_id).then(|| {
                        self.tcx
                            .codegen_fn_attrs(static_def_id)
                            .symbol_name
                            .unwrap_or_else(|| self.tcx.item_name(static_def_id))
                            .to_string()
                    });
                    if let Some(symbol) = foreign_symbol.clone() {
                        self.ref_resolution.c_symbol_static_state_idx.insert(symbol, vec_idx);
                    }

                    // P2-S1: in a `#[kani::proof_for_contract]` CHECK harness
                    // the contract must hold for ARBITRARY ambient static
                    // state (Kani havocs these via CBMC `--enforce-contract`).
                    // Pinning a `static mut` (or the UnsafeCell parts of an
                    // immutable static) to its initializer is a FAIL-OPEN: a
                    // contract that breaks under some static state falsely
                    // proves. Havoc = simply omit every initializer pin below
                    // (entry pin, referent seeds, pointer-init resolution,
                    // typed-memory mirror). Immutable non-interior-mut
                    // statics and promoted constants remain pinned.
                    // Kani-INTERNAL statics stay pinned: the contract
                    // machinery's #[kanitool::recursion_tracker] reentry flag
                    // must start at its initializer (false) — havocking it
                    // spuriously trips the recursion reentry check
                    // (mutual_recursion_unsound false-positived at the v38
                    // gate). Any kanitool-attributed static is machinery,
                    // never ambient program state.
                    let is_kani_internal_static =
                        crate::kani_middle::attributes::KaniAttributes::for_item(
                            self.tcx,
                            static_def_id,
                        )
                        .is_recursion_tracker();
                    let contract_havoc = self.contract_static_havoc
                        && !is_kani_internal_static
                        && (is_mutable_static || self.ty_has_interior_mut(static_ty));
                    if contract_havoc {
                        debug!(
                            vec_idx,
                            static_name = %static_name,
                            is_mutable_static,
                            "CHC: contract harness — havocking static (P2-S1)"
                        );
                    }

                    // Compute and cache the initial value for the entry rule.
                    // Part of #3496 Phase 5: Use static_init_from_alloc which handles
                    // flattened Datatype array elements correctly (byte-order fix).
                    // Part of #3496: For pointer-typed statics whose allocations contain
                    // provenance (pointers to inner statics), resolve the target to a
                    // concrete address instead of reading raw bytes (which are zero).
                    // A foreign (`extern "C" { static X: T; }`) static has no
                    // MIR initializer body — calling `eval_initializer()` on it
                    // triggers a rustc `span_bug` panic that `.ok()` cannot
                    // catch (SIGABRT/exit 101). Guard it: a foreign static must
                    // be modelled as nondet (it could hold ANY value), which is
                    // exactly the None-path below (static left unconstrained).
                    // NEVER substitute zero here — that would let `assert X != 1`
                    // pass as a FALSE proof.
                    let init_alloc_opt = if self.tcx.is_foreign_item(static_def_id) {
                        None
                    } else {
                        static_def.eval_initializer().ok()
                    };
                    let mut init_expr_opt = init_alloc_opt
                        .as_ref()
                        .and_then(|alloc| self.static_init_from_alloc(alloc, &sort, static_ty));

                    // A foreign static has no MIR initializer — but a
                    // `--c-lib` translation unit may DEFINE the object
                    // (`uint32_t S = 12;`), and that definition IS the initial
                    // value. This is the same dropped input the effect frame
                    // exists for, and pinning it is what `assert!(S == 12)`
                    // needs. Guarded like a call: the C declaration's type must
                    // match the Rust one, and a C global whose initializer did
                    // not fold to a constant pins NOTHING — the static stays
                    // nondet rather than being given a convenient zero.
                    if init_expr_opt.is_none()
                        && let Some(ref symbol) = foreign_symbol
                        && let Some(cglobal) = crate::c_ffi::global(symbol)
                        && let Some(value) = cglobal.init
                        && crate::codegen_ay::c_ffi_check::scalar_ty_matches(
                            &cglobal.ty,
                            static_ty,
                            crate::c_ffi::target(),
                        )
                        && let Some(width) = sort.bitvec_width()
                    {
                        let wrapped =
                            if width >= 128 { value } else { value.rem_euclid(1i128 << width) };
                        debug!(
                            vec_idx,
                            static_name = %static_name,
                            symbol = %symbol,
                            value,
                            "CHC: foreign static pinned to its --c-lib initializer"
                        );
                        init_expr_opt =
                            Some(Val::of_value(ay_bindings::Expr::bitvec_const(wrapped, width)));
                    }
                    let mut seed_metadata = if is_mutable_static || contract_havoc {
                        None
                    } else {
                        init_expr_opt.clone().and_then(|init_expr| {
                            self.static_seed_metadata_for_value(
                                static_ty,
                                init_expr,
                                init_alloc_opt.as_ref(),
                            )
                        })
                    };

                    // If the static is pointer-typed and its allocation has provenance,
                    // the raw bytes are zero (pointer data lives in provenance, not bytes).
                    // Resolve the provenance target to a concrete heap address so that
                    // reads/writes through this pointer reach the correct memory location.
                    // Handles both thin pointers (BV64) and fat pointers (BV128 = data + length).
                    // Part of #4072: fat pointer provenance resolution for &[T] and &str statics.
                    // P2-S1: skipped under contract havoc — resolving the
                    // pointer target (and seeding the target's memory) would
                    // re-pin state the contract must treat as arbitrary.
                    if !contract_havoc
                        // Which pointer shape did `translate_ty` declare for
                        // this static? A *representation* question about the
                        // slot, asked once. Whether the slot holds a pointer at
                        // all is decided on the next line, by the allocation's
                        // own relocation table — not by this width.
                        && let Some(ptr_slot) = PtrSlot::of_sort(&sort)
                        && let Some(ref alloc) = init_alloc_opt
                        && !alloc.provenance.ptrs.is_empty()
                    {
                        let target_alloc_id = alloc.provenance.ptrs[0].1.0;
                        // Derive the pointee type from the static's type
                        // (e.g., &mut i32 → i32, *mut i32 → i32).
                        let pointee_ty = Self::deref_ref_ty(static_ty).0;
                        if !is_mutable_static
                            && let Some(metadata) = self
                                .resolve_pointer_static_seed_metadata(target_alloc_id, pointee_ty)
                        {
                            seed_metadata = Some(metadata);
                        }
                        if let Some(resolved_data_ptr) = self.resolve_pointer_static_init(
                            target_alloc_id,
                            pointee_ty,
                            &static_name,
                            vec_idx,
                        ) {
                            let repr = match ptr_slot {
                                PtrSlot::Thin => Some(PtrRepr::Thin(resolved_data_ptr)),
                                PtrSlot::Fat => {
                                    // The length half lives in the allocation's
                                    // raw bytes just past the relocation; where
                                    // it lands in the packed word is stated by
                                    // `PtrRepr::into_packed`, not restated here.
                                    //
                                    // A read that FAILS means the initializer
                                    // image is shorter than the fat-pointer slot
                                    // — this allocation never carried the
                                    // metadata. Substituting `0` was a DECLARED
                                    // role reporting a length the program never
                                    // computed, and a zero length makes every
                                    // bounds obligation over the referent
                                    // trivially satisfiable: the fabrication
                                    // manufactures a PROOF, not a spurious
                                    // counterexample. Declining leaves the
                                    // static unconstrained, which is booked
                                    // below as `static_init_incomplete` — a
                                    // sound widening.
                                    let ptr_bytes =
                                        (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
                                    Self::read_composite_from_bytes(
                                        &alloc.bytes,
                                        ptr_bytes,
                                        &ay_bindings::Sort::bitvec(
                                            crate::codegen_ay::types::POINTER_WIDTH,
                                        ),
                                    )
                                    .map(|metadata_expr| {
                                        PtrRepr::from_declared_roles(
                                            resolved_data_ptr,
                                            Val::of_value(metadata_expr),
                                        )
                                    })
                                }
                            };
                            // The static's initial VALUE is the pointer it
                            // holds — not the address of the static itself,
                            // which is minted separately below.
                            if let Some(repr) = repr {
                                init_expr_opt =
                                    Some(Val::of_value(AllocScalar::Ptr(repr).into_expr()));
                            }
                        }
                    }

                    if let Some((seed_value, seed_len)) = seed_metadata {
                        self.ref_resolution.static_ref_value_seeds.insert(vec_idx, seed_value);
                        if let Some(seed_len) = seed_len {
                            self.ref_resolution.static_ref_len_seeds.insert(vec_idx, seed_len);
                        }
                    }

                    if contract_havoc {
                        // P2-S1: no entry pin. For an interior-mut IMMUTABLE
                        // static, pin only the Freeze fields (field-precise;
                        // Kani over-approximates by havocking the whole
                        // static). A `static mut` gets no pin at all. This is
                        // intentional contract semantics, NOT an encoding gap:
                        // do not book `static_init_incomplete` (havoc is a
                        // sound widening for the contract obligation).
                        if !is_mutable_static && let Some(ref init_expr) = init_expr_opt {
                            let var_expr = ay_bindings::Expr::var(&*in_name, sort.clone());
                            let mut pins = Vec::new();
                            self.collect_contract_partial_static_pins(
                                static_ty,
                                var_expr,
                                init_expr.as_expr().clone(),
                                &mut pins,
                            );
                            debug!(
                                vec_idx,
                                static_name = %static_name,
                                num_pins = pins.len(),
                                "CHC: partial Freeze-field pins for interior-mut static (P2-S1)"
                            );
                            self.ref_resolution.contract_static_partial_pins.extend(pins);
                        }
                    } else if let Some(ref init_expr) = init_expr_opt {
                        debug!(
                            vec_idx,
                            static_name = %static_name,
                            "CHC: cached initial value for static (#428)"
                        );
                        self.ref_resolution
                            .static_initial_values
                            .insert(vec_idx, init_expr.as_expr().clone());
                    } else if init_alloc_opt.is_some() {
                        // Part of #3447: allocation exists but encoding returned None
                        // (composite type encoding gap). Static left unconstrained.
                        //
                        // AUDIT (task #65): the static's initial value is left
                        // unconstrained (havoc). WIDENING ONLY — the real,
                        // single concrete initializer value is one admitted
                        // instantiation of the unconstrained state, so proofs
                        // over the widened model remain valid; the gap can only
                        // fail or un-conclude harnesses that relied on the
                        // actual value. Plumbed via generate_metadata
                        // (codegen_units.rs) as SOUND_APPROXIMATION — the
                        // driver's Step-C fail-closes a Success carrying it.
                        self.diagnostics.static_init_incomplete.inc();
                        debug!(
                            vec_idx,
                            static_name = %static_name,
                            "CHC: static init incomplete — allocation exists but encoding failed"
                        );
                    }

                    // Part of #3496 Bug B: create unique concrete address for each static
                    // so that pointer comparisons like `&A != &B` can be decided.
                    // Uses the same obj_id address scheme as heap allocations:
                    // addr = obj_id(BV32) ++ offset(BV32), with offset=0.
                    if let Some(obj_id) = self.heap_state.next_alloc_id() {
                        // Freshly minted object base: an address by
                        // construction, which is what makes this the right
                        // place — and the only place — to say so.
                        let addr = Loc::of_address(
                            ay_bindings::Expr::bitvec_const(obj_id as i128, 32)
                                .concat(ay_bindings::Expr::bitvec_const(0i128, 32)),
                        );
                        self.ref_resolution
                            .static_address_exprs
                            .insert(alloc_id, addr.as_expr().clone());

                        // Part of #3793: Record static layout metadata so the entry rule
                        // emits obj_size[obj_id] = size. Family 3 also threads the
                        // concrete alignment so static addresses carry an explicit
                        // base-alignment constraint in the entry rule.
                        if let Some(type_size) = self.get_type_size(static_ty) {
                            let type_align = self.get_type_align(static_ty).unwrap_or(1);
                            self.ref_resolution.static_alloc_sizes.push((
                                obj_id,
                                type_size as u32,
                                type_align,
                            ));
                        }

                        // Part of #3496 Phase 5: If we have both an init value and
                        // an address, register typed memory mirror entries in the
                        // entry rule. This links the static's initial data to the
                        // memory arrays actually used by flat deref loads.
                        // P2-S1: a contract-havocked `static mut` gets no
                        // memory mirror (raw-pointer reads must see arbitrary
                        // bytes). Interior-mut immutable statics are fully
                        // havocked on the raw-memory path by the gate inside
                        // `register_static_memory_init_entries` (their Freeze
                        // fields stay pinned only on the state-var side).
                        if !(contract_havoc && is_mutable_static)
                            && let Some(init_value) = init_expr_opt.clone()
                        {
                            self.register_static_memory_init_entries(static_ty, init_value, addr);
                            debug!(
                                vec_idx,
                                static_name = %static_name,
                                "CHC: registered static memory mirror (#3496 Phase 5)"
                            );
                        }
                    }

                    debug!(
                        vec_idx,
                        static_name = %static_name,
                        ?alloc_id,
                        "CHC: created state variable for static (#3496)"
                    );

                    e.insert(vec_idx);
                    discovered_statics.push((static_name.clone(), static_ty, vec_idx));
                }

                local_to_alloc.push((lhs.local, alloc_id));
            }
        }

        // Map locals to their static state variable indices (by alloc_id).
        for (dest_local, alloc) in &local_to_alloc {
            if let Some(&vec_idx) = alloc_to_vec_idx.get(alloc) {
                self.map_static_local_to_state_idx(*dest_local, vec_idx);
                debug!(dest_local, vec_idx, "CHC: mapped local to static state var (#428)");
            }
        }

        self.propagate_static_ref_state_idxs();

        if !self.ref_resolution.static_ref_to_state_idx.is_empty() {
            debug!(
                num_statics = discovered_statics.len(),
                num_ref_locals = self.ref_resolution.static_ref_to_state_idx.len(),
                "CHC: collected static state variables (#428)"
            );
        }
    }

    /// P2-S1: does this type contain interior mutability (an `UnsafeCell`
    /// reachable BY VALUE — not behind a reference/raw pointer)? A static
    /// whose type matches must be havocked in a contract CHECK harness.
    ///
    /// Implemented via rustc's `is_freeze` (`!Freeze` ⇔ interior-mutable by
    /// value), which recurses through ADT FIELD types. NOTE: a rustc_public
    /// `TyVisitor` port of Kani's `is_interior_mut` is NOT sufficient here —
    /// `RigidTy::Adt`'s `super_visit` only walks generic args, so
    /// `struct WithMut { f: UnsafeCell<u8> }` would be missed (verified
    /// against rustc_public/src/visitor.rs). A non-monomorphic type
    /// (leftover params) conservatively counts as interior-mutable: the
    /// fail direction must be MORE havoc, never a pin.
    pub(in crate::codegen_ay::chc) fn ty_has_interior_mut(&self, ty: rustc_public::ty::Ty) -> bool {
        use rustc_middle::ty::TypeVisitableExt;
        let internal_ty = rustc_public::rustc_internal::internal(self.tcx, ty);
        if internal_ty.has_param() {
            return true; // fail toward havoc
        }
        !internal_ty.is_freeze(self.tcx, rustc_middle::ty::TypingEnv::fully_monomorphized())
    }

    /// P2-S1: pins only the Freeze (non-UnsafeCell) parts of an interior-mut
    /// immutable static's state variable to its initializer; UnsafeCell-covered
    /// parts stay unconstrained (havoc). Bails to FULL havoc (no constraint)
    /// on any shape it cannot decompose — the fail direction is always MORE
    /// havoc, never a pin on possibly-mutable state.
    ///
    /// FORM MATTERS: the pin is a single CONSTRUCTOR equality
    /// `var == Mk(freeze_init.., fresh..)` with fresh (universally
    /// quantified) rule variables in the havocked slots — NOT a conjunction
    /// of accessor equalities `fld(var) == c`, which leaves `var` a free
    /// datatype constrained only through accessors and lands in ay-chc's
    /// free-datatype Unknown class (observed: fixme_static_interior_mut
    /// went inconclusive under the accessor form).
    fn collect_contract_partial_static_pins(
        &self,
        rust_ty: rustc_public::ty::Ty,
        var_expr: ay_bindings::Expr,
        init_expr: ay_bindings::Expr,
        out: &mut Vec<ay_bindings::Expr>,
    ) {
        if let Some(term) = self.contract_partial_pin_term(rust_ty, init_expr) {
            out.push(var_expr.eq(term));
        }
    }

    /// Builds the constructor-shaped pin term for
    /// `collect_contract_partial_static_pins`: initializer values in Freeze
    /// positions, fresh havoc variables in UnsafeCell-covered positions.
    /// `None` means the shape cannot be decomposed — the caller emits no
    /// constraint at all (full havoc).
    fn contract_partial_pin_term(
        &self,
        rust_ty: rustc_public::ty::Ty,
        init_expr: ay_bindings::Expr,
    ) -> Option<ay_bindings::Expr> {
        use super::codegen_types_adt_sort::CodegenTypesAdtSort;
        use crate::codegen_ay::chc::{chc_fresh_name, declare_pending_var};
        use rustc_public::ty::{RigidTy, TyKind};

        if !self.ty_has_interior_mut(rust_ty) {
            return Some(init_expr); // fully Freeze: exact initializer value
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = rust_ty.kind() else {
            return None; // non-ADT interior-mut carrier (e.g. [UnsafeCell<T>; N]): full havoc
        };
        let internal_def = rustc_public::rustc_internal::internal(self.tcx, def);
        if internal_def.is_unsafe_cell() || !internal_def.is_struct() {
            return None; // the cell itself / enum / union: full havoc
        }
        let dt = init_expr.sort().datatype_sort()?.clone();
        let ctor = dt.constructors.first()?;
        let variants = def.variants();
        let variant = variants.first()?;
        if ctor.fields.len() != variant.fields().len() {
            return None; // encoding shape mismatch: full havoc
        }
        let mut field_terms = Vec::with_capacity(ctor.fields.len());
        for (field_idx, field_def) in variant.fields().iter().enumerate() {
            let field = ctor.fields.get(field_idx)?;
            let field_ty =
                <ChcCtx as CodegenTypesAdtSort>::resolve_generic_ty(field_def.ty(), &args)
                    .unwrap_or_else(|| field_def.ty());
            let init_field =
                init_expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
            let term = match self.contract_partial_pin_term(field_ty, init_field) {
                Some(term) => term,
                // Interior-mutable slot: fresh universally-quantified rule
                // var — the entry rule then holds for EVERY value (havoc).
                None => declare_pending_var(
                    chc_fresh_name("__contract_static_havoc"),
                    field.sort.clone(),
                ),
            };
            field_terms.push(term);
        }
        Some(ay_bindings::Expr::datatype_constructor(
            &dt.name,
            &ctor.name,
            field_terms,
            init_expr.sort().clone(),
        ))
    }

    // scalar_from_alloc, read_composite_from_bytes, sort_byte_width,
    // sort_alignment, sort_default_expr moved to codegen_decl_static_alloc.rs
    // (Part of #4196 file-size compliance).
    // Allocation-aware const readers also live in codegen_decl_static_alloc.rs.
    // resolve_pointer_static_init, static_init_from_alloc,
    // read_array_with_flatten live in codegen_decl_static_init.rs.
    // Callee static pre-scan lives in codegen_decl_static_callee.rs (#4014).
}
