// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static variable state-var collection for CHC encoding.
//!
//! Part of #428: Scans the MIR body for constant operands with
//! `GlobalAlloc::Static` provenance and creates auxiliary state
//! variables for mutable statics. This enables CHC to model reads
//! and writes through `static mut` references.

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::CrateDef;
use rustc_public::mir::mono::StaticDef;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use tracing::debug;

use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};

use super::ChcCtx;
use super::codegen_decl_static_alloc::AllocScalar;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstTarget, TargetKey};

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
/// Sound-fallback reason (FailClose): a constant pointer into a LIVE static at
/// an offset (or at another type) that no static place path names. Its read
/// would come from typed memory, which a store through the static's state
/// variable never reaches, so no verdict may rest on it (D6).
pub(in crate::codegen_ay::chc) const CONST_PTR_INTO_LIVE_STATIC: &str =
    "const_ptr_into_live_static";

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
        use rustc_public::ty::{RigidTy, TyKind};

        // Part of #3496 Bug C: one state variable per static, keyed by its
        // definition (the identity `const_pointer::TargetKey` uses), so every
        // constant pointer to it — from any body — shares it.
        let mut discovered_statics: Vec<(String, rustc_public::ty::Ty, usize)> = Vec::new(); // (name, ty, vec_idx)
        let mut def_to_vec_idx: std::collections::HashMap<StaticDef, usize> =
            std::collections::HashMap::new();

        // Collect (dest_local, static, offset, pointee) for second-pass local
        // mapping.
        let mut local_to_static: Vec<(usize, StaticDef, u64, rustc_public::ty::Ty)> = Vec::new();

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                // Match: _N = Use(Constant(ptr_with_static_provenance))
                let const_op = match rhs {
                    Rvalue::Use(Operand::Constant(c), ..) => c,
                    _ => continue, // external enum: Rvalue
                };

                let mir_const = &const_op.const_;
                // N5: only a POINTER-TYPED constant (`&T`, `*const T`, `*mut T`,
                // thin or fat) is a constant pointer, and its pointer is the
                // relocation at its own byte 0 (`const_pointer`). A constant
                // VALUE that merely contains a pointer (`[*const u32; 2]` of
                // two fields of a static) is a value whose slots follow the
                // slot clause; mapping it to the static's state variable made
                // `_6 = const PTRS` an alias of `PAIR`.
                if !matches!(
                    mir_const.ty().kind(),
                    TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
                ) {
                    continue;
                }
                let Some(ptr) =
                    const_pointer::const_bytes(mir_const).and_then(|b| b.stored_pointer(0))
                else {
                    continue;
                };
                let ConstTarget::Static(static_def) = ptr.kind() else {
                    continue;
                };
                let Some(const_pointee) = Self::deref_pointee_ty(mir_const.ty()) else {
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

                // Create the state variable on first sight of this static.
                if let std::collections::hash_map::Entry::Vacant(e) =
                    def_to_vec_idx.entry(static_def)
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
                    self.ref_resolution.static_state_ty.insert(vec_idx, static_ty);
                    // LIVE: its value can change (`static mut`, or an
                    // interior-mutable type an `&` can write).
                    if is_mutable_static || self.ty_has_interior_mut(static_ty) {
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
                    // The static's own bytes come from
                    // `const_pointer::target_bytes`, which declines a foreign
                    // (`extern "C" { static X: T; }`) static — it has no MIR
                    // initializer body, and evaluating one triggers a rustc
                    // `span_bug` panic that `.ok()` cannot catch
                    // (SIGABRT/exit 101) — and a still-generic one. A foreign
                    // static must be modelled as nondet (it could hold ANY
                    // value), which is exactly the None-path below (static
                    // left unconstrained). NEVER substitute zero here — that
                    // would let `assert X != 1` pass as a FALSE proof.
                    let init_alloc_opt = const_pointer::target_bytes(
                        self.tcx,
                        &const_pointer::TargetKey::Static(static_def),
                    )
                    .map(|(bytes, _)| bytes);
                    // Every pointer slot of the initializer names its target as
                    // read at the slot's pointee type (D2's read set).
                    if let Some(ref bytes) = init_alloc_opt {
                        self.note_pointer_slots(bytes, static_ty, 0);
                    }
                    let mut init_expr_opt = init_alloc_opt
                        .as_ref()
                        .and_then(|bytes| self.static_init_from_alloc(bytes, &sort, static_ty));

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
                    // A referent seed pins reads to the initializer: only a
                    // FIXED static's value may be decoded.
                    let mut seed_metadata = if is_mutable_static
                        || contract_havoc
                        || self.ty_has_interior_mut(static_ty)
                    {
                        None
                    } else {
                        init_expr_opt.clone().and_then(|init_expr| {
                            self.static_seed_metadata_for_value(
                                static_ty,
                                init_expr,
                                init_alloc_opt.as_ref().map(|bytes| bytes.len()),
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
                        // all is decided on the next line, by the relocation at
                        // the static's own byte 0 — not by this width.
                        && let Some(ptr_slot) = PtrSlot::of_sort(&sort)
                        && let Some(ref static_bytes) = init_alloc_opt
                        && static_bytes.stored_pointer(0).is_some()
                    {
                        // Derive the pointee type from the static's type
                        // (e.g., &mut i32 → i32, *mut i32 → i32).
                        let pointee_ty = Self::deref_ref_ty(static_ty).0;
                        // D9: the seed is the window the static's OWN pointer
                        // names, and its length the static's own metadata word.
                        if !is_mutable_static
                            && let Some(metadata) =
                                self.resolve_pointer_static_seed_metadata(static_bytes, pointee_ty)
                        {
                            seed_metadata = Some(metadata);
                        }
                        let pointer_static_fixed =
                            !is_mutable_static && !self.ty_has_interior_mut(static_ty);
                        if let Some(resolved_data_ptr) = self.resolve_pointer_static_init(
                            static_bytes,
                            pointee_ty,
                            &static_name,
                            vec_idx,
                            pointer_static_fixed,
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
                                    static_bytes.stored_word(const_pointer::PTR_BYTES).map(|len| {
                                        PtrRepr::from_declared_roles(
                                            resolved_data_ptr,
                                            Val::of_value(ay_bindings::Expr::bitvec_const(
                                                u128::from(len),
                                                crate::codegen_ay::types::POINTER_WIDTH,
                                            )),
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

                    // Part of #3496 Bug B: the static's ONE object (D1,
                    // `global_objects`), so pointer comparisons like `&A != &B`
                    // can be decided. `mint_object` returns the object the
                    // shared walk already minted for it: this is a lookup, and
                    // cannot give the static a second object (R10a).
                    if let Some(obj_id) = self.mint_object(TargetKey::Static(static_def)) {
                        let addr = Loc::of_address(
                            crate::codegen_ay::chc::decl::global_objects::object_base_for(obj_id),
                        );
                        self.ref_resolution.static_state_idx_by_obj.insert(obj_id, vec_idx);
                        self.ref_resolution.registered_static_memory.insert(static_def);

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
                            self.register_static_memory_init_entries(
                                static_ty,
                                init_value,
                                addr,
                                is_mutable_static,
                            );
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
                        "CHC: created state variable for static (#3496)"
                    );

                    e.insert(vec_idx);
                    discovered_statics.push((static_name.clone(), static_ty, vec_idx));
                }

                local_to_static.push((lhs.local, static_def, ptr.offset(), const_pointee));
            }
        }

        // Map locals to their static state variable indices (D6). A constant
        // pointer names the static's WHOLE value only at offset 0 with the
        // static's own type. Otherwise it names a part of it: a FIXED static's
        // part is folded from its initializer window (Pass 4); a LIVE static's
        // part is its state variable along the static place path, and with no
        // such path the lane cannot name its live state and fails closed.
        for (dest_local, static_def, offset, pointee) in &local_to_static {
            let Some(&vec_idx) = def_to_vec_idx.get(static_def) else { continue };
            let Some(&static_ty) = self.ref_resolution.static_state_ty.get(&vec_idx) else {
                continue;
            };
            if *offset == 0
                && crate::codegen_ay::chc::decl::static_path::same_ty_modulo_regions(
                    *pointee, static_ty,
                )
            {
                self.map_static_local_to_state_idx(*dest_local, vec_idx);
                debug!(dest_local, vec_idx, "CHC: mapped local to static state var (#428)");
                continue;
            }
            if !self.ref_resolution.mutable_static_state_idxs.contains(&vec_idx) {
                debug!(
                    dest_local,
                    vec_idx, offset, "CHC: const ptr into a fixed static folds (D6)"
                );
                continue;
            }
            match crate::codegen_ay::chc::decl::static_path::static_path(
                static_ty, *offset, *pointee,
            ) {
                Some(path) => {
                    self.map_static_local_to_state_idx(*dest_local, vec_idx);
                    self.ref_resolution.static_ref_paths.insert(*dest_local, path);
                    debug!(
                        dest_local,
                        vec_idx, offset, "CHC: const ptr into a live static via its path (D6)"
                    );
                }
                None => {
                    debug!(
                        dest_local,
                        vec_idx,
                        offset,
                        "CHC: const ptr into a live static has no path — fail closed (D6)"
                    );
                    self.record_sound_fallback_reason(CONST_PTR_INTO_LIVE_STATIC);
                }
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
        // One copy of the test: `foreign_defs::ty_has_interior_mut` (a type
        // with unresolved parameters fails toward havoc there).
        crate::codegen_ay::foreign_defs::ty_has_interior_mut(self.tcx, ty)
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
        use crate::codegen_ay::chc::chc_fresh_name;
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
            // The static's concrete arguments, instantiated and normalized by
            // rustc (see `register_static_memory_init_entries`: the manual
            // substitution's generic fallback was the R12 ICE).
            let field_ty = mono_ty::field_ty(&field_def, &args)?;
            let init_field =
                init_expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
            let term = match self.contract_partial_pin_term(field_ty, init_field) {
                Some(term) => term,
                // Interior-mutable slot: fresh universally-quantified rule
                // var — the entry rule then holds for EVERY value (havoc).
                None => {
                    ExactVar::nondet(chc_fresh_name("__contract_static_havoc"), field.sort.clone())
                }
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
    // resolve_pointer_static_init and static_init_from_alloc live in
    // codegen_decl_static_init.rs, the layout reader in
    // codegen_decl_static_layout.rs.
    // Callee static pre-scan lives in codegen_decl_static_callee.rs (#4014).
}
