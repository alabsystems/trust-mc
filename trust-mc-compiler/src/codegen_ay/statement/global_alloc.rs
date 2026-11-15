// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Global allocations (statics, constant memory) in the BMC lane.
//!
//! A constant pointer carries provenance to a global allocation. Every global
//! allocation this harness names gets ONE address symbol, from ONE table
//! (`AYCtx::global_alloc_addrs`, keyed by `const_pointer::TargetKey`), whichever lane
//! reaches it first: the value decoder (`const_ptr_value`, which reads the
//! symbols this module materializes at body entry, for a pointer slot of a
//! constant value and for a `&str`/`&[T]` constant's `fld_ptr`) or the
//! reference lane (`derived_place_address` through a constant reference such
//! as `&S`).
//! Before the table was shared, `&raw const S` and `&S` named one static with
//! two unrelated symbols, and `ptr::eq(&S, P)` for `const P: *const u32 =
//! &raw const S` was certified FALSE.
//!
//! Minting a symbol (`global_alloc_address`) gives it the validity facts a
//! stack address symbol gets, keeps it apart from every heap object and every
//! registered stack object (`register_stack_object`: without it the solver
//! placed `static mut A` on a later `Box` and certified a counterexample to
//! `*a == 1` after `*a = 1; let b = Box::new(2)`), and gives it allocation
//! identity (pairwise non-overlap with every other named allocation, through
//! `alloc_roots`). Separately, an allocation the value decoder can read
//! gets its initializer bytes constrained on the INITIAL memory array — the
//! value before any store, so a write made earlier through another pointer is
//! never overwritten. Bytes the initializer does not determine (uninitialized
//! bytes, pointer bytes carrying provenance, a foreign static with no
//! initializer) stay free, recorded as a sound approximation.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::Body;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::shared::const_pointer::{
    self, ConstRead, ConstWindow, Fixedness, MAX_PROVENANCE_DEPTH, Slot, TargetKey,
};
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

/// Largest allocation whose bytes are constrained one by one.
const MAX_CONSTRAINED_BYTES: usize = 4096;

/// Whether a constant of type `ty` can hand the value decoder
/// (`codegen_scalar_from_bytes`, whose pointer slots read a global
/// allocation's address through `const_ptr_value`) a pointer slot: a raw or
/// function pointer, a reference INSIDE a value, or an aggregate decoded
/// field by field down to one. A top-level reference is decoded through its
/// POINTEE (`try_codegen_const_ref_pointee`), so it qualifies exactly when
/// its pointee does (`&RP` for a static `RP: *const T` reaches `RP` and,
/// transitively, `RP`'s target); a `&str` panic message or a `&Location`
/// never qualifies. Materializing those gave every harness address, identity
/// and initializer-byte facts no read could use, and the extra SMT starved
/// solver re-queries (negative/cover_probe_starved.rs::starved_violation_requery
/// read its factoring checks SUCCESS). A type deeper than the bound qualifies.
fn const_may_yield_raw_ptr(ty: Ty, depth: usize) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => value_may_hold_pointer(pointee, depth),
        _ => value_may_hold_pointer(ty, depth),
    }
}

/// Whether a VALUE of type `ty` can hold a pointer slot.
fn value_may_hold_pointer(ty: Ty, depth: usize) -> bool {
    let Some(depth) = depth.checked_sub(1) else {
        return true;
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::FnPtr(..)) => true,
        // A THIN reference inside a value is a pointer slot; a fat one
        // (`&str`, `&[T]`, `&dyn`) is not decoded inside a value.
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
            pointee.layout().is_ok_and(|layout| layout.shape().is_sized())
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().any(|elem| value_may_hold_pointer(*elem, depth))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _)) => value_may_hold_pointer(elem, depth),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants_iter().any(|variant| {
            variant.fields().iter().any(|field| {
                mono_ty::field_ty(field, &args).is_none_or(|t| value_may_hold_pointer(t, depth))
            })
        }),
        TyKind::RigidTy(RigidTy::Closure(..)) => true,
        _ => false,
    }
}

/// Materialize every global allocation reachable from `body`'s constants that
/// can yield a raw pointer (`const_may_yield_raw_ptr`), through the shared
/// transitive walk (`const_pointer::reachable_targets`).
pub(super) fn materialize_body_global_allocs(ctx: &mut AYCtx<'_, '_>, body: &Body) {
    if ctx.config.use_chc {
        return;
    }
    let reachable = const_pointer::reachable_targets(ctx.tcx, body, |ty| {
        const_may_yield_raw_ptr(ty, MAX_PROVENANCE_DEPTH)
    });
    let mut deferred: Vec<DeferredPointer> = Vec::new();
    for reached in reachable.targets {
        let target = reached.bytes.as_ref().map(|(bytes, _)| bytes);
        let addr = address_for_key(ctx, &reached.key, target);
        constrain_initializer_bytes(ctx, &reached.key, &addr, target, &mut deferred);
    }
    emit_deferred_pointers(ctx, deferred);
}

/// A pointer stored inside a global allocation's initializer: its bytes at
/// `at` are `target`'s address plus `offset`, once `target` has a symbol.
struct DeferredPointer {
    at: Expr,
    target_key: Option<TargetKey>,
    offset: u128,
}

/// Constrain every stored pointer's bytes on the initial memory array to its
/// target allocation's address plus offset. A target this lane cannot name (a
/// function, a vtable, an allocation past the provenance depth) leaves the
/// bytes free, recorded.
fn emit_deferred_pointers(ctx: &mut AYCtx<'_, '_>, deferred: Vec<DeferredPointer>) {
    let Some(initial) = ctx.initial_memory.clone() else {
        if !deferred.is_empty() {
            ctx.bmc_sound_havoc("global_alloc_unknown_bytes");
        }
        return;
    };
    let mut unknown = false;
    for pointer in deferred {
        let base = pointer.target_key.and_then(|k| ctx.global_alloc_addrs.get(&k).cloned());
        let Some(base) = base else {
            unknown = true;
            continue;
        };
        let value = base.bvadd(Expr::bitvec_const(pointer.offset, POINTER_WIDTH));
        for byte in 0..(POINTER_WIDTH / 8) {
            let at = pointer.at.clone().bvadd(Expr::bitvec_const(byte as u128, POINTER_WIDTH));
            let low = byte * 8;
            ctx.assert(initial.clone().select(at).eq(value.clone().extract(low + 7, low)));
        }
    }
    if unknown {
        ctx.bmc_sound_havoc("global_alloc_unknown_bytes");
    }
}

/// The ONE address symbol of the global allocation `key` names for this
/// harness, minted on first use by either lane (module docs).
///
/// A FIXED target (constant memory, an immutable `Freeze` static) gets its
/// whole initializer on the initial memory array when this call names it,
/// exactly as the body walk gives the targets a body's constants reach
/// (`materialize_body_global_allocs`): the rule's "a fixed target is known
/// whole, at every type the harness reads it through a pointer"
/// (`shared/const_pointer.rs`). The reference lane names a target when it
/// forms an address into it (`derived_place_address`: `E as *const u32`,
/// `&ARR[0]`) or a `&str`/`&[T]` constant's `fld_ptr`, and a raw pointer
/// derived from that address by a cast, `wrapping_add`, `byte_add` or
/// `as_ptr` reads MEMORY: before this, its bytes were free there, and
/// `*(E as *const u8).wrapping_add(4).cast::<u32>() == 3` for
/// `const E: &u32 = &[1u32, 2, 3][1]` was certified FALSE (Genuine), as were
/// six more shapes (`const_pointer_raw_from_ref_dual.rs`). A LIVE target's
/// bytes are left as they were: its state is what the program wrote, which
/// the initial image does not describe.
///
/// `Naming::PanicOnly` names a target from a PANIC-ONLY block (every path
/// from it diverges: `compute_may_continue_blocks`, the analysis the CHC
/// lane's whole-object seeding reads for the same purpose): the address is
/// minted and the bytes are NOT put on memory, because a run that enters
/// such a block fails whatever it reads there. A later naming from a block
/// that can continue materializes them then (the bytes constrain the INITIAL
/// memory array, so the order does not matter). Materializing an assertion
/// message there cost every float harness its verdict: ay answers `unknown`
/// (`unsupported`) for floating point beside a constrained `memory` select,
/// so `bmc_f64_rem_true`'s TRUE `x % 3.0 == 2.0` lost its proof
/// (integration_bmc_tests::test_bmc_e2e_f64_rem_true_assertion_proves_unsat).
/// The residual is the CHC lane's: a free value read on a panic-only path can
/// change WHICH failing check a counterexample names, never whether the run
/// fails.
pub(super) fn global_alloc_address(
    ctx: &mut AYCtx<'_, '_>,
    key: &TargetKey,
    naming: Naming,
) -> Option<Expr> {
    let addr = match ctx.global_alloc_addrs.get(key) {
        Some(addr) => addr.clone(),
        None => {
            let target = const_pointer::target_bytes(ctx.tcx, key);
            address_for_key(ctx, key, target.as_ref().map(|(bytes, _)| bytes))
        }
    };
    if naming == Naming::MayContinue
        && !ctx.global_alloc_bytes.contains(key)
        && let Some((bytes, Fixedness::Fixed)) = const_pointer::target_bytes(ctx.tcx, key)
    {
        materialize_fixed_target(ctx, *key, &addr, bytes);
    }
    Some(addr)
}

/// Where the reference lane names a global allocation: in a block that can
/// continue (reach a `Return` or a cycle), or in a panic-only one
/// ([`global_alloc_address`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Naming {
    MayContinue,
    PanicOnly,
}

impl super::StatementCodegen<'_, '_, '_> {
    /// How the block being translated names a global allocation
    /// ([`Naming`]). `current_bb` is set at every block entry of THIS body
    /// (`initialize_block_entry_env`; an inlined callee gets its own
    /// `StatementCodegen`). An index outside the body answers `MayContinue`,
    /// the side that materializes.
    pub(super) fn global_alloc_naming(&mut self) -> Naming {
        let body = self.body;
        let may_continue = self
            .may_continue_blocks
            .get_or_insert_with(|| crate::codegen_ay::chc::compute_may_continue_blocks(body));
        if may_continue.get(self.current_bb).copied().unwrap_or(true) {
            Naming::MayContinue
        } else {
            Naming::PanicOnly
        }
    }
}

/// Constrain a fixed target's bytes on the initial memory array, and name the
/// targets its stored pointers reach (fixed ones materialized the same way,
/// to [`MAX_PROVENANCE_DEPTH`]), so a stored pointer reads as `base + k`. A
/// pointer whose target this lane cannot name leaves its bytes free, recorded
/// (`emit_deferred_pointers`).
fn materialize_fixed_target(
    ctx: &mut AYCtx<'_, '_>,
    key: TargetKey,
    addr: &Expr,
    bytes: ConstWindow,
) {
    let mut deferred: Vec<DeferredPointer> = Vec::new();
    let mut work: Vec<(TargetKey, Expr, ConstWindow, usize)> = vec![(key, addr.clone(), bytes, 0)];
    while let Some((key, addr, bytes, depth)) = work.pop() {
        if ctx.global_alloc_bytes.contains(&key) {
            continue;
        }
        let inner: Vec<TargetKey> = bytes
            .relocations()
            .into_iter()
            .filter_map(|(_, ptr)| ptr.and_then(|p| p.key()))
            .collect();
        constrain_initializer_bytes(ctx, &key, &addr, Some(&bytes), &mut deferred);
        if depth + 1 >= MAX_PROVENANCE_DEPTH {
            continue;
        }
        for next in inner {
            // Materialized already (an address minted from a panic-only block
            // alone is not: `global_alloc_address`).
            if ctx.global_alloc_bytes.contains(&next) {
                continue;
            }
            let target = const_pointer::target_bytes(ctx.tcx, &next);
            let next_addr = address_for_key(ctx, &next, target.as_ref().map(|(b, _)| b));
            if let Some((next_bytes, Fixedness::Fixed)) = target {
                work.push((next, next_addr, next_bytes, depth + 1));
            }
        }
    }
    emit_deferred_pointers(ctx, deferred);
}

/// Look up, or mint, the address symbol of the allocation keyed `key`.
fn address_for_key(ctx: &mut AYCtx<'_, '_>, key: &TargetKey, target: Option<&ConstWindow>) -> Expr {
    if let Some(addr) = ctx.global_alloc_addrs.get(key) {
        return addr.clone();
    }
    let name = format!("global_alloc_{}_addr", key.symbol_key().replace(':', "_"));
    let addr = ctx.declare_var(&name, ptr_sort());
    ctx.global_alloc_addrs.insert(*key, addr.clone());
    let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
    ctx.assert(addr.clone().eq(zero.clone()).not());

    let Some(target) = target else {
        // A foreign static, or one whose initializer cannot be evaluated: the
        // address is non-null and nothing else. Its extent is unknown, so it is
        // not kept apart from other objects (a foreign static may even be a
        // local `#[no_mangle]` static under another name). Recorded.
        ctx.bmc_sound_havoc("global_alloc_unknown_initializer");
        return addr;
    };
    let size = target.len() as u128;
    let align = u128::from(target.align());
    if align > 1 {
        ctx.assert(addr.clone().bvand(Expr::bitvec_const(align - 1, POINTER_WIDTH)).eq(zero));
    }
    let max = (1u128 << POINTER_WIDTH) - 1;
    ctx.assert(addr.clone().bvule(Expr::bitvec_const(max - size, POINTER_WIDTH)));
    if let Ok(extent) = u64::try_from(size) {
        ctx.heap_constrain_within_region(addr.clone(), extent.saturating_add(1));
        // Apart from every heap object and every registered stack object, as a
        // stack address symbol is (`register_stack_object`). `alloc_roots`
        // below separates only the allocations this lane NAMES; a Box's
        // payload region is not among them.
        ctx.register_stack_object(addr.clone(), extent);
    }
    // Allocation identity: distinct from every allocation already named.
    let end = addr.clone().bvadd(Expr::bitvec_const(size, POINTER_WIDTH));
    let others: Vec<(Expr, u128)> = ctx.alloc_roots.values().cloned().collect();
    for (other_base, other_extent) in others {
        let other_end = other_base.clone().bvadd(Expr::bitvec_const(other_extent, POINTER_WIDTH));
        ctx.assert(end.clone().bvule(other_base).or(other_end.bvule(addr.clone())));
    }
    ctx.alloc_roots.insert(Arc::from(name.as_str()), (addr.clone(), size));
    addr
}

/// Constrain the initializer bytes of the allocation keyed `key`, based at
/// `addr`, on the initial memory array, once per harness.
fn constrain_initializer_bytes(
    ctx: &mut AYCtx<'_, '_>,
    key: &TargetKey,
    addr: &Expr,
    target: Option<&ConstWindow>,
    deferred: &mut Vec<DeferredPointer>,
) {
    if !ctx.global_alloc_bytes.insert(*key) {
        return;
    }
    let Some(target) = target else {
        // Unknown bytes; `address_for_key` recorded the unknown initializer.
        return;
    };
    let Some(initial) = ctx.initial_memory.clone() else {
        ctx.bmc_sound_havoc("global_alloc_unknown_initializer");
        return;
    };
    let ptr_bytes = const_pointer::PTR_BYTES;
    let mut unknown = false;
    for (off, ptr) in target.relocations() {
        match ptr {
            Some(ptr) if off + ptr_bytes <= MAX_CONSTRAINED_BYTES => {
                deferred.push(DeferredPointer {
                    at: addr.clone().bvadd(Expr::bitvec_const(off as u128, POINTER_WIDTH)),
                    target_key: ptr.key(),
                    offset: u128::from(ptr.offset()),
                })
            }
            _ => unknown = true,
        }
    }
    for idx in 0..target.len().min(MAX_CONSTRAINED_BYTES) {
        // The slot clause: a byte a relocation covers is not data (the
        // deferred pointer above constrains it), an uninitialized byte is
        // unknown.
        match target.read_slot(idx, 8) {
            Slot::Data(b) => {
                let at = addr.clone().bvadd(Expr::bitvec_const(idx as u128, POINTER_WIDTH));
                ctx.assert(initial.clone().select(at).eq(Expr::bitvec_const(b, 8)));
            }
            Slot::PartialPointer | Slot::Pointer(_) => {}
            Slot::Uninit | Slot::OutOfBounds => unknown = true,
        }
    }
    if unknown || target.len() > MAX_CONSTRAINED_BYTES {
        ctx.bmc_sound_havoc("global_alloc_unknown_bytes");
    }
}
