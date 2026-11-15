// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06: modifies frame-condition enforcement for contract CHECK mode.
//!
//! The contract transform instruments the modifies-wrapper closure with
//! `modifies_frame_enter(_wrapper_arg)` / `modifies_frame_exit()` marker
//! calls (see `kani_middle::transform::contracts_frame`). After the wrapper
//! is inlined into the harness those markers delimit the dynamic extent of
//! the checked function: every block reachable from the enter call without
//! crossing an exit call executes inside the checked function (its body plus
//! inlined callees).
//!
//! This module:
//! 1. Pre-scans the harness body for marker calls and computes each frame's
//!    extent block set (`prescan_modifies_frames`).
//! 2. Resolves the declared footprint — the `_wrapper_arg` tuple of
//!    `*const T` pointers — into `(base, size)` byte ranges at the enter
//!    block, where the tuple local is still live
//!    (`resolve_modifies_footprint`).
//! 3. Checks every memory store encoded in an extent block against the
//!    footprint (`modifies_frame_store_check`), pushing a fail-if-false
//!    pending check that makes the CHC error state reachable on violation
//!    (CBMC DFCC "Check that *x is assignable" equivalent).
//!
//! Precision notes (documented FC-06 limits):
//! - Object-granular fallback when a footprint element's pointee size is
//!   unknown (matches any offset within the same object).
//! - A store whose address cannot be split into (obj, offset) or translated,
//!   and any store inside a frame whose footprint did not resolve, fails
//!   closed (`record_sound_fallback_reason`, a proof becomes Unknown). These
//!   were fail-open until 2026-09-12.
//! - `suppress_heap_store_checks` stores (fresh-allocation writes such as
//!   `Box::new` initialization) are exempt — allocations created during the
//!   call may be freely written, matching DFCC freshness semantics.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{
    AggregateKind, Body, CopyNonOverlapping, Mutability, Operand, Place, ProjectionElem, Rvalue,
    StatementKind, Terminator, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, try_kani_function_from_fn_def};

/// Whether a value of type `ty` holds no pointer, so a write through a
/// reference to it reaches only its own `size_of::<T>()` bytes. Recurses
/// through arrays, slices, tuples and every field of every ADT variant (so
/// `Cell`/`UnsafeCell` are transparent and `Box`/`Vec`/`String`/`NonNull`/`Rc`
/// reach a raw pointer and answer `false`); references, raw pointers, function
/// pointers, `dyn`, closures, coroutines and anything unresolved answer
/// `false` (fail-closed), as does a type nested deeper than the bound.
pub(in crate::codegen_ay::chc) fn pointee_is_pointer_free(ty: Ty) -> bool {
    fn walk(ty: Ty, depth: usize) -> bool {
        const MAX_DEPTH: usize = 12;
        if depth > MAX_DEPTH {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool)
            | TyKind::RigidTy(RigidTy::Char)
            | TyKind::RigidTy(RigidTy::Int(_))
            | TyKind::RigidTy(RigidTy::Uint(_))
            | TyKind::RigidTy(RigidTy::Float(_))
            | TyKind::RigidTy(RigidTy::Str)
            | TyKind::RigidTy(RigidTy::Never)
            | TyKind::RigidTy(RigidTy::FnDef(..)) => true,
            TyKind::RigidTy(RigidTy::Array(elem, _)) | TyKind::RigidTy(RigidTy::Slice(elem)) => {
                walk(elem, depth + 1)
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().all(|t| walk(*t, depth + 1)),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().iter().all(|variant| {
                variant.fields().iter().all(|field| {
                    mono_ty::field_ty(field, &args).is_some_and(|t| walk(t, depth + 1))
                })
            }),
            _ => false,
        }
    }
    walk(ty, 0)
}

/// One byte-range of the declared assignable footprint.
pub(in crate::codegen_ay::chc) struct FootprintRange {
    /// BV64 pointer value (obj_id ++ offset) of the range base.
    pub base: Expr,
    /// BV32 byte size of the range; `None` = object-granular (whole object
    /// with the base's obj_id is assignable).
    pub size: Option<Expr>,
    /// This range came from a FAT pointer (`&mut [T]`, `&mut str`): its base and
    /// its extent are both read out of the wrapper argument's 128-bit value, and
    /// the object id that lands in the base does not reliably match the object id
    /// a store inside the extent computes. A frame holding one of these cannot
    /// certify either verdict; see `modifies_frame_store_check`.
    pub wide: bool,
}

/// A modifies frame: the dynamic extent of one checked-function invocation.
pub(in crate::codegen_ay::chc) struct ModifiesFrame {
    /// Block whose terminator is the `modifies_frame_enter` call.
    pub enter_bb: usize,
    /// Blocks that execute inside the checked function's extent.
    pub blocks: HashSet<usize>,
    /// Footprint ranges, resolved when the enter block is encoded.
    pub footprint: Vec<FootprintRange>,
    /// Whether footprint resolution ran. Until then — and permanently when
    /// resolution was not possible — every extent store fails CLOSED (a
    /// demoting fallback), never open.
    pub resolved: bool,
    /// Frame net: address-taken locals that exist outside the extent, whose
    /// state changes inside the extent are classified by `modifies_frame_net`.
    pub watched: Vec<super::modifies_frame_net::WatchedLocal>,
    /// Frame net: footprint elements traced statically to harness locals
    /// (proves coverage only).
    pub static_footprint: Vec<super::modifies_frame_net::StaticFootprint>,
    /// Locals whose storage is created inside the extent (a `StorageLive` in
    /// an extent block and in no other block). DFCC freshness: storage the
    /// checked function creates is assignable whatever the footprint says.
    pub frame_locals: HashSet<usize>,
}

/// Leaf segment of a callee path without generic arguments:
/// `core::intrinsics::write_bytes::<u32>` -> `write_bytes`.
/// The callee's own name: the last `::`-separated segment at angle-bracket
/// depth 0 that is not itself a generic-argument group.
///
/// A resolved path puts its generic arguments wherever the item is generic —
/// `std::mem::replace::<&mut u8>` at the END, `std::option::Option::<T>::replace`
/// and `core::slice::<impl [T]>::len` in the MIDDLE — so neither "truncate at
/// the first `::<`" nor "take the last `::` segment" is right on its own: the
/// first gives `Option` and `slice`, the second gives `<&mut u8>`.
pub(in crate::codegen_ay::chc) fn callee_path_leaf(path: &str) -> &str {
    let bytes = path.as_bytes();
    let mut depth: i32 = 0;
    let mut segments: Vec<(usize, usize)> = Vec::new();
    let mut start = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' => depth = (depth - 1).max(0),
            b':' if depth == 0 && bytes.get(i + 1) == Some(&b':') => {
                segments.push((start, i));
                i += 2;
                start = i;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    segments.push((start, bytes.len()));
    for &(s, e) in segments.iter().rev() {
        let seg = &path[s..e];
        if !seg.is_empty() && !seg.starts_with('<') {
            return seg;
        }
    }
    path
}

#[cfg(test)]
mod callee_path_leaf_tests {
    use super::callee_path_leaf;

    #[test]
    fn generics_at_the_end_are_skipped() {
        assert_eq!(callee_path_leaf("std::mem::replace::<&mut u8>"), "replace");
        assert_eq!(callee_path_leaf("core::ptr::write::<u8>"), "write");
    }

    #[test]
    fn generics_in_the_middle_are_skipped() {
        assert_eq!(callee_path_leaf("std::option::Option::<T>::replace"), "replace");
        assert_eq!(callee_path_leaf("core::slice::<impl [T]>::len"), "len");
        assert_eq!(callee_path_leaf("core::slice::<impl [T]>::contains"), "contains");
    }

    #[test]
    fn a_plain_path_is_its_last_segment() {
        assert_eq!(
            callee_path_leaf("core::intrinsics::typed_swap_nonoverlapping"),
            "typed_swap_nonoverlapping"
        );
        assert_eq!(callee_path_leaf("main"), "main");
    }

    /// `->` inside a generic argument must not unbalance the depth counter.
    #[test]
    fn a_fn_type_argument_does_not_unbalance() {
        assert_eq!(callee_path_leaf("core::mem::replace::<fn() -> u8>"), "replace");
    }
}

fn is_std_path(path: &str) -> bool {
    ["core::", "std::", "alloc::"].iter().any(|prefix| path.starts_with(prefix))
}

/// Library writers of a byte span `count * size_of::<T>()` through a `*mut T`:
/// `(destination argument, element-count argument)` pairs.
fn span_writer_args(path: &str) -> Option<&'static [(usize, usize)]> {
    if !is_std_path(path) {
        return None;
    }
    match callee_path_leaf(path) {
        "write_bytes" | "volatile_set_memory" => Some(&[(0, 2)]),
        "copy" | "copy_nonoverlapping" => Some(&[(1, 2)]),
        "volatile_copy_memory" | "volatile_copy_nonoverlapping_memory" => Some(&[(0, 2)]),
        "swap_nonoverlapping" => Some(&[(0, 2), (1, 2)]),
        _ => None,
    }
}

/// Library calls that write exactly one pointee through every writable pointer
/// argument (so a violation found through them is a real store, not a guess).
fn exact_element_writer(path: &str) -> bool {
    if !is_std_path(path) {
        return false;
    }
    let leaf = callee_path_leaf(path);
    (path.contains("ptr::")
        && matches!(leaf, "write" | "write_unaligned" | "write_volatile" | "replace" | "swap"))
        || (path.contains("mem::") && matches!(leaf, "replace" | "swap"))
        || matches!(leaf, "typed_swap_nonoverlapping" | "volatile_store")
}

/// Classify a terminator as one of the modifies-frame marker calls.
fn frame_hook_kind(body: &Body, term: &Terminator) -> Option<KaniHook> {
    let TerminatorKind::Call { func, .. } = &term.kind else {
        return None;
    };
    let (def, _) = func.ty(body.locals()).ok()?.kind().fn_def()?;
    match try_kani_function_from_fn_def(def)? {
        KaniFunction::Hook(hook @ (KaniHook::ModifiesFrameEnter | KaniHook::ModifiesFrameExit)) => {
            Some(hook)
        }
        _ => None,
    }
}

/// Pre-scan the body for modifies-frame markers and compute extent blocks.
///
/// Runs before block encoding (from `generate_transition_rules`), so the
/// enter block — encoded in topological order before its extent — can resolve
/// the footprint before any extent store is checked.
pub(in crate::codegen_ay::chc) fn prescan_modifies_frames(ctx: &mut ChcCtx<'_, '_>) {
    let mut frames: Vec<ModifiesFrame> = Vec::new();
    for (bb_idx, block) in ctx.body.blocks.iter().enumerate() {
        if frame_hook_kind(ctx.body, &block.terminator) != Some(KaniHook::ModifiesFrameEnter) {
            continue;
        }
        let TerminatorKind::Call { target, .. } = &block.terminator.kind else {
            continue;
        };
        // Forward DFS from the enter call's continuation; an exit call block
        // belongs to the extent (its statements run inside the wrapper) but
        // its successors do not.
        let mut extent: HashSet<usize> = HashSet::new();
        if let Some(entry) = target {
            let mut stack = vec![*entry];
            while let Some(bb) = stack.pop() {
                if !extent.insert(bb) {
                    continue;
                }
                let term = &ctx.body.blocks[bb].terminator;
                if frame_hook_kind(ctx.body, term) == Some(KaniHook::ModifiesFrameExit) {
                    continue;
                }
                stack.extend(term.successors());
            }
        }
        let watched = super::modifies_frame_net::watched_locals_for_extent(ctx.body, &extent);
        let static_footprint =
            super::modifies_frame_net::static_footprints(ctx.body, &block.terminator);
        let mut live_inside: HashSet<usize> = HashSet::new();
        let mut live_outside: HashSet<usize> = HashSet::new();
        for (block_idx, block_data) in ctx.body.blocks.iter().enumerate() {
            let live =
                if extent.contains(&block_idx) { &mut live_inside } else { &mut live_outside };
            for stmt in &block_data.statements {
                if let StatementKind::StorageLive(local) = &stmt.kind {
                    live.insert(*local);
                }
            }
        }
        let frame_locals: HashSet<usize> = live_inside.difference(&live_outside).copied().collect();
        debug!(
            enter_bb = bb_idx,
            extent_blocks = extent.len(),
            ?watched,
            ?static_footprint,
            frame_locals = frame_locals.len(),
            "FC-06: prescanned modifies frame"
        );
        frames.push(ModifiesFrame {
            enter_bb: bb_idx,
            blocks: extent,
            footprint: Vec::new(),
            resolved: false,
            watched,
            static_footprint,
            frame_locals,
        });
    }
    if frames.is_empty() {
        return;
    }
    let mut by_bb: HashMap<usize, usize> = HashMap::new();
    for (idx, frame) in frames.iter().enumerate() {
        for bb in &frame.blocks {
            by_bb.insert(*bb, idx);
        }
    }
    ctx.modifies_frames = frames;
    ctx.modifies_frame_by_bb = by_bb;
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle the `ModifiesFrameEnter` hook: resolve the footprint from the
    /// `_wrapper_arg` tuple argument, then pass through control flow.
    pub(in crate::codegen_ay::chc) fn hook_modifies_frame_enter(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        self.resolve_modifies_footprint(dcx);
        self.hook_noop_transition(dcx, "kani_hook::modifies_frame_enter");
    }

    /// Resolve the declared footprint of the frame entered at `dcx.bb_idx`.
    ///
    /// Each `_wrapper_arg` tuple field is a `*const T` pointer:
    /// - thin pointer: range = (ptr, size_of::<T>())
    /// - slice/str fat pointer (BV128 = len ++ data): range = (data, len * elem_size)
    /// - unknown size: object-granular range.
    fn resolve_modifies_footprint(&mut self, dcx: &DispatchCallContext<'_>) {
        let Some(frame_idx) = self.modifies_frames.iter().position(|f| f.enter_bb == dcx.bb_idx)
        else {
            return;
        };
        let Some(arg) = dcx.args.first() else {
            self.modifies_frames[frame_idx].resolved = true;
            return;
        };
        let Ok(arg_ty) = arg.ty(self.body.locals()) else {
            debug!("FC-06: cannot type _wrapper_arg; footprint unresolved (fail-open)");
            return;
        };
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = arg_ty.kind() else {
            debug!(?arg_ty, "FC-06: _wrapper_arg is not a tuple; footprint unresolved (fail-open)");
            return;
        };
        if fields.is_empty() {
            // No modifies clause: empty footprint, every extent store violates.
            self.modifies_frames[frame_idx].resolved = true;
            return;
        }
        let place = match arg {
            Operand::Copy(p) | Operand::Move(p) => p.clone(),
            Operand::Constant(_) => {
                debug!("FC-06: constant _wrapper_arg tuple; footprint unresolved (fail-open)");
                return;
            }
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => return,
        };
        let mut ranges: Vec<FootprintRange> = Vec::new();
        let mut all_resolved = true;
        for (i, field_ty) in fields.iter().enumerate() {
            let mut field_place = place.clone();
            field_place.projection.push(ProjectionElem::Field(i, *field_ty));
            let Some(expr) = self.translate_place_with_modified(&field_place, dcx.modified_locals)
            else {
                debug!(field = i, "FC-06: footprint pointer untranslatable");
                all_resolved = false;
                continue;
            };
            match self.footprint_range_for(expr, *field_ty) {
                Some(range) => ranges.push(range),
                None => {
                    debug!(field = i, "FC-06: unsupported footprint pointer shape");
                    all_resolved = false;
                }
            }
        }
        let frame = &mut self.modifies_frames[frame_idx];
        frame.footprint = ranges;
        // If any element failed to resolve, enforcing the partial footprint
        // could reject writes to the missing element: stay fail-open.
        frame.resolved = all_resolved;
        debug!(
            enter_bb = dcx.bb_idx,
            ranges = self.modifies_frames[frame_idx].footprint.len(),
            resolved = all_resolved,
            "FC-06: resolved modifies footprint"
        );
    }

    /// Build a footprint range from a resolved pointer expression + its type.
    fn footprint_range_for(&self, expr: Expr, field_ty: Ty) -> Option<FootprintRange> {
        let pointee = match field_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(t, _)) => t,
            TyKind::RigidTy(RigidTy::Ref(_, t, _)) => t,
            _ => return None,
        };
        let width = expr.sort().bitvec_width();
        let is_slice_like =
            matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str));
        match width {
            Some(128) if is_slice_like => {
                // BV128 fat pointer = concat(len: BV64, data: BV64). The length
                // counts ELEMENTS, so the byte extent is `len * size_of::<T>()`
                // — and `T` is the slice's element, not the slice itself.
                // `get_type_size` has no size for the unsized `[u32]`, so asking
                // it for the pointee gave `unwrap_or(1)` and a footprint of
                // `len` BYTES: every store into a `#[kani::modifies(s)]`
                // footprint with `s: &mut [u32]` fell outside it and was
                // certified FAILED (memory_safety) while BMC proved the same
                // harness (negative/modifies_frame_slice_params.rs,
                // negative/modifies_frame_interior_raw.rs, main 31793ccc3).
                let base = expr.clone().extract(63, 0);
                let len32 = expr.extract(95, 64);
                let elem_ty = match pointee.kind() {
                    TyKind::RigidTy(RigidTy::Slice(elem)) => Some(elem),
                    _ => None, // external enum: TyKind — `str` has byte elements
                };
                let elem_size = match elem_ty {
                    Some(elem) => self.get_type_size(elem).unwrap_or(1).max(1),
                    None => 1, // `str`
                };
                let size = len32.bvmul(Expr::bitvec_const(elem_size as u128, 32));
                Some(FootprintRange { base, size: Some(size), wide: true })
            }
            Some(128) => {
                // Other fat pointers (dyn Trait): object-granular.
                Some(FootprintRange { base: expr.extract(63, 0), size: None, wide: false })
            }
            Some(64) => {
                // A slice-like pointee that arrives as a THIN 64-bit value has no
                // extent at all (`get_type_size` has none for `[T]`), so the range
                // degrades to object-granular AND its object id is whatever the
                // flattened wrapper slot holds — which is how the `&mut [T]`
                // footprints were accused even after the byte extent was fixed.
                // Slice-likeness, not the 128-bit width, is what makes a footprint
                // element uncertifiable.
                let size = self.get_type_size(pointee).map(|sz| Expr::bitvec_const(sz as u128, 32));
                Some(FootprintRange { base: expr, size, wide: is_slice_like })
            }
            _ => None,
        }
    }

    /// Objects the checked function created (DFCC freshness): its stack locals
    /// AND every heap allocation made inside the frame's extent.
    ///
    /// The heap half was missing, so a `Box` allocated inside the checked
    /// function and written through (`let mut bx = Box::new(0); *bx = 1;`) was
    /// accused of leaving a `#[kani::modifies(a)]` frame and the harness was
    /// FAILED [AY:CTREX_CAT:Genuine] on a `memory_safety` check
    /// (negative/modifies_frame_shapes.rs::box_local_store_safe; it is red on
    /// main as well).
    fn frame_local_obj_ids(&self, frame_idx: usize) -> Vec<u32> {
        let frame = &self.modifies_frames[frame_idx];
        let mut objs: Vec<u32> = self
            .heap_state
            .stack_local_obj_ids()
            .into_iter()
            .filter(|obj| {
                self.heap_state
                    .local_idx_for_obj_id(*obj)
                    .is_some_and(|local| frame.frame_locals.contains(&local))
            })
            .collect();
        if let Some(fresh) = self.heap_state.frame_fresh_heap_objs.get(&frame_idx) {
            objs.extend(fresh.iter().copied::<u32>());
        }
        objs
    }

    /// Condition that the `len` bytes (BV64) at `addr` lie inside frame
    /// `frame_idx`'s footprint or in storage the checked function created.
    /// Offsets are compared in 64 bits so a large length cannot wrap.
    fn modifies_frame_range_allowed(
        &self,
        frame_idx: usize,
        addr: &Expr,
        len: &Expr,
    ) -> Option<Expr> {
        let (obj_a, off_a) = self.split_pointer(addr)?;
        let start = off_a.zero_extend(32);
        let end = start.clone().bvadd(len.clone());
        let mut allowed = len.clone().eq(Expr::bitvec_const(0u64, 64));
        for obj in self.frame_local_obj_ids(frame_idx) {
            allowed = allowed.or(obj_a.clone().eq(Expr::bitvec_const(u128::from(obj), 32)));
        }
        for range in &self.modifies_frames[frame_idx].footprint {
            let Some((obj_b, off_b)) = self.split_pointer(&range.base) else {
                continue;
            };
            let same_obj = obj_a.clone().eq(obj_b);
            let cond = match &range.size {
                Some(size) => {
                    let range_start = off_b.zero_extend(32);
                    let range_end = range_start.clone().bvadd(size.clone().zero_extend(32));
                    same_obj.and(range_start.bvule(start.clone())).and(end.clone().bvule(range_end))
                }
                None => same_obj,
            };
            allowed = allowed.or(cond);
        }
        Some(allowed)
    }

    /// FC-06: a call writes through its pointer arguments without routing the
    /// store through a checked store path when a stub, model or intrinsic encodes
    /// it (`Vec::push`, `String::push`, `mem::swap`, `write_bytes`, `copy`,
    /// `write_unaligned`: negative/modifies_frame_residual.rs,
    /// negative/modifies_frame_variants.rs). Check every writable pointer argument:
    /// - a byte-span writer (`write_bytes`, the `copy` family) or an exact
    ///   single-element writer (`ptr::write`, `mem::swap`, ...): the written bytes
    ///   must be assignable, and a violation is a real store;
    /// - `&mut T` (or `&T` with interior mutability) passed to any other call: the
    ///   call MAY write the pointee, so the same check is emitted as an
    ///   over-approximation (`modifies_frame_call_arg_overapprox`, SoundHavoc: a
    ///   proof stays clean, a counterexample is never certified);
    /// - an address, size or count that does not translate fails closed.
    pub(in crate::codegen_ay::chc) fn modifies_frame_call_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&dcx.bb_idx) else {
            return;
        };
        if let Ok(func_ty) = dcx.func.ty(self.body.locals())
            && let Some((def, _)) = func_ty.kind().fn_def()
            && matches!(
                try_kani_function_from_fn_def(def),
                Some(KaniFunction::Hook(
                    KaniHook::ModifiesFrameEnter | KaniHook::ModifiesFrameExit
                ))
            )
        {
            return;
        }
        let path = self.resolve_callee_path(dcx.func).unwrap_or_default();
        let spans = span_writer_args(&path);
        let exact = spans.is_some() || exact_element_writer(&path);
        for (index, arg) in dcx.args.iter().enumerate() {
            let Ok(arg_ty) = arg.ty(self.body.locals()) else {
                continue;
            };
            let span_count = spans
                .and_then(|s| s.iter().find(|(dst, _)| *dst == index))
                .map(|(_, count)| *count);
            let (pointee, writable) = match arg_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Mut)) => (pointee, true),
                TyKind::RigidTy(RigidTy::RawPtr(pointee, Mutability::Mut)) => {
                    (pointee, span_count.is_some() || exact)
                }
                TyKind::RigidTy(RigidTy::Ref(_, pointee, Mutability::Not)) => {
                    (pointee, self.ty_has_interior_mut(pointee))
                }
                _ => continue,
            };
            if !writable {
                continue;
            }
            let len = match (span_count, self.get_type_size(pointee)) {
                (_, None) => None,
                (None, Some(size)) => Some(Expr::bitvec_const(size.max(1) as u128, 64)),
                (Some(count_idx), Some(size)) => dcx
                    .args
                    .get(count_idx)
                    .and_then(|count| {
                        self.translate_operand_with_modified(count, dcx.modified_locals)
                    })
                    .map(|count| {
                        crate::codegen_ay::types::coerce_bitvec_width_safe(
                            count,
                            64,
                            crate::codegen_ay::types::SignExtension::ZeroExtend,
                        )
                        .bvmul(Expr::bitvec_const(size as u128, 64))
                    }),
            };
            let place = match arg {
                Operand::Copy(place) | Operand::Move(place) => Some(place.clone()),
                _ => None,
            };
            let addr = place.and_then(|mut place| {
                place.projection.push(ProjectionElem::Deref);
                self.translate_ref_to_address(&place, dcx.modified_locals)
            });
            let allowed = match (addr, len) {
                (Some(addr), Some(len)) if self.modifies_frames[frame_idx].resolved => {
                    self.modifies_frame_range_allowed(frame_idx, addr.as_expr(), &len)
                }
                _ => None,
            };
            let Some(allowed) = allowed else {
                debug!(bb = dcx.bb_idx, index, %path, "FC-06: call store not checkable — fail-closed");
                self.record_sound_fallback_reason("modifies_frame_call_store_untranslatable");
                continue;
            };
            debug!(bb = dcx.bb_idx, index, %path, exact, "FC-06: emitted call store frame check");
            self.emit_error_rule_for_condition(
                dcx.from_app,
                allowed,
                dcx.stmt_constraints,
                dcx.bb_idx,
            );
            if !exact {
                self.record_sound_fallback_reason("modifies_frame_call_arg_overapprox");
                // Booked separately so the frame net around this call does not
                // count its own check's tag as an effect it cannot see — but
                // only when the check covers everything the call can write
                // through this argument (`call_arg_check_is_self_contained`).
                // Otherwise the tag stays foreign and the net demotes.
                if self.call_arg_check_is_self_contained(pointee, arg) {
                    self.modifies_frame_net.call_arg_check_records += 1;
                } else {
                    debug!(
                        bb = dcx.bb_idx,
                        index,
                        %path,
                        ?arg,
                        pointer_free = pointee_is_pointer_free(pointee),
                        chain = ?self.pointer_chain_trace(arg),
                        "FC-06: call arg check is not self-contained — net keeps the demotion"
                    );
                }
            }
        }
    }

    /// Whether the FC-06 over-approximated check on `arg` (pointee `pointee`)
    /// covers EVERYTHING the call can write through that argument, so the
    /// frame net may treat the check's own tag as covered rather than as an
    /// effect it cannot see (`CallNetSnapshot::foreign_sound_records`).
    ///
    /// The check proves "the `size_of::<T>()` bytes at the argument's address
    /// are assignable". That covers the call's writes through the argument
    /// only when both hold (T2 review, 2026-09-24; each counterexample below
    /// was proved clean with the unconditional exemption while Kani fails it):
    /// - the pointee holds no pointer (`pointee_is_pointer_free`): through a
    ///   `&mut Vec<u8>` the call writes the pre-existing heap buffer
    ///   (`modifies(v); v[0] = 9`, `push` into spare capacity), through a
    ///   `&CH { r: &Cell<u32> }` the referent of `r`;
    /// - the argument's address is DIRECT (`operand_address_is_direct`): a
    ///   borrow chain rooted at a local's own storage or at a function
    ///   argument, with no pointer loaded from memory on the way. For a
    ///   reference loaded from a struct field (`h.r.set(5)`), the check's
    ///   address resolved inside the containing struct, not at the referent.
    fn call_arg_check_is_self_contained(&self, pointee: Ty, arg: &Operand) -> bool {
        pointee_is_pointer_free(pointee) && self.operand_address_is_direct(arg)
    }

    /// The borrow chain `pointer_local_is_direct` walks, for the debug log.
    fn pointer_chain_trace(&self, arg: &Operand) -> Vec<String> {
        let mut out = Vec::new();
        let mut local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            other => return vec![format!("operand {other:?}")],
        };
        for _ in 0..8 {
            if local != 0 && local <= self.body.arg_locals().len() {
                out.push(format!(
                    "_{local}: argument, never rebound = {}",
                    super::modifies_frame_net::arg_never_rebound(self.body, local)
                ));
                break;
            }
            let def = super::modifies_frame_net::unique_def(self.body, local);
            out.push(format!("_{local} = {def:?}"));
            local = match def {
                Some(Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place))
                    if matches!(place.projection.first(), Some(ProjectionElem::Deref)) =>
                {
                    place.local
                }
                Some(
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                    | Rvalue::CopyForDeref(src),
                ) => match self.copied_pointer_source(src) {
                    Some(source) => source,
                    None => {
                        let base = super::modifies_frame_net::unique_def(self.body, src.local);
                        out.push(format!("_{} = {base:?}", src.local));
                        break;
                    }
                },
                _ => break,
            };
        }
        out
    }

    /// `arg` is a whole local whose pointer value is direct (see
    /// [`Self::call_arg_check_is_self_contained`]).
    fn operand_address_is_direct(&self, arg: &Operand) -> bool {
        match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.pointer_local_is_direct(place.local, 0)
            }
            _ => false,
        }
    }

    /// A pointer-valued local is direct when it is a function argument that is
    /// never rebound, or its single definition is a borrow of a direct place or
    /// a copy of another direct pointer local.
    fn pointer_local_is_direct(&self, local: usize, depth: usize) -> bool {
        const MAX_DEPTH: usize = 16;
        if depth > MAX_DEPTH {
            return false;
        }
        let body = self.body;
        if local != 0 && local <= body.arg_locals().len() {
            return super::modifies_frame_net::arg_never_rebound(body, local);
        }
        match super::modifies_frame_net::unique_def(body, local) {
            Some(Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) => {
                self.place_is_direct(place, depth + 1)
            }
            Some(
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                | Rvalue::CopyForDeref(src),
            ) => match self.copied_pointer_source(src) {
                Some(source) => self.pointer_local_is_direct(source, depth + 1),
                None => false,
            },
            _ => false,
        }
    }

    /// The local a copied pointer value came from without passing through
    /// memory: the copied local itself, or — for a field of a local tuple or
    /// closure environment (`_e.0`, how a contract wrapper and an inlined
    /// closure carry their arguments) — the whole local the aggregate's
    /// single definition put in that field. `None` for anything read through
    /// a dereference, a nested projection, or an aggregate that is not the
    /// field's only writer (`unique_def` refuses partial writes and borrows).
    fn copied_pointer_source(&self, src: &Place) -> Option<usize> {
        match src.projection.as_slice() {
            [] => Some(src.local),
            [ProjectionElem::Field(field, _)] => self.aggregate_field_source(src.local, *field),
            _ => None,
        }
    }

    /// The whole local that the single definition of aggregate `local` (a
    /// tuple or closure environment, possibly reached through whole-local
    /// copies) put in `field`.
    fn aggregate_field_source(&self, mut local: usize, field: usize) -> Option<usize> {
        for _ in 0..8 {
            match super::modifies_frame_net::unique_def(self.body, local)? {
                Rvalue::Aggregate(AggregateKind::Tuple | AggregateKind::Closure(..), ops) => {
                    return match ops.get(field)? {
                        Operand::Copy(place) | Operand::Move(place)
                            if place.projection.is_empty() =>
                        {
                            Some(place.local)
                        }
                        _ => None,
                    };
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                    if place.projection.is_empty() =>
                {
                    local = place.local;
                }
                _ => return None,
            }
        }
        None
    }

    /// A borrowed place is direct when it is in a local's own storage, or its
    /// ONLY dereference is the first projection and the dereferenced local is a
    /// direct pointer; every other projection stays inside that object.
    fn place_is_direct(&self, place: &Place, depth: usize) -> bool {
        let (rooted, rest) = match place.projection.split_first() {
            Some((ProjectionElem::Deref, rest)) => {
                (self.pointer_local_is_direct(place.local, depth), rest)
            }
            _ => (true, &place.projection[..]),
        };
        rooted
            && rest.iter().all(|elem| {
                matches!(
                    elem,
                    ProjectionElem::Field(..)
                        | ProjectionElem::Downcast(..)
                        | ProjectionElem::Index(..)
                        | ProjectionElem::ConstantIndex { .. }
                        | ProjectionElem::Subslice { .. }
                )
            })
    }

    /// FC-06: a `copy_nonoverlapping` statement inside a frame writes
    /// `count * size_of::<T>()` bytes at `dst`; they must be assignable.
    pub(in crate::codegen_ay::chc) fn modifies_frame_copy_statement_check(
        &mut self,
        copy: &CopyNonOverlapping,
        modified_locals: &HashSet<usize>,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return;
        };
        let pointee = copy.dst.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(pointee),
            _ => None,
        });
        let len = pointee.and_then(|pointee| self.get_type_size(pointee)).and_then(|size| {
            self.translate_operand_with_modified(&copy.count, modified_locals).map(|count| {
                crate::codegen_ay::types::coerce_bitvec_width_safe(
                    count,
                    64,
                    crate::codegen_ay::types::SignExtension::ZeroExtend,
                )
                .bvmul(Expr::bitvec_const(size as u128, 64))
            })
        });
        let addr = match &copy.dst {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut deref = place.clone();
                deref.projection.push(ProjectionElem::Deref);
                self.translate_ref_to_address(&deref, modified_locals)
            }
            _ => None,
        };
        let allowed = match (addr, len) {
            (Some(addr), Some(len)) if self.modifies_frames[frame_idx].resolved => {
                self.modifies_frame_range_allowed(frame_idx, addr.as_expr(), &len)
            }
            _ => None,
        };
        match allowed {
            Some(allowed) => self.heap_state.pending_checks.push(allowed),
            None => {
                self.record_sound_fallback_reason("modifies_frame_call_store_untranslatable");
            }
        }
    }

    /// Check a register-promoted deref store (`*p = v` lowered to a direct
    /// state-var write via ref_targets / arg-ref / static-ref resolution)
    /// against the active modifies frame.
    ///
    /// These stores bypass `build_memory_store` entirely, so the frame check
    /// resolves the pointer local's value as the store address instead.
    pub(in crate::codegen_ay::chc) fn modifies_frame_ref_store_check(
        &mut self,
        lhs: &rustc_public::mir::Place,
        modified_locals: &HashSet<usize>,
    ) {
        if self.modifies_frames.is_empty()
            || !self.modifies_frame_by_bb.contains_key(&self.current_encode_bb)
        {
            return;
        }
        // Soundness (missed-bug E): compute the FULL store address, INCLUDING
        // the place's Deref+Field/Index projection offsets, via
        // `translate_ref_to_address` (which Deref-loads the pointer then adds
        // each field/index byte offset). The previous code translated only the
        // pointer local's VALUE (`Place{local, projection: []}`), dropping the
        // sub-field offset — so a store to `(*p).b` was checked at `(*p)`'s base
        // and spuriously matched a `modifies((*p).a)` footprint (whose offset IS
        // retained by resolve_modifies_footprint), letting an undeclared-field
        // write escape the frame check (a false Safe, regression from FC-06).
        let Some(addr) = self.translate_ref_to_address(lhs, modified_locals) else {
            // Fail CLOSED: an unchecked store inside the extent must not leave
            // a clean proof behind.
            self.modifies_frame_fail_closed("reg-level deref store address untranslatable");
            return;
        };
        // GUARD DELETED (wave 11): this site used to re-test the width of
        // `translate_ref_to_address`'s result and take `extract(63, 0)` on a
        // 128-bit "fat pointer". That branch is unreachable — the producer's
        // ENSURES states every `Some` result is exactly `POINTER_WIDTH` wide
        // (allocation base `concat(bv32, bv32)`, deref lanes normalized by
        // `normalize_deref_address_expr`, projections width-preserving
        // `bvadd`s), and it now says so in its return type. Re-deriving
        // address shape from a width test is exactly the heuristic this
        // refactor removes.
        //
        // The assertion below restates the ENSURES but is NOT what makes the
        // deletion safe: this workspace sets `profile.dev.debug-assertions =
        // false`, so it is compiled out of the driver. The argument is the
        // structural one above (and a non-`POINTER_WIDTH` `current_addr` could
        // not survive a projection's `bvadd` in the first place).
        debug_assert_eq!(
            addr.as_expr().sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "translate_ref_to_address must mint POINTER_WIDTH addresses"
        );
        let pointee_ty =
            lhs.ty(self.body.locals()).ok().unwrap_or_else(|| self.body.locals()[lhs.local].ty);
        self.modifies_frame_store_check(addr.as_expr(), pointee_ty);
        if let Some(target) = self.ref_resolution.ref_targets.get(&lhs.local).map(|rt| rt.local) {
            self.modifies_frame_certify_local(target);
        }
    }

    /// Check a memory store against the active modifies frame, if any.
    ///
    /// Pushes a fail-if-false pending check: the store address (byte range
    /// `[addr, addr + size_of(pointee_ty))`) must lie within one of the
    /// declared footprint ranges. Violation makes the CHC error state
    /// reachable, failing the harness.
    pub(in crate::codegen_ay::chc) fn modifies_frame_store_check(
        &mut self,
        addr: &Expr,
        pointee_ty: Ty,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        // ZST writes are trivially assignable (no bytes touched).
        if super::call::codegen_call_kani_model_dst::is_zst_ty(pointee_ty) {
            return;
        }
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return;
        };
        let frame = &self.modifies_frames[frame_idx];
        if !frame.resolved {
            self.modifies_frame_fail_closed("store in modifies frame with unresolved footprint");
            return;
        }
        // A FAT-pointer footprint (`#[kani::modifies(s)]` with `s: &mut [T]`)
        // cannot certify. The range's base is the data half of the wrapper
        // argument's 128-bit value, and the address a store inside the extent
        // computes does not reliably carry the same object id, so the check
        // below is falsifiable for stores that are plainly inside the footprint:
        // index 0, index 2, a guarded or assumed symbolic index, `len()-1`,
        // `fill`, `swap`, `copy_from_slice` and `split_at_mut` were ALL certified
        // FAILED (memory_safety) while BMC proved the identical harness
        // (negative/modifies_frame_slice_params.rs, main 31793ccc3). The thin
        // `&mut [T; N]` and `&s[0]` footprints in the same file are exact.
        //
        // The check is still EMITTED — a genuine frame violation must still fail
        // — but the harness is tainted, so a spurious accusation can no longer be
        // certified Genuine and a proof over it is not clean. Until this branch
        // was written the same rows read as EncodingGap only because ONE
        // harness's untranslatable assert was charged to the whole crate.
        let wide_footprint = self.modifies_frames[frame_idx].footprint.iter().any(|r| r.wide);
        if wide_footprint {
            debug!(
                bb = self.current_encode_bb,
                "FC-06: fat-pointer footprint — store check cannot certify"
            );
            self.record_sound_fallback_reason("modifies_frame_slice_footprint_inexact");
        }
        let Some((obj_a, off_a)) = self.split_pointer(addr) else {
            self.modifies_frame_fail_closed("store address not splittable");
            return;
        };
        let store_size = self.get_type_size(pointee_ty).unwrap_or(1).max(1);
        let store_end = off_a.clone().bvadd(Expr::bitvec_const(store_size as u128, 32));
        // DFCC freshness: storage the checked function created is assignable —
        // its stack locals AND its own heap allocations (`frame_local_obj_ids`).
        // Without the stack half a store through `&mut x` to a local of the
        // checked function was accused with a Genuine certificate; without the
        // heap half `let mut bx = Box::new(0); *bx = 1;` inside the function was.
        let frame_local_objs: Vec<u32> = self.frame_local_obj_ids(frame_idx);
        let frame = &self.modifies_frames[frame_idx];
        if Self::const_obj_id_u32(&obj_a).is_some_and(|obj| frame_local_objs.contains(&obj)) {
            debug!(bb = self.current_encode_bb, "FC-06: store to frame-local storage — assignable");
            return;
        }
        let mut allowed = Expr::bool_const(false);
        for obj in frame_local_objs {
            allowed = allowed.or(obj_a.clone().eq(Expr::bitvec_const(u128::from(obj), 32)));
        }
        for range in &frame.footprint {
            let Some((obj_b, off_b)) = self.split_pointer(&range.base) else {
                continue;
            };
            let same_obj = obj_a.clone().eq(obj_b);
            let cond = match &range.size {
                Some(size) => {
                    let starts_after = off_b.clone().bvule(off_a.clone());
                    let ends_before = store_end.clone().bvule(off_b.clone().bvadd(size.clone()));
                    same_obj.and(starts_after).and(ends_before)
                }
                None => same_obj,
            };
            allowed = allowed.or(cond);
        }
        debug!(
            bb = self.current_encode_bb,
            ranges = frame.footprint.len(),
            "FC-06: emitted modifies frame store check"
        );
        self.heap_state.pending_checks.push(allowed);
        self.modifies_frame_certify_addr(addr);
    }
}
