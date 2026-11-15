// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Two MIR-only nets over memory accessed under a type it was not written as.
//! Both are decided per basic block, once per body, over the solved value
//! flow of that body (`untyped_view_flow.rs`: every carrier a value can take,
//! a reference to a local read back through it, a struct, tuple, array or
//! enum field, a closure environment, a call's arguments and result, memory
//! outside the locals), and recorded when the block is encoded
//! (`record_untyped_view_reasons`).
//!
//! 1. `pointer_bytes_rewritten_untyped` (FailClose). The provenance facts
//!    this encoder keeps for a local that holds a pointer — the allocation a
//!    pointer local was built from (`known_alloc_ids`,
//!    `trace_deref_store_alloc_id`), its points-at edge (`ref_targets`), the
//!    operand an aggregate put in a pointer field
//!    (`pointer_field_value_source`), the object an exposed address named when
//!    it was taken — are read off the local's DEFINITIONS. A typed pointer
//!    store into the local fails closed where it is made
//!    (`pointer_stored_through_deref_rebinds_target`,
//!    `pointer_stored_into_aggregate_rebinds_target`), but the local's bytes
//!    can also change with no pointer store at all. A block is refused when:
//!    - it stores through a pointer that may address pointer-carrying bytes
//!      under another type (a pun: `*(addr_of_mut!(a) as *mut usize) = ..`, a
//!      `.cast()`, a transmute), however that pointer got there (a reference
//!      to it read back, a field, a closure capture, an `Option` payload, an
//!      integer launder);
//!    - it copies or writes bytes (`copy_nonoverlapping`, `write_bytes`,
//!      `swap` the typed-swap model cannot exchange) into a local whose
//!      facts are definition-based: a pointer, an aggregate holding one
//!      (an array of two or more elements is read through memory and exempt),
//!      or an integer holding an exposed address;
//!    - it stores through a pointer into an integer local holding an exposed
//!      address (`let pa = &mut addr; *pa = ..`; review of fix/chc-lost-writes
//!      round 7, finding 4);
//!    - it stores into a field of a union that can hold a pointer;
//!    - a call that may write through its arguments receives a punned pointer,
//!      a reference to one, or a reference to an address integer;
//!    - (a body the call walker inlines) a punned pointer leaves through the
//!      return value or memory outside the body.
//!    No exact update of every derived fact is available, so the block fails
//!    closed. The pointee (or the copy's destination) must be able to hold a
//!    pointer value for a pun to count.
//!
//! 2. `static_memory_read_unseeded_view` (SoundHavoc). A static's memory
//!    image is seeded by the entry rule (`register_static_memory_init_entries`)
//!    and written by the static store lanes (`static_image.rs`) under exactly
//!    the views its type decomposes into: the static's own type, each array
//!    element, each field `static_image_fields` gives a struct or tuple (also
//!    inside an array element). A raw read of the static through a pointer
//!    that may name some other view (`*(addr_of!(G) as *const u8).add(2)` for
//!    `G: [u16; 2]`, a field of an enum payload, a super-element view away from
//!    the base) selects a typed-memory cell nothing constrains, a free value. A
//!    proof over a free value is valid for every value, so the reason is
//!    SoundHavoc; what it forbids is a Genuine certificate resting on it. The
//!    pointer is followed through every carrier (review of fix/chc-lost-writes
//!    round 7, findings 1 and 3); a call that may read through its arguments
//!    and receives such a pointer, or a reference to one, is a read; a body the
//!    call walker inlines that hands a static's pointer to its caller (the
//!    return value, memory outside the body) is one too. A static store through
//!    such a pointer is not a read and keeps its own fail-closed handling.
//!
//! 3. `const_pointer_names_model_object` (FailClose). The split pointer numbers
//!    objects from 1 in its high word, so a LITERAL address whose high word is
//!    such a number (`0x2_0000_0000 as *const u8`, a transmute of one,
//!    `without_provenance(0x2_0000_0000)`, a pointer constant with no
//!    provenance) names a model object: a stack slot, a `Box`, a static. The
//!    integer-to-pointer lane's invalidation does not reach a stack local
//!    (whose validity is always true), so a read through it succeeded where
//!    Kani reports an invalid pointer (a missed bug on main). Such a literal
//!    (an integer or a pointer) is followed like the others, and a block fails
//!    closed that dereferences a pointer carrying one, hands one to a call
//!    that may read through it, stores one where another body can load it, or
//!    (an inlined callee) returns one. Handed as a number to a function of the
//!    standard library instantiated on its own data (`checked_mul`,
//!    `Result::is_err`), it is only a number; a harness's function, or a
//!    standard-library one that can reach the harness's code (a closure, a
//!    trait impl of a harness type), may make a pointer of it and read it. A
//!    literal below 2^32 names the null object (exact), and a high word no
//!    harness reaches as an object count (`usize::MAX`, a sentinel) names
//!    nothing.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{BTreeSet, HashMap, HashSet};

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::mir::alloc::AllocId;
use rustc_public::mir::mono::StaticDef;
use rustc_public::mir::visit::{Location, MirVisitor, PlaceContext};
use rustc_public::mir::{
    BinOp, CastKind, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::const_pointer::{ConstRead, TargetKey, const_bytes, target_bytes};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::untyped_view_flow::{Cell, Contents, Flow, FlowRules, Tracked, may_carry};

mod constant_cell;

/// FailClose: pointer-carrying bytes may change without a typed pointer store.
pub(in crate::codegen_ay::chc) const POINTER_BYTES_REWRITTEN_UNTYPED: &str =
    "pointer_bytes_rewritten_untyped";
/// SoundHavoc: a static's memory is read under a view it is never seeded or
/// written under.
pub(in crate::codegen_ay::chc) const STATIC_MEMORY_READ_UNSEEDED_VIEW: &str =
    "static_memory_read_unseeded_view";
/// FailClose: a pointer made from a literal address that names a model object
/// is dereferenced (net 3).
pub(in crate::codegen_ay::chc) const CONST_POINTER_NAMES_MODEL_OBJECT: &str =
    "const_pointer_names_model_object";

/// Object lanes below this bound can name an object a harness allocates.
const MODEL_OBJECT_LANE_BOUND: u64 = 1 << 24;

/// Nesting followed when deciding whether a type can hold a pointer value.
const MAX_POINTER_HOLDER_DEPTH: u32 = 6;

/// Every place one rvalue, statement or terminator mentions.
struct Places(Vec<Place>);

impl MirVisitor for Places {
    fn visit_place(&mut self, place: &Place, _ptx: PlaceContext, _location: Location) {
        self.0.push(place.clone());
    }
}

fn pointee(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => Some(inner),
        _ => None,
    }
}

fn is_integer(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
}

/// Can a value of `ty` hold a pointer (a reference, a raw or function
/// pointer, a `Box`/`Rc`/`NonNull`, or an aggregate containing one)? Past
/// the depth bound the answer is `true`, the conservative side.
pub(super) fn may_hold_pointer(ty: Ty, depth: u32) -> bool {
    if depth > MAX_POINTER_HOLDER_DEPTH {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Ref(..) | RigidTy::RawPtr(..) | RigidTy::FnPtr(..) | RigidTy::Dynamic(..),
        ) => true,
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
            may_hold_pointer(elem, depth + 1)
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().any(|t| may_hold_pointer(*t, depth + 1)),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().into_iter().any(|v| {
            v.fields()
                .into_iter()
                .any(|f| mono_ty::field_ty(&f, &args).is_none_or(|t| may_hold_pointer(t, depth + 1)))
        }),
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Str
            | RigidTy::Never
            // An extern type (a vtable) is opaque and unsized: nothing writes
            // through a pointer to one without casting it first.
            | RigidTy::Foreign(_),
        ) => false,
        // Closures, coroutines, parameters, aliases: unknown, so conservative.
        _ => true,
    }
}

/// Is `view` a view the entry rule seeds for a static of type `whole` at
/// every offset a typed walk from the static's base can reach: the type
/// itself, or the element type of a (nested) array of it?
fn homogeneous_view(whole: Ty, view: Ty) -> bool {
    if whole == view {
        return true;
    }
    // A slice of `E` is read in units of `E` from the base.
    if let TyKind::RigidTy(RigidTy::Slice(elem)) = view.kind() {
        return homogeneous_view(whole, elem);
    }
    match whole.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
            homogeneous_view(elem, view)
        }
        // A `str` is its UTF-8 bytes.
        TyKind::RigidTy(RigidTy::Str) => view == Ty::unsigned_ty(rustc_public::ty::UintTy::U8),
        _ => false,
    }
}

/// The last `::` segment of a callee path (`core::ptr::mut_ptr::<impl *mut
/// T>::add` -> `add`).
fn callee_leaf(path: &str) -> &str {
    path.rsplit("::").next().unwrap_or(path)
}

/// Callees that return (a pointer derived from) their pointer argument and do
/// not access memory through it.
fn is_pointer_arithmetic_callee(leaf: &str) -> bool {
    matches!(
        leaf,
        "add"
            | "sub"
            | "offset"
            | "wrapping_add"
            | "wrapping_sub"
            | "wrapping_offset"
            | "byte_add"
            | "byte_sub"
            | "byte_offset"
            | "wrapping_byte_add"
            | "wrapping_byte_sub"
            | "wrapping_byte_offset"
            | "cast"
            | "cast_mut"
            | "cast_const"
            | "as_ptr"
            | "as_mut_ptr"
            | "as_non_null_ptr"
            | "new_unchecked"
            | "from_raw_parts"
            | "from_raw_parts_mut"
            | "slice_from_raw_parts"
            | "slice_from_raw_parts_mut"
            | "with_metadata_of"
            | "with_addr"
            | "map_addr"
            | "addr"
            | "expose_provenance"
            | "with_exposed_provenance"
            | "with_exposed_provenance_mut"
            | "from_ref"
            | "from_mut"
    )
}

/// Byte-moving arithmetic: the result may point into the middle of a view.
fn is_byte_arithmetic_callee(leaf: &str) -> bool {
    leaf.contains("byte_")
        || matches!(leaf, "with_addr" | "map_addr" | "with_exposed_provenance")
        || leaf == "with_exposed_provenance_mut"
}

/// Callees that only read through, compare, or release their pointer
/// argument: no write of the pointee's bytes.
fn is_non_writing_callee(leaf: &str) -> bool {
    matches!(
        leaf,
        "read"
            | "read_unaligned"
            | "read_volatile"
            | "is_null"
            | "is_aligned"
            | "is_aligned_to"
            | "align_offset"
            | "offset_from"
            | "byte_offset_from"
            | "offset_from_unsigned"
            | "eq"
            | "ne"
            | "partial_cmp"
            | "cmp"
            | "lt"
            | "le"
            | "gt"
            | "ge"
            | "dealloc"
            | "__rust_dealloc"
            | "__rdl_dealloc"
            | "deallocate"
            // A reallocation moves the bytes into a fresh object; no local's
            // bytes change.
            | "realloc"
            | "__rust_realloc"
            | "__rdl_realloc"
            | "grow"
            | "grow_zeroed"
            | "shrink"
            | "vtable_size"
            | "vtable_align"
            | "size_of_val"
            | "align_of_val"
            | "size_of_val_raw"
            | "align_of_val_raw"
            | "metadata"
            | "to_raw_parts"
            | "addr_eq"
            // Kani's memory predicates read a pointer's provenance and bounds.
            | "can_dereference"
            | "can_write"
            | "can_read_unaligned"
            | "can_write_unaligned"
            | "same_allocation"
            | "is_inbounds"
            | "checked_size_of_raw"
            | "checked_align_of_raw"
            | "is_ptr_aligned"
            | "pointer_object"
            | "pointer_offset"
            | "is_allocated"
            | "is_initialized"
            // The standard library's debug-assertion checks
            // (`ub_checks::assert_unsafe_precondition!` expands to a local
            // `precondition_check` over the pointers cast to `*const ()`):
            // they compare addresses and lengths.
            | "precondition_check"
            | "check_language_ub"
            | "check_library_ub"
            | "maybe_is_aligned_and_not_null"
            | "maybe_is_aligned"
            | "maybe_is_nonoverlapping"
            | "is_aligned_and_not_null"
            | "is_nonoverlapping"
            | "is_valid_allocation_size"
    )
}

/// Callees that read their pointer argument's pointee.
fn is_reading_callee(leaf: &str) -> bool {
    matches!(leaf, "read" | "read_unaligned" | "read_volatile")
}

/// Callees that move bytes into (or exchange the bytes of) the memory their
/// pointer arguments name, whatever those bytes are.
///
/// The volatile stores are here by their intrinsic names too. After MIR
/// inlining `ptr::write_volatile(&mut q, p)` is the call
/// `intrinsics::volatile_store(&mut q, p)`, which the CHC lane models as an
/// exact store into `q`'s state variable (`codegen_volatile_store`): no MIR
/// assignment rebinds `q`, so the points-at edge read off `q`'s definition
/// (`ref_targets`, `pointer_field_value_source`) kept naming the old referent,
/// and `*q = 7` wrote it. A local or a pointer field rebound that way gave
/// clean missed bugs and Genuine false certificates on main and on
/// fix/chc-lost-writes (review of fix/chc-lost-writes, lostwrite round 1,
/// finding 5).
fn is_byte_writer_callee(leaf: &str) -> bool {
    matches!(
        leaf,
        "copy"
            | "copy_nonoverlapping"
            | "write_bytes"
            | "swap"
            | "swap_nonoverlapping"
            | "typed_swap_nonoverlapping"
            | "volatile_copy_memory"
            | "volatile_copy_nonoverlapping_memory"
            | "volatile_set_memory"
            | "volatile_store"
            | "unaligned_volatile_store"
            | "write_unaligned"
            | "write_volatile"
    )
}

/// A pointee through which no byte can be written without a further cast: a
/// zero-sized type (`()`, the data pointer of a trait object) or an extern
/// type.
fn is_opaque_view(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Foreign(_)))
        || matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(t)) if t.is_empty())
        || ty.layout().ok().is_some_and(|l| !l.shape().is_unsized() && l.shape().size.bytes() == 0)
}

fn is_dyn(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
}

/// What a cast of a pointer to `from` (a pointer-carrying pointee) into a
/// value of type `to` makes of it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CastView {
    /// The same bytes under the same (or an element) type.
    Same,
    /// A pointer that names no bytes until cast again (`*mut ()`, a trait
    /// object's data pointer, a vtable).
    Erased,
    /// The bytes under another type, or the address as an integer.
    Punned,
}

fn classify_cast(from: Ty, to: Ty) -> CastView {
    match pointee(to) {
        // A trait object cast to another trait object keeps its data and
        // swaps the vtable (`&dyn Fn() as *mut dyn Any`).
        Some(to_pointee) if is_dyn(from) && is_dyn(to_pointee) => CastView::Same,
        Some(to_pointee) if to_pointee == from || is_element_view(from, to_pointee) => {
            CastView::Same
        }
        Some(to_pointee) if is_opaque_view(to_pointee) => CastView::Erased,
        // A trait object's data pointer taken thin (`p as *const u8` inside
        // `is_null`, `addr_eq`, `dealloc`): the concrete type is unknown here,
        // so the pointer is erased; a store through it is still refused.
        Some(_) if is_dyn(from) => CastView::Erased,
        Some(_) => CastView::Punned,
        None if is_integer(to) => CastView::Punned,
        None => CastView::Same,
    }
}

/// Is `to` the element view of `from` (`[E; N]` or `[E]` as `E` or `[E]`)?
/// Such a cast keeps every access typed as the element.
fn is_element_view(from: Ty, to: Ty) -> bool {
    let elem_of = |t: Ty| match t.kind() {
        TyKind::RigidTy(RigidTy::Array(e, _) | RigidTy::Slice(e)) => Some(e),
        _ => None,
    };
    elem_of(from).is_some_and(|e| e == to || elem_of(to) == Some(e))
}

/// Is `arg` of a `mem::swap` / `typed_swap_nonoverlapping` call the address
/// of a thin pointer local that only ever holds a borrow of a local
/// (`let mut p = &mut a;`)? The typed-swap model
/// (`codegen_typed_swap`) exchanges exactly what such a pointer's identity
/// is, its points-at edge; a pointer defined any other way (`&mut *bx`, a
/// `Box`, a call result) also carries an allocation the model does not
/// exchange, which the store through it would then use.
fn swaps_exchanged_exactly(body: &rustc_public::mir::Body, arg: &Operand) -> bool {
    let locals = body.locals();
    let defs_of = |local: usize| -> Vec<&Rvalue> {
        body.blocks
            .iter()
            .flat_map(|b| b.statements.iter())
            .filter_map(|st| match &st.kind {
                // A store THROUGH the local (`(*p) = v`) leaves its bytes alone.
                StatementKind::Assign(lhs, rv)
                    if lhs.local == local
                        && !matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) =>
                {
                    Some((lhs.projection.is_empty(), rv))
                }
                _ => None,
            })
            .map(|(whole, rv)| if whole { Some(rv) } else { None })
            .collect::<Option<Vec<_>>>()
            .unwrap_or_default()
    };
    let is_call_destination = |local: usize| {
        body.blocks.iter().any(|b| {
            matches!(&b.terminator.kind, TerminatorKind::Call { destination, .. } if destination.local == local)
        })
    };
    // Follow the argument back to `&mut L` / `&raw mut L`.
    let Some(mut current) = operand_local(arg) else { return false };
    let mut target = None;
    for _ in 0..8 {
        if is_call_destination(current) {
            return false;
        }
        let defs = defs_of(current);
        let [rv] = defs.as_slice() else { return false };
        match rv {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
            | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                if p.projection.is_empty() =>
            {
                current = p.local;
            }
            // A reborrow `&mut (*x)` holds `x`'s value.
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
            {
                current = place.local;
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if place.projection.is_empty() =>
            {
                target = Some(place.local);
                break;
            }
            _ => return false,
        }
    }
    let Some(target) = target else { return false };
    let thin_pointer = locals.get(target).is_some_and(|d| match d.ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => !matches!(
            inner.kind(),
            TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str | RigidTy::Dynamic(..))
        ),
        _ => false,
    });
    if !thin_pointer || is_call_destination(target) {
        return false;
    }
    let defs = defs_of(target);
    !defs.is_empty()
        && defs.iter().all(|rv| {
            matches!(rv, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if !place.projection.iter().any(|e| matches!(e, ProjectionElem::Deref)))
        })
}

fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

/// The type of every proper prefix of `place` and the element that extends it.
fn place_prefix_types(place: &Place, locals: &[rustc_public::mir::LocalDecl]) -> Vec<Option<Ty>> {
    (0..place.projection.len())
        .map(|k| {
            Place { local: place.local, projection: place.projection[..k].to_vec() }.ty(locals).ok()
        })
        .collect()
}

fn is_union(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == rustc_public::ty::AdtKind::Union
    )
}

/// The static a constant operand's pointer value addresses: the target of its
/// FIRST relocation, whatever the constant's type (a net, so it errs toward
/// following). Read through `shared::const_pointer`, which alone spells
/// rustc's constant representation.
fn static_of_constant(op: &Operand) -> Option<StaticDef> {
    let Operand::Constant(c) = op else { return None };
    let (_, key) = const_bytes(&c.const_)?.relocation_keys().into_iter().next()?;
    key?.static_def()
}

/// The anonymous constant allocation (constant memory: a promoted constant, a
/// literal) a constant operand's pointer value addresses, and whether it
/// addresses its base. `None` when the constant is not one pointer (thin or
/// wide) into such memory. A pointer whose offset bytes are not initialized
/// data is not at its base (fail closed: the view is then unseeded).
pub(super) fn memory_of_constant(op: &Operand) -> Option<(AllocId, bool)> {
    let Operand::Constant(c) = op else { return None };
    let bytes = const_bytes(&c.const_)?;
    let relocations = bytes.relocation_keys();
    let [(0, Some(TargetKey::Memory(id)))] = relocations.as_slice() else {
        return None;
    };
    let at_base = bytes.stored_pointer(0).is_some_and(|ptr| ptr.offset() == 0);
    Some((*id, at_base))
}

/// Do `bytes` hold a pointer into a static or into anonymous constant memory
/// (so a pointer loaded out of them may address either)?
fn bytes_hold_tracked_pointer(bytes: &dyn ConstRead) -> bool {
    bytes.relocation_keys().iter().any(|(_, key)| key.is_some())
}

/// Do the bytes of the target `key` names hold such a pointer (the referent
/// of `static R: &[u16; 2] = &[..]`)? A static whose initializer cannot be
/// evaluated (foreign, generic) may: `true`.
fn target_holds_tracked_pointer(tcx: rustc_middle::ty::TyCtxt<'_>, key: TargetKey) -> bool {
    target_bytes(tcx, &key).is_none_or(|(bytes, _)| bytes_hold_tracked_pointer(&bytes))
}

/// Can a pointer in `body` come to name bytes under a type they were not
/// seeded as: a cast of a pointer to another pointee that is not an element
/// view of it or an erased view, a pointer made from or turned into a
/// non-pointer, a reinterpreting callee, or a union? Anonymous constant memory
/// is followed only in such a body (net 2).
fn body_may_reinterpret(body: &rustc_public::mir::Body, leaves: &HashMap<usize, String>) -> bool {
    let locals = body.locals();
    if locals.iter().any(|d| is_union(d.ty)) {
        return true;
    }
    if leaves.values().any(|leaf| {
        is_byte_arithmetic_callee(leaf)
            || matches!(
                leaf.as_str(),
                "cast"
                    | "cast_mut"
                    | "cast_const"
                    | "addr"
                    | "expose_provenance"
                    | "transmute"
                    | "transmute_copy"
                    | "from_raw_parts"
                    | "from_raw_parts_mut"
            )
    }) {
        return true;
    }
    body.blocks.iter().flat_map(|b| b.statements.iter()).any(|st| {
        let StatementKind::Assign(_, Rvalue::Cast(kind, op, to)) = &st.kind else { return false };
        let from = op.ty(locals).ok();
        let from_pointee = from.and_then(pointee);
        let to_pointee = pointee(*to);
        match kind {
            CastKind::PointerExposeAddress | CastKind::PointerWithExposedProvenance => true,
            CastKind::PtrToPtr | CastKind::Transmute => match (from_pointee, to_pointee) {
                (Some(f), Some(t)) => {
                    !(f == t
                        || is_element_view(f, t)
                        || array_descendant(f, t)
                        || is_opaque_view(t)
                        || is_dyn(t) && is_dyn(f))
                }
                (None, None) => false,
                _ => true,
            },
            _ => false,
        }
    })
}

/// The leaf [`ChcCtx::leaf_of_call`] gives every callee of the panic and
/// formatting machinery.
const FORMATTING_LEAF: &str = "<formatting>";

/// A callee path of the panic or formatting machinery. Its data is the
/// message and its arguments, packed the way the formatting runtime unpacks
/// them (the `fmt::Arguments` of this toolchain holds the message's bytes as a
/// `NonNull<Argument>` next to their tagged address); it prints them and
/// writes through none. Counted as a read of an unseeded view, every
/// promoted-constant message a body panicked with failed its harness's
/// certificate closed (`pointer-overflow/main.rs` and six other parity units).
fn is_formatting_path(path: &str) -> bool {
    path.contains("panicking::")
        || ["core::fmt::", "std::fmt::", "alloc::fmt::"].iter().any(|p| path.starts_with(p))
}

/// A type of the formatting runtime (`core::fmt::rt::Argument`, ...). The
/// panic and formatting machinery, inlined into a body, packs a message's
/// bytes as a pointer to one (this toolchain's `fmt::Arguments` holds the
/// template as `NonNull<Argument>`); only the formatting runtime, which the
/// nets treat as inert, reads it back.
fn is_formatting_runtime_ty(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if {
        let name = def.name();
        name.starts_with("core::fmt::") || name.starts_with("std::fmt::")
    })
}

/// Callees that format or panic: they read their arguments to print them
/// and never write through them or keep them.
fn is_formatting_callee(leaf: &str) -> bool {
    if leaf == FORMATTING_LEAF {
        return true;
    }
    matches!(
        leaf,
        "assert_failed"
            | "assert_failed_inner"
            | "panic"
            | "panic_fmt"
            | "panic_nounwind"
            | "panic_nounwind_fmt"
            | "panic_display"
            | "panic_str"
            | "panic_explicit"
            | "begin_panic"
            | "unreachable_display"
            | "_print"
            | "_eprint"
            | "format"
            | "format_inner"
            | "fmt"
            | "write_fmt"
            | "new_v1"
            | "new_v1_formatted"
            | "new_const"
            | "new_display"
            | "new_debug"
            | "new_lower_hex"
            | "new_upper_hex"
            | "new_pointer"
            | "from_str"
            | "kani_assert"
            // Kani's panic model (`kani_core` `PanicStub`).
            | "panic_stub"
            | "assert"
            | "cover"
            | "assume"
            | "any"
    )
}

/// The argument positions a byte-writer callee writes through.
fn byte_writer_destinations(leaf: &str, argc: usize) -> Vec<usize> {
    match leaf {
        "copy" | "copy_nonoverlapping" => vec![1],
        "write_bytes"
        | "write_unaligned"
        | "write_volatile"
        | "volatile_store"
        | "unaligned_volatile_store"
        | "volatile_copy_memory"
        | "volatile_copy_nonoverlapping_memory"
        | "volatile_set_memory" => vec![0],
        "swap" | "swap_nonoverlapping" | "typed_swap_nonoverlapping" => vec![0, 1],
        _ => (0..argc).collect(),
    }
}

/// The element type of an array or slice.
fn element_of(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => Some(elem),
        // A `str` is its UTF-8 bytes.
        TyKind::RigidTy(RigidTy::Str) => Some(Ty::unsigned_ty(rustc_public::ty::UintTy::U8)),
        _ => None,
    }
}

/// Is `inner` reached from `outer` by descending array and slice elements
/// (a slice of `E` counting as `E`)? Every such view of `outer`'s bytes is on
/// the grid of `outer`'s own elements.
fn array_descendant(outer: Ty, inner: Ty) -> bool {
    let inner = element_of(inner)
        .filter(|_| matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_))))
        .unwrap_or(inner);
    let mut cur = outer;
    for _ in 0..8 {
        let Some(elem) = element_of(cur) else { return false };
        if elem == inner {
            return true;
        }
        cur = elem;
    }
    false
}

/// A mutable reference or raw pointer.
fn is_mut_pointer(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut)
                | RigidTy::RawPtr(_, rustc_public::mir::Mutability::Mut)
        )
    )
}

/// Can a value of `ty` hold a mutable reference or raw pointer (an aggregate,
/// a closure environment)? Past the depth bound the answer is `true`.
fn holds_mut_pointer(ty: Ty, depth: u32) -> bool {
    if depth > MAX_POINTER_HOLDER_DEPTH {
        return true;
    }
    if is_mut_pointer(ty) {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _)) => holds_mut_pointer(elem, depth + 1),
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().any(|t| holds_mut_pointer(*t, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().into_iter().any(|v| {
            v.fields().into_iter().any(|f| {
                mono_ty::field_ty(&f, &args).is_none_or(|t| holds_mut_pointer(t, depth + 1))
            })
        }),
        TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => false,
        TyKind::RigidTy(RigidTy::Closure(..) | RigidTy::Coroutine(..)) => true,
        _ => false,
    }
}

/// An array of two or more elements: its element values are read through
/// memory, not off the local's definition.
fn is_multi_element_array(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(_, len))
        if len.eval_target_usize().ok().is_some_and(|n| n >= 2))
}

// ---------------------------------------------------------------------------
// Net 1: pointers that may address pointer-carrying bytes under another type.
// ---------------------------------------------------------------------------

/// What net 1 tracks about a value.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
struct Pun {
    /// May address pointer-carrying bytes under another type (or be such an
    /// address as an integer).
    punned: bool,
    /// May address pointer-carrying bytes through an opaque view (`*mut ()`,
    /// a trait object's data pointer): harmless until cast to a view with
    /// bytes, which is a pun.
    erased: bool,
    /// May be (or hold) an exposed address: an integer made from a pointer.
    addr: bool,
}

impl Tracked for Pun {
    fn join(&self, other: &Self) -> Self {
        Pun {
            punned: self.punned || other.punned,
            erased: self.erased || other.erased,
            addr: self.addr || other.addr,
        }
    }
}

/// Does a value of type `to` read the bytes a pointer names: a pointer to a
/// view with bytes, or the address as an integer?
fn reinterprets_bytes(to: Ty) -> bool {
    match pointee(to) {
        Some(p) => !is_opaque_view(p),
        None => is_integer(to),
    }
}

/// What a cast of kind `kind` from `from` to `to` makes of a value carrying
/// `v` (net 1).
fn pun_cast(kind: &CastKind, from: Option<Ty>, to: Ty, v: Option<Pun>) -> Option<Pun> {
    // An unsizing or mutability coercion keeps the data's type (a trait
    // object is still accessed as its concrete type through the vtable).
    if matches!(kind, CastKind::PointerCoercion(_)) {
        return v;
    }
    let mut out = v.unwrap_or_default();
    let from_pointee = from.and_then(pointee);
    if from_pointee.is_some() && is_integer(to) {
        out.addr = true;
    }
    if out.erased && reinterprets_bytes(to) {
        out.punned = true;
    }
    if let Some(from) = from_pointee
        && may_hold_pointer(from, 0)
    {
        match classify_cast(from, to) {
            CastView::Punned => out.punned = true,
            CastView::Erased => out.erased = true,
            CastView::Same => {}
        }
    }
    (out != Pun::default()).then_some(out)
}

struct PunRules;

impl FlowRules for PunRules {
    type V = Pun;

    fn constant(&self, _op: &Operand, _ty: Option<Ty>) -> Option<Pun> {
        None
    }

    fn cast(
        &self,
        kind: &CastKind,
        _op: &Operand,
        from: Option<Ty>,
        to: Ty,
        v: Option<Pun>,
    ) -> Option<Pun> {
        pun_cast(kind, from, to, v)
    }

    fn retype(&self, v: Pun, _holder: Option<Ty>) -> Option<Pun> {
        Some(v)
    }

    fn reborrow(&self, v: Pun, _pointee: Option<Ty>, _rest: &[ProjectionElem]) -> Option<Pun> {
        Some(v)
    }

    fn arith(&self, _op: Option<&BinOp>, v: Pun, _ty: Option<Ty>) -> Option<Pun> {
        Some(v)
    }

    fn load(&self, _v: &Pun, _loaded: Option<Ty>) -> Option<Pun> {
        None
    }

    fn pointer_call(
        &self,
        leaf: &str,
        _callee_ty: Option<Ty>,
        _ops: &[Operand],
        args: &[(Option<Ty>, Option<Pun>)],
        dest: Option<Ty>,
    ) -> Option<Option<Pun>> {
        if !is_pointer_arithmetic_callee(leaf) {
            return None;
        }
        let tracked = args.iter().filter_map(|(_, v)| *v).fold(Pun::default(), |a, b| a.join(&b));
        // `.cast::<U>()` reinterprets the pointee like an `as` cast, and
        // `.addr()` / `.expose_provenance()` turn the address into an integer.
        // The other pointer-returning callees (`Vec::as_mut_ptr`,
        // `NonNull::as_ptr`) name another object or the same pointee.
        let reinterpreting = matches!(leaf, "cast" | "cast_mut" | "cast_const" | "addr")
            || leaf == "expose_provenance";
        let mut out = Pun { punned: tracked.punned, erased: false, addr: tracked.addr };
        if reinterpreting && let Some(to) = dest {
            for (ty, v) in args {
                if let Some(cast) = pun_cast(&CastKind::PtrToPtr, *ty, to, *v) {
                    out = out.join(&cast);
                }
            }
            if is_integer(to) {
                out.addr = true;
            }
        } else if tracked.erased {
            out.erased = true;
        }
        Some((out != Pun::default()).then_some(out))
    }

    fn is_inert_callee(&self, leaf: &str) -> bool {
        is_non_writing_callee(leaf) || is_formatting_callee(leaf)
    }

    fn through_memory(&self, v: Pun) -> Pun {
        v
    }
}

// ---------------------------------------------------------------------------
// Net 2: pointers into a static's memory, and the view they read it under.
// ---------------------------------------------------------------------------

/// Where the memory a net-2 pointer addresses lives, and how its image is
/// seeded.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Origin {
    /// A static's image (`register_static_memory_init_entries`).
    Static(StaticDef),
    /// Anonymous constant memory (`GlobalAlloc::Memory`), immutable.
    /// `static_image`: the referent of a static's pointer, seeded like a
    /// static (`codegen_decl_static_alloc.rs`); otherwise a promoted constant,
    /// seeded by the constant-reference decoder (`codegen_decl_ref_const_*`),
    /// whose field cells are not the static image's.
    Memory { id: AllocId, static_image: bool },
    /// One of several promoted constants.
    Consts,
}

impl Origin {
    /// Memory seeded by the constant decoder (a promoted constant).
    fn promoted(origin: Option<Origin>) -> bool {
        matches!(origin, Some(Origin::Memory { static_image: false, .. } | Origin::Consts))
    }
}

/// What net 2 tracks about a value.
#[derive(Clone, PartialEq, Debug)]
enum StaticView {
    /// May address a static's memory under a view the image does not seed
    /// (or be such an address as an integer).
    Unseeded,
    /// One of several pointers, each into a static's or a constant's memory
    /// under a view its image seeds, whose views do not join (the fields of
    /// one aggregate, memory outside the locals: the pieces and arguments of
    /// an `fmt::Arguments`). None of them names an unseeded view; which one a
    /// load yields is known only from the type it is loaded as.
    Mixed {
        /// Some member's memory holds a pointer to a static or constant.
        holds_static_pointers: bool,
        /// Every member points into promoted constants.
        promoted: bool,
        /// Some member gained its view from the exact byte-entry check.
        byte_view: bool,
    },
    /// Addresses a static of type `whole` under the seeded view `view`, at a
    /// position whose image value has sort `sort` (`None`: unknown, so no
    /// field of it counts as seeded).
    Seeded {
        whole: Ty,
        view: Ty,
        sort: Option<Sort>,
        /// The pointer addresses the static's base.
        at_base: bool,
        /// The static's initializer holds a pointer to a static.
        holds_static_pointers: bool,
        /// The static or constant memory itself (`None`: one of several of the
        /// same type).
        origin: Option<Origin>,
        /// Made from the static's address by one chain of copies and borrows
        /// of places (`&(*p).f`, `&((*p) as Some).0`) through single-definition
        /// locals: the encoder resolves a read through it to the static's
        /// state variable (`static_ref_to_state_idx`, `ref_targets`), never to
        /// its memory image, so a field of an enum payload or of an undecomposed
        /// value read through it is exact.
        direct: bool,
        /// Exact native byte offset in one promoted allocation. This fact is
        /// independent of its canonical datatype encoding and image sort.
        const_offset: Option<u64>,
        /// This view gained authority from a native-byte entry, which an
        /// opaque call must never launder into an unrelated returned pointer.
        byte_view: bool,
    },
}

impl StaticView {
    fn byte_view(&self) -> bool {
        match self {
            StaticView::Seeded { byte_view, .. } | StaticView::Mixed { byte_view, .. } => {
                *byte_view
            }
            StaticView::Unseeded => false,
        }
    }

    fn holds_pointers(&self) -> bool {
        match self {
            StaticView::Seeded { holds_static_pointers, .. }
            | StaticView::Mixed { holds_static_pointers, .. } => *holds_static_pointers,
            StaticView::Unseeded => false,
        }
    }

    /// Points into promoted constants only.
    fn promoted(&self) -> bool {
        match self {
            StaticView::Seeded { origin, .. } => Origin::promoted(*origin),
            StaticView::Mixed { promoted, .. } => *promoted,
            StaticView::Unseeded => false,
        }
    }
}

impl Tracked for StaticView {
    /// Two pointers that may each be the value. The same view joins to itself
    /// (off its base when the memories differ); two views where one is an
    /// element-grid descendant of the other join to the DEEPER one, off its
    /// base, which every memory seeding the shallower view seeds too (a static
    /// image decomposes arrays element by element, a constant array seeds its
    /// elements, a `str` its bytes). A read through the join under that view
    /// is seeded whichever pointer it is; any other view is not. The same
    /// constant under `str`, `[u8]` and `u8` (a panic message's bytes) joined
    /// to "unseeded" before, and every call reaching the cell counted as an
    /// unseeded read.
    fn join(&self, other: &Self) -> Self {
        let (
            StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct,
                const_offset,
                byte_view,
            },
            StaticView::Seeded {
                whole: whole2,
                view: view2,
                sort: sort2,
                at_base: at_base2,
                holds_static_pointers: holds2,
                origin: origin2,
                direct: direct2,
                const_offset: const_offset2,
                byte_view: byte_view2,
            },
        ) = (self, other)
        else {
            return match (self, other) {
                (StaticView::Unseeded, _) | (_, StaticView::Unseeded) => StaticView::Unseeded,
                _ => StaticView::Mixed {
                    holds_static_pointers: self.holds_pointers() || other.holds_pointers(),
                    promoted: self.promoted() && other.promoted(),
                    byte_view: self.byte_view() || other.byte_view(),
                },
            };
        };
        let promoted = self.promoted() && other.promoted();
        let origin = if origin == origin2 {
            *origin
        } else if promoted {
            Some(Origin::Consts)
        } else {
            None
        };
        let holds_static_pointers = *holds_static_pointers || *holds2;
        // The whole the join keeps decides whether element arithmetic keeps
        // the view (`arith`): keep one whose element grid does NOT hold the
        // view when there is one (a struct field moved by an offset reaches
        // its siblings).
        let on_grid = |w: Ty, v: Ty| w == v || array_descendant(w, v);
        let pick_whole = |v: Ty| if on_grid(*whole, v) { *whole2 } else { *whole };
        if view == view2 {
            let same_memory = whole == whole2 && origin.is_some();
            return StaticView::Seeded {
                whole: if whole == whole2 { *whole } else { pick_whole(*view) },
                view: *view,
                sort: if sort == sort2 { sort.clone() } else { None },
                at_base: *at_base && *at_base2 && same_memory,
                holds_static_pointers,
                origin,
                direct: *direct && *direct2 && same_memory,
                const_offset: if same_memory
                    && matches!(origin, Some(Origin::Memory { static_image: false, .. }))
                    && const_offset == const_offset2
                {
                    *const_offset
                } else {
                    None
                },
                byte_view: *byte_view || *byte_view2,
            };
        }
        let (view, sort) = if array_descendant(*view, *view2) {
            (*view2, sort2.clone())
        } else if array_descendant(*view2, *view) {
            (*view, sort.clone())
        } else {
            return StaticView::Mixed {
                holds_static_pointers,
                promoted,
                byte_view: *byte_view || *byte_view2,
            };
        };
        StaticView::Seeded {
            whole: pick_whole(view),
            view,
            sort,
            at_base: false,
            holds_static_pointers,
            origin,
            direct: false,
            const_offset: None,
            byte_view: *byte_view || *byte_view2,
        }
    }
}

struct StaticRules<'c, 'tcx, 'body> {
    ctx: &'c ChcCtx<'tcx, 'body>,
    /// Follow pointers into anonymous constant memory (a body that may
    /// reinterpret a pointer, [`body_may_reinterpret`]).
    track_consts: bool,
}

impl StaticRules<'_, '_, '_> {
    fn size(&self, ty: Ty) -> Option<usize> {
        self.ctx.get_type_size(ty)
    }

    /// The image sort at the position of view `to` below a value of type
    /// `from` whose image sort is `sort`, `to` being `from` or one of its
    /// (nested) array elements; for a slice view `[E]`, the level of the array
    /// whose elements are `E`.
    fn descend_sort(from: Ty, to: Ty, sort: Option<Sort>) -> Option<Sort> {
        let (target, slice) = match to.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => (elem, true),
            _ => (to, false),
        };
        let mut ty = from;
        let mut sort = sort?;
        for _ in 0..8 {
            if slice && element_of(ty) == Some(target) || !slice && ty == target {
                return Some(sort);
            }
            ty = element_of(ty)?;
            sort = sort.array_sort()?.element_sort.clone();
        }
        None
    }

    /// The image sort at view `view` of a static of type `whole`.
    fn chain_sort(&self, whole: Ty, view: Ty) -> Option<Sort> {
        Self::descend_sort(whole, view, ChcCtx::translate_ty(whole))
    }

    /// What a pointer held in `alloc` addresses: each static it names at the
    /// offset its bytes give (a static at offset 0 under its own type is a
    /// seeded view; anything else is not), and each anonymous constant
    /// allocation it names, under the loaded pointer's pointee type, seeded
    /// like a static when `static_image` (the memory a static's pointer holds)
    /// and by the constant decoder otherwise.
    fn loaded_view(
        &self,
        alloc: &dyn ConstRead,
        static_image: bool,
        loaded: Option<Ty>,
    ) -> StaticView {
        let mut out: Option<StaticView> = None;
        let relocations = alloc.relocation_keys();
        for (offset, key) in &relocations {
            let at_base = alloc.stored_pointer(*offset).is_some_and(|ptr| ptr.offset() == 0);
            let v = match *key {
                Some(TargetKey::Static(target)) => {
                    // A nested static (`static mut FOO: &mut i32 = &mut 12`) has no
                    // type of its own to ask for: it is the referent of the pointer
                    // that names it, so its type is the loaded pointer's pointee.
                    let whole = match self.ctx.static_type(target) {
                        Some(ty) => ty,
                        None => match loaded.and_then(pointee) {
                            Some(p) if relocations.len() == 1 => p,
                            _ => return StaticView::Unseeded,
                        },
                    };
                    if at_base {
                        StaticView::Seeded {
                            whole,
                            view: whole,
                            sort: ChcCtx::translate_ty(whole),
                            at_base: true,
                            holds_static_pointers: may_hold_pointer(whole, 0)
                                && target_holds_tracked_pointer(
                                    self.ctx.tcx,
                                    TargetKey::Static(target),
                                ),
                            origin: Some(Origin::Static(target)),
                            direct: false,
                            const_offset: None,
                            byte_view: false,
                        }
                    } else {
                        StaticView::Unseeded
                    }
                }
                // Constant memory: a well-typed load of a pointer of type
                // `loaded` names memory of its pointee type.
                Some(TargetKey::Memory(id)) => {
                    let Some(whole) = loaded.and_then(pointee) else {
                        return StaticView::Unseeded;
                    };
                    if at_base {
                        StaticView::Seeded {
                            whole,
                            view: whole,
                            sort: if static_image { ChcCtx::translate_ty(whole) } else { None },
                            at_base: true,
                            holds_static_pointers: may_hold_pointer(whole, 0)
                                && target_holds_tracked_pointer(
                                    self.ctx.tcx,
                                    TargetKey::Memory(id),
                                ),
                            origin: Some(Origin::Memory { id, static_image }),
                            direct: false,
                            const_offset: None,
                            byte_view: false,
                        }
                    } else {
                        StaticView::Unseeded
                    }
                }
                None => continue,
            };
            out = Some(match out {
                None => v,
                Some(o) => o.join(&v),
            });
        }
        out.unwrap_or(StaticView::Unseeded)
    }

    /// Is the memory `origin` names seeded like a static's image and never
    /// written after entry (so a wrapper's content cells are seeded,
    /// [`ChcCtx::static_image_wrapper_content`])?
    fn immutable_static_image(&self, origin: Option<Origin>) -> bool {
        match origin {
            Some(Origin::Static(def)) => !self.ctx.tcx.is_mutable_static(
                rustc_public::rustc_internal::internal(self.ctx.tcx, def.def_id()),
            ),
            Some(Origin::Memory { static_image, .. }) => static_image,
            Some(Origin::Consts) | None => false,
        }
    }

    /// `ty` itself, or the content an immutable static image decomposes the
    /// wrapper `ty` as.
    fn image_content(&self, ty: Ty, origin: Option<Origin>) -> Ty {
        if self.immutable_static_image(origin)
            && let Some(content) = self.ctx.static_image_wrapper_content(ty)
        {
            return content;
        }
        ty
    }

    /// A value of `ty` is read under one cell only: it has no element or field
    /// the image could hold separately.
    fn image_leaf(ty: Ty) -> bool {
        matches!(
            ty.kind(),
            TyKind::RigidTy(
                RigidTy::Bool
                    | RigidTy::Char
                    | RigidTy::Int(_)
                    | RigidTy::Uint(_)
                    | RigidTy::Float(_)
                    | RigidTy::RawPtr(..)
                    | RigidTy::Ref(..)
                    | RigidTy::FnPtr(..)
            )
        )
    }

    /// Does re-typing a view of `outer` as `inner`, a wrapper the typed memory
    /// keys like its content (`UnsafeCell<T>`, `MaybeUninit<T>` as `T`), read
    /// seeded cells? Only when `inner` has one cell (a scalar: the wrapper's
    /// own cell is it), or when the image decomposes the wrapper as its content
    /// (an immutable static's `MaybeUninit` / `ManuallyDrop`). A
    /// `MaybeUninit<[u16; 2]>` read as its elements otherwise selected element
    /// cells nothing seeds (review of fix/chc-lost-writes round 3, finding 2).
    fn wrapper_keeps_view(&self, outer: Ty, inner: Ty, origin: Option<Origin>) -> bool {
        if ChcCtx::type_key_for_ty(outer) != ChcCtx::type_key_for_ty(inner)
            || self.size(outer).is_none()
            || self.size(outer) != self.size(inner)
        {
            return false;
        }
        Self::image_leaf(inner)
            || self.image_content(outer, origin) != outer
                && self.image_content(outer, origin) == self.image_content(inner, origin)
    }

    /// A constant pointer into anonymous constant memory (a promoted `&[1u16,
    /// 0x0102]`, a literal): its pointee type, seeded by the constant-reference
    /// decoder, at its base. Followed only in a body that may reinterpret a
    /// pointer ([`body_may_reinterpret`]); a constant that is not one pointer
    /// (an aggregate holding several) is not followed.
    fn constant_memory(&self, op: &Operand, ty: Option<Ty>) -> Option<StaticView> {
        if !self.track_consts {
            return None;
        }
        let (id, at_base) = memory_of_constant(op)?;
        let whole = ty.and_then(pointee)?;
        // A string literal is not followed: it is every panic message and
        // format template, which the inlined formatting machinery packs with
        // byte arithmetic and casts into its own types (a `NonNull<Argument>`
        // tagged through `map_addr`), and following it made every call of a
        // panicking body an unseeded read. Its bytes are seeded, so only a
        // read of a literal under a view wider than a byte goes unfollowed.
        if matches!(whole.kind(), TyKind::RigidTy(RigidTy::Str)) {
            return None;
        }
        if !at_base {
            return Some(StaticView::Unseeded);
        }
        Some(StaticView::Seeded {
            whole,
            view: whole,
            // The decoder's field cells are not the static image's.
            sort: None,
            at_base: true,
            holds_static_pointers: may_hold_pointer(whole, 0)
                && target_holds_tracked_pointer(self.ctx.tcx, TargetKey::Memory(id)),
            origin: Some(Origin::Memory { id, static_image: false }),
            // A read through the constant's reference resolves to its decoded
            // value (`const_ref_values`), not to memory.
            direct: true,
            // Restrict the new authority to the pointer-free value family
            // whose immutable native layout the constant decoder checks.
            const_offset: self.ctx.const_safe_value_supported(whole, 0).then_some(0),
            byte_view: false,
        })
    }

    /// The same pointer re-typed to address `n`.
    fn view_change(&self, v: StaticView, n: Ty) -> StaticView {
        // A member of a join loaded as `n`: a well-typed load yields the
        // member whose view is `n` (a reinterpreted member is `Unseeded`
        // already, and so is the join). Element moves need its whole, which is
        // lost: the unit type stands for a whole whose grid holds no view, so
        // `arith` treats an offset as leaving the view, and no field of `n`
        // counts as seeded (no sort).
        if let StaticView::Mixed { holds_static_pointers, promoted, byte_view } = v {
            if byte_view {
                return StaticView::Unseeded;
            }
            return StaticView::Seeded {
                whole: Ty::new_tuple(&[]),
                view: n,
                sort: None,
                at_base: false,
                holds_static_pointers,
                origin: promoted.then_some(Origin::Consts),
                direct: false,
                const_offset: None,
                byte_view,
            };
        }
        let StaticView::Seeded {
            whole,
            view,
            sort,
            at_base,
            holds_static_pointers,
            origin,
            direct,
            const_offset,
            byte_view,
        } = v
        else {
            return StaticView::Unseeded;
        };
        if n == view {
            return StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct,
                const_offset,
                byte_view,
            };
        }
        if byte_view {
            return StaticView::Unseeded;
        }
        // This is an independently seeded native byte cell, never a cast of
        // the whole value's canonical datatype bits.
        if self.seeded_const_byte(origin, const_offset, n) {
            return StaticView::Seeded {
                whole,
                view: n,
                sort: None,
                at_base,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset,
                byte_view: true,
            };
        }
        // An erased view (`*const ()`, an extern type, a trait object) names
        // no bytes until it is cast again, and the cast back is checked
        // against the view kept here: Kani's contract instrumentation erases a
        // static's pointer to `*const ()` for its write set
        // (`function-contract/modifies/global_replace_fail.rs`), and the next
        // read is through the static's own type.
        if is_opaque_view(n) || is_dyn(n) {
            return StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset: None,
                byte_view,
            };
        }
        // A promoted constant's bytes packed for the formatting runtime (a
        // panic message's template as `NonNull<fmt::rt::Argument>`) are not
        // read in the body; followed as an unseeded view, they made every
        // call a panicking body makes an unseeded read (`Cleanup/unwind_fixme.rs`).
        if Origin::promoted(origin) && is_formatting_runtime_ty(n) {
            return StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset: None,
                byte_view,
            };
        }
        // A promoted constant's direct chain (copies and casts of the
        // constant's reference) keeps its decoded value: the encoder answers a
        // read through it from `const_ref_values`, carried across the casts,
        // so a type encoded exactly like the view reads the same bits
        // (`*(&100u32 as *const u32 as *const char)`).
        if direct
            && matches!(origin, Some(Origin::Memory { static_image: false, .. }))
            && ChcCtx::translate_ty(n).is_some()
            && ChcCtx::translate_ty(n) == ChcCtx::translate_ty(view)
        {
            return StaticView::Seeded {
                whole,
                view: n,
                sort: None,
                at_base,
                holds_static_pointers,
                origin,
                direct,
                const_offset: None,
                byte_view,
            };
        }
        // A wrapper the image decomposes as its content is its content.
        let (whole, view) = (self.image_content(whole, origin), self.image_content(view, origin));
        if n == view {
            return StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset: None,
                byte_view,
            };
        }
        // Another view: a cast, which the place resolution does not follow.
        let seeded = |view: Ty, sort: Option<Sort>| StaticView::Seeded {
            whole,
            view,
            sort,
            at_base,
            holds_static_pointers,
            origin,
            direct: false,
            const_offset: None,
            byte_view,
        };
        // A (nested) element of the current view: on the current view's grid.
        if array_descendant(view, n) {
            return seeded(n, Self::descend_sort(view, n, sort));
        }
        // The whole, or one of its elements, from the static's base.
        if at_base && (n == whole || array_descendant(whole, n)) {
            return seeded(n, self.chain_sort(whole, n));
        }
        // A field at offset 0 of the same size, through any number of such
        // fields, each one a seeded field view.
        let (mut cur, mut cur_sort) = (view, sort.clone());
        for _ in 0..4 {
            let Some(so) = cur_sort.clone() else { break };
            let Some(fields) = self.ctx.static_image_field_views(cur, &so) else { break };
            let size = self.size(cur);
            let Some((field_ty, field_sort, _)) =
                fields.into_iter().find(|(t, _, off)| *off == 0 && self.size(*t) == size)
            else {
                break;
            };
            cur = field_ty;
            cur_sort = Some(field_sort);
            if cur == n {
                return seeded(n, cur_sort);
            }
        }
        // A wrapper the typed memory keys like its content (`UnsafeCell<T>`
        // as `T`): the same cells, when they are seeded.
        if self.wrapper_keeps_view(view, n, origin) {
            return seeded(n, sort);
        }
        StaticView::Unseeded
    }

    /// Walk `rest` (no dereference) from a pointer carrying `v` to the view
    /// the place it names is read under.
    fn walk(&self, v: StaticView, pointee: Option<Ty>, rest: &[ProjectionElem]) -> StaticView {
        let v = match pointee {
            Some(p) => self.view_change(v, p),
            None => v,
        };
        let StaticView::Seeded {
            whole,
            view,
            sort,
            mut at_base,
            holds_static_pointers,
            origin,
            direct,
            mut const_offset,
            byte_view,
        } = v
        else {
            return StaticView::Unseeded;
        };
        let (mut cur, mut cur_sort) = (view, sort);
        for elem in rest {
            match elem {
                ProjectionElem::Field(idx, field_ty) => {
                    const_offset =
                        self.const_tuple_field_offset(cur, *idx, *field_ty, const_offset);
                    let views =
                        cur_sort.as_ref().and_then(|so| self.ctx.static_image_field_views(cur, so));
                    match views.and_then(|fields| fields.into_iter().nth(*idx)) {
                        Some((_, field_sort, offset)) => {
                            at_base &= offset == 0;
                            cur = *field_ty;
                            cur_sort = Some(field_sort);
                        }
                        None => {
                            // A wrapper keyed like its content (`UnsafeCell`),
                            // when those cells are seeded.
                            if self.wrapper_keeps_view(cur, *field_ty, origin) {
                                cur = *field_ty;
                            } else if direct {
                                // Resolved to the static's place, not its image.
                                at_base = false;
                                cur = *field_ty;
                                cur_sort = None;
                            } else {
                                return StaticView::Unseeded;
                            }
                        }
                    }
                }
                // An enum's variants are not decomposed in the image; a direct
                // pointer resolves to the static's place.
                ProjectionElem::Downcast(_) if direct => {
                    cur_sort = None;
                    const_offset = None;
                }
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                    let Some(elem_ty) = element_of(cur) else { return StaticView::Unseeded };
                    cur = elem_ty;
                    cur_sort =
                        cur_sort.and_then(|so| so.array_sort().map(|a| a.element_sort.clone()));
                    at_base = false;
                    const_offset = None;
                }
                ProjectionElem::Subslice { .. } => {
                    at_base = false;
                    const_offset = None;
                }
                ProjectionElem::OpaqueCast(ty) => {
                    if byte_view && *ty != cur {
                        return StaticView::Unseeded;
                    }
                    cur = *ty;
                    const_offset = None;
                }
                // An enum's variants are not decomposed.
                _ => return StaticView::Unseeded,
            }
        }
        StaticView::Seeded {
            whole,
            view: cur,
            sort: cur_sort,
            at_base,
            holds_static_pointers,
            origin,
            direct,
            const_offset,
            byte_view,
        }
    }
}

impl FlowRules for StaticRules<'_, '_, '_> {
    type V = StaticView;

    fn constant(&self, op: &Operand, ty: Option<Ty>) -> Option<StaticView> {
        let Some(def) = static_of_constant(op) else {
            return self.constant_memory(op, ty);
        };
        let Some(whole) = self.ctx.static_type(def) else { return Some(StaticView::Unseeded) };
        let holds_static_pointers = may_hold_pointer(whole, 0)
            && target_holds_tracked_pointer(self.ctx.tcx, TargetKey::Static(def));
        let Some(view) = ty.and_then(pointee) else { return Some(StaticView::Unseeded) };
        let origin = Some(Origin::Static(def));
        if view == whole {
            return Some(StaticView::Seeded {
                whole,
                view,
                sort: ChcCtx::translate_ty(whole),
                at_base: true,
                holds_static_pointers,
                origin,
                direct: true,
                const_offset: None,
                byte_view: false,
            });
        }
        if homogeneous_view(whole, view) {
            return Some(StaticView::Seeded {
                whole,
                view,
                sort: self.chain_sort(whole, view),
                at_base: false,
                holds_static_pointers,
                origin,
                direct: true,
                const_offset: None,
                byte_view: false,
            });
        }
        Some(StaticView::Unseeded)
    }

    fn cast(
        &self,
        _kind: &CastKind,
        _op: &Operand,
        _from: Option<Ty>,
        _to: Ty,
        v: Option<StaticView>,
    ) -> Option<StaticView> {
        // The assignment re-types the value to the cast's target.
        v
    }

    fn retype(&self, v: StaticView, holder: Option<Ty>) -> Option<StaticView> {
        let Some(holder) = holder else { return Some(v) };
        if let Some(n) = pointee(holder) {
            return Some(self.view_change(v, n));
        }
        match holder.kind() {
            // The address as a number. A promoted constant's address as a
            // number is not followed: every way back to a pointer from it
            // records its own reason (the integer-to-pointer lane, or a
            // transmute taking it), and followed through memory it made every
            // pointer loaded from memory outside the locals unseeded (Kani's
            // uninit shadow memory is keyed by such addresses:
            // `Cleanup/unwind_fixme.rs`).
            TyKind::RigidTy(
                RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Bool
                | RigidTy::Char,
            ) => (!v.promoted()).then_some(StaticView::Unseeded),
            // Held inside an aggregate: kept as it is, but a field load is not
            // a chain the place resolution follows.
            _ => Some(self.through_memory(v)),
        }
    }

    fn reborrow(
        &self,
        v: StaticView,
        pointee: Option<Ty>,
        rest: &[ProjectionElem],
    ) -> Option<StaticView> {
        Some(self.walk(v, pointee, rest))
    }

    fn arith(&self, op: Option<&BinOp>, v: StaticView, _ty: Option<Ty>) -> Option<StaticView> {
        let StaticView::Seeded {
            whole, view, sort, holds_static_pointers, origin, byte_view, ..
        } = v
        else {
            return Some(StaticView::Unseeded);
        };
        // Element arithmetic keeps every seeded view only when the unit is
        // on the static's element grid; a field of a struct static reaches
        // its siblings, and integer arithmetic on an address is a number.
        if matches!(op, Some(BinOp::Offset)) && (view == whole || array_descendant(whole, view)) {
            return Some(StaticView::Seeded {
                whole,
                view,
                sort,
                at_base: false,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset: None,
                byte_view,
            });
        }
        Some(StaticView::Unseeded)
    }

    fn load(&self, v: &StaticView, loaded: Option<Ty>) -> Option<StaticView> {
        // A pointer loaded out of a static whose initializer holds a pointer
        // to a static addresses that static: at its base, under its own
        // type, when the initializer says so; otherwise under any view.
        match v {
            StaticView::Seeded { holds_static_pointers: true, origin, .. }
                if loaded.is_none_or(|t| may_hold_pointer(t, 0)) =>
            {
                // The target's bytes through `shared::const_pointer`; a static
                // whose initializer cannot be evaluated (foreign, generic) gives
                // no view.
                let loaded_from = |key: TargetKey, image| {
                    target_bytes(self.ctx.tcx, &key).map_or(StaticView::Unseeded, |(bytes, _)| {
                        self.loaded_view(&bytes, image, loaded)
                    })
                };
                Some(match origin {
                    Some(Origin::Static(def)) => loaded_from(TargetKey::Static(*def), true),
                    Some(Origin::Memory { id, static_image }) => {
                        loaded_from(TargetKey::Memory(*id), *static_image)
                    }
                    Some(Origin::Consts) | None => StaticView::Unseeded,
                })
            }
            StaticView::Mixed { holds_static_pointers: true, .. }
                if loaded.is_none_or(|t| may_hold_pointer(t, 0)) =>
            {
                Some(StaticView::Unseeded)
            }
            _ => None,
        }
    }

    fn pointer_call(
        &self,
        leaf: &str,
        callee_ty: Option<Ty>,
        _ops: &[Operand],
        args: &[(Option<Ty>, Option<StaticView>)],
        _dest: Option<Ty>,
    ) -> Option<Option<StaticView>> {
        if !is_pointer_arithmetic_callee(leaf) {
            return None;
        }
        let preserve_location = self.native_pointer_cast(callee_ty, leaf);
        if !preserve_location
            && args.iter().any(|(_, v)| v.as_ref().is_some_and(StaticView::byte_view))
        {
            return Some(Some(StaticView::Unseeded));
        }
        if matches!(leaf, "addr" | "expose_provenance") {
            // The address as a number (`retype` into an integer): a promoted
            // constant's is not followed.
            let tracked: Vec<&StaticView> = args.iter().filter_map(|(_, v)| v.as_ref()).collect();
            let followed = !tracked.is_empty() && !tracked.iter().all(|v| v.promoted());
            return Some(followed.then_some(StaticView::Unseeded));
        }
        if is_byte_arithmetic_callee(leaf) {
            return Some(args.iter().any(|(_, v)| v.is_some()).then_some(StaticView::Unseeded));
        }
        // The pointer argument moves (or is re-typed); a count is a number.
        let Some((arg_ty, mut v)) = args
            .iter()
            .filter(|(t, _)| t.is_none_or(|t| pointee(t).is_some()))
            .find_map(|(t, v)| v.clone().map(|v| (*t, v)))
        else {
            return Some(None);
        };
        if !preserve_location && let StaticView::Seeded { const_offset, .. } = &mut v {
            *const_offset = None;
        }
        let moving = matches!(
            leaf,
            "add" | "sub" | "offset" | "wrapping_add" | "wrapping_sub" | "wrapping_offset"
        );
        if moving {
            let v = match arg_ty.and_then(pointee) {
                Some(p) => self.view_change(v, p),
                None => v,
            };
            return Some(self.arith(Some(&BinOp::Offset), v, None));
        }
        // No move: the destination re-types it.
        Some(Some(v))
    }

    fn is_inert_callee(&self, leaf: &str) -> bool {
        is_non_writing_callee(leaf) || is_formatting_callee(leaf)
    }

    fn through_memory(&self, v: StaticView) -> StaticView {
        // The carrier flow merges aggregate fields and aliased/reassigned
        // locals. Keep older view policy, but no new exact byte authority.
        self.through_call(v)
    }

    fn through_pointer_call(&self, v: StaticView) -> StaticView {
        match v {
            StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                const_offset,
                byte_view,
                ..
            } => StaticView::Seeded {
                whole,
                view,
                sort,
                at_base,
                holds_static_pointers,
                origin,
                direct: false,
                const_offset,
                byte_view,
            },
            other => other,
        }
    }

    fn through_call(&self, v: StaticView) -> StaticView {
        if v.byte_view() {
            return StaticView::Unseeded;
        }
        let mut v = self.through_pointer_call(v);
        if let StaticView::Seeded { const_offset, .. } = &mut v {
            *const_offset = None;
        }
        v
    }

    fn borrow_local(&self, v: Option<StaticView>) -> Option<StaticView> {
        v.filter(StaticView::byte_view).map(|_| StaticView::Unseeded)
    }
}

// ---------------------------------------------------------------------------
// Net 3: pointers made from literal addresses that name model objects.
// ---------------------------------------------------------------------------

/// Callees that make a pointer from the address their first argument holds.
fn is_address_to_pointer_callee(leaf: &str) -> bool {
    matches!(
        leaf,
        "without_provenance"
            | "without_provenance_mut"
            | "with_exposed_provenance"
            | "with_exposed_provenance_mut"
            | "from_exposed_addr"
            | "from_exposed_addr_mut"
            | "invalid"
            | "invalid_mut"
    )
}

/// The standard library's pointer methods that dereference no argument and
/// call no code of another crate, whatever the pointee (`<*const T>::offset`
/// on a harness type `T`). `map_addr` calls its closure with the address, so
/// it is not one.
fn is_pure_pointer_method(leaf: &str) -> bool {
    (is_pointer_arithmetic_callee(leaf) && leaf != "map_addr")
        || is_address_to_pointer_callee(leaf)
        || matches!(
            leaf,
            "is_null"
                | "addr_eq"
                | "addr"
                | "expose_provenance"
                | "precondition_check"
                | "is_aligned"
                | "is_aligned_to"
                | "align_offset"
        )
}

/// Comparisons: they dereference no pointer argument when the standard
/// library's own impl compares standard-library data (a `&T` impl calls
/// `T`'s).
fn is_comparison_method(leaf: &str) -> bool {
    matches!(leaf, "eq" | "ne" | "cmp" | "partial_cmp" | "lt" | "le" | "gt" | "ge")
}

/// Is `ty` data of the standard library alone: primitives, and references,
/// arrays, tuples and `core`/`alloc`/`std` types built from them? No closure,
/// function or trait object (a way into code of the harness's crate), and no
/// type of another crate (whose trait impls a generic standard-library
/// function may call).
fn is_standard_library_data(ty: Ty, depth: u32) -> bool {
    if depth > MAX_POINTER_HOLDER_DEPTH {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Str
            | RigidTy::Never,
        ) => true,
        TyKind::RigidTy(
            RigidTy::Ref(_, inner, _)
            | RigidTy::RawPtr(inner, _)
            | RigidTy::Array(inner, _)
            | RigidTy::Slice(inner),
        ) => is_standard_library_data(inner, depth + 1),
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().all(|t| is_standard_library_data(*t, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            matches!(def.krate().name.as_str(), "core" | "alloc" | "std")
                && args.0.iter().all(|a| match a {
                    rustc_public::ty::GenericArgKind::Type(t) => {
                        is_standard_library_data(*t, depth + 1)
                    }
                    _ => true,
                })
        }
        _ => false,
    }
}

/// Whether the callee of `func` is a function of the standard library
/// (`core`, `alloc`, `std`) or of Kani's library (its intrinsic models,
/// `kani::rustc_intrinsics::offset`), and whether it is a standard-library
/// function instantiated on standard-library data only (`Result<isize, TryFromIntError>::is_err`,
/// `<isize as TryFrom<usize>>::try_from`). A function of the second kind
/// makes no pointer from an integer it is handed to read through it: it
/// makes pointers only from pointer arguments (followed as pointers) or
/// through the address-to-pointer constructors, whose results the flow
/// follows, and it reaches no code of the harness's crate (`Into::into`
/// calls a harness type's `From`).
fn standard_library_callee(
    func: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> (bool, bool) {
    let Ok(ty) = func.ty(locals) else { return (false, false) };
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return (false, false) };
    let krate = match rustc_public::mir::mono::Instance::resolve(def, &args) {
        Ok(instance) => instance.def.krate(),
        Err(_) => def.krate(),
    };
    let std_data = matches!(krate.name.as_str(), "core" | "alloc" | "std")
        && args.0.iter().all(|a| match a {
            rustc_public::ty::GenericArgKind::Type(t) => is_standard_library_data(*t, 0),
            _ => true,
        });
    let std_crate = matches!(krate.name.as_str(), "core" | "alloc" | "std" | "kani");
    (std_crate, std_data)
}

/// Is `op` a literal (a constant with no provenance) whose value's high word
/// names a model object?
fn literal_names_model_object(op: &Operand) -> bool {
    model_object_literal_lane(op).is_some()
}

/// The object number a literal `op` (eight bytes, no provenance) names in its
/// high word, when that is a number a harness can allocate.
pub(in crate::codegen_ay::chc) fn model_object_literal_lane(op: &Operand) -> Option<u32> {
    let Operand::Constant(c) = op else { return None };
    let bytes = const_bytes(&c.const_)?;
    if bytes.has_relocations() || bytes.len() != 8 {
        return None;
    }
    let value = bytes.read_uint_at(0, 8)?;
    let high = (value >> 32) as u64;
    (high != 0 && high < MODEL_OBJECT_LANE_BOUND).then_some(high as u32)
}

/// What net 3 tracks: a pointer made from such a literal.
#[derive(Clone, Copy, PartialEq, Debug)]
struct ModelObjectLiteral;

impl Tracked for ModelObjectLiteral {
    fn join(&self, _other: &Self) -> Self {
        ModelObjectLiteral
    }
}

struct LiteralRules;

impl FlowRules for LiteralRules {
    type V = ModelObjectLiteral;

    fn constant(&self, op: &Operand, ty: Option<Ty>) -> Option<ModelObjectLiteral> {
        // The integer too: `let a = 0x2_0000_0000usize; a as *const u8` casts
        // a local, not the literal.
        (ty.is_some_and(|t| is_integer(t) || pointee(t).is_some())
            && literal_names_model_object(op))
        .then_some(ModelObjectLiteral)
    }

    fn cast(
        &self,
        kind: &CastKind,
        op: &Operand,
        from: Option<Ty>,
        to: Ty,
        v: Option<ModelObjectLiteral>,
    ) -> Option<ModelObjectLiteral> {
        let int_to_ptr =
            matches!(kind, CastKind::PointerWithExposedProvenance | CastKind::Transmute)
                && from.is_some_and(is_integer)
                && pointee(to).is_some();
        if int_to_ptr && literal_names_model_object(op) { Some(ModelObjectLiteral) } else { v }
    }

    fn retype(&self, v: ModelObjectLiteral, _holder: Option<Ty>) -> Option<ModelObjectLiteral> {
        Some(v)
    }

    fn reborrow(
        &self,
        v: ModelObjectLiteral,
        _pointee: Option<Ty>,
        _rest: &[ProjectionElem],
    ) -> Option<ModelObjectLiteral> {
        Some(v)
    }

    fn arith(
        &self,
        _op: Option<&BinOp>,
        v: ModelObjectLiteral,
        _ty: Option<Ty>,
    ) -> Option<ModelObjectLiteral> {
        Some(v)
    }

    fn load(&self, _v: &ModelObjectLiteral, _loaded: Option<Ty>) -> Option<ModelObjectLiteral> {
        None
    }

    fn pointer_call(
        &self,
        leaf: &str,
        _callee_ty: Option<Ty>,
        ops: &[Operand],
        args: &[(Option<Ty>, Option<ModelObjectLiteral>)],
        _dest: Option<Ty>,
    ) -> Option<Option<ModelObjectLiteral>> {
        if is_address_to_pointer_callee(leaf) {
            let literal = ops.first().is_some_and(literal_names_model_object);
            let carried = args.first().is_some_and(|(_, v)| v.is_some());
            return Some((literal || carried).then_some(ModelObjectLiteral));
        }
        if !is_pointer_arithmetic_callee(leaf) {
            return None;
        }
        Some(args.iter().find_map(|(_, v)| *v))
    }

    fn is_inert_callee(&self, leaf: &str) -> bool {
        is_non_writing_callee(leaf) || is_formatting_callee(leaf)
    }

    fn through_memory(&self, v: ModelObjectLiteral) -> ModelObjectLiteral {
        v
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Record, for block `bb` of the body being encoded, the reasons the two
    /// nets above assign it.
    pub(in crate::codegen_ay::chc) fn record_untyped_view_reasons(&self, bb: usize) {
        let reasons =
            self.untyped_view_scan.get_or_init(|| self.scan_untyped_views(self.body, false));
        if let Some(found) = reasons.get(&bb) {
            for reason in found {
                debug!(bb, reason, "CHC: memory accessed under an untracked view");
                self.record_sound_fallback_reason(reason);
            }
        }
    }

    /// The same for a body the call walker inlines (every block: the walk
    /// merges the callee's paths into the caller's rule). A body from another
    /// crate is skipped: the standard library moves element bytes of its own
    /// buffers (`ptr::copy` in `Vec`, `hashbrown`), which no local's
    /// provenance fact describes, and a call that rewrites a CALLER's local is
    /// caught at the call site (a byte writer, a punned argument, a reference
    /// to either).
    pub(in crate::codegen_ay::chc) fn record_untyped_view_reasons_for_inline_body(
        &self,
        body: &rustc_public::mir::Body,
        instance: Option<rustc_public::mir::mono::Instance>,
    ) {
        if let Some(instance) = instance
            && !rustc_public::rustc_internal::internal(self.tcx, instance.def.def_id()).is_local()
        {
            return;
        }
        let reasons = self.scan_untyped_views(body, true);
        let mut recorded: HashSet<&'static str> = HashSet::new();
        for reason in reasons.values().flatten() {
            if recorded.insert(reason) {
                debug!(reason, "CHC: an inlined body accesses memory under an untracked view");
                self.record_sound_fallback_reason(reason);
            }
        }
    }

    /// `callee`: the body is one the call walker inlines, whose arguments come
    /// from a caller this scan cannot see.
    fn scan_untyped_views(
        &self,
        body: &rustc_public::mir::Body,
        callee: bool,
    ) -> HashMap<usize, Vec<&'static str>> {
        let mut out: HashMap<usize, Vec<&'static str>> = HashMap::new();
        for bb in self.untyped_pointer_rewrite_blocks(body, callee) {
            out.entry(bb).or_default().push(POINTER_BYTES_REWRITTEN_UNTYPED);
        }
        for bb in self.static_unseeded_view_read_blocks(body, callee) {
            out.entry(bb).or_default().push(STATIC_MEMORY_READ_UNSEEDED_VIEW);
        }
        for bb in self.model_object_literal_blocks(body, callee) {
            out.entry(bb).or_default().push(CONST_POINTER_NAMES_MODEL_OBJECT);
        }
        out
    }

    /// The type of the static `def` as a MIR body sees it: regions erased (the
    /// declared type carries its own: `&'static mut i32`) and constants
    /// evaluated (`[T; SIZE]`); `None` for a nested static, which has no type
    /// of its own to ask for.
    fn static_type(&self, def: StaticDef) -> Option<Ty> {
        (!crate::kani_middle::is_anon_static(self.tcx, def.def_id()))
            .then(|| self.normalize_static_ty(def.ty()))
    }

    /// The callee leaf of a call; a callee of the panic or formatting
    /// machinery, whatever its leaf (`panic_nounwind_fmt::runtime`, the
    /// `fmt::rt` helpers), answers [`FORMATTING_LEAF`].
    fn leaf_of_call(
        &self,
        func: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> Option<String> {
        self.resolve_callee_path_with_locals(func, locals).map(|p| {
            if is_formatting_path(&p) {
                FORMATTING_LEAF.to_string()
            } else {
                callee_leaf(&p).to_string()
            }
        })
    }

    /// The callee leaf of every block's `Call` terminator.
    fn call_leaves(&self, body: &rustc_public::mir::Body) -> HashMap<usize, String> {
        let locals = body.locals();
        body.blocks
            .iter()
            .enumerate()
            .filter_map(|(bb, block)| match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => {
                    self.leaf_of_call(func, locals).map(|leaf| (bb, leaf))
                }
                _ => None,
            })
            .collect()
    }

    /// The blocks of net 1 (see the module documentation).
    fn untyped_pointer_rewrite_blocks(
        &self,
        body: &rustc_public::mir::Body,
        callee: bool,
    ) -> HashSet<usize> {
        let locals = body.locals();
        let leaves = self.call_leaves(body);
        let flow = Flow::solve(body, &PunRules, leaves.clone(), callee);
        if flow.saturated {
            debug!("CHC: the untyped-view flow did not converge; every block fails closed");
            return (0..body.blocks.len()).collect();
        }
        let punned = |c: &Contents<Pun>| c.val.is_some_and(|v| v.punned);
        let escapes = |c: &Contents<Pun>| c.val.is_some_and(|v| v.punned || v.erased);
        // An integer local (or an aggregate of non-pointers) that may hold an
        // exposed address.
        // An integer local (or a struct or tuple of non-pointers) DEFINED from
        // an exposed address: the int-to-pointer lanes follow such a local back
        // to the pointer its definition exposed.
        let defined_addresses: HashSet<usize> = body
            .blocks
            .iter()
            .flat_map(|b| b.statements.iter())
            .filter_map(|st| match &st.kind {
                StatementKind::Assign(lhs, rv)
                    if !lhs.projection.iter().any(|e| matches!(e, ProjectionElem::Deref))
                        && flow.rvalue(rv).val.is_some_and(|v| v.addr) =>
                {
                    Some(lhs.local)
                }
                _ => None,
            })
            .filter(|l| {
                locals.get(*l).is_some_and(|d| {
                    !may_hold_pointer(d.ty, 0)
                        && !matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                })
            })
            .collect();
        // ... whose address is taken mutably (`&mut addr`, `&raw mut addr`):
        // only then can a store through a pointer or a call rewrite it. The
        // standard library and Kani's instrumentation pass `&raw const` of
        // such temporaries to read them.
        let mutably_borrowed: HashSet<usize> = body
            .blocks
            .iter()
            .flat_map(|b| b.statements.iter())
            .filter_map(|st| match &st.kind {
                StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, rustc_public::mir::BorrowKind::Mut { .. }, place)
                    | Rvalue::AddressOf(rustc_public::mir::RawPtrKind::Mut, place),
                ) if !place.projection.iter().any(|e| matches!(e, ProjectionElem::Deref)) => {
                    Some(place.local)
                }
                _ => None,
            })
            .collect();
        let address_local =
            |l: usize| defined_addresses.contains(&l) && mutably_borrowed.contains(&l);
        // A local whose pointer-carrying bytes carry definition-based facts: a
        // pointer, or an aggregate holding one (an array of two or more
        // elements is read through memory).
        let pointer_tracked = |l: usize| {
            locals
                .get(l)
                .is_some_and(|d| !is_multi_element_array(d.ty) && may_hold_pointer(d.ty, 0))
        };
        // Cells with definition-based facts a byte write through a pointer to
        // `pointee` may change: a typed write of a type that cannot hold a
        // pointer only changes memory of that type (a pun of pointer-carrying
        // memory is `punned` and refused on its own), so the pointer locals
        // count only for a pointee that can hold one; an address integer always
        // counts. In a body the call walker inlines, memory outside the locals
        // includes the caller's locals.
        let names_definition_tracked = |cells: &BTreeSet<Cell>, pointee: Option<Ty>| {
            let carries = pointee.is_none_or(|t| may_hold_pointer(t, 0));
            cells.iter().any(|c| match c {
                Cell::Local(l) => carries && pointer_tracked(*l) || address_local(*l),
                Cell::Ext => callee && carries,
                Cell::Const => false,
            })
        };
        let names_address_local = |cells: &BTreeSet<Cell>| {
            cells.iter().any(|c| matches!(c, Cell::Local(l) if address_local(*l)))
        };

        let mut blocks = HashSet::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            let mut flag = |why: &str| {
                debug!(bb, why, "CHC: pointer-carrying bytes may be rewritten untyped");
                blocks.insert(bb);
            };
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rv) => {
                        if let Some((pointer, _, _)) = flow.last_deref(lhs) {
                            // A store through a punned pointer, or through an
                            // erased one that names bytes.
                            let stores_bytes =
                                lhs.ty(locals).ok().is_none_or(|t| !is_opaque_view(t));
                            if punned(&pointer)
                                || stores_bytes && pointer.val.is_some_and(|v| v.erased)
                            {
                                flag(
                                    "store through a pointer cast from a pointer-carrying pointee",
                                );
                            }
                            // A store into an address integer through a pointer.
                            let targets = flow.write_targets(lhs);
                            if names_address_local(&targets) {
                                debug!(?targets, "CHC: a store may reach an address integer");
                                flag(
                                    "an exposed address held in a local is rewritten through a pointer",
                                );
                            }
                            // A body the call walker inlines hands a pun to its
                            // caller through memory.
                            if callee && targets.contains(&Cell::Ext) && escapes(&flow.rvalue(rv)) {
                                flag("a punned pointer is stored where the caller can read it");
                            }
                        }
                        // A store into a field of a union that can hold a pointer.
                        let prefixes = place_prefix_types(lhs, locals);
                        let union_store =
                            lhs.projection.iter().zip(prefixes.iter()).any(|(elem, parent)| {
                                matches!(elem, ProjectionElem::Field(..))
                                    && parent.is_some_and(|t| is_union(t) && may_hold_pointer(t, 0))
                            });
                        if union_store {
                            flag("store into a field of a union that can hold a pointer");
                        }
                        // A punned pointer returned to the caller.
                        if lhs.local == 0 && escapes(&flow.rvalue(rv)) {
                            flag("a punned pointer is returned");
                        }
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                        let dst = flow.operand(&copy.dst);
                        let pointee = copy.dst.ty(locals).ok().and_then(pointee);
                        if punned(&dst) || names_definition_tracked(&dst.targets(), pointee) {
                            flag(
                                "a byte copy into pointer-carrying bytes with definition-based facts",
                            );
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        if flow.last_deref(place).is_some_and(|(p, _, _)| punned(&p)) {
                            flag("a discriminant write through a punned pointer");
                        }
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { args, .. } => {
                    let leaf = leaves.get(&bb).map(String::as_str).unwrap_or_default();
                    let contents: Vec<Contents<Pun>> =
                        args.iter().map(|a| flow.operand(a)).collect();
                    if !(is_pointer_arithmetic_callee(leaf)
                        || is_non_writing_callee(leaf)
                        || is_formatting_callee(leaf))
                    {
                        let (reach, all) = flow.reach_all(&contents);
                        if punned(&all) {
                            flag("a punned pointer reaches a call that may write through it");
                        }
                        // An erased pointer the callee may cast back and write
                        // through, naming a local with definition-based facts.
                        if args.iter().zip(&contents).any(|(a, c)| {
                            c.val.is_some_and(|v| v.erased)
                                && names_definition_tracked(
                                    &c.targets(),
                                    a.ty(locals).ok().and_then(pointee),
                                )
                        }) {
                            flag("an erased pointer to a pointer-carrying local reaches a call");
                        }
                        // A mutable pointer to an address integer: the callee
                        // may rewrite it (`mem::replace(&mut addr, ..)`).
                        if args.iter().zip(&contents).any(|(a, c)| {
                            let ty = a.ty(locals).ok();
                            if ty.is_some_and(is_mut_pointer) {
                                names_address_local(&c.pts)
                            } else if ty.is_some_and(|t| holds_mut_pointer(t, 0)) {
                                names_address_local(&flow.reach(c.pts.iter().copied()))
                            } else {
                                false
                            }
                        }) {
                            flag(
                                "an exposed address held in a local reaches a call that may write it",
                            );
                        }
                        let _ = &reach;
                    }
                    if is_byte_writer_callee(leaf) {
                        for idx in byte_writer_destinations(leaf, args.len()) {
                            let (Some(arg), Some(dst)) = (args.get(idx), contents.get(idx)) else {
                                continue;
                            };
                            let exempt_swap = matches!(leaf, "swap" | "typed_swap_nonoverlapping")
                                && args.len() >= 2
                                && args[..2].iter().all(|a| swaps_exchanged_exactly(body, a));
                            let pointee = arg.ty(locals).ok().and_then(pointee);
                            if punned(dst)
                                || !exempt_swap && names_definition_tracked(&dst.targets(), pointee)
                            {
                                flag(
                                    "a byte writer or swap over pointer-carrying bytes with definition-based facts",
                                );
                            }
                        }
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let held =
                        Contents { val: None, pts: BTreeSet::from([Cell::Local(place.local)]) };
                    if punned(&flow.reach_all(&[held]).1) {
                        flag("a value holding a punned pointer is dropped");
                    }
                }
                _ => {}
            }
        }
        blocks
    }

    /// The blocks of net 2 (see the module documentation).
    fn static_unseeded_view_read_blocks(
        &self,
        body: &rustc_public::mir::Body,
        callee: bool,
    ) -> HashSet<usize> {
        // Nothing to follow in a body that names no static and no constant
        // memory it may reinterpret.
        let mut mentions_static = false;
        let mut mentions_memory = false;
        let mut operands = Operands(Vec::new());
        operands.visit_body(body);
        for op in &operands.0 {
            mentions_static |= static_of_constant(op).is_some();
            mentions_memory |= memory_of_constant(op).is_some();
        }
        if !mentions_static && !mentions_memory {
            return HashSet::new();
        }
        let locals = body.locals();
        let leaves = self.call_leaves(body);
        let track_consts = mentions_memory && body_may_reinterpret(body, &leaves);
        if !mentions_static && !track_consts {
            return HashSet::new();
        }
        let rules = StaticRules { ctx: self, track_consts };
        let flow = Flow::solve(body, &rules, leaves.clone(), callee);
        if flow.saturated {
            debug!("CHC: the static-view flow did not converge; every block is a read");
            return (0..body.blocks.len()).collect();
        }
        let is_unseeded = |c: &Contents<StaticView>| matches!(c.val, Some(StaticView::Unseeded));
        // A read of `place`: every dereference in it reads through a pointer
        // (`skip_last`: the last one is the address a borrow or a store takes).
        let reads_unseeded = |place: &Place, skip_last: bool| {
            // The caller's exact direct shared-array read consumes its cached
            // typed window, not an unseeded memory view. Keep this exception at
            // the read: the pointer remains Unseeded for every cast, field,
            // arithmetic step, passed argument, or callee-body interpretation.
            if !callee
                && !skip_last
                && matches!(place.projection.as_slice(), [ProjectionElem::Deref])
                && self.direct_fixed_array_window_value(place.local).is_some()
            {
                return false;
            }
            let derefs = flow.derefs(place);
            let n = derefs.len();
            derefs.into_iter().enumerate().any(|(k, (pointer, pointee, rest))| {
                !(skip_last && k + 1 == n)
                    && pointer.val.is_some_and(|v| {
                        matches!(rules.walk(v, pointee, &rest), StaticView::Unseeded)
                    })
            })
        };
        let places_read = |places: &[Place]| places.iter().any(|p| reads_unseeded(p, false));

        let mut blocks = HashSet::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            let mut read = false;
            for (si, stmt) in block.statements.iter().enumerate() {
                let location = rustc_public::mir::visit::statement_location(body, &bb, si);
                match &stmt.kind {
                    StatementKind::Assign(lhs, rv) => {
                        match rv {
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                read |= reads_unseeded(place, true);
                            }
                            _ => {
                                let mut places = Places(Vec::new());
                                places.visit_rvalue(rv, location);
                                read |= places_read(&places.0);
                            }
                        }
                        read |= reads_unseeded(lhs, true);
                        // A body the call walker inlines hands a static's pointer
                        // to its caller, which this scan cannot follow.
                        if callee {
                            let targets = flow.write_targets(lhs);
                            if (targets.contains(&Cell::Ext) || targets.contains(&Cell::Local(0)))
                                && flow.rvalue(rv).val.is_some()
                            {
                                read = true;
                            }
                        }
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                        read |= is_unseeded(&flow.operand(&copy.src));
                        let mut places = Places(Vec::new());
                        places.visit_statement(stmt, location);
                        read |= places_read(&places.0);
                    }
                    _ => {}
                }
            }
            let location = rustc_public::mir::visit::terminator_location(body, &bb);
            match &block.terminator.kind {
                TerminatorKind::Call { args, destination, .. } => {
                    let mut places = Places(Vec::new());
                    for arg in args {
                        places.visit_operand(arg, location);
                    }
                    read |= places_read(&places.0);
                    read |= reads_unseeded(destination, true);
                    let leaf = leaves.get(&bb).map(String::as_str).unwrap_or_default();
                    let contents: Vec<Contents<StaticView>> =
                        args.iter().map(|a| flow.operand(a)).collect();
                    let (_, all) = flow.reach_all(&contents);
                    if is_unseeded(&all) && !is_formatting_callee(leaf) {
                        read |= is_reading_callee(leaf)
                            || !(is_pointer_arithmetic_callee(leaf) || is_non_writing_callee(leaf));
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let held =
                        Contents { val: None, pts: BTreeSet::from([Cell::Local(place.local)]) };
                    read |= is_unseeded(&flow.reach_all(&[held]).1);
                }
                _ => {
                    let mut places = Places(Vec::new());
                    places.visit_terminator(&block.terminator, location);
                    read |= places_read(&places.0);
                }
            }
            let _ = locals;
            if read {
                debug!(bb, "CHC: a static's memory is read under a view it is not seeded under");
                blocks.insert(bb);
            }
        }
        blocks
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The blocks of net 3 (see the module documentation): a dereference of a
    /// pointer made from a literal that names a model object, or a call that
    /// may dereference one.
    fn model_object_literal_blocks(
        &self,
        body: &rustc_public::mir::Body,
        callee: bool,
    ) -> HashSet<usize> {
        let mut operands = Operands(Vec::new());
        operands.visit_body(body);
        if !operands.0.iter().any(literal_names_model_object) {
            return HashSet::new();
        }
        let leaves = self.call_leaves(body);
        let rules = LiteralRules;
        let flow = Flow::solve(body, &rules, leaves.clone(), callee);
        if flow.saturated {
            return (0..body.blocks.len()).collect();
        }
        let locals = body.locals();
        // A dereference in `place` through a pointer made from such a literal.
        let derefs_literal = |place: &Place| {
            flow.derefs(place).into_iter().any(|(pointer, _, _)| pointer.val.is_some())
        };
        let mut blocks = HashSet::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            let mut hit = false;
            for (si, stmt) in block.statements.iter().enumerate() {
                let location = rustc_public::mir::visit::statement_location(body, &bb, si);
                match &stmt.kind {
                    StatementKind::Assign(lhs, rv) => {
                        // A reference made through such a pointer counts as a
                        // read: handed on (to the formatting machinery, say), it
                        // is read where this scan does not look.
                        let mut places = Places(Vec::new());
                        places.visit_rvalue(rv, location);
                        hit |= places.0.iter().any(|p| derefs_literal(p));
                        hit |= derefs_literal(lhs);
                        // Such a value stored where another body can load it (a
                        // static, memory outside the locals) or, from a body the
                        // call walker inlines, returned to its caller: this scan
                        // cannot follow it there.
                        let targets = flow.write_targets(lhs);
                        if (targets.contains(&Cell::Ext)
                            || (callee && targets.contains(&Cell::Local(0))))
                            && flow.rvalue(rv).val.is_some()
                        {
                            hit = true;
                        }
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                        hit |= flow.operand(&copy.src).val.is_some()
                            || flow.operand(&copy.dst).val.is_some();
                        let mut places = Places(Vec::new());
                        places.visit_statement(stmt, location);
                        hit |= places.0.iter().any(|p| derefs_literal(p));
                    }
                    _ => {
                        let mut places = Places(Vec::new());
                        places.visit_statement(stmt, location);
                        hit |= places.0.iter().any(|p| derefs_literal(p));
                    }
                }
            }
            let location = rustc_public::mir::visit::terminator_location(body, &bb);
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    let mut places = Places(Vec::new());
                    for arg in args {
                        places.visit_operand(arg, location);
                    }
                    hit |= places.0.iter().any(|p| derefs_literal(p));
                    hit |= derefs_literal(destination);
                    let leaf = leaves.get(&bb).map(String::as_str).unwrap_or_default();
                    // Callee names are matched only on the standard library's
                    // own functions: a harness's `eq`, `add` or `from` may read
                    // through what it is handed.
                    let (std_crate, std_data) = standard_library_callee(func, &locals);
                    // The formatting machinery prints and reads through no
                    // argument: the panic message of a precondition check
                    // carries the count it rejects (`ptr::offset` in Kani's
                    // model, `ptr-offset-overflow-bytes/main.rs`).
                    let reads_no_argument = (std_crate
                        && (is_pure_pointer_method(leaf) || is_formatting_callee(leaf)))
                        || (std_data && is_comparison_method(leaf));
                    if !reads_no_argument {
                        for arg in args {
                            let contents = flow.operand(arg);
                            let direct = contents.val.is_some();
                            if !direct && flow.reach_all(&[contents]).1.val.is_none() {
                                continue;
                            }
                            // The literal as a number (a value whose type holds no
                            // pointer, an `Option<u64>`: whatever cells the flow
                            // joined to it), or an untracked reference to one,
                            // handed to the standard library's own code.
                            let integer = arg.ty(&locals).ok().is_some_and(|t| {
                                !may_hold_pointer(t, 0)
                                    || (!direct
                                        && pointee(t).is_some_and(|h| !may_hold_pointer(h, 0)))
                            });
                            if !(integer && std_data) {
                                hit = true;
                            }
                        }
                    }
                }
                _ => {
                    let mut places = Places(Vec::new());
                    places.visit_terminator(&block.terminator, location);
                    hit |= places.0.iter().any(|p| derefs_literal(p));
                }
            }
            if hit {
                debug!(
                    bb,
                    "CHC: a pointer made from a literal naming a model object is dereferenced"
                );
                blocks.insert(bb);
            }
        }
        blocks
    }
}

/// Every operand of a body.
struct Operands(Vec<Operand>);

impl MirVisitor for Operands {
    fn visit_operand(&mut self, operand: &Operand, _location: Location) {
        self.0.push(operand.clone());
    }
}
