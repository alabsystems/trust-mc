// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Stack allocation addresses: identity by object id, order and integer value by a
//! nondeterministic address region; wrapping steps in Kani's 48-bit offset range.
//!
//! # The model
//!
//! A pointer into a stack local is the split pointer `concat(obj_id, offset)`
//! (`get_or_create_local_address`). That term is the pointer's IDENTITY: memory
//! is indexed by it, `obj_valid` / `obj_size` by its object lane, and the
//! same-allocation checks of `offset_from` compare object lanes. It is NOT the
//! address a program observes. `obj_id` is handed out in declaration order, so
//! reading the term as an address proved `assert!(pa < pb)` for two distinct
//! locals (tools/soundness-duals/ptr_cmp_distinct_allocations_dual.rs), where Rust
//! leaves the order unspecified and rustc changes it with the optimization level.
//!
//! Addresses are Kani's layout: every object has its own 2^48-byte REGION, and
//! the address of a byte is `region << 48 | offset48`. The identity term reads as
//! an address through its ADDRESS VIEW: `concat(h16, field16, offset32)` (`h16`
//! the high part of a 48-bit offset) is `concat(region, h16, offset32)`, with the
//! object field replaced by the object's region ([`ChcCtx::ptr_to_int_value`],
//! inverted by [`ChcCtx::int_to_ptr_value`]).
//!
//! An untracked object's region is its id. An address-taken local whose body
//! observes addresses gets a read-only state variable, its BASE, constrained at
//! entry to `region << 48`: the region free (so the order of two allocations
//! stays unspecified), non-zero, not a tracked object id, and distinct from every
//! other tracked base's region ([`ChcCtx::stack_base_entry_constraints`]). Every
//! object's base is thereby 2^48-aligned, as in Kani's layout, where a local's
//! address is its object number over a zero offset (Kani proves `(&x as *const T
//! as usize) % 4096 == 0`). The region map swaps each tracked id with its base's
//! region and fixes every other value, so it is an involution, and the
//! integer/pointer round trip is exact. The observed address of
//! `concat(obj_id, offset)` is `base(obj_id) + offset`.
//! Observations are:
//!
//! * relational comparison (`<`, `<=`, `>`, `>=`, `cmp`) of two raw pointers:
//!   exact on the offsets when both pointers are in one allocation, the order of
//!   the bases otherwise ([`ChcCtx::ptr_order_operands`]);
//! * a pointer-to-integer cast or transmute ([`ChcCtx::ptr_to_int_value`]).
//!
//! Not observations: the casts rustc inserts for its own null and alignment
//! checks on a raw dereference (`-C debug-assertions`, on in both drivers). A
//! stack object's identity term is non-null, so the null check is exact on it,
//! and `concat(obj_id, offset) & (align - 1)` equals `(base + offset) & (align -
//! 1)` for every alignment, since every base is 2^48-aligned. An alignment check
//! is therefore never an observation ([`ChcCtx::rustc_pointer_check_casts`]):
//! reading a `#[repr(C)] struct { a: u32, b: u32 }` at offset 0 through a
//! `*const u64` is aligned, as Kani reports (`p1_ptr_cast.rs` `pad_cast_safe`,
//! `sgn_cast_safe`), although Rust gives the struct only 4-byte alignment.
//! Counting every check cast tracked
//! bases in any body with a raw deref and cost solver time for nothing
//! (kani/Pointers_OtherTypes: 26 s parity -> 49 s unknown).
//!
//! Equality stays on identity (Kani's `==` on pointers compares object and
//! offset). Pointer arithmetic, `offset_from` and every memory operation stay on
//! identity, so they remain exact within an allocation.
//!
//! # Wrapping steps and far pointers
//!
//! A wrapping step (`wrapping_*`, `arith_offset`, `with_addr`, `map_addr`) keeps
//! the pointer's object, as both Rust (provenance) and Kani (object bits) do, and
//! moves its offset `T` from the object's base by the count, mod 2^64. Kani's
//! object range is `[0, 2^48)`: an offset there is the same pointer, the same
//! address and the same equality in every mode Kani uses. An offset outside it
//! makes the pointer FAR, marked by the [`FAR_BIT`] of its object field over the
//! low 48 bits of `T` ([`ChcCtx::step_wrapping_address`]). Kani then answers each
//! observation in one of three ways depending on how CBMC simplified it (measured
//! on corpus-rev Kani, 2026-10-02: a symbolic count wraps the offset at 48 bits
//! for `addr()`, `as usize`, `==` and `<`; a literal count keeps 64 bits for `as
//! usize`, `==` and `<` and 48 for `addr()`; a dereference always checks the
//! 64-bit offset against the object's size). So a far pointer's dereference is
//! out of bounds (exact), and its address, its order, its `offset_from` and an
//! equality that its low 48 bits would decide are FAIL-CLOSED observations
//! ([`ChcCtx::record_far_observation`]): the path on which one is far ends in a
//! property that is never certified, and every other rule of the block is cut
//! to the paths where it is not, so no proof and no certified counterexample
//! rests on a mode Kani might not take.
//!
//! The first model left a base anywhere disjoint from the other bases and read
//! an untracked object's identity term as its address, which put objects 2^32
//! apart and let a base sit next to another object: `heap - 1 == &x as usize`,
//! `heap_a + 2^32 == heap_b`, two adjacent locals and a local at `0x1000` all
//! certified counterexamples Kani refutes (fourth review of
//! fix/chc-false-certificates, 2026-09-28).

use crate::codegen_ay::chc::codegen_ctx::{Havoc, sound_havoc};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::visit::{
    Location, MirVisitor, PlaceContext, statement_location, terminator_location,
};
use rustc_public::mir::{
    AggregateKind, AssertMessage, BinOp, CastKind, Local, Operand, ProjectionElem, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::codegen_ctx::globals::chc_fresh_name;
use crate::codegen_ay::chc::codegen_expr_heap::obj_size_in;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};

/// Most address-taken locals one body tracks. Disjointness is pairwise, so the
/// entry constraint grows quadratically; untracked locals fall back as above.
pub(in crate::codegen_ay::chc) const MAX_TRACKED_STACK_BASES: usize = 16;

/// Callee path fragments that observe a raw pointer's address when a raw pointer
/// (or a reference to one) is an argument.
const ADDRESS_OBSERVING_CALLEES: &[&str] = &[
    "PartialOrd",
    "::cmp",
    "::partial_cmp",
    "::lt",
    "::le",
    "::gt",
    "::ge",
    "::min",
    "::max",
    "::clamp",
    "::addr",
    "expose_provenance",
];

/// Callee path fragments that rebuild a pointer from an address while keeping
/// the receiver's provenance: each pointer they receive has its address
/// observed on its own. `with_addr(self, a)` is `self.wrapping_byte_offset(a -
/// self.addr())`, and without a base for `self` the difference of two identity
/// terms moved `self` exactly onto another object's identity, so a deref out of
/// `self`'s object stayed in bounds of the other (third review of
/// fix/chc-false-certificates, 2026-09-27: `ad_with_addr_other_obj_bug`). A
/// lone `addr()` needs no base: no tracked base may fall in an untracked
/// object's identity slot instead (`untracked_address_disjointness`),
/// and counting the `addr()` of the library's own precondition checks would
/// give bases to bodies that never compare an address.
const ADDRESS_REBASING_CALLEES: &[&str] = &["::with_addr", "::map_addr"];

/// Whether `ty` holds a raw pointer or a reference, directly or in an array, a
/// tuple or a struct field. A field type Rule A refuses (`mono_ty::field_ty`)
/// counts as holding one: the answer adds an address observation.
fn ty_contains_pointer(ty: Ty, depth: u32) -> bool {
    if depth > 8 {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)) => true,
        TyKind::RigidTy(RigidTy::Array(inner, _)) => ty_contains_pointer(inner, depth + 1),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field| ty_contains_pointer(*field, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants_iter().any(|variant| {
            variant.fields().iter().any(|field| {
                mono_ty::field_ty(field, &args).is_none_or(|ty| ty_contains_pointer(ty, depth + 1))
            })
        }),
        _ => false,
    }
}

/// Whether `ty` holds an integer, directly or in an array, a tuple or a struct
/// field (a refused field type counts, as above).
fn ty_contains_integer(ty: Ty, depth: u32) -> bool {
    if depth > 8 {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)) => true,
        TyKind::RigidTy(RigidTy::Array(inner, _)) => ty_contains_integer(inner, depth + 1),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field| ty_contains_integer(*field, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants_iter().any(|variant| {
            variant.fields().iter().any(|field| {
                mono_ty::field_ty(field, &args).is_none_or(|ty| ty_contains_integer(ty, depth + 1))
            })
        }),
        _ => false,
    }
}

/// One tracked stack local and its base-address state variable.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay::chc) struct StackBase {
    pub(in crate::codegen_ay::chc) local: usize,
    pub(in crate::codegen_ay::chc) name: Arc<str>,
    pub(in crate::codegen_ay::chc) size: u64,
    pub(in crate::codegen_ay::chc) align: u64,
    /// Assigned when the entry rule allocates the local.
    pub(in crate::codegen_ay::chc) obj_id: Option<u32>,
}

impl StackBase {
    fn var(&self) -> Expr {
        Expr::var(&*self.name, Sort::bitvec(POINTER_WIDTH))
    }

    /// The base's address region: its top 16 bits.
    fn region(&self) -> Expr {
        self.var().extract(63, REGION_SHIFT)
    }

    /// The base's offset within its region: zero, since the entry constraint
    /// makes every base 2^48-aligned (its low 48 bits are zero).
    fn in_region_offset(&self) -> Expr {
        Expr::bitvec_const(0u128, REGION_SHIFT)
    }
}

/// An address is `region << REGION_SHIFT | offset`: Kani's 16 object bits over
/// 48 offset bits.
const REGION_SHIFT: u32 = 48;

/// Object ids that have an address region of their own (the 16-bit object
/// field of an identity term).
pub(in crate::codegen_ay::chc) const REGION_COUNT: u32 = 1 << 16;

/// Allocation ids stay below this (`ChcHeapState::next_alloc_id`), so a
/// constant lane at or above it — an object field in the top half, or any
/// high offset bits — names no object, and an access through it is outside
/// every object (`heap_access_checks`).
pub(in crate::codegen_ay::chc) const OBJECT_ID_LIMIT: u32 = 1 << 15;

/// The FAR bit of an identity's object field, bit 15, which no allocation id
/// reaches ([`OBJECT_ID_LIMIT`]): the pointer's offset from its object's base
/// (Rust's offset, and the one Kani's bounds checks use) is outside `[0,
/// 2^48)`, Kani's object range. The field's low 15 bits keep the object and
/// the identity's 48 offset bits the offset's low 48 bits
/// ([`ChcCtx::step_wrapping_address`]). A far pointer's lane is no object's, so
/// every dereference of it is outside its object, as in Kani.
pub(in crate::codegen_ay::chc) const FAR_BIT: u32 = 1 << 15;

fn bool_const_value(e: &Expr) -> Option<bool> {
    match e.value() {
        ExprValue::BoolConst(b) => Some(*b),
        _ => None,
    }
}

fn is_thin_ptr_sort(e: &Expr) -> bool {
    e.sort().bitvec_width() == Some(64) && POINTER_WIDTH == 64
}

/// The data word of a pointer term: the term itself for a thin pointer, the
/// address half of a wide one (`*const [T]`, `*const str`, a widened thin
/// slice pointer), whose metadata a wrapping step keeps.
fn pointer_data_word(value: &Expr) -> Option<Expr> {
    if is_thin_ptr_sort(value) {
        return Some(value.clone());
    }
    let data = crate::codegen_ay::ptr_repr::PtrRepr::classify(value)?.data().clone().into_expr();
    is_thin_ptr_sort(&data).then_some(data)
}

fn ty_is_raw_ptr(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
}

fn ty_is_raw_ptr_or_ref_to_one(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty_is_raw_ptr_or_ref_to_one(inner),
        _ => false,
    }
}

/// A raw pointer, a reference, or one of the pointer wrappers the CHC lane
/// models as the address itself (`NonNull`, `Unique`: `translate_ty` gives
/// them `ptr_sort`). A transmute between one of these and an integer is the
/// integer-to-pointer rule's business either way (`cast_exposes_address`,
/// `transmute_makes_pointer_from_integer`): in Kani's address layout an
/// integer is not the identity term, so `transmute::<usize, NonNull<u16>>(a +
/// 4)` of a `Box<[u16; 2]>`'s address, passed through as bits, named no object
/// and read past the box clean (`symbolic_lane_oob_dual.rs::
/// bug_transmute_nonnull_oob`, found merging main dbfe268fc into
/// fix/chc-lost-writes).
fn ty_is_pointer_like(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)) => true,
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            use rustc_public::CrateDef;
            def.kind() == rustc_public::ty::AdtKind::Struct
                && (def.trimmed_name() == "NonNull"
                    || def.trimmed_name() == "Unique"
                    || rustc_middle::ty::tls::with(|tcx| {
                        crate::codegen_ay::shared::native_box_raw::native_box_raw_pointer_field(
                            tcx, def, &args,
                        )
                        .is_some()
                    }))
        }
        _ => false,
    }
}

/// A type whose value is plain bits with no provenance: an integer, or a
/// float. A transmute between a pointer and one of these is the
/// integer-to-pointer rule's business (`cast_exposes_address`,
/// `transmute_makes_pointer_from_integer`), whatever the bits are spelled as:
/// Rust gives a float no provenance either, so `transmute::<f64, *const T>`
/// of a pointer's bits is exactly `transmute::<u64, *const T>` of them. The
/// CHC lane models an `f64` as its 64-bit IEEE pattern, the same sort as a
/// pointer, so without this a pointer laundered through a float's bits came
/// back with its object, and `bug_static_f64_transmute_nostore`
/// (tools/soundness-duals/bit_launder_dual.rs) was PROVED once the
/// constant-pointer rule seeded the static it read.
fn ty_is_provenance_free_bits(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)))
}

/// Every local one statement or terminator mentions, read or written.
struct MentionedLocals(Vec<usize>);

impl MirVisitor for MentionedLocals {
    fn visit_local(&mut self, local: &Local, _ptx: PlaceContext, _location: Location) {
        self.0.push(*local);
    }
}

fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

/// What a pointer points into, as far as a def-use walk can tell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(in crate::codegen_ay::chc) enum PtrRoot {
    /// A place of this local (`&x`, `&x.f`, `&x[i]`, `&raw const x`), possibly
    /// moved by allocation-preserving pointer arithmetic or slice indexing.
    StackLocal(usize),
    /// A pointer argument never reassigned in the body, or a constant: it
    /// cannot point into a local of this body.
    Foreign,
    /// Anything else (loads, joins, other calls).
    Unknown,
}

/// Where a local receives a whole value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefSite {
    Stmt(usize, usize),
    Call(usize),
}

/// A cast rustc inserted for its own null or alignment check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct PointerCheckCast {
    /// Alignment the check requires; `None` for a null check.
    pub(in crate::codegen_ay::chc) required_align: Option<u64>,
    /// What the checked pointer points into.
    pub(in crate::codegen_ay::chc) root: PtrRoot,
    /// Size of the checked pointee, when sized.
    pub(in crate::codegen_ay::chc) pointee_size: Option<u64>,
}

impl PointerCheckCast {
    /// The identity term answers this check exactly, so it observes nothing.
    ///
    /// A null check always: a stack identity term is non-null. An alignment
    /// check when the required alignment divides the alignment of the object
    /// the pointer points into, since the base is aligned to that object. A
    /// pointer into no local of this body has no base to read. For an unknown
    /// root, every laid-out local at least as large as the pointee must be
    /// aligned enough; a pointer into a smaller local makes the dereference
    /// out of bounds, which the memory-safety check reports on its own.
    fn decides_nothing_on_identity(&self, layouts: &HashMap<usize, (u64, u64)>) -> bool {
        // Every base is 2^48-aligned (Kani's layout), so the identity's offset
        // decides every alignment check.
        if self.required_align.is_some_and(|required| required < (1u64 << REGION_SHIFT)) {
            return true;
        }
        let Some(required) = self.required_align else { return true };
        match self.root {
            PtrRoot::Foreign => true,
            PtrRoot::StackLocal(local) => {
                layouts.get(&local).is_none_or(|&(_, align)| required <= align)
            }
            PtrRoot::Unknown => layouts
                .values()
                .filter(|&&(size, _)| self.pointee_size.is_none_or(|p| size >= p))
                .all(|&(_, align)| required <= align),
        }
    }
}

/// The address-taken locals some observation reaches.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Observed {
    Locals(HashSet<usize>),
    All,
}

/// What the roots of the pointers one comparison or call observes require.
/// Two pointers into one local compare exactly on offsets and a pointer into no
/// local of the body has no base, so tracking helps only for two distinct
/// locals; an unknown root may be any local.
fn observed_by_roots(roots: &[PtrRoot]) -> Option<Observed> {
    if roots.contains(&PtrRoot::Unknown) {
        return Some(Observed::All);
    }
    let locals: HashSet<usize> = roots
        .iter()
        .filter_map(|r| match r {
            PtrRoot::StackLocal(l) => Some(*l),
            _ => None,
        })
        .collect();
    (locals.len() >= 2).then_some(Observed::Locals(locals))
}

fn ty_points_to_array_or_slice(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
            matches!(inner.kind(), TyKind::RigidTy(RigidTy::Array(..) | RigidTy::Slice(_)))
        }
        _ => false,
    }
}

fn ty_points_to_str(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
            matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str))
        }
        _ => false,
    }
}

/// `op` observes the order of its operands.
pub(in crate::codegen_ay::chc) fn is_relational_ptr_op(op: BinOp) -> bool {
    matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Cmp)
}

/// A cast from `src` to `target` reads a pointer's address as an integer.
pub(in crate::codegen_ay::chc) fn cast_exposes_address(
    kind: &CastKind,
    src: Ty,
    target: Ty,
) -> bool {
    match kind {
        CastKind::PointerExposeAddress => true,
        CastKind::Transmute => ty_is_pointer_like(src) && ty_is_provenance_free_bits(target),
        _ => false,
    }
}

/// Is a cast of kind `kind` from `src` to `target` a transmute of an integer
/// (or a float's bits: `ty_is_provenance_free_bits`) into a pointer: the
/// integer-to-pointer lane of `CastKind::PointerWithExposedProvenance`,
/// spelled as a transmute (`transmute::<usize, *const T>(a)`)?
pub(in crate::codegen_ay::chc) fn transmute_makes_pointer_from_integer(
    kind: &CastKind,
    src: Ty,
    target: Ty,
) -> bool {
    matches!(kind, CastKind::Transmute)
        && ty_is_provenance_free_bits(src)
        && ty_is_pointer_like(target)
}

/// Can a value of `ty` hold a pointer (a reference, a raw or function pointer,
/// or an ADT or tuple holding one)? Past the depth bound the answer is `true`.
fn ty_holds_pointer(ty: Ty, depth: u32) -> bool {
    if depth > 4 {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..) | RigidTy::FnPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().any(|t| ty_holds_pointer(*t, depth + 1)),
        TyKind::RigidTy(RigidTy::Array(elem, _)) => ty_holds_pointer(elem, depth + 1),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().into_iter().any(|v| {
            // A field whose type does not resolve may hold one.
            v.fields().into_iter().any(|f| {
                crate::codegen_ay::shared::mono_ty::field_ty(&f, &args)
                    .is_none_or(|t| ty_holds_pointer(t, depth + 1))
            })
        }),
        _ => false,
    }
}

/// Is a cast of kind `kind` from `src` to `target` a transmute of plain bits
/// (an integer or a float) or a raw pointer into a NICHE-encoded enum whose payload holds a pointer
/// (`Option<&T>`, `Option<NonNull<T>>`, `Option<Box<T>>`)? Such a value is
/// `None` exactly when the bits are zero. The transmute's sort coercion does
/// not decode the niche: `transmute::<usize, Option<&u16>>(a + 2)` of a live
/// address unwrapped to `None`, and the panic was certified Genuine on main
/// and on fix/chc-lost-writes (review of fix/chc-lost-writes, lostwrite round
/// 1, finding 4's neighbours).
pub(in crate::codegen_ay::chc) fn transmute_makes_niche_pointer_enum(
    kind: &CastKind,
    src: Ty,
    target: Ty,
) -> bool {
    use rustc_public::abi::{TagEncoding, VariantsShape};
    matches!(kind, CastKind::Transmute)
        && (ty_is_provenance_free_bits(src) || ty_is_raw_ptr(src))
        && matches!(
            target.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == rustc_public::ty::AdtKind::Enum
        )
        && target.layout().ok().is_some_and(|l| {
            matches!(
                l.shape().variants,
                VariantsShape::Multiple { tag_encoding: TagEncoding::Niche { .. }, .. }
            )
        })
        && ty_holds_pointer(target, 0)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Declare a base-address state variable for each address-taken local an
    /// address observation of the body reaches. See the module docs.
    pub(in crate::codegen_ay::chc) fn collect_stack_base_state_vars(&mut self) {
        if self.int_lift || POINTER_WIDTH != 64 {
            return;
        }
        let arg_count = self.body.arg_locals().len();
        let mut seen = HashSet::new();
        let mut candidates = Vec::new();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
                let (Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) = rvalue else {
                    continue;
                };
                if place.local == 0
                    || place.local <= arg_count
                    || place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                {
                    continue;
                }
                if seen.insert(place.local) {
                    candidates.push(place.local);
                }
            }
        }
        if candidates.is_empty() {
            return;
        }
        let mut laid_out = Vec::new();
        for local in candidates {
            let ty = self.body.locals()[local].ty;
            let Some(size) = self.get_type_size(ty).and_then(|s| u64::try_from(s).ok()) else {
                continue;
            };
            let Some(align) = self
                .resolve_body_ty(ty)
                .layout()
                .ok()
                .and_then(|l| u64::try_from(l.shape().abi_align).ok())
            else {
                continue;
            };
            if !align.is_power_of_two() || size > u64::MAX - align {
                continue;
            }
            laid_out.push((local, size, align));
        }
        if laid_out.is_empty() {
            return;
        }
        let layouts: HashMap<usize, (u64, u64)> =
            laid_out.iter().map(|&(local, size, align)| (local, (size, align))).collect();
        let observed = match self.body_address_observations(&layouts) {
            None => return,
            Some(Observed::All) => None,
            Some(Observed::Locals(locals)) => Some(locals),
        };
        let fn_tag: String =
            self.fn_name.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect();
        for (local, size, align) in laid_out {
            if observed.as_ref().is_some_and(|locals| !locals.contains(&local)) {
                continue;
            }
            if self.heap_state.stack_bases.len() >= MAX_TRACKED_STACK_BASES {
                debug!(local, "CHC stack base: tracking cap reached");
                break;
            }
            let name: Arc<str> = format!("_{fn_tag}__stack_base_{local}").into();
            let out_name = format!("{name}__out");
            self.push_state_var_pair(&name, &out_name, Sort::bitvec(POINTER_WIDTH));
            debug!(local, size, align, %name, "CHC stack base: tracked address-taken local");
            self.heap_state.stack_bases.push(StackBase { local, name, size, align, obj_id: None });
        }
    }

    /// The address-taken locals whose addresses the body observes: through a
    /// relational comparison of raw pointers, a pointer-to-integer cast, or a
    /// raw pointer passed to a callee that compares or exposes it. `None` when
    /// no observation needs a base. `layouts` maps every laid-out
    /// address-taken local to its `(size, align)`.
    fn body_address_observations(&self, layouts: &HashMap<usize, (u64, u64)>) -> Option<Observed> {
        let locals = self.body.locals();
        let defs = self.local_def_sites();
        let check_casts = self.pointer_check_casts(&defs);
        let mut observed: HashSet<usize> = HashSet::new();
        let mut merge = |found: Option<Observed>, what: &dyn std::fmt::Debug| -> bool {
            match found {
                None => false,
                Some(Observed::All) => {
                    debug!(fn_name = %self.fn_name, ?what, "CHC stack base: observation of an unknown pointer (all locals)");
                    true
                }
                Some(Observed::Locals(found)) => {
                    debug!(fn_name = %self.fn_name, ?what, ?found, "CHC stack base: observation");
                    observed.extend(found);
                    false
                }
            }
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
                match rvalue {
                    Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)
                        if is_relational_ptr_op(*op)
                            && lhs.ty(locals).ok().is_some_and(ty_is_raw_ptr) =>
                    {
                        let roots = [
                            self.operand_pointer_root(&defs, lhs),
                            self.operand_pointer_root(&defs, rhs),
                        ];
                        if merge(observed_by_roots(&roots), &(op, roots)) {
                            return Some(Observed::All);
                        }
                    }
                    Rvalue::Cast(kind, operand, target) => {
                        let Ok(src) = operand.ty(locals) else { continue };
                        // A transmute of an aggregate holding pointers into one
                        // holding integers (`[*const u8; 2]` into `[usize; 2]`)
                        // reads those pointers' addresses as a scalar transmute
                        // does (third review: `a2_arr_transmute_one_observed_safe`,
                        // `tr_ptr_to_usize_arr_safe`).
                        let aggregate_exposes = matches!(kind, CastKind::Transmute)
                            && !ty_is_pointer_like(src)
                            && ty_contains_pointer(src, 0)
                            && ty_contains_integer(*target, 0);
                        if !cast_exposes_address(kind, src, *target) && !aggregate_exposes {
                            continue;
                        }
                        if dest.projection.is_empty()
                            && let Some(check) = check_casts.get(&dest.local)
                            && check.decides_nothing_on_identity(layouts)
                        {
                            continue;
                        }
                        let root = self.operand_pointer_root(&defs, operand);
                        let found = match root {
                            PtrRoot::StackLocal(l) => Some(Observed::Locals(HashSet::from([l]))),
                            PtrRoot::Foreign => None,
                            PtrRoot::Unknown => Some(Observed::All),
                        };
                        if merge(found, &(kind, root)) {
                            return Some(Observed::All);
                        }
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
                && args.iter().any(|a| a.ty(locals).ok().is_some_and(ty_is_raw_ptr_or_ref_to_one))
                && let Some(path) = self.resolve_callee_path(func)
            {
                let roots: Vec<PtrRoot> = args
                    .iter()
                    .filter(|a| a.ty(locals).ok().is_some_and(ty_is_raw_ptr_or_ref_to_one))
                    .map(|a| self.operand_pointer_root(&defs, a))
                    .collect();
                if ADDRESS_REBASING_CALLEES.iter().any(|m| path.contains(m)) {
                    // `p.with_addr(p.addr() + k)` is `p` moved by `k` bytes
                    // (`address_is_pointer_addr_plus`): no base needed.
                    if let [pointer, address, ..] = args.as_slice()
                        && self.address_is_pointer_addr_plus(address, pointer).is_some()
                    {
                        continue;
                    }
                    // Each pointer's address is read on its own.
                    for root in &roots {
                        let found = match root {
                            PtrRoot::StackLocal(l) => Some(Observed::Locals(HashSet::from([*l]))),
                            PtrRoot::Foreign => None,
                            PtrRoot::Unknown => Some(Observed::All),
                        };
                        if merge(found, &(&path, root)) {
                            return Some(Observed::All);
                        }
                    }
                } else if ADDRESS_OBSERVING_CALLEES.iter().any(|m| path.contains(m))
                    && merge(observed_by_roots(&roots), &(&path, &roots))
                {
                    return Some(Observed::All);
                }
            }
        }
        (!observed.is_empty()).then_some(Observed::Locals(observed))
    }

    /// Every whole-value definition of every local: assignments to the bare
    /// local and call destinations.
    fn local_def_sites(&self) -> HashMap<usize, Vec<DefSite>> {
        let mut defs: HashMap<usize, Vec<DefSite>> = HashMap::new();
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                if let StatementKind::Assign(place, _) = &stmt.kind
                    && place.projection.is_empty()
                {
                    defs.entry(place.local).or_default().push(DefSite::Stmt(bb, si));
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.projection.is_empty()
            {
                defs.entry(destination.local).or_default().push(DefSite::Call(bb));
            }
        }
        defs
    }

    /// Pointer-to-integer casts rustc inserted for its own null and alignment
    /// checks on a raw dereference, keyed by destination local.
    ///
    /// Shape (nightly MIR at `-C debug-assertions`):
    /// `_3 = copy _2 as usize (Transmute); _5 = BitAnd(copy _3, _4);
    /// _6 = Eq(copy _5, 0); assert(copy _6, MisalignedPointerDereference {
    /// required, found: copy _3 })`, and for null `_10 = Eq(copy _8, 0);
    /// _11 = BitAnd(_10, _9); _12 = Not(_11); assert(copy _12,
    /// NullPointerDereference)`. A cast qualifies only when its single
    /// definition is reached backwards from such an assert through
    /// single-definition `BinaryOp` / `UnaryOp` / `Use` statements, and every
    /// other statement or terminator mentioning its destination is part of a
    /// check chain or one of those asserts. A cast the program also uses
    /// elsewhere is an observation.
    pub(in crate::codegen_ay::chc) fn rustc_pointer_check_casts(
        &self,
    ) -> HashMap<usize, PointerCheckCast> {
        self.pointer_check_casts(&self.local_def_sites())
    }

    fn pointer_check_casts(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
    ) -> HashMap<usize, PointerCheckCast> {
        let body = self.body;
        let locals = body.locals();
        let mut chain_sites: HashSet<(usize, usize)> = HashSet::new();
        let mut check_blocks: HashSet<usize> = HashSet::new();
        let mut casts: HashMap<usize, PointerCheckCast> = HashMap::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Assert { cond, msg, .. } = &block.terminator.kind else {
                continue;
            };
            let (required, found) = match msg {
                AssertMessage::NullPointerDereference => (None, None),
                #[cfg(trust_toolchain)]
                AssertMessage::NullReferenceConstructed => (None, None),
                AssertMessage::MisalignedPointerDereference { required, found } => {
                    let align = match required {
                        Operand::Constant(c) => c.const_.eval_target_usize().ok(),
                        _ => None,
                    };
                    // An alignment the MIR does not state divides nothing.
                    (Some(align.unwrap_or(u64::MAX)), Some(found))
                }
                _ => continue,
            };
            check_blocks.insert(bb);
            let mut work: Vec<usize> =
                [Some(cond), found].into_iter().flatten().filter_map(operand_local).collect();
            let mut seen = HashSet::new();
            while let Some(local) = work.pop() {
                if !seen.insert(local) || seen.len() > 16 {
                    continue;
                }
                let Some([DefSite::Stmt(dbb, dsi)]) = defs.get(&local).map(Vec::as_slice) else {
                    continue;
                };
                let StatementKind::Assign(_, rvalue) = &body.blocks[*dbb].statements[*dsi].kind
                else {
                    continue;
                };
                match rvalue {
                    Rvalue::BinaryOp(_, a, b) => {
                        chain_sites.insert((*dbb, *dsi));
                        work.extend([a, b].into_iter().filter_map(operand_local));
                    }
                    Rvalue::UnaryOp(_, a) | Rvalue::Use(a, ..) => {
                        chain_sites.insert((*dbb, *dsi));
                        work.extend(operand_local(a));
                    }
                    Rvalue::Cast(kind, op, target)
                        if op
                            .ty(locals)
                            .is_ok_and(|src| cast_exposes_address(kind, src, *target)) =>
                    {
                        chain_sites.insert((*dbb, *dsi));
                        let root = self.operand_pointer_root(defs, op);
                        let pointee_size =
                            operand_local(op).and_then(|l| self.checked_pointee_size(defs, l));
                        let entry = casts.entry(local).or_insert(PointerCheckCast {
                            required_align: required,
                            root,
                            pointee_size,
                        });
                        entry.required_align = entry.required_align.max(required);
                    }
                    _ => {}
                }
            }
        }
        if casts.is_empty() {
            return casts;
        }
        let mut escaped: HashSet<usize> = HashSet::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                if chain_sites.contains(&(bb, si)) {
                    continue;
                }
                let mut mentioned = MentionedLocals(Vec::new());
                mentioned.visit_statement(stmt, statement_location(body, &bb, si));
                escaped.extend(mentioned.0.into_iter().filter(|l| casts.contains_key(l)));
            }
            if check_blocks.contains(&bb) {
                continue;
            }
            let mut mentioned = MentionedLocals(Vec::new());
            mentioned.visit_terminator(&block.terminator, terminator_location(body, &bb));
            escaped.extend(mentioned.0.into_iter().filter(|l| casts.contains_key(l)));
        }
        casts.retain(|local, _| !escaped.contains(local));
        casts
    }

    /// The root of a pointer operand. A reference to a pointer local (`&p`, as
    /// `PartialOrd::lt` takes it) roots where the pointer's value does.
    fn operand_pointer_root(&self, defs: &HashMap<usize, Vec<DefSite>>, op: &Operand) -> PtrRoot {
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return if matches!(op, Operand::Constant(_)) {
                PtrRoot::Foreign
            } else {
                PtrRoot::Unknown
            };
        };
        if !place.projection.is_empty() {
            return PtrRoot::Unknown;
        }
        let Some(decl) = self.body.locals().get(place.local) else { return PtrRoot::Unknown };
        if let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = decl.ty.kind()
            && ty_is_raw_ptr_or_ref_to_one(inner)
        {
            let Some([DefSite::Stmt(bb, si)]) = defs.get(&place.local).map(Vec::as_slice) else {
                return PtrRoot::Unknown;
            };
            return match &self.body.blocks[*bb].statements[*si].kind {
                StatementKind::Assign(_, Rvalue::Ref(_, _, pointer))
                    if pointer.projection.is_empty() =>
                {
                    self.pointer_root(defs, pointer.local)
                }
                _ => PtrRoot::Unknown,
            };
        }
        self.pointer_root(defs, place.local)
    }

    /// Walk a pointer local back through single-definition copies, pointer
    /// casts, reborrows and allocation-preserving calls to the place it was
    /// taken from.
    fn pointer_root(&self, defs: &HashMap<usize, Vec<DefSite>>, start: usize) -> PtrRoot {
        let arg_count = self.body.arg_locals().len();
        let locals = self.body.locals();
        let mut local = start;
        let mut seen = HashSet::new();
        while seen.insert(local) && seen.len() <= 32 {
            let Some(sites) = defs.get(&local) else {
                return if local != 0 && local <= arg_count {
                    PtrRoot::Foreign
                } else {
                    PtrRoot::Unknown
                };
            };
            let [site] = sites.as_slice() else { return PtrRoot::Unknown };
            let next = match *site {
                DefSite::Stmt(bb, si) => {
                    let StatementKind::Assign(_, rvalue) =
                        &self.body.blocks[bb].statements[si].kind
                    else {
                        return PtrRoot::Unknown;
                    };
                    match rvalue {
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => op,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            let derefs = place
                                .projection
                                .iter()
                                .filter(|p| matches!(p, ProjectionElem::Deref))
                                .count();
                            match (derefs, place.projection.first()) {
                                (0, _) => return PtrRoot::StackLocal(place.local),
                                (1, Some(ProjectionElem::Deref)) => {
                                    local = place.local;
                                    continue;
                                }
                                _ => return PtrRoot::Unknown,
                            }
                        }
                        _ => return PtrRoot::Unknown,
                    }
                }
                DefSite::Call(bb) => {
                    let TerminatorKind::Call { func, args, .. } =
                        &self.body.blocks[bb].terminator.kind
                    else {
                        return PtrRoot::Unknown;
                    };
                    let (Some(path), Some(arg0)) = (self.resolve_callee_path(func), args.first())
                    else {
                        return PtrRoot::Unknown;
                    };
                    let Ok(arg0_ty) = arg0.ty(locals) else { return PtrRoot::Unknown };
                    let preserves_allocation = (Self::offset_walk_identity_callee(&path)
                        && (ty_is_raw_ptr(arg0_ty) || ty_points_to_array_or_slice(arg0_ty)))
                        || ([
                            "::index",
                            "::index_mut",
                            "::get_unchecked",
                            "::get_unchecked_mut",
                            "::as_ptr",
                            "::as_mut_ptr",
                        ]
                        .iter()
                        .any(|m| path.ends_with(m))
                            && ty_points_to_array_or_slice(arg0_ty));
                    if !preserves_allocation {
                        return PtrRoot::Unknown;
                    }
                    arg0
                }
            };
            match next {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => local = p.local,
                Operand::Constant(_) => return PtrRoot::Foreign,
                _ => return PtrRoot::Unknown,
            }
        }
        PtrRoot::Unknown
    }

    /// Size of the pointee a check cast's pointer operand carries before
    /// rustc erased it to `*const ()`.
    fn checked_pointee_size(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        start: usize,
    ) -> Option<u64> {
        let locals = self.body.locals();
        let mut local = start;
        for _ in 0..8 {
            let ty = locals.get(local)?.ty;
            let (TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _))) =
                ty.kind()
            else {
                return None;
            };
            let is_unit = matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty());
            if !is_unit {
                return self.get_type_size(pointee).and_then(|s| u64::try_from(s).ok());
            }
            let [DefSite::Stmt(bb, si)] = defs.get(&local)?.as_slice() else { return None };
            let StatementKind::Assign(_, Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _)) =
                &self.body.blocks[*bb].statements[*si].kind
            else {
                return None;
            };
            local = operand_local(op)?;
        }
        None
    }

    /// Entry-rule constraints on the tracked bases. Allocates an object id for a
    /// tracked local the stack allocator skipped (a zero-sized local).
    ///
    /// A tracked base is `region << 48`: the local is the only object of its
    /// 2^48-byte region and sits at its base, as in Kani, whose objects sit at
    /// `id << 48`. The region is free (the order of two allocations stays
    /// unspecified), not 0 (the null page and the small integers), distinct
    /// from every other tracked base's, and not a tracked object id, so the
    /// region map ([`Self::address_region_of_object`]) is an involution. The
    /// base is 2^48-aligned, so no access to the local at an aligned offset is
    /// misaligned, as Kani reports (Rust promises only the type's alignment;
    /// the fourth round left a base offset `r` aligned for the type only, and
    /// certified misaligned-pointer counterexamples Kani refutes). Non-null and
    /// no-wrap follow. The first model left a base anywhere
    /// disjoint from the other bases: two locals could be adjacent, a base
    /// could sit on a constant address or one byte below an untracked
    /// object, and each certified a counterexample Kani refutes (fourth
    /// review of fix/chc-false-certificates, 2026-09-28:
    /// `ad3_stack_end_heap_start_safe`, `a4_stack_stack_adjacent_safe`,
    /// `a4_stack_const_addr_safe`).
    pub(in crate::codegen_ay::chc) fn stack_base_entry_constraints(&mut self) -> Vec<Expr> {
        if self.heap_state.stack_bases.is_empty() {
            return Vec::new();
        }
        let mut constraints = Vec::new();
        let mut bases = std::mem::take(&mut self.heap_state.stack_bases);
        for base in &mut bases {
            let obj_id = match self.heap_state.local_addresses.get(&base.local) {
                Some((id, _)) => Some(*id),
                None => self.heap_state.next_alloc_id().inspect(|&id| {
                    let addr_name =
                        crate::codegen_ay::names::state_var_addr_name(&self.fn_name, base.local);
                    self.heap_state.insert_local_address(base.local, id, addr_name);
                    if let Ok(size) = u32::try_from(base.size) {
                        constraints.push(
                            obj_size_in()
                                .select(Expr::bitvec_const(id as i128, 32))
                                .eq(Expr::bitvec_const(size as i128, 32)),
                        );
                    }
                }),
            };
            // An object id past the 16-bit object field has no region of its
            // own: the local stays untracked (its address is its identity's).
            base.obj_id = obj_id.filter(|&id| id < OBJECT_ID_LIMIT);
        }
        let tracked: Vec<&StackBase> = bases.iter().filter(|b| b.obj_id.is_some()).collect();
        let ids: Vec<u32> = tracked.iter().filter_map(|b| b.obj_id).collect();
        for (i, base) in tracked.iter().enumerate() {
            let var = base.var();
            // The base is its region over a zero offset: 2^48-aligned, as a
            // local is in Kani's layout. The fourth round left the low 32 bits
            // free and aligned only for the local's type, so a read needing
            // more alignment than the type guarantees could be misaligned:
            // `pad_cast_safe` / `sgn_cast_safe` (p1_ptr_cast.rs) and
            // `chc_aggregate_reinterpret_dual.rs` (8-aligned struct read as a
            // u128) failed the misaligned-pointer check with a certified
            // counterexample where Kani proves them (fifth round,
            // 2026-10-01: decided by Kani's layout, the oracle).
            constraints.push(var.clone().extract(47, 0).eq(Expr::bitvec_const(0u128, 48)));
            let region = base.region();
            constraints.push(region.clone().eq(Expr::bitvec_const(0u128, 16)).not());
            for id in &ids {
                constraints.push(region.clone().eq(Expr::bitvec_const(*id as i128, 16)).not());
            }
            for other in &tracked[i + 1..] {
                constraints.push(region.clone().eq(other.region()).not());
            }
        }
        debug!(
            tracked = tracked.len(),
            constraints = constraints.len(),
            "CHC stack base: entry constraints"
        );
        self.heap_state.stack_bases = bases;
        constraints
    }

    /// `(obj_id, region, offset in the region)` for every tracked local that
    /// has an object id.
    fn stack_base_table(&self) -> Vec<(u32, Expr, Expr)> {
        self.heap_state
            .stack_bases
            .iter()
            .filter_map(|b| b.obj_id.map(|id| (id, b.region(), b.in_region_offset())))
            .collect()
    }

    /// Object lane of a 64-bit split pointer, folded to a constant when possible.
    fn obj_lane(ptr: &Expr) -> (Expr, Option<u32>) {
        let lane = ptr.clone().extract(63, 32);
        match Self::const_obj_id_u32(&lane) {
            Some(id) => (Expr::bitvec_const(id as i128, 32), Some(id)),
            None => (lane, None),
        }
    }

    /// The object field of an identity term: its lane's low 16 bits. A wrapping
    /// step carries past the 32-bit offset into the lane's HIGH 16 bits (the
    /// high part of a 48-bit offset), never into this field; bit 15 of it is the
    /// [`FAR_BIT`].
    fn object_field(ptr: &Expr) -> Expr {
        ptr.clone().extract(47, 32)
    }

    /// The object of an identity term: its object field without the
    /// [`FAR_BIT`].
    fn object15(ptr: &Expr) -> Expr {
        ptr.clone().extract(46, 32)
    }

    /// The [`FAR_BIT`] of an identity term, as a 1-bit vector.
    fn far_flag(ptr: &Expr) -> Expr {
        ptr.clone().extract(47, 47)
    }

    /// Whether an identity term is far ([`FAR_BIT`]).
    pub(in crate::codegen_ay::chc) fn identity_is_far(ptr: &Expr) -> Expr {
        Self::far_flag(ptr).eq(Expr::bitvec_const(1u128, 1))
    }

    /// The 48-bit offset of an identity term (`h16` over the 32-bit offset).
    fn offset48(ptr: &Expr) -> Expr {
        ptr.clone().extract(63, 48).concat(ptr.clone().extract(31, 0))
    }

    /// The identity term with 48-bit offset `offset48`, far flag `far` (1 bit)
    /// and object `object15` (15 bits).
    fn compose_identity(offset48: Expr, far: Expr, object15: Expr) -> Expr {
        offset48
            .clone()
            .extract(47, 32)
            .concat(far)
            .concat(object15)
            .concat(offset48.extract(31, 0))
    }

    /// Whether the identity term `ptr` points into a tracked object (its object
    /// field is a tracked id; the high offset bits may be set), and, when it
    /// does, its observed address `region << 48 | (r + offset48) mod 2^48`.
    pub(in crate::codegen_ay::chc) fn stack_observed_address(
        table: &[(u32, Expr, Expr)],
        ptr: &Expr,
        default: Expr,
    ) -> (Expr, Expr) {
        let object = Self::object_field(ptr);
        let low48 = Self::offset48(ptr);
        if let Some(id) = Self::const_bv_u32(&object) {
            return match table.iter().find(|(tid, _, _)| *tid == id) {
                Some((_, region, r)) => (
                    region.clone().concat(Self::plus_region_offset(low48, r)),
                    Expr::bool_const(true),
                ),
                None => (default, Expr::bool_const(false)),
            };
        }
        let mut addr = default;
        let mut tracked = Expr::bool_const(false);
        for (id, region, r) in table.iter().rev() {
            let is_id = object.clone().eq(Expr::bitvec_const(*id as i128, 16));
            let observed = region.clone().concat(Self::plus_region_offset(low48.clone(), r));
            addr = Expr::ite(is_id.clone(), observed, addr);
            tracked = is_id.or(tracked);
        }
        (addr, tracked)
    }

    /// `offset48 + r`, skipping the sum when `r` folds to zero (every tracked
    /// base is 2^48-aligned, so it always does).
    fn plus_region_offset(offset48: Expr, r: &Expr) -> Expr {
        if Self::const_bv_u32(r) == Some(0) { offset48 } else { offset48.bvadd(r.clone()) }
    }
    /// The offset in its region of the object with object field `object`: the
    /// base's `r` for a tracked local, 0 for any other object.
    fn in_region_offset_of_object(object: &Expr, table: &[(u32, Expr, Expr)]) -> Expr {
        let zero = Expr::bitvec_const(0u128, REGION_SHIFT);
        if let Some(value) = Self::const_bv_u32(object) {
            return table
                .iter()
                .find(|(id, _, _)| *id == value)
                .map_or(zero, |(_, _, r)| r.clone());
        }
        table.iter().rev().fold(zero, |acc, (id, _, r)| {
            Expr::ite(object.clone().eq(Expr::bitvec_const(*id as i128, 16)), r.clone(), acc)
        })
    }

    /// A constant bit-vector's value, when it fits `u32`.
    fn const_bv_u32(e: &Expr) -> Option<u32> {
        let (value, _width) =
            crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value(e)?;
        u32::try_from(value).ok()
    }

    /// The address region (the top 16 bits of an address) of the object with
    /// the 16-bit object field `object`, and the inverse: the map swaps each
    /// tracked id with its base's region and fixes every other value
    /// (`stack_base_entry_constraints` keeps the swaps disjoint), so it is its
    /// own inverse. An untracked object's region is its id, as in Kani.
    ///
    /// A constant id that is an allocated, untracked object keeps its region
    /// under the layout fact that no tracked base took it (recorded for the
    /// rule under construction). Kani gives every object its own region, so
    /// every layout Kani admits satisfies the fact.
    fn address_region_of_object(&self, object: Expr, table: &[(u32, Expr, Expr)]) -> Expr {
        if table.is_empty() {
            return object;
        }
        if let Some(value) = Self::const_bv_u32(&object) {
            if let Some((_, region, _)) = table.iter().find(|(id, _, _)| *id == value) {
                return region.clone();
            }
            if value != 0 && value < self.heap_state.next_alloc_id {
                let apart = table
                    .iter()
                    .map(|(_, region, _)| region.clone().eq(object.clone()).not())
                    .reduce(Expr::and);
                if let Some(fact) = apart {
                    self.pending_address_assumptions.borrow_mut().push(fact);
                }
                return object;
            }
            if value == 0 {
                return object;
            }
        }
        let mut mapped = object.clone();
        for (id, region, _) in table.iter().rev() {
            let id_expr = Expr::bitvec_const(*id as i128, 16);
            mapped = Expr::ite(
                object.clone().eq(id_expr.clone()),
                region.clone(),
                Expr::ite(object.clone().eq(region.clone()), id_expr, mapped),
            );
        }
        mapped
    }

    /// [`Self::address_region_of_object`] for the SYMBOLIC object field of a
    /// pointer being cast to an integer: a tracked id maps to its base's region,
    /// any other value to itself, under the recorded fact that no tracked base
    /// took that value as its region (vacuous for a tracked id). The full map's
    /// other half (a tracked region back to its id) is only reached by an
    /// integer cast to a pointer, which takes [`Self::int_to_ptr_value`]; a
    /// pointer whose object field is an allocation's id never needs it. Keeping
    /// it out leaves `ite(obj == t_i, ..)` conditions that constant
    /// propagation folds once the field is known: with the swap half, a Box
    /// field's address kept a comparison against a free region, and
    /// `negative/alloc_id_fields_offsets.rs::box_u32_fields_offset_safe` lost
    /// its straight-line proof (a 0.01 s proof on main, Unknown at 63 s).
    fn address_region_of_pointer_object(&self, object: Expr, table: &[(u32, Expr, Expr)]) -> Expr {
        let is_tracked = table.iter().fold(Expr::bool_const(false), |acc, (id, _, _)| {
            acc.or(object.clone().eq(Expr::bitvec_const(*id as i128, 16)))
        });
        let apart = table
            .iter()
            .map(|(_, region, _)| region.clone().eq(object.clone()).not())
            .reduce(Expr::and);
        if let Some(apart) = apart {
            self.pending_address_assumptions.borrow_mut().push(is_tracked.or(apart));
        }
        table.iter().rev().fold(object.clone(), |acc, (id, region, _)| {
            Expr::ite(object.clone().eq(Expr::bitvec_const(*id as i128, 16)), region.clone(), acc)
        })
    }

    /// Replacement operands for a relational comparison of two thin raw pointers.
    /// Comparing the returned pair with the unsigned bit-vector order is exact on
    /// offsets within one allocation and the order of the observed addresses
    /// across allocations. See the module docs.
    pub(in crate::codegen_ay::chc) fn ptr_order_operands(
        &mut self,
        lhs: Expr,
        rhs: Expr,
    ) -> (Expr, Expr) {
        if !is_thin_ptr_sort(&lhs) || !is_thin_ptr_sort(&rhs) || self.int_lift {
            return (lhs, rhs);
        }
        // Kani orders far pointers by their object bits and low 48 offset bits
        // under a symbolic count and by the full offsets under a literal one.
        if self.may_be_far_observed(&lhs) || self.may_be_far_observed(&rhs) {
            self.record_far_observation(
                Self::identity_is_far(&lhs).or(Self::identity_is_far(&rhs)),
                "order",
            );
        }
        let (lane_l, id_l) = Self::obj_lane(&lhs);
        let (lane_r, id_r) = Self::obj_lane(&rhs);
        let statically_same = match (id_l, id_r) {
            (Some(a), Some(b)) => Some(a == b),
            _ if lane_l == lane_r => Some(true),
            _ => None,
        };
        if statically_same == Some(true) {
            return (lhs, rhs);
        }
        let table = self.stack_base_table();
        let (addr_l, tracked_l) = Self::stack_observed_address(&table, &lhs, lhs.clone());
        let (addr_r, tracked_r) = Self::stack_observed_address(&table, &rhs, rhs.clone());
        let both_tracked = tracked_l.and(tracked_r);
        let (cross_l, cross_r) = if bool_const_value(&both_tracked) == Some(true) {
            (addr_l, addr_r)
        } else {
            let booked = self.record_sound_fallback_reason("cross_alloc_ptr_order_untracked");
            let fresh_l =
                Havoc::booked(booked, chc_fresh_name("__cross_alloc_order_l"), Sort::bitvec(64));
            let fresh_r =
                Havoc::booked(booked, chc_fresh_name("__cross_alloc_order_r"), Sort::bitvec(64));
            if bool_const_value(&both_tracked) == Some(false) {
                (fresh_l, fresh_r)
            } else {
                (
                    Expr::ite(both_tracked.clone(), addr_l, fresh_l),
                    Expr::ite(both_tracked, addr_r, fresh_r),
                )
            }
        };
        if statically_same == Some(false) {
            return (cross_l, cross_r);
        }
        let same = lane_l.eq(lane_r);
        (Expr::ite(same.clone(), lhs, cross_l), Expr::ite(same, rhs, cross_r))
    }

    /// The integer a thin raw pointer casts to: the address of its identity
    /// term, `region(object) << 48 | offset48` ([`Self::identity_address`]):
    /// every object has its own 2^48-byte region, an untracked object the region
    /// numbered by its id and a tracked local the free region of its base.
    ///
    /// The address of a FAR pointer ([`FAR_BIT`]) is an observation Kani answers
    /// in more than one way: its object bits over the low 48 offset bits for
    /// `addr()` and for a symbolic count, the 64-bit sum for `as usize` with a
    /// literal count (corpus-rev Kani, 2026-10-02). It is fail-closed
    /// ([`Self::record_far_observation`]). The fifth round answered with the
    /// arithmetic address where no object owned the window the pointer reached,
    /// and certified or proved what that address implied:
    /// `p.wrapping_byte_sub(k).addr() == p.addr() - k` for a symbolic `k == 1`
    /// was proved, where Kani fails it (first review of the sixth round,
    /// `k48d.rs` `s_cast_neg1`, `s_addr_neg1`).
    ///
    /// The first model read an untracked object's identity term as its address,
    /// which put objects 2^32 apart: `heap_a as usize + (1 << 32) == heap_b as
    /// usize` held, and a tracked base could sit one byte below a `Box`'s
    /// address. Both certified counterexamples Kani refutes (fourth review of
    /// fix/chc-false-certificates, 2026-09-28: `ad3_heap_minus1_safe`,
    /// `ad3_heap_plus_2p32_safe`, `a4_heap_heap_plus_2p32_safe`).
    pub(in crate::codegen_ay::chc) fn ptr_to_int_value(&self, ptr: Expr) -> Expr {
        if !is_thin_ptr_sort(&ptr) || self.int_lift {
            return ptr;
        }
        if self.may_be_far_observed(&ptr) {
            self.record_far_observation(Self::identity_is_far(&ptr), "address");
        }
        self.identity_address(&ptr)
    }

    /// [`Self::ptr_to_int_value`] without recording the observation.
    fn identity_address(&self, ptr: &Expr) -> Expr {
        let table = self.stack_base_table();
        let object = Self::object_field(ptr);
        let region = if !table.is_empty() && Self::const_bv_u32(&object).is_none() {
            self.address_region_of_pointer_object(object.clone(), &table)
        } else {
            self.address_region_of_object(object.clone(), &table)
        };
        let low48 = Self::offset48(ptr);
        let low48 = if table.is_empty() {
            low48
        } else {
            Self::plus_region_offset(low48, &Self::in_region_offset_of_object(&object, &table))
        };
        let address = region.concat(low48);
        trust_mc_core::chc_const_prop::eval::try_eval_to_const(&address).unwrap_or(address)
    }

    /// The address region of the object of the identity term `ptr` (its field
    /// without the [`FAR_BIT`]).
    fn identity_object_region(&self, ptr: &Expr) -> Expr {
        let table = self.stack_base_table();
        let object = Expr::bitvec_const(0u128, 1).concat(Self::object15(ptr));
        let object =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&object).unwrap_or(object);
        if !table.is_empty() && Self::const_bv_u32(&object).is_none() {
            self.address_region_of_pointer_object(object, &table)
        } else {
            self.address_region_of_object(object, &table)
        }
    }

    /// A wrapping pointer step (`wrapping_add`, `wrapping_byte_offset`,
    /// `arith_offset`, ...) by `byte_offset` bytes, subtracted when `is_sub`.
    /// See [`Self::step_wrapping_address_from`].
    pub(in crate::codegen_ay::chc) fn step_wrapping_address(
        &self,
        ptr: Expr,
        byte_offset: Expr,
        is_sub: bool,
    ) -> Expr {
        self.step_wrapping_address_from(ptr, byte_offset, is_sub, None)
    }

    /// A wrapping pointer step from a pointer whose 64-bit offset from its
    /// object's base the caller may know (`base_t64`,
    /// [`Self::wrapping_operand_t64`]).
    ///
    /// # Kani's object range
    ///
    /// Rust keeps a pointer's provenance under wrapping arithmetic and Kani its
    /// object bits, so the step keeps the pointer's OBJECT and moves its offset
    /// `T` from the object's base, mod 2^64. While `T` stays in `[0, 2^48)`,
    /// Kani's object range, the stepped identity is the object over `T` and every
    /// observation of it is exact: `q.addr() == p.addr() + k` for any `k` that
    /// keeps `q` below `2^48` past the base, as Rust and every Kani mode agree.
    /// Outside it the pointer is FAR: its object field carries the [`FAR_BIT`]
    /// over the object, its 48 offset bits are `T`'s low 48 bits, and a
    /// dereference is outside its object.
    ///
    /// The fifth round used windows CENTERED on each base (`[-2^47, 2^47)`) and
    /// decided landing at their edge: a step of `2^47` to `2^48 - 8` bytes was
    /// marked as landed in the next window and given a fixed wrong address, and
    /// a step into a window no object owned took that window as its object, so
    /// the way back was marked as landed in its own object. Both proved real bugs
    /// clean (`p.wrapping_byte_add(k).addr() != p.addr() + k` for `k == 2^47`,
    /// `p.wrapping_byte_add(k).wrapping_byte_sub(k) != p` for `k == 2^62`) and
    /// certified false counterexamples (first review of the sixth round,
    /// 2026-10-02: `r1a.rs`, `r1i.rs`, `r1j.rs`).
    ///
    /// # A step from a far pointer
    ///
    /// The identity keeps only `T`'s low 48 bits, so a step from a far pointer
    /// knows `T` exactly only through `base_t64`, the offset its caller
    /// accumulated along the pointer's definition chain (which makes the round
    /// trip `p + k - k` exactly `p`), or through a far constant this body built.
    /// Otherwise the result's low 48 bits are exact and whether it is far is a
    /// free bit, an identified sound approximation ([`Self::far_step_unknown`]).
    pub(in crate::codegen_ay::chc) fn step_wrapping_address_from(
        &self,
        ptr: Expr,
        byte_offset: Expr,
        is_sub: bool,
        base_t64: Option<Expr>,
    ) -> Expr {
        use crate::codegen_ay::chc::pointer_step::step_wrapping_pointer;
        if !is_thin_ptr_sort(&ptr) || self.int_lift || byte_offset.sort().bitvec_width() != Some(64)
        {
            return step_wrapping_pointer(ptr, byte_offset, is_sub);
        }
        let fold =
            |e: Expr| trust_mc_core::chc_const_prop::eval::try_eval_to_const(&e).unwrap_or(e);
        let k = fold(byte_offset);
        let delta = if is_sub { fold(Expr::bitvec_const(0u128, 64).bvsub(k)) } else { k };
        if const_u64(&delta) == Some(0) {
            return ptr;
        }
        let t64 = base_t64.or_else(|| self.identity_t64(&ptr));
        let object15 = fold(Self::object15(&ptr));
        let (result, moved_t64) = match t64 {
            Some(t) => {
                let moved = fold(t.bvadd(delta));
                let far = Self::far_flag_of_t64(&moved);
                (Self::compose_identity(moved.clone().extract(47, 0), far, object15), Some(moved))
            }
            None => {
                let offset48 = Self::offset48(&ptr);
                let moved48 = offset48.clone().bvadd(delta.clone().extract(47, 0));
                let exact = Self::far_flag_of_t64(&offset48.zero_extend(16).bvadd(delta));
                let far = self.far_or_unknown(&ptr, exact);
                (Self::compose_identity(moved48, far, object15), None)
            }
        };
        let result = fold(result);
        self.note_far_producer(&result);
        if let (Some(value), Some(t)) = (const_u64(&result), moved_t64.as_ref().and_then(const_u64))
            && value & (u64::from(FAR_BIT) << 32) != 0
        {
            // A far constant: remember its full offset, unless another far
            // constant with the same identity had a different one.
            let mut table = self.far_literal_t64.borrow_mut();
            let entry = table.entry(value).or_insert(Some(t));
            if *entry != Some(t) {
                *entry = None;
            }
        }
        result
    }

    /// The [`FAR_BIT`] of a 64-bit offset `T`: 1 when `T` is outside `[0,
    /// 2^48)`, as a 1-bit vector.
    fn far_flag_of_t64(t64: &Expr) -> Expr {
        let outside = t64.clone().extract(63, 48).eq(Expr::bitvec_const(0u128, 16)).not();
        let flag = Expr::ite(outside, Expr::bitvec_const(1u128, 1), Expr::bitvec_const(0u128, 1));
        trust_mc_core::chc_const_prop::eval::try_eval_to_const(&flag).unwrap_or(flag)
    }

    /// The 64-bit offset `T` of an identity term from its object's base, when
    /// it is known: the zero-extended 48 offset bits of a pointer that is not
    /// far (its far bit folds to zero, or [`Self::may_be_far`] rules it out), or
    /// the offset of a far constant this body built.
    fn identity_t64(&self, ptr: &Expr) -> Option<Expr> {
        let far = Self::far_flag(ptr);
        let far = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&far).unwrap_or(far);
        match Self::const_bv_u32(&far) {
            Some(0) => Some(Self::offset48(ptr).zero_extend(16)),
            Some(_) => {
                let value = const_u64(ptr)?;
                let known = self.far_literal_t64.borrow().get(&value).copied().flatten()?;
                Some(Expr::bitvec_const(known as u128, 64))
            }
            None => (!self.may_be_far(ptr)).then(|| Self::offset48(ptr).zero_extend(16)),
        }
    }

    /// The free bit of a step from a far pointer whose full offset is unknown
    /// ([`Self::step_wrapping_address_from`]): a fresh 1-bit declare-var,
    /// accounted as an identified sound approximation, so a counterexample that
    /// reads it is not certified while a proof over both of its values stands.
    /// The far bit of a pointer built from `ptr` when `exact` is its far bit
    /// for a `ptr` that is not far: `exact` unless `ptr` may be far
    /// ([`Self::may_be_far`]), then a free bit on the paths where it is
    /// ([`Self::far_step_unknown`]), created only then so a pointer that cannot
    /// be far records no approximation.
    fn far_or_unknown(&self, ptr: &Expr, exact: Expr) -> Expr {
        let is_far = Self::identity_is_far(ptr);
        let is_far =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&is_far).unwrap_or(is_far);
        if bool_const_value(&is_far) == Some(false) || !self.may_be_far(ptr) {
            return exact;
        }
        Expr::ite(is_far, self.far_step_unknown(), exact)
    }

    fn far_step_unknown(&self) -> Expr {
        let name = chc_fresh_name("__wrap_far_unknown");
        debug!(fn_name = %self.fn_name, %name, "CHC: a free far bit for a step from a pointer that may be far");
        Havoc::mint_deferred(self, sound_havoc::WRAPPING_STEP_FAR_UNKNOWN, name, Sort::bitvec(1))
    }

    /// `p.with_addr(a)`, which is `p.wrapping_byte_offset(a - p.addr())`: the
    /// pointer with `p`'s object at address `a`. For a `p` that is not far,
    /// `T + a - p.addr()` is `a - base(p)`, so the result is `p`'s object over
    /// `a`'s low 48 bits, far exactly when `a` is outside `p`'s region, with no
    /// term over `p`'s own offset. The fifth round stepped through the address
    /// and back, a term per step that straight-line fusion inlined into the next:
    /// on tag round trips (`map_addr(|a| a | 1)` and back) the compiler did not
    /// finish inside the driver's budget (first review of the sixth round,
    /// `r1e_split` `e01`-`e09`). For a far `p` the low 48 bits are the same in
    /// every mode and whether the result is far is a free bit.
    ///
    /// `keeps_region` is the caller's MIR evidence that `a`'s top 16 bits are
    /// `p`'s region (`address_keeps_pointer_region`: `p.addr()` under tag
    /// arithmetic), so the result is not far.
    pub(in crate::codegen_ay::chc) fn with_addr_value(
        &self,
        ptr: Expr,
        addr: Expr,
        keeps_region: bool,
        base_not_far: bool,
    ) -> Expr {
        if !is_thin_ptr_sort(&ptr) || self.int_lift || addr.sort().bitvec_width() != Some(64) {
            let address = self.ptr_to_int_value(ptr.clone());
            return crate::codegen_ay::chc::pointer_step::step_wrapping_pointer(
                ptr,
                addr.bvsub(address),
                false,
            );
        }
        let region = self.identity_object_region(&ptr);
        // `p.map_addr(|a| a | TAG)` and back give an address whose top 16 bits
        // are syntactically `p`'s region: decide it here, so the result is not
        // far and observing it costs nothing.
        let top = address_top_bits(&addr).unwrap_or_else(|| addr.clone().extract(63, REGION_SHIFT));
        let outside = if keeps_region || top == region {
            Expr::bool_const(false)
        } else {
            top.eq(region).not()
        };
        let exact = Expr::ite(outside, Expr::bitvec_const(1u128, 1), Expr::bitvec_const(0u128, 1));
        let far = if base_not_far || self.identity_t64(&ptr).is_some() {
            exact
        } else {
            self.far_or_unknown(&ptr, exact)
        };
        let result =
            Self::compose_identity(addr.extract(REGION_SHIFT - 1, 0), far, Self::object15(&ptr));
        let result =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&result).unwrap_or(result);
        self.note_far_producer(&result);
        result
    }

    /// Note a pointer this body built that may be far. In a body the prescan
    /// ([`Self::far_pointers_possible`]) took for one that builds none (a step
    /// inside a walked closure or callee), far pointers become possible from
    /// here on; an observation translated earlier recorded no fail-closed
    /// condition, so when one was skipped the harness fails closed
    /// ([`Self::book_far_pointer_prescan`]).
    fn note_far_producer(&self, ptr: &Expr) {
        if self.far_pointers_possible() {
            return;
        }
        let far = Self::far_flag(ptr);
        let far = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&far).unwrap_or(far);
        if Self::const_bv_u32(&far) != Some(0) {
            self.far_pointers_possible_cache.set(Some(true));
            if self.far_observation_skipped.get() {
                self.far_prescan_missed.set(true);
            }
        }
    }

    /// An observation site met while no far pointer is possible yet: remember
    /// it if a later step could still make `ptr` far ([`Self::note_far_producer`]).
    fn note_observation_without_far_pointers(&self, ptr: &Expr) {
        if self.far_pointers_possible()
            || !is_thin_ptr_sort(ptr)
            || self.far_observation_suppressed.get()
        {
            return;
        }
        let far = Self::far_flag(ptr);
        let far = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&far).unwrap_or(far);
        if Self::const_bv_u32(&far) != Some(0) {
            self.far_observation_skipped.set(true);
        }
    }

    /// A far pointer appeared after an observation was translated without
    /// fail-closed conditions ([`Self::note_far_producer`]): ask
    /// `mir_to_chc_internal` to translate the body again with far pointers
    /// possible from the start ([`take_far_prescan_retry`]); in that second
    /// translation (or wherever no retry follows) the harness fails closed.
    pub(in crate::codegen_ay::chc) fn book_far_pointer_prescan(&mut self) {
        if !self.far_prescan_missed.get() {
            return;
        }
        if far_forced_for(&self.fn_name) {
            self.record_sound_fallback_reason("far_pointer_outside_prescan");
            return;
        }
        debug!(fn_name = %self.fn_name, "CHC: far pointer outside the prescan; retranslating");
        FAR_RETRY_FN.with(|f| *f.borrow_mut() = Some(self.fn_name.to_string()));
        // This VC is discarded for the retry's, so none of its per-function
        // diagnostics are recorded (`translate_inner`).
        self.far_retry_requested = true;
    }

    /// Whether this body may build a far pointer: it calls a wrapping step, a
    /// rebasing call or an integer-to-pointer constructor, or casts or transmutes
    /// an integer to a pointer. Every far pointer starts at one of these (a
    /// havocked pointer value is an approximation of its own); a translation that
    /// builds one anyway fails closed ([`Self::note_far_producer`]).
    pub(in crate::codegen_ay::chc) fn far_pointers_possible(&self) -> bool {
        if let Some(known) = self.far_pointers_possible_cache.get() {
            return known;
        }
        if far_forced_for(&self.fn_name) {
            self.far_pointers_possible_cache.set(Some(true));
            return true;
        }
        let answer = self.body_may_build_far_pointers();
        self.far_pointers_possible_cache.set(Some(answer));
        answer
    }

    fn body_may_build_far_pointers(&self) -> bool {
        if self.int_lift || POINTER_WIDTH != 64 {
            return false;
        }
        let locals = self.body.locals();
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(_, Rvalue::Cast(kind, op, target)) = &stmt.kind else {
                    continue;
                };
                let Ok(src) = op.ty(locals) else { return true };
                let to_ptr = ty_is_pointer_like(*target);
                match kind {
                    CastKind::PointerWithExposedProvenance => return true,
                    CastKind::Transmute if to_ptr && ty_is_provenance_free_bits(src) => {
                        return true;
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                let Some(path) =
                    self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
                else {
                    continue;
                };
                if FAR_PRODUCING_CALLEES.iter().any(|m| path.ends_with(m)) {
                    return true;
                }
                if WRAPPING_STEP_CALLEES.iter().any(|m| path.ends_with(m))
                    && args.first().and_then(|a| a.ty(locals).ok()).is_some_and(ty_is_raw_ptr)
                {
                    return true;
                }
            }
        }
        false
    }

    /// Whether the identity term `ptr` may be far. False when this body builds
    /// no far pointer ([`Self::far_pointers_possible`]), when its far bit folds
    /// to zero, or when every variable it reads is a state variable of a local
    /// whose definition chain cannot produce a far pointer
    /// ([`Self::pointer_local_may_be_far`]). The walk visits each node of the
    /// expression's DAG once.
    pub(in crate::codegen_ay::chc) fn may_be_far(&self, ptr: &Expr) -> bool {
        self.may_be_far_for(ptr, false)
    }

    /// [`Self::may_be_far`] for an OBSERVATION of `ptr` (its address, order or
    /// equality): a pointer built from an integer (`n as *const T`,
    /// `without_provenance`) is the integer's own object over its low 48 bits,
    /// in every mode Kani uses, so its observation is exact even when its
    /// object field's top bit (an object no allocation has) reads like the
    /// [`FAR_BIT`]; a step from it still treats that bit as far.
    pub(in crate::codegen_ay::chc) fn may_be_far_observed(&self, ptr: &Expr) -> bool {
        self.may_be_far_for(ptr, true)
    }

    fn may_be_far_for(&self, ptr: &Expr, observation: bool) -> bool {
        if !self.far_pointers_possible() {
            if observation {
                self.note_observation_without_far_pointers(ptr);
            }
            return false;
        }
        if observation
            && self.far_from_integer.borrow().iter().any(|e| std::ptr::eq(e.value(), ptr.value()))
        {
            return false;
        }
        let far = Self::far_flag(ptr);
        let far = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&far).unwrap_or(far);
        match Self::const_bv_u32(&far) {
            Some(0) => return false,
            Some(_) => return true,
            None => {}
        }
        let mut stack = vec![ptr.clone()];
        let mut seen: HashSet<usize> = HashSet::new();
        while let Some(node) = stack.pop() {
            if !seen.insert(node.value() as *const ExprValue as usize) {
                continue;
            }
            if let ExprValue::Var { name } = node.value() {
                if self.var_may_hold_far_pointer(name, observation) {
                    return true;
                }
                continue;
            }
            stack.extend(node.children().cloned());
        }
        false
    }

    /// Whether the state variable `name` may hold (or feed) a far pointer: true
    /// for a variable that is no local's state variable (a fresh value, a memory
    /// array) and for a local whose definition chain may produce one.
    fn var_may_hold_far_pointer(&self, name: &str, observation: bool) -> bool {
        let key = if observation { format!("{name}\u{0}observed") } else { name.to_string() };
        if let Some(&known) = self.far_var_cache.borrow().get(&key) {
            return known;
        }
        let slot = self
            .state_var_index_by_name(name)
            .or_else(|| self.output_state_var_index_by_name(name));
        let answer = match slot.and_then(|slot| {
            self.state_var_mgr
                .local_to_state_idx
                .iter()
                .find_map(|(&local, &idx)| (idx == slot).then_some(local))
        }) {
            Some(local) => self.pointer_local_may_be_far(local, observation),
            None => true,
        };
        self.far_var_cache.borrow_mut().insert(key, answer);
        answer
    }

    /// Whether a local's value may be (or feed) a far pointer: false only when
    /// a walk through single definitions (copies, casts, reborrows, `as_ptr` /
    /// `as_mut_ptr` / indexing of an array or slice, and in-bounds `add` / `sub`
    /// / `offset` / `byte_*` / the `offset` intrinsic) reaches a place's address,
    /// a constant or a fresh allocation (`Box::new`, the allocator) without
    /// passing a wrapping step, a join, a load, a parameter or another call.
    /// Whether the pointer operand `op` is a local whose definition chain
    /// cannot produce a far pointer ([`Self::pointer_local_may_be_far`]).
    pub(in crate::codegen_ay::chc) fn operand_cannot_be_far(&self, op: &Operand) -> bool {
        operand_local(op).is_some_and(|local| !self.pointer_local_may_be_far(local, false))
    }

    fn pointer_local_may_be_far(&self, start: usize, observation: bool) -> bool {
        let key = (start, observation);
        if let Some(&known) = self.far_local_cache.borrow().get(&key) {
            return known;
        }
        let answer = self.pointer_local_may_be_far_walk(start, observation);
        debug!(fn_name = %self.fn_name, local = start, observation, answer, "CHC: may a local hold a far pointer");
        self.far_local_cache.borrow_mut().insert(key, answer);
        answer
    }

    fn pointer_local_may_be_far_walk(&self, start: usize, observation: bool) -> bool {
        let defs = self.local_def_sites();
        let mut local = start;
        let mut seen = HashSet::new();
        while seen.insert(local) && seen.len() <= 32 {
            // A write through a reference to the local is a definition the
            // def sites do not list (`*r = p.wrapping_byte_add(k)`, `swap`).
            if self.address_taken_locals().contains(&local) {
                return true;
            }
            let Some(sites) = defs.get(&local) else { return true };
            let [site] = sites.as_slice() else { return true };
            let next = match *site {
                DefSite::Stmt(bb, si) => {
                    let StatementKind::Assign(_, rvalue) =
                        &self.body.blocks[bb].statements[si].kind
                    else {
                        return true;
                    };
                    match rvalue {
                        Rvalue::Cast(CastKind::PointerWithExposedProvenance, ..) => {
                            return !observation;
                        }
                        Rvalue::Cast(CastKind::Transmute, op, target)
                            if ty_is_pointer_like(*target)
                                && op
                                    .ty(self.body.locals())
                                    .is_ok_and(ty_is_provenance_free_bits) =>
                        {
                            return !observation;
                        }
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                            if !place.projection.is_empty() =>
                        {
                            match self.field_read_source(&defs, place) {
                                FieldReadSource::FreshAllocation => return false,
                                FieldReadSource::Operand(op) => op,
                                FieldReadSource::Unknown => return true,
                            }
                        }
                        Rvalue::Use(op, ..)
                        | Rvalue::Cast(_, op, _)
                        | Rvalue::BinaryOp(BinOp::Offset, op, _) => op,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            let derefs = place
                                .projection
                                .iter()
                                .filter(|p| matches!(p, ProjectionElem::Deref))
                                .count();
                            match (derefs, place.projection.first()) {
                                (0, _) => return false,
                                (1, Some(ProjectionElem::Deref)) => {
                                    local = place.local;
                                    continue;
                                }
                                _ => return true,
                            }
                        }
                        _ => return true,
                    }
                }
                DefSite::Call(bb) => {
                    let TerminatorKind::Call { func, args, .. } =
                        &self.body.blocks[bb].terminator.kind
                    else {
                        return true;
                    };
                    let path =
                        self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func));
                    let (Some(path), Some(arg0)) = (path, args.first()) else {
                        return true;
                    };
                    // `p.with_addr(a)` with `a` built from `p.addr()` by tag
                    // arithmetic (`address_keeps_pointer_region`) is `p`'s object
                    // at an address in `p`'s own region: far exactly when `p` is
                    // (`with_addr_value`).
                    if path.ends_with("::with_addr")
                        && args.get(1).is_some_and(|a| self.address_keeps_pointer_region(a, arg0))
                    {
                        match arg0 {
                            // Observing it is exact only when `p` cannot be far
                            // at all: a pointer from an integer, exact to
                            // observe itself, is a far bit's look-alike to
                            // rebase (`with_addr_value`).
                            Operand::Copy(p) | Operand::Move(p)
                                if p.projection.is_empty() && observation =>
                            {
                                return self.pointer_local_may_be_far(p.local, false);
                            }
                            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                                local = p.local;
                                continue;
                            }
                            _ => return true,
                        }
                    }
                    if WRAPPING_STEP_CALLEES.iter().any(|m| path.ends_with(m))
                        || path.ends_with("arith_offset")
                    {
                        return true;
                    }
                    // A pointer built from an integer: exact to observe, a far
                    // bit's look-alike to step from (`may_be_far_observed`).
                    if FAR_PRODUCING_CALLEES.iter().any(|m| path.ends_with(m)) {
                        let from_integer =
                            arg0.ty(self.body.locals()).is_ok_and(ty_is_provenance_free_bits);
                        return !(observation && from_integer);
                    }
                    // The data pointer of a `Box` (`into_raw`, `leak`, `as_ptr`,
                    // ...) is the pointer the box was built from: a fresh
                    // allocation for `Box::new`, the argument of
                    // `Box::from_raw`. `Box::from_raw` of memory that is not a
                    // `Box` allocation of that layout is undefined behavior Kani
                    // does not report, so a far pointer round-tripped through a
                    // box stays far (`Box::from_raw(q)` with `q` stepped by
                    // `1 << 48` gave `Box::into_raw(b) != p` a clean proof where
                    // Kani fails it: review of fix/chc-false-certificates round 1,
                    // `rv_far_obs.rs` `o11_box_from_raw_roundtrip`, the same on
                    // main).
                    if let Some(box_local) = self.box_accessor_box_local(&defs, &path, arg0) {
                        match self.box_pointer_source(&defs, box_local) {
                            BoxPointerSource::Allocation => return false,
                            BoxPointerSource::FromRaw(raw) => match operand_local(raw) {
                                Some(raw_local) => {
                                    local = raw_local;
                                    continue;
                                }
                                None => return !matches!(raw, Operand::Constant(_)),
                            },
                            BoxPointerSource::Unknown => return true,
                        }
                    }
                    // A fresh allocation (a `Box`, or the allocator's
                    // pointer), or the allocation pointer of a `Vec`, is no far
                    // pointer.
                    if call_returns_allocation_pointer(&path) {
                        return false;
                    }
                    let in_bounds_step = [
                        "::add",
                        "::sub",
                        "::offset",
                        "::byte_add",
                        "::byte_sub",
                        "::byte_offset",
                        "::cast",
                        "::cast_mut",
                        "::cast_const",
                    ]
                    .iter()
                    .any(|m| path.ends_with(m))
                        && (path.contains("const_ptr") || path.contains("mut_ptr"))
                        || path.contains("rustc_intrinsics::offset");
                    let place_pointer = [
                        "::as_ptr",
                        "::as_mut_ptr",
                        "::index",
                        "::index_mut",
                        "::get_unchecked",
                        "::get_unchecked_mut",
                    ]
                    .iter()
                    .any(|m| path.ends_with(m))
                        && arg0.ty(self.body.locals()).is_ok_and(ty_points_to_array_or_slice);
                    // `str::as_ptr` is the reference's data pointer, no step:
                    // `T.as_ptr()` of a constant `&str` is no far pointer
                    // (const_pointer_raw_from_ref_dual.rs `bug_substr_as_ptr`
                    // lost its Genuine label to a free far bit on the merge
                    // with main's constant-pointer rows).
                    let str_pointer = path.ends_with("::as_ptr")
                        && arg0.ty(self.body.locals()).is_ok_and(ty_points_to_str);
                    if !(in_bounds_step || place_pointer || str_pointer) {
                        return true;
                    }
                    arg0
                }
            };
            match next {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => local = p.local,
                Operand::Constant(_) => return false,
                _ => return true,
            }
        }
        true
    }

    /// Where a pointer read out of a field of a local (`copy (_1.0.0)`, a `Box`'s
    /// data pointer, `w.p`) comes from: the operand of the local's single
    /// aggregate definition for a one-level field read, an allocation for any
    /// field of a `Box` local defined once by `Box::new`, unknown otherwise.
    fn field_read_source<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        place: &rustc_public::mir::Place,
    ) -> FieldReadSource<'p> {
        // The data pointer of a `Box` read through a reference to it (`Box::
        // into_raw`'s `(*b).0.0` once inlined): a reference points to a valid
        // `Box`, whose non-dangling pointer is at offset 0 of its allocation.
        //
        // A box of a zero-sized `T` owns no allocation: `Box::new` gives it a
        // dangling pointer, so only a box `Box::from_raw` built answers (its
        // pointer is the one it was built from). Without it a far pointer
        // round-tripped through a `Box<()>` and stepped back drew a free far
        // bit and failed closed where main and Kani prove it
        // (`chc_box_from_raw_provenance_dual.rs`
        // `safe_zst_box_round_trip_far_step_back`).
        if let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice()
            && !rest.is_empty()
            && rest.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            && self.reference_to_box_pointee_size(place.local).is_some()
        {
            let sized = self.reference_to_sized_box(place.local);
            return match self.reference_box_local(defs, place.local) {
                Some(box_local) => match self.box_data_pointer_source(defs, box_local) {
                    FieldReadSource::FreshAllocation if !sized => FieldReadSource::Unknown,
                    source => source,
                },
                None => FieldReadSource::Unknown,
            };
        }
        if !place.projection.iter().all(|p| matches!(p, ProjectionElem::Field(..))) {
            return FieldReadSource::Unknown;
        }
        // A `Box`'s data pointer is the pointer it was built from: a fresh
        // allocation at its offset 0 for `Box::new`, the argument of
        // `Box::from_raw` (whose UB Kani does not report: see the far walk).
        if self.local_is_box(place.local) {
            return self.box_data_pointer_source(defs, place.local);
        }
        if let [ProjectionElem::Field(0, _)] = place.projection.as_slice()
            && let Some(inner) = self.into_raw_with_allocator_box(defs, place.local)
        {
            return self.box_data_pointer_source(defs, inner);
        }
        if self.address_taken_locals().contains(&place.local) {
            return FieldReadSource::Unknown;
        }
        let Some([site]) = defs.get(&place.local).map(Vec::as_slice) else {
            return FieldReadSource::Unknown;
        };
        match *site {
            DefSite::Call(bb) => {
                let TerminatorKind::Call { func, .. } = &self.body.blocks[bb].terminator.kind
                else {
                    return FieldReadSource::Unknown;
                };
                let path =
                    self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func));
                if path.is_some_and(|p| p.contains("boxed::Box") && p.ends_with("::new")) {
                    FieldReadSource::FreshAllocation
                } else {
                    FieldReadSource::Unknown
                }
            }
            DefSite::Stmt(bb, si) => {
                let StatementKind::Assign(_, Rvalue::Aggregate(_, operands)) =
                    &self.body.blocks[bb].statements[si].kind
                else {
                    return FieldReadSource::Unknown;
                };
                match place.projection.as_slice() {
                    [ProjectionElem::Field(index, _)] => operands
                        .get(*index)
                        .map_or(FieldReadSource::Unknown, FieldReadSource::Operand),
                    _ => FieldReadSource::Unknown,
                }
            }
        }
    }

    /// Record a FAIL-CLOSED observation of a far pointer: `cond` holds on the
    /// paths where the value just built reads a far pointer in a way Kani
    /// answers in more than one way (module docs). The block's rule generation
    /// ends those paths in a property that is never certified and cuts every
    /// other rule of the block to the paths where `cond` fails
    /// ([`Self::apply_far_observation_cuts`]). An observation recorded outside a
    /// block's rule generation fails the harness closed.
    pub(in crate::codegen_ay::chc) fn record_far_observation(
        &self,
        cond: Expr,
        what: &'static str,
    ) {
        if self.far_observation_suppressed.get() {
            return;
        }
        let cond = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&cond).unwrap_or(cond);
        if bool_const_value(&cond) == Some(false) {
            return;
        }
        if !self.far_observation_range_active.get() {
            debug!(what, fn_name = %self.fn_name, "CHC: far pointer observation outside a block");
            self.record_sound_fallback_reason("far_pointer_observation_outside_block");
            return;
        }
        debug!(what, fn_name = %self.fn_name, "CHC: fail-closed far pointer observation");
        self.pending_far_observations.borrow_mut().push((cond, FAR_OBSERVATION_MESSAGE, false));
    }

    /// Record a memory-safety violation on the paths where `cond` holds, with
    /// Kani's `message`, for a statement whose effect past the violation the
    /// encoding does not model: the block's rules are cut to the paths where
    /// `cond` fails and copies of them over `cond` reach the violation's
    /// property, which is certifiable ([`Self::apply_far_observation_cuts`]).
    /// Outside a block's rule generation the harness fails closed.
    pub(in crate::codegen_ay::chc) fn record_block_violation(
        &self,
        cond: Expr,
        message: &'static str,
    ) {
        let cond = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&cond).unwrap_or(cond);
        if bool_const_value(&cond) == Some(false) {
            return;
        }
        if !self.far_observation_range_active.get() {
            self.record_sound_fallback_reason("block_violation_outside_block");
            return;
        }
        debug!(message, fn_name = %self.fn_name, "CHC: block violation recorded");
        self.pending_far_observations.borrow_mut().push((cond, message, true));
    }

    /// [`Self::record_block_violation`] for a violation the encoding cannot
    /// decide: its property is never certified (fail-closed).
    pub(in crate::codegen_ay::chc) fn record_uncertified_violation(
        &self,
        cond: Expr,
        message: &'static str,
    ) {
        let cond = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&cond).unwrap_or(cond);
        if bool_const_value(&cond) == Some(false) {
            return;
        }
        if !self.far_observation_range_active.get() {
            self.record_sound_fallback_reason("block_violation_outside_block");
            return;
        }
        debug!(message, fn_name = %self.fn_name, "CHC: uncertified block violation recorded");
        self.pending_far_observations.borrow_mut().push((cond, message, false));
    }

    /// The observation `==` / `!=` of two thin raw pointers makes. Kani compares
    /// a far pointer's object bits and low 48 offset bits under a symbolic count
    /// and the full offsets under a literal one, so the comparison is
    /// fail-closed exactly when one side is far and the two agree on object and
    /// low 48 bits; everywhere else identity equality is every mode's answer.
    /// Before, a symbolic `k == 1 << 48` made `p.wrapping_byte_add(k) == p` a
    /// certified counterexample where Kani proves it, and `k != 0 ->
    /// p.wrapping_byte_add(k) != p` a proof where Kani fails it (first review of
    /// the sixth round: `k48*.rs` `sym_eq_2p48`, `sym_ne_nonzero`).
    ///
    /// `t64` is both pointers' full offsets when the caller knows them
    /// ([`Self::wrapping_operand_t64`]): equal offsets are equal in every mode
    /// (`p.wrapping_byte_add(1 << 48) == p.wrapping_byte_add(k)` for `k == 1 <<
    /// 48`), so only different ones that agree in the low 48 bits disagree.
    pub(in crate::codegen_ay::chc) fn note_ptr_equality(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        t64: Option<(Expr, Expr)>,
    ) {
        if !is_thin_ptr_sort(lhs) || !is_thin_ptr_sort(rhs) || self.int_lift {
            return;
        }
        if !self.may_be_far_observed(lhs) && !self.may_be_far_observed(rhs) {
            return;
        }
        let mut cond = Self::identity_is_far(lhs)
            .or(Self::identity_is_far(rhs))
            .and(Self::object15(lhs).eq(Self::object15(rhs)))
            .and(Self::offset48(lhs).eq(Self::offset48(rhs)));
        if let Some((tl, tr)) = t64 {
            cond = cond.and(tl.eq(tr).not());
        }
        self.record_far_observation(cond, "equality");
    }

    /// [`Self::note_ptr_equality`] for two raw pointers of any width: a wide
    /// pointer's data word is the address compared.
    pub(in crate::codegen_ay::chc) fn note_raw_pointer_equality(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        t64: Option<(Expr, Expr)>,
    ) {
        use crate::codegen_ay::ptr_repr::PtrRepr;
        let data = |e: &Expr| match PtrRepr::classify(e) {
            Some(
                PtrRepr::Thin(loc) | PtrRepr::WidenedThin(loc) | PtrRepr::Fat { data: loc, .. },
            ) => Some(loc.into_expr()),
            None => None,
        };
        if let (Some(l), Some(r)) = (data(lhs), data(rhs)) {
            self.note_ptr_equality(&l, &r, t64);
        }
    }

    /// The observation `offset_from` of two thin pointers makes: Kani's
    /// same-allocation check passes a far pointer whose object and low 48
    /// offset bits are in bounds under a symbolic count and fails it under a
    /// literal one, so it is fail-closed when one side is far, both name one
    /// object and the low 48 bits are equal or within `size_bound` (when the
    /// allocation's size is known; any otherwise).
    pub(in crate::codegen_ay::chc) fn note_ptr_offset_from(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        size_bound: Option<u64>,
    ) {
        if !is_thin_ptr_sort(lhs) || !is_thin_ptr_sort(rhs) || self.int_lift {
            return;
        }
        if !self.may_be_far_observed(lhs) && !self.may_be_far_observed(rhs) {
            return;
        }
        let (off_l, off_r) = (Self::offset48(lhs), Self::offset48(rhs));
        let in_bounds = match size_bound {
            Some(size) => {
                let size = Expr::bitvec_const(size as u128, 48);
                off_l.clone().bvule(size.clone()).and(off_r.clone().bvule(size))
            }
            None => Expr::bool_const(true),
        };
        let cond = Self::identity_is_far(lhs)
            .or(Self::identity_is_far(rhs))
            .and(Self::object15(lhs).eq(Self::object15(rhs)))
            .and(off_l.eq(off_r).or(in_bounds));
        self.record_far_observation(cond, "offset_from");
    }

    /// Start collecting the fail-closed observations of one block's (or one
    /// fragment's) rules; returns the index its rules start at. Observations
    /// pending from outside a block fail the harness closed.
    pub(in crate::codegen_ay::chc) fn begin_far_observation_range(&self) -> usize {
        if !self.pending_far_observations.borrow().is_empty() {
            self.pending_far_observations.borrow_mut().clear();
            self.record_sound_fallback_reason("far_pointer_observation_outside_block");
        }
        self.far_observation_range_active.set(true);
        self.vc.rules.len()
    }

    /// End a block's (or fragment's) rule generation: when it recorded
    /// fail-closed observations ([`Self::record_far_observation`]), every rule
    /// it emitted from `rules_start` on is split in two — the rule restricted
    /// to the paths where no observation is fail-closed, and the same body with
    /// the observation's condition leading to a property whose guard reads an
    /// identified fresh variable, so it is reported but never certified. A path
    /// that reads a far pointer in a way Kani answers in more than one way thus
    /// reaches neither a proof nor a certified counterexample, and every other
    /// path, including one that only might have been far, is exact.
    pub(in crate::codegen_ay::chc) fn apply_far_observation_cuts(
        &mut self,
        rules_start: usize,
        bb_idx: usize,
    ) {
        self.far_observation_range_active.set(false);
        let entries: Vec<(Expr, &'static str, bool)> =
            self.pending_far_observations.borrow_mut().drain(..).collect();
        // One group per property: a message, and whether a counterexample that
        // reaches it may be certified.
        let mut groups: Vec<((&'static str, bool), Expr)> = Vec::new();
        for (cond, message, certified) in entries {
            let kind = (message, certified);
            match groups.iter_mut().find(|(k, _)| *k == kind) {
                Some((_, acc)) => *acc = acc.clone().or(cond),
                None => groups.push((kind, cond)),
            }
        }
        let fold =
            |e: Expr| trust_mc_core::chc_const_prop::eval::try_eval_to_const(&e).unwrap_or(e);
        let groups: Vec<((&'static str, bool), Expr)> = groups
            .into_iter()
            .map(|(k, c)| (k, fold(c)))
            .filter(|(_, c)| bool_const_value(c) != Some(false))
            .collect();
        let Some(cond) = groups.iter().map(|(_, c)| c.clone()).reduce(Expr::or) else { return };
        let cond = fold(cond);
        let end = self.vc.rules.len();
        let mut targets: Vec<(usize, HashSet<String>)> = Vec::new();
        for idx in rules_start..end {
            let rule = &self.vc.rules[idx];
            let Some(relation) = rule.body.relation.as_ref() else { continue };
            if relation.name.as_str().starts_with("error") {
                continue;
            }
            let found = expr_var_names(relation.args.iter().chain(rule.body.constraints.iter()));
            targets.push((idx, found));
        }
        if targets.is_empty() {
            // No rule of the block to attach the property to: dropping it
            // silently lost the violation (a store past its local's end as a
            // function's last statement). The transition generator now emits a
            // return block's rule when a violation is pending; anything else
            // that reaches here fails closed.
            self.record_sound_fallback_reason("block_violation_without_rule");
            return;
        }
        // Each group's property, and the extra guard of its copies: the far
        // observations' reads an identified fresh variable and the property is
        // marked dependent (never certified); a violation's needs none.
        let mut heads: Vec<(Expr, HashSet<String>, RelationApp, Option<Expr>)> = Vec::new();
        for (kind, group_cond) in &groups {
            let group_vars = expr_var_names(std::iter::once(group_cond));
            if !targets.iter().any(|(_, found)| group_vars.iter().all(|v| found.contains(v))) {
                self.record_sound_fallback_reason("block_violation_without_rule");
                continue;
            }
            let (message, certified) = *kind;
            let head = self.register_error_head(
                trust_mc_core::violation::PropertyKind::MemorySafety,
                bb_idx,
                Some(message.to_string()),
            );
            let fired = if !certified {
                self.far_observation_relations.borrow_mut().push(head.name.as_str().to_string());
                let name = chc_fresh_name("__far_observation");
                let var = Havoc::mint_deferred(
                    &*self,
                    sound_havoc::FAR_POINTER_OBSERVATION,
                    name,
                    Sort::bitvec(1),
                );
                Some(var.eq(Expr::bitvec_const(1u128, 1)))
            } else {
                None
            };
            heads.push((group_cond.clone(), group_vars, head, fired));
        }
        let mut specials = Vec::new();
        for (idx, found) in targets {
            let rule = &self.vc.rules[idx];
            let relation = rule.body.relation.clone();
            let head = rule.head.clone();
            let constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
            for (group_cond, group_vars, special_head, fired) in &heads {
                if !group_vars.iter().all(|v| found.contains(v)) {
                    continue;
                }
                let mut special = constraints.clone();
                special.push(group_cond.clone());
                special.extend(fired.clone());
                specials.push(Rule::new(
                    RuleBody::new(relation.clone(), special),
                    special_head.clone(),
                ));
            }
            let mut cut = constraints;
            cut.push(cond.clone().not());
            self.vc.rules[idx] = Rule::new(RuleBody::new(relation, cut), head);
        }
        debug!(bb_idx, specials = specials.len(), "CHC: far pointer observations cut");
        for rule in specials {
            self.vc.add_rule(rule);
        }
    }

    /// Whether `local` is the destination of a cast rustc inserted for its own
    /// null or alignment check ([`Self::rustc_pointer_check_casts`]).
    pub(in crate::codegen_ay::chc) fn is_rustc_check_cast_dest(&self, local: usize) -> bool {
        if !self.far_pointers_possible() {
            return false;
        }
        self.far_check_cast_dests
            .get_or_init(|| self.rustc_pointer_check_casts().into_keys().collect())
            .contains(&local)
    }

    /// The access checks of a dereference of the pointer local `ptr_local`
    /// (value `addr`) that may have been moved by a wrapping step and whose
    /// lane is symbolic, so `heap_access_checks` bounds nothing
    /// (`provenance_deref_bound_checks` resolves stack and raw-allocation
    /// pointers only). The step keeps the pointer's object in its field, so:
    ///
    /// * the access is outside every object unless its lane is its object
    ///   alone — no offset bit at or past 2^32, no [`FAR_BIT`] (certified);
    /// * when the wrapping chain starts at a `Box`'s pointer (`Box::new`, then
    ///   `as_ptr`, `into_raw`, ...), the allocation is the box's pointee, at
    ///   offset 0: the offset plus the access must be within its size
    ///   (certified);
    /// * when it starts at a `Vec`'s buffer, whose extent the byte model does
    ///   not carry, any access that is not definitely outside is a fail-closed
    ///   violation (never certified).
    ///
    /// Before, such a dereference checked neither lane nor bounds:
    /// `*b.as_ptr().wrapping_add(k)` on a `Box<[u8; 4]>` or a `vec![1u8; 4]`
    /// with `k` in `[4, 1000)`, and a `Box` stepped by `1 << 48`, were clean
    /// proofs where Kani reports a pointer outside object bounds (first review
    /// of the sixth round: `k48g.rs`, `k48e.rs`, `k48f.rs`, `r1b.rs`; the same
    /// on main).
    pub(in crate::codegen_ay::chc) fn wrapping_deref_checks(
        &mut self,
        addr: &Expr,
        pointee_ty: Ty,
        ptr_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Vec<Expr> {
        if !is_thin_ptr_sort(addr) || self.int_lift || !self.may_be_far(addr) {
            return Vec::new();
        }
        let Some(access) =
            self.get_type_size(pointee_ty).and_then(|s| u64::try_from(s).ok()).filter(|&s| s > 0)
        else {
            return Vec::new();
        };
        let lane = addr.clone().extract(63, 32);
        let lane = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&lane).unwrap_or(lane);
        if Self::const_obj_id_u32(&lane).is_some() {
            return Vec::new();
        }
        let in_lane = addr.clone().extract(63, 47).eq(Expr::bitvec_const(0u128, 17));
        let mut checks = vec![in_lane.clone()];
        let root = self.wrapping_chain_root_extent(ptr_local);
        debug!(
            ptr_local,
            access,
            extent = ?root.as_ref().map(|(_, e)| match e {
                RootExtent::Bytes(b) => *b as i128,
                RootExtent::Unmodeled => -1,
            }),
            "CHC: wrapping dereference checks"
        );
        match root {
            Some((base, RootExtent::Bytes(size))) => {
                // The base is at the allocation's offset 0; the bound reads it
                // from the base's own value where that is still available, so
                // the solver needs no invariant about the base's offset.
                let base_offset = self
                    .available_local_value(base, modified_locals)
                    .map(|value| value.extract(31, 0).zero_extend(32))
                    .unwrap_or_else(|| Expr::bitvec_const(0u128, 64));
                let offset = addr.clone().extract(31, 0).zero_extend(32);
                let end = offset.bvadd(Expr::bitvec_const(access as u128, 64));
                let limit = base_offset.bvadd(Expr::bitvec_const(size as u128, 64));
                checks.push(end.bvule(limit));
            }
            Some((_, RootExtent::Unmodeled)) => self.record_uncertified_violation(
                in_lane,
                "dereference of a pointer stepped out of a buffer whose extent is not modeled",
            ),
            None => {}
        }
        checks
    }

    /// The extent of the allocation the wrapping chain of `ptr_local` starts
    /// at: through copies, pointer casts and wrapping steps to a base pointer,
    /// then from it back to a `Box` defined once by `Box::new` (its pointee's
    /// size, the base at offset 0) or a `Vec`'s buffer (not modeled). `None`
    /// when the chain has no wrapping step or the base is neither.
    fn wrapping_chain_root_extent(&self, ptr_local: usize) -> Option<(usize, RootExtent)> {
        let defs = self.wrapping_step_defs();
        let mut local = ptr_local;
        let mut stepped = false;
        for _ in 0..16 {
            match defs.get(&local) {
                Some(WrappingDef::Through(src)) => local = *src,
                Some(WrappingDef::Step { base, .. } | WrappingDef::WithAddr { base, .. }) => {
                    stepped = true;
                    local = *base;
                }
                None => break,
            }
        }
        if !stepped {
            return None;
        }
        self.allocation_root_extent(local).map(|extent| (local, extent))
    }

    /// See [`Self::wrapping_chain_root_extent`]: the extent behind a base
    /// pointer local.
    fn allocation_root_extent(&self, start: usize) -> Option<RootExtent> {
        let defs = self.local_def_sites();
        let locals = self.body.locals();
        let mut local = start;
        for _ in 0..16 {
            // A wrapping chain followed through a `Box` round trip
            // (`box_round_trip_def`, `box_round_trip_stmt_def`) can end at the
            // box itself: its extent is its allocation's.
            if self.local_is_box(local) {
                return self.box_local_extent(&defs, local, &[]);
            }
            if self.address_taken_locals().contains(&local) {
                return None;
            }
            let [site] = defs.get(&local)?.as_slice() else { return None };
            debug!(local, ?site, "CHC: allocation root walk");
            let next = match *site {
                DefSite::Stmt(bb, si) => {
                    let StatementKind::Assign(_, rvalue) =
                        &self.body.blocks[bb].statements[si].kind
                    else {
                        return None;
                    };
                    debug!(local, ?rvalue, "CHC: allocation root walk definition");
                    match rvalue {
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                            match place.projection.split_first() {
                                None => place.local,
                                // A field of a `Box` read through a reference to
                                // it (`(*_r).0.0`, `Box::deref`).
                                Some((ProjectionElem::Deref, rest)) => {
                                    let target = self
                                        .reference_box_local(&defs, place.local)
                                        .or_else(|| self.borrowed_local(&defs, place.local))?;
                                    return self.box_local_extent(&defs, target, rest);
                                }
                                // A field of a `Box` local: its data pointer.
                                Some(_) => {
                                    return self.box_local_extent(
                                        &defs,
                                        place.local,
                                        &place.projection,
                                    );
                                }
                            }
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            match place.projection.as_slice() {
                                [ProjectionElem::Deref] => place.local,
                                _ => return None,
                            }
                        }
                        _ => return None,
                    }
                }
                DefSite::Call(bb) => {
                    let TerminatorKind::Call { func, args, .. } =
                        &self.body.blocks[bb].terminator.kind
                    else {
                        return None;
                    };
                    let path = self
                        .resolve_callee_path(func)
                        .or_else(|| self.resolve_fn_def_name(func))?;
                    debug!(local, %path, "CHC: allocation root walk call");
                    let arg0 = args.first()?;
                    // `exchange_malloc(size, align)`: a fresh block of `size`
                    // bytes, the pointer at its offset 0.
                    if path.contains("exchange_malloc") {
                        let size = match arg0 {
                            Operand::Constant(c) => c.const_.eval_target_usize().ok()?,
                            _ => return None,
                        };
                        return (size > 0).then_some(RootExtent::Bytes(size));
                    }
                    if path.contains("vec::Vec")
                        && ["::as_ptr", "::as_mut_ptr", "::as_non_null"]
                            .iter()
                            .any(|m| path.ends_with(m))
                    {
                        return Some(
                            self.vec_literal_buffer_extent(&defs, arg0, bb)
                                .unwrap_or(RootExtent::Unmodeled),
                        );
                    }
                    if path.contains("boxed::Box")
                        && ["::into_raw", "::leak", "::as_ptr", "::as_mut_ptr"]
                            .iter()
                            .any(|m| path.ends_with(m))
                    {
                        let box_local = self.box_accessor_box_local(&defs, &path, arg0)?;
                        return self.box_local_extent(&defs, box_local, &[]);
                    }
                    let place_pointer =
                        ["::as_ptr", "::as_mut_ptr"].iter().any(|m| path.ends_with(m))
                            && arg0.ty(locals).is_ok_and(ty_points_to_array_or_slice);
                    if !place_pointer {
                        return None;
                    }
                    operand_local(arg0)?
                }
            };
            local = next;
        }
        None
    }

    /// The extent of the buffer of the `Vec` a `Vec::as_ptr(&v)` reads, when `v`
    /// is a `vec![a, b, ..]` literal not mutated before the call: `v`'s one
    /// definition is `<[T]>::into_vec` of a `Box<[T; N]>` over its own
    /// allocation (`Box::new`, or the macro's `exchange_malloc` block) and
    /// unsized, and no block that can reach the `as_ptr` call (the call's own
    /// block included) borrows `v`'s storage mutably or by raw address or moves
    /// it, so no push, reserve or shrink can have moved its buffer by then. A
    /// later change is not this function's business, and the heap checks do NOT
    /// report a read through the stale pointer: an access after a possible change
    /// of the `Vec` fails the harness closed instead
    /// (heap/vec_buffer_access.rs; second review of round 9, `r2_vec.rs` v02,
    /// v03, v09, v12, which this function had reopened). The buffer is then that
    /// box's allocation, the pointer at its offset 0, of `N * size_of::<T>()`
    /// bytes. Without it a
    /// wrapped dereference of any `Vec` buffer failed closed:
    /// `vec![1u16, 2].as_ptr().wrapping_add(1)` read `2` where Kani proves it
    /// (`int_to_ptr_exposed_dual.rs` `safe_vec_wrapping_add_in_bounds`, a
    /// measured cost of the sixth round).
    fn vec_literal_buffer_extent(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        arg0: &Operand,
        call_bb: usize,
    ) -> Option<RootExtent> {
        use rustc_public::mir::PointerCoercion;
        let vec_local = self.borrowed_local(defs, operand_local(arg0)?)?;
        if self.local_mutated_before(vec_local, call_bb) {
            return None;
        }
        let [DefSite::Call(bb)] = defs.get(&vec_local)?.as_slice() else { return None };
        let TerminatorKind::Call { func, args, .. } = &self.body.blocks[*bb].terminator.kind else {
            return None;
        };
        let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
        if !path.ends_with("::into_vec") {
            return None;
        }
        let [boxed_slice] = args.as_slice() else { return None };
        let slice_local = operand_local(boxed_slice)?;
        if self.address_taken_locals().contains(&slice_local) {
            return None;
        }
        let [DefSite::Stmt(sbb, si)] = defs.get(&slice_local)?.as_slice() else { return None };
        let StatementKind::Assign(
            _,
            Rvalue::Cast(
                CastKind::PointerCoercion(PointerCoercion::Unsize),
                Operand::Copy(src) | Operand::Move(src),
                _,
            ),
        ) = &self.body.blocks[*sbb].statements[*si].kind
        else {
            return None;
        };
        if !src.projection.is_empty() || !self.local_is_box(src.local) {
            return None;
        }
        let ty = self.resolve_body_ty(self.body.locals().get(src.local)?.ty);
        let TyKind::RigidTy(RigidTy::Adt(_, box_args)) = ty.kind() else { return None };
        let array = box_args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(t) => Some(*t),
            _ => None,
        })?;
        if !matches!(self.resolve_body_ty(array).kind(), TyKind::RigidTy(RigidTy::Array(..))) {
            return None;
        }
        // The box's own allocation: `Box::new`, or the `exchange_malloc` block
        // the `vec!` macro's inlined box is built over.
        let extent = self.box_local_extent(defs, src.local, &[])?;
        debug!(
            vec_local,
            src = src.local,
            size = match extent {
                RootExtent::Bytes(b) => b as i128,
                RootExtent::Unmodeled => -1,
            },
            "CHC: wrapped Vec buffer extent from its literal"
        );
        matches!(extent, RootExtent::Bytes(_)).then_some(extent)
    }

    /// Whether a block that can reach block `target` (`target` itself
    /// included: its statements precede its terminator) borrows `local`'s own
    /// storage mutably or by raw address, or moves it.
    fn local_mutated_before(&self, local: usize, target: usize) -> bool {
        use rustc_public::mir::BorrowKind;
        let blocks = &self.body.blocks;
        // Blocks that can reach `target`.
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); blocks.len()];
        for (bb, block) in blocks.iter().enumerate() {
            for succ in block.terminator.successors() {
                if succ < blocks.len() {
                    preds[succ].push(bb);
                }
            }
        }
        let mut reaches = vec![false; blocks.len()];
        let mut work = vec![target];
        while let Some(bb) = work.pop() {
            if bb >= blocks.len() || reaches[bb] {
                continue;
            }
            reaches[bb] = true;
            work.extend(preds[bb].iter().copied());
        }
        let own = |place: &rustc_public::mir::Place| {
            place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        };
        let moves = |op: &Operand| matches!(op, Operand::Move(p) if p.local == local);
        for (bb, block) in blocks.iter().enumerate() {
            if !reaches[bb] {
                continue;
            }
            for stmt in &block.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
                let mutating = match rvalue {
                    Rvalue::Ref(_, kind, place) => {
                        own(place) && !matches!(kind, BorrowKind::Shared | BorrowKind::Fake(_))
                    }
                    Rvalue::AddressOf(_, place) => own(place),
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => moves(op),
                    Rvalue::Aggregate(_, ops) => ops.iter().any(moves),
                    _ => false,
                };
                if mutating {
                    return true;
                }
            }
            if bb != target
                && let TerminatorKind::Call { args, .. } = &block.terminator.kind
                && args.iter().any(moves)
            {
                return true;
            }
        }
        false
    }

    /// The local a reference local borrows whole: through single definitions
    /// `_r = &b`, `_r = &raw b`, reborrows `_r = &(*_s)` and copies.
    fn borrowed_local(&self, defs: &HashMap<usize, Vec<DefSite>>, start: usize) -> Option<usize> {
        let mut local = start;
        for _ in 0..8 {
            let [DefSite::Stmt(bb, si)] = defs.get(&local)?.as_slice() else { return None };
            let StatementKind::Assign(_, rvalue) = &self.body.blocks[*bb].statements[*si].kind
            else {
                return None;
            };
            match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                    match place.projection.as_slice() {
                        [] => return Some(place.local),
                        [ProjectionElem::Deref] => local = place.local,
                        _ => return None,
                    }
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                    if place.projection.is_empty() =>
                {
                    local = place.local
                }
                _ => return None,
            }
        }
        None
    }

    /// The place a reference local points at, as a local and a projection:
    /// through single definitions by whole copies and pointer casts, borrows of
    /// a place (`&mut x.f`) and reborrows through another such reference
    /// (`&mut (*r).f` names the place `r` points at, extended by `.f`).
    fn reference_place(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        start: usize,
        depth: u32,
    ) -> Option<(usize, Vec<ProjectionElem>)> {
        if depth > 8 {
            return None;
        }
        let mut local = start;
        for _ in 0..12 {
            if self.address_taken_locals().contains(&local) {
                return None;
            }
            let [DefSite::Stmt(bb, si)] = defs.get(&local)?.as_slice() else { return None };
            let StatementKind::Assign(_, rvalue) = &self.body.blocks[*bb].statements[*si].kind
            else {
                return None;
            };
            match rvalue {
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                    return match place.projection.split_first() {
                        Some((ProjectionElem::Deref, rest)) => {
                            if rest.iter().any(|p| !matches!(p, ProjectionElem::Field(..))) {
                                return None;
                            }
                            let (base, mut proj) =
                                self.reference_place(defs, place.local, depth + 1)?;
                            proj.extend(rest.iter().cloned());
                            Some((base, proj))
                        }
                        _ if place
                            .projection
                            .iter()
                            .all(|p| matches!(p, ProjectionElem::Field(..))) =>
                        {
                            Some((place.local, place.projection.clone()))
                        }
                        _ => None,
                    };
                }
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                    if p.projection.is_empty() =>
                {
                    local = p.local
                }
                _ => return None,
            }
        }
        None
    }

    /// The `Box` local a reference points at whole: a `Box` local itself, or
    /// the `Box` a `ManuallyDrop<Box<T>>` local holds (its field 0) when that
    /// local's one definition is `ManuallyDrop::new(b)`, which `Box::into_raw`
    /// inlines to (`let mut m = ManuallyDrop::new(b); &raw mut **(&mut m).0`).
    fn reference_box_local(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        ref_local: usize,
    ) -> Option<usize> {
        let (base, proj) = self.reference_place(defs, ref_local, 0)?;
        match proj.as_slice() {
            [] if self.local_is_box(base) => Some(base),
            [ProjectionElem::Field(0, field_ty)]
                if matches!(self.resolve_body_ty(*field_ty).kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                    if matches!(def.name().as_str(), "std::boxed::Box" | "alloc::boxed::Box")) =>
            {
                if self.address_taken_locals().contains(&base) && !self.borrows_only_read(base) {
                    return None;
                }
                let [DefSite::Call(bb)] = defs.get(&base)?.as_slice() else { return None };
                let TerminatorKind::Call { func, args, .. } =
                    &self.body.blocks[*bb].terminator.kind
                else {
                    return None;
                };
                let path =
                    self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
                if !(path.contains("ManuallyDrop") && path.ends_with("::new")) {
                    return None;
                }
                let inner = operand_local(args.first()?)?;
                self.local_is_box(inner).then_some(inner)
            }
            _ => None,
        }
    }

    /// Whether every reference to `base`'s storage the body takes is only read
    /// through: the references (borrows of `base` or of a field of it, their
    /// whole copies, moves and pointer casts, and borrows of a place behind
    /// one) are never written through, never handed to a call but the drop
    /// glue and never stored into a place, so no write reaches `base` but its
    /// own definitions before it is dropped.
    fn borrows_only_read(&self, base: usize) -> bool {
        let mut refs: HashSet<usize> = HashSet::new();
        loop {
            let before = refs.len();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                    let derived = match rvalue {
                        // A reference to a zero-sized part (a `Box`'s allocator,
                        // borrowed by the inlined drop glue's `deallocate`) writes
                        // no byte.
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                            if place
                                .ty(self.body.locals())
                                .ok()
                                .and_then(|ty| self.get_type_size(ty))
                                == Some(0) =>
                        {
                            false
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            (place.local == base
                                && !matches!(place.projection.first(), Some(ProjectionElem::Deref)))
                                || (refs.contains(&place.local)
                                    && matches!(
                                        place.projection.first(),
                                        Some(ProjectionElem::Deref)
                                    ))
                        }
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                        | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => {
                            p.projection.is_empty() && refs.contains(&p.local)
                        }
                        _ => false,
                    };
                    if derived {
                        if !lhs.projection.is_empty() {
                            return false;
                        }
                        refs.insert(lhs.local);
                    }
                }
            }
            if refs.len() == before {
                break;
            }
        }
        let mentions_ref = |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if refs.contains(&p.local));
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                if refs.contains(&lhs.local)
                    && matches!(lhs.projection.first(), Some(ProjectionElem::Deref))
                {
                    return false;
                }
                // A reference stored into an aggregate escapes the walk.
                if let Rvalue::Aggregate(_, ops) = rvalue
                    && ops.iter().any(mentions_ref)
                {
                    return false;
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    // The drop glue ends the value's life; a later use of it is
                    // a use-after-free the heap checks report.
                    let drop_glue = self
                        .resolve_callee_path(func)
                        .or_else(|| self.resolve_fn_def_name(func))
                        .is_some_and(|path| path.contains("drop_in_place"));
                    if (args.iter().any(mentions_ref) && !drop_glue)
                        || (refs.contains(&destination.local)
                            && matches!(
                                destination.projection.first(),
                                Some(ProjectionElem::Deref)
                            ))
                    {
                        return false;
                    }
                }
                TerminatorKind::Drop { place, .. } if refs.contains(&place.local) => return false,
                _ => {}
            }
        }
        true
    }

    /// The raw pointer operand a `Unique` / `NonNull` operand wraps: through
    /// whole copies, `Unique::new_unchecked` / `NonNull::new_unchecked` /
    /// `Unique::from` / `NonNull::from` of a raw pointer, the wrappers'
    /// aggregates (`Unique(NonNull(p), PhantomData)`) and pointer casts or
    /// transmutes from a raw pointer.
    fn wrapper_raw_pointer<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        op: &'p Operand,
        depth: u32,
    ) -> Option<&'p Operand> {
        if depth > 8 {
            return None;
        }
        let locals = self.body.locals();
        if op.ty(locals).is_ok_and(ty_is_raw_ptr) {
            return Some(op);
        }
        let local = operand_local(op)?;
        if self.address_taken_locals().contains(&local) {
            return None;
        }
        let [site] = defs.get(&local)?.as_slice() else { return None };
        match *site {
            DefSite::Stmt(bb, si) => {
                let StatementKind::Assign(_, rvalue) = &self.body.blocks[bb].statements[si].kind
                else {
                    return None;
                };
                match rvalue {
                    Rvalue::Use(inner, ..) | Rvalue::Cast(_, inner, _) => {
                        self.wrapper_raw_pointer(defs, inner, depth + 1)
                    }
                    Rvalue::Aggregate(AggregateKind::Adt(def, ..), ops)
                        if matches!(def.trimmed_name().as_str(), "Unique" | "NonNull") =>
                    {
                        self.wrapper_raw_pointer(defs, ops.first()?, depth + 1)
                    }
                    _ => None,
                }
            }
            DefSite::Call(bb) => {
                let TerminatorKind::Call { func, args, .. } = &self.body.blocks[bb].terminator.kind
                else {
                    return None;
                };
                let path =
                    self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
                let wrapper = path.contains("ptr::Unique")
                    || path.contains("ptr::NonNull")
                    || path.contains("unique::Unique")
                    || path.contains("non_null::NonNull");
                if !(wrapper && ["::new_unchecked", "::from"].iter().any(|m| path.ends_with(m))) {
                    return None;
                }
                let [arg] = args.as_slice() else { return None };
                self.wrapper_raw_pointer(defs, arg, depth + 1)
            }
        }
    }

    /// The `Box` `Box::into_raw_with_allocator(b)` took, when that call is the
    /// one definition of the pair local `pair` (what `Box::leak` inlines to).
    fn into_raw_with_allocator_box(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        pair: usize,
    ) -> Option<usize> {
        if self.address_taken_locals().contains(&pair) {
            return None;
        }
        let [DefSite::Call(bb)] = defs.get(&pair)?.as_slice() else { return None };
        let TerminatorKind::Call { func, args, .. } = &self.body.blocks[*bb].terminator.kind else {
            return None;
        };
        let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
        if !(path.contains("boxed::Box") && path.ends_with("::into_raw_with_allocator")) {
            return None;
        }
        let inner = operand_local(args.first()?)?;
        self.local_is_box(inner).then_some(inner)
    }

    /// Fail the harness closed when a `Box` is built by `Box::from_raw` of a
    /// pointer into a stack local (`Box::from_raw(a.as_mut_ptr())`), which is
    /// undefined behavior Kani does not report. The encoder reads through such a
    /// box from typed memory the local's value never reached, so a read of the
    /// array through it returned anything: `*Box::into_raw(b) == 7` for `a =
    /// [7u8; 16]` was a certified counterexample where Kani proves it (review of
    /// fix/chc-false-certificates round 1, `rv_box_bound.rs`
    /// `b02_safe_stack16_as_box_u8_step`, the same on main).
    ///
    /// The definition walk ([`Self::pointer_roots_at_stack_place`]) follows
    /// copies, casts, borrows, `as_ptr`, in-bounds steps, fields of aggregate
    /// locals and `Option::unwrap` of a `Some` aggregate. The encoder's own
    /// points-to metadata answers too: a raw pointer `ref_targets` takes to a
    /// local's own storage points into that local whatever route it took
    /// there. Without both, a stack pointer carried to `Box::from_raw`
    /// through a tuple or struct field or `Option::unwrap` gave certified
    /// counterexamples where Kani proves the program (second review of round
    /// 9, `r2_boxstack.rs` t01, t02, t04, t08, t09, t11, `r2_boxsrc.rs` s01):
    /// the slice `as_mut_ptr` stub gives the pointer no address of its own, so
    /// once the box hop drops the metadata the read through the box read a
    /// memory cell at an unconstrained address.
    pub(in crate::codegen_ay::chc) fn book_box_from_raw_of_stack_pointer(&self) {
        let defs = self.local_def_sites();
        for local in 0..self.body.locals().len() {
            if !self.local_is_box(local) {
                continue;
            }
            if let BoxPointerSource::FromRaw(raw) = self.box_pointer_source(&defs, local)
                && (self.pointer_roots_at_stack_place(&defs, raw)
                    || self.pointer_targets_stack_storage(raw))
            {
                debug!(fn_name = %self.fn_name, local, "CHC: Box::from_raw of a pointer into a stack local (fail closed)");
                self.record_sound_fallback_reason("box_from_raw_of_stack_pointer");
                return;
            }
        }
    }

    /// Whether the encoder's points-to metadata takes the pointer operand `op`
    /// to a local's own storage (a `ref_targets` entry whose place does not
    /// start with a dereference). A `Vec` buffer pointer's entry names the
    /// `Vec` local, not the buffer: `Box::from_raw(v.as_mut_ptr())` was booked
    /// as a box over stack storage (third review of round 10,
    /// `r3_box.rs` `b09_safe_from_raw_of_vec_buffer`).
    fn pointer_targets_stack_storage(&self, op: &Operand) -> bool {
        operand_local(op).is_some_and(|local| {
            self.ref_resolution.ref_targets.get(&local).is_some_and(|target| {
                !matches!(target.projections.first(), Some(ProjectionElem::Deref))
                    && target.local < self.body.locals().len()
            }) && !self.pointer_addresses_vec_buffer(local)
        })
    }

    /// Whether the pointer operand `op` provably points into a stack local:
    /// through single definitions by whole copies and casts, reborrows
    /// (`&raw mut (*p)`, `&mut (*p).f`), slice and array `as_ptr` /
    /// `as_mut_ptr`, in-bounds steps and pointer casts, to a borrow of a local's
    /// own storage.
    fn pointer_roots_at_stack_place(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        op: &Operand,
    ) -> bool {
        let Some(mut local) = operand_local(op) else { return false };
        for _ in 0..16 {
            let Some([site]) = defs.get(&local).map(Vec::as_slice) else { return false };
            match *site {
                DefSite::Stmt(bb, si) => {
                    let StatementKind::Assign(_, rvalue) =
                        &self.body.blocks[bb].statements[si].kind
                    else {
                        return false;
                    };
                    match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                        | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                            if p.projection.is_empty() =>
                        {
                            local = p.local
                        }
                        // A field of a tuple, struct or enum local built once
                        // by an aggregate (`(a.as_mut_ptr(),).0`).
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) => {
                            let Some(next) =
                                self.aggregate_field_operand(defs, p).and_then(operand_local)
                            else {
                                return false;
                            };
                            local = next;
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            match place.projection.first() {
                                None => return true,
                                Some(ProjectionElem::Deref) => local = place.local,
                                Some(_) => {
                                    return !place
                                        .projection
                                        .iter()
                                        .any(|p| matches!(p, ProjectionElem::Deref));
                                }
                            }
                        }
                        _ => return false,
                    }
                }
                DefSite::Call(bb) => {
                    let TerminatorKind::Call { func, args, .. } =
                        &self.body.blocks[bb].terminator.kind
                    else {
                        return false;
                    };
                    let Some(path) =
                        self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
                    else {
                        return false;
                    };
                    let Some(arg0) = args.first() else { return false };
                    // `Some(p).unwrap()`: the payload `p`.
                    if let Some(payload) = self.unwrapped_payload_operand(defs, &path, args) {
                        let Some(next) = operand_local(payload) else { return false };
                        local = next;
                        continue;
                    }
                    let place_pointer =
                        ["::as_ptr", "::as_mut_ptr"].iter().any(|m| path.ends_with(m))
                            && arg0.ty(self.body.locals()).is_ok_and(ty_points_to_array_or_slice);
                    let step = (path.contains("const_ptr") || path.contains("mut_ptr"))
                        && [
                            "::add",
                            "::sub",
                            "::offset",
                            "::byte_add",
                            "::byte_sub",
                            "::byte_offset",
                            "::cast",
                            "::cast_mut",
                            "::cast_const",
                        ]
                        .iter()
                        .any(|m| path.ends_with(m));
                    if !(place_pointer || step) {
                        return false;
                    }
                    let Some(next) = operand_local(arg0) else { return false };
                    local = next;
                }
            }
        }
        false
    }

    /// Whether `local` is a `Box`.
    fn local_is_box(&self, local: usize) -> bool {
        self.body.locals().get(local).is_some_and(|decl| {
            matches!(self.resolve_body_ty(decl.ty).kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                if matches!(def.name().as_str(), "std::boxed::Box" | "alloc::boxed::Box"))
        })
    }

    /// [`Self::field_read_source`] for a field read of the `Box` local
    /// `box_local`: its data pointer.
    fn box_data_pointer_source<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        box_local: usize,
    ) -> FieldReadSource<'p> {
        match self.box_pointer_source(defs, box_local) {
            BoxPointerSource::Allocation => FieldReadSource::FreshAllocation,
            BoxPointerSource::FromRaw(raw) => FieldReadSource::Operand(raw),
            BoxPointerSource::Unknown => FieldReadSource::Unknown,
        }
    }

    /// The `Box` local a `Box` pointer accessor call reads (`into_raw(b)`,
    /// `leak(b)`, `into_non_null(b)` take the box, `as_ptr(&b)` /
    /// `as_mut_ptr(&mut b)` a reference to it), when `path` is one.
    fn box_accessor_box_local(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        path: &str,
        arg0: &Operand,
    ) -> Option<usize> {
        if !path.contains("boxed::Box") {
            return None;
        }
        let by_value =
            ["::into_raw", "::leak", "::into_non_null"].iter().any(|m| path.ends_with(m));
        let by_ref = ["::as_ptr", "::as_mut_ptr"].iter().any(|m| path.ends_with(m));
        let local = operand_local(arg0)?;
        if by_value && self.local_is_box(local) {
            Some(local)
        } else if by_ref {
            self.reference_box_local(defs, local)
        } else {
            None
        }
    }

    /// Whether the storage of `local` is written other than whole: a field,
    /// element or downcast assignment, a call returning into a part of it, a
    /// `SetDiscriminant`, or a drop of a part. [`Self::local_def_sites`] lists
    /// whole definitions only.
    fn local_written_in_part(&self, local: usize) -> bool {
        self.local_written_in_part_touching(local, None)
    }

    /// [`Self::local_written_in_part`], where a write to a field of a struct
    /// or tuple `local` other than `field` (`g.n = 5` beside `g.b`) does not
    /// count: it leaves `field` as the aggregate built it. A box stored in a
    /// struct whose other field was written failed closed where Kani and main
    /// prove the stepped read through it (third review of round 10 of
    /// fix/chc-false-certificates, `r3_box2.rs`
    /// `f08_safe_box_struct_other_field_written`).
    fn local_written_in_part_touching(&self, local: usize, field: Option<usize>) -> bool {
        let part = |place: &rustc_public::mir::Place| {
            place.local == local
                && !place.projection.is_empty()
                && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                && !matches!((place.projection.first(), field),
                    (Some(ProjectionElem::Field(written, _)), Some(kept)) if *written != kept)
        };
        self.body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| match &stmt.kind {
                StatementKind::Assign(place, _) => part(place),
                StatementKind::SetDiscriminant { place, .. } => place.local == local,
                _ => false,
            }) || match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } => part(destination),
                TerminatorKind::Drop { place, .. } => part(place),
                _ => false,
            }
        })
    }

    /// The operand a field read `place` of an aggregate local yields: `h.i` of
    /// a tuple or struct `h`, or `(h as V).i` of an enum `h`, whose one
    /// definition is the aggregate that built it (of variant `V`), when `h` is
    /// written neither in part nor through a borrow that may write.
    fn aggregate_field_operand<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        place: &rustc_public::mir::Place,
    ) -> Option<&'p Operand> {
        let (variant, index) = match place.projection.as_slice() {
            [ProjectionElem::Field(index, _)] => (None, *index),
            [ProjectionElem::Downcast(variant), ProjectionElem::Field(index, _)] => {
                (Some(crate::rustc_public_bridge::IndexedVal::to_index(variant)), *index)
            }
            _ => return None,
        };
        let (kind, operands) = self.aggregate_definition_through_copies(
            defs,
            place.local,
            variant.is_none().then_some(index),
        )?;
        let matches_kind = match (kind, variant) {
            (AggregateKind::Tuple, None) => true,
            (AggregateKind::Adt(def, built, _, _, None), None) => {
                def.kind() == rustc_public::ty::AdtKind::Struct
                    && crate::rustc_public_bridge::IndexedVal::to_index(built) == 0
            }
            (AggregateKind::Adt(def, built, _, _, None), Some(read)) => {
                def.kind() == rustc_public::ty::AdtKind::Enum
                    && crate::rustc_public_bridge::IndexedVal::to_index(built) == read
            }
            _ => false,
        };
        if !matches_kind {
            return None;
        }
        operands.get(index)
    }

    /// The aggregate that built the local `holder` whole: its one definition,
    /// through whole copies and moves of it (an inlined `Result::unwrap` reads
    /// `(r2 as Ok).0` of `r2 = r`), when no local on the way is written in part
    /// or through a borrow that may write.
    fn aggregate_definition_through_copies<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        holder: usize,
        field: Option<usize>,
    ) -> Option<(&'p AggregateKind, &'p [Operand])> {
        let mut holder = holder;
        for _ in 0..8 {
            if (self.address_taken_locals().contains(&holder) && !self.borrows_only_read(holder))
                || self.local_written_in_part_touching(holder, field)
            {
                return None;
            }
            let [DefSite::Stmt(bb, si)] = defs.get(&holder)?.as_slice() else { return None };
            match &self.body.blocks[*bb].statements[*si].kind {
                StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) => {
                    return Some((kind, operands.as_slice()));
                }
                StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..),
                ) if src.projection.is_empty() => holder = src.local,
                _ => return None,
            }
        }
        None
    }

    /// The payload operand `Option::unwrap` / `expect` / `unwrap_unchecked`
    /// (or `Result`'s `unwrap` / `expect` of `Ok`) returns, when `path` is one
    /// of them and its argument is a local built once by `Some(op)` (`Ok(op)`):
    /// `op`, the only value the call can return without panicking.
    fn unwrapped_payload_operand<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        path: &str,
        args: &'p [Operand],
    ) -> Option<&'p Operand> {
        let method = path.rsplit("::").next()?;
        let method = method.split('<').next()?;
        let payload_variant = if path.contains("option::Option") {
            if !matches!(method, "unwrap" | "expect" | "unwrap_unchecked") {
                return None;
            }
            "Some"
        } else if path.contains("result::Result") {
            if !matches!(method, "unwrap" | "expect" | "unwrap_unchecked") {
                return None;
            }
            "Ok"
        } else {
            return None;
        };
        let holder = operand_local(args.first()?)?;
        let (AggregateKind::Adt(def, built, _, _, None), operands) =
            self.aggregate_definition_through_copies(defs, holder, None)?
        else {
            return None;
        };
        let variant = def
            .variants()
            .into_iter()
            .nth(crate::rustc_public_bridge::IndexedVal::to_index(built))?;
        if variant.name() != payload_variant {
            return None;
        }
        match operands {
            [payload] => Some(payload),
            _ => None,
        }
    }

    /// Where the data pointer of the `Box` local `box_local` comes from:
    /// through single definitions by whole moves and copies, field moves out
    /// of an aggregate local ([`Self::aggregate_field_operand`]) and the
    /// unwrapping of a `Some` / `Ok` aggregate
    /// ([`Self::unwrapped_payload_operand`]), to `Box::new` or the allocation
    /// `ShallowInitBox` initializes (a fresh allocation), or to `Box::from_raw`
    /// / `from_raw_in` / `from_non_null` (their pointer argument). Anything
    /// else, and a box whose storage is borrowed mutably or by raw address, is
    /// unknown. A valid box moved out of an `Option` or a struct field, then
    /// stepped by a wrapping offset and dereferenced in bounds, failed closed
    /// where main and Kani prove it (second review of round 9,
    /// `r2_boxsrc.rs` `p05_safe_option_unwrap_step`,
    /// `p06_safe_struct_field_box_step`).
    ///
    /// A box local with several definitions (reassigned, or chosen on a path)
    /// is a fresh allocation when every definition is one, and so is a box
    /// moved out of a field of a holder every whole definition of which built
    /// that field from one: all of them allocate the local's one pointee
    /// type. Such boxes failed closed where Kani and main prove the stepped
    /// read through them (third review of round 10, `r3_box2.rs`
    /// `f01_safe_box_reassigned`, `f02_safe_box_chosen_on_path`, `r3_box.rs`
    /// `b06_safe_field_after_whole_reassign`).
    fn box_pointer_source<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        box_local: usize,
    ) -> BoxPointerSource<'p> {
        self.box_pointer_source_fuel(defs, box_local, 16)
    }

    /// Every definition's source a fresh allocation: one. Anything else
    /// (a `Box::from_raw` on one path, an unknown source) is unknown.
    fn merged_box_sources<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        locals: &[usize],
        fuel: usize,
    ) -> BoxPointerSource<'p> {
        if locals.is_empty() || fuel == 0 {
            return BoxPointerSource::Unknown;
        }
        for &local in locals {
            if !matches!(
                self.box_pointer_source_fuel(defs, local, fuel),
                BoxPointerSource::Allocation
            ) {
                return BoxPointerSource::Unknown;
            }
        }
        BoxPointerSource::Allocation
    }

    /// The field operands every whole definition of the struct or tuple
    /// local `place.local` stores at `place`'s field, when each definition is
    /// an aggregate of that kind (directly, not through copies) and the local
    /// is written neither in that field nor through a borrow that may write.
    fn aggregate_field_operands_of_every_definition<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        place: &rustc_public::mir::Place,
    ) -> Option<Vec<&'p Operand>> {
        let [ProjectionElem::Field(index, _)] = place.projection.as_slice() else { return None };
        let holder = place.local;
        if (self.address_taken_locals().contains(&holder) && !self.borrows_only_read(holder))
            || self.local_written_in_part_touching(holder, Some(*index))
        {
            return None;
        }
        let sites = defs.get(&holder)?;
        let mut out = Vec::new();
        for site in sites {
            let DefSite::Stmt(bb, si) = *site else { return None };
            let (kind, operands) = match &self.body.blocks[bb].statements[si].kind {
                StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) => {
                    (kind, operands.as_slice())
                }
                // `h = move t` of a `t` built once by an aggregate (MIR builds
                // the new value aside before it drops the old one).
                StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..),
                ) if src.projection.is_empty() => {
                    self.aggregate_definition_through_copies(defs, src.local, Some(*index))?
                }
                _ => return None,
            };
            let struct_or_tuple = match kind {
                AggregateKind::Tuple => true,
                AggregateKind::Adt(def, built, _, _, None) => {
                    def.kind() == rustc_public::ty::AdtKind::Struct
                        && crate::rustc_public_bridge::IndexedVal::to_index(built) == 0
                }
                _ => false,
            };
            if !struct_or_tuple {
                return None;
            }
            out.push(operands.get(*index)?);
        }
        Some(out)
    }

    fn box_pointer_source_fuel<'p>(
        &'p self,
        defs: &HashMap<usize, Vec<DefSite>>,
        box_local: usize,
        fuel: usize,
    ) -> BoxPointerSource<'p> {
        let mut local = box_local;
        for step in 0..fuel {
            // A borrow of the box's storage may write it, except one only read
            // through or handed to the drop glue (`drop_in_place(&raw mut b)`).
            if (self.address_taken_locals().contains(&local) && !self.borrows_only_read(local))
                || self.local_written_in_part(local)
            {
                return BoxPointerSource::Unknown;
            }
            let Some(sites) = defs.get(&local).map(Vec::as_slice) else {
                return BoxPointerSource::Unknown;
            };
            let rest = fuel - step - 1;
            if sites.len() > 1 {
                // Each definition on its own: a whole copy or move of another
                // box local, or a call / aggregate that names the source.
                let mut sources = Vec::new();
                for site in sites {
                    match *site {
                        DefSite::Stmt(bb, si) => match &self.body.blocks[bb].statements[si].kind {
                            StatementKind::Assign(
                                _,
                                Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..),
                            ) if p.projection.is_empty() && self.local_is_box(p.local) => {
                                sources.push(p.local)
                            }
                            #[cfg(not(trust_toolchain))]
                            StatementKind::Assign(_, Rvalue::ShallowInitBox(..)) => {}
                            _ => return BoxPointerSource::Unknown,
                        },
                        DefSite::Call(bb) => {
                            let TerminatorKind::Call { func, .. } =
                                &self.body.blocks[bb].terminator.kind
                            else {
                                return BoxPointerSource::Unknown;
                            };
                            let fresh = self
                                .resolve_callee_path(func)
                                .or_else(|| self.resolve_fn_def_name(func))
                                .is_some_and(|path| {
                                    path.contains("boxed::Box") && path.ends_with("::new")
                                });
                            if !fresh {
                                return BoxPointerSource::Unknown;
                            }
                        }
                    }
                }
                return if sources.is_empty() {
                    BoxPointerSource::Allocation
                } else {
                    self.merged_box_sources(defs, &sources, rest)
                };
            }
            let [site] = sites else {
                return BoxPointerSource::Unknown;
            };
            match *site {
                DefSite::Stmt(bb, si) => {
                    let StatementKind::Assign(_, rvalue) =
                        &self.body.blocks[bb].statements[si].kind
                    else {
                        return BoxPointerSource::Unknown;
                    };
                    match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                            if p.projection.is_empty() && self.local_is_box(p.local) =>
                        {
                            local = p.local
                        }
                        // A box moved out of a field of an aggregate local
                        // (`let b = h.b` of `h = Holder { b: Box::new(..) }`, or
                        // an inlined `Option::unwrap`'s `(o as Some).0`): the
                        // operand the aggregate stored there.
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                            if !p.projection.is_empty() =>
                        {
                            match self
                                .aggregate_field_operand(defs, p)
                                .and_then(operand_local)
                                .filter(|&l| self.local_is_box(l))
                            {
                                Some(inner) => local = inner,
                                // A holder rebuilt whole (`h = H { b: Box::new(..) }`
                                // twice): every definition's field.
                                None => {
                                    let Some(inners) = self
                                        .aggregate_field_operands_of_every_definition(defs, p)
                                        .and_then(|ops| {
                                            ops.into_iter()
                                                .map(|op| {
                                                    operand_local(op)
                                                        .filter(|&l| self.local_is_box(l))
                                                })
                                                .collect::<Option<Vec<usize>>>()
                                        })
                                    else {
                                        return BoxPointerSource::Unknown;
                                    };
                                    return self.merged_box_sources(defs, &inners, rest);
                                }
                            }
                        }
                        #[cfg(not(trust_toolchain))]
                        Rvalue::ShallowInitBox(..) => return BoxPointerSource::Allocation,
                        // `Box(Unique::new_unchecked(raw), alloc)`: `Box::from_raw`
                        // inlined.
                        Rvalue::Aggregate(AggregateKind::Adt(def, ..), ops)
                            if matches!(
                                def.name().as_str(),
                                "std::boxed::Box" | "alloc::boxed::Box"
                            ) =>
                        {
                            return match ops
                                .first()
                                .and_then(|op| self.wrapper_raw_pointer(defs, op, 0))
                            {
                                Some(raw) => BoxPointerSource::FromRaw(raw),
                                None => BoxPointerSource::Unknown,
                            };
                        }
                        _ => return BoxPointerSource::Unknown,
                    }
                }
                DefSite::Call(bb) => {
                    let TerminatorKind::Call { func, args, .. } =
                        &self.body.blocks[bb].terminator.kind
                    else {
                        return BoxPointerSource::Unknown;
                    };
                    let Some(path) =
                        self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
                    else {
                        return BoxPointerSource::Unknown;
                    };
                    // `Some(b).unwrap()`, `Ok(b).expect(..)`: the payload of the
                    // aggregate that built the unwrapped local.
                    if let Some(payload) = self.unwrapped_payload_operand(defs, &path, args) {
                        match operand_local(payload).filter(|&l| self.local_is_box(l)) {
                            Some(inner) => {
                                local = inner;
                                continue;
                            }
                            None => return BoxPointerSource::Unknown,
                        }
                    }
                    if !path.contains("boxed::Box") {
                        return BoxPointerSource::Unknown;
                    }
                    if path.ends_with("::new") {
                        return BoxPointerSource::Allocation;
                    }
                    if ["::from_raw", "::from_raw_in", "::from_non_null"]
                        .iter()
                        .any(|m| path.ends_with(m))
                    {
                        return match args.first() {
                            Some(raw) => BoxPointerSource::FromRaw(raw),
                            None => BoxPointerSource::Unknown,
                        };
                    }
                    return BoxPointerSource::Unknown;
                }
            }
        }
        BoxPointerSource::Unknown
    }

    /// The extent of the allocation behind the `Box` local `box_local`, read
    /// whole or through field projections (its data pointer): its pointee's
    /// size. A valid `Box<T>` owns exactly an allocation of `size_of::<T>()`
    /// bytes at its pointer's offset 0 (`Box::from_raw` of anything else is
    /// undefined behavior), so no definition of the local needs to be seen.
    /// Whether `local` is a reference (`&Box<T>` / `&mut Box<T>`) to a `Box` of
    /// a sized, non-zero-sized `T`.
    fn reference_to_sized_box(&self, local: usize) -> bool {
        self.reference_to_box_pointee_size(local).is_some_and(|size| size > 0)
    }

    /// The pointee size of the `Box` a reference local (`&Box<T>` / `&mut
    /// Box<T>`) points to, for a sized `T` (zero for a zero-sized one).
    fn reference_to_box_pointee_size(&self, local: usize) -> Option<usize> {
        let decl = self.body.locals().get(local)?;
        let TyKind::RigidTy(RigidTy::Ref(_, boxed, _)) = self.resolve_body_ty(decl.ty).kind()
        else {
            return None;
        };
        let boxed = self.resolve_body_ty(boxed);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else { return None };
        if !matches!(def.name().as_str(), "std::boxed::Box" | "alloc::boxed::Box") {
            return None;
        }
        args.0
            .iter()
            .find_map(|arg| match arg {
                rustc_public::ty::GenericArgKind::Type(t) => Some(*t),
                _ => None,
            })
            .and_then(|pointee| self.get_type_size(pointee))
    }

    fn box_local_extent(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        box_local: usize,
        projection: &[ProjectionElem],
    ) -> Option<RootExtent> {
        debug!(box_local, ?projection, "CHC: allocation root walk reached a Box candidate");
        if !projection.iter().all(|p| matches!(p, ProjectionElem::Field(..))) {
            return None;
        }
        // `Box::leak` inlined: `t = Box::into_raw_with_allocator(b)` returns the
        // pair `(b's pointer, b's allocator)`, so `t.0` is `b`'s data pointer.
        if let [ProjectionElem::Field(0, _)] = projection
            && let Some(inner) = self.into_raw_with_allocator_box(defs, box_local)
        {
            return self.box_local_extent(defs, inner, &[]);
        }
        let ty = self.resolve_body_ty(self.body.locals().get(box_local)?.ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        if !matches!(def.name().as_str(), "std::boxed::Box" | "alloc::boxed::Box") {
            return None;
        }
        // The extent is the allocation the box was built from. `Box::from_raw`
        // of memory that is not a `Box` allocation of that layout is undefined
        // behavior Kani does not report: a 4-byte heap block taken as a
        // `Box<[u8; 16]>` read its byte 8 in bounds of the box's type (review of
        // fix/chc-false-certificates round 1, `rv_box_bound.rs`
        // `b03_bug_heap4_as_box16_step`, the same on main). A box built from a
        // pointer whose allocation the walk does not reach (a stack array's
        // `as_mut_ptr`) fails closed: the read through it took a typed memory
        // cell the local's value never reached, and a stepped read of a stack
        // array laundered through `Box::from_raw` was a certified
        // counterexample where Kani proves it (`b02_safe_stack16_as_box_u8_step`,
        // the same on main).
        match self.box_pointer_source(defs, box_local) {
            BoxPointerSource::Allocation => {}
            BoxPointerSource::FromRaw(raw) => {
                return Some(
                    operand_local(raw)
                        .and_then(|raw_local| self.allocation_root_extent(raw_local))
                        .unwrap_or(RootExtent::Unmodeled),
                );
            }
            // A box this body did not build: its allocation is not known to be
            // one of its pointee type, so a dereference stepped from it fails
            // closed.
            BoxPointerSource::Unknown => return Some(RootExtent::Unmodeled),
        }
        let pointee = args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(t) => Some(*t),
            _ => None,
        })?;
        let size = self.get_type_size(pointee).and_then(|s| u64::try_from(s).ok())?;
        (size > 0).then_some(RootExtent::Bytes(size))
    }

    /// Mark every fail-closed far pointer observation's property as dependent
    /// on an approximation, after the dependence analysis ran: its guard reads
    /// an identified fresh variable, and a pass that folded that guard away must
    /// not let the property be certified.
    pub(in crate::codegen_ay::chc) fn mark_far_observation_properties_dependent(&mut self) {
        let relations = self.far_observation_relations.borrow().clone();
        if relations.is_empty() {
            return;
        }
        for property in &mut self.vc.properties {
            if relations.iter().any(|r| *r == property.relation) {
                property.approximation_dependent = Some(true);
            }
        }
    }

    /// The 64-bit offset `T` (from its object's base) of the pointer a wrapping
    /// step receives as `op` with value `value`, when it is known exactly: the
    /// identity says so ([`Self::identity_t64`]), or `op` is a local defined
    /// once by a wrapping step, a copy or a pointer cast whose operands are known
    /// the same way and still hold the values that definition read.
    ///
    /// Why they still hold them: a local with a single definition site
    /// (`single_assign_locals`, which excludes every local written through a
    /// reference) is definitely initialized wherever it is read, so the
    /// definition dominates the read; its operands' single definitions dominate
    /// it, and a path re-running one of them between the definition and the read
    /// would give a path from the entry to the read that avoids the definition.
    /// Their state variables must still be in the block's frame
    /// (`live_state_indices`; [`Self::extend_used_with_wrapping_bases`] keeps
    /// them there while the stepped local is read).
    pub(in crate::codegen_ay::chc) fn wrapping_operand_t64(
        &mut self,
        op: &Operand,
        value: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if self.int_lift {
            return None;
        }
        // A wide pointer's step moves its data word (`with_metadata_of(self)`).
        let value = &pointer_data_word(value)?;
        if let Some(t) = self.identity_t64(value) {
            return Some(t);
        }
        let local = operand_local(op)?;
        // The operand's own definition chain may rule a far pointer out where
        // its value (a field slot read in this block) does not.
        if !self.pointer_local_may_be_far(local, false) {
            return Some(Self::offset48(value).zero_extend(16));
        }
        self.local_t64(local, modified_locals, 0)
    }

    fn local_t64(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
        depth: u32,
    ) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        let def = self.wrapping_step_defs().get(&local).cloned()?;
        match def {
            WrappingDef::Through(src) => self.available_local_t64(src, modified_locals, depth),
            WrappingDef::Step { base, count, elem_size, is_sub } => {
                let t = self.available_local_t64(base, modified_locals, depth)?;
                let count = self.wrapping_count_value(&count, modified_locals)?;
                let bytes = if elem_size == 1 {
                    count
                } else {
                    count.bvmul(Expr::bitvec_const(elem_size as u128, 64))
                };
                let moved = if is_sub { t.bvsub(bytes) } else { t.bvadd(bytes) };
                Some(
                    trust_mc_core::chc_const_prop::eval::try_eval_to_const(&moved).unwrap_or(moved),
                )
            }
            WrappingDef::WithAddr { base, addr } => {
                let value = self.available_local_value(base, modified_locals)?;
                self.identity_t64(&value)?;
                let addr = self.wrapping_count_value(&addr, modified_locals)?;
                let base_address = self
                    .identity_object_region(&value)
                    .concat(Expr::bitvec_const(0u128, REGION_SHIFT));
                let t = addr.bvsub(base_address);
                Some(trust_mc_core::chc_const_prop::eval::try_eval_to_const(&t).unwrap_or(t))
            }
        }
    }

    fn available_local_t64(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
        depth: u32,
    ) -> Option<Expr> {
        let value = self.available_local_value(local, modified_locals)?;
        if let Some(t) = self.identity_t64(&value) {
            return Some(t);
        }
        self.local_t64(local, modified_locals, depth + 1)
    }

    /// The current value of `local` when it still holds the value its single
    /// definition gave it (see [`Self::wrapping_operand_t64`]).
    fn available_local_value(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !self.encode.single_assign_locals.contains(&local)
            || self.address_taken_locals().contains(&local)
        {
            return None;
        }
        let idx = *self.state_var_mgr.local_to_state_idx.get(&local)?;
        let live = modified_locals.contains(&local)
            || self
                .state_var_mgr
                .live_state_indices
                .get(self.current_encode_bb)
                .is_some_and(|live| live.contains(&idx));
        if !live {
            return None;
        }
        let place = rustc_public::mir::Place { local, projection: Vec::new() };
        let value = self.translate_operand_with_modified(&Operand::Copy(place), modified_locals)?;
        // A count is a `usize`; a wide pointer base gives its data word.
        pointer_data_word(&value)
    }

    fn wrapping_count_value(
        &mut self,
        count: &WrappingCount,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        match count {
            WrappingCount::Const(value) => Some(Expr::bitvec_const(*value as u128, 64)),
            WrappingCount::Local(local) => self.available_local_value(*local, modified_locals),
        }
    }

    /// Locals whose address the body takes in a way that can write them: a
    /// write through the reference is a definition no def-site walk sees. A
    /// shared borrow of a local without interior mutability (`Box::deref`'s
    /// `&b`) writes nothing; a mutable borrow or a raw address does.
    fn address_taken_locals(&self) -> &HashSet<usize> {
        self.far_address_taken.get_or_init(|| {
            use rustc_public::mir::BorrowKind;
            let mut taken = HashSet::new();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
                    let (place, shared) = match rvalue {
                        Rvalue::Ref(_, kind, place) => {
                            (place, matches!(kind, BorrowKind::Shared | BorrowKind::Fake(_)))
                        }
                        Rvalue::AddressOf(_, place) => (place, false),
                        _ => continue,
                    };
                    if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                        continue;
                    }
                    let interior_mut = self
                        .body
                        .locals()
                        .get(place.local)
                        .is_none_or(|decl| self.ty_has_interior_mut(decl.ty));
                    if !shared || interior_mut {
                        taken.insert(place.local);
                    }
                }
            }
            taken
        })
    }

    /// The single definitions of locals that a wrapping step's accumulated
    /// offset can follow ([`Self::wrapping_operand_t64`]): a wrapping step or
    /// `with_addr` of a raw pointer, or a copy or pointer cast of a pointer.
    pub(in crate::codegen_ay::chc) fn wrapping_step_defs(&self) -> &HashMap<usize, WrappingDef> {
        self.far_wrapping_defs.get_or_init(|| {
            let mut out = HashMap::new();
            if !self.far_pointers_possible() {
                return out;
            }
            let locals = self.body.locals();
            let all_defs = self.local_def_sites();
            for (&local, sites) in &all_defs {
                let [site] = sites.as_slice() else { continue };
                let def = match *site {
                    DefSite::Stmt(bb, si) => match &self.body.blocks[bb].statements[si].kind {
                        StatementKind::Assign(_, Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _))
                            if op.ty(locals).is_ok_and(ty_is_raw_ptr)
                                && locals.get(local).is_some_and(|d| ty_is_raw_ptr(d.ty))
                                && operand_local(op).is_some() =>
                        {
                            operand_local(op).map(WrappingDef::Through)
                        }
                        StatementKind::Assign(_, rvalue)
                            if locals.get(local).is_some_and(|d| ty_is_raw_ptr(d.ty)) =>
                        {
                            self.box_round_trip_stmt_def(&all_defs, rvalue)
                                .map(WrappingDef::Through)
                        }
                        _ => None,
                    },
                    DefSite::Call(bb) => {
                        self.wrapping_call_def(bb).or_else(|| self.box_round_trip_def(bb))
                    }
                };
                if let Some(def) = def {
                    out.insert(local, def);
                }
            }
            out
        })
    }

    /// The raw pointer local whose value the raw pointer `rvalue` defines is,
    /// bit for bit, through the INLINED `Box` round trip: a reborrow or raw
    /// address of a raw pointer's pointee (`&raw mut (*q)`), and a read of a
    /// `Box`'s data pointer (`(*r).0.0` through a reference to the box once
    /// `Box::into_raw` / `Box::leak` are inlined, directly or through a
    /// `NonNull` copy and its transmute) whose box `Box::from_raw` built from
    /// a raw pointer local ([`Self::field_read_source`]). A field read of any
    /// other aggregate counts only when the aggregate is not written in part.
    ///
    /// A call to `Box::from_raw` / `Box::into_raw` is [`Self::box_round_trip_def`];
    /// both are inlined into the harness more often than not
    /// (`Box(Unique::new_unchecked(p), alloc)`, `ManuallyDrop::new(b)` read back
    /// through `&mut (*m).0`), and then a far pointer round-tripped through a
    /// sized `Box<u8>` or `Box::leak` and stepped back drew a free far bit
    /// (`wrapping_step_far_unknown`) and its dereference or comparison failed
    /// closed where main and Kani prove it (second review of round 9,
    /// `r2_roundtrip.rs` r01, r02, r03, r07).
    fn box_round_trip_stmt_def(
        &self,
        defs: &HashMap<usize, Vec<DefSite>>,
        rvalue: &Rvalue,
    ) -> Option<usize> {
        let locals = self.body.locals();
        let raw_local = |l: usize| locals.get(l).is_some_and(|d| ty_is_raw_ptr(d.ty)).then_some(l);
        let read_source = |place: &rustc_public::mir::Place| -> Option<usize> {
            if !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                && !self.local_is_box(place.local)
                && self.local_written_in_part(place.local)
            {
                return None;
            }
            match self.field_read_source(defs, place) {
                FieldReadSource::Operand(op) => operand_local(op).and_then(raw_local),
                _ => None,
            }
        };
        match rvalue {
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if matches!(place.projection.as_slice(), [ProjectionElem::Deref]) =>
            {
                if let Some(raw) = raw_local(place.local) {
                    return Some(raw);
                }
                // `&raw mut (*r)` of a reference `r = &mut (*q)` to a raw
                // pointer `q`'s pointee (`Box::leak`'s `&mut *ptr`, inlined).
                let reference = place.local;
                if self.address_taken_locals().contains(&reference) {
                    return None;
                }
                let [DefSite::Stmt(bb, si)] = defs.get(&reference)?.as_slice() else { return None };
                let StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, _, inner) | Rvalue::AddressOf(_, inner),
                ) = &self.body.blocks[*bb].statements[*si].kind
                else {
                    return None;
                };
                if !matches!(inner.projection.as_slice(), [ProjectionElem::Deref]) {
                    return None;
                }
                raw_local(inner.local)
            }
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
            | Rvalue::Cast(
                CastKind::Transmute | CastKind::PtrToPtr,
                Operand::Copy(place) | Operand::Move(place),
                _,
            ) => {
                if !place.projection.is_empty() {
                    return read_source(place);
                }
                // A `NonNull` / `Unique` copy of a box's data pointer, then
                // transmuted to the raw pointer (`Box::into_raw` inlined).
                let wrapper = place.local;
                let is_pointer_wrapper = locals.get(wrapper).is_some_and(|decl| {
                    matches!(self.resolve_body_ty(decl.ty).kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
                        if matches!(def.name().as_str(), "std::ptr::NonNull" | "core::ptr::NonNull"
                            | "std::ptr::Unique" | "core::ptr::Unique"))
                });
                if !is_pointer_wrapper || self.address_taken_locals().contains(&wrapper) {
                    return None;
                }
                let [DefSite::Stmt(bb, si)] = defs.get(&wrapper)?.as_slice() else { return None };
                let StatementKind::Assign(
                    _,
                    Rvalue::Use(Operand::Copy(inner) | Operand::Move(inner), ..),
                ) = &self.body.blocks[*bb].statements[*si].kind
                else {
                    return None;
                };
                if inner.projection.is_empty() {
                    return None;
                }
                read_source(inner)
            }
            _ => None,
        }
    }

    /// `b = Box::from_raw(q)` and `r = Box::into_raw(b)` carry the pointer
    /// unchanged (`call/codegen_call_ptr_identity.rs` equates the destination
    /// with the argument, or fails the harness closed): a far pointer
    /// round-tripped through a box keeps its offset, so stepping it back by the
    /// count that moved it is the pointer it started from. Without this the
    /// step back drew a free far bit and `*r` failed closed where main and Kani
    /// prove it (review of fix/chc-false-certificates round 1,
    /// `rv_alloc_far.rs` `z06_zst_box_into_raw_far_step_back`).
    fn box_round_trip_def(&self, bb: usize) -> Option<WrappingDef> {
        let TerminatorKind::Call { func, args, destination, .. } =
            &self.body.blocks[bb].terminator.kind
        else {
            return None;
        };
        let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
        if !path.contains("boxed::Box") {
            return None;
        }
        let [arg] = args.as_slice() else { return None };
        let src = operand_local(arg)?;
        let locals = self.body.locals();
        let dest_ty = locals.get(destination.local)?.ty;
        let src_ty = arg.ty(locals).ok()?;
        let from_raw = path.ends_with("::from_raw")
            && ty_is_raw_ptr(src_ty)
            && self.local_is_box(destination.local);
        let into_raw =
            path.ends_with("::into_raw") && self.local_is_box(src) && ty_is_raw_ptr(dest_ty);
        (from_raw || into_raw).then_some(WrappingDef::Through(src))
    }

    fn wrapping_call_def(&self, bb: usize) -> Option<WrappingDef> {
        let TerminatorKind::Call { func, args, .. } = &self.body.blocks[bb].terminator.kind else {
            return None;
        };
        let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
        // Reject unrelated calls BEFORE reading a count as a pointer-sized
        // scalar. For example native ptr::write(p, 17u32) has no count and its
        // four-byte constant cannot be evaluated by eval_target_usize.
        let method = path.rsplit("::").next()?;
        if !matches!(
            method,
            "wrapping_add"
                | "wrapping_sub"
                | "wrapping_offset"
                | "arith_offset"
                | "wrapping_byte_add"
                | "wrapping_byte_offset"
                | "wrapping_byte_sub"
                | "with_addr"
        ) {
            return None;
        }
        let locals = self.body.locals();
        let [base_op, count_op] = args.as_slice() else { return None };
        let base_ty = base_op.ty(locals).ok()?;
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = base_ty.kind() else { return None };
        let base = operand_local(base_op)?;
        if !matches!(
            count_op.ty(locals).ok()?.kind(),
            TyKind::RigidTy(
                RigidTy::Uint(rustc_public::ty::UintTy::Usize)
                    | RigidTy::Int(rustc_public::ty::IntTy::Isize)
            )
        ) {
            return None;
        }
        let count = match count_op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                WrappingCount::Local(p.local)
            }
            Operand::Constant(c) => WrappingCount::Const(c.const_.eval_target_usize().ok()?),
            _ => return None,
        };
        let elem = || self.get_type_size(pointee).and_then(|s| u64::try_from(s).ok());
        Some(match method {
            "wrapping_add" => WrappingDef::Step { base, count, elem_size: elem()?, is_sub: false },
            "wrapping_sub" => WrappingDef::Step { base, count, elem_size: elem()?, is_sub: true },
            "wrapping_offset" | "arith_offset" => {
                WrappingDef::Step { base, count, elem_size: elem()?, is_sub: false }
            }
            "wrapping_byte_add" | "wrapping_byte_offset" => {
                WrappingDef::Step { base, count, elem_size: 1, is_sub: false }
            }
            "wrapping_byte_sub" => WrappingDef::Step { base, count, elem_size: 1, is_sub: true },
            "with_addr" => WrappingDef::WithAddr { base, addr: count },
            _ => return None,
        })
    }

    /// Keep a wrapping step's base pointer and count in the frame wherever the
    /// stepped local is read, so [`Self::wrapping_operand_t64`] can follow its
    /// definition: `used[bb]` gains, transitively, the operands of every local
    /// it already contains whose single definition the accumulated offset
    /// follows.
    pub(in crate::codegen_ay::chc) fn extend_used_with_wrapping_bases(
        &self,
        used: &mut [HashSet<usize>],
    ) {
        let defs = self.wrapping_step_defs();
        if defs.is_empty() {
            return;
        }
        for set in used.iter_mut() {
            let mut work: Vec<usize> =
                set.iter().copied().filter(|l| defs.contains_key(l)).collect();
            while let Some(local) = work.pop() {
                let deps: Vec<usize> = match &defs[&local] {
                    WrappingDef::Through(src) => vec![*src],
                    WrappingDef::Step { base, count, .. }
                    | WrappingDef::WithAddr { base, addr: count } => {
                        let mut deps = vec![*base];
                        if let WrappingCount::Local(l) = count {
                            deps.push(*l);
                        }
                        deps
                    }
                };
                for dep in deps {
                    if set.insert(dep) && defs.contains_key(&dep) {
                        work.push(dep);
                    }
                }
            }
        }
    }

    /// Whether the integer `operand` is, on every path, the exposed address of a
    /// pointer moved by a constant of fewer than 2^32 bytes: its local has one
    /// whole definition, no address taken, and that definition is a pointer
    /// read as an integer (`p as usize`, a transmute of a pointer, which is
    /// `addr()`), a copy of such an integer, or one plus or minus such a
    /// constant (`a + 4`, `CheckedAdd(a, 4).0`).
    ///
    /// Such an integer names the object it was read from: the address of an
    /// identity is a bijection ([`Self::ptr_to_int_value`] and
    /// [`Self::int_to_ptr_value`] are inverse), and a step of fewer than 2^32
    /// bytes stays in the object's 2^48-byte window, so the pointer made back
    /// from it is that object's pointer at the moved offset, in Kani's layout
    /// and here alike. The integer-to-pointer lane's invalidation exists for
    /// the other integers, a constant or a computed number that may name a
    /// model object only by the model's numbering, which Kani's does not share
    /// (`invalidate_int_to_ptr_object`); a pointer made back from an exposed
    /// address does not need it.
    pub(in crate::codegen_ay::chc) fn int_operand_is_exposed_address(
        &self,
        operand: &Operand,
    ) -> bool {
        self.int_operand_is_exposed_address_at(operand, 0)
    }

    fn int_operand_is_exposed_address_at(&self, operand: &Operand, depth: u32) -> bool {
        if depth > 8 {
            return false;
        }
        // The roundtrip exception is for integer addresses, not every type
        // sharing their bitvector sort. Pointer-to-float transmute still uses
        // address bits, but those bits cannot retain allocation provenance.
        // Check recursive operands too, so an integer alias cannot hide a
        // float intermediate and regain the exception.
        let Ok(operand_ty) = operand.ty(self.body.locals()) else { return false };
        if !matches!(
            self.resolve_body_ty(operand_ty).kind(),
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))
        ) {
            return false;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return false };
        let local = place.local;
        let arg_count = self.body.arg_locals().len();
        if local == 0
            || (1..=arg_count).contains(&local)
            || self.local_has_multiple_whole_definitions(local)
        {
            return false;
        }
        let mut definition = None;
        for statement in self.body.blocks.iter().flat_map(|b| b.statements.iter()) {
            match &statement.kind {
                StatementKind::Assign(dest, rvalue) if dest.local == local => {
                    if !dest.projection.is_empty() {
                        return false;
                    }
                    definition = Some(rvalue);
                }
                StatementKind::Assign(_, Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p))
                    if p.local == local =>
                {
                    return false;
                }
                _ => {}
            }
        }
        let Some(definition) = definition else { return false };
        let small_constant = |op: &Operand| -> bool {
            use crate::codegen_ay::shared::const_pointer::ConstRead;
            let Operand::Constant(c) = op else { return false };
            crate::codegen_ay::shared::const_pointer::const_bytes(&c.const_).is_some_and(|bytes| {
                !bytes.has_relocations()
                    && bytes.len() == 8
                    && bytes.read_uint_at(0, 8).is_some_and(|v| v < (1u128 << 32))
            })
        };
        let step = |lhs: &Operand, rhs: &Operand, commutes: bool| -> bool {
            (small_constant(rhs) && self.int_operand_is_exposed_address_at(lhs, depth + 1))
                || (commutes
                    && small_constant(lhs)
                    && self.int_operand_is_exposed_address_at(rhs, depth + 1))
        };
        match (place.projection.as_slice(), definition) {
            ([], Rvalue::Cast(CastKind::PointerExposeAddress, ..)) => true,
            ([], Rvalue::Cast(kind @ CastKind::Transmute, op, target)) => op
                .ty(self.body.locals())
                .ok()
                .is_some_and(|src| cast_exposes_address(kind, self.resolve_body_ty(src), *target)),
            ([], Rvalue::Use(op, ..)) => self.int_operand_is_exposed_address_at(op, depth + 1),
            ([], Rvalue::BinaryOp(BinOp::Add | BinOp::AddUnchecked, lhs, rhs)) => {
                step(lhs, rhs, true)
            }
            ([], Rvalue::BinaryOp(BinOp::Sub | BinOp::SubUnchecked, lhs, rhs)) => {
                step(lhs, rhs, false)
            }
            ([ProjectionElem::Field(0, _)], Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs)) => {
                step(lhs, rhs, true)
            }
            ([ProjectionElem::Field(0, _)], Rvalue::CheckedBinaryOp(BinOp::Sub, lhs, rhs)) => {
                step(lhs, rhs, false)
            }
            _ => false,
        }
    }

    /// [`Self::int_to_ptr_value`] for an integer OPERAND, deciding a constant
    /// in the null object first: an integer that folds to a constant whose
    /// high word is 0 is that constant as a pointer, whatever stack range it
    /// may fall in.
    ///
    /// Such a constant carries no provenance, in Kani or in Rust, so it names
    /// no allocation however the stack bases are placed. Under the stack-range
    /// `ite` this replaced, `ptr::null()` (a transmute of `0usize` once
    /// inlined) became a pointer whose object lane does not fold in any body
    /// that also exposes a stack address: the null object's exemption in
    /// `invalidate_int_to_ptr_object` no longer applied, a must-fail harness
    /// lost its Genuine certificate to `int_to_ptr_obj_invalidated`, and the
    /// `obj_valid` store at a symbolic index made a 10 s proof take 72 s
    /// (review of fix/chc-lost-writes, lostwrite round 1, finding 6). The
    /// region map of [`Self::int_to_ptr_value`] (Kani's layout, dfebf493c)
    /// folds such a constant to the same pointer, since region 0 is no tracked
    /// base's; the fold here keeps the exemption independent of that.
    ///
    /// Any other integer takes [`Self::int_to_ptr_value`]. In Kani's layout a
    /// constant such as `5usize << 32` is object 0 at offset `5 << 32`, whose
    /// lane no allocation has (`OBJECT_ID_LIMIT`); under the earlier layout it
    /// named stack slot 5, and folding it kept that lane, so a read or write
    /// through it verified clean where Kani reports an invalid integer address
    /// (lostwrite track round 1, finding 1). The result's lane is invalidated
    /// either way and, when it names an object whose validity the model takes
    /// for granted, fails closed (`invalidate_int_to_ptr_object`).
    pub(in crate::codegen_ay::chc) fn int_to_ptr_value_of_operand(&self, addr: Expr) -> Expr {
        if is_thin_ptr_sort(&addr)
            && let Some(folded) = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&addr)
            && let ay_bindings::ExprValue::BitVecConst { width: 64, .. } = folded.value()
            && Self::const_obj_id_u32(&folded.clone().extract(63, 32)) == Some(0)
        {
            return folded;
        }
        self.int_to_ptr_value(addr)
    }

    /// The pointer an integer with exposed provenance casts to: the identity term
    /// whose address ([`Self::ptr_to_int_value`]) it is. An address in a tracked
    /// local's region names that local again.
    pub(in crate::codegen_ay::chc) fn int_to_ptr_value(&self, addr: Expr) -> Expr {
        if !is_thin_ptr_sort(&addr) || self.int_lift {
            return addr;
        }
        let table = self.stack_base_table();
        let object = self.address_region_of_object(addr.clone().extract(63, REGION_SHIFT), &table);
        let low48 = addr.extract(REGION_SHIFT - 1, 0);
        let low48 = if table.is_empty() {
            low48
        } else {
            let r = Self::in_region_offset_of_object(&object, &table);
            if Self::const_bv_u32(&r) == Some(0) { low48 } else { low48.bvsub(r) }
        };
        let ptr = low48.clone().extract(47, 32).concat(object).concat(low48.extract(31, 0));
        let ptr = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&ptr).unwrap_or(ptr);
        self.note_far_producer(&ptr);
        // Observing it is exact (`may_be_far_observed`), also before it reaches
        // a local's state variable.
        self.far_from_integer.borrow_mut().push(ptr.clone());
        ptr
    }

    /// State-vector indices of the tracked bases (always live).
    pub(in crate::codegen_ay::chc) fn stack_base_state_indices(&self) -> Vec<usize> {
        self.heap_state
            .stack_bases
            .iter()
            .filter_map(|b| self.state_var_mgr.state_var_index_by_name(&b.name))
            .collect()
    }
}

/// The message of the property a fail-closed far pointer observation reaches
/// ([`ChcCtx::apply_far_observation_cuts`]).
const FAR_OBSERVATION_MESSAGE: &str = "pointer outside its object's 48-bit offset range observed \
     (Kani answers this observation differently for symbolic and literal offsets)";

/// Callee path suffixes of the wrapping pointer steps (with a raw-pointer
/// receiver) and the rebasing calls.
const WRAPPING_STEP_CALLEES: &[&str] = &[
    "::wrapping_add",
    "::wrapping_sub",
    "::wrapping_offset",
    "::wrapping_byte_add",
    "::wrapping_byte_sub",
    "::wrapping_byte_offset",
    "::with_addr",
    "::map_addr",
];

/// Callee path suffixes that build a pointer from an integer or step one by
/// any amount whatever the receiver.
const FAR_PRODUCING_CALLEES: &[&str] = &[
    "arith_offset",
    "::without_provenance",
    "::without_provenance_mut",
    "::with_exposed_provenance",
    "::with_exposed_provenance_mut",
    "::from_exposed_addr",
    "::from_exposed_addr_mut",
    "::invalid",
    "::invalid_mut",
    "::transmute",
    "::transmute_unchecked",
];

/// The single definition of a local that a wrapping step's accumulated offset
/// follows ([`ChcCtx::wrapping_operand_t64`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum WrappingDef {
    /// A copy or pointer cast of another pointer local.
    Through(usize),
    /// A wrapping step of the pointer local `base` by `count` elements of
    /// `elem_size` bytes (`elem_size == 1` for the byte steps).
    Step { base: usize, count: WrappingCount, elem_size: u64, is_sub: bool },
    /// `base.with_addr(addr)`.
    WithAddr { base: usize, addr: WrappingCount },
}

/// A wrapping step's count operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum WrappingCount {
    Const(u64),
    Local(usize),
}

/// A constant 64-bit vector's value.
fn const_u64(e: &Expr) -> Option<u64> {
    let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(e);
    let (value, width) = crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value(
        folded.as_ref().unwrap_or(e),
    )?;
    if width != 64 {
        return None;
    }
    u64::try_from(value).ok()
}

/// The names of every variable the expressions read; each node of their DAG is
/// visited once.
fn expr_var_names<'a>(exprs: impl IntoIterator<Item = &'a Expr>) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut seen: HashSet<usize> = HashSet::new();
    let mut stack: Vec<&Expr> = exprs.into_iter().collect();
    while let Some(node) = stack.pop() {
        if !seen.insert(node.value() as *const ExprValue as usize) {
            continue;
        }
        if let ExprValue::Var { name } = node.value() {
            names.insert(name.to_string());
            continue;
        }
        stack.extend(node.children());
    }
    names
}

/// [`ChcCtx::box_pointer_source`].
enum BoxPointerSource<'p> {
    /// A fresh allocation of the box's pointee type, the box at its offset 0.
    Allocation,
    /// `Box::from_raw(p)`: the box holds `p`.
    FromRaw(&'p Operand),
    Unknown,
}

/// [`ChcCtx::field_read_source`].
enum FieldReadSource<'p> {
    FreshAllocation,
    Operand(&'p Operand),
    Unknown,
}

/// Whether a call returns a fresh allocation, or the allocation pointer of a
/// `Vec`: never a far pointer. A `Box`'s pointer accessors are the pointer the
/// box was built from (`ChcCtx::box_pointer_source`); one whose box the walk
/// cannot name is not answered here.
fn call_returns_allocation_pointer(path: &str) -> bool {
    (path.contains("boxed::Box") && path.ends_with("::new"))
        || path.contains("exchange_malloc")
        || path.contains("__rust_alloc")
        || path.ends_with("alloc::alloc::alloc")
        || path.ends_with("alloc::alloc::alloc_zeroed")
        || (path.contains("vec::Vec")
            && ["::as_ptr", "::as_mut_ptr", "::as_non_null"].iter().any(|m| path.ends_with(m)))
}

/// [`ChcCtx::wrapping_chain_root_extent`]: the extent of an allocation a
/// wrapping chain starts at.
enum RootExtent {
    /// The allocation's size in bytes; the chain's base is at its offset 0.
    Bytes(u64),
    /// A buffer whose extent the byte model does not carry.
    Unmodeled,
}

/// The top 16 bits (the region) of a 64-bit address term, read through the
/// shapes an address keeps them in: `concat(region, low48)` (an identity's
/// address, [`ChcCtx::ptr_to_int_value`]) and a bitwise `|`, `&` or `^` with a
/// constant that leaves the top 16 bits alone (`map_addr` tag arithmetic).
fn address_top_bits(addr: &Expr) -> Option<Expr> {
    const MASK48: u64 = (1u64 << 48) - 1;
    match addr.value() {
        ExprValue::BvConcat(high, low)
            if high.sort().bitvec_width() == Some(16) && low.sort().bitvec_width() == Some(48) =>
        {
            Some(high.clone())
        }
        ExprValue::BvOr(a, b) | ExprValue::BvXor(a, b) => {
            let (term, constant) = if const_u64(b).is_some() { (a, b) } else { (b, a) };
            (const_u64(constant)? & !MASK48 == 0).then(|| address_top_bits(term)).flatten()
        }
        ExprValue::BvAnd(a, b) => {
            let (term, constant) = if const_u64(b).is_some() { (a, b) } else { (b, a) };
            (const_u64(constant)? | MASK48 == u64::MAX).then(|| address_top_bits(term)).flatten()
        }
        _ => None,
    }
}

thread_local! {
    /// The function whose translation must treat far pointers as possible from
    /// the start (`mir_to_chc_internal`'s retry).
    static FAR_FORCED_FN: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
    /// The function whose translation met a far pointer after an observation it
    /// had translated without fail-closed conditions.
    static FAR_RETRY_FN: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

fn far_forced_for(fn_name: &str) -> bool {
    FAR_FORCED_FN.with(|f| f.borrow().as_deref() == Some(fn_name))
}

/// Whether the last translation of `fn_name` asked for a retry with far
/// pointers possible from the start ([`ChcCtx::book_far_pointer_prescan`]);
/// clears the request.
pub(in crate::codegen_ay) fn take_far_prescan_retry(fn_name: &str) -> bool {
    FAR_RETRY_FN.with(|f| {
        let mut slot = f.borrow_mut();
        if slot.as_deref() == Some(fn_name) {
            *slot = None;
            true
        } else {
            false
        }
    })
}

/// Make (or stop making) far pointers possible from the start of every
/// translation of `fn_name`.
pub(in crate::codegen_ay) fn set_far_forced(fn_name: Option<&str>) {
    FAR_FORCED_FN.with(|f| *f.borrow_mut() = fn_name.map(str::to_string));
}
