// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Implement a transformation pass that instrument the code to detect possible UB due to
//! the generation of an invalid value.
//!
//! This pass highly depend on Rust type layouts. For more details, see:
//! <https://doc.rust-lang.org/reference/type-layout.html>
//!
//! For that, we traverse the function body and look for unsafe operations that may generate
//! invalid values. For each operation found, we add checks to ensure the value is valid.
//!
//! Note: There is some redundancy in the checks that could be optimized. Example:
//!   1. We could merge the invalid values by the offset.
//!   2. We could avoid checking places that have been checked before.
mod ty_validity;

#[cfg(test)]
mod tests;

use ty_validity::{
    assignment_check_points, build_value_range_check, first_aggregate_operand, intrinsic_name,
    move_local,
};
pub(crate) use ty_validity::{build_limits, ty_validity_per_offset};

use crate::args::ExtraChecks;
use crate::kani_middle::transform::body::{
    CheckType, InsertPosition, MutableBody, SourceInstruction,
};
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_middle::ty::{Const, TyCtxt};
use rustc_public::abi::{FieldsShape, Scalar, ValueAbi, WrappingRange};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::{Location, PlaceContext, PlaceRef};
use rustc_public::mir::{
    AggregateKind, BasicBlockIdx, BinOp, Body, CastKind, Local, LocalDecl, MirVisitor, Mutability,
    NonDivergingIntrinsic, Operand, Place, ProjectionElem, RawPtrKind, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind,
};
use rustc_public::rustc_internal;
use rustc_public::target::{MachineInfo, MachineSize};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind, UintTy};
use std::fmt::Debug;
use strum_macros::AsRefStr;
use tracing::{debug, trace};

/// Instrument the code with checks for invalid values.
#[derive(Debug, Clone)]
pub(crate) struct ValidValuePass {
    pub(crate) safety_check_type: CheckType,
    pub(crate) unsupported_check_type: CheckType,
}

impl TransformPass for ValidValuePass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Instrumentation
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        let args = query_db.args();
        args.ub_check.contains(&ExtraChecks::Validity)
    }

    /// Transform the function body by inserting checks one-by-one.
    /// For every unsafe dereference or a transmute operation, we check all values are valid.
    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        trace!(function=?instance.name(), "transform");
        let mut new_body = MutableBody::from(body);
        let orig_len = new_body.blocks().len();
        // Do not cache body.blocks().len() since it will change as we add new checks.
        for bb_idx in 0..new_body.blocks().len() {
            let Some(candidate) =
                CheckValueVisitor::find_next(tcx, &new_body, bb_idx, bb_idx >= orig_len)
            else {
                continue;
            };
            self.build_check(&mut new_body, candidate);
        }
        (orig_len != new_body.blocks().len(), new_body.into())
    }
}

impl ValidValuePass {
    fn build_check(&self, body: &mut MutableBody, instruction: UnsafeInstruction) {
        debug!(?instruction, "build_check");
        let mut source = instruction.source;
        for operation in instruction.operations {
            match operation {
                SourceOp::BytesValidity { ranges, target_ty, rvalue } => {
                    // Task #76: For a transmute-like cast from a bit-faithful
                    // scalar, check the SOURCE operand's bytes instead of
                    // materializing the destination and reading it back.
                    // Transmute preserves bytes, so the ranges apply verbatim,
                    // but the destination read-back observes the value AFTER
                    // backend normalization: `Cast(Transmute, u8, bool)` is
                    // lowered value-normalizing (`x != 0`), so the read-back
                    // byte is always 0/1 and an invalid bitpattern (e.g. 2)
                    // is unobservable — the check discharges vacuously
                    // (false-Safe). Reading the source also avoids the
                    // type-punned pointer cast (`*const char as *const u32`)
                    // that the CHC type-indexed memory model mistracks.
                    if let Some(src_op) = transmute_scalar_source(body.locals(), &rvalue) {
                        let value = body.insert_assignment(
                            Rvalue::Use(src_op),
                            &mut source,
                            InsertPosition::Before,
                        );
                        let rvalue_ptr = Rvalue::AddressOf(RawPtrKind::Const, Place::from(value));
                        for range in ranges {
                            let result =
                                build_limits(body, &range, rvalue_ptr.clone(), &mut source);
                            let msg =
                                format!("Undefined Behavior: Invalid value of type `{target_ty}`",);
                            body.insert_check(
                                &self.safety_check_type,
                                &mut source,
                                InsertPosition::Before,
                                Some(result),
                                &msg,
                            );
                        }
                        continue;
                    }
                    // Fail-closed (#76): a bool-valid range checked through the
                    // materialized destination can never observe the invalid
                    // byte (see above). If we cannot redirect to the source
                    // bytes, emit an unsupported-check (demoted FAILED) for
                    // those ranges instead of a vacuous check. Other ranges
                    // (char, NonZero, niche ints) read back bit-faithfully
                    // from BV-sorted destinations and keep the precise check.
                    let is_transmute_like = matches!(
                        rvalue,
                        Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, _, _)
                    );
                    let (normalizing, precise): (Vec<_>, Vec<_>) = if is_transmute_like {
                        ranges.into_iter().partition(range_is_bool_like)
                    } else {
                        (Vec::new(), ranges)
                    };
                    if !precise.is_empty() {
                        let value =
                            body.insert_assignment(rvalue, &mut source, InsertPosition::Before);
                        let rvalue_ptr = Rvalue::AddressOf(RawPtrKind::Const, Place::from(value));
                        for range in precise {
                            let result =
                                build_limits(body, &range, rvalue_ptr.clone(), &mut source);
                            let msg =
                                format!("Undefined Behavior: Invalid value of type `{target_ty}`",);
                            body.insert_check(
                                &self.safety_check_type,
                                &mut source,
                                InsertPosition::Before,
                                Some(result),
                                &msg,
                            );
                        }
                    }
                    if !normalizing.is_empty() {
                        let reason = format!(
                            "trust_mc can't observe the pre-transmute bytes for the \
                             `bool` validity of `{target_ty}` (non-scalar transmute source)",
                        );
                        self.unsupported_check(body, &mut source, &reason);
                    }
                }
                SourceOp::DerefValidity { pointee_ty, rvalue, ranges } => {
                    // Precise array-element redirect (analogous to
                    // `transmute_scalar_source`): when the dereferenced pointer
                    // traces back — through casts / reborrows only — to a base
                    // array `[E; N]` whose element `E` is an unsigned integer of
                    // exactly the requirement's byte size, read the array
                    // ELEMENT directly (`arr[offset/stride]`) instead of
                    // dereferencing the type-punned byte pointer. The CHC
                    // type-indexed memory model cannot resolve the punned read
                    // back to the stored value (it demotes to an unconstrained
                    // load / whole-array sort mismatch), so the byte-pointer
                    // path yields an EncodingGap; the direct element read is
                    // bit-exact (`size_of(E) == req.size`, static in-bounds
                    // index) and lets the assert consume the real value.
                    // Fail-closed: any non-trivial projection, non-array base,
                    // size/kind mismatch, or unaligned/out-of-range offset falls
                    // back to the unchanged byte-pointer path below.
                    let element_plan = array_source(body, &rvalue)
                        .and_then(|src| plan_array_element_checks(&ranges, &src));
                    if let Some((arr_place, plan)) = element_plan {
                        for (index, req) in plan {
                            let mut projection = arr_place.projection.clone();
                            projection.push(ProjectionElem::ConstantIndex {
                                offset: index as u64,
                                min_length: index as u64 + 1,
                                from_end: false,
                            });
                            let value = Operand::Copy(Place { local: arr_place.local, projection });
                            let result = build_value_range_check(body, &req, value, &mut source);
                            let msg = format!(
                                "Undefined Behavior: Invalid value of type `{pointee_ty}`",
                            );
                            body.insert_check(
                                &self.safety_check_type,
                                &mut source,
                                InsertPosition::Before,
                                Some(result),
                                &msg,
                            );
                        }
                        continue;
                    }
                    for range in ranges {
                        let result = build_limits(body, &range, rvalue.clone(), &mut source);
                        let msg =
                            format!("Undefined Behavior: Invalid value of type `{pointee_ty}`",);
                        body.insert_check(
                            &self.safety_check_type,
                            &mut source,
                            InsertPosition::Before,
                            Some(result),
                            &msg,
                        );
                    }
                }
                SourceOp::UnsupportedCheck { check, ty } => {
                    let reason = format!(
                        "trust_mc currently doesn't support checking validity of `{check}` for `{ty}`",
                    );
                    self.unsupported_check(body, &mut source, &reason);
                }
                SourceOp::GuardedDerefValidity { pointee_ty, rvalue, ranges, count } => {
                    // Part of #698: Handle dynamic count by guarding validity check.
                    // The check is: count == 0 || validity_check
                    // This avoids false positives when count is 0 and still catches bugs
                    // for at least the first element when count > 0.
                    //
                    // INVARIANT: ranges is non-empty (caller ensures this in visit_statement)
                    debug_assert!(
                        !ranges.is_empty(),
                        "GuardedDerefValidity requires non-empty ranges"
                    );
                    let span = source.span(body.blocks());

                    // Build count_is_zero = (count == 0)
                    let zero_const = body.new_uint_operand(0, UintTy::Usize, span);
                    let count_local = body.insert_assignment(
                        Rvalue::Use(count),
                        &mut source,
                        InsertPosition::Before,
                    );
                    let count_is_zero = body.insert_binary_op(
                        BinOp::Eq,
                        move_local(count_local),
                        zero_const,
                        &mut source,
                        InsertPosition::Before,
                    );

                    // Build validity check for all ranges (ANDed together)
                    let mut validity_result: Option<Local> = None;
                    for range in ranges {
                        let range_result = build_limits(body, &range, rvalue.clone(), &mut source);
                        validity_result = Some(match validity_result {
                            None => range_result,
                            Some(prev) => body.insert_binary_op(
                                BinOp::BitAnd,
                                move_local(prev),
                                move_local(range_result),
                                &mut source,
                                InsertPosition::Before,
                            ),
                        });
                    }

                    // Build guarded_result = count_is_zero || validity_result
                    // Note: validity_result is always Some because ranges is non-empty (invariant above)
                    let guarded_result = match validity_result {
                        Some(validity) => body.insert_binary_op(
                            BinOp::BitOr,
                            move_local(count_is_zero),
                            move_local(validity),
                            &mut source,
                            InsertPosition::Before,
                        ),
                        None => {
                            unreachable!("ranges is non-empty, so validity_result must be Some")
                        }
                    };

                    let msg = format!(
                        "Undefined Behavior: Invalid value of type `{pointee_ty}` in copy_nonoverlapping",
                    );
                    body.insert_check(
                        &self.safety_check_type,
                        &mut source,
                        InsertPosition::Before,
                        Some(guarded_result),
                        &msg,
                    );
                }
            }
        }
    }

    fn unsupported_check(
        &self,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        reason: &str,
    ) {
        body.insert_check(
            &self.unsupported_check_type,
            source,
            InsertPosition::Before,
            None,
            reason,
        );
    }
}

/// If `rvalue` is a transmute-like cast whose source operand is a scalar with
/// a bit-faithful backend byte image (`char` / integer — BV-sorted, identity
/// read-back), return a copyable operand for that source (task #76).
///
/// `bool` and float sources are excluded: a `bool` local is Bool-sorted in the
/// CHC backend (byte read-back reintroduces the bool/u8 pun) and float locals
/// are FP-sorted (no guaranteed bit-precise byte image).
fn transmute_scalar_source(locals: &[LocalDecl], rvalue: &Rvalue) -> Option<Operand> {
    let Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, op, _) = rvalue else {
        return None;
    };
    let op_ty = op.ty(locals).ok()?;
    let bit_faithful =
        matches!(op_ty.kind(), TyKind::RigidTy(RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_)));
    if !bit_faithful {
        return None;
    }
    Some(match op {
        // The inserted read runs BEFORE the original statement, so a `Move`
        // operand must be duplicated as `Copy` (the original move still
        // consumes the place afterwards).
        Operand::Move(place) | Operand::Copy(place) => Operand::Copy(place.clone()),
        constant @ Operand::Constant(_) => constant.clone(),
    })
}

/// A base array place a `DerefValidity` pointer resolves to.
struct ArraySource {
    /// The array place (`[E; N]`); its own projections are normally empty.
    place: Place,
    /// Element type `E`.
    elem_ty: Ty,
    /// Byte stride between consecutive elements (== `size_of::<E>()` for the
    /// scalar element types this redirect accepts).
    stride_bytes: usize,
    /// Element count `N`.
    count: usize,
}

/// Trace a `DerefValidity` rvalue's pointer back to the base array place it
/// points at, following only value- and address-preserving steps: `Use`/`Cast`
/// of a bare local, and `Ref`/`AddressOf` of either the array itself (`&arr`)
/// or a reborrow (`&(*ptr)`). Returns `None` (fail-closed) on a non-unique
/// definition, any field/index/offset projection, or a non-array referent —
/// anything that could shift the pointer off the array base or that this pass
/// cannot prove addresses the whole array.
fn array_source(body: &MutableBody, rvalue: &Rvalue) -> Option<ArraySource> {
    let Rvalue::Use(Operand::Copy(ptr_place) | Operand::Move(ptr_place)) = rvalue else {
        return None;
    };
    if !ptr_place.projection.is_empty() {
        return None;
    }
    let mut current = ptr_place.local;
    // Bounded to guard against any (unexpected) self-referential definition.
    for _ in 0..16 {
        let rhs = unique_assignment_rhs(body, current)?;
        match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projection.is_empty() => {
                current = p.local;
            }
            Rvalue::Cast(kind, Operand::Copy(p) | Operand::Move(p), _)
                if p.projection.is_empty() && array_source_cast_preserves_address(kind) =>
            {
                current = p.local;
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                match place.projection.as_slice() {
                    [] => {
                        let ty = body.locals()[place.local].ty;
                        let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
                            // Referent is not an array: cannot prove it is the base.
                            return None;
                        };
                        let shape = ty.layout().ok()?.shape();
                        let FieldsShape::Array { stride, count } = shape.fields else {
                            return None;
                        };
                        return Some(ArraySource {
                            place: place.clone(),
                            elem_ty,
                            stride_bytes: stride.bytes(),
                            count: count.try_into().ok()?,
                        });
                    }
                    // Reborrow `&(*ptr)`: follow the underlying pointer local.
                    [ProjectionElem::Deref] => current = place.local,
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// Whether a cast can be erased while tracing a dereference back to the exact
/// allocation it addresses.
///
/// `PtrToPtr` preserves the data address and provenance; `Subtype` is a
/// representation-preserving type-system cast.  In particular, do not follow
/// expose-address / with-exposed-provenance or numeric casts.  A chain such as
/// pointer -> integer -> float -> integer -> pointer can have unique MIR
/// assignments while changing or rounding the address; redirecting that final
/// dereference to the original array would then validate the wrong bytes.
fn array_source_cast_preserves_address(kind: &CastKind) -> bool {
    matches!(kind, CastKind::PtrToPtr | CastKind::Subtype)
}

/// Find the unique `current = rhs` assignment across the whole body, or `None`
/// if there is not exactly one authoritative definition.
///
/// Argument locals already have a caller-provided value before any MIR
/// statement runs, so a single conditional assignment to an argument is not a
/// unique definition. Call destinations similarly define their local on the
/// normal-return edge. Both cases must decline the redirect: otherwise a
/// branch-local pointer derived from an array could be mistaken for the value
/// used on a different branch. Inline assembly is unsupported and may also
/// write locals, so its presence conservatively declines this analysis.
fn unique_assignment_rhs(body: &MutableBody, current: Local) -> Option<&Rvalue> {
    if (1..=body.arg_count()).contains(&current) {
        return None;
    }

    let mut found: Option<&Rvalue> = None;
    for block in body.blocks() {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.projection.is_empty()
                && lhs.local == current
            {
                if found.is_some() {
                    return None;
                }
                found = Some(rhs);
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. }
                if destination.local == current && destination.projection.is_empty() =>
            {
                return None;
            }
            TerminatorKind::InlineAsm { .. } => return None,
            _ => {}
        }
    }
    found
}

/// For each validity requirement, compute the static array element index it
/// covers and validate the redirect is bit-exact. Returns `(arr_place, plan)`
/// pairing each element index with its requirement, or `None` (fail-closed)
/// unless EVERY requirement qualifies: the element is an unsigned integer whose
/// size equals both the stride and the requirement's size, the offset is a
/// multiple of the stride, and the resulting index is in `0..count`. This
/// guarantees `arr[idx]` reads exactly the bits the punned byte-pointer would,
/// with matching unsigned comparison sorts.
fn plan_array_element_checks(
    ranges: &[ValidValueReq],
    source: &ArraySource,
) -> Option<(Place, Vec<(usize, ValidValueReq)>)> {
    let stride = source.stride_bytes;
    if stride == 0 {
        return None;
    }
    let TyKind::RigidTy(RigidTy::Uint(_)) = source.elem_ty.kind() else {
        return None;
    };
    let elem_bytes = source.elem_ty.layout().ok()?.shape().size.bytes();
    if elem_bytes != stride {
        return None;
    }
    let mut plan = Vec::with_capacity(ranges.len());
    for req in ranges {
        if req.size.bytes() != stride || req.offset % stride != 0 {
            return None;
        }
        let index = req.offset / stride;
        if index >= source.count {
            return None;
        }
        plan.push((index, req.clone()));
    }
    Some((source.place.clone(), plan))
}

/// Whether this validity requirement is the `bool` shape (single byte, value
/// range `0..=1`). The backend materializes `bool` destinations
/// value-normalizing, so a destination read-back for this shape is vacuous
/// (task #76). Custom one-byte `0..=1` niches are conservatively included —
/// misclassification only demotes (fail-closed), never passes vacuously.
fn range_is_bool_like(req: &ValidValueReq) -> bool {
    req.size.bits() == 8
        && matches!(req.valid_range, ValidityRange::Single(WrappingRange { start: 0, end: 1 }))
}

/// Represent a requirement for the value stored in the given offset.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(super) struct ValidValueReq {
    /// Offset in bytes.
    pub(super) offset: usize,
    /// Size of this requirement.
    pub(super) size: MachineSize,
    /// The range restriction is represented by a Scalar.
    pub(super) valid_range: ValidityRange,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(super) enum ValidityRange {
    /// The value validity fits in a single value range.
    /// This includes cases where the full range is covered.
    Single(WrappingRange),
    /// The validity includes more than one value range.
    /// Currently, this is only the case for `char`, which has two ranges.
    /// If more cases come up, we could turn this into a vector instead.
    Multiple([WrappingRange; 2]),
}

// OPTIMIZATION OPPORTUNITY: Merging validity range requirements.
//
// Currently, each validity range generates a separate check. When the same bytes
// are checked multiple times (e.g., nested struct fields), this creates redundant
// SMT constraints. Merging would reduce verification overhead.
//
// Cases to handle:
// 1. Subset: new range ⊆ existing range → drop new range (already covered)
// 2. Overlap: ranges intersect → merge into single range
// 3. Split: intersection creates two disjoint ranges → keep both
// 4. Disjoint: ranges don't intersect → keep both (or report conflict)
//
// Impact: Low priority. SMT solvers handle redundant constraints efficiently,
// and the redundancy is bounded by type nesting depth. Profile before optimizing.
// Part of #1359.
impl ValidValueReq {
    /// Only a type with `ValueAbi::Scalar` and `ValueAbi::ScalarPair` can be directly assigned an
    /// invalid value directly.
    ///
    /// It's not possible to define a `rustc_layout_scalar_valid_range_*` to any other structure.
    /// Note that this annotation only applies to the first scalar in the layout.
    pub(crate) fn try_from_ty(machine_info: &MachineInfo, ty: Ty) -> Option<ValidValueReq> {
        if ty.kind().is_char() {
            Some(ValidValueReq {
                offset: 0,
                size: MachineSize::from_bits(size_of::<char>() * 8),
                valid_range: ValidityRange::Multiple([
                    WrappingRange { start: 0, end: 0xD7FF },
                    WrappingRange { start: 0xE000, end: char::MAX.into() },
                ]),
            })
        } else {
            let shape = ty.layout().expect("type layout for valid value req").shape();
            match shape.abi {
                ValueAbi::Scalar(Scalar::Initialized { value, valid_range })
                | ValueAbi::ScalarPair(Scalar::Initialized { value, valid_range }, _) => {
                    Some(ValidValueReq {
                        offset: 0,
                        size: value.size(machine_info),
                        valid_range: ValidityRange::Single(valid_range),
                    })
                }
                ValueAbi::Scalar(_)
                | ValueAbi::ScalarPair(_, _)
                | ValueAbi::Vector { .. }
                | ValueAbi::Aggregate { .. } => None,
            }
        }
    }

    /// Check if range is full.
    pub(crate) fn is_full(&self) -> bool {
        if let ValidityRange::Single(valid_range) = self.valid_range {
            valid_range.is_full(self.size).expect("is_full check")
        } else {
            false
        }
    }

    /// Check if this range contains `other` range.
    ///
    /// I.e., `scalar_2` ⊆ `scalar_1`
    pub(crate) fn contains(&self, other: &ValidValueReq) -> bool {
        assert_eq!(self.size, other.size);
        match (&self.valid_range, &other.valid_range) {
            (ValidityRange::Single(this_range), ValidityRange::Single(other_range)) => {
                range_contains(this_range, other_range, self.size)
            }
            (ValidityRange::Multiple(this_ranges), ValidityRange::Single(other_range)) => {
                range_contains(&this_ranges[0], other_range, self.size)
                    || range_contains(&this_ranges[1], other_range, self.size)
            }
            (ValidityRange::Single(this_range), ValidityRange::Multiple(other_ranges)) => {
                range_contains(this_range, &other_ranges[0], self.size)
                    && range_contains(this_range, &other_ranges[1], self.size)
            }
            (ValidityRange::Multiple(this_ranges), ValidityRange::Multiple(other_ranges)) => {
                let contains = (range_contains(&this_ranges[0], &other_ranges[0], self.size)
                    || range_contains(&this_ranges[1], &other_ranges[0], self.size))
                    && (range_contains(&this_ranges[0], &other_ranges[1], self.size)
                        || range_contains(&this_ranges[1], &other_ranges[1], self.size));
                // Multiple today only cover `char` case.
                debug_assert!(
                    contains,
                    "Expected validity of `char` for Multiple ranges. Found: {self:?}, {other:?}"
                );
                contains
            }
        }
    }
}

/// Check if range `r1` contains range `r2`.
///
/// I.e., `r2` ⊆ `r1`
fn range_contains(r1: &WrappingRange, r2: &WrappingRange, sz: MachineSize) -> bool {
    match (r1.wraps_around(), r2.wraps_around()) {
        (true, true) | (false, false) => r1.start <= r2.start && r1.end >= r2.end,
        (true, false) => r1.start <= r2.start || r1.end >= r2.end,
        (false, true) => r1.is_full(sz).expect("is_full for range_contains"),
    }
}

#[derive(AsRefStr, Clone, Debug)]
#[allow(clippy::large_enum_variant)]
enum SourceOp {
    /// Validity checks are done on a byte level when the Rvalue can generate invalid value.
    ///
    /// This variant tracks a location that is valid for its current type, but it may not be
    /// valid for the given location in target type. This happens for:
    ///  - Transmute
    ///  - Field assignment
    ///  - Aggregate assignment
    ///  - Union Access
    ///
    /// Each range is a pair of offset and scalar that represents the valid values.
    /// Note that the same offset may have multiple ranges that may require being joined.
    BytesValidity { target_ty: Ty, rvalue: Rvalue, ranges: Vec<ValidValueReq> },

    /// Similar to BytesValidity, but it stores any dereference that may be unsafe.
    ///
    /// This can happen for:
    ///  - Raw pointer dereference
    DerefValidity { pointee_ty: Ty, rvalue: Rvalue, ranges: Vec<ValidValueReq> },

    /// Represents a validity check that Kani/trust_mc does not currently support.
    ///
    /// This variant is used for corner cases with `#[rustc_layout_scalar_valid_range_*]`
    /// attributes, such as:
    /// - Non-intersecting validity ranges
    /// - Enumerations with complex niche layouts
    /// - Unit pointer casts where provenance is lost
    ///
    /// ## Current Behavior (Sound)
    /// Emits `UnsupportedCheckHook` which causes verification to report failure.
    /// This is conservative: no bugs are missed, but users must disable the check
    /// if they hit these edge cases.
    ///
    /// ## Alternative: Compilation Warning
    /// Could instead emit a compile-time warning and skip the check. This would
    /// improve usability for corner cases but could miss bugs. The trade-off is:
    /// - Soundness (current): Never miss a bug, may have false positives
    /// - Usability (alternative): Skip rare edge cases with warning
    ///
    /// Decision: Keep current sound behavior. These edge cases are rare enough
    /// that the soundness guarantee outweighs usability cost. Part of #1359.
    UnsupportedCheck { check: &'static str, ty: Ty },

    /// Guarded validity check for dynamic count operations like copy_nonoverlapping.
    ///
    /// Generates check: `count == 0 || validity_check`
    /// - When count == 0: check passes (no bytes copied, nothing to validate)
    /// - When count > 0: validates the first element (conservative but sound)
    ///
    /// Part of #698: handle copy_nonoverlapping with dynamic counts.
    GuardedDerefValidity {
        pointee_ty: Ty,
        rvalue: Rvalue,
        ranges: Vec<ValidValueReq>,
        count: Operand,
    },
}

/// The unsafe instructions that may generate invalid values.
/// We need to instrument all operations to ensure the instruction is safe.
#[derive(Clone, Debug)]
struct UnsafeInstruction {
    /// The instruction that depends on the potentially invalid value.
    source: SourceInstruction,
    /// The unsafe operations that may cause an invalid value in this instruction.
    operations: Vec<SourceOp>,
}

/// Extract any source that may potentially trigger UB due to the generation of an invalid value.
///
/// Generating an invalid value requires an unsafe operation, however, in MIR, it
/// may just be represented as a regular assignment.
///
/// Thus, we have to instrument every assignment to an object that has niche and that the source
/// is an object of a different source, e.g.:
///   - Aggregate assignment
///   - Transmute
///   - MemCopy
///   - Cast
struct CheckValueVisitor<'a, 'b> {
    tcx: TyCtxt<'b>,
    locals: &'a [LocalDecl],
    /// Whether we should skip the next instruction, since it might've been instrumented already.
    /// When we instrument an instruction, we partition the basic block, and the instruction that
    /// may trigger UB becomes the first instruction of the basic block, which we need to skip
    /// later.
    skip_next: bool,
    /// The instruction being visited at a given point.
    current: SourceInstruction,
    /// The target instruction that should be verified.
    pub target: Option<UnsafeInstruction>,
    /// The basic block being visited.
    bb: BasicBlockIdx,
    /// Machine information needed to calculate Niche.
    machine: MachineInfo,
}

impl<'a, 'b> CheckValueVisitor<'a, 'b> {
    fn find_next(
        tcx: TyCtxt<'b>,
        body: &'a MutableBody,
        bb: BasicBlockIdx,
        skip_first: bool,
    ) -> Option<UnsafeInstruction> {
        let mut visitor = CheckValueVisitor {
            tcx,
            locals: body.locals(),
            skip_next: skip_first,
            current: SourceInstruction::Statement { idx: 0, bb },
            target: None,
            bb,
            machine: MachineInfo::target(),
        };
        visitor.visit_basic_block(&body.blocks()[bb]);
        visitor.target
    }

    fn push_target(&mut self, op: SourceOp) {
        let target = self
            .target
            .get_or_insert_with(|| UnsafeInstruction { source: self.current, operations: vec![] });
        target.operations.push(op);
    }

    fn constant_operand_target_usize(operand: &Operand) -> Option<usize> {
        match operand {
            Operand::Constant(constant) => {
                constant.const_.eval_target_usize().ok().map(|v| v as usize)
            }
            _ => None,
        }
    }

    fn expand_validity_for_count(
        pointee_ty: Ty,
        base_ranges: &[ValidValueReq],
        count: usize,
    ) -> Option<Vec<ValidValueReq>> {
        if count == 0 {
            return Some(vec![]);
        }
        let elem_size = pointee_ty.layout().ok()?.shape().size.bytes();
        if elem_size == 0 {
            return Some(vec![]);
        }
        let mut ranges = Vec::with_capacity(base_ranges.len().saturating_mul(count));
        for idx in 0..count {
            let base_offset = idx.checked_mul(elem_size)?;
            for req in base_ranges {
                let mut req = req.clone();
                req.offset = req.offset.checked_add(base_offset)?;
                ranges.push(req);
            }
        }
        Some(ranges)
    }
}

impl MirVisitor for CheckValueVisitor<'_, '_> {
    fn visit_statement(&mut self, stmt: &Statement, location: Location) {
        if self.skip_next {
            self.skip_next = false;
        } else if self.target.is_none() {
            // Leave it as an exhaustive match to be notified when a new kind is added.
            match &stmt.kind {
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                    // Source is a *const T and it must be safe for read.
                    // We check that the memory at the source pointer contains valid values.
                    let src_ty = copy.src.ty(self.locals).expect("copy src type");
                    // Extract pointee type from the raw pointer type (*const T -> T)
                    if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = src_ty.kind() {
                        let validity = ty_validity_per_offset(&self.machine, pointee_ty, 0);
                        match validity {
                            Ok(base_ranges) if !base_ranges.is_empty() => {
                                // Try to evaluate count as a constant
                                let count_const = Self::constant_operand_target_usize(&copy.count);
                                match count_const {
                                    Some(count) => {
                                        // Constant count: expand ranges for all elements
                                        match Self::expand_validity_for_count(
                                            pointee_ty,
                                            &base_ranges,
                                            count,
                                        ) {
                                            Some(ranges) if !ranges.is_empty() => {
                                                self.push_target(SourceOp::DerefValidity {
                                                    pointee_ty,
                                                    rvalue: Rvalue::Use(copy.src.clone()),
                                                    ranges,
                                                });
                                            }
                                            Some(_) => {
                                                // Empty ranges (count == 0), no check needed
                                            }
                                            None => {
                                                // Overflow in range expansion
                                                self.push_target(SourceOp::UnsupportedCheck {
                                                    check: "copy_nonoverlapping",
                                                    ty: pointee_ty,
                                                });
                                            }
                                        }
                                    }
                                    None => {
                                        // Part of #698: Dynamic count - use guarded validity check.
                                        // Generates: count == 0 || validity_check(first_element)
                                        // - Passes when count == 0 (no bytes copied)
                                        // - Checks first element when count > 0 (conservative)
                                        self.push_target(SourceOp::GuardedDerefValidity {
                                            pointee_ty,
                                            rvalue: Rvalue::Use(copy.src.clone()),
                                            ranges: base_ranges,
                                            count: copy.count.clone(),
                                        });
                                    }
                                }
                            }
                            Err(_msg) => self.push_target(SourceOp::UnsupportedCheck {
                                check: "copy_nonoverlapping",
                                ty: pointee_ty,
                            }),
                            _ => {} // non-enum: Result — no validity constraints for this type
                        }
                    } else {
                        // Source is not a raw pointer (unexpected but handle gracefully)
                        self.push_target(SourceOp::UnsupportedCheck {
                            check: "copy_nonoverlapping",
                            ty: src_ty,
                        });
                    }
                }
                StatementKind::Assign(place, rvalue) => {
                    // First check rvalue.
                    self.super_statement(stmt, location);
                    // Then check the destination place.
                    let ranges = assignment_check_points(
                        &self.machine,
                        self.locals,
                        place,
                        rvalue.ty(self.locals).expect("rvalue type"),
                    );
                    if !ranges.is_empty() {
                        self.push_target(SourceOp::BytesValidity {
                            target_ty: self.locals[place.local].ty,
                            rvalue: rvalue.clone(),
                            ranges,
                        });
                    }
                }
                StatementKind::FakeRead(_, _)
                | StatementKind::SetDiscriminant { .. }
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Retag(_, _)
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType { .. }
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(_))
                | StatementKind::Nop => self.super_statement(stmt, location),
            }
        }

        let SourceInstruction::Statement { idx, bb } = self.current else {
            unreachable!("self.current must be SourceInstruction::Statement during visit_statement")
        };
        self.current = SourceInstruction::Statement { idx: idx + 1, bb };
    }
    fn visit_terminator(&mut self, term: &Terminator, location: Location) {
        if !(self.skip_next || self.target.is_some()) {
            self.current = SourceInstruction::Terminator { bb: self.bb };
            // Leave it as an exhaustive match to be notified when a new kind is added.
            match &term.kind {
                TerminatorKind::Call { func, args, .. } => {
                    // Note: For transmute, both Src and Dst must be valid type.
                    // In this case, we need to save the Dst, and invoke super_terminator.
                    self.super_terminator(term, location);
                    match intrinsic_name(self.locals, func).as_deref() {
                        Some("write_bytes") => {
                            // The write bytes intrinsic may trigger UB in safe code.
                            // pub unsafe fn write_bytes<T>(dst: *mut T, val: u8, count: usize)
                            // <https://doc.rust-lang.org/stable/core/intrinsics/fn.write_bytes.html>
                            // This is an over-approximation since writing an invalid value is
                            // not UB, only reading it will be.
                            assert_eq!(
                                args.len(),
                                3,
                                "Unexpected number of arguments for `write_bytes`"
                            );
                            if Self::constant_operand_target_usize(&args[2]) == Some(0) {
                                return;
                            }
                            let TyKind::RigidTy(RigidTy::RawPtr(target_ty, Mutability::Mut)) =
                                args[0].ty(self.locals).expect("write_bytes arg type").kind()
                            else {
                                unreachable!("write_bytes first argument must be *mut T")
                            };
                            let validity = ty_validity_per_offset(&self.machine, target_ty, 0);
                            match validity {
                                Ok(ranges) if ranges.is_empty() => {}
                                Ok(ranges) => {
                                    let sz = rustc_internal::stable(Const::from_target_usize(
                                        self.tcx,
                                        target_ty
                                            .layout()
                                            .expect("write_bytes target layout")
                                            .shape()
                                            .size
                                            .bytes() as u64,
                                    ));
                                    self.push_target(SourceOp::BytesValidity {
                                        target_ty,
                                        rvalue: Rvalue::Repeat(args[1].clone(), sz),
                                        ranges,
                                    });
                                }
                                _ => self.push_target(SourceOp::UnsupportedCheck {
                                    // non-enum: Result
                                    check: "write_bytes",
                                    ty: target_ty,
                                }),
                            }
                        }
                        Some("transmute") | Some("transmute_copy") => {
                            unreachable!("Should've been lowered")
                        }
                        _ => {} // non-enum: Option<&str> (intrinsic name)
                    }
                }
                TerminatorKind::Goto { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Return
                | TerminatorKind::Unreachable
                | TerminatorKind::Drop { .. }
                | TerminatorKind::Assert { .. }
                | TerminatorKind::InlineAsm { .. } => self.super_terminator(term, location),
            }
        }
    }

    fn visit_place(&mut self, place: &Place, ptx: PlaceContext, location: Location) {
        for (idx, elem) in place.projection.iter().enumerate() {
            let place_ref = PlaceRef { local: place.local, projection: &place.projection[..idx] };
            match elem {
                ProjectionElem::Deref => {
                    let ptr_ty = place_ref.ty(self.locals).expect("place_ref type for deref");
                    if ptr_ty.kind().is_raw_ptr() {
                        let target_ty = elem.ty(ptr_ty).expect("deref target type");
                        let validity = ty_validity_per_offset(&self.machine, target_ty, 0);
                        match validity {
                            Ok(ranges) if !ranges.is_empty() => {
                                self.push_target(SourceOp::DerefValidity {
                                    pointee_ty: target_ty,
                                    rvalue: Rvalue::Use(
                                        Operand::Copy(Place {
                                            local: place_ref.local,
                                            projection: place_ref.projection.to_vec(),
                                        })
                                        .clone(),
                                    ),
                                    ranges,
                                });
                            }
                            Err(_msg) => self.push_target(SourceOp::UnsupportedCheck {
                                check: "raw pointer dereference",
                                ty: target_ty,
                            }),
                            _ => {} // non-enum: Result — no validity constraints
                        }
                    }
                }
                ProjectionElem::Field(idx, target_ty) => {
                    if target_ty.kind().is_union()
                        && (!ptx.is_mutating() || place.projection.len() > idx + 1)
                    {
                        let validity = ty_validity_per_offset(&self.machine, *target_ty, 0);
                        match validity {
                            Ok(ranges) if !ranges.is_empty() => {
                                self.push_target(SourceOp::BytesValidity {
                                    target_ty: *target_ty,
                                    rvalue: Rvalue::Use(Operand::Copy(Place {
                                        local: place_ref.local,
                                        projection: place_ref.projection.to_vec(),
                                    })),
                                    ranges,
                                });
                            }
                            Err(_msg) => self.push_target(SourceOp::UnsupportedCheck {
                                check: "union access",
                                ty: *target_ty,
                            }),
                            _ => {} // non-enum: Result — no validity constraints
                        }
                    }
                }
                ProjectionElem::Downcast(_) => {}
                ProjectionElem::OpaqueCast(_) => {}
                ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => { /* safe */ }
            }
        }
        self.super_place(place, ptx, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        match rvalue {
            Rvalue::Cast(kind, op, dest_ty) => match kind {
                CastKind::PtrToPtr => {
                    // For mutable raw pointer, if the type we are casting to is less restrictive
                    // than the original type, writing to the pointer could generate UB if the
                    // value is ever read again using the original pointer.
                    let TyKind::RigidTy(RigidTy::RawPtr(dest_pointee_ty, Mutability::Mut)) =
                        dest_ty.kind()
                    else {
                        // We only care about *mut T as *mut U
                        return;
                    };
                    if dest_pointee_ty.kind().is_unit() {
                        // Ignore cast to *mut () since nothing can be written to it.
                        // This is a common pattern
                        return;
                    }

                    let src_ty = op.ty(self.locals).expect("src type for ptr cast");
                    debug!(?src_ty, ?dest_ty, "visit_rvalue mutcast");
                    let TyKind::RigidTy(RigidTy::RawPtr(src_pointee_ty, _)) = src_ty.kind() else {
                        unreachable!("source of PtrToPtr cast to *mut T must be a raw pointer")
                    };

                    if src_pointee_ty.kind().is_unit() {
                        // We cannot track what was the initial type. Thus, fail.
                        self.push_target(SourceOp::UnsupportedCheck {
                            check: "mutable cast",
                            ty: src_ty,
                        });
                        return;
                    }

                    if let Ok(src_validity) =
                        ty_validity_per_offset(&self.machine, src_pointee_ty, 0)
                    {
                        if !src_validity.is_empty() {
                            if let Ok(dest_validity) =
                                ty_validity_per_offset(&self.machine, dest_pointee_ty, 0)
                            {
                                if dest_validity != src_validity {
                                    self.push_target(SourceOp::UnsupportedCheck {
                                        check: "mutable cast",
                                        ty: src_ty,
                                    });
                                }
                            } else {
                                self.push_target(SourceOp::UnsupportedCheck {
                                    check: "mutable cast",
                                    ty: *dest_ty,
                                });
                            }
                        }
                    } else {
                        self.push_target(SourceOp::UnsupportedCheck {
                            check: "mutable cast",
                            ty: src_ty,
                        });
                    }
                }
                CastKind::Transmute | CastKind::Subtype => {
                    debug!(?dest_ty, "transmute");
                    // For transmute, we care about the destination type only.
                    // This could be optimized to only add a check if the requirements of the
                    // destination type are stricter than the source.
                    if let Ok(dest_validity) = ty_validity_per_offset(&self.machine, *dest_ty, 0) {
                        trace!(?dest_validity, "transmute");
                        if !dest_validity.is_empty() {
                            self.push_target(SourceOp::BytesValidity {
                                target_ty: *dest_ty,
                                rvalue: rvalue.clone(),
                                ranges: dest_validity,
                            });
                        }
                    } else {
                        self.push_target(SourceOp::UnsupportedCheck {
                            check: "transmute",
                            ty: *dest_ty,
                        });
                    }
                }
                CastKind::PointerExposeAddress
                | CastKind::PointerWithExposedProvenance
                | CastKind::PointerCoercion(_)
                | CastKind::IntToInt
                | CastKind::FloatToInt
                | CastKind::FloatToFloat
                | CastKind::IntToFloat
                | CastKind::FnPtrToPtr => {}
            },
            Rvalue::ShallowInitBox(_, _) => {
                // The contents of the box is considered uninitialized.
                // This should already be covered by the Assign detection.
            }
            Rvalue::Aggregate(kind, operands) => match kind {
                // If the aggregated structure has invalid value, this could generate invalid value.
                // But only if the operands don't have the exact same restrictions.
                // This happens today with the usage of `rustc_layout_scalar_valid_range_*`
                // attributes.
                // In this case, only the value of the first member in memory can be restricted,
                // thus, we only need to check the operand used to assign to the first in memory
                // field.
                AggregateKind::Adt(def, _variant, args, _, _) => {
                    if def.kind() == AdtKind::Struct {
                        let dest_ty = Ty::from_rigid_kind(RigidTy::Adt(*def, args.clone()));
                        if let Some(req) = ValidValueReq::try_from_ty(&self.machine, dest_ty)
                            && !req.is_full()
                        {
                            let dest_layout = dest_ty.layout().expect("dest_ty layout").shape();
                            let first_op =
                                first_aggregate_operand(dest_ty, &dest_layout.fields, operands);
                            let first_ty = first_op.ty(self.locals).expect("first_op type");
                            // Rvalue must have same Abi layout except for range.
                            if !req.contains(
                                &ValidValueReq::try_from_ty(&self.machine, first_ty)
                                    .expect("first_ty validity req"),
                            ) {
                                self.push_target(SourceOp::BytesValidity {
                                    target_ty: dest_ty,
                                    rvalue: Rvalue::Use(first_op),
                                    ranges: vec![req],
                                });
                            }
                        }
                    }
                }
                // Only aggregate value.
                AggregateKind::Array(_)
                | AggregateKind::Closure(_, _)
                | AggregateKind::Coroutine(_, _)
                | AggregateKind::CoroutineClosure(_, _)
                | AggregateKind::RawPtr(_, _)
                | AggregateKind::Tuple => {}
            },
            Rvalue::AddressOf(_, _)
            | Rvalue::BinaryOp(_, _, _)
            | Rvalue::CheckedBinaryOp(_, _, _)
            | Rvalue::CopyForDeref(_)
            | Rvalue::Discriminant(_)
            | Rvalue::Len(_)
            | Rvalue::Ref(_, _, _)
            | Rvalue::Repeat(_, _)
            | Rvalue::ThreadLocalRef(_)
            | Rvalue::NullaryOp(_)
            | Rvalue::UnaryOp(_, _)
            | Rvalue::Use(_) => {}
        }
        self.super_rvalue(rvalue, location);
    }
}
