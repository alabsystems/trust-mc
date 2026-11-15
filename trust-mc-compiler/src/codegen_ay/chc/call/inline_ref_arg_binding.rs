// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! What a reference argument of an inlined callee binds to.
//!
//! The inline walker models references transparently: the term bound to a
//! `&T` parameter is read AS the `T` datum. `*_1` is identity, and a bare
//! bitvector left over is unflattened into `T`'s datatype
//! (`resolve_projected_place`). The referent cascade
//! (`resolve_ref_or_const_referent_tagged`) keeps that contract whenever a tier
//! dereferences, and says so with `Referent::Value`. When no tier does, it hands
//! back the operand's OWN term, `Referent::Unreported`, which at the Mem track
//! level is the reference's ADDRESS.
//!
//! Bound as a parameter, that address was decoded as the referent. For an enum
//! the tag came out of the bits of `concat(obj_id, offset)`; the
//! literal-constructor fast path (#4290) turned the decoded constructor into a
//! constant discriminant, `const_fold_switch_target` walked a single arm, and
//! nothing was recorded. Under `--ay-chc` that PROVED `!(a == b)` for an Option
//! that more than one branch assigned: the producers of `a` clear the `&a`
//! points-at edge (f1f2079d1), Tier 5 answers with the address, and
//! `<Option<T> as PartialEq>::eq` compared pointer bits
//! (`tools/soundness-duals/negative/eq_joined_option_false_proof.rs`).
//!
//! The decision here uses facts the binder has — the `Referent` tag, the
//! operand's MIR type, the pointee's translated sort and the track level —
//! never a width test:
//!
//! * the pointee carries no enum encoding the walker would decode, or the term
//!   already has the pointee's sort (value semantics below Mem): bind the term,
//!   exactly as before;
//! * a shared, `Freeze` referent at the Mem track level: bind the value read
//!   from typed memory THROUGH the address term. That term is the reference's
//!   own path-sensitive value (its state variable, or the constant address its
//!   single producer wrote in this block), so a reference joined from several
//!   borrows reads the borrow its path took;
//! * anything else — `&mut`, interior mutability, no memory model, a load that
//!   fails or yields another sort — refuses the inline. The call then reaches
//!   the later dispatchers and, failing those, the fail-closed
//!   `call_dispatch_fallback`.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, ExprValue, Sort, SortInner};
use rustc_public::mir::{Mutability, Operand};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::args::ChcTrackLevel;
use crate::codegen_ay::provenance::{Loc, mir_ty_denotes_address};

use super::ChcCtx;
use super::codegen_call_misc::Referent;
use super::codegen_expr_constant::ExprConstant;
use super::codegen_types::CodegenTypes;

/// How deep [`enum_placement`] and [`ty_holds_address`] look into a type.
/// Past it both answer conservatively (an enum is assumed, an address is
/// assumed), which only ever routes a shape to the more careful arm.
pub(in crate::codegen_ay::chc) const SHAPE_DEPTH: usize = 8;

/// What an inlined callee's argument binds to.
pub(in crate::codegen_ay::chc) enum InlineArgBinding {
    /// The term the cascade produced, unchanged.
    Bound(Expr),
    /// The cascade explicitly resolved this reference to its referent value.
    /// Keep this authority separate from an unreported pointer-shaped term.
    BoundReferent(Expr),
    /// The cascade's own term for a reference whose referent it did not
    /// resolve (`Referent::Unreported`), bound unchanged although it is, or may
    /// be, the reference's ADDRESS: at the Mem track level an unreported term is
    /// the address whatever its width, and below it a term of another sort than
    /// the referent is not the referent. The walker reads a bound reference as
    /// its referent, so the binder reports it (F2, `inline_walk_guard.rs`) and
    /// a transparent read of it fails closed.
    BoundAddress(Expr),
    /// The referent value, read from typed memory through the reference's
    /// address. The walker must take this as the whole referent: receiver
    /// field hints derived from a pointer-identity trace do not apply to it.
    ReadThrough(Expr),
    /// Nothing resolved the operand; the caller's placeholder/skip logic runs.
    Unresolved,
    /// The operand resolved only to a term the walker would misread. The
    /// inline must not proceed; the reason names the construct.
    Refused(&'static str),
}

/// Where a multi-constructor datatype — the encoding of an enum — sits in a
/// sort.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum EnumPlacement {
    /// No enum encoding anywhere the walker would decode one.
    Absent,
    /// The sort itself is an enum encoding (`Option`, `Result`, a user enum).
    Top,
    /// A single-constructor datatype (tuple, struct) holds one in a field, or
    /// an array holds them as elements.
    Nested,
}

/// Classify `sort` by where an enum encoding sits in it.
pub(in crate::codegen_ay::chc) fn enum_placement(sort: &Sort) -> EnumPlacement {
    match sort.inner() {
        SortInner::Datatype(dt) if dt.constructors.len() >= 2 => EnumPlacement::Top,
        SortInner::Datatype(_) | SortInner::Array(_) if sort_holds_enum(sort, SHAPE_DEPTH) => {
            EnumPlacement::Nested
        }
        _ => EnumPlacement::Absent,
    }
}

/// Does an enum encoding occur anywhere in `sort`? Conservative past `depth`.
fn sort_holds_enum(sort: &Sort, depth: usize) -> bool {
    if depth == 0 {
        return true;
    }
    match sort.inner() {
        SortInner::Datatype(dt) => {
            dt.constructors.len() >= 2
                || dt
                    .constructors
                    .iter()
                    .flat_map(|ctor| ctor.fields.iter())
                    .any(|field| sort_holds_enum(&field.sort, depth - 1))
        }
        SortInner::Array(arr) => sort_holds_enum(&arr.element_sort, depth - 1),
        _ => false,
    }
}

/// Does a value of `ty` hold an address anywhere (a reference, raw pointer or
/// pointer wrapper), or is it a shape this module does not classify (a union,
/// a slice, a closure, an unnormalized alias, ...)? Conservative: `true`
/// whenever it cannot say `false`.
pub(in crate::codegen_ay::chc) fn ty_holds_address(
    ctx: &ChcCtx<'_, '_>,
    ty: Ty,
    depth: usize,
) -> bool {
    if depth == 0 {
        return true;
    }
    let ty = ctx.resolve_body_ty(ty);
    if mir_ty_denotes_address(ty) {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_),
        ) => false,
        TyKind::RigidTy(RigidTy::Array(elem, _)) => ty_holds_address(ctx, elem, depth - 1),
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().any(|elem| ty_holds_address(ctx, *elem, depth - 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
            AdtKind::Union => true,
            AdtKind::Enum | AdtKind::Struct => def.variants_iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    mono_ty::field_ty(field, &args)
                        .is_none_or(|t| ty_holds_address(ctx, t, depth - 1))
                })
            }),
        },
        _ => true,
    }
}

/// Is `path` a method of `PartialEq`, `PartialOrd` or `Ord` — the trait
/// methods themselves, or the tuple, array and blanket-reference impls?
pub(in crate::codegen_ay::chc) fn is_comparison_callee_path(path: &str) -> bool {
    path.contains("cmp::PartialEq") || path.contains("cmp::PartialOrd") || path.contains("cmp::Ord")
}

/// Does a value of `ty` hold a REFERENCE anywhere (`&T`, `&mut T`), or is it a
/// shape this module cannot classify? Raw pointers and the std pointer
/// wrappers built on them (`Vec`, `Box`, `String`) are compared by their own
/// lanes and answer `false` unless they hold a reference themselves.
fn ty_holds_reference(ctx: &ChcCtx<'_, '_>, ty: Ty, depth: usize) -> bool {
    if depth == 0 {
        return true;
    }
    let ty = ctx.resolve_body_ty(ty);
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(..)) => true,
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::RawPtr(..)
            | RigidTy::Str
            | RigidTy::Never,
        ) => false,
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
            ty_holds_reference(ctx, elem, depth - 1)
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().any(|elem| ty_holds_reference(ctx, *elem, depth - 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
            AdtKind::Union => true,
            AdtKind::Enum | AdtKind::Struct => def.variants_iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    mono_ty::field_ty(field, &args)
                        .is_none_or(|t| adt_field_holds_reference(ctx, t, depth - 1))
                })
            }),
        },
        _ => true,
    }
}

/// Does an ADT field of type `field_ty` hold a reference the comparison lanes
/// could compare as an address?
///
/// An ADT field of reference type is modeled by VALUE (`deref_ref_ty_sized_only`
/// declares the payload slot of `Option<&T>` with `T`'s sort), so the slot holds
/// the referent's datum, not an address. When that referent is the unit type
/// `()` or `!`, the datum is the one canonical unit constant
/// (`canonical_zst_expr`: `translate_ty` gives both the Bool sort, and a decoded
/// constant `Some(&())` is `Some(true)`), and `*l == *r` is `() == ()`, true:
/// there is no address anywhere in the field for a lane to compare, and SMT
/// equality over the slots is `PartialEq`. `[(); 10].first() == Some(&())` is
/// that shape (test_call_slice_zst_first). Any other referent keeps counting,
/// and so does a `&()` in a tuple or an array, whose element slots `translate_ty`
/// gives the pointer sort.
fn adt_field_holds_reference(ctx: &ChcCtx<'_, '_>, field_ty: Ty, depth: usize) -> bool {
    let field_ty = ctx.resolve_body_ty(field_ty);
    if let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = field_ty.kind()
        && ty_is_unit_like(ctx, pointee)
    {
        return false;
    }
    ty_holds_reference(ctx, field_ty, depth)
}

/// Is `ty` the unit type `()` or the never type `!` — a ZST with exactly one
/// inhabitant (or none) and the built-in `PartialEq` that compares equal?
fn ty_is_unit_like(ctx: &ChcCtx<'_, '_>, ty: Ty) -> bool {
    match ctx.resolve_body_ty(ty).kind() {
        TyKind::RigidTy(RigidTy::Tuple(elems)) => elems.is_empty(),
        TyKind::RigidTy(RigidTy::Never) => true,
        _ => false,
    }
}

/// For a comparison call whose first operand has type `&T`: is `T`, below every
/// reference level, the unit type? `<&() as PartialEq<&()>>::eq` is `*l == *r`,
/// `() == ()`: `true` whatever addresses the two references hold, so the
/// comparison has a constant answer and no address to compare. The nested
/// inline of the `Some(&()) == Some(&())` arm of `Option<&()>::eq` is that call
/// (test_call_slice_zst_first).
pub(in crate::codegen_ay::chc) fn comparison_referent_is_unit_like(
    ctx: &ChcCtx<'_, '_>,
    first_arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    let Ok(arg_ty) = first_arg.ty(locals) else {
        return false;
    };
    let mut compared = ctx.resolve_body_ty(arg_ty);
    let mut peeled = 0;
    while let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = compared.kind() {
        if peeled == SHAPE_DEPTH {
            return false;
        }
        compared = ctx.resolve_body_ty(pointee);
        peeled += 1;
    }
    peeled > 0 && ty_is_unit_like(ctx, compared)
}

/// Is `arg` a reference whose referent the declaration pre-pass decoded as a
/// constant FIELDLESS variant — the `&None` of `first(&a) == None`, a unit
/// variant of a user enum?
fn operand_is_const_ref_to_fieldless_variant(ctx: &ChcCtx<'_, '_>, arg: &Operand) -> bool {
    let (Operand::Copy(place) | Operand::Move(place)) = arg else {
        return false;
    };
    if !place.projection.is_empty() {
        return false;
    }
    ctx.ref_resolution.const_ref_values.get(&place.local).is_some_and(|expr| {
        matches!(expr.value(), ExprValue::DatatypeConstructor { args, .. } if args.is_empty())
    })
}

/// Does a comparison call compare against a constant fieldless variant?
///
/// `PartialEq` on an enum compares the discriminants first and reaches the
/// fields of a variant only when both sides are that variant; a fieldless
/// variant has none. So whatever reference a payload of the other side holds,
/// no referent is compared: the result is the discriminant test, and the lanes
/// that fail a reference-holding comparison closed
/// (`comparison_value_holds_nested_reference`,
/// `comparison_referent_holds_reference`) have nothing to protect here.
/// `assert_eq!(a.first(), None)` and `v.get(i) != None` are this shape.
pub(in crate::codegen_ay::chc) fn comparison_against_fieldless_variant_constant(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
) -> bool {
    args.iter().take(2).any(|arg| operand_is_const_ref_to_fieldless_variant(ctx, arg))
}

/// For a comparison call (`PartialEq::eq(&T, &T)` and the other methods of
/// the comparison traits) whose first operand has type `&T`: is `T` a sized
/// type that holds a reference?
///
/// Comparing such a `T` compares REFERENTS (`(&o, 1) == (&c, 1)` ends in
/// `*self.0 == *other.0`, `<&Option<u8> as PartialEq>::eq` in `**self ==
/// **other`). Every encoding lane for those calls that is not a dedicated one
/// ended up comparing ADDRESSES: the flattened-tuple dispatch with SMT
/// equality, and the inline walker, whose nested comparison of the
/// memory-backed fields handed the known-call fast path two pointers, which
/// proved `!((&o, 1u8) == (&c, 1u8))` with `o == c`
/// (tools/soundness-duals/negative/review_r03_ref_in_aggregate.rs). Such a
/// call is not inlined; it reaches the fail-closed fallback. `str`, slice and
/// `dyn` referents are compared by their own lanes and answer `false`.
pub(in crate::codegen_ay::chc) fn comparison_referent_holds_reference(
    ctx: &ChcCtx<'_, '_>,
    first_arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    let Ok(arg_ty) = first_arg.ty(locals) else {
        return false;
    };
    let compared = match ctx.resolve_body_ty(arg_ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ctx.resolve_body_ty(pointee),
        _ => return false,
    };
    let unsized_referent = |ty: Ty| {
        matches!(
            ctx.resolve_body_ty(ty).kind(),
            TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_) | RigidTy::Dynamic(..))
        )
    };
    if unsized_referent(compared) {
        return false;
    }
    if let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = compared.kind()
        && unsized_referent(inner)
    {
        return false;
    }
    ty_holds_reference(ctx, compared, SHAPE_DEPTH)
}

/// For a comparison call whose first operand is `&T`, `&&T`, ...: once every
/// leading reference level is peeled (the levels the comparison lanes load
/// through), does the compared value still hold a REFERENCE?
///
/// `PartialEq` on such a value compares referents (`(&o, 1) == (&c, 1)` ends
/// in `*self.0 == *other.0`, `Option<&u8>` in `*l == *r`); the operands the
/// primitive comparison lanes build hold the reference values, i.e.
/// addresses. `str` and `dyn` referents are compared by their own lanes and
/// answer `false`; a slice answers for its element.
pub(in crate::codegen_ay::chc) fn comparison_value_holds_nested_reference(
    ctx: &ChcCtx<'_, '_>,
    first_arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    let Ok(arg_ty) = first_arg.ty(locals) else {
        return false;
    };
    let mut compared = ctx.resolve_body_ty(arg_ty);
    let mut peeled = 0;
    while let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = compared.kind() {
        if peeled == SHAPE_DEPTH {
            return true;
        }
        compared = ctx.resolve_body_ty(pointee);
        peeled += 1;
    }
    match compared.kind() {
        TyKind::RigidTy(RigidTy::Str | RigidTy::Dynamic(..)) => false,
        TyKind::RigidTy(RigidTy::Slice(elem)) => ty_holds_reference(ctx, elem, SHAPE_DEPTH),
        _ => ty_holds_reference(ctx, compared, SHAPE_DEPTH),
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Decide what the inline walker's parameter for `arg` binds to, given what
    /// the referent cascade answered for it. See the module documentation.
    ///
    /// `comparison_callee` is set for a method of `PartialEq`, `PartialOrd` or
    /// `Ord`. Such a callee compares its arguments' REFERENTS, so a reference
    /// argument the cascade answered with the reference's own address binds to
    /// the referent read through that address whatever the referent's shape, or
    /// the inline is refused: bound to the address, `&(*other).0` in the body
    /// became an address the comparison fast paths compared as a value.
    pub(in crate::codegen_ay::chc) fn bind_inline_referent_arg(
        &mut self,
        arg: &Operand,
        referent: Referent,
        comparison_callee: bool,
    ) -> InlineArgBinding {
        let term = match referent {
            Referent::Value(val) => {
                return if self.reference_pointee(arg).is_some() {
                    InlineArgBinding::BoundReferent(val.into_expr())
                } else {
                    InlineArgBinding::Bound(val.into_expr())
                };
            }
            Referent::Unreported(term) => term,
        };
        let Some((pointee_ty, mutability)) = self.reference_pointee(arg) else {
            return InlineArgBinding::Bound(term);
        };
        let Some(pointee_sort) = Self::translate_ty(pointee_ty) else {
            return self.bind_unreported_term(term, None);
        };
        // A comparison reads a plain referent through its address; at the Mem
        // track level an unreported term is that address even when its width is
        // the referent's (`&u64`).
        let comparison_read = comparison_callee
            && self.track_level >= ChcTrackLevel::Mem
            && !ty_holds_address(self, pointee_ty, SHAPE_DEPTH);
        match enum_placement(&pointee_sort) {
            EnumPlacement::Absent if !comparison_read => {
                return self.bind_unreported_term(term, Some(&pointee_sort));
            }
            // A carrier that also holds addresses (a Vec of Options, a struct
            // with a Box) keeps its pointer binding: its collection and field-map
            // lanes read through the address, and typed memory does not hold its
            // shadow state. Only plain aggregates are read through here.
            EnumPlacement::Nested if ty_holds_address(self, pointee_ty, SHAPE_DEPTH) => {
                return self.bind_unreported_term(term, Some(&pointee_sort));
            }
            EnumPlacement::Absent | EnumPlacement::Top | EnumPlacement::Nested => {}
        }
        // The cascade's own term already denotes the datum (value semantics,
        // e.g. below the Mem track level): nothing to decode.
        let address_width =
            pointee_sort.bitvec_width() == Some(crate::codegen_ay::types::POINTER_WIDTH);
        if *term.sort() == pointee_sort && !(comparison_read && address_width) {
            return self.bind_unreported_term(term, Some(&pointee_sort));
        }
        // From here the term is not the referent, and the walker would decode
        // it as one.
        if mutability == Mutability::Mut {
            // A value snapshot would drop the callee's writes; the address lane
            // is the one that misreads. Neither is sound to walk.
            return InlineArgBinding::Refused("inline_ref_arg_mut_referent_unresolved");
        }
        if self.ty_has_interior_mut(pointee_ty) {
            return InlineArgBinding::Refused("inline_ref_arg_referent_interior_mutable");
        }
        if self.track_level < ChcTrackLevel::Mem {
            return InlineArgBinding::Refused("inline_ref_arg_referent_no_memory_model");
        }
        let value = match arg {
            Operand::Constant(const_op) => self.translate_constant_referent(const_op),
            // The typed-memory cell must already hold the referent's sort. A
            // layout-width cell unflattened into the datatype is not the
            // referent: `Option<Ordering>` sits in one byte, and its bits
            // decoded as `(is_some, payload)` compared unequal to the
            // `Some(Ordering::Less)` it held.
            _ => self
                .load_from_memory(Loc::of_address(term), pointee_ty)
                .map(|loaded| loaded.into_expr()),
        };
        match value {
            Some(value) if *value.sort() == pointee_sort => {
                debug!(
                    fn_name = %self.fn_name,
                    ?pointee_ty,
                    "fn_inline: reference argument bound to its referent read through the address"
                );
                InlineArgBinding::ReadThrough(value)
            }
            Some(_) => InlineArgBinding::Refused("inline_ref_arg_referent_sort_mismatch"),
            None => InlineArgBinding::Refused("inline_ref_arg_referent_unreadable"),
        }
    }

    /// Bind an unreported reference term unchanged, reporting it as an address
    /// ([`InlineArgBinding::BoundAddress`]) when it has a pointer's shape and
    /// is not established as the referent: at the Mem track level, or when its
    /// sort is not the referent's.
    fn bind_unreported_term(&self, term: Expr, pointee_sort: Option<&Sort>) -> InlineArgBinding {
        let pointer_shaped =
            crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(&term).is_some();
        let not_the_referent = self.track_level >= ChcTrackLevel::Mem
            || pointee_sort.is_none_or(|sort| term.sort() != sort);
        if pointer_shaped && not_the_referent {
            InlineArgBinding::BoundAddress(term)
        } else {
            InlineArgBinding::Bound(term)
        }
    }

    /// The pointee type and mutability of a `&T` / `&mut T` operand.
    fn reference_pointee(&self, arg: &Operand) -> Option<(Ty, Mutability)> {
        let ty = self.resolve_body_ty(arg.ty(self.body.locals()).ok()?);
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, mutability)) => {
                Some((self.resolve_body_ty(pointee), mutability))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{EnumPlacement, enum_placement};
    use ay_bindings::Sort;

    fn option_u8() -> Sort {
        Sort::enum_type(
            "Option_u8",
            vec![
                ("None_Option_u8", vec![]),
                ("Some_Option_u8", vec![("value_Option_u8", Sort::bitvec(8))]),
            ],
        )
    }

    #[test]
    fn an_enum_encoding_is_top() {
        assert_eq!(enum_placement(&option_u8()), EnumPlacement::Top);
        let unit_only = Sort::simple_enum_type("Color", ["R", "G", "B"]);
        assert_eq!(enum_placement(&unit_only), EnumPlacement::Top);
    }

    #[test]
    fn aggregates_holding_an_enum_are_nested() {
        let tuple = Sort::tuple(vec![option_u8(), Sort::bitvec(8)]);
        assert_eq!(enum_placement(&tuple), EnumPlacement::Nested);
        let wrapper = Sort::struct_type("W", vec![("o", option_u8())]);
        assert_eq!(enum_placement(&wrapper), EnumPlacement::Nested);
        let array = Sort::array(Sort::bitvec(64), option_u8());
        assert_eq!(enum_placement(&array), EnumPlacement::Nested);
    }

    #[test]
    fn scalars_and_plain_structs_are_absent() {
        assert_eq!(enum_placement(&Sort::bitvec(64)), EnumPlacement::Absent);
        assert_eq!(enum_placement(&Sort::bool()), EnumPlacement::Absent);
        let pair = Sort::struct_type("S", vec![("a", Sort::bitvec(8)), ("b", Sort::bitvec(16))]);
        assert_eq!(enum_placement(&pair), EnumPlacement::Absent);
        let bytes = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        assert_eq!(enum_placement(&bytes), EnumPlacement::Absent);
    }
}
