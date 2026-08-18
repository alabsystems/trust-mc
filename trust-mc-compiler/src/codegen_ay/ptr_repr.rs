// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! `PtrRepr`: which *shape* of pointer is this bitvector?
//!
//! # Why this exists
//!
//! [`Val`] and [`Loc`] answer "is this an address or a value?". They cannot
//! answer the question the fat-pointer decoders ask, because a wide pointer is
//! *both*: a data address **and** a metadata value packed into one `bv128`.
//! Worse, the packed form is **bit-identical** to a thin `bv64` address that was
//! widened into the same slot by `coerce_bitvec_width_safe` — and that widening
//! happens far from every consumer that later asks "is bit 127..64 a slice
//! length?".
//!
//! Six sites across `codegen_ay` used to answer that question by measuring the
//! width:
//!
//! ```text
//! if e.sort().bitvec_width() == Some(2 * POINTER_WIDTH) { e.extract(127, 64) }
//! ```
//!
//! For a widened thin pointer the high half is extension padding, so the
//! "metadata" is fabricated — reliably `0` for a zero-extension. A length of `0`
//! makes `size_of_val`, `len()` and bounds obligations trivially satisfiable, so
//! the fabrication can manufacture a **PROOF**, not merely a spurious
//! counterexample. That is the defect behind the BV128 fat-pointer metadata
//! soundness fix; the ad-hoc `is_fabricated_fat_ptr_metadata` escape hatch that
//! fix added was evidence the fact could not be recovered locally.
//!
//! `PtrRepr` promotes that escape hatch to a first-class tagged enum, decoded
//! **once**, in one place, structurally — never by width alone.
//!
//! # The three shapes
//!
//! | variant | when | data | metadata |
//! |---|---|---|---|
//! | [`PtrRepr::Thin`] | width == `POINTER_WIDTH` | the expression itself | none — a thin pointer has none |
//! | [`PtrRepr::Fat`] | `bv64‖bv64` concat, or an opaque `bv128` | low half | high half — the program's own |
//! | [`PtrRepr::WidenedThin`] | an extension node over `<= 64` bits, or a `bv128` constant with a zero high half | low half | **none** — the high half is padding |
//!
//! The data address is available from **all three** (a widened thin pointer
//! still points somewhere), so [`PtrRepr::data`] is total. Metadata is available
//! from `Fat` **only**, so [`PtrRepr::metadata`] returns `Option<&Val>` and the
//! fabrication is unrepresentable rather than merely discouraged.
//!
//! # Deliberate imprecision
//!
//! A `bv128` constant whose high half is zero is classified `WidenedThin` even
//! though it *could* be a genuine fat pointer to an empty slice: constant
//! folding erases the extension node, so the two are indistinguishable here.
//! Refusing costs precision (a havoced length, hence a possible spurious
//! counterexample); trusting costs soundness (a fabricated proof). This is the
//! same trade the ad-hoc predicate made, preserved verbatim.
//!
//! # Consumers (wave 4)
//!
//! Wave 3 built the decoders; wave 4 converted the sites that *read* the result,
//! which is where the fabrication actually did damage:
//!
//! * `extract_embedded_vtable_expr` and the `pointer_wrapper_deref` vtable
//!   fallback used to hand back padding as a **vtable id**, pinning dynamic
//!   dispatch to whichever impl carried it;
//! * `collect_box_dyn_dealloc_effects` and `shared_pointer_storage_expr` chose
//!   which half names the object being **freed**;
//! * the two `raw_pointer_*_components` decoders **ordered** pointers on the
//!   padding, and now decline a mixed fat/widened comparison instead.
//!
//! [`PtrRepr::into_packed`] is the write side of the same fact: it states the
//! `[metadata : upper | data : lower]` layout once, so the sites that build a
//! wide pointer from declared datatype roles cannot transpose the two halves.

use ay_bindings::{Expr, ExprValue, Sort};

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::types::POINTER_WIDTH;

/// Which pointer shape does a **declared sort** describe?
///
/// # Sort, not expression — and only for a slot already known to be a pointer
///
/// [`PtrRepr::classify`] inspects an *expression* and has to work structurally,
/// because a `bv128` that was widened from a thin address is bit-identical to a
/// genuine fat pointer. `PtrSlot` asks a strictly narrower question of a
/// *declaration*: `translate_ty` mapped a pointer-typed place to this sort, so
/// how wide did it make the slot — one word (thin) or two (data + metadata)?
///
/// That is a **representation** question with a definite answer, in the same
/// sense as [`crate::codegen_ay::provenance::is_transparent_pointer_wrapper_repr`],
/// and unlike a width test on an expression it cannot be fooled by widening:
/// nothing widens a sort. It does **not** answer "is this an address?" — the
/// caller must already know that from the Rust type of the place, which at both
/// current call sites is a `Ref`/`RawPtr` matched out of `TyKind`.
///
/// # Why it is shared
///
/// Wave 8: the static/const decoder classified the same declared pointer sort in
/// two places with two inline copies of `w == POINTER_WIDTH` /
/// `w == 2 * POINTER_WIDTH` — one deciding whether provenance resolution runs at
/// all (`collect_static_state_vars`), one deciding whether to pack metadata
/// alongside the resolved address (`read_pointer_like_from_allocation`). If those
/// two drift, a static is resolved as thin on one path and read back as fat on
/// the other, which is the fat-pointer half of the slot-misalignment shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PtrSlot {
    /// One machine word: the address, and no metadata exists.
    Thin,
    /// Two machine words: `[metadata : upper | data : lower]`.
    Fat,
}

impl PtrSlot {
    /// Classifies the sort `translate_ty` produced for a pointer-typed place.
    ///
    /// `None` for any other width, which every caller treats as "not a pointer
    /// slot I can decode" and falls through.
    pub(crate) fn of_sort(sort: &Sort) -> Option<Self> {
        let width = sort.bitvec_width()?;
        if width == POINTER_WIDTH {
            Some(Self::Thin)
        } else if width == 2 * POINTER_WIDTH {
            Some(Self::Fat)
        } else {
            None
        }
    }
}

/// The decoded representation of a pointer-shaped bitvector.
#[derive(Clone, Debug)]
pub(crate) enum PtrRepr {
    /// A `POINTER_WIDTH` address. No metadata exists.
    Thin(Loc),
    /// A genuine wide pointer: `(data, metadata)` the program actually computed.
    Fat { data: Loc, meta: Val },
    /// A thin address widened into a `2 * POINTER_WIDTH` slot. The high half is
    /// extension padding; reading it as metadata fabricates a value the program
    /// never computed.
    WidenedThin(Loc),
}

impl PtrRepr {
    /// Decodes a pointer-shaped expression.
    ///
    /// The **caller** asserts that `expr` denotes a pointer (it came from a
    /// pointer-typed place, a `from_raw` argument, a reference referent, ...).
    /// This function decides only *which shape* it is, and it decides that
    /// **structurally** — never from the width alone, which is exactly the test
    /// that cannot separate `Fat` from `WidenedThin`.
    ///
    /// Returns `None` when the expression is not pointer-shaped at all (some
    /// other width, or not a bitvector), which every caller treats as
    /// "not applicable" and falls through.
    pub(crate) fn classify(expr: &Expr) -> Option<Self> {
        let width = expr.sort().bitvec_width()?;
        if width == POINTER_WIDTH {
            return Some(Self::Thin(Loc::of_address(expr.clone())));
        }
        if width != 2 * POINTER_WIDTH {
            return None;
        }

        let low_half = || Loc::of_address(expr.clone().extract(POINTER_WIDTH - 1, 0));

        match expr.value() {
            // Structural fat pointer: `concat(metadata, data)`. Both halves are
            // recovered as sub-expressions rather than re-extracted, which is
            // what the `split_fat_pointer_expr` decoder this replaces already
            // did — a constant length stays syntactically constant.
            ExprValue::BvConcat(metadata, data_ptr)
                if metadata.sort().bitvec_width() == Some(POINTER_WIDTH)
                    && data_ptr.sort().bitvec_width() == Some(POINTER_WIDTH) =>
            {
                Some(Self::Fat {
                    data: Loc::of_address(data_ptr.clone()),
                    meta: Val::of_value(metadata.clone()),
                })
            }
            // Widened thin pointer, un-folded form: the extension node survives
            // when the address is symbolic.
            ExprValue::BvZeroExtend { expr: inner, .. }
            | ExprValue::BvSignExtend { expr: inner, .. }
                if inner.sort().bitvec_width().is_some_and(|w| w <= POINTER_WIDTH) =>
            {
                Some(Self::WidenedThin(low_half()))
            }
            // Widened thin pointer, folded form: constant folding erased the
            // extension node, so matching on the node alone would miss it.
            ExprValue::BitVecConst { value, width: const_width }
                if *const_width == 2 * POINTER_WIDTH
                    && (value >> POINTER_WIDTH) == num_bigint::BigInt::from(0) =>
            {
                Some(Self::WidenedThin(low_half()))
            }
            // Opaque `bv128`: no evidence of widening, so the high half is the
            // program's own metadata.
            _ => Some(Self::Fat {
                data: low_half(),
                meta: Val::of_value(expr.clone().extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH)),
            }),
        }
    }

    /// The address of a pointer term the caller knows must be **thin**.
    ///
    /// # The caller supplies the provenance, this supplies the shape
    ///
    /// The caller must already have established, *from the MIR type*, that
    /// `expr` is a pointer's own term — the value of a `*const T` / `&T` local,
    /// or the base of a `Deref` step through one. This function does not decide
    /// that and cannot: a bare `bv64` is equally a `usize`, which is the whole
    /// reason [`Loc`] exists. What it decides is which *shape* the pointer has,
    /// and it accepts only the thin one.
    ///
    /// # Why a wide pointer is declined rather than split
    ///
    /// Every current caller is a scalar load site (`load_from_memory` on the
    /// pointee type) or byte-offset address arithmetic. A wide pointer reaching
    /// one of those means the projection and the pointee disagree about width,
    /// and all of them decline it today. Silently substituting `data()` here
    /// would drop the metadata on the floor at a site that never reasoned about
    /// metadata — a behaviour change, not a retyping.
    ///
    /// # What it replaces
    ///
    /// The bare `sort().bitvec_width() == Some(POINTER_WIDTH)` test that stood
    /// at the inline walker's load and address-arithmetic sites. Same predicate,
    /// two differences that matter: it is no longer the thing that *decides*
    /// provenance (the MIR type does, at the caller, where the fact is known),
    /// and its result is a [`Loc`] instead of one more anonymous `Expr` that the
    /// next consumer has to re-guess about.
    pub(crate) fn thin_address(expr: &Expr) -> Option<Loc> {
        match Self::classify(expr)? {
            Self::Thin(loc) => Some(loc),
            Self::Fat { .. } | Self::WidenedThin(_) => None,
        }
    }

    /// Builds a `Fat` pointer from field roles **declared** by the datatype.
    ///
    /// Unlike [`PtrRepr::classify`], nothing is inferred here: the caller has
    /// read the roles off the declaration (a field literally named `fld_ptr` /
    /// `fld_len`, or a `Slice_`/`Dyn_` datatype's positional convention) and is
    /// reporting them. See `docs/addr-vs-value-conversion-queue.md` §4 item 7 —
    /// the positional half of that is the residual ambiguity a per-datatype
    /// field-role table has to close; a type cannot decide it.
    pub(crate) fn from_declared_roles(data: Loc, meta: Val) -> Self {
        Self::Fat { data, meta }
    }

    /// Packs the representation back into a `2 * POINTER_WIDTH` bitvector.
    ///
    /// The encoder's wide-pointer layout is `[metadata : upper | data : lower]`
    /// — deliberately the *opposite* of `flatten_datatype_to_bitvec`'s MSB-first
    /// field order, which is why several sites used to hand-roll
    /// `vtable.concat(ptr)` with a comment restating the convention. Two
    /// adjacent `Expr` operands where one is an address and one is a value is
    /// the canonical shape of the slot-misalign defect class; taking [`Loc`] and
    /// [`Val`] instead makes the swap a compile error, and states the byte order
    /// once.
    ///
    /// `None` for the shapes that have no metadata: there is nothing to pack,
    /// and synthesizing a zero high half is the fabrication this enum exists to
    /// prevent.
    pub(crate) fn into_packed(self) -> Option<Expr> {
        match self {
            Self::Fat { data, meta } => Some(meta.into_expr().concat(data.into_expr())),
            Self::Thin(_) | Self::WidenedThin(_) => None,
        }
    }

    /// The data address. Total: every shape points somewhere.
    pub(crate) fn data(&self) -> &Loc {
        match self {
            Self::Thin(loc) | Self::WidenedThin(loc) => loc,
            Self::Fat { data, .. } => data,
        }
    }

    /// Consumes the representation and returns the data address.
    pub(crate) fn into_data(self) -> Loc {
        match self {
            Self::Thin(loc) | Self::WidenedThin(loc) => loc,
            Self::Fat { data, .. } => data,
        }
    }

    /// The metadata value — `Some` for a genuine fat pointer **only**.
    ///
    /// `None` for `Thin` (there is no metadata) and for `WidenedThin` (the high
    /// half is padding, and reading it fabricates a length). Callers must treat
    /// `None` as "unresolved" and fall through to their honest fallback; they
    /// must never substitute the high half themselves.
    // Borrowing counterpart of `into_metadata`; the wave's consumers all own
    // their `PtrRepr`, so only the tests exercise this one so far.
    #[allow(dead_code)]
    pub(crate) fn metadata(&self) -> Option<&Val> {
        match self {
            Self::Fat { meta, .. } => Some(meta),
            Self::Thin(_) | Self::WidenedThin(_) => None,
        }
    }

    /// Consumes the representation and returns both halves at once.
    ///
    /// The address is total and the metadata is not, which is the asymmetry the
    /// whole enum exists to express: a consumer that wants `(addr, meta)` gets
    /// `None` for the metadata of a thin — or widened-thin — pointer instead of
    /// its padding.
    pub(crate) fn into_parts(self) -> (Loc, Option<Val>) {
        match self {
            Self::Thin(loc) | Self::WidenedThin(loc) => (loc, None),
            Self::Fat { data, meta } => (data, Some(meta)),
        }
    }

    /// Consumes the representation and returns the metadata value, if any.
    pub(crate) fn into_metadata(self) -> Option<Val> {
        match self {
            Self::Fat { meta, .. } => Some(meta),
            Self::Thin(_) | Self::WidenedThin(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::PtrRepr;
    use crate::codegen_ay::provenance::{Loc, Val};
    use crate::codegen_ay::types::POINTER_WIDTH;
    use ay_bindings::{Expr, Sort};

    fn addr(name: &str) -> Expr {
        Expr::var(name, Sort::bitvec(POINTER_WIDTH))
    }

    /// A `POINTER_WIDTH` expression is a thin pointer and has no metadata.
    #[test]
    fn thin_pointer_has_no_metadata() {
        let repr = PtrRepr::classify(&addr("_1_ptr")).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::Thin(_)));
        assert!(repr.metadata().is_none());
        assert_eq!(repr.data().as_expr(), &addr("_1_ptr"));
    }

    /// `concat(meta, data)` decodes structurally — the halves come back as the
    /// concat's own operands, not as re-extractions.
    #[test]
    fn concat_decodes_to_structural_fat_pointer() {
        let meta = Expr::bitvec_const(7u64, POINTER_WIDTH);
        let data = addr("_2_ptr");
        let fat = meta.clone().concat(data.clone());

        let repr = PtrRepr::classify(&fat).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::Fat { .. }));
        assert_eq!(repr.data().as_expr(), &data);
        assert_eq!(repr.metadata().expect("fat carries metadata").as_expr(), &meta);
    }

    /// A zero-extended thin address is `WidenedThin`, so the fabricated high
    /// half is **not reachable** through the metadata accessor.
    #[test]
    fn zero_extended_thin_pointer_refuses_metadata() {
        let widened = addr("_3_ptr").zero_extend(POINTER_WIDTH);
        let repr = PtrRepr::classify(&widened).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::WidenedThin(_)));
        assert!(repr.metadata().is_none(), "widened padding must never be read as metadata");
    }

    /// The sign-extended form is refused identically.
    #[test]
    fn sign_extended_thin_pointer_refuses_metadata() {
        let widened = addr("_4_ptr").sign_extend(POINTER_WIDTH);
        let repr = PtrRepr::classify(&widened).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::WidenedThin(_)));
        assert!(repr.metadata().is_none());
    }

    /// Constant folding erases the extension node; the folded form is caught by
    /// the zero-high-half test instead.
    #[test]
    fn folded_widened_constant_refuses_metadata() {
        let folded = Expr::bitvec_const(0x1000u64, 2 * POINTER_WIDTH);
        let repr = PtrRepr::classify(&folded).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::WidenedThin(_)));
        assert!(repr.metadata().is_none());
    }

    /// A `bv128` constant with a non-zero high half carries real metadata.
    #[test]
    fn constant_with_nonzero_high_half_is_fat() {
        let value = (num_bigint::BigInt::from(3) << 64u32) + num_bigint::BigInt::from(0x2000);
        let folded = Expr::bitvec_const(value, 2 * POINTER_WIDTH);
        let repr = PtrRepr::classify(&folded).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::Fat { .. }));
        assert!(repr.metadata().is_some());
    }

    /// An opaque `bv128` (no widening evidence) is treated as a genuine fat
    /// pointer, matching the predicate this enum replaces.
    #[test]
    fn opaque_double_width_var_is_fat() {
        let opaque = Expr::var("_5_fat", Sort::bitvec(2 * POINTER_WIDTH));
        let repr = PtrRepr::classify(&opaque).expect("pointer-shaped");
        assert!(matches!(repr, PtrRepr::Fat { .. }));
        assert!(repr.metadata().is_some());
    }

    /// Widths that are neither thin nor double-width are not pointer-shaped.
    #[test]
    fn non_pointer_widths_are_rejected() {
        assert!(PtrRepr::classify(&Expr::bitvec_const(1u64, 32)).is_none());
        assert!(PtrRepr::classify(&Expr::bitvec_const(1u64, 8)).is_none());
        assert!(PtrRepr::classify(&Expr::bool_const(true)).is_none());
    }

    /// The declared-role constructor reports what the datatype says; it infers
    /// nothing and always yields a `Fat`.
    #[test]
    fn declared_roles_build_a_fat_pointer() {
        let data = Loc::of_address(addr("_6_ptr"));
        let meta = Val::of_value(Expr::bitvec_const(4u64, POINTER_WIDTH));
        let repr = PtrRepr::from_declared_roles(data, meta);
        assert!(matches!(repr, PtrRepr::Fat { .. }));
        assert!(repr.metadata().is_some());
    }

    /// Packing declared roles yields `[meta : upper | data : lower]`, and
    /// re-classifying the packed form recovers the same two halves.
    #[test]
    fn packing_declared_roles_round_trips_through_classify() {
        let data = addr("_10_ptr");
        let meta = Expr::bitvec_const(9u64, POINTER_WIDTH);
        let packed = PtrRepr::from_declared_roles(
            Loc::of_address(data.clone()),
            Val::of_value(meta.clone()),
        )
        .into_packed()
        .expect("declared roles always pack");

        assert_eq!(packed.sort().bitvec_width(), Some(2 * POINTER_WIDTH));
        let repr = PtrRepr::classify(&packed).expect("pointer-shaped");
        assert_eq!(repr.data().as_expr(), &data);
        assert_eq!(repr.metadata().expect("fat carries metadata").as_expr(), &meta);
    }

    /// Shapes with no metadata refuse to pack rather than inventing a high half.
    #[test]
    fn metadata_free_shapes_refuse_to_pack() {
        assert!(PtrRepr::classify(&addr("_11_ptr")).expect("thin").into_packed().is_none());
        assert!(
            PtrRepr::classify(&addr("_12_ptr").zero_extend(POINTER_WIDTH))
                .expect("widened")
                .into_packed()
                .is_none()
        );
    }

    /// `thin_address` accepts a thin pointer and hands back its address.
    #[test]
    fn thin_address_accepts_a_thin_pointer() {
        let ptr = addr("_13_ptr");
        let loc = PtrRepr::thin_address(&ptr).expect("a thin pointer has an address");
        assert_eq!(loc.as_expr(), &ptr);
    }

    /// `thin_address` declines both wide shapes rather than silently dropping
    /// the metadata half at a scalar load site.
    #[test]
    fn thin_address_declines_wide_pointers() {
        let fat = Expr::bitvec_const(7u64, POINTER_WIDTH).concat(addr("_14_ptr"));
        assert!(PtrRepr::thin_address(&fat).is_none(), "a fat pointer is not a thin address");

        let widened = addr("_15_ptr").zero_extend(POINTER_WIDTH);
        assert!(
            PtrRepr::thin_address(&widened).is_none(),
            "a widened thin pointer occupies a wide slot and is declined too"
        );
    }

    /// `thin_address` agrees with the width test it replaces: non-pointer
    /// widths and non-bitvector sorts have no address.
    #[test]
    fn thin_address_declines_non_pointer_shapes() {
        assert!(PtrRepr::thin_address(&Expr::bitvec_const(1u64, 32)).is_none());
        assert!(PtrRepr::thin_address(&Expr::bool_const(true)).is_none());
    }

    /// A declared sort is classified by how many words the slot holds, and the
    /// two widths the encoder emits for pointer-typed places are the only ones
    /// accepted.
    #[test]
    fn ptr_slot_classifies_declared_pointer_sorts() {
        use super::PtrSlot;
        assert_eq!(PtrSlot::of_sort(&Sort::bitvec(POINTER_WIDTH)), Some(PtrSlot::Thin));
        assert_eq!(PtrSlot::of_sort(&Sort::bitvec(2 * POINTER_WIDTH)), Some(PtrSlot::Fat));
        assert_eq!(PtrSlot::of_sort(&Sort::bitvec(32)), None);
        assert_eq!(PtrSlot::of_sort(&Sort::bool()), None);
        assert_eq!(PtrSlot::of_sort(&Sort::array(Sort::bitvec(64), Sort::bitvec(8))), None);
    }

    /// `into_data` agrees with `data` for every shape.
    #[test]
    fn into_data_agrees_with_data() {
        for expr in [
            addr("_7_ptr"),
            addr("_8_ptr").zero_extend(POINTER_WIDTH),
            Expr::var("_9_fat", Sort::bitvec(2 * POINTER_WIDTH)),
        ] {
            let repr = PtrRepr::classify(&expr).expect("pointer-shaped");
            let borrowed = repr.data().as_expr().clone();
            assert_eq!(repr.into_data().into_expr(), borrowed);
        }
    }
}
