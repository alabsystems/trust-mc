// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SSA versioning and signedness detection for AY codegen.
//!
//! This module handles Static Single Assignment (SSA) variable naming:
//! - Version tracking for each variable name
//! - Base name construction from MIR Place projections
//! - SSA name generation with automatic version incrementing
//! - Signedness detection for binary operations (Part of #126, #265)
//!
//! SSA form ensures each variable has exactly one definition point,
//! enabling efficient SMT constraint generation.

use super::*;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Determine signedness for a binary operation from operand types.
    ///
    /// Returns `Some(true)` for signed, `Some(false)` for unsigned, `None` when unknown.
    /// Callers handle `None` by defaulting to unsigned. Part of #126.
    pub(super) fn is_signed_integer_op(&self, lhs: &Operand, rhs: &Operand) -> Option<bool> {
        let lhs_ty = lhs.ty(self.body.locals()).into_option();
        let rhs_ty = rhs.ty(self.body.locals()).into_option();

        // Check lhs first, then rhs - one known type suffices for shift operations
        let lhs_signed = lhs_ty.and_then(Self::ty_signedness);
        let rhs_signed = rhs_ty.and_then(Self::ty_signedness);

        match (lhs_signed, rhs_signed) {
            // Both known - must agree
            (Some(l), Some(r)) if l == r => Some(l),
            // One known - use that (shift amount may be usize with u32 value)
            (Some(s), None) | (None, Some(s)) => Some(s),
            // Both unknown or disagree
            _ => None, // non-enum: tuple
        }
    }

    /// Determine signedness for a single operand (used for shift distance checks).
    pub(super) fn operand_signedness(&self, operand: &Operand) -> Option<bool> {
        operand.ty(self.body.locals()).into_option().and_then(Self::ty_signedness)
    }

    /// Get signedness of a type: Some(true) for signed, Some(false) for unsigned, None for non-integer.
    ///
    /// Handles:
    /// - Direct integer types (Int, Uint), Bool, Char
    /// - References and raw pointers (recursively check inner type)
    /// - Pointer-wrapper ADTs: Box, Unique, NonNull (recurse into generic type arg)
    /// - Tuples (recurse into first element, for checked arithmetic results)
    /// - Atomic types (AtomicI*, AtomicU*, AtomicIsize, AtomicUsize)
    ///
    /// Delegates to `ty_signedness_shallow` from `shared.rs` for leaf types.
    /// Part of #2944: shared core extraction. Part of #2954: parity with CHC.
    pub(super) fn ty_signedness(ty: rustc_public::ty::Ty) -> Option<bool> {
        use crate::codegen_ay::shared::{is_pointer_wrapper_adt, ty_signedness_shallow};
        use rustc_public::abi::IntegerType;
        use rustc_public::ty::{AdtKind, GenericArgKind};

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, ref inner, _) | RigidTy::RawPtr(ref inner, _)) => {
                Self::ty_signedness(*inner)
            }
            TyKind::RigidTy(RigidTy::Adt(def, ref args)) => {
                let name = def.name();
                if is_pointer_wrapper_adt(&name)
                    && let Some(GenericArgKind::Type(inner_ty)) = args.0.first()
                {
                    return Self::ty_signedness(*inner_ty);
                }
                // Part of #3186: parity with CHC ty_signedness (Fixes #3262).
                // Enums with explicit signed repr (e.g., `#[repr(i8)]` like
                // `std::cmp::Ordering`: Less=-1, Equal=0, Greater=1) use signed
                // discriminants. Default enums without signed repr use unsigned
                // discriminants (sequential 0..N-1).
                if def.kind() == AdtKind::Enum {
                    let is_signed_repr = matches!(
                        def.repr().int,
                        Some(IntegerType::Fixed { is_signed: true, .. })
                            | Some(IntegerType::Pointer { is_signed: true })
                    );
                    return Some(is_signed_repr);
                }
                // Struct ADTs: fieldless structs (ZSTs) have no data, so signedness
                // is irrelevant — default to unsigned. Single-field structs (newtype
                // wrappers) inherit the inner field's signedness.
                if def.kind() == AdtKind::Struct {
                    if let Some(variant) = def.variants().first() {
                        let fields = variant.fields();
                        if fields.is_empty() {
                            return Some(false); // ZST — no data to compare
                        }
                        if fields.len() == 1 {
                            if let Some(inner) = Self::ty_signedness(fields[0].ty()) {
                                return Some(inner);
                            }
                        }
                        // Part of #3690: multi-field structs have no inherent sign
                        // semantics when encoded as BV. Default to unsigned.
                        return Some(false);
                    }
                }
                ty_signedness_shallow(ty)
            }
            // Part of #3690: arrays inherit element signedness.
            TyKind::RigidTy(RigidTy::Array(ref elem_ty, _)) => Self::ty_signedness(*elem_ty),
            // Empty tuple () has no data — signedness is irrelevant.
            TyKind::RigidTy(RigidTy::Tuple(ref elements)) if elements.is_empty() => Some(false),
            TyKind::RigidTy(RigidTy::Tuple(ref elements)) if !elements.is_empty() => {
                Self::ty_signedness(elements[0])
            }
            _ => ty_signedness_shallow(ty), // external enum: TyKind
        }
    }

    /// Returns `true` iff the local named by `base_name` (pattern
    /// `{fn}::local_{N}[_...]`) has a type that provably contains an `UnsafeCell`
    /// — i.e. is interior-mutable. Mirrors `signedness_from_base_name`'s index
    /// parse. Used to fail-close interior-mutable values at control-flow merges
    /// (writes through a shared `&Cell` bypass `env`, so a merged env snapshot of
    /// such a local can be stale and must not be trusted).
    pub(super) fn base_name_is_interior_mutable(&self, base_name: &str) -> bool {
        let local_prefix = "::local_";
        let Some(local_start) = base_name.find(local_prefix).map(|p| p + local_prefix.len()) else {
            return false;
        };
        let rest = &base_name[local_start..];
        let digit_end = rest.bytes().position(|b| !b.is_ascii_digit()).unwrap_or(rest.len());
        let Ok(local_idx) = rest[..digit_end].parse::<usize>() else {
            return false;
        };
        let Some(local) = self.body.locals().get(local_idx) else {
            return false;
        };
        Self::ty_contains_unsafe_cell(local.ty, 0)
    }

    /// Whether the interior-mutable payload named by `base_name` lives in ONE
    /// storage slot in this model — see
    /// [`StatementCodegen::unsafe_cell_is_single_payload`]. Same local-index
    /// parse as `base_name_is_interior_mutable`, and the two are used together:
    /// the read fail-close in `place_deref_first` stands down only when the
    /// pointee is interior-mutable AND single-payload.
    pub(super) fn base_name_unsafe_cell_is_single_payload(&self, base_name: &str) -> bool {
        let local_prefix = "::local_";
        let Some(local_start) = base_name.find(local_prefix).map(|p| p + local_prefix.len()) else {
            return false;
        };
        let rest = &base_name[local_start..];
        let digit_end = rest.bytes().position(|b| !b.is_ascii_digit()).unwrap_or(rest.len());
        let Ok(local_idx) = rest[..digit_end].parse::<usize>() else {
            return false;
        };
        let Some(local) = self.body.locals().get(local_idx) else {
            return false;
        };
        Self::unsafe_cell_is_single_payload(local.ty, 0)
    }

    /// Determine signedness from a base name by extracting the local index and looking up its type.
    ///
    /// Base names follow the pattern `{fn_name}::local_{N}` or `{fn_name}::local_{N}_field_{M}`.
    /// This extracts N, looks up the local's type, and returns its signedness.
    /// Returns None if the base name doesn't match the expected pattern or the type is non-integer.
    ///
    /// Part of #265: signedness-aware coercions.
    /// Part of #3094: ADT enum fallback to unsigned.
    pub(super) fn signedness_from_base_name(&self, base_name: &str) -> Option<bool> {
        // Extract local index from base name: "fn::local_N" or "fn::local_N_..."
        let local_prefix = "::local_";
        let local_start = base_name.find(local_prefix)? + local_prefix.len();
        let rest = &base_name[local_start..];
        // Parse the local index from the digit prefix of `rest` without allocating a String.
        let digit_end = rest.bytes().position(|b| !b.is_ascii_digit()).unwrap_or(rest.len());
        let local_idx: usize = rest[..digit_end].parse().ok()?;

        // Look up the local's type from the body
        let ty = self.body.locals().get(local_idx)?.ty;
        if let Some(signed) = Self::ty_signedness(ty) {
            return Some(signed);
        }
        // Part of #3094: For ADT types (enums, structs) stored as bitvec, enum
        // discriminant indices are always unsigned. Returning Some(false) prevents
        // the signedness_fallback counter from firing during phi harmonization BV
        // coercions, which otherwise causes false PROOF demotion.
        if let TyKind::RigidTy(RigidTy::Adt(..)) = ty.kind() {
            return Some(false);
        }
        None
    }

    /// Get the current SSA version of a variable and increment it.
    ///
    /// # Invariants (runtime-enforced)
    /// - Version numbers are monotonically increasing per base name
    /// - Each call with the same var_name returns a strictly greater version
    /// - Version N for base B guarantees names B_0..B_(N-1) were previously allocated
    /// - Panics on overflow (u32::MAX) to prevent silent name collisions
    fn next_ssa_version(&mut self, var_name: &str) -> u32 {
        // Avoid allocating for the HashMap key on every call.
        // get_mut() checks existence without allocation; only entry() allocates an Arc<str>.
        let version = if let Some(v) = self.ssa_version.get_mut(var_name) {
            v
        } else {
            self.ssa_version.entry(std::sync::Arc::from(var_name)).or_insert(0)
        };
        let current = *version;

        // Runtime invariant: SSA version overflow produces name collisions,
        // which silently corrupt verification results. checked_add makes this
        // fail-closed instead of silently wrapping in release builds.
        // Matches the pattern in heap_state.rs:218 for allocation IDs.
        *version = current
            .checked_add(1)
            .expect("SSA version overflow: name collision would corrupt verification");

        current
    }

    /// Get the SSA variable name for a place.
    pub(super) fn ssa_name(&mut self, place: &Place, increment: bool) -> String {
        let base_name = self.ssa_base_name(place);
        self.ssa_name_from_base(&base_name, increment)
    }

    /// Get the SSA variable name from a base name.
    ///
    /// If `increment` is true, allocates a new version and returns `base_N` with the new version.
    /// If `increment` is false, returns `base_N` with the current (most recent) version.
    ///
    /// # Contract
    /// - REQUIRES: base_name is a valid SSA base name (e.g., "fn::local_0")
    /// - ENSURES: Returns "base_name_N" where N is the version number
    /// - ENSURES: Result ends with "_N" where N is a non-negative integer
    pub(super) fn ssa_name_from_base(&mut self, base_name: &str, increment: bool) -> String {
        use std::fmt::Write;

        let version = if increment {
            self.next_ssa_version(base_name)
        } else {
            // `ssa_version` tracks the *next* version to allocate, so the current version is `n-1`.
            let next_version = *self.ssa_version.get(base_name).unwrap_or(&0);
            next_version.saturating_sub(1)
        };

        // Pre-allocate: base_name + "_" + version digits (max 10 for u32)
        let mut result = String::with_capacity(base_name.len() + 1 + 10);
        result.push_str(base_name);
        result.push('_');
        let _ = write!(&mut result, "{version}");

        // Debug invariant: result must end with _N suffix
        debug_assert!(
            result.contains('_')
                && result.rsplit('_').next().is_some_and(|s| s.parse::<u32>().is_ok()),
            "SSA name must end with _N suffix: {}",
            result
        );

        result
    }

    /// Build a base name for a Place, incorporating all projections.
    ///
    /// The base name uniquely identifies the storage location:
    /// - `fn::local_N` for a local variable N
    /// - `fn::local_N_field_M` for field M of local N
    /// - `fn::local_N_deref` for dereferencing local N
    /// - And so on for other projections (Index, Downcast, etc.)
    ///
    /// REQUIRES: place is a valid Place from self.body
    /// ENSURES: Returns a unique base name encoding the place's projections
    pub(super) fn ssa_base_name(&mut self, place: &Place) -> String {
        self.ssa_base_name_for_projections(place, &place.projection)
    }

    /// Build a base name for a place prefix (projections `[0..end)`).
    ///
    /// This enables projection-aware ref key construction for ref_pointees lookups,
    /// allowing Deref resolution for references stored in projected locations.
    /// Part of #431: Ref_pointees resolution for projected references.
    pub(super) fn ssa_base_name_for_prefix(&mut self, place: &Place, end: usize) -> String {
        // Preserve historical `iter().take(end)` semantics: if `end` exceeds
        // projection length, include all projections instead of panicking.
        let clamped_end = end.min(place.projection.len());
        self.ssa_base_name_for_projections(place, &place.projection[..clamped_end])
    }

    /// Shared implementation for SSA base name construction from a slice of projections.
    ///
    /// Uses `write!` instead of `push_str(&format!(...))` to avoid intermediate
    /// String allocations per projection element.
    fn ssa_base_name_for_projections(
        &mut self,
        place: &Place,
        projections: &[ProjectionElem],
    ) -> String {
        use std::fmt::Write;

        let mut base_name =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), place.local);
        for proj in projections {
            match proj {
                ProjectionElem::Field(field, _) => {
                    let _ = write!(base_name, "_field_{}", field);
                }
                ProjectionElem::Deref => {
                    base_name.push_str("_deref");
                }
                ProjectionElem::Downcast(variant_idx) => {
                    let _ = write!(base_name, "_variant_{}", variant_idx.to_index());
                }
                ProjectionElem::Index(local) => {
                    let _ = write!(base_name, "_idx_by_{}", local);
                }
                ProjectionElem::ConstantIndex { offset, min_length: _, from_end } => {
                    if *from_end {
                        let _ = write!(base_name, "_cidx_end_{}", offset);
                    } else {
                        let _ = write!(base_name, "_cidx_{}", offset);
                    }
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    if *from_end {
                        let _ = write!(base_name, "_subslice_end_{}_{}", from, to);
                    } else {
                        let _ = write!(base_name, "_subslice_{}_{}", from, to);
                    }
                }
                ProjectionElem::OpaqueCast(_ty) => {
                    base_name.push_str("_cast");
                }
            }
        }
        base_name
    }
}
