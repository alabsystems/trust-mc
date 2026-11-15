// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant-reference discriminant collection for CHC encoding.
//!
//! Extracted from codegen_decl_ref_analysis.rs per #2246 (large-file decomposition wave 3).
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};

use rustc_public::mir::{Operand, Rvalue, StatementKind};
use tracing::debug;

use super::ChcCtx;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn build_const_ref_discriminant_propagation_edges(&self) -> HashMap<usize, Vec<usize>> {
        let mut by_src: HashMap<usize, Vec<usize>> = HashMap::new();

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };

                if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rhs
                    && place.projection.is_empty()
                {
                    by_src.entry(place.local).or_default().push(lhs.local);
                }
            }
        }

        by_src
    }

    fn enqueue_const_ref_discriminant_local(
        queue: &mut VecDeque<usize>,
        queued: &mut HashSet<usize>,
        local: usize,
    ) {
        if queued.insert(local) {
            queue.push_back(local);
        }
    }

    fn propagate_const_ref_discriminants_worklist(&mut self, by_src: &HashMap<usize, Vec<usize>>) {
        // Part of #2286: source-indexed worklist propagation avoids
        // full-body fixpoint rescans for each newly discovered local.
        let mut queue: VecDeque<usize> =
            self.ref_resolution.const_ref_discriminants.keys().copied().collect();
        let mut queued: HashSet<usize> =
            self.ref_resolution.const_ref_discriminants.keys().copied().collect();

        while let Some(src_local) = queue.pop_front() {
            queued.remove(&src_local);
            let Some(&discr) = self.ref_resolution.const_ref_discriminants.get(&src_local) else {
                continue;
            };

            if let Some(dest_locals) = by_src.get(&src_local) {
                for &dest_local in dest_locals {
                    if self.ref_resolution.const_ref_discriminants.contains_key(&dest_local) {
                        continue;
                    }
                    debug!(
                        "Pass3.2 propagate const_ref_discriminant: _{} = _{} -> discriminant {}",
                        dest_local, src_local, discr
                    );
                    self.ref_resolution.const_ref_discriminants.insert(dest_local, discr);
                    Self::enqueue_const_ref_discriminant_local(&mut queue, &mut queued, dest_local);
                }
            }
        }
    }

    /// Collects discriminant values from constant references to unit enums.
    ///
    /// Part of #1905: This enables translate_discriminant to handle patterns like:
    /// ```mir
    /// _9 = const &Ordering::Equal   // constant reference
    /// _11 = Copy(_9)                // propagated reference
    /// _13 = Discriminant(*_11)      // need to resolve this
    /// ```
    ///
    /// By tracking that _11 ultimately refers to Ordering::Equal (discriminant 0),
    /// we can return the correct discriminant when the deref chain can't be resolved.
    pub(in crate::codegen_ay::chc) fn collect_const_ref_discriminants(&mut self) {
        use rustc_public::ty::{RigidTy, TyKind};

        // Pass 3.1: Direct constant assignments
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && let Rvalue::Use(Operand::Constant(const_op), ..) = rhs
                {
                    let dest_local: usize = lhs.local;
                    let mir_const = &const_op.const_;
                    let ty = mir_const.ty();

                    // Check if this is a reference to an enum (unit or non-unit)
                    if let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind()
                        && let TyKind::RigidTy(RigidTy::Adt(def, _)) = inner_ty.kind()
                    {
                        let variants = def.variants();
                        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());

                        if is_unit_enum {
                            // Unit enum: the pointee WINDOW is the discriminant.
                            if let Some((mut discr, alloc_bytes)) =
                                self.extract_discriminant_from_const(mir_const, inner_ty)
                            {
                                // Part of #3536: read_int() zero-pads to 16 bytes before
                                // interpreting, so a 1-byte [0xFF] produces 255i128 not -1.
                                // Sign-extend from the allocation byte width when the
                                // effective discriminant type is signed. Default (no repr)
                                // is isize (signed) per rustc discr_type().
                                use rustc_public::abi::IntegerType;
                                let discr_type = def
                                    .repr()
                                    .int
                                    .unwrap_or(IntegerType::Pointer { is_signed: true });
                                let is_signed = matches!(
                                    discr_type,
                                    IntegerType::Fixed { is_signed: true, .. }
                                        | IntegerType::Pointer { is_signed: true }
                                );
                                if is_signed && alloc_bytes > 0 && alloc_bytes < 8 {
                                    let bits = alloc_bytes * 8;
                                    let mask = 1u64 << (bits - 1);
                                    if discr & mask != 0 {
                                        discr |= !((1u64 << bits) - 1);
                                    }
                                }
                                debug!(
                                    "Pass3 const_ref_discriminant: _{} = discriminant {}",
                                    dest_local, discr
                                );
                                self.ref_resolution
                                    .const_ref_discriminants
                                    .insert(dest_local, discr);
                            }
                        } else if variants.len() >= 2 {
                            // Part of #3798, #4026: Non-unit enum promoted constant reference.
                            // The target allocation contains the full enum value;
                            // the discriminant is at byte 0 of the target allocation.
                            // Read just the discriminant tag byte(s), then map to the
                            // actual ADT discriminant value via variant index.
                            // Niche-encoded enums are skipped: their packed BV
                            // representation differs from the variant index.
                            if let Some(discr) =
                                self.extract_non_unit_enum_discriminant(mir_const, def, inner_ty)
                            {
                                debug!(
                                    dest_local,
                                    discr, "Pass3 const_ref_discriminant: non-unit enum"
                                );
                                self.ref_resolution
                                    .const_ref_discriminants
                                    .insert(dest_local, discr);
                            }
                        }
                    }
                }
            }
        }

        // Pass 3.2: Propagate through Copy/Move.
        let propagation_edges = self.build_const_ref_discriminant_propagation_edges();
        self.propagate_const_ref_discriminants_worklist(&propagation_edges);

        debug!(
            count = self.ref_resolution.const_ref_discriminants.len(),
            "CHC: collected constant reference discriminants"
        );
    }

    /// Extracts the discriminant value and byte count of the unit enum a
    /// constant reference points at: the pointee WINDOW at the pointer's
    /// offset in its (fixed) target (`const_pointer::fixed_pointee`).
    ///
    /// Part of #1905 / R6. The discriminant was read at the target's byte 0 —
    /// for `DR = &[Dir::B, Dir::A][1]` that is `B`'s tag, and `matches!(*DR,
    /// Dir::B)` PROVED — and, for a constant into a static or a `Ty`-kind
    /// constant, from the constant's OWN bytes: the pointer's offset read as
    /// the tag.
    ///
    /// Returns `(raw_discriminant, byte_count)` where the caller must
    /// sign-extend from `byte_count * 8` bits for signed repr enums
    /// (Part of #3536).
    fn extract_discriminant_from_const(
        &self,
        mir_const: &rustc_public::ty::MirConst,
        inner_ty: rustc_public::ty::Ty,
    ) -> Option<(u64, usize)> {
        let bytes = const_pointer::const_bytes(mir_const)?;
        let (_, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, inner_ty)?;
        let byte_count = window.len();
        if byte_count == 0 {
            return Some((0, 0));
        }
        let value = window.read_uint_at(0, byte_count)?;
        Some((value as u64, byte_count))
    }

    /// Part of #3798, #4026 / R6: the discriminant of the non-unit enum a
    /// constant reference points at.
    ///
    /// The enum value is the pointee WINDOW at the pointer's offset in its
    /// fixed target; its tag is read at the layout's tag field and width
    /// (`decode_non_unit_enum_variant_index`), then mapped to the variant's
    /// discriminant. The tag was read at the target's byte 0, one or two
    /// bytes wide by variant count: for `OE = &[None, Some(3u8)][1]`,
    /// `matches!(*OE, None)` PROVED.
    ///
    /// Returns None for niche-encoded enums: their packed BV representation
    /// (concat of discriminant bits + payload bits) differs from the variant
    /// index stored in the tag byte, so populating `const_ref_discriminants`
    /// would cause a representation mismatch in `translate_discriminant`.
    pub(in crate::codegen_ay::chc::decl) fn extract_non_unit_enum_discriminant(
        &self,
        mir_const: &rustc_public::ty::MirConst,
        def: rustc_public::ty::AdtDef,
        inner_ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        use rustc_abi::VariantIdx as InternalVariantIdx;
        use rustc_public::abi::{TagEncoding, VariantsShape};
        use rustc_public::rustc_internal;

        // Part of #4026: Bail out for niche-encoded enums. The packed BV
        // representation used by translate_discriminant differs from the
        // variant index, so const_ref_discriminants would be wrong.
        if let Ok(layout) = inner_ty.layout()
            && matches!(
                layout.shape().variants,
                VariantsShape::Multiple { tag_encoding: TagEncoding::Niche { .. }, .. }
            )
        {
            return None;
        }

        let bytes = const_pointer::const_bytes(mir_const)?;
        let (_, window) = const_pointer::fixed_pointee(self.tcx, &bytes, 0, inner_ty)?;
        let num_variants = def.variants().len();
        let variant_idx =
            crate::codegen_ay::chc::expr::codegen_expr_constant_payload::decode_non_unit_enum_variant_index(
                &window,
                inner_ty,
                num_variants,
            )?;
        let internal_def = rustc_internal::internal(self.tcx, def);
        let discr = internal_def
            .discriminant_for_variant(self.tcx, InternalVariantIdx::from_usize(variant_idx));
        // The encoder's discriminant convention: sign-extended to the pointer
        // width (`translate_discriminant`), not the raw truncated bits.
        Some(crate::codegen_ay::chc::stmt::codegen_stmt_aggregate_adt::sign_extend_discr_val(
            discr.val,
            discr.ty,
            self.tcx,
            crate::codegen_ay::types::POINTER_WIDTH,
        ) as u64)
    }
}
