// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant-reference discriminant collection for CHC encoding.
//!
//! Extracted from codegen_decl_ref_analysis.rs per #2246 (large-file decomposition wave 3).
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_public::mir::{Operand, Rvalue, StatementKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn build_const_ref_discriminant_propagation_edges(&self) -> HashMap<usize, Vec<usize>> {
        let mut by_src: HashMap<usize, Vec<usize>> = HashMap::new();

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };

                if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rhs
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
                    && let Rvalue::Use(Operand::Constant(const_op)) = rhs
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
                            // Unit enum: the entire allocation IS the discriminant.
                            if let Some((mut discr, alloc_bytes)) =
                                Self::extract_discriminant_from_const(mir_const.kind().clone())
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
                            if let Some(discr) = Self::extract_non_unit_enum_discriminant(
                                mir_const.kind().clone(),
                                def,
                                inner_ty,
                                self.tcx,
                            ) {
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

    /// Extracts discriminant value and allocation byte count from a constant
    /// reference to a unit enum.
    ///
    /// Part of #1905: Constant references like `const &Ordering::Equal` store a pointer
    /// in the allocation. We follow the provenance to get the target allocation
    /// containing the actual discriminant value.
    ///
    /// Returns `(raw_discriminant, alloc_byte_count)` where the caller must
    /// sign-extend from `alloc_byte_count * 8` bits for signed repr enums
    /// (Part of #3536).
    fn extract_discriminant_from_const(
        kind: rustc_public::ty::ConstantKind,
    ) -> Option<(u64, usize)> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::ConstantKind;

        match kind {
            // Allocated constants contain the actual data
            ConstantKind::Allocated(alloc) => {
                // For references, the allocation contains a pointer with provenance.
                // Follow the provenance to get the target allocation.
                if !alloc.provenance.ptrs.is_empty() {
                    let alloc_id = alloc.provenance.ptrs[0].1.0;
                    if let GlobalAlloc::Memory(target_alloc) = GlobalAlloc::from(alloc_id) {
                        let byte_count = target_alloc.bytes.len();
                        // Read discriminant from target allocation
                        if let Ok(val) = target_alloc.read_int() {
                            return Some((val as u64, byte_count));
                        } else if let Ok(val) = target_alloc.read_uint() {
                            return Some((val as u64, byte_count));
                        }
                    }
                }
                // Fallback: try reading directly (for non-pointer constants)
                let byte_count = alloc.bytes.len();
                if let Ok(val) = alloc.read_int() {
                    Some((val as u64, byte_count))
                } else if let Ok(val) = alloc.read_uint() {
                    Some((val as u64, byte_count))
                } else {
                    None
                }
            }
            // Type constants may have evaluated values
            ConstantKind::Ty(ty_const) => {
                use rustc_public::ty::TyConstKind;
                match ty_const.kind() {
                    TyConstKind::Value(_value_ty, alloc) => {
                        let byte_count = alloc.bytes.len();
                        if let Ok(val) = alloc.read_int() {
                            Some((val as u64, byte_count))
                        } else if let Ok(val) = alloc.read_uint() {
                            Some((val as u64, byte_count))
                        } else {
                            None
                        }
                    }
                    TyConstKind::ZSTValue(_) => Some((0, 0)), // ZST has discriminant 0
                    _ => None,                                // external enum: TyConstKind
                }
            }
            ConstantKind::ZeroSized => Some((0, 0)),
            _ => None, // external enum: ConstantKind
        }
    }

    /// Part of #3798, #4026: Extract the discriminant from a promoted non-unit enum constant.
    ///
    /// For non-unit enums (variants with fields), the target allocation contains
    /// the full enum value. The discriminant tag is stored at the start of the
    /// allocation. We read the tag byte(s) and map to the real discriminant value
    /// via `discriminant_for_variant`.
    ///
    /// Returns None for niche-encoded enums: their packed BV representation
    /// (concat of discriminant bits + payload bits) differs from the variant
    /// index stored in the tag byte, so populating `const_ref_discriminants`
    /// would cause a representation mismatch in `translate_discriminant`.
    pub(in crate::codegen_ay::chc::decl) fn extract_non_unit_enum_discriminant(
        kind: rustc_public::ty::ConstantKind,
        def: rustc_public::ty::AdtDef,
        inner_ty: rustc_public::ty::Ty,
        tcx: rustc_middle::ty::TyCtxt<'_>,
    ) -> Option<u64> {
        use rustc_abi::VariantIdx as InternalVariantIdx;
        use rustc_public::abi::{TagEncoding, VariantsShape};
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::rustc_internal;
        use rustc_public::ty::ConstantKind;

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

        let alloc = match kind {
            ConstantKind::Allocated(a) => a,
            _ => return None,
        };
        if alloc.provenance.ptrs.is_empty() {
            return None;
        }
        let alloc_id = alloc.provenance.ptrs[0].1.0;
        let target_alloc = match GlobalAlloc::from(alloc_id) {
            GlobalAlloc::Memory(a) => a,
            _ => return None,
        };
        // Read the tag byte(s) from the start of the target allocation.
        // Enums with ≤256 variants use a 1-byte tag; ≤65536 use 2 bytes.
        let num_variants = def.variants().len();
        let tag_bytes = if num_variants <= 256 { 1usize } else { 2 };
        if target_alloc.bytes.len() < tag_bytes {
            return None;
        }
        let mut tag: u64 = 0;
        for (i, byte) in target_alloc.bytes.iter().take(tag_bytes).enumerate() {
            let b = (*byte)? as u64;
            tag |= b << (i * 8);
        }
        // The tag is the variant index. Map to the actual discriminant value.
        let variant_idx = tag as usize;
        if variant_idx >= num_variants {
            return None;
        }
        let internal_def = rustc_internal::internal(tcx, def);
        let discr =
            internal_def.discriminant_for_variant(tcx, InternalVariantIdx::from_usize(variant_idx));
        Some(discr.val as u64)
    }
}
