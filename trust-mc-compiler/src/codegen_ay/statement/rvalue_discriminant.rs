// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Enum discriminant codegen for AY.
//!
//! Extracted from `rvalue.rs` per #2246 to keep each file single-responsibility.
//! Handles `Rvalue::Discriminant` translation through multiple resolution strategies:
//! checked arithmetic results, bitvec-stored enums (ControlFlow/Result/Option/unit),
//! datatype is-constructor testers, codegen_place fallback, and symbolic fallback.

use std::sync::Arc;

use ay_bindings::{Expr, Sort, SortInner};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Translate `Rvalue::Discriminant(place)` into a AY bitvec expression.
    ///
    /// Tries resolution strategies in order:
    /// 1. Checked arithmetic result field (`.0` / `_field_1`)
    /// 2. Bitvec-stored ControlFlow/Result/Option/unit enum dispatch
    /// 3. Datatype is-constructor testers (2-variant and N-variant)
    /// 4. `codegen_place` fallback for projected places
    /// 5. Unit enum lookup / single-variant discriminant value
    /// 6. Symbolic discriminant variable as last resort
    pub(super) fn codegen_discriminant(&mut self, place: &Place, rvalue: &Rvalue) -> Option<Expr> {
        let base_name: Arc<str> = self.ssa_base_name(place).into();

        // If place has a Deref projection, follow the reference to find the pointee
        let target_base = if !place.projection.is_empty()
            && matches!(place.projection[0], ProjectionElem::Deref)
        {
            let ref_base =
                crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), place.local);
            self.ref_pointees
                .get(ref_base.as_str())
                .cloned()
                .unwrap_or_else(|| Arc::clone(&base_name))
        } else {
            base_name
        };

        // Strategy 1: Checked arithmetic result with discriminant at .0
        if let Some(result) = self.try_checked_arith_discriminant(target_base.as_ref()) {
            return Some(result);
        }

        // Strategy 2-3: Env lookup → bitvec dispatch or datatype tester
        if let Some(result) = self.try_env_discriminant(target_base.as_ref(), place) {
            return Some(result);
        }

        // Part of #3798: rustc lowers `discriminant_value(&non_enum)` through
        // `Rvalue::Discriminant` on the referent. The intrinsic semantics are
        // explicit here: non-enum referents have discriminant value 0.
        if let Some(ty) = place.ty(self.body.locals()).into_option()
            && !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, _) | RigidTy::Coroutine(..)))
        {
            debug!(?place, ?ty, "codegen_rvalue_discriminant: non-enum -> zero");
            return Some(Expr::bitvec_const(0, POINTER_WIDTH));
        }

        // Strategy 4: codegen_place fallback for projected places
        if let Some(result) = self.try_place_fallback_discriminant(place) {
            return Some(result);
        }

        // Strategy 5: Unit enum handling
        if let Some(result) = self.try_unit_enum_discriminant(place, target_base.as_ref()) {
            return Some(result);
        }

        // Strategy 6: Symbolic discriminant fallback
        debug!(
            "codegen_rvalue_discriminant: FALLBACK to symbolic discriminant for place={:?}",
            place
        );
        let name = self.ssa_name(place, false);
        let discr_name = crate::codegen_ay::names::discriminant_name(&name);
        let sort = self.try_infer_sort_from_rvalue_ty(rvalue).unwrap_or_else(|| Sort::bitvec(32));
        Some(self.ctx.declare_var(&discr_name, sort))
    }

    /// Check if this is a checked arithmetic result with discriminant at `.0` or `_field_1`.
    fn try_checked_arith_discriminant(&self, target_base: &str) -> Option<Expr> {
        let discrim_field = crate::codegen_ay::names::discrim_name(target_base);
        if let Some(expr) = self.env_lookup(&discrim_field) {
            return Some(expr.clone());
        }

        // CheckedBinaryOp result with overflow at _field_1
        // Option<T>: overflow=true → discriminant=0, overflow=false → discriminant=1
        let overflow_field = crate::codegen_ay::names::indexed_field_name(target_base, 1);
        if let Some(overflow_expr) = self.env_lookup(&overflow_field) {
            let zero = Expr::bitvec_const(0, 32);
            let one = Expr::bitvec_const(1, 32);
            return Some(Expr::ite(overflow_expr.clone(), zero, one));
        }

        None
    }

    /// Look up target_base in env and extract discriminant from bitvec or datatype.
    fn try_env_discriminant(&mut self, target_base: &str, place: &Place) -> Option<Expr> {
        debug!("codegen_rvalue_discriminant: target_base={}, place={:?}", target_base, place);
        let dt_expr = self.env_lookup(target_base).cloned()?;
        debug!("codegen_rvalue_discriminant: found expr sort={:?}", dt_expr.sort());

        if let Some(result) = Self::try_coroutine_discriminant_expr(&dt_expr) {
            return Some(result);
        }

        // Bitvec-stored enums: ControlFlow/Result/Option/unit
        if dt_expr.sort().is_bitvec()
            && let Some(result) = self.try_bitvec_discriminant(&dt_expr, place)
        {
            return Some(result);
        }

        // Datatype is-constructor testers
        if let SortInner::Datatype(dt) = dt_expr.sort().inner() {
            // Allocation Result types: force Ok discriminant (0).
            if dt.name.contains("Result") && dt.name.contains("AllocError") {
                debug!(
                    "codegen_rvalue_discriminant: Allocation Result - forcing Ok (discriminant 0)"
                );
                return Some(Expr::bitvec_const(0, POINTER_WIDTH));
            }
            // The Option-like encoding orders its constructors by PAYLOAD
            // (`[None_*, Some_*]`), not by MIR variant, so the constructor-index
            // chain below is wrong whenever the payload variant is variant 0:
            // `Poll::Ready(v)` came back as discriminant 1, the `SwitchInt` took
            // the `Pending` arm, and everything after an `.await` was UNREACHABLE
            // — a harness whose only assertion follows an `.await` was proved
            // VACUOUSLY (its broken twin too). Map by payload arity instead.
            if let Some(result) = self.try_option_like_discriminant(dt, &dt_expr, place) {
                return Some(result);
            }
            // All datatype enums (2-variant and N-variant): use constructor-index
            // ITE chain. Previously the 2-variant case hardcoded empty→0/payload→1,
            // which was WRONG when the empty variant wasn't at index 0 (e.g.,
            // `enum E { Foo{a,b}, Bar }` where Bar is variant 1 but was mapped to 0).
            // Part of #3094.
            return Some(Self::build_discriminant_ite_chain(&dt.name, &dt.constructors, &dt_expr));
        }

        None
    }

    /// Discriminant of an Option-like datatype value, keyed on the place's ADT.
    ///
    /// Applies only to the exact Option-like encoding — two constructors of
    /// arity {0, 1} — over an ADT with exactly two variants, one of which has
    /// fields. Returns the MIR variant index of the constructor the value is
    /// in (32-bit, like `build_discriminant_ite_chain`). For `Option<T>` this
    /// is the identity mapping the chain already computed; for `Poll<T>` and
    /// any `enum E { WithPayload(T), Empty }` it is the swap the chain got
    /// wrong. `None` for every other shape, so the caller falls through.
    fn try_option_like_discriminant(
        &self,
        dt: &ay_bindings::DatatypeSort,
        dt_expr: &Expr,
        place: &Place,
    ) -> Option<Expr> {
        if dt.constructors.len() != 2 {
            return None;
        }
        let (empty_ctor, payload_ctor) =
            match (dt.constructors[0].fields.len(), dt.constructors[1].fields.len()) {
                (0, 1) => (&dt.constructors[0], &dt.constructors[1]),
                (1, 0) => (&dt.constructors[1], &dt.constructors[0]),
                _ => return None,
            };
        let ty = place.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let payload_idx = variants.iter().position(|v| !v.fields().is_empty())?;
        let empty_idx = variants.iter().position(|v| v.fields().is_empty())?;
        debug!(
            "codegen_rvalue_discriminant: Option-like {} payload={} ({}) empty={} ({})",
            dt.name, payload_idx, payload_ctor.name, empty_idx, empty_ctor.name
        );
        let is_payload = dt_expr.clone().is_constructor(&dt.name, &payload_ctor.name);
        Some(Expr::ite(
            is_payload,
            Expr::bitvec_const(payload_idx as i128, 32),
            Expr::bitvec_const(empty_idx as i128, 32),
        ))
    }

    /// Extract discriminant from a bitvec-stored enum value.
    ///
    /// For `Option<T>` where T is a unit enum: derives the discriminant from
    /// the bitvec value by checking if it matches any valid T discriminant.
    /// This is precise (no over-approximation) and handles both concrete and
    /// symbolic values correctly. Part of #3094.
    ///
    /// For ControlFlow/Result (and Option<T> with non-unit T): creates a
    /// symbolic discriminant variable constrained to valid values {0, 1}.
    /// This is a sound over-approximation — the solver explores both variant
    /// paths. Pre-#2462 hardcoded a single variant, creating false proofs.
    fn try_bitvec_discriminant(&mut self, dt_expr: &Expr, place: &Place) -> Option<Expr> {
        let ty = place.ty(self.body.locals()).into_option()?;
        debug!("codegen_rvalue_discriminant: is_bitvec=true, ty={:?}", ty);
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return None;
        };

        // Part of #2267: Use trimmed_name() instead of format!("{:?}") to avoid allocation.
        let type_name = def.trimmed_name();
        debug!("codegen_rvalue_discriminant: type_name={}", type_name);

        // Option<T> where T is a unit enum: derive discriminant from bitvec value.
        // The bitvec stores T's discriminant value for Some, or a niche value for None.
        // Check: if value matches any valid T discriminant → Some (1), else → None (0).
        // Part of #3094: replaces symbolic over-approximation that caused false failures
        // for concrete Option<unit_enum> values like Some(Foo::A).
        if type_name.contains("Option") {
            if let Some(result) = self.try_option_unit_enum_discriminant(dt_expr, &args) {
                return Some(result);
            }
        }

        // ControlFlow/Result stored as bitvec (and Option<T> with non-unit T):
        // use symbolic discriminant constrained to valid values {0, 1}
        // (sound over-approximation).
        if type_name.contains("ControlFlow")
            || type_name.contains("Result")
            || type_name.contains("Option")
        {
            let fn_name = self.ctx.current_fn_name();
            let mut discr_name = String::with_capacity(fn_name.len() + 30);
            discr_name.push_str(fn_name);
            discr_name.push_str("::local_");
            {
                use std::fmt::Write;
                let _ = write!(discr_name, "{}_bitvec_discr", place.local);
            }
            warn!(
                type_name = %type_name,
                discr_name = %discr_name,
                "bitvec-stored enum discriminant: using symbolic variable (both variants explored)"
            );
            let discr_var = self.ctx.declare_var(&discr_name, ptr_sort());
            let zero = Expr::bitvec_const(0, POINTER_WIDTH);
            let one = Expr::bitvec_const(1, POINTER_WIDTH);
            let valid = discr_var.clone().eq(zero).or(discr_var.clone().eq(one));
            self.ctx.assert(valid);
            return Some(discr_var);
        }

        // Unit enums stored as bitvec: the value IS the discriminant
        let variants = def.variants();
        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());
        if is_unit_enum {
            // Single-variant unit enum: constant discriminant, not unconstrained bitvec (Part of #3094).
            if variants.len() == 1 {
                let int_def = rustc_internal::internal(self.ctx.tcx, def);
                let d = int_def
                    .discriminant_for_variant(self.ctx.tcx, InternalVariantIdx::from_usize(0));
                // Part of #3543: Sign-extend signed discriminants (read must match write).
                let dv = sign_extend_discr_val(d.val, d.ty, self.ctx.tcx, 32);
                debug!("single-variant unit enum {type_name} discriminant = {}", dv);
                return Some(Expr::bitvec_const(dv, 32));
            }

            debug!("codegen_rvalue_discriminant: unit enum {type_name} bitvec - returning value");
            // Coerce to 32 bits for consistency with sort_inference.rs (#1417).
            let width = dt_expr.sort().bitvec_width();
            let owned = dt_expr.clone();
            let result = match width {
                Some(32) | None => owned,
                Some(w) if w < 32 => owned.zero_extend(32 - w),
                Some(_) => owned.extract(31, 0),
            };
            return Some(result);
        }

        None
    }

    /// For `Option<T>` where T is a unit enum, derive the Option discriminant
    /// from the bitvec value. Returns Some(1) if the value matches any valid T
    /// discriminant, Some(0) otherwise (None niche). Part of #3094.
    fn try_option_unit_enum_discriminant(
        &self,
        dt_expr: &Expr,
        option_args: &rustc_public::ty::GenericArgs,
    ) -> Option<Expr> {
        // Extract T from Option<T>
        let inner_ty = match option_args.0.first()? {
            GenericArgKind::Type(ty) => *ty,
            _ => return None,
        };
        let TyKind::RigidTy(RigidTy::Adt(inner_def, _)) = inner_ty.kind() else {
            return None;
        };
        let inner_variants = inner_def.variants();
        // Only handle unit enums (all variants fieldless)
        if !inner_variants.iter().all(|v| v.fields().is_empty()) {
            return None;
        }
        if inner_variants.is_empty() {
            return None;
        }

        let internal_def = rustc_internal::internal(self.ctx.tcx, inner_def);
        let bv_width = dt_expr.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
        let one = Expr::bitvec_const(1, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0, POINTER_WIDTH);

        // Build: ITE(val==d0 OR val==d1 OR ... OR val==dn, 1, 0)
        // where d0..dn are the valid inner enum discriminant values.
        let mut is_some: Option<Expr> = None;
        for (i, _variant) in inner_variants.iter().enumerate() {
            let variant_idx = InternalVariantIdx::from_usize(i);
            let discr = internal_def.discriminant_for_variant(self.ctx.tcx, variant_idx);
            // Part of #3543: Sign-extend signed discriminants (read must match write).
            let discr_val = sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, bv_width);
            let discr_const = Expr::bitvec_const(discr_val, bv_width);
            let matches_variant = dt_expr.clone().eq(discr_const);
            is_some = Some(match is_some {
                None => matches_variant,
                Some(acc) => acc.or(matches_variant),
            });
        }

        let is_some = is_some?;
        debug!(
            "codegen_rvalue_discriminant: Option<unit_enum> - deriving discriminant from bitvec value, inner_type={}, num_variants={}",
            inner_def.trimmed_name(),
            inner_variants.len()
        );
        Some(Expr::ite(is_some, one, zero))
    }

    /// Try codegen_place fallback for projected discriminant places.
    fn try_place_fallback_discriminant(&mut self, place: &Place) -> Option<Expr> {
        if place.projection.is_empty() {
            return None;
        }
        let place_expr = self.codegen_place(place)?;
        debug!("codegen_rvalue_discriminant: codegen_place returned sort={:?}", place_expr.sort());
        if let Some(result) = Self::try_coroutine_discriminant_expr(&place_expr) {
            return Some(result);
        }
        // Unit enums stored as bitvec: the value IS the discriminant
        if place_expr.sort().is_bitvec() {
            return Some(place_expr);
        }
        // Datatypes: extract discriminant using is_constructor
        if let SortInner::Datatype(dt) = place_expr.sort().inner() {
            // Same payload-order correction as `try_env_discriminant`.
            if let Some(result) = self.try_option_like_discriminant(dt, &place_expr, place) {
                return Some(result);
            }
            return Some(Self::build_discriminant_ite_chain(
                &dt.name,
                &dt.constructors,
                &place_expr,
            ));
        }
        None
    }

    /// Handle unit enum discriminant resolution.
    fn try_unit_enum_discriminant(&mut self, place: &Place, target_base: &str) -> Option<Expr> {
        let ty = place.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
            return None;
        };

        let variants = def.variants();
        let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());
        if !is_unit_enum {
            return None;
        }

        // Single-variant: return actual discriminant value
        if variants.len() == 1 {
            let internal_def = rustc_internal::internal(self.ctx.tcx, def);
            let variant_idx = InternalVariantIdx::from_usize(0);
            let discr = internal_def.discriminant_for_variant(self.ctx.tcx, variant_idx);
            // Part of #3543: Sign-extend signed discriminants (read must match write).
            let discriminant_val = sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, 32);
            debug!(
                "codegen_rvalue_discriminant: single-variant unit enum - returning {}",
                discriminant_val
            );
            return Some(Expr::bitvec_const(discriminant_val, 32));
        }

        // Multi-variant: try env lookup
        if let Some(expr) = self.env_lookup(target_base) {
            return Some(expr.clone());
        }

        // Fallback: symbolic variable
        let name = self.ssa_name(place, false);
        let num_variants = variants.len();
        let bits = if num_variants <= 65536 { 32 } else { 64 };
        Some(self.ctx.declare_var(&name, Sort::bitvec(bits)))
    }

    fn try_coroutine_discriminant_expr(expr: &Expr) -> Option<Expr> {
        let discr = crate::codegen_ay::types::coroutine_discriminant_select(expr.clone())?;
        Some(match discr.sort().bitvec_width() {
            Some(width) if width < POINTER_WIDTH => discr.zero_extend(POINTER_WIDTH - width),
            Some(width) if width > POINTER_WIDTH => discr.extract(POINTER_WIDTH - 1, 0),
            _ => discr,
        })
    }

    // ── SwitchInt→variant bridge (Effort 2, #3017) ───────────────────────────
    //
    // Thread the active variant established by a `Discriminant`+`SwitchInt` on the
    // current path to the arm's field read, and assert `is_constructor` on the
    // IDENTICAL SSA datatype term the field selects from. All helpers here fail
    // CLOSED: any uncertainty yields None/no-match, preserving the pre-existing
    // variant-0 fail-close.

    /// Version-INDEPENDENT canonical storage key for `place`, shared by the
    /// discriminant-read (GEN) and field-read (USE) sites so the SAME storage maps
    /// to byte-identical keys. A single leading `Deref` is resolved to its pointee
    /// base via `ref_pointees` (canonicalizing aliases to the same storage); every
    /// remaining projection MUST be a `Field` (appended as `_field_{i}`). Any other
    /// shape (second Deref, Index, Downcast, untracked ref, …) returns `None`.
    ///
    /// Collision-freedom: two places produce the same key iff they share the same
    /// canonical storage root AND identical field path — i.e. they ARE the same
    /// storage location. The USE site additionally requires `dt_name` and the term's
    /// datatype sort to match, so even a hypothetical name coincidence cannot assert
    /// on a term of a different datatype.
    pub(super) fn variant_fact_place_key(&self, place: &Place) -> Option<Arc<str>> {
        use std::fmt::Write;
        let fn_name = self.ctx.current_fn_name();
        let (mut key, proj_start) =
            if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                let ref_base = crate::codegen_ay::names::local_name(fn_name, place.local);
                let pointee = self.ref_pointees.get(ref_base.as_str())?;
                (pointee.to_string(), 1)
            } else {
                (crate::codegen_ay::names::local_name(fn_name, place.local), 0)
            };
        for proj in &place.projection[proj_start..] {
            match proj {
                ProjectionElem::Field(field, _) => {
                    let _ = write!(key, "_field_{}", field);
                }
                _ => return None,
            }
        }
        Some(Arc::from(key.as_str()))
    }

    /// Resolve the version-independent STORAGE ROOT (no field suffix) written by
    /// `place`, for over-approximate fact killing. A leading `Deref` resolves to its
    /// pointee base; an untracked Deref returns `None` (caller over-kills all facts).
    fn variant_fact_kill_root(&self, place: &Place) -> Option<Arc<str>> {
        let fn_name = self.ctx.current_fn_name();
        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            self.ref_pointees
                .get(crate::codegen_ay::names::local_name(fn_name, place.local).as_str())
                .cloned()
        } else {
            Some(Arc::from(crate::codegen_ay::names::local_name(fn_name, place.local).as_str()))
        }
    }

    /// KILL: drop every variant fact whose storage could be invalidated by a write to
    /// `place` (an `Assign`/`SetDiscriminant` destination). Conservative — any fact
    /// whose `place_key` shares the write's storage root is dropped; if the root is
    /// unresolvable, ALL facts are dropped (over-kill on doubt keeps us fail-closed).
    pub(super) fn kill_variant_facts_for_place(&mut self, place: &Place) {
        if self.current_variant_facts.is_empty() {
            return;
        }
        match self.variant_fact_kill_root(place) {
            Some(root) => {
                self.current_variant_facts.retain(|f| !f.place_key.starts_with(&*root));
            }
            None => self.current_variant_facts.clear(),
        }
    }

    /// The bare local a SwitchInt discriminant operand traces to (`Copy`/`Move` of a
    /// projection-free place), else `None`.
    pub(super) fn discr_local_of_operand(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        }
    }

    /// Map a SwitchInt `case_val` to the UNIQUE ADT variant index whose discriminant
    /// equals it (MIR truth via `discriminant_for_variant` + `sign_extend_discr_val`),
    /// independent of the ite-encoding convention. Returns `None` if no variant — or
    /// (defensively) more than one — matches.
    pub(super) fn variant_idx_for_case_val(
        &self,
        adt_def: rustc_public::ty::AdtDef,
        num_variants: usize,
        case_val: u128,
    ) -> Option<usize> {
        let internal_def = rustc_internal::internal(self.ctx.tcx, adt_def);
        let mut found = None;
        for i in 0..num_variants {
            let discr = internal_def
                .discriminant_for_variant(self.ctx.tcx, InternalVariantIdx::from_usize(i));
            let dv = sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, 128);
            if dv == case_val {
                if found.is_some() {
                    return None;
                }
                found = Some(i);
            }
        }
        found
    }

    /// True iff every variant's discriminant value equals its declaration index
    /// (the identity permutation). This is the soundness gate for the bridge: the
    /// per-branch fact GUARD is compared against `build_discriminant_ite_chain`,
    /// which outputs the declaration INDEX (0..N-1), whereas the SwitchInt case_val
    /// is the DISCRIMINANT VALUE. The two spaces agree ONLY for the identity
    /// permutation. For explicit-`#[repr]` / permuted / signed discriminants they
    /// diverge, which would pair the correct ctor with a mis-mapped guard and
    /// manufacture an `is-B => is-C` contradiction (a FALSE PROOF that renders a
    /// live arm dead). Gate the bridge on identity; non-identity enums fall back to
    /// the #3017 variant-0 fail-close (sound, no improvement).
    pub(super) fn enum_has_identity_discriminants(
        &self,
        adt_def: rustc_public::ty::AdtDef,
        num_variants: usize,
    ) -> bool {
        let internal_def = rustc_internal::internal(self.ctx.tcx, adt_def);
        for i in 0..num_variants {
            let discr = internal_def
                .discriminant_for_variant(self.ctx.tcx, InternalVariantIdx::from_usize(i));
            let dv = sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, 128);
            if dv != i as u128 {
                return false;
            }
        }
        true
    }

    /// Stage the field-read place context for the NEXT `apply_post_deref_projections`
    /// call so its `Field` arm can compute the parent-enum place key. Gated on live
    /// facts: when none are live the bridge cannot fire, so we skip the `Place` clone
    /// (leaving the field `None`). `proj_base` is the number of leading projections of
    /// `place` already consumed before the slice handed to that call.
    pub(super) fn stage_bridge_enum_read(&mut self, place: &Place, proj_base: usize) {
        if !self.current_variant_facts.is_empty() {
            self.bridge_enum_read = Some((place.clone(), proj_base));
        }
    }

    /// USE: if a live `VariantFact` provably pins the datatype term `expr` (loaded from
    /// the storage identified by `enum_key`) to a specific constructor, assert
    /// `guard => is_constructor` on the IDENTICAL term and return that constructor
    /// index — mirroring `assert_downcast_variant_guards`. Returns `None` (→ caller
    /// keeps its variant-0 fail-close) whenever the key/`dt_name`/sort/ctor do not all
    /// match, or no fact is live.
    pub(super) fn bridge_variant_for_field(
        &mut self,
        expr: &Expr,
        enum_key: Option<&Arc<str>>,
    ) -> Option<usize> {
        let enum_key = enum_key?;
        if self.current_variant_facts.is_empty() {
            return None;
        }
        let key: &str = enum_key;
        let dt_name = expr.sort().datatype_name()?;
        let fact = self
            .current_variant_facts
            .iter()
            .find(|f| &*f.place_key == key && &*f.dt_name == dt_name)
            .cloned()?;
        // The fact's constructor must exist at `ctor_idx` in THIS datatype sort.
        let dt = expr.sort().datatype_sort()?;
        match dt.constructors.get(fact.ctor_idx) {
            Some(c) if c.name.as_str() == &*fact.ctor_name => {}
            _ => return None,
        }
        // `try_is_constructor` fails closed if the sort is somehow not a datatype.
        let Ok(is_c) = expr.clone().try_is_constructor(&*fact.dt_name, &*fact.ctor_name) else {
            return None;
        };
        let guarded = fact.guard.clone().implies(is_c);
        self.ctx.assert(guarded);
        Some(fact.ctor_idx)
    }
}
