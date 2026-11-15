// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Memory swap intrinsic codegen for AY.
//!
//! Part of #3477: BMC parity with CHC encoding.
//! Handles typed_swap_nonoverlapping and std::mem::swap.

use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::{IntoOption, StatementCodegen};
use crate::kani_middle::abi::LayoutOf;

#[derive(Debug)]
struct TypedSwapPointee {
    load_base: Option<String>,
    update_bases: Vec<String>,
}

#[derive(Debug)]
struct TypedSwapResolvedPointee {
    base: String,
    aliases: Vec<String>,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen typed_swap_nonoverlapping / std::mem::swap.
    ///
    /// Models as: old_x = *x; old_y = *y; *x = old_y; *y = old_x
    /// Both pointer operands must be non-overlapping.
    ///
    /// REQUIRES: args[0] = pointer x, args[1] = pointer y
    /// ENSURES: Memory at *x gets old value of *y and vice versa
    pub(in crate::codegen_ay::statement) fn codegen_typed_swap(
        &mut self,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_typed_swap: insufficient args ({})", args.len());
            return None;
        }

        let ptr_x = self.codegen_operand(&args[0])?;
        let ptr_y = self.codegen_operand(&args[1])?;
        debug!("codegen_typed_swap: ptr_x_sort={:?}, ptr_y_sort={:?}", ptr_x.sort(), ptr_y.sort());

        // Determine element size from the pointer type.
        // args[0] is *mut T — get T's size from the operand's type.
        let ptr_ty = args[0].ty(self.body.locals()).into_option()?;
        let pointee_ty = match ptr_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(ty, _)) => ty,
            TyKind::RigidTy(RigidTy::Ref(_, ty, _)) => ty,
            _ => {
                debug!("codegen_typed_swap: non-pointer type {:?}", ptr_ty);
                return None;
            }
        };
        let size = LayoutOf::new(pointee_ty).size_of().unwrap_or(1);
        debug!("codegen_typed_swap: element size = {} bytes", size);
        if size == 0 {
            return target;
        }

        // Load old values from both locations
        let x_pointee = self.typed_swap_pointee(&args[0]);
        let y_pointee = self.typed_swap_pointee(&args[1]);
        let old_x = self.typed_swap_load_old_value(x_pointee.as_ref(), ptr_x.clone(), size as u32);
        let old_y = self.typed_swap_load_old_value(y_pointee.as_ref(), ptr_y.clone(), size as u32);

        // FC-06(bmc): swap writes are env-level, invisible to the ref-deref
        // store hook — certify each against a non-empty modifies footprint
        // (by pointer value or tracked name) so a modifies-only checked
        // swap discharges its per-store assigns obligations (corpus:
        // function-contract/modifies/simple_only_verification_modifies
        // emitted zero VCs and the vacuity gate refused the proof).
        let x_base = x_pointee.as_ref().and_then(|p| p.load_base.clone());
        let y_base = y_pointee.as_ref().and_then(|p| p.load_base.clone());
        self.bmc_modifies_certify_swap_store(x_base.as_deref());
        self.bmc_modifies_certify_swap_store(y_base.as_deref());

        // The flattened components of each pointee (`{base}.0` discriminant,
        // `{base}_variant_V_field_N` payload, `{base}_field_N`) are part of its
        // value: a flattened `Option<u8>` keeps its variant under `{base}.0`, and
        // a swap that exchanged only the payload word left `o.0 = 1` after
        // `mem::swap(&mut o, &mut q)` with `q = None`, so `o == None` read
        // `Some(0)` and `assert!(!(o == None))` was proved
        // (tools/soundness-duals/negative/review_r18_mutate_then_compare.rs).
        let x_components = self.typed_swap_components(x_base.as_deref());
        let y_components = self.typed_swap_components(y_base.as_deref());

        // Cross-store: *x = old_y, *y = old_x
        self.store_memory_bytes_on_path(ptr_x, old_y.clone(), "typed_swap store");
        self.store_memory_bytes_on_path(ptr_y, old_x.clone(), "typed_swap store");
        self.typed_swap_update_pointees(x_pointee.as_ref(), old_y);
        self.typed_swap_update_pointees(y_pointee.as_ref(), old_x);
        self.typed_swap_exchange_components(
            x_pointee.as_ref(),
            y_pointee.as_ref(),
            x_components,
            y_components,
        );

        // The swapped VALUES may themselves be pointers (`mem::swap(&mut p, &mut q)`
        // with `p, q: &mut u8`): their storage now holds each other's address, so
        // the pointee bindings recorded for `p` and `q` must travel with them, or a
        // later `*p = 7` writes `p`'s OLD referent: `swap_refs_store_must_fail`
        // (`assert!(a == 7)` after the swap made `p` point at `b`) verified
        // SUCCESSFUL and the safe twin FAILED with a Genuine counterexample
        // (negative/merged_pointer_shapes.rs). Swap the two entries, or poison both
        // so any later read through them fails closed.
        //
        // The pointer need not BE the swapped value: an `Option<*mut u8>`, a
        // `Result`, a tuple or an array carries one just as well, and
        // `let mut a: Option<*mut u8> = Some(&mut x); let mut b = Some(&mut y);
        // mem::swap(&mut a, &mut b); *a.unwrap() = 9; assert!(y == 2)` verified
        // SUCCESSFUL with `[AY:PROOF_QUALIFIERS:clean]` while its safe twin was
        // FAILED [AY:CTREX_CAT:Genuine], because `is_pointer_like_ty` answered
        // `false` for the carrier and nothing was exchanged OR recorded (fourth
        // adversarial review of m3/soundness-fixes-2, 2026-09-14, defect M2/D3).
        if Self::is_pointer_like_ty(pointee_ty) || Self::ty_carries_a_pointer_value(pointee_ty) {
            self.typed_swap_pointer_bindings(x_base.as_deref(), y_base.as_deref());
        }

        target
    }

    /// Snapshot the flattened components recorded under a pointee base.
    fn typed_swap_components(&self, base: Option<&str>) -> Vec<(String, ay_bindings::Expr)> {
        base.map(|base| Self::collect_flattened_value_entries(&self.current_env, base))
            .unwrap_or_default()
    }

    /// Give each pointee the other's flattened components.
    ///
    /// A component one side records and the other does not has no exact
    /// counterpart: it is left unconstrained, and the harness is marked so it
    /// cannot come back clean.
    fn typed_swap_exchange_components(
        &mut self,
        x_pointee: Option<&TypedSwapPointee>,
        y_pointee: Option<&TypedSwapPointee>,
        x_components: Vec<(String, ay_bindings::Expr)>,
        y_components: Vec<(String, ay_bindings::Expr)>,
    ) {
        if x_components.is_empty() && y_components.is_empty() {
            return;
        }
        let x_suffixes: Vec<&String> = x_components.iter().map(|(suffix, _)| suffix).collect();
        let y_suffixes: Vec<&String> = y_components.iter().map(|(suffix, _)| suffix).collect();
        let unmatched: Vec<(String, ay_bindings::Sort)> = x_components
            .iter()
            .filter(|(suffix, _)| !y_suffixes.contains(&suffix))
            .chain(y_components.iter().filter(|(suffix, _)| !x_suffixes.contains(&suffix)))
            .map(|(suffix, expr)| (suffix.clone(), expr.sort().clone()))
            .collect();
        let (Some(x_pointee), Some(y_pointee)) = (x_pointee, y_pointee) else {
            self.ctx.unsupported_with_fallback(
                "typed_swap_components",
                "flattened components of an unresolved swap pointee".to_string(),
            );
            return;
        };
        for base in &x_pointee.update_bases {
            self.apply_flattened_value_entries(base, y_components.clone());
        }
        for base in &y_pointee.update_bases {
            self.apply_flattened_value_entries(base, x_components.clone());
        }
        if unmatched.is_empty() {
            return;
        }
        self.ctx.unsupported_with_fallback(
            "typed_swap_components",
            format!("flattened components without a counterpart: {unmatched:?}"),
        );
        for base in x_pointee.update_bases.iter().chain(&y_pointee.update_bases) {
            for (suffix, sort) in &unmatched {
                let key = format!("{base}{suffix}");
                let name = self.ssa_name_from_base(&key, true);
                let fresh = self.ctx.declare_var(&name, sort.clone());
                self.env_update(key, fresh);
            }
        }
    }

    /// Exchange the `ref_pointees` entries of two pointer-typed storages whose
    /// values were just swapped. Both entries must be present, unpoisoned and
    /// unaliased by nested bindings; otherwise every binding under either name is
    /// poisoned and the statement records a fail-closed fallback.
    fn typed_swap_pointer_bindings(&mut self, x_base: Option<&str>, y_base: Option<&str>) {
        let (Some(x_base), Some(y_base)) = (x_base, y_base) else {
            self.ctx.unsupported_with_fallback(
                "mem::swap of pointers: a swapped storage is not tracked",
                "typed_swap",
            );
            return;
        };
        let generation = self.ref_pointees.generation();
        let x_target = self.ref_pointees.get(x_base).cloned();
        let y_target = self.ref_pointees.get(y_base).cloned();
        let exact = !self.ref_pointees.is_poisoned(x_base)
            && !self.ref_pointees.is_poisoned(y_base)
            && self.ref_pointees.nested_keys(x_base).is_empty()
            && self.ref_pointees.nested_keys(y_base).is_empty();
        match (x_target, y_target) {
            (Some(xt), Some(yt)) if exact => {
                self.ref_pointees.insert(std::sync::Arc::from(x_base), yt);
                self.ref_pointees.insert(std::sync::Arc::from(y_base), xt);
                debug!(x_base, y_base, "typed_swap: pointee bindings exchanged");
            }
            // A CARRIER (an `Option`, a `Result`, a tuple, an array) holds the
            // pointer under a derived name, so neither base has an entry of its
            // own. Exchange the nested entries when both sides carry exactly the
            // same slots; anything else falls through and fails closed.
            (None, None) if self.typed_swap_exchange_carrier_bindings(x_base, y_base) => {}
            _ => {
                // Bindings exist for at most one side, are merged, or carry nested
                // entries: poison what is there (a stale entry would name the old
                // referent) and fail closed.
                self.ref_pointees.poison_stale_since(x_base, generation);
                self.ref_pointees.poison_stale_since(y_base, generation);
                self.ctx.unsupported_with_fallback(
                    "mem::swap of pointers: pointee bindings not exchanged",
                    format!("{x_base} <-> {y_base}"),
                );
            }
        }
    }

    /// Exchange the pointee bindings held under two CARRIER storages: every
    /// entry `{x_base}{suffix}` against `{y_base}{suffix}`, and only when both
    /// sides carry exactly the same suffixes and none of them is poisoned.
    ///
    /// Returns `false` when the exchange cannot be made exactly; the caller then
    /// poisons both sides and records a fail-closed reason.
    fn typed_swap_exchange_carrier_bindings(&mut self, x_base: &str, y_base: &str) -> bool {
        let x_keys = self.ref_pointees.nested_keys(x_base);
        let y_keys = self.ref_pointees.nested_keys(y_base);
        if x_keys.is_empty() || x_keys.len() != y_keys.len() {
            return false;
        }
        let mut pairs = Vec::with_capacity(x_keys.len());
        for x_key in &x_keys {
            let Some(suffix) = x_key.strip_prefix(x_base) else {
                return false;
            };
            let y_key = format!("{y_base}{suffix}");
            if !self.ref_pointees.has_entry(&y_key) {
                return false;
            }
            if self.ref_pointees.is_poisoned(x_key) || self.ref_pointees.is_poisoned(&y_key) {
                return false;
            }
            let (Some(xt), Some(yt)) = (
                self.ref_pointees.get(x_key.as_ref()).cloned(),
                self.ref_pointees.get(y_key.as_str()).cloned(),
            ) else {
                return false;
            };
            pairs.push((std::sync::Arc::clone(x_key), std::sync::Arc::<str>::from(y_key), xt, yt));
        }
        for (x_key, y_key, xt, yt) in pairs {
            self.ref_pointees.insert(x_key, yt);
            self.ref_pointees.insert(y_key, xt);
        }
        debug!(x_base, y_base, "typed_swap: carrier pointee bindings exchanged");
        true
    }

    fn typed_swap_pointee(&mut self, operand: &Operand) -> Option<TypedSwapPointee> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => return None,
        };
        let ref_base = self.ssa_base_name(place);
        let pointee_base = self.ref_pointees.get(ref_base.as_str())?.to_string();
        let mut update_bases = Vec::new();

        let load_base = if let Some(resolved) = self.typed_swap_resolve_deref_pointee(&pointee_base)
        {
            Self::typed_swap_push_unique(&mut update_bases, resolved.base.clone());
            for alias in resolved.aliases {
                Self::typed_swap_push_unique(&mut update_bases, alias);
            }
            Some(resolved.base)
        } else if Self::typed_swap_has_local_deref_suffix(&pointee_base) {
            // A raw-pointer deref alias with no ref_pointees chain is not a stack local.
            // Load through byte memory, but refresh the alias so later `*ptr` reads
            // through the same tracked raw-pointer temporary see the swap.
            Self::typed_swap_push_unique(&mut update_bases, pointee_base);
            None
        } else {
            Self::typed_swap_push_unique(&mut update_bases, pointee_base.clone());
            Some(pointee_base)
        };

        Some(TypedSwapPointee { load_base, update_bases })
    }

    fn typed_swap_load_old_value(
        &mut self,
        pointee: Option<&TypedSwapPointee>,
        ptr: ay_bindings::Expr,
        size: u32,
    ) -> ay_bindings::Expr {
        pointee
            .and_then(|pointee| pointee.load_base.as_deref())
            .and_then(|base| self.env_lookup(base).cloned())
            .unwrap_or_else(|| self.ctx.load_memory_bytes(ptr, size))
    }

    fn typed_swap_update_pointees(
        &mut self,
        pointee: Option<&TypedSwapPointee>,
        value: ay_bindings::Expr,
    ) {
        let Some(pointee) = pointee else { return };
        for base in &pointee.update_bases {
            self.typed_swap_update_pointee(base, value.clone());
        }
    }

    fn typed_swap_update_pointee(&mut self, base: &str, value: ay_bindings::Expr) {
        let ssa_name = self.ssa_name_from_base(base, true);
        let var = self.ctx.declare_var(&ssa_name, value.sort().clone());
        self.assert_ssa_def(var.clone(), value, base);
        self.env_update(base.to_owned(), var);
    }

    /// Resolve a (possibly `_deref`-aliased) pointee base name to its root
    /// plus every alias along the chain. Used by typed_swap and by the
    /// contract havoc (`write_any_slim`) so a store through an alias
    /// refreshes ALL names that denote the same storage.
    pub(super) fn resolve_deref_pointee_chain(&self, pointee_base: &str) -> Vec<String> {
        match self.typed_swap_resolve_deref_pointee(pointee_base) {
            Some(resolved) => {
                let mut v = vec![resolved.base];
                v.extend(resolved.aliases);
                if !v.iter().any(|n| n == pointee_base) {
                    v.push(pointee_base.to_owned());
                }
                v
            }
            None => vec![pointee_base.to_owned()],
        }
    }

    fn typed_swap_resolve_deref_pointee(
        &self,
        pointee_base: &str,
    ) -> Option<TypedSwapResolvedPointee> {
        let mut current = pointee_base.to_owned();
        let mut aliases = Vec::new();
        for _ in 0..8 {
            let Some((root_base, suffix)) = Self::typed_swap_split_local_base(&current) else {
                return (!aliases.is_empty())
                    .then_some(TypedSwapResolvedPointee { base: current, aliases });
            };
            let Some(rest) = suffix.strip_prefix("_deref") else {
                return (!aliases.is_empty())
                    .then_some(TypedSwapResolvedPointee { base: current, aliases });
            };
            Self::typed_swap_push_unique(&mut aliases, current.clone());

            let target_base = self.ref_pointees.get(root_base.as_str())?;
            let mut next = String::with_capacity(target_base.len() + rest.len());
            next.push_str(target_base.as_ref());
            next.push_str(rest);
            if next == current {
                return None;
            }
            current = next;
        }
        None
    }

    fn typed_swap_has_local_deref_suffix(base: &str) -> bool {
        Self::typed_swap_split_local_base(base)
            .is_some_and(|(_, suffix)| suffix.starts_with("_deref"))
    }

    fn typed_swap_split_local_base(base: &str) -> Option<(String, &str)> {
        let (fn_prefix, local_suffix) = base.split_once("::local_")?;
        let local_digits_len = local_suffix.bytes().take_while(u8::is_ascii_digit).count();
        if local_digits_len == 0 {
            return None;
        }
        let local_idx = local_suffix[..local_digits_len].parse::<usize>().ok()?;
        let root = crate::codegen_ay::names::local_name(fn_prefix, local_idx);
        Some((root, &local_suffix[local_digits_len..]))
    }

    fn typed_swap_push_unique(bases: &mut Vec<String>, base: String) {
        if !bases.iter().any(|existing| existing == &base) {
            bases.push(base);
        }
    }
}
