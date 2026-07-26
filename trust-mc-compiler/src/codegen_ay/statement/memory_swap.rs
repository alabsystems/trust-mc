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

        // Cross-store: *x = old_y, *y = old_x
        self.ctx.store_memory_bytes(ptr_x, old_y.clone());
        self.ctx.store_memory_bytes(ptr_y, old_x.clone());
        self.typed_swap_update_pointees(x_pointee.as_ref(), old_y);
        self.typed_swap_update_pointees(y_pointee.as_ref(), old_x);

        target
    }

    fn typed_swap_pointee(&mut self, operand: &Operand) -> Option<TypedSwapPointee> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
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
