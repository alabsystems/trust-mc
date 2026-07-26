// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared set operations for BTreeSet and HashSet BMC stubs (Part of #2308).
//!
//! Both collection types model sets as `Array<Key, Bool>` (element presence maps)
//! and share identical operation semantics. This module consolidates the duplicated
//! logic, parameterized only by collection name (for fresh variable prefixes and
//! debug messages).

use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, trace, warn};

use super::super::{IntoOption, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen set `new` operation: `const_array(key_sort, false)`, len = 0.
    pub(in super::super) fn set_op_new(
        &mut self,
        collection_name: &str,
        key_sort: Sort,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let empty_set = Expr::const_array(key_sort, Expr::bool_const(false));
        self.assign_value_to_place(destination, empty_set);

        let dest_base = self.ssa_base_name(destination);
        let len_name = crate::codegen_ay::names::len_name(&dest_base);
        trace!(%len_name, "{collection_name}New: initializing length to 0");
        let zero_len = Expr::bitvec_const(0, POINTER_WIDTH);
        self.env_update(len_name, zero_len);
        target
    }

    /// Codegen set `insert` operation: `store(key, true)`, return `was_absent`.
    pub(in super::super) fn set_op_insert(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("{collection_name}::insert requires 2 args (self, value) — fail-closed (#2497)");
            return None;
        }

        let resolved = self.resolve_collection_base(&args[0]);
        let key = self.codegen_operand(&args[1]);

        if let (Some((base, set)), Some(k)) = (resolved, key) {
            debug!("{collection_name}Insert: set_sort={:?}, key_sort={:?}", set.sort(), k.sort());
            let was_present = set.clone().select(k.clone());
            let new_set = set.store(k, Expr::bool_const(true));
            self.env_update(std::sync::Arc::clone(&base), new_set);
            let was_absent = was_present.not();
            self.assign_value_to_place(destination, was_absent.clone());

            let len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(old_len) = self.env_lookup(&len_name).cloned() {
                let one = Expr::bitvec_const(1, POINTER_WIDTH);
                let incremented = old_len.clone().bvadd(one);
                let new_len = Expr::ite(was_absent, incremented, old_len);
                trace!(%len_name, "{collection_name}Insert: updating length (conditional increment)");
                self.env_update(len_name, new_len);
            }
        } else {
            let prefix = collection_name.to_ascii_lowercase();
            let name = self.ctx.fresh_name_with_suffix(&prefix, "insert");
            let result = self.ctx.declare_var(&name, bool_sort());
            self.assign_value_to_place(destination, result);
            if let Some(base) = self.get_map_base_from_ref(&args[0]) {
                let len_name = crate::codegen_ay::names::len_name(&base);
                if self.env_lookup(&len_name).is_some() {
                    let fresh = self.ctx.fresh_name_with_suffix(&prefix, "len");
                    let len_sym = self.ctx.declare_var(&fresh, ptr_sort());
                    self.env_update(len_name, len_sym);
                }
            }
        }
        target
    }

    /// Codegen set `contains` operation: `select(set, key)`.
    pub(in super::super) fn set_op_contains(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!(
                "{collection_name}::contains requires 2 args (self, value) — fail-closed (#2497)"
            );
            return None;
        }

        let resolved = self.resolve_collection_base(&args[0]);
        let key = self.get_value_through_ref(&args[1]);

        if let (Some((_base, set)), Some(k)) = (resolved, key) {
            debug!("{collection_name}Contains: set_sort={:?}, key_sort={:?}", set.sort(), k.sort());
            let contains = set.select(k);
            self.assign_value_to_place(destination, contains);
        } else {
            let prefix = collection_name.to_ascii_lowercase();
            let name = self.ctx.fresh_name_with_suffix(&prefix, "contains");
            let result = self.ctx.declare_var(&name, bool_sort());
            self.assign_value_to_place(destination, result);
        }
        target
    }

    /// Codegen set `remove` operation: `store(key, false)`, return `was_present`.
    pub(in super::super) fn set_op_remove(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("{collection_name}::remove requires 2 args (self, value) — fail-closed (#2497)");
            return None;
        }

        let resolved = self.resolve_collection_base(&args[0]);
        let key = self.get_value_through_ref(&args[1]);

        if let (Some((base, set)), Some(k)) = (resolved, key) {
            debug!("{collection_name}Remove: set_sort={:?}, key_sort={:?}", set.sort(), k.sort());
            let was_present = set.clone().select(k.clone());
            let new_set = set.store(k, Expr::bool_const(false));
            self.env_update(std::sync::Arc::clone(&base), new_set);
            self.assign_value_to_place(destination, was_present.clone());

            let len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(old_len) = self.env_lookup(&len_name).cloned() {
                let one = Expr::bitvec_const(1, POINTER_WIDTH);
                let decremented = old_len.clone().bvsub(one);
                let new_len = Expr::ite(was_present, decremented, old_len);
                trace!(%len_name, "{collection_name}Remove: updating length (conditional decrement)");
                self.env_update(len_name, new_len);
            }
        } else {
            let prefix = collection_name.to_ascii_lowercase();
            let name = self.ctx.fresh_name_with_suffix(&prefix, "remove");
            let result = self.ctx.declare_var(&name, bool_sort());
            self.assign_value_to_place(destination, result);
            if let Some(base) = self.get_map_base_from_ref(&args[0]) {
                let len_name = crate::codegen_ay::names::len_name(&base);
                if self.env_lookup(&len_name).is_some() {
                    let fresh = self.ctx.fresh_name_with_suffix(&prefix, "len");
                    let len_sym = self.ctx.declare_var(&fresh, ptr_sort());
                    self.env_update(len_name, len_sym);
                }
            }
        }
        target
    }

    /// Codegen set `len` operation: return tracked length or symbolic fallback.
    pub(in super::super) fn set_op_len(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("{collection_name}::len requires 1 arg (self) — fail-closed (#2497)");
            return None;
        }

        let set_base = self.get_map_base_from_ref(&args[0]);
        if let Some(base) = set_base {
            let len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(len_expr) = self.env_lookup(&len_name).cloned() {
                debug!("{collection_name}Len: returning tracked length for base={}", base);
                self.assign_value_to_place(destination, len_expr);
                return target;
            }
        }

        let prefix = collection_name.to_ascii_lowercase();
        let name = self.ctx.fresh_name_with_suffix(&prefix, "len");
        let len = self.ctx.declare_var(&name, ptr_sort());
        self.assign_value_to_place(destination, len);
        target
    }

    /// Codegen set `is_empty` operation: `len == 0` or symbolic fallback.
    pub(in super::super) fn set_op_is_empty(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("{collection_name}::is_empty requires 1 arg (self) — fail-closed (#2497)");
            return None;
        }

        let set_base = self.get_map_base_from_ref(&args[0]);
        if let Some(base) = set_base {
            let len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(len_expr) = self.env_lookup(&len_name).cloned() {
                debug!("{collection_name}IsEmpty: checking tracked length for base={}", base);
                let zero = Expr::bitvec_const(0, POINTER_WIDTH);
                let is_empty_expr = len_expr.eq(zero);
                self.assign_value_to_place(destination, is_empty_expr);
                return target;
            }
        }

        let prefix = collection_name.to_ascii_lowercase();
        let name = self.ctx.fresh_name_with_suffix(&prefix, "is_empty");
        let is_empty = self.ctx.declare_var(&name, bool_sort());
        self.assign_value_to_place(destination, is_empty);
        target
    }

    /// Codegen set `clear` operation: `const_array(key_sort, false)`, len = 0.
    pub(in super::super) fn set_op_clear(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("{collection_name}::clear requires 1 arg (self) — fail-closed (#2497)");
            return None;
        }

        let resolved = self.resolve_collection_base(&args[0]);
        if let Some((ref base, ref set)) = resolved
            && let Some(arr) = set.sort().array_sort()
        {
            let key_sort = arr.index_sort.clone();
            let empty_set = Expr::const_array(key_sort, Expr::bool_const(false));
            self.env_update(std::sync::Arc::clone(base), empty_set);
        }

        if let Some((base, _)) = resolved {
            let len_name = crate::codegen_ay::names::len_name(&base);
            trace!(%len_name, "{collection_name}Clear: resetting length to 0");
            let zero_len = Expr::bitvec_const(0, POINTER_WIDTH);
            self.env_update(len_name, zero_len);
        }
        target
    }

    /// Codegen set `clone` operation: copy set and length tracking.
    pub(in super::super) fn set_op_clone(
        &mut self,
        collection_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("{collection_name}::clone requires 1 arg (self) — fail-closed (#2497)");
            return None;
        }

        if let Some((base, set)) = self.resolve_collection_base(&args[0]) {
            self.assign_value_to_place(destination, set);

            let src_len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(len_expr) = self.env_lookup(&src_len_name).cloned() {
                let dest_base = self.ssa_base_name(destination);
                let dest_len_name = crate::codegen_ay::names::len_name(&dest_base);
                trace!(%src_len_name, %dest_len_name, "{collection_name}Clone: copying length to cloned set");
                self.env_update(dest_len_name, len_expr);
            }
        } else {
            self.codegen_symbolic_result(destination);
        }
        target
    }

    /// Codegen set `into_iter` or `iter` operation: delegate to `make_set_into_iter`.
    pub(in super::super) fn set_op_iter(
        &mut self,
        collection_name: &str,
        method_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("{collection_name}::{method_name} requires 1 arg (self) — fail-closed (#2497)");
            return None;
        }

        if let Some((base, set)) = self.resolve_collection_base(&args[0]) {
            let iter = self.make_set_into_iter(set, Some(&base));
            self.assign_value_to_place(destination, iter);
        } else {
            self.codegen_symbolic_result(destination);
        }
        target
    }

    /// Infer key sort from a set destination type, parameterized by type name.
    #[must_use]
    pub(in super::super) fn infer_set_key_sort(
        &self,
        destination: &Place,
        type_name: &str,
    ) -> Option<Sort> {
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind()
            && def.trimmed_name() == type_name
        {
            return args.0.first().and_then(|arg| match arg {
                GenericArgKind::Type(ty) => Self::infer_sort_from_ty(*ty),
                _ => None, // external enum: GenericArgKind
            });
        }
        None
    }
}
