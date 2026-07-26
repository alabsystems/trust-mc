// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// HashMap sort/option utilities extracted from hashmap.rs for structural decomposition.
// Converted from include!() to module for #2306.

use crate::codegen_ay::types::{bool_sort, ptr_sort};
use crate::rustc_public::CrateDef;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::warn;

use super::super::super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names::enum_sort;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Infer key and value sorts from a HashMap/TrustMcMap/BTreeMap destination type.
    ///
    /// Part of #1752: Include BTreeMap since its operations route through HashMap stubs.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn infer_hashmap_sorts(
        &self,
        destination: &Place,
    ) -> Option<(Sort, Sort)> {
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind() {
            let name = def.trimmed_name();
            // Part of #1752: BTreeMap operations route through HashMap stubs,
            // so we must infer sorts for BTreeMap types as well.
            if name == "HashMap" || name == "TrustMcMap" || name == "BTreeMap" {
                // Extract K, V from generic args
                let key_sort = args
                    .0
                    .first()
                    .and_then(|arg| match arg {
                        GenericArgKind::Type(ty) => Self::infer_sort_from_ty(*ty),
                        _ => None, // external enum: GenericArgKind
                    })
                    .unwrap_or(ptr_sort());

                let val_sort = args
                    .0
                    .get(1)
                    .and_then(|arg| match arg {
                        GenericArgKind::Type(ty) => Self::infer_sort_from_ty(*ty),
                        _ => None, // external enum: GenericArgKind
                    })
                    .unwrap_or(ptr_sort());

                let option_sort = self.make_option_sort(val_sort);
                return Some((key_sort, option_sort));
            }
        }
        None
    }

    /// Resolve a collection's base name and current expression from a reference operand.
    ///
    /// Combines `get_map_base_from_ref` + `env_lookup` into a single call.
    /// Returns `(base_name, expression)` or `None` if either step fails.
    pub(in crate::codegen_ay::statement) fn resolve_collection_base(
        &mut self,
        operand: &Operand,
    ) -> Option<(std::sync::Arc<str>, Expr)> {
        let base = self.get_map_base_from_ref(operand)?;
        let expr = self.env_lookup(base.as_ref()).cloned()?;
        Some((base, expr))
    }

    /// Get the base name of a HashMap from a reference operand.
    pub(in crate::codegen_ay::statement) fn get_map_base_from_ref(
        &mut self,
        operand: &Operand,
    ) -> Option<std::sync::Arc<str>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let ref_base = self.ssa_base_name(place);
                // Look up in ref_pointees
                self.ref_pointees.get(ref_base.as_str()).cloned().or_else(|| {
                    // Try direct lookup if not a reference
                    if self.env_lookup(&ref_base).is_some() {
                        Some(std::sync::Arc::from(ref_base))
                    } else {
                        None
                    }
                })
            }
            _ => None, // external enum: Operand
        }
    }

    /// Get or create a len symbol for a HashMap instance (#1315).
    ///
    /// Returns the existing len symbol if already tracked, otherwise creates
    /// a fresh symbolic bitvec and stores it for future calls.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn get_or_create_hashmap_len(
        &mut self,
        map_base: &str,
    ) -> Expr {
        if let Some(existing) = self.hashmap_len_symbols.get(map_base) {
            existing.clone()
        } else {
            let name = self.ctx.fresh_name("hashmap_len");
            let len = self.ctx.declare_var(&name, ptr_sort());
            self.hashmap_len_symbols.insert(map_base.into(), len.clone());
            len
        }
    }

    /// Create an Option sort for a given value sort: Option_T = None | Some(T)
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_option_sort(&self, value_sort: Sort) -> Sort {
        let sort_name = crate::codegen_ay::names::sort_short_name(&value_sort);
        let option_sort_name = crate::codegen_ay::names::option_sort_name(&sort_name);
        enum_sort(
            &option_sort_name,
            crate::codegen_ay::names::option_constructors(&option_sort_name, value_sort),
        )
    }

    /// Create a None value for the given Option sort.
    ///
    /// REQUIRES: option_sort must be a datatype sort (created by make_option_sort).
    /// If not, logs error and creates a symbolic fallback to avoid panic.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_option_none(&self, option_sort: &Sort) -> Expr {
        if let Some(dt_name) = option_sort.datatype_name() {
            let none_ctor = crate::codegen_ay::names::option_none_constructor_name(dt_name);
            Expr::datatype_constructor(dt_name, none_ctor, vec![], option_sort.clone())
        } else {
            // Part of #1275 audit: Previous code would panic calling datatype_constructor
            // with non-datatype sort. Create fallback Option sort and construct None.
            warn!("make_option_none: expected datatype sort, creating fallback Option");
            let fallback_sort = self.make_option_sort(ptr_sort());
            let dt_name = fallback_sort.datatype_name().unwrap_or("Option_bv64");
            let none_ctor = crate::codegen_ay::names::option_none_constructor_name(dt_name);
            Expr::datatype_constructor(dt_name, none_ctor, vec![], fallback_sort.clone())
        }
    }

    /// Create a Some(value) for the given Option sort.
    ///
    /// REQUIRES: option_sort must be a datatype sort (created by make_option_sort).
    /// If not, logs error and creates a symbolic fallback to avoid panic.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_option_some(
        &self,
        option_sort: &Sort,
        value: Expr,
    ) -> Expr {
        if let Some(dt_name) = option_sort.datatype_name() {
            let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
            Expr::datatype_constructor(dt_name, some_ctor, vec![value], option_sort.clone())
        } else {
            // Part of #1275 audit: Previous code would panic calling datatype_constructor
            // with non-datatype sort. Create fallback Option sort matching value's sort.
            warn!("make_option_some: expected datatype sort, creating fallback Option");
            let fallback_sort = self.make_option_sort(value.sort().clone());
            let dt_name = fallback_sort.datatype_name().unwrap_or("Option_fallback");
            let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
            Expr::datatype_constructor(dt_name, some_ctor, vec![value], fallback_sort.clone())
        }
    }

    /// Check if an Option value is Some.
    ///
    /// Returns true if the Option contains a value, false otherwise.
    /// If sort isn't a datatype, returns symbolic boolean (over-approximation).
    #[must_use]
    pub(in crate::codegen_ay::statement) fn option_is_some(&mut self, option_expr: &Expr) -> Expr {
        let sort = option_expr.sort();
        if let Some(dt_name) = sort.datatype_name() {
            let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
            option_expr.clone().is_constructor(dt_name, some_ctor)
        } else {
            // Part of #1275 audit: Returning false was unsound - would incorrectly
            // indicate no key exists. Return symbolic boolean for over-approximation.
            warn!("option_is_some: expected datatype, returning symbolic bool");
            let name = self.ctx.fresh_name("option_is_some_fallback");
            self.ctx.declare_var(&name, bool_sort())
        }
    }
}
