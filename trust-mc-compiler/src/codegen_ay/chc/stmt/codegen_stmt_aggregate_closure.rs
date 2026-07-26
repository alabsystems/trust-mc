// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Closure and coroutine aggregate construction for CHC statement encoding.
//! Extracted from codegen_stmt_aggregate.rs per #4057 (500 LOC threshold).

use std::borrow::Cow;
use std::collections::HashSet;

use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use crate::codegen_ay::names::struct_sort;
use crate::rustc_public_bridge::IndexedVal;
use rustc_public::mir::Operand;
use rustc_public::ty::{ClosureDef, CoroutineDef, GenericArgs, RigidTy, TyKind};
use tracing::{debug, warn};

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::codegen_ctx::globals::declare_pending_var;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extract closure upvar types from generic args (last tuple after FnPtr).
    pub(in crate::codegen_ay::chc) fn closure_upvar_tys(
        args: &GenericArgs,
    ) -> Option<Vec<rustc_public::ty::Ty>> {
        args.0
            .iter()
            .enumerate()
            .find_map(|(pos, arg)| {
                if matches!(
                    arg,
                    rustc_public::ty::GenericArgKind::Type(ty)
                        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_)))
                ) {
                    match args.0.get(pos + 1) {
                        Some(rustc_public::ty::GenericArgKind::Type(ty)) => match ty.kind() {
                            TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                            _ => None, // external enum: TyKind
                        },
                        _ => None, // external enum: GenericArgKind
                    }
                } else {
                    None
                }
            })
            // Some closure generic-arg layouts include extra leading params.
            // Fall back to trailing tupled_upvars in those cases.
            .or_else(|| {
                args.0.iter().rev().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Type(ty) => match ty.kind() {
                        TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                        _ => None, // external enum: TyKind
                    },
                    _ => None, // external enum: GenericArgKind
                })
            })
    }

    /// Part of #2083: Closure aggregate — struct with cap_N fields.
    pub(in crate::codegen_ay::chc) fn translate_closure_aggregate(
        &mut self,
        def: ClosureDef,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let closure_id = def.0.to_index();
        let closure_name = crate::codegen_ay::names::closure_sort_name(closure_id);
        let expected_upvars = Self::closure_upvar_tys(args);

        if operands.is_empty() {
            if expected_upvars.as_ref().is_some_and(|u| !u.is_empty()) {
                warn!(closure_name = %closure_name, "closure args expect captures but aggregate has none");
            }
            debug!(closure_name = %closure_name, "non-capturing closure (ZST -> Bool)");
            return Some(Expr::bool_const(true));
        }
        let mut field_exprs = Vec::with_capacity(operands.len());
        let mut fields: Vec<(Cow<'static, str>, Sort)> = Vec::with_capacity(operands.len());
        let use_typed_fields =
            expected_upvars.as_ref().is_some_and(|upvars| upvars.len() == operands.len());
        if use_typed_fields {
            let upvars = expected_upvars?;
            for (i, (op, upvar_ty)) in operands.iter().zip(upvars.iter()).enumerate() {
                let Some(mut val) = self.translate_operand_with_modified(op, modified_locals)
                else {
                    warn!(i, ?op, "translate_closure_aggregate: failed to translate capture");
                    self.record_fallback();
                    return None;
                };
                let mut expected_sort = if let Some(sort) = Self::translate_ty(*upvar_ty) {
                    sort
                } else {
                    warn!(
                        i,
                        ?upvar_ty,
                        "translate_closure_aggregate: failed to translate expected upvar sort; using operand sort"
                    );
                    val.sort().clone()
                };
                if *val.sort() != expected_sort {
                    if let (Some(expected_width), Some(_actual_width)) =
                        (expected_sort.bitvec_width(), val.sort().bitvec_width())
                    {
                        let ext = SignExtension::for_signedness(matches!(
                            upvar_ty.kind(),
                            TyKind::RigidTy(RigidTy::Int(_))
                        ));
                        val = coerce_bitvec_width_safe(val, expected_width, ext);
                    } else {
                        warn!(
                            i,
                            expected = ?expected_sort,
                            actual = ?val.sort(),
                            "translate_closure_aggregate: capture sort mismatch; using operand sort"
                        );
                        expected_sort = val.sort().clone();
                    }
                }
                fields.push((crate::codegen_ay::names::capture_field_name(i), expected_sort));
                field_exprs.push(val);
            }
        } else {
            if let Some(upvars) = expected_upvars.as_ref() {
                warn!(
                    closure_name = %closure_name,
                    expected_captures = upvars.len(),
                    actual_captures = operands.len(),
                    "translate_closure_aggregate: capture arity mismatch, falling back to operand sorts"
                );
            } else {
                debug!(
                    closure_name = %closure_name,
                    actual_captures = operands.len(),
                    "translate_closure_aggregate: could not decode closure upvars from args; using operand sorts"
                );
            }

            for (i, op) in operands.iter().enumerate() {
                let Some(val) = self.translate_operand_with_modified(op, modified_locals) else {
                    warn!(i, ?op, "translate_closure_aggregate: failed to translate capture");
                    self.record_fallback();
                    return None;
                };
                fields.push((crate::codegen_ay::names::capture_field_name(i), val.sort().clone()));
                field_exprs.push(val);
            }
        }

        // Part of #4057: Bridge DT-sorted locals referenced by closure captures into typed memory.
        // When a closure captures `&vec_local`, the capture operand is a BV64 pointer but the
        // Vec DT value only exists in SSA state. Emitting a typed memory store here makes
        // `load_from_memory` inside the closure body's nested call handler succeed.
        self.bridge_closure_capture_dt_stores(operands, &field_exprs, modified_locals);

        let sort = struct_sort(&closure_name, fields);
        self.declare_datatype_sort_if_needed(&sort);
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&sort, &closure_name);
        debug!(
            closure_name = %closure_name,
            num_captures = field_exprs.len(),
            "translate_closure_aggregate: constructed capturing closure"
        );
        Some(Expr::datatype_constructor(closure_name, cons_name, field_exprs, sort))
    }

    /// Part of #4057: For each closure capture operand that is a reference to a DT-sorted local,
    /// emit a typed memory store so that `load_from_memory` succeeds inside the closure body.
    ///
    /// This is a redundant bridge — it makes SSA-only Vec/struct values also available through
    /// the typed memory model. The value is identical; we're creating a second access path.
    fn bridge_closure_capture_dt_stores(
        &mut self,
        operands: &[Operand],
        field_exprs: &[Expr],
        modified_locals: &HashSet<usize>,
    ) {
        for (i, op) in operands.iter().enumerate() {
            let addr = match field_exprs.get(i) {
                Some(expr) if expr.sort().bitvec_width() == Some(POINTER_WIDTH) => expr,
                _ => continue,
            };

            // Get the operand's local index (the reference-holding local).
            let ref_local = match op {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    place.local
                }
                _ => continue,
            };

            // Look up ref_targets to find the referent local.
            let ref_target = match self.ref_resolution.ref_targets.get(&ref_local) {
                Some(t) if t.projections.is_empty() => t,
                _ => continue,
            };
            let referent_local = ref_target.local;

            // Get the referent local's current SSA value.
            let referent_value =
                match self.local_expr_with_modified(referent_local, modified_locals) {
                    Some(v) => v,
                    None => continue,
                };

            // Only bridge DT-sorted values (Vec, struct). Scalar BV locals don't need this.
            if !referent_value.sort().is_datatype() {
                continue;
            }

            // Get the referent's type for the memory store.
            let referent_ty = match self.body.locals().get(referent_local) {
                Some(decl) => decl.ty,
                None => continue,
            };

            debug!(
                capture_idx = i,
                ref_local,
                referent_local,
                referent_sort = ?referent_value.sort(),
                "bridge_closure_capture_dt_stores: emitting typed memory store (#4057)"
            );
            self.build_memory_store(addr.clone(), referent_value, referent_ty);
        }
    }

    /// Part of #1351: Coroutine aggregate — root state machine with direct-fields view.
    pub(in crate::codegen_ay::chc) fn translate_coroutine_aggregate(
        &mut self,
        def: CoroutineDef,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let coro_name = crate::codegen_ay::names::coroutine_sort_name(def.0.to_index());
        let coroutine_ty =
            rustc_public::ty::Ty::from_rigid_kind(RigidTy::Coroutine(def, args.clone()));
        let info = build_coroutine_sort_info(self.tcx, coroutine_ty, |field_ty| {
            Self::translate_ty(field_ty).unwrap_or_else(ptr_sort)
        })?;

        // By-name operand mapping: view fields are offset-ordered while MIR
        // aggregate operands are indexed by MIR field index — pair them via
        // the index encoded in each field's name, never positionally.
        let Some(operand_map) = info.direct_fields.operand_map(operands.len()) else {
            warn!(coro_name = %coro_name, fields = info.direct_fields.fields.len(), actual = operands.len(), "translate_coroutine_aggregate: operand/field name mapping failed");
            self.record_fallback();
            return None;
        };
        let mut direct_field_exprs = Vec::with_capacity(info.direct_fields.fields.len());
        for (field, mapped_idx) in info.direct_fields.fields.iter().zip(&operand_map) {
            let expr = match mapped_idx {
                None => match field.sort.bitvec_width() {
                    Some(width) => Expr::bitvec_const(0, width),
                    None => Expr::bool_const(false),
                },
                Some(mir_idx) => {
                    let Some(op) = operands.get(*mir_idx) else {
                        warn!(coro_name = %coro_name, mir_idx, "translate_coroutine_aggregate: missing direct field operand");
                        self.record_fallback();
                        return None;
                    };
                    let Some(val) = self.translate_operand_with_modified(op, modified_locals)
                    else {
                        warn!(
                            ?op,
                            "translate_coroutine_aggregate: direct field translation failed"
                        );
                        self.record_fallback();
                        return None;
                    };
                    val
                }
            };
            direct_field_exprs.push(expr);
        }

        self.declare_datatype_sort_if_needed(&info.root_sort);
        let direct_sort_name = info.direct_fields.sort.datatype_name()?;
        let direct_cons = crate::codegen_ay::names::resolve_ctor_name(
            &info.direct_fields.sort,
            &direct_sort_name,
        );
        let direct_expr = Expr::datatype_constructor(
            direct_sort_name,
            direct_cons,
            direct_field_exprs,
            info.direct_fields.sort.clone(),
        );

        let mut root_field_exprs = Vec::with_capacity(1 + info.variants.len());
        root_field_exprs.push(direct_expr);
        for variant in &info.variants {
            let fresh_name = chc_fresh_name("__coroutine_variant_view");
            root_field_exprs.push(declare_pending_var(fresh_name, variant.sort.clone()));
        }

        let cons = crate::codegen_ay::names::resolve_ctor_name(&info.root_sort, &coro_name);
        debug!(
            coro_name = %coro_name,
            direct_fields = info.direct_fields.fields.len(),
            variants = info.variants.len(),
            "coroutine aggregate constructed"
        );
        Some(Expr::datatype_constructor(coro_name, cons, root_field_exprs, info.root_sort))
    }
}
