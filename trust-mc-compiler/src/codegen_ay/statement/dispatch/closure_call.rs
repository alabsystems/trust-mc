// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure call codegen (FnOnce::call_once, Fn::call, FnMut::call_mut).
//!
//! Normalizes the RustCall ABI (`receiver`, tupled arguments) into the callee MIR
//! signature so the BMC mini-inliner can execute small closure bodies directly.

use ay_bindings::{Expr, SortInner};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Operand, Place, ProjectionElem};
use rustc_public::ty::{ClosureKind, RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::names;
use crate::codegen_ay::statement::StatementCodegen;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen closure call (FnOnce::call_once, Fn::call, FnMut::call_mut).
    ///
    /// Closures in Rust are implemented as structs containing captured environment.
    /// When called via FnOnce::call_once, the closure struct is consumed.
    /// We resolve the closure instance and attempt to inline simple patterns.
    ///
    /// #478: Required for array iteration which uses closures in Option::map.
    pub(in crate::codegen_ay::statement) fn codegen_closure_call(
        &mut self,
        _func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_closure_call: no arguments");
            self.codegen_symbolic_result(destination);
            return target;
        }

        let closure_arg = &args[0];
        let Some(closure_ty) = closure_arg.ty(self.body.locals()).into_option() else {
            warn!("codegen_closure_call: could not recover closure type");
            self.codegen_symbolic_result(destination);
            return target;
        };
        debug!("codegen_closure_call: closure_ty={:?}", closure_ty);

        let Some(instance) = self.resolve_closure_instance(closure_ty) else {
            debug!("codegen_closure_call: not a resolvable closure type");
            self.codegen_symbolic_result(destination);
            return target;
        };

        let Some(params) = self.translate_closure_inline_params(instance, args) else {
            debug!(
                callee = instance.name(),
                "codegen_closure_call: could not normalize RustCall tuple arguments"
            );
            self.codegen_symbolic_result(destination);
            return target;
        };

        if let Some(next_bb) =
            self.try_inline_small_instance_call(instance, &params, destination, target)
        {
            debug!(callee = instance.name(), "codegen_closure_call: inlined closure body");
            return Some(next_bb);
        }

        debug!(callee = instance.name(), "codegen_closure_call: mini-inline declined closure body");
        self.codegen_symbolic_result(destination);
        target
    }

    pub(in crate::codegen_ay::statement) fn resolve_closure_instance(
        &self,
        closure_ty: Ty,
    ) -> Option<Instance> {
        let (def, generic_args, kinds) = match closure_ty.kind() {
            TyKind::RigidTy(RigidTy::Closure(def, generic_args)) => {
                (def, generic_args, [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce])
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..))) =>
            {
                let TyKind::RigidTy(RigidTy::Closure(def, generic_args)) = inner.kind() else {
                    unreachable!("guard ensures inner closure type");
                };
                (def, generic_args, [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce])
            }
            _ => return None,
        };

        for kind in kinds {
            if let Ok(instance) = Instance::resolve_closure(def, &generic_args, kind)
                && instance.body().is_some()
            {
                return Some(instance);
            }
        }
        None
    }

    fn translate_closure_inline_params(
        &mut self,
        instance: Instance,
        args: &[Operand],
    ) -> Option<Vec<super::inline_body::InlineArgValue>> {
        let body = self.ctx.body_or_instance_body(instance)?;
        let arg_locals = body.arg_locals();
        let (receiver_local, callee_params) = arg_locals.split_first()?;

        let mut params = Vec::with_capacity(arg_locals.len());
        params.push(self.translate_inline_arg_value(&args[0], receiver_local.ty)?);

        if callee_params.is_empty() {
            return Some(params);
        }

        let tuple_arg = args.get(1)?;
        params.extend(self.translate_rust_call_tuple_args(tuple_arg, callee_params)?);
        Some(params)
    }

    fn translate_rust_call_tuple_args(
        &mut self,
        tuple_arg: &Operand,
        callee_params: &[rustc_public::mir::LocalDecl],
    ) -> Option<Vec<super::inline_body::InlineArgValue>> {
        let tuple_ty = tuple_arg.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Tuple(tuple_fields)) = tuple_ty.kind() else {
            return None;
        };
        if callee_params.len() == 1
            && let TyKind::RigidTy(RigidTy::Tuple(expected_fields)) = callee_params[0].ty.kind()
            && expected_fields.len() == tuple_fields.len()
        {
            return Some(vec![super::inline_body::InlineArgValue {
                expr: self.build_concrete_tuple_expr(tuple_arg, tuple_fields.as_slice())?,
                pointee_base: None,
                flattened_entries: Vec::new(),
                nested_ref_pointees: Vec::new(),
            }]);
        }
        if tuple_fields.len() != callee_params.len() {
            return None;
        }

        match tuple_arg {
            Operand::Copy(place) | Operand::Move(place) => callee_params
                .iter()
                .enumerate()
                .map(|(index, local_decl)| {
                    let mut projection = place.projection.clone();
                    projection.push(ProjectionElem::Field(index, tuple_fields[index]));
                    let field_place = Place { local: place.local, projection };
                    let field_operand = Operand::Copy(field_place);
                    self.translate_inline_arg_value(&field_operand, local_decl.ty)
                })
                .collect(),
            Operand::Constant(_) => {
                let tuple_expr = self.codegen_operand(tuple_arg)?;
                let SortInner::Datatype(dt) = tuple_expr.sort().inner() else {
                    return None;
                };
                let constructor = dt.constructors.first()?;
                if constructor.fields.len() != callee_params.len() {
                    return None;
                }
                callee_params
                    .iter()
                    .enumerate()
                    .map(|(index, local_decl)| {
                        if matches!(
                            local_decl.ty.kind(),
                            TyKind::RigidTy(RigidTy::Ref(..))
                                | TyKind::RigidTy(RigidTy::RawPtr(..))
                        ) {
                            return None;
                        }
                        let field = constructor.fields.get(index)?;
                        Some(super::inline_body::InlineArgValue {
                            expr: tuple_expr.clone().field_select(
                                &dt.name,
                                &field.name,
                                field.sort.clone(),
                            ),
                            pointee_base: None,
                            flattened_entries: Vec::new(),
                            nested_ref_pointees: Vec::new(),
                        })
                    })
                    .collect()
            }
        }
    }

    fn build_concrete_tuple_expr(
        &mut self,
        tuple_arg: &Operand,
        tuple_fields: &[Ty],
    ) -> Option<Expr> {
        let field_values = self.translate_tuple_field_values(tuple_arg, tuple_fields)?;
        if field_values.is_empty() {
            let unit_sort = names::struct_sort("Unit", Vec::<(&str, ay_bindings::Sort)>::new());
            return Some(Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort));
        }
        let fields: Vec<_> = field_values
            .iter()
            .enumerate()
            .map(|(index, expr)| (names::tuple_field_name(index), expr.sort().clone()))
            .collect();
        let sort_name = Self::tuple_sort_name(&fields);
        let tuple_sort = names::struct_sort(&sort_name, fields);
        let cons_name = names::resolve_ctor_name(&tuple_sort, &sort_name);
        Some(Expr::datatype_constructor(sort_name, cons_name, field_values, tuple_sort))
    }

    fn translate_tuple_field_values(
        &mut self,
        tuple_arg: &Operand,
        tuple_fields: &[Ty],
    ) -> Option<Vec<Expr>> {
        match tuple_arg {
            Operand::Copy(place) | Operand::Move(place) => tuple_fields
                .iter()
                .enumerate()
                .map(|(index, field_ty)| {
                    let mut projection = place.projection.clone();
                    projection.push(ProjectionElem::Field(index, *field_ty));
                    let field_place = Place { local: place.local, projection };
                    self.codegen_operand(&Operand::Copy(field_place))
                })
                .collect(),
            Operand::Constant(_) => {
                let tuple_expr = self.codegen_operand(tuple_arg)?;
                let SortInner::Datatype(dt) = tuple_expr.sort().inner() else {
                    return None;
                };
                let constructor = dt.constructors.first()?;
                if constructor.fields.len() != tuple_fields.len() {
                    return None;
                }
                constructor
                    .fields
                    .iter()
                    .map(|field| {
                        Some(tuple_expr.clone().field_select(
                            &dt.name,
                            &field.name,
                            field.sort.clone(),
                        ))
                    })
                    .collect()
            }
        }
    }
}
