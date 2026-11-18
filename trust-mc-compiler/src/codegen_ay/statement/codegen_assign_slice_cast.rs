// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Slice-cast assignment helpers.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::context::SharedScalarSlice;
use crate::codegen_ay::types::{POINTER_WIDTH, bv8_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Body, Mutability, Operand, Place, TerminatorKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

/// Private constructor: only the authenticated singleton handler can issue a
/// receipt, after binding the result of the actual call in this borrowed body.
pub(in crate::codegen_ay) struct ExactSharedScalarSliceModel<'a> {
    root: Option<Instance>,
    body: &'a Body,
    block: usize,
    callee: Instance,
}

impl<'a> ExactSharedScalarSliceModel<'a> {
    pub(in crate::codegen_ay) fn into_parts(self) -> (Option<Instance>, &'a Body, usize, Instance) {
        (self.root, self.body, self.block, self.callee)
    }
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// `core::slice::from_ref` borrows the same scalar bytes as a slice of
    /// length one. Inlining through `array::from_ref` instead asks the raw
    /// deref machinery for an array-valued store at the scalar's address.
    /// Only a live, typed shared borrow of an integer supplies both the
    /// existing address and a value that is immutable for the borrow.
    pub(super) fn try_codegen_shared_scalar_slice(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
    ) -> Option<()> {
        if self.ctx.unit_has_stubs() || !destination.projection.is_empty() {
            return None;
        }
        let [Operand::Copy(source) | Operand::Move(source)] = args else {
            return None;
        };
        let locals = self.body.locals();
        let input = source.ty(locals).into_option()?;
        let output = destination.ty(locals).into_option()?;
        let TyKind::RigidTy(RigidTy::Ref(_, scalar, Mutability::Not)) = input.kind() else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, slice, Mutability::Not)) = output.kind() else {
            return None;
        };
        if !matches!(scalar.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
            || !matches!(slice.kind(), TyKind::RigidTy(RigidTy::Slice(element)) if element == scalar)
        {
            return None;
        }
        let callee = self.authenticate_slice_from_ref(func, scalar)?;

        let source_base = self.ssa_base_name(source);
        if self.ref_pointees.is_poisoned(source_base.as_str()) {
            return None;
        }
        let pointee = self.ref_pointees.get(source_base.as_str())?;
        let owner = Self::resolve_stack_storage_owner(&self.ref_pointees, pointee).ok()??;
        let recorded = self.addr_symbols.get(pointee.as_ref())?;
        let (_, view) = self.resolve_alloc(recorded)?;
        let addr = self.env_lookup(&source_base)?;
        if view.root != owner.base
            || self.stack_owner_is_live(&owner) != Some(true)
            || !self.retains_alloc_address(addr, recorded)
        {
            return None;
        }
        let elem_sort = Self::infer_sort_from_ty(scalar)?;
        let value = self.env_lookup(pointee.as_ref())?.clone();
        if value.sort() != &elem_sort {
            return None;
        }

        let snapshot = Expr::const_array(ptr_sort(), value.clone());
        let address = recorded.clone();
        let pointee = pointee.clone();
        let name = self.ctx.fresh_name("shared_scalar_slice_backing");
        let data = self.ctx.declare_var(&name, snapshot.sort().clone());
        // This fresh symbol defines the backing everywhere. The SSA slice
        // assignment separately controls where the reference is available.
        self.ctx.assert(data.clone().eq(snapshot));
        self.ctx.shared_scalar_slices.insert(
            name,
            SharedScalarSlice {
                owner: owner.base,
                pointee,
                address: address.clone(),
                backing: data.clone(),
                scalar: value,
            },
        );
        let result = Self::construct_slice_datatype(elem_sort, address, 1, data);
        let dest_base = self.ssa_base_name(destination);
        self.ref_pointees.forget_rooted_at(&dest_base);
        self.assign_value_to_place(destination, result);
        // A substituted dispatch context earns no receipt, even when the
        // singleton model itself can encode its supplied operands. The ledger
        // separately requires this exact body, block and callee to have survived
        // the compiler's inliner and every complete encoding attempt.
        if let Some(block) = self.body.blocks.get(self.current_bb)
            && let TerminatorKind::Call {
                func: actual_func,
                args: actual_args,
                destination: actual_destination,
                target: Some(_),
                ..
            } = &block.terminator.kind
            && actual_func == func
            && actual_args == args
            && actual_destination == destination
        {
            crate::codegen_ay::unstubbed_accounting::record_exact_shared_scalar_slice(
                ExactSharedScalarSliceModel {
                    root: self.ctx.current_fn().map(|function| function.instance),
                    body: self.body,
                    block: self.current_bb,
                    callee,
                },
            );
        }
        Some(())
    }

    fn authenticate_slice_from_ref(&self, func: &Operand, scalar: Ty) -> Option<Instance> {
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
            func.ty(self.body.locals()).into_option()?.kind()
        else {
            return None;
        };
        let instance = Instance::resolve(def, &generics).into_option()?;
        if matches!(instance.kind, InstanceKind::Virtual { .. })
            || instance.def.def_id() != def.def_id()
        {
            return None;
        }
        let tcx = self.ctx.tcx;
        let id = rustc_internal::internal(tcx, instance.def.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            tcx,
            id,
            &["slice", "raw", "from_ref"],
        ) {
            return None;
        }
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [input] = signature.inputs() else { return None };
        let TyKind::RigidTy(RigidTy::Ref(_, output, Mutability::Not)) = signature.output().kind()
        else {
            return None;
        };
        (matches!(input.kind(), TyKind::RigidTy(RigidTy::Ref(_, actual, Mutability::Not)) if actual == scalar)
            && matches!(output.kind(), TyKind::RigidTy(RigidTy::Slice(actual)) if actual == scalar))
        .then_some(instance)
    }

    /// Construct a precise slice datatype for array-to-slice coercions (#1140).
    ///
    /// When casting `&[T; N]` to `&[T]`, build `Slice_T(fld_ptr, fld_len, fld_data)`.
    /// `fld_data` is included only when a tracked backing array proves the data identity.
    pub(super) fn try_construct_slice_datatype_from_cast(
        &mut self,
        operand: &Operand,
        target_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let src_ty = operand.ty(self.body.locals()).into_option()?;
        let len = Self::array_len_from_pointer_ty(src_ty)?;

        let pointee = match target_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return None,
        };
        let elem_sort = match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => Self::infer_sort_from_ty(elem)?,
            TyKind::RigidTy(RigidTy::Str) => bv8_sort(),
            _ => return None,
        };

        let (operand_place, ref_base) = match operand {
            Operand::Copy(place) | Operand::Move(place) => (place, self.ssa_base_name(place)),
            Operand::Constant(_) => return None,
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => return None,
        };

        let ptr_expr = self.slice_cast_known_pointer_identity(&ref_base);

        let expected_data_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let data = if let Some(pointee_base) = self
            .ref_pointees
            .get(ref_base.as_str())
            .cloned()
            .or_else(|| self.ensure_ref_pointee_for_place(operand_place))
        {
            self.slice_cast_backing_from_pointee_base(
                &ref_base,
                &pointee_base,
                &expected_data_sort,
            )?
        } else if let Some(data) = self.try_ref_pointee_from_env_value(&ref_base, operand_place) {
            if data.sort() == &expected_data_sort {
                data
            } else {
                self.ctx.unsupported_with_fallback(
                    "slice_cast_env_backing_sort_mismatch",
                    format!(
                        "ref_base={ref_base}, expected={expected_data_sort:?}, actual={:?}",
                        data.sort()
                    ),
                );
                return None;
            }
        } else {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_untracked",
                format!("ref_base={ref_base}, target_ty={target_ty:?}"),
            );
            return None;
        };

        Some(Self::construct_slice_datatype(elem_sort, ptr_expr, len as u128, data))
    }

    fn construct_slice_datatype(elem_sort: Sort, addr: Expr, len: u128, data: Expr) -> Expr {
        let slice_sort = Self::slice_sort(elem_sort);
        let sort_name = slice_sort.datatype_name().unwrap_or("Slice");
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&slice_sort, sort_name);
        Expr::datatype_constructor(
            sort_name,
            cons_name,
            vec![addr, Expr::bitvec_const(len, POINTER_WIDTH), data],
            slice_sort.clone(),
        )
    }

    fn slice_cast_backing_from_pointee_base(
        &mut self,
        ref_base: &str,
        pointee_base: &str,
        expected_data_sort: &Sort,
    ) -> Option<Expr> {
        let Some(data) = self.env_lookup(pointee_base).cloned().or_else(|| {
            let pointee_var = format!("{pointee_base}_0");
            let sort_matches = self
                .ctx
                .program
                .get_sort(&pointee_var)
                .is_some_and(|sort| sort == expected_data_sort);
            if sort_matches {
                let data = self.ctx.declare_var(&pointee_var, expected_data_sort.clone());
                self.env_update(std::sync::Arc::<str>::from(pointee_base), data.clone());
                Some(data)
            } else {
                None
            }
        }) else {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_missing",
                format!("ref_base={ref_base}, pointee_base={pointee_base}"),
            );
            return None;
        };
        if data.sort() != expected_data_sort {
            self.ctx.unsupported_with_fallback(
                "slice_cast_backing_sort_mismatch",
                format!(
                    "ref_base={ref_base}, pointee_base={pointee_base}, expected={expected_data_sort:?}, actual={:?}",
                    data.sort()
                ),
            );
            return None;
        }
        Some(data)
    }

    fn slice_cast_known_pointer_identity(&mut self, ref_base: &str) -> Expr {
        if let Some(env_expr) = self.env_lookup(ref_base)
            && env_expr.sort() == &ptr_sort()
        {
            return env_expr.clone();
        }

        if let Some(addr) = self.addr_symbols.get(ref_base) {
            return addr.clone();
        }

        let addr_name = crate::codegen_ay::names::addr_name(ref_base);
        let addr = self.ctx.declare_var(&addr_name, ptr_sort());
        self.ctx.assert(addr.clone().ne(Expr::bitvec_const(0u128, POINTER_WIDTH)));
        self.addr_symbols.insert(std::sync::Arc::from(ref_base), addr.clone());
        addr
    }
}
