// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec construction and mutation operations for AY BMC codegen.
//!
//! Extracted from `vec.rs` per 500-line limit. Handles:
//! - VecFromElem: `vec![elem; n]` construction
//! - VecResize: `Vec::resize(&mut self, new_len, value)`
//! - VecExtendFromSlice: `Vec::extend_from_slice(&mut self, &[T])`
//! - SliceIntoVec: `<[T]>::into_vec` / `vec![...]` expansion
//!
//! Part of #3494: BMC parity for CHC-only StubKind variants.
//! Part of #3477: BMC encoding parity gap closure.

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, flatten_dt_array_element, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::super::{IntoOption, StatementCodegen};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `vec![elem; n]` — construct Vec with const_array data.
    ///
    /// args[0] = elem value, args[1] = count (usize).
    /// CHC equivalent: codegen_call_vec_ops.rs `vec_op_from_elem`.
    pub(in crate::codegen_ay::statement) fn codegen_vec_from_elem(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let elem_sort = self.infer_vec_elem_sort(destination).unwrap_or_else(ptr_sort);
        let elem_sort = flatten_dt_array_element(elem_sort);
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let vec_sort_name = names::vec_sort_name(&names::sort_short_name(&elem_sort));
        let vec_sort = struct_sort(vec_sort_name.clone(), names::vec_fields(array_sort));

        let count = args
            .get(1)
            .and_then(|a| self.codegen_operand(a))
            .map(|c| self.coerce_to_ptr_width(c))
            .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));

        let ptr_name = self.ctx.fresh_name("vec_fe_ptr");
        let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());

        // Build data array: const_array where every index maps to elem value.
        let data = if let Some(elem) = args.first().and_then(|a| self.codegen_operand(a)) {
            Expr::const_array(ptr_sort(), elem)
        } else {
            let default_name = self.ctx.fresh_name("vec_fe_default");
            let default_elem = self.ctx.declare_var(&default_name, elem_sort);
            Expr::const_array(ptr_sort(), default_elem)
        };

        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&vec_sort, &vec_sort_name);
        let vec = Expr::datatype_constructor(
            vec_sort_name,
            ctor_name,
            vec![ptr, count.clone(), count, data],
            vec_sort,
        );
        self.assign_value_to_place(destination, vec);
        target
    }

    /// Codegen `Vec::resize(&mut self, new_len, value)`.
    ///
    /// Model: len' = new_len, cap' = max(cap, new_len), data/ptr preserved.
    /// CHC equivalent: codegen_call_vec_ops.rs `vec_op_resize`.
    pub(in crate::codegen_ay::statement) fn codegen_vec_resize(
        &mut self,
        args: &[Operand],
        _destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("Vec::resize requires 2+ args (self, new_len) — fail-closed (#3494)");
            return None;
        }

        let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
            return target;
        };

        let new_len_raw = self.codegen_operand(&args[1]);
        if let Some(new_len_raw) = new_len_raw
            && let Some(fields) = Self::extract_all_vec_fields(&vec)
        {
            let new_len = self.coerce_to_ptr_width(new_len_raw);
            let grow_needed = fields.cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), fields.cap);

            let new_vec = Expr::datatype_constructor(
                fields.dt_name,
                fields.ctor_name,
                vec![fields.ptr, new_len, new_cap, fields.data],
                fields.sort,
            );
            self.env_update(base, new_vec);
        }
        target
    }

    /// Codegen `Vec::extend_from_slice(&mut self, &[T])`.
    ///
    /// Model: len' = old_len + source_len, cap' = max(cap, new_len).
    /// Data contents left unconstrained (sound over-approximation).
    /// CHC equivalent: codegen_call_vec_ops_len.rs `vec_op_extend_from_slice`.
    pub(in crate::codegen_ay::statement) fn codegen_vec_extend_from_slice(
        &mut self,
        args: &[Operand],
        _destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("Vec::extend_from_slice requires 2 args — fail-closed (#3494)");
            return None;
        }

        let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
            return target;
        };

        if let Some(fields) = Self::extract_all_vec_fields(&vec) {
            // Try to resolve source slice length from args[1]
            let source_len = self.slice_len_expr(&args[1]).unwrap_or_else(|| {
                let name = self.ctx.fresh_name("ext_src_len");
                self.ctx.declare_var(&name, ptr_sort())
            });

            let new_len = fields.len.clone().bvadd(source_len);
            // Part of #3409: guard against unsigned overflow on len+source_len.
            // Rust's Vec::extend panics on capacity overflow (checked_add).
            self.ctx.assert(new_len.clone().bvuge(fields.len.clone()));
            let grow_needed = fields.cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), fields.cap);

            let new_vec = Expr::datatype_constructor(
                fields.dt_name,
                fields.ctor_name,
                vec![fields.ptr, new_len, new_cap, fields.data],
                fields.sort,
            );
            self.env_update(base, new_vec);
        }
        target
    }

    /// Codegen `<[T]>::into_vec` / `vec![...]` expansion.
    ///
    /// Sound over-approximation: construct Vec with correct length from source
    /// slice but symbolic data array. This loses element-level tracking but is
    /// sound — the solver considers all possible element values.
    /// CHC equivalent: codegen_call_vec_into.rs (394 lines — full element tracking).
    pub(in crate::codegen_ay::statement) fn codegen_slice_into_vec(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let elem_sort = self.infer_vec_elem_sort(destination).unwrap_or_else(ptr_sort);
        let elem_sort = flatten_dt_array_element(elem_sort);
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let vec_sort_name = names::vec_sort_name(&names::sort_short_name(&elem_sort));
        let vec_sort = struct_sort(vec_sort_name.clone(), names::vec_fields(array_sort));

        let ptr_name = self.ctx.fresh_name("vec_iv_ptr");
        let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());

        // Resolve the source length. `vec![a, b, ...]` lowers to an `into_vec`
        // over a `Box<[T; N]>` (unsized to `Box<[T]>`), so the literal length N
        // is exactly the Vec length — recovering it as a CONCRETE bitvector (not
        // a fresh symbol) is both sound and required for downstream bounded
        // iterator unrolling (`codegen_iter_all_any`). Falls back to the slice
        // length expression, then to a fresh symbol.
        let concrete_len = self.into_vec_concrete_len(args);
        let arg_ty_dbg = args
            .first()
            .and_then(|a| a.ty(self.body.locals()).into_option())
            .map(|t| format!("{:?}", t.kind()));
        debug!(
            ?concrete_len,
            arg_ty = ?arg_ty_dbg,
            slice_len_some = args.first().and_then(|_| self.slice_len_expr(&args[0])).is_some(),
            "codegen_slice_into_vec: length resolution"
        );
        let len = concrete_len
            .map(|n| Expr::bitvec_const(u128::from(n), POINTER_WIDTH))
            .or_else(|| args.first().and_then(|_| self.slice_len_expr(&args[0])))
            .unwrap_or_else(|| {
                let name = self.ctx.fresh_name("vec_iv_len");
                self.ctx.declare_var(&name, ptr_sort())
            });

        // Symbolic data array: sound over-approximation
        let default_name = self.ctx.fresh_name("vec_iv_default");
        let default_elem = self.ctx.declare_var(&default_name, elem_sort);
        let data = Expr::const_array(ptr_sort(), default_elem);

        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&vec_sort, &vec_sort_name);
        let vec = Expr::datatype_constructor(
            vec_sort_name,
            ctor_name,
            vec![ptr, len.clone(), len, data],
            vec_sort,
        );
        self.assign_value_to_place(destination, vec);
        target
    }

    /// Recover the CONCRETE element count of a `vec![...]` / `<[T]>::into_vec`
    /// expansion from the source `Box<[T; N]>` array length.
    ///
    /// `vec![a, b]` lowers to `into_vec(Box::new([a, b]) as Box<[T]>)`; the
    /// pre-unsizing operand carries the array length `N`. We look at the
    /// argument type directly, then trace one `Cast(Unsize)` backward to the
    /// pre-unsize local (the array length is erased by the unsize cast). Returns
    /// `None` when the length is not statically known (the caller then falls back
    /// to the prior symbolic length — sound, just less precise).
    fn into_vec_concrete_len(&self, args: &[Operand]) -> Option<u64> {
        let arg = args.first()?;
        if let Some(ty) = arg.ty(self.body.locals()).into_option()
            && let Some(n) = Self::array_len_from_any_ty(ty)
        {
            return Some(n);
        }
        // Trace `arg.local = Cast(Unsize, src, _)` back to the `Box<[T; N]>` src.
        let arg_local = match arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == arg_local
                    && lhs.projection.is_empty()
                    && let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) = rhs
                    && src.projection.is_empty()
                    && let Some(n) = Self::array_len_from_any_ty(self.body.locals()[src.local].ty)
                {
                    return Some(n);
                }
            }
        }
        None
    }

    /// Static `[T; N]` length reachable through `Box<[T; N]>`, `&[T; N]`,
    /// `*const [T; N]`, or a bare `[T; N]` type. `None` for slices / unknown.
    fn array_len_from_any_ty(ty: Ty) -> Option<u64> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().into_option(),
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Self::array_len_from_any_ty(inner),
            TyKind::RigidTy(RigidTy::Adt(def, adt_args)) if def.0.name().contains("boxed::Box") => {
                adt_args.0.iter().find_map(|a| match a {
                    rustc_public::ty::GenericArgKind::Type(t) => Self::array_len_from_any_ty(*t),
                    _ => None,
                })
            }
            _ => None,
        }
    }
}
