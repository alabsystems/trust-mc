// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer/memory-heavy stub dispatch helpers.
//!
//! Extracted from `stub_dispatch.rs` per #2246 to keep the main dispatch
//! table focused on routing.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, flatten_dt_array_element, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

use super::super::IntoOption;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn try_codegen_pointer_memory_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        if matches!(stub_kind, StubKind::NonNullDangling) {
            return Some(self.codegen_nonnull_dangling_stub(destination, target));
        }
        if matches!(stub_kind, StubKind::NonNullAsMutPtr) {
            return Some(self.codegen_nonnull_as_mut_ptr_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::BoxIntoRawWithAllocator) {
            return Some(self.codegen_box_into_raw_with_allocator_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::UniqueNewUnchecked) {
            return Some(self.codegen_unique_new_unchecked_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::VecFromRawPartsIn) {
            return Some(self.codegen_vec_from_raw_parts_in_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::RawVecNewIn) {
            return Some(self.codegen_rawvec_new_in_stub(destination, target));
        }
        if matches!(stub_kind, StubKind::RawVecCapacity) {
            return Some(self.codegen_rawvec_capacity_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::RawVecGrowOne) {
            return Some(self.codegen_rawvec_grow_one_stub(args, target));
        }
        if matches!(stub_kind, StubKind::RawVecPtr) {
            return Some(self.codegen_rawvec_ptr_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::RawVecFromNonNullIn) {
            return Some(self.codegen_rawvec_from_nonnull_in_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::RawVecDrop | StubKind::RawVecShrinkToFit) {
            return Some(self.codegen_rawvec_drop_stub(target));
        }
        if matches!(stub_kind, StubKind::CheckedAddUnsigned) {
            return Some(self.codegen_checked_add_unsigned_stub(args, destination, target));
        }
        if matches!(stub_kind, StubKind::SliceAsPtr | StubKind::SliceAsMutPtr) {
            return Some(self.codegen_slice_as_ptr_stub(args, destination, target));
        }
        None
    }

    fn codegen_nonnull_dangling_stub(
        &mut self,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let align = destination
            .ty(self.body.locals())
            .into_option()
            .and_then(|dest_ty| {
                if let TyKind::RigidTy(RigidTy::Adt(def, args)) = dest_ty.kind()
                    && def.0.name().contains("NonNull")
                    && let Some(GenericArgKind::Type(pointee_ty)) = args.0.first()
                {
                    return LayoutOf::new(*pointee_ty).align_of();
                }
                None
            })
            .unwrap_or(8);
        debug!("codegen_stubbed_call: NonNull::dangling with alignment={}", align);
        let dangling_ptr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
        if self.ctx.config.extra_pointer_checks {
            self.ctx.heap_invalidate_no_provenance(dangling_ptr.clone());
        }
        self.assign_value_to_place(destination, dangling_ptr);
        target
    }

    fn codegen_nonnull_as_mut_ptr_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: NonNull::as_mut_ptr - extracting data pointer");
        let arg_expr = args.first().and_then(|a| self.codegen_operand(a))?;
        let ptr = self.coerce_to_ptr_width(arg_expr);
        self.assign_value_to_place(destination, ptr);
        target
    }

    /// <[T]>::as_ptr / as_mut_ptr — pointer identity (Part of #3104).
    ///
    /// For stack arrays, the self argument is a pointer (bitvec) to the array
    /// base address. For Slice datatypes, extracts `fld_ptr`. Either way,
    /// returns a pointer to the first element.
    fn codegen_slice_as_ptr_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: slice::as_ptr/as_mut_ptr - extracting data pointer");
        let arg_expr = args.first().and_then(|a| self.codegen_operand(a))?;

        // If the argument is already a bitvec (pointer), return it directly.
        // If it's a Slice datatype, extract fld_ptr.
        let ptr = if arg_expr.sort().is_bitvec() {
            self.coerce_to_ptr_width(arg_expr)
        } else if arg_expr.sort().datatype_name().is_some_and(|n| n.contains("Slice")) {
            // Clone the Sort (cheap Arc increment) to borrow the datatype name without
            // conflicting with the consumption of arg_expr by field_select. Avoids a
            // String allocation from .to_string(). Part of #2267.
            let sort = arg_expr.sort().clone();
            let sort_name = sort.datatype_name().expect("invariant: is_some_and guard");
            arg_expr.field_select(sort_name, "fld_ptr", ptr_sort())
        } else {
            // Unknown representation — return self coerced to pointer width.
            // This handles cases where the array ref is passed as an opaque value.
            warn!(
                "slice::as_ptr: unexpected arg sort {:?}, treating as pointer identity",
                arg_expr.sort()
            );
            self.coerce_to_ptr_width(arg_expr)
        };
        self.assign_value_to_place(destination, ptr);
        target
    }

    fn codegen_box_into_raw_with_allocator_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: Box::into_raw_with_allocator - decomposing Box");
        let box_expr = args.first().and_then(|a| self.codegen_operand(a))?;
        let ptr = self.coerce_to_ptr_width(box_expr);
        self.assign_value_to_place(destination, ptr);
        target
    }

    /// Unique::<T>::new_unchecked(ptr) → Unique<T> — pointer identity.
    /// Part of #1739: Box::from_raw desugars to this in MIR.
    fn codegen_unique_new_unchecked_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: Unique::new_unchecked - pointer identity passthrough");
        let ptr_expr = args.first().and_then(|a| self.codegen_operand(a))?;
        let ptr = self.coerce_to_ptr_width(ptr_expr);
        self.assign_value_to_place(destination, ptr);
        target
    }

    fn codegen_vec_from_raw_parts_in_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: Vec::from_raw_parts_in - constructing Vec struct with data");

        let ptr = args
            .first()
            .and_then(|a| self.codegen_operand(a))
            .map_or_else(|| Expr::bitvec_const(0, POINTER_WIDTH), |e| self.coerce_to_ptr_width(e));
        let len = args
            .get(1)
            .and_then(|a| self.codegen_operand(a))
            .map_or_else(|| Expr::bitvec_const(0, POINTER_WIDTH), |e| self.coerce_to_ptr_width(e));
        let cap = args
            .get(2)
            .and_then(|a| self.codegen_operand(a))
            .map_or_else(|| Expr::bitvec_const(0, POINTER_WIDTH), |e| self.coerce_to_ptr_width(e));

        let elem_sort = self.infer_vec_elem_sort(destination).unwrap_or_else(ptr_sort);
        // Part of #2990: flatten DT elements to BV for PDR compatibility.
        let elem_sort = flatten_dt_array_element(elem_sort);
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let vec_sort_name = crate::codegen_ay::names::vec_sort_name(
            &crate::codegen_ay::names::sort_short_name(&elem_sort),
        );

        let data_name = self.ctx.fresh_name("vec_data");
        let data = self.ctx.declare_var(&data_name, array_sort.clone());

        let vec_sort = struct_sort(vec_sort_name.clone(), names::vec_fields(array_sort));
        let ctor_name = crate::codegen_ay::names::cons_name(&vec_sort_name);
        let vec_expr = Expr::datatype_constructor(
            vec_sort_name,
            ctor_name,
            vec![ptr, len, cap, data],
            vec_sort,
        );

        self.assign_value_to_place(destination, vec_expr);
        target
    }

    fn codegen_rawvec_new_in_stub(
        &mut self,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::new_in - creating empty buffer");
        let rawvec_sort = struct_sort("RawVec", names::rawvec_fields());
        let ptr_name = self.ctx.fresh_name("rawvec_ptr");
        let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        self.ctx.assert(ptr.clone().bvugt(zero.clone()));
        if self.ctx.config.extra_pointer_checks {
            self.ctx.heap_invalidate_no_provenance(ptr.clone());
        }
        let rawvec =
            Expr::datatype_constructor("RawVec", "RawVec_mk", vec![ptr, zero], rawvec_sort);
        self.assign_value_to_place(destination, rawvec);
        target
    }

    fn codegen_rawvec_capacity_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::capacity - extracting cap field");
        if let Some(rawvec_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
            let is_rawvec_datatype = rawvec_expr.sort().datatype_name() == Some("RawVec");
            if is_rawvec_datatype {
                let cap = rawvec_expr.field_select("RawVec", "fld_cap", ptr_sort());
                self.assign_value_to_place(destination, cap);
            } else {
                warn!(
                    "RawVec::capacity: arg is {:?}, not RawVec datatype - using symbolic capacity",
                    rawvec_expr.sort()
                );
                let name = self.ctx.fresh_name("rawvec_cap_fallback");
                let cap = self.ctx.declare_var(&name, ptr_sort());
                self.assign_value_to_place(destination, cap);
            }
        } else {
            let name = self.ctx.fresh_name("rawvec_cap");
            let cap = self.ctx.declare_var(&name, ptr_sort());
            self.assign_value_to_place(destination, cap);
        }
        target
    }

    fn codegen_rawvec_grow_one_stub(
        &mut self,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::grow_one - increasing capacity");
        if args.is_empty() {
            warn!("RawVec::grow_one requires 1 arg (self) — fail-closed (#2617)");
            return None;
        }
        let rawvec_base = self.get_map_base_from_ref(&args[0]);
        let rawvec_expr = rawvec_base.as_ref().and_then(|base| self.env_lookup(base).cloned());

        if let (Some(base), Some(rawvec)) = (rawvec_base, rawvec_expr) {
            let is_rawvec_datatype = rawvec.sort().datatype_name() == Some("RawVec");
            if is_rawvec_datatype {
                let rawvec_sort = rawvec.sort().clone();
                let ptr = rawvec.clone().field_select("RawVec", "fld_ptr", ptr_sort());
                let old_cap = rawvec.field_select("RawVec", "fld_cap", ptr_sort());
                let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                let cap_name = self.ctx.fresh_name("rawvec_new_cap");
                let new_cap = self.ctx.declare_var(&cap_name, ptr_sort());
                self.ctx.assert(new_cap.clone().bvugt(old_cap.clone()));
                self.ctx.assert(new_cap.clone().bvuge(old_cap.bvadd(one)));
                let new_rawvec = Expr::datatype_constructor(
                    "RawVec",
                    "RawVec_mk",
                    vec![ptr, new_cap],
                    rawvec_sort,
                );
                self.env_update(base, new_rawvec);
            } else {
                warn!(
                    "RawVec::grow_one: expr is {:?}, not RawVec datatype - ignoring grow",
                    rawvec.sort()
                );
            }
        }
        target
    }

    fn codegen_rawvec_ptr_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::ptr - extracting ptr field");
        if let Some(rawvec_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
            let is_rawvec_datatype = rawvec_expr.sort().datatype_name() == Some("RawVec");
            if is_rawvec_datatype {
                let ptr = rawvec_expr.field_select("RawVec", "fld_ptr", ptr_sort());
                self.assign_value_to_place(destination, ptr);
            } else {
                warn!(
                    "RawVec::ptr: arg is {:?}, not RawVec datatype - using symbolic pointer",
                    rawvec_expr.sort()
                );
                let name = self.ctx.fresh_name("rawvec_ptr_fallback");
                let ptr = self.ctx.declare_var(&name, ptr_sort());
                self.assign_value_to_place(destination, ptr);
            }
        } else {
            let name = self.ctx.fresh_name("rawvec_ptr");
            let ptr = self.ctx.declare_var(&name, ptr_sort());
            self.assign_value_to_place(destination, ptr);
        }
        target
    }

    fn codegen_rawvec_from_nonnull_in_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::from_nonnull_in - constructing from NonNull");

        let ptr = args.first().and_then(|a| self.codegen_operand(a)).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("rawvec_ptr");
            self.ctx.declare_var(&name, ptr_sort())
        });

        let cap = args.get(1).and_then(|a| self.codegen_operand(a)).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("rawvec_cap");
            self.ctx.declare_var(&name, ptr_sort())
        });

        let ptr = if ptr.sort().is_bitvec() && ptr.sort().bitvec_width() != Some(POINTER_WIDTH) {
            Self::coerce_to_width(ptr, POINTER_WIDTH)
        } else if !ptr.sort().is_bitvec() {
            let name = self.ctx.fresh_name("rawvec_ptr_fallback");
            self.ctx.declare_var(&name, ptr_sort())
        } else {
            ptr
        };
        let cap = if cap.sort().is_bitvec() && cap.sort().bitvec_width() != Some(POINTER_WIDTH) {
            Self::coerce_to_width(cap, POINTER_WIDTH)
        } else if !cap.sort().is_bitvec() {
            let name = self.ctx.fresh_name("rawvec_cap_fallback");
            self.ctx.declare_var(&name, ptr_sort())
        } else {
            cap
        };

        let rawvec_sort = struct_sort("RawVec", names::rawvec_fields());
        let rawvec = Expr::datatype_constructor("RawVec", "RawVec_mk", vec![ptr, cap], rawvec_sort);
        self.assign_value_to_place(destination, rawvec);
        target
    }

    fn codegen_rawvec_drop_stub(&mut self, target: Option<BasicBlockIdx>) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: RawVec::drop - no-op (deallocation not modeled)");
        target
    }

    fn codegen_checked_add_unsigned_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        debug!("codegen_stubbed_call: checked_add_unsigned");

        if args.len() < 2 {
            warn!("checked_add_unsigned requires 2 args (self, rhs) — fail-closed (#2497)");
            return None;
        }

        let lhs = self.codegen_operand(&args[0]);
        let rhs = self.codegen_operand(&args[1]);

        if let (Some(lhs_expr), Some(rhs_expr)) = (lhs, rhs) {
            let lhs_sort = lhs_expr.sort();
            let Some(width) = lhs_sort.bitvec_width() else {
                warn!(
                    lhs_sort = ?lhs_sort,
                    "checked_add_unsigned expects bitvec lhs; falling back to symbolic result"
                );
                self.codegen_symbolic_result(destination);
                return target;
            };
            let rhs_sort = rhs_expr.sort();
            let Some(rhs_width) = rhs_sort.bitvec_width() else {
                warn!(
                    rhs_sort = ?rhs_sort,
                    "checked_add_unsigned expects bitvec rhs; falling back to symbolic result"
                );
                self.codegen_symbolic_result(destination);
                return target;
            };
            if rhs_width != width {
                warn!(
                    lhs_width = width,
                    rhs_width,
                    "checked_add_unsigned expects equal-width operands; falling back to symbolic result"
                );
                self.codegen_symbolic_result(destination);
                return target;
            }
            let wide_width = width * 2;
            debug!(width, wide_width, "checked_add_unsigned: operand width");

            let lhs_wide = lhs_expr.sign_extend(width);
            let rhs_wide = rhs_expr.zero_extend(width);
            let sum_wide = lhs_wide.bvadd(rhs_wide);

            let signed_min = if width <= 63 {
                Expr::bitvec_const(-(1i64 << (width - 1)), wide_width)
            } else {
                let min_val = -(num_bigint::BigInt::from(1) << (width - 1));
                Expr::bitvec_const(min_val, wide_width)
            };
            let signed_max = if width <= 63 {
                Expr::bitvec_const((1i64 << (width - 1)) - 1, wide_width)
            } else {
                let max_val = (num_bigint::BigInt::from(1) << (width - 1)) - 1;
                Expr::bitvec_const(max_val, wide_width)
            };

            let in_range =
                sum_wide.clone().bvsge(signed_min).and(sum_wide.clone().bvsle(signed_max));
            let result_n = sum_wide.extract(width - 1, 0);

            let option_sort = self.make_option_sort(Sort::bitvec(width));
            let some_result = self.make_option_some(&option_sort, result_n);
            let none_result = self.make_option_none(&option_sort);

            let final_result = Expr::ite(in_range, some_result, none_result);
            self.assign_value_to_place(destination, final_result);
        } else {
            debug!("checked_add_unsigned: fallback to symbolic result");
            self.codegen_symbolic_result(destination);
        }

        target
    }
}
