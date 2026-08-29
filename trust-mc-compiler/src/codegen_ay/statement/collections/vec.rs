// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec semantic model for AY codegen.
//!
//! Vec is modeled as a struct with (ptr, len, cap, data) fields where
//! data is an SMT Array<usize, Element> for element storage.
//! This provides element-level tracking for `v[i]` indexing.
//!
//! Part of #1312: Collection stubs implementation.
//! Part of #1354: Statement module refactoring.
//! Part of #1628: Array backing for slice indexing.

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, flatten_dt_array_element, ptr_sort};
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::StatementCodegen;
// VecFields, VEC_FIELD_FALLBACK_COUNTER, counter functions, and field
// extraction helpers moved to vec_fields.rs per #4206.

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Dangling-pointer + provenance constraints for `Vec::new` /
    /// `Vec::with_capacity`.
    ///
    /// Address-vs-value (wave 1): the two payload parameters used to be two
    /// adjacent bare `Expr`s — trivially swappable, and the caller's only
    /// protection was that nobody had swapped them yet. `cap` is the CAPACITY
    /// (a `usize` value), `ptr` is the Vec's allocation base (an address); they
    /// are now different types, so the swap is a compile error.
    ///
    /// The old `cap.sort().bitvec_width() == Some(POINTER_WIDTH)` guard read as
    /// "is the capacity a pointer?". It is not; the real precondition is that
    /// `cap` is comparable with the `zero` constant it is about to be equated
    /// to, so it is now written against `zero`'s own width. `zero` is built at
    /// `POINTER_WIDTH`, so the two tests accept exactly the same expressions.
    fn add_vec_dangling_provenance_constraints(
        &mut self,
        stub_kind: StubKind,
        cap: &Val,
        ptr: &Loc,
    ) {
        if !self.ctx.config.extra_pointer_checks {
            return;
        }

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        if stub_kind == StubKind::VecNew {
            self.ctx.assert(ptr.as_expr().clone().bvugt(zero));
            self.ctx.heap_invalidate_no_provenance(ptr.as_expr().clone());
            return;
        }

        // For VecWithCapacity: if cap is statically zero, unconditionally
        // invalidate (same as VecNew). For symbolic cap, assert the pointer
        // is non-null on the cap==0 lane via ITE.
        let is_static_zero = matches!(
            cap.as_expr().value(),
            ExprValue::BitVecConst { value, .. } if value == &0u8.into()
        );
        if is_static_zero {
            self.ctx.assert(ptr.as_expr().clone().bvugt(zero));
            self.ctx.heap_invalidate_no_provenance(ptr.as_expr().clone());
        } else if cap.as_expr().sort().bitvec_width() == zero.sort().bitvec_width() {
            // Symbolic cap: conditionally assert ptr > 0 when cap == 0.
            let cap_is_zero = cap.as_expr().clone().eq(zero.clone());
            self.ctx.assert(Expr::ite(
                cap_is_zero.clone(),
                ptr.as_expr().clone().bvugt(zero),
                Expr::bool_const(true),
            ));
            // Conditional provenance invalidation: when cap == 0, the pointer
            // has no backing allocation, so its provenance is invalid.
            // Mirrors the unconditional heap_invalidate_no_provenance in the
            // static-zero branch above.
            self.ctx.heap_invalidate_no_provenance_if(ptr.as_expr().clone(), cap_is_zero);
        }
    }

    /// Codegen Vec operations (Part of #1312, #1628).
    ///
    /// Vec is modeled as a struct with (ptr, len, cap, data) fields
    /// where data is an SMT Array for element storage.
    pub(in crate::codegen_ay::statement) fn codegen_vec_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            SliceIntoVec, VecAsMutPtr, VecAsPtr, VecAsSlice, VecCapacity, VecClear, VecClone,
            VecContains, VecDrop, VecEq, VecExtendFromSlice, VecFromElem, VecFromSlice, VecInsert,
            VecIntoIter, VecIsEmpty, VecIter, VecIterMut, VecLen, VecNew, VecPop, VecPush,
            VecRemove, VecReserve, VecReserveExact, VecResize, VecSetLen, VecShrinkToFit,
            VecSplice, VecTruncate, VecWithCapacity,
        };

        debug!(?stub_kind, %callee_path, "codegen_vec_stub");

        match stub_kind {
            VecNew | VecWithCapacity => {
                // Infer element sort from destination type, default to bitvec(POINTER_WIDTH)
                let elem_sort = self.infer_vec_elem_sort(destination).unwrap_or_else(ptr_sort);
                // Part of #2990: flatten DT elements to BV for PDR compatibility.
                let elem_sort = flatten_dt_array_element(elem_sort);
                let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
                let vec_sort_name = names::vec_sort_name(&names::sort_short_name(&elem_sort));

                let vec_sort = struct_sort(vec_sort_name.clone(), names::vec_fields(array_sort));

                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                let ptr_name = self.ctx.fresh_name("vec_ptr");
                // Freshly declared allocation base for this Vec: an ADDRESS by
                // construction (this is the site that mints it).
                let ptr = Loc::of_address(self.ctx.declare_var(&ptr_name, ptr_sort()));

                // `Vec::with_capacity(n)`'s argument is a `usize` COUNT, and the
                // `Vec::new` case is the literal 0: a VALUE either way.
                let cap = Val::of_value(if stub_kind == VecWithCapacity && !args.is_empty() {
                    self.codegen_operand(&args[0]).unwrap_or(zero.clone())
                } else {
                    zero.clone()
                });
                self.add_vec_dangling_provenance_constraints(stub_kind, &cap, &ptr);

                // Initialize data array with symbolic default value
                let default_name = self.ctx.fresh_name("vec_default");
                let default_elem = self.ctx.declare_var(&default_name, elem_sort);
                let data = Expr::const_array(ptr_sort(), default_elem);

                let ctor_name =
                    crate::codegen_ay::names::resolve_ctor_name(&vec_sort, &vec_sort_name);
                let vec = Expr::datatype_constructor(
                    vec_sort_name,
                    ctor_name,
                    vec![ptr.into_expr(), zero, cap.into_expr(), data],
                    vec_sort,
                );
                self.assign_value_to_place(destination, vec);
                target
            }

            VecPush => {
                if args.len() < 2 {
                    warn!("Vec::push requires 2 args (self, value) — fail-closed (#2497)");
                    return None;
                }

                let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
                    return target;
                };

                if let Some(fields) = Self::extract_all_vec_fields(&vec) {
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_len = fields.len.clone().bvadd(one);

                    // Deterministic cap updates: cap+1 before comparison to avoid clone
                    let cap_if_grow =
                        fields.cap.clone().bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
                    let grow_needed = fields.cap.clone().bvult(new_len.clone());
                    // Last use of `fields.cap` — move into ite else-branch
                    let new_cap = Expr::ite(grow_needed, cap_if_grow, fields.cap);

                    // Store the pushed value into the data array at index = len
                    let value = self.codegen_operand(&args[1]);
                    let new_data = if let Some(mut val) = value {
                        val = crate::codegen_ay::chc::call::codegen_call_vec_ops::coerce_array_element(val, &fields.data.sort());
                        // Last-resort: fresh symbolic if sorts still mismatch (Part of dterm#6841).
                        if let Some(arr) = fields.data.sort().array_sort() {
                            if *val.sort() != arr.element_sort {
                                let sym_name =
                                    crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                                val = self.ctx.declare_var(&sym_name, arr.element_sort.clone());
                            }
                        }
                        fields.data.store(fields.len, val)
                    } else {
                        fields.data
                    };

                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, new_cap, new_data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecInsert => {
                if args.len() < 3 {
                    warn!("Vec::insert requires 3 args (self, index, element) — fail-closed");
                    return None;
                }

                let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
                    return target;
                };

                if let Some(fields) = Self::extract_all_vec_fields(&vec) {
                    let index = self
                        .codegen_operand(&args[1])
                        .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
                    let index = self.coerce_to_ptr_width(index);

                    // assert(index <= len) — Vec::insert panics if index > len
                    self.ctx.assert(index.clone().bvule(fields.len.clone()));

                    // Store element at index position
                    let value = self.codegen_operand(&args[2]);
                    let new_data = if let Some(mut val) = value {
                        val = crate::codegen_ay::chc::call::codegen_call_vec_ops::coerce_array_element(val, &fields.data.sort());
                        if let Some(arr) = fields.data.sort().array_sort() {
                            if *val.sort() != arr.element_sort {
                                let sym_name =
                                    crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                                val = self.ctx.declare_var(&sym_name, arr.element_sort.clone());
                            }
                        }
                        fields.data.store(index, val)
                    } else {
                        fields.data
                    };

                    // Elements after index are now unconstrained (sound over-approximation)
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_len = fields.len.bvadd(one);

                    let cap_if_grow =
                        fields.cap.clone().bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
                    let grow_needed = fields.cap.clone().bvult(new_len.clone());
                    let new_cap = Expr::ite(grow_needed, cap_if_grow, fields.cap);

                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, new_cap, new_data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecReserve | VecReserveExact => {
                if args.len() < 2 {
                    let method = if stub_kind == VecReserveExact {
                        "Vec::reserve_exact"
                    } else {
                        "Vec::reserve"
                    };
                    warn!("{method} requires 2 args (self, additional) — fail-closed (#2497)");
                    return None;
                }

                let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
                    return target;
                };

                if let Some(additional_raw) = self.codegen_operand(&args[1])
                    && let Some(fields) = Self::extract_all_vec_fields(&vec)
                {
                    let additional = self.coerce_to_ptr_width(additional_raw);
                    let required_cap = fields.len.clone().bvadd(additional);
                    // Part of #3409: guard against unsigned overflow on len+additional.
                    // Rust's Vec::reserve panics on capacity overflow (checked_add).
                    self.ctx.assert(required_cap.clone().bvuge(fields.len.clone()));
                    let grow_needed = fields.cap.clone().bvult(required_cap.clone());
                    let new_cap = Expr::ite(grow_needed, required_cap, fields.cap);

                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, fields.len, new_cap, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecShrinkToFit => {
                if args.is_empty() {
                    warn!("Vec::shrink_to_fit requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, vec)) = self.resolve_collection_base(&args[0])
                    && let Some(fields) = Self::extract_all_vec_fields(&vec)
                {
                    // Conservative model: shrink capacity to the current length.
                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, fields.len.clone(), fields.len, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecPop => {
                // Part of #1745: Return actual popped element, not symbolic
                if args.is_empty() {
                    warn!("Vec::pop requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, vec)) = self.resolve_collection_base(&args[0]) {
                    if let Some(fields) = Self::extract_all_vec_fields(&vec) {
                        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                        let len_gt_zero = fields.len.clone().bvugt(zero.clone());

                        // Get element at len-1 BEFORE decrementing
                        let last_idx = fields.len.clone().bvsub(one.clone());
                        let popped_elem = fields.data.clone().select(last_idx);

                        // Get element sort from the data array
                        let elem_sort = fields
                            .data
                            .sort()
                            .array_sort()
                            .map_or_else(ptr_sort, |arr| arr.element_sort.clone());

                        // Create Option<T> result
                        let option_sort = self.make_option_sort(elem_sort);
                        let none = self.make_option_none(&option_sort);
                        let some = self.make_option_some(&option_sort, popped_elem);

                        // Return Some(elem) if len > 0, None otherwise
                        let result = Expr::ite(len_gt_zero.clone(), some, none);
                        self.assign_value_to_place(destination, result);

                        // Update len (decrement if > 0); last use of fields.len — move
                        let new_len = Expr::ite(len_gt_zero, fields.len.bvsub(one), zero);
                        let new_vec = Expr::datatype_constructor(
                            fields.dt_name,
                            fields.ctor_name,
                            vec![fields.ptr, new_len, fields.cap, fields.data],
                            fields.sort,
                        );
                        self.env_update(base, new_vec);
                    } else {
                        // Fallback: if vec not tracked, return symbolic Option
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    // Fallback: if vec not tracked, return symbolic Option
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            VecRemove => {
                // Vec::remove(index) -> T — removes and returns element at index,
                // shifting all elements after it left by one. Panics if index >= len.
                if args.len() < 2 {
                    warn!("Vec::remove requires 2 args (self, index) — fail-closed");
                    return None;
                }

                let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
                    self.codegen_symbolic_result(destination);
                    return target;
                };

                if let Some(fields) = Self::extract_all_vec_fields(&vec) {
                    let index = self
                        .codegen_operand(&args[1])
                        .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
                    let index = self.coerce_to_ptr_width(index);

                    // assert(index < len) — Vec::remove panics if index >= len
                    self.ctx.assert(index.clone().bvult(fields.len.clone()));

                    // Select the element at index (return value)
                    let removed_elem = fields.data.clone().select(index);
                    self.assign_value_to_place(destination, removed_elem);

                    // Decrement len by 1
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_len = fields.len.bvsub(one);

                    // Shifted positions are unconstrained (sound over-approximation):
                    // we keep the same data array, which is sound because indices
                    // >= new_len are logically out-of-bounds.
                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, fields.cap, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                } else {
                    // Fallback: if vec not tracked, return symbolic result
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            VecLen => {
                if args.is_empty() {
                    warn!("Vec::len requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());
                    self.assign_value_to_place(destination, len);
                } else {
                    let name = self.ctx.fresh_name("vec_len");
                    let len = self.ctx.declare_var(&name, ptr_sort());
                    self.assign_value_to_place(destination, len);
                }
                target
            }

            VecCapacity => {
                if args.is_empty() {
                    warn!("Vec::capacity requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let cap = self.vec_field_select_declared(&vec, "fld_cap", ptr_sort());
                    self.assign_value_to_place(destination, cap);
                } else {
                    let name = self.ctx.fresh_name("vec_cap");
                    let cap = self.ctx.declare_var(&name, ptr_sort());
                    self.assign_value_to_place(destination, cap);
                }
                target
            }

            VecIsEmpty => {
                if args.is_empty() {
                    warn!("Vec::is_empty requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    let is_empty = len.eq(zero);
                    self.assign_value_to_place(destination, is_empty);
                } else {
                    let name = self.ctx.fresh_name("vec_is_empty");
                    let is_empty = self.ctx.declare_var(&name, bool_sort());
                    self.assign_value_to_place(destination, is_empty);
                }
                target
            }

            // Part of #2125 Phase 2: Vec::contains(&self, &T) -> bool
            // Part of #3348: Vec::eq (PartialEq) -> bool
            // Sound over-approximation: symbolic Bool (no element-level content model)
            VecContains | VecEq => {
                let prefix = if stub_kind == VecEq { "vec_eq" } else { "vec_contains" };
                let name = self.ctx.fresh_name(prefix);
                let result = self.ctx.declare_var(&name, bool_sort());
                self.assign_value_to_place(destination, result);
                target
            }

            VecClear => {
                if args.is_empty() {
                    warn!("Vec::clear requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, vec)) = self.resolve_collection_base(&args[0])
                    && let Some(fields) = Self::extract_all_vec_fields(&vec)
                {
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, zero, fields.cap, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecTruncate => {
                if args.len() < 2 {
                    warn!("Vec::truncate requires 2 args (self, len) — fail-closed");
                    return None;
                }

                let new_len_arg = self.codegen_operand(&args[1]);

                if let Some(new_len_arg) = new_len_arg
                    && let Some((base, vec)) = self.resolve_collection_base(&args[0])
                    && let Some(fields) = Self::extract_all_vec_fields(&vec)
                {
                    // Truncate to min(new_len_arg, len) — no effect if new_len_arg >= len
                    let shrink = new_len_arg.clone().bvult(fields.len.clone());
                    let new_len = Expr::ite(shrink, new_len_arg, fields.len);
                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, fields.cap, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            // Part of #3895: Vec::set_len(new_len) — len-only mutation preserving
            // ptr, cap, and data. Same pattern as VecClear but with args[1] instead
            // of zero.
            VecSetLen => {
                if args.len() < 2 {
                    warn!("Vec::set_len requires 2 args (self, new_len) — fail-closed");
                    return None;
                }

                let new_len_expr = self.codegen_operand(&args[1]);

                if let Some(new_len) = new_len_expr
                    && let Some((base, vec)) = self.resolve_collection_base(&args[0])
                    && let Some(fields) = Self::extract_all_vec_fields(&vec)
                {
                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, fields.cap, fields.data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                }
                target
            }

            VecClone => {
                if args.is_empty() {
                    warn!("Vec::clone requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    self.assign_value_to_place(destination, vec);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            VecDrop => target, // no-op: ownership not in SMT state
            // View/pointer/iterator creation delegated to vec_view.rs
            VecAsSlice | VecAsPtr | VecAsMutPtr | VecIntoIter | VecIter | VecIterMut => {
                self.codegen_vec_view_stub(stub_kind, args, destination, target, callee_path)
            }

            // Part of #3494: construction/mutation ops delegated to vec_ops.rs.
            VecFromElem => self.codegen_vec_from_elem(args, destination, target),
            VecResize => self.codegen_vec_resize(args, destination, target),
            VecExtendFromSlice => self.codegen_vec_extend_from_slice(args, destination, target),
            SliceIntoVec => self.codegen_slice_into_vec(args, destination, target),
            VecFromSlice => {
                // `<Vec<T> as From<&[T]>>::from` and `From<[T; N]>`.
                //
                // This used to leave the destination entirely unconstrained. The
                // DATA genuinely is an over-approximation here, but the LENGTH is
                // not an approximation at all -- a Vec built from a slice has
                // exactly that slice's length, and from `[T; N]` exactly N.
                // Leaving it symbolic was strictly weaker than what we know, and
                // it made obviously-true facts unprovable:
                //
                //     Vec::from([1u8, 2, 3, 4]).len() == 4      // FAILED
                //
                // which in turn sank `<Vec<T> as BoundedArbitrary>::bounded_any`,
                // since that builds its vector this way before truncating.
                //
                // `codegen_slice_into_vec` already resolves the length correctly
                // -- concrete when it can recover N from the argument's type,
                // else the slice's length expression, else a fresh symbol -- and
                // keeps the data array symbolic, so routing here refines the
                // length without weakening anything about the contents.
                debug!("VecFromSlice: precise length, symbolic data (BMC)");
                self.codegen_slice_into_vec(args, destination, target)
            }

            VecSplice => {
                // Vec::splice(range, replace_with) -> Splice<I> (Part of #4202).
                // Sound over-approximation: the replaced range is removed, replacement
                // elements are inserted. We model the length change as symbolic and leave
                // the data array unconstrained (shifted/replaced positions unknown).
                if args.len() < 3 {
                    warn!("Vec::splice requires 3 args (self, range, replace_with) — fail-closed");
                    return None;
                }

                let Some((base, vec)) = self.resolve_collection_base(&args[0]) else {
                    self.codegen_symbolic_result(destination);
                    return target;
                };

                if let Some(fields) = Self::extract_all_vec_fields(&vec) {
                    // Over-approximate: new_len is symbolic (splice can grow or shrink).
                    let sym_name = self.ctx.fresh_name("ay_vec_splice_len");
                    let new_len = self.ctx.declare_var(&sym_name, ptr_sort());

                    // Build new data array with symbolic default (sound over-approximation).
                    let elem_sort = fields
                        .data
                        .sort()
                        .array_sort()
                        .map(|a| a.element_sort.clone())
                        .unwrap_or_else(ptr_sort);
                    let sym_data_name = self.ctx.fresh_name("ay_vec_splice_data");
                    let new_default = self.ctx.declare_var(&sym_data_name, elem_sort);
                    let new_data = Expr::const_array(ptr_sort(), new_default);

                    // Capacity grows if needed: cap = max(old_cap, new_len).
                    let grow_needed = fields.cap.clone().bvult(new_len.clone());
                    let new_cap = Expr::ite(grow_needed, new_len.clone(), fields.cap);

                    let new_vec = Expr::datatype_constructor(
                        fields.dt_name,
                        fields.ctor_name,
                        vec![fields.ptr, new_len, new_cap, new_data],
                        fields.sort,
                    );
                    self.env_update(base, new_vec);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                // splice returns Splice iterator — over-approximate as symbolic destination.
                target
            }
            // partial dispatch: StubKind — parent routes only Vec* variants here.
            _other => {
                warn!(
                    ?_other,
                    "codegen_vec_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }

    // infer_vec_elem_sort, extract_all_vec_fields, vec_field_select, extract_vec_data
    // moved to vec_fields.rs per #4206.
}
