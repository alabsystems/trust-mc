// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Struct aggregate codegen for AY.
//!
//! Extracted from `aggregate_adt.rs` to reduce file size (#2246).
//! Handles construction of struct values in SMT encoding:
//! - Generic structs: field-by-field construction
//! - Vec: actual layout (buf: RawVec, len) → model (ptr, len, cap, data)
//! - String: wraps Vec<u8>
//! - RawVec: (ptr: Unique<T>, cap)
//! - BigInt/BigUint/Ratio: fresh symbolic Int (sound over-approximation)

use ay_bindings::{Expr, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{AdtDef, GenericArgs, VariantIdx};
use rustc_public_bridge::IndexedVal;
use tracing::debug;

use crate::codegen_ay::types::int_sort;

use super::StatementCodegen;
use crate::codegen_ay::names::{RUST_STRING_CONS, RUST_STRING_SORT};
use crate::codegen_ay::types::{POINTER_WIDTH, bv8_sort, flatten_dt_array_element, ptr_sort};

/// Non-null placeholder pointer value used when actual pointer cannot be extracted.
const FALLBACK_POINTER: u128 = 0x1000;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen struct aggregate construction.
    pub(super) fn codegen_struct_aggregate(
        &mut self,
        def: AdtDef,
        variant_idx: VariantIdx,
        args: GenericArgs,
        operands: &[Operand],
        adt_name: &str,
    ) -> Option<Expr> {
        let variants = def.variants();
        let base_name = def.trimmed_name();

        // Defensive: structs should always have exactly one variant
        if variants.is_empty() {
            self.ctx
                .unsupported("Aggregate::Adt", format!("Struct '{}' has no variants", adt_name));
            return None;
        }
        debug_assert_eq!(variant_idx.to_index(), 0, "Struct should always use variant 0");

        // #924: Check field count BEFORE Int sort handling
        let variant = &variants[variant_idx.to_index()];
        let expected_fields = variant.fields().len();

        if operands.len() != expected_fields {
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!(
                    "Struct '{}' expected {} fields, got {} operands",
                    adt_name,
                    expected_fields,
                    operands.len()
                ),
            );
            return None;
        }

        // Clone args before sort inference so field operands can be coerced to
        // the constructor field sorts below.
        let args_for_fields = args.clone();
        // Part of #1632: Clone args only for Vec/RawVec element type extraction
        let args_for_vec = if base_name == "Vec" { Some(args.clone()) } else { None };
        let sort = Self::infer_adt_sort(def, args)?;

        // #918, #926: BigInt/BigUint/Ratio types return Int sort - handle specially
        if sort.is_int() {
            return self.codegen_bigint_aggregate(adt_name, &sort);
        }
        if !sort.is_datatype() {
            if sort.is_bool() && operands.is_empty() {
                debug!(
                    "codegen_adt_aggregate: {} fieldless struct ZST -> canonical Bool false",
                    adt_name
                );
                return Some(Expr::bool_const(false));
            }
            if operands.len() == 1 {
                let expr = self.codegen_operand(&operands[0])?;
                debug!(
                    "codegen_adt_aggregate: {} non-datatype wrapper → returning operand directly",
                    adt_name
                );
                return Some(expr);
            }
            self.ctx.unsupported(
                "Aggregate::Adt",
                format!(
                    "Struct '{}' mapped to non-datatype sort {:?} with {} operands",
                    adt_name,
                    sort,
                    operands.len()
                ),
            );
            return None;
        }

        // Part of #1275, #1632: Vec/String/RawVec special handling.
        if base_name == "Vec" && operands.len() == 2 {
            return self.codegen_vec_aggregate(operands, args_for_vec.as_ref()?, sort);
        }
        if base_name == "String" && operands.len() == 1 {
            return self.codegen_string_aggregate(operands, sort);
        }
        if base_name == "RawVec" && operands.len() == 2 {
            return self.codegen_rawvec_aggregate(operands, sort);
        }

        // The constructor's DECLARED field sorts (from `infer_adt_sort`, which
        // uses `field.ty_with_args` — the recursive substitution). The
        // per-field coercion below targets the weaker `resolve_generic_ty`
        // sort, which can disagree with the declaration for nested generics;
        // the final guard reconciles each field against THESE authoritative
        // sorts so the emitted datatype constructor is always well-typed.
        let declared_field_sorts: Vec<Sort> = sort
            .datatype_sort()
            .and_then(|dt| dt.constructors.first())
            .map(|c| c.fields.iter().map(|f| f.sort.clone()).collect())
            .unwrap_or_default();

        // Codegen all field values
        let variant_fields = variant.fields();
        let mut field_exprs = Vec::with_capacity(operands.len());
        for (i, op) in operands.iter().enumerate() {
            if let Some(expr) = self.codegen_operand(op) {
                let expr = if let Some(field_def) = variant_fields.get(i) {
                    let expected_sort = Self::resolve_generic_ty(field_def.ty(), &args_for_fields)
                        .and_then(Self::infer_sort_from_ty);
                    if let Some(target_sort) = expected_sort {
                        self.coerce_struct_field_to_sort(op, expr, &target_sort)
                    } else {
                        expr
                    }
                } else {
                    expr
                };
                // Final well-typedness guard. If the field expr STILL disagrees
                // with the constructor's declared field sort, emitting it builds
                // a MALFORMED datatype constructor (e.g. `Arguments_lt_mk` with
                // an `Array` where `fld_template: BitVec64`): the solver rejects
                // the command as a "problem-contributing command discarded" and
                // silently DROPS that constraint, collapsing the whole VC to
                // reason-unknown / INCONCLUSIVE (no checks). Fail-safe to a fresh
                // unconstrained symbolic of the DECLARED field sort — a sound
                // over-approximation (havoc only ADDS behaviours, never removes a
                // counterexample, so it can never hide a bug / mask a missed bug)
                // that keeps the SMT well-typed. Strictly better than dropping the
                // whole command. A mismatch here always meant a malformed
                // (already-failing) query, so this converts failures without
                // weakening a genuine proof.
                let expr = match declared_field_sorts.get(i) {
                    Some(declared) if expr.sort() != declared => {
                        let fresh = self.ctx.fresh_name("field_sort_mismatch");
                        self.ctx.declare_var(&fresh, declared.clone())
                    }
                    _ => expr,
                };
                field_exprs.push(expr);
            } else {
                self.ctx.unsupported(
                    "Aggregate::Adt",
                    format!("Failed to codegen field {} of struct '{}'", i, adt_name),
                );
                return None;
            }
        }

        debug!("  Constructing struct '{}' with {} fields", adt_name, field_exprs.len());
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&sort, adt_name);
        Some(Expr::datatype_constructor(adt_name, cons_name, field_exprs, sort))
    }

    fn coerce_struct_field_to_sort(
        &mut self,
        op: &Operand,
        expr: Expr,
        target_sort: &Sort,
    ) -> Expr {
        if expr.sort() == target_sort {
            return expr;
        }
        if let Some(option_expr) = self.wrap_flattened_option_field(op, &expr, target_sort) {
            return option_expr;
        }
        expr
    }

    fn wrap_flattened_option_field(
        &mut self,
        op: &Operand,
        payload: &Expr,
        target_sort: &Sort,
    ) -> Option<Expr> {
        if !payload.sort().is_bitvec() {
            return None;
        }

        let dt = target_sort.datatype_sort()?;
        let none_ctor = dt.constructors.iter().find(|ctor| ctor.fields.is_empty())?;
        let some_ctor = dt
            .constructors
            .iter()
            .find(|ctor| ctor.fields.len() == 1 && payload.sort() == &ctor.fields[0].sort)?;

        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }

        let base = self.ssa_base_name(place);
        let discr_name = crate::codegen_ay::names::discrim_name(&base);
        let discr = self.resolve_concrete_expr(self.env_lookup(&discr_name)?);
        let is_some = if discr.sort().is_bool() {
            discr
        } else {
            let width = discr.sort().bitvec_width()?;
            discr.eq(Expr::bitvec_const(1, width))
        };

        let some_expr = Expr::datatype_constructor(
            &dt.name,
            &some_ctor.name,
            vec![payload.clone()],
            target_sort.clone(),
        );
        let none_expr =
            Expr::datatype_constructor(&dt.name, &none_ctor.name, vec![], target_sort.clone());
        Some(Expr::ite(is_some, some_expr, none_expr))
    }

    /// Codegen BigInt/BigUint/Ratio aggregate as fresh symbolic Int.
    /// Sound over-approximation: "some Int value was constructed".
    pub(super) fn codegen_bigint_aggregate(
        &mut self,
        adt_name: &str,
        _sort: &Sort,
    ) -> Option<Expr> {
        let fresh_name = self.ctx.fresh_name("bigint_aggregate");
        let symbolic_int = self.ctx.declare_var(&fresh_name, int_sort());
        if adt_name == "BigUint" {
            self.ctx.assert(symbolic_int.clone().int_ge(Expr::int_const(0)));
            debug!(
                "  BigUint '{}': returning fresh non-negative symbolic Int '{}' (#934)",
                adt_name, fresh_name
            );
        } else {
            debug!(
                "  BigInt/Int-sorted '{}': returning fresh symbolic Int '{}' (#926)",
                adt_name, fresh_name
            );
        }
        Some(symbolic_int)
    }

    /// Codegen Vec aggregate from actual layout (buf: RawVec, len) to model (ptr, len, cap, data).
    fn codegen_vec_aggregate(
        &mut self,
        operands: &[Operand],
        args_for_vec: &GenericArgs,
        sort: Sort,
    ) -> Option<Expr> {
        let buf_expr = self.codegen_operand(&operands[0])?;
        let len_expr = self.codegen_operand(&operands[1])?;

        let (ptr_expr, cap_expr) = if let Some(dt_name) = buf_expr.sort().datatype_name()
            && dt_name == "RawVec"
        {
            let ptr = buf_expr.clone().field_select("RawVec", "fld_ptr", ptr_sort());
            let cap = buf_expr.field_select("RawVec", "fld_cap", ptr_sort());
            (ptr, cap)
        } else {
            debug!("Vec aggregate: buf is {:?}, using defaults", buf_expr.sort());
            let ptr = if buf_expr.sort().is_bitvec() {
                buf_expr
            } else {
                Expr::bitvec_const(FALLBACK_POINTER, POINTER_WIDTH)
            };
            (ptr, Expr::bitvec_const(0, POINTER_WIDTH))
        };

        use rustc_public::ty::GenericArgKind;
        let elem_sort = if let Some(GenericArgKind::Type(inner_ty)) = args_for_vec.0.first() {
            Self::infer_sort_from_ty(*inner_ty).unwrap_or_else(|| Sort::bitvec(32))
        } else {
            Sort::bitvec(32)
        };
        // Part of #2990: flatten DT elements to BV for PDR compatibility.
        let elem_sort = flatten_dt_array_element(elem_sort);
        // Part of #2267: Cow<str> auto-derefs to &str for name functions.
        let elem_sort_name = crate::codegen_ay::names::sort_short_name(&elem_sort);
        let array_sort = Sort::array(ptr_sort(), elem_sort);

        let data_name = self.ctx.fresh_name("vec_data");
        let data = self.ctx.declare_var(&data_name, array_sort);

        debug!("  Constructing Vec with fld_data from actual layout");
        let sort_name = crate::codegen_ay::names::vec_sort_name(&elem_sort_name);
        let cons_name = crate::codegen_ay::names::cons_name(&sort_name);
        Some(Expr::datatype_constructor(
            sort_name,
            cons_name,
            vec![ptr_expr, len_expr, cap_expr, data],
            sort,
        ))
    }

    /// Codegen String aggregate from actual layout (vec: Vec<u8>) to model (ptr, len, cap, data).
    fn codegen_string_aggregate(&mut self, operands: &[Operand], sort: Sort) -> Option<Expr> {
        let vec_expr = self.codegen_operand(&operands[0])?;

        // Clone Sort (O(1) Arc) so dt_name borrows from sort_ref rather than vec_expr.
        let vec_sort_ref = vec_expr.sort().clone();
        let vec_dt_name: Option<&str> = vec_sort_ref.datatype_name();
        let (ptr_expr, len_expr, cap_expr, data_expr) = if let Some(dt_name) = vec_dt_name
            && dt_name.starts_with("Vec")
        {
            let ptr = vec_expr.clone().field_select(dt_name, "fld_ptr", ptr_sort());
            let len = vec_expr.clone().field_select(dt_name, "fld_len", ptr_sort());
            let cap = vec_expr.clone().field_select(dt_name, "fld_cap", ptr_sort());
            let u8_sort = bv8_sort();
            let array_sort = Sort::array(ptr_sort(), u8_sort);
            let data = vec_expr.field_select(dt_name, "fld_data", array_sort);
            (ptr, len, cap, data)
        } else {
            debug!("String aggregate: inner vec is {:?}, using defaults", vec_expr.sort());
            let u8_sort = bv8_sort();
            let array_sort = Sort::array(ptr_sort(), u8_sort);
            let data_name = self.ctx.fresh_name("string_data");
            let data = self.ctx.declare_var(&data_name, array_sort);
            (
                Expr::bitvec_const(FALLBACK_POINTER, POINTER_WIDTH),
                Expr::bitvec_const(0, POINTER_WIDTH),
                Expr::bitvec_const(0, POINTER_WIDTH),
                data,
            )
        };

        debug!("  Constructing String with fld_data from actual layout");
        Some(Expr::datatype_constructor(
            RUST_STRING_SORT,
            RUST_STRING_CONS,
            vec![ptr_expr, len_expr, cap_expr, data_expr],
            sort,
        ))
    }

    /// Codegen RawVec aggregate from actual layout (ptr: Unique<T>, cap: usize).
    fn codegen_rawvec_aggregate(&mut self, operands: &[Operand], sort: Sort) -> Option<Expr> {
        let ptr_expr = self.codegen_operand(&operands[0])?;
        let cap_expr = self.codegen_operand(&operands[1])?;

        let ptr_val = if ptr_expr.sort().is_bitvec() {
            ptr_expr
        } else {
            debug!("RawVec aggregate: ptr is {:?}, coercing", ptr_expr.sort());
            Expr::bitvec_const(FALLBACK_POINTER, POINTER_WIDTH)
        };

        debug!("  Constructing simplified RawVec from actual layout");
        Some(Expr::datatype_constructor("RawVec", "RawVec_mk", vec![ptr_val, cap_expr], sort))
    }
}
