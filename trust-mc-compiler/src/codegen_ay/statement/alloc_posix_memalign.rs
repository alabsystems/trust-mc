// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct `libc::posix_memalign` modeling for statement/BMC codegen.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Model direct `libc::posix_memalign(&mut out, align, size)` calls (BMC).
    pub(super) fn try_codegen_posix_memalign_bmc(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        if callee_path != "libc::posix_memalign" || args.len() < 3 {
            return None;
        }
        let out_local = match &args[0] {
            Operand::Copy(place) | Operand::Move(place) => {
                let ref_base = self.ssa_base_name(place);
                let pointee_base = self
                    .ref_pointees
                    .get(ref_base.as_str())
                    .cloned()
                    .or_else(|| self.ensure_ref_pointee_for_place(place))?;
                let ref_pointees = &self.ref_pointees;
                Self::resolve_ref_chain_target(ref_pointees, &pointee_base)
            }
            _ => return None,
        };
        if out_local == usize::MAX {
            return None;
        }
        let out_place = Place { local: out_local, projection: vec![] };
        let old_out = self.codegen_place(&out_place)?;
        let size_raw = self.codegen_operand(&args[2])?;
        let size_expr = self.coerce_to_ptr_width(size_raw);
        let align_raw = self.codegen_operand(&args[1])?;
        let align_expr = self.coerce_to_ptr_width(align_raw);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let one = Expr::bitvec_const(1u128, POINTER_WIDTH);
        let ptr_bytes = Expr::bitvec_const((POINTER_WIDTH / 8) as u128, POINTER_WIDTH);
        let valid_align = align_expr.clone().ne(zero.clone()).and(
            align_expr
                .clone()
                .bvand(align_expr.clone().bvsub(one))
                .eq(zero.clone())
                .and(align_expr.clone().bvurem(ptr_bytes).eq(zero)),
        );
        let ret_width = self.infer_sort_from_place(destination)?.bitvec_width()?;
        let ret_code = Expr::ite(
            valid_align.clone(),
            Expr::bitvec_const(0u128, ret_width),
            Expr::bitvec_const(22u128, ret_width),
        );
        self.assign_value_to_place(destination, ret_code);
        let alloc_val = self.ctx.heap_alloc(size_expr, align_expr);
        self.assign_value_to_place(&out_place, Expr::ite(valid_align, alloc_val, old_out));
        debug!("posix_memalign: modeled direct libc::posix_memalign call (BMC)");
        target
    }
}
