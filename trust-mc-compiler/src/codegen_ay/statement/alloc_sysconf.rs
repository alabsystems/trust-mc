// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct `libc::sysconf` modeling for statement/BMC codegen.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Model direct `libc::sysconf(name)` calls (BMC).
    ///
    /// The call has no Rust-visible memory effects. Its return depends on the
    /// host environment, so assign a fresh symbolic value instead of choosing a
    /// platform-specific constant.
    pub(super) fn try_codegen_sysconf_bmc(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;
        if callee_path != "libc::sysconf" || args.len() != 1 {
            return None;
        }

        let result_sort = self.infer_sort_from_place(destination)?;
        let result_name = self.ctx.fresh_name("sysconf_result");
        let symbolic_result = self.ctx.declare_var(&result_name, result_sort);
        self.assign_value_to_place(destination, symbolic_result);
        debug!("sysconf: modeled direct libc::sysconf call (BMC)");
        target
    }
}
