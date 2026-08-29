// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Memory/pointer intrinsic dispatch: align_of_val, size_of_val, transmute, copy,
//! offset, volatile_load/store, typed_swap_nonoverlapping.
//!
//! Part of #3477: volatile and swap intrinsics added for BMC parity with CHC encoding.

use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use super::{CallDispatchOutcome, extract_method_name};
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Memory/pointer intrinsics: align_of_val, size_of_val, transmute, copy, offset,
    /// volatile_load/store, typed_swap_nonoverlapping.
    ///
    /// Part of #3758: Returns `CallDispatchOutcome` so the family boundary can
    /// distinguish miss, continue, and diverge explicitly.
    ///
    /// Once the method name matches a memory intrinsic, this function MUST
    /// return a handled outcome — never `Miss`. Malformed-args branches
    /// record `unsupported_with_fallback` and return the normal target
    /// instead of silently dropping the call.
    pub(in crate::codegen_ay::statement) fn dispatch_memory(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        let Some(method) = extract_method_name(fn_name) else {
            return CallDispatchOutcome::Miss;
        };

        if method == "align_of_val" {
            debug!("AY codegen: handling align_of_val");
            return CallDispatchOutcome::from_handled_target(self.codegen_align_of_val(
                args,
                destination,
                target,
            ));
        }
        if method == "size_of_val" {
            debug!("AY codegen: handling size_of_val");
            return CallDispatchOutcome::from_handled_target(self.codegen_size_of_val(
                args,
                destination,
                target,
            ));
        }
        if method == "transmute" {
            debug!("AY codegen: handling transmute");
            return CallDispatchOutcome::from_handled_target(self.codegen_transmute_intrinsic(
                args,
                destination,
                target,
            ));
        }
        if method == "copy_nonoverlapping" {
            debug!("AY codegen: handling copy_nonoverlapping");
            if args.len() >= 3 {
                self.codegen_copy_nonoverlapping(&args[0], &args[1], &args[2], self.body.span);
                return CallDispatchOutcome::from_handled_target(target);
            }
            // Part of #3742 D3: recognized but malformed — record fallback.
            self.ctx.unsupported_with_fallback(
                "copy_nonoverlapping",
                format!("expected >= 3 args, got {}", args.len()),
            );
            return CallDispatchOutcome::from_handled_target(target);
        }
        if method == "copy"
            && (fn_name.contains("intrinsics::copy") || fn_name.contains("ptr::copy"))
        {
            debug!("AY codegen: handling copy");
            if args.len() >= 3 {
                self.codegen_copy(&args[0], &args[1], &args[2], self.body.span);
                return CallDispatchOutcome::from_handled_target(target);
            }
            // Part of #3742 D3: recognized but malformed — record fallback.
            self.ctx.unsupported_with_fallback(
                "copy",
                format!("expected >= 3 args, got {}", args.len()),
            );
            return CallDispatchOutcome::from_handled_target(target);
        }
        if method == "write_bytes" {
            debug!("AY codegen: handling write_bytes");
            if args.len() >= 3 {
                self.codegen_write_bytes(&args[0], &args[1], &args[2], self.body.span);
                return CallDispatchOutcome::from_handled_target(target);
            }
            // Part of #3742 D3: recognized but malformed — record fallback.
            self.ctx.unsupported_with_fallback(
                "write_bytes",
                format!("expected >= 3 args, got {}", args.len()),
            );
            return CallDispatchOutcome::from_handled_target(target);
        }
        // Part of #3477: volatile intrinsics — BMC parity with CHC encoding.
        // Volatile semantics only prevent compiler reordering/elision. In the SMT
        // memory array model there is no optimization pass, so volatile_load/store
        // are semantically identical to atomic_load/store.
        if method == "volatile_load"
            || method == "unaligned_volatile_load"
            // #3728: core::ptr::read_volatile wraps intrinsics::volatile_load.
            // If MIR doesn't inline, callee path ends with "read_volatile".
            || (method == "read_volatile" && fn_name.contains("core::ptr::"))
        {
            debug!("AY codegen: handling {} (memory read)", method);
            // `volatile_load` requires `src` aligned (UB otherwise); the
            // `unaligned_volatile_load` variant is exempt by definition.
            // Without this obligation a misaligned load verified SUCCESSFUL
            // (tests/expected/intrinsics/volatile_load/unaligned).
            if method != "unaligned_volatile_load"
                && let Some(ptr) = args.first()
            {
                self.emit_intrinsic_alignment_check(ptr, "src");
            }
            return CallDispatchOutcome::from_handled_target(self.codegen_atomic_load(
                args,
                destination,
                target,
            ));
        }
        if method == "volatile_store"
            // #3728: symmetric with read_volatile above.
            || (method == "write_volatile" && fn_name.contains("core::ptr::"))
        {
            debug!("AY codegen: handling volatile_store (memory write)");
            // Symmetric with the load: `dst` must be properly aligned.
            if let Some(ptr) = args.first() {
                self.emit_intrinsic_alignment_check(ptr, "dst");
            }
            return CallDispatchOutcome::from_handled_target(
                self.codegen_atomic_store(args, target),
            );
        }
        // Volatile copy variants delegate to the non-volatile copy implementations.
        if method == "volatile_copy_nonoverlapping_memory" {
            debug!("AY codegen: handling volatile_copy_nonoverlapping_memory");
            if args.len() >= 3 {
                self.codegen_copy_nonoverlapping(&args[0], &args[1], &args[2], self.body.span);
                return CallDispatchOutcome::from_handled_target(target);
            }
            // Part of #3742 D3: recognized but malformed — record fallback.
            self.ctx.unsupported_with_fallback(
                "volatile_copy_nonoverlapping_memory",
                format!("expected >= 3 args, got {}", args.len()),
            );
            return CallDispatchOutcome::from_handled_target(target);
        }
        if method == "volatile_copy_memory" {
            debug!("AY codegen: handling volatile_copy_memory");
            if args.len() >= 3 {
                self.codegen_copy(&args[0], &args[1], &args[2], self.body.span);
                return CallDispatchOutcome::from_handled_target(target);
            }
            // Part of #3742 D3: recognized but malformed — record fallback.
            self.ctx.unsupported_with_fallback(
                "volatile_copy_memory",
                format!("expected >= 3 args, got {}", args.len()),
            );
            return CallDispatchOutcome::from_handled_target(target);
        }
        // Part of #3477: typed_swap_nonoverlapping — BMC parity with CHC encoding.
        // Models as: old_x = *x; old_y = *y; *x = old_y; *y = old_x
        // Part of #3742 D4: consume codegen_typed_swap failure at the family
        // boundary — do not forward None as "no memory intrinsic matched".
        if method == "typed_swap_nonoverlapping" {
            debug!("AY codegen: handling typed_swap_nonoverlapping");
            let result = self.codegen_typed_swap(args, target).or_else(|| {
                self.ctx
                    .unsupported_with_fallback("typed_swap_nonoverlapping", "translation failed");
                target
            });
            return CallDispatchOutcome::from_handled_target(result);
        }
        // std::mem::swap also resolves to typed_swap_nonoverlapping in MIR
        if method == "swap" && (fn_name.contains("core::mem::") || fn_name.contains("std::mem::")) {
            debug!("AY codegen: handling std::mem::swap (as typed_swap)");
            let result = self.codegen_typed_swap(args, target).or_else(|| {
                self.ctx.unsupported_with_fallback("std::mem::swap", "translation failed");
                target
            });
            return CallDispatchOutcome::from_handled_target(result);
        }
        if method == "offset_from_unsigned" {
            debug!("AY codegen: handling pointer offset_from_unsigned");
            return CallDispatchOutcome::from_handled_target(self.codegen_ptr_offset_from(
                args,
                destination,
                target,
                true,
            ));
        }
        if method == "offset_from" {
            debug!("AY codegen: handling pointer offset_from");
            return CallDispatchOutcome::from_handled_target(self.codegen_ptr_offset_from(
                args,
                destination,
                target,
                false,
            ));
        }
        if method == "arith_offset" {
            debug!("AY codegen: handling arith_offset (wrapping)");
            return CallDispatchOutcome::from_handled_target(
                self.codegen_arith_offset_intrinsic(args, destination, target),
            );
        }
        if method == "offset" {
            debug!("AY codegen: handling pointer offset");
            return CallDispatchOutcome::from_handled_target(self.codegen_ptr_offset_intrinsic(
                args,
                destination,
                target,
            ));
        }
        CallDispatchOutcome::Miss
    }
}
