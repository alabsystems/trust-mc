// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Atomic intrinsic dispatch: load, store, xchg, cxchg, fetch_*, fence.

use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use tracing::debug;

use super::extract_method_name;
use crate::codegen_ay::statement::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Atomic intrinsics: load, store, xchg, cxchg, fetch_*, fence.
    pub(in crate::codegen_ay::statement) fn dispatch_atomics(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Quick prefix check to avoid scanning for non-atomic names
        if !fn_name.contains("atomic") {
            return None;
        }
        let method = extract_method_name(fn_name)?;

        if method.starts_with("atomic_load") {
            debug!("AY codegen: handling atomic_load (memory read)");
            return self.codegen_atomic_load(args, destination, target);
        }
        if method.starts_with("atomic_store") {
            debug!("AY codegen: handling atomic_store (memory write)");
            return self.codegen_atomic_store(args, target);
        }
        if method.starts_with("atomic_xchg") {
            debug!("AY codegen: handling atomic_xchg (exchange)");
            return self.codegen_atomic_exchange(args, destination, target);
        }
        if method.starts_with("atomic_cxchg") || method.starts_with("atomic_cxchgweak") {
            debug!("AY codegen: handling atomic_cxchg (compare-exchange)");
            return self.codegen_atomic_cxchg(args, destination, target);
        }
        if method.starts_with("atomic_xadd") || method.starts_with("atomic_uadd") {
            debug!("AY codegen: handling atomic_xadd/atomic_uadd (fetch_add)");
            return self.codegen_atomic_fetch_binop(args, destination, target, BinOp::Add);
        }
        if method.starts_with("atomic_xsub") || method.starts_with("atomic_usub") {
            debug!("AY codegen: handling atomic_xsub/atomic_usub (fetch_sub)");
            return self.codegen_atomic_fetch_binop(args, destination, target, BinOp::Sub);
        }
        if method.starts_with("atomic_and") {
            debug!("AY codegen: handling atomic_and (fetch_and)");
            return self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitAnd);
        }
        if method.starts_with("atomic_or") {
            debug!("AY codegen: handling atomic_or (fetch_or)");
            return self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitOr);
        }
        if method.starts_with("atomic_xor") {
            debug!("AY codegen: handling atomic_xor (fetch_xor)");
            return self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitXor);
        }
        if method.starts_with("atomic_nand") {
            debug!("AY codegen: handling atomic_nand (fetch_nand)");
            return self.codegen_atomic_fetch_nand(args, destination, target);
        }
        // Signed min/max - check before unsigned variants (prefix overlap)
        if method.starts_with("atomic_max") && !method.starts_with("atomic_umax") {
            debug!("AY codegen: handling atomic_max (signed fetch_max)");
            return self.codegen_atomic_fetch_minmax(args, destination, target, true, true);
        }
        if method.starts_with("atomic_min") && !method.starts_with("atomic_umin") {
            debug!("AY codegen: handling atomic_min (signed fetch_min)");
            return self.codegen_atomic_fetch_minmax(args, destination, target, false, true);
        }
        if method.starts_with("atomic_umax") {
            debug!("AY codegen: handling atomic_umax (unsigned fetch_max)");
            return self.codegen_atomic_fetch_minmax(args, destination, target, true, false);
        }
        if method.starts_with("atomic_umin") {
            debug!("AY codegen: handling atomic_umin (unsigned fetch_min)");
            return self.codegen_atomic_fetch_minmax(args, destination, target, false, false);
        }
        if method.starts_with("atomic_fence") || method.starts_with("atomic_singlethreadfence") {
            debug!("AY codegen: handling atomic fence (no-op for verification)");
            return target;
        }

        // --- Stable API method names (std::sync::atomic::{AtomicBool,...}) ---
        // When the full path is under sync::atomic, match stable method names
        // to the same handlers as raw intrinsics. Argument layout is compatible:
        // (&self, [val,] ordering...) vs (ptr, [val]) — same first N args,
        // extra ordering args ignored by handlers.
        // Excludes fetch_update (closure).
        // Part of #3452: Atomic/Stable dispatch gap.
        if fn_name.contains("sync::atomic") {
            return match method {
                "load" => {
                    debug!("AY codegen: handling stable atomic load");
                    self.codegen_atomic_load(args, destination, target)
                }
                "store" => {
                    debug!("AY codegen: handling stable atomic store");
                    self.codegen_atomic_store(args, target)
                }
                "swap" => {
                    debug!("AY codegen: handling stable atomic swap (exchange)");
                    self.codegen_atomic_exchange(args, destination, target)
                }
                "fetch_add" | "fetch_byte_add" => {
                    debug!("AY codegen: handling stable atomic fetch_add");
                    self.codegen_atomic_fetch_binop(args, destination, target, BinOp::Add)
                }
                "fetch_sub" | "fetch_byte_sub" => {
                    debug!("AY codegen: handling stable atomic fetch_sub");
                    self.codegen_atomic_fetch_binop(args, destination, target, BinOp::Sub)
                }
                "fetch_and" => {
                    debug!("AY codegen: handling stable atomic fetch_and");
                    self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitAnd)
                }
                "fetch_or" => {
                    debug!("AY codegen: handling stable atomic fetch_or");
                    self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitOr)
                }
                "fetch_xor" => {
                    debug!("AY codegen: handling stable atomic fetch_xor");
                    self.codegen_atomic_fetch_binop(args, destination, target, BinOp::BitXor)
                }
                "fetch_nand" => {
                    debug!("AY codegen: handling stable atomic fetch_nand");
                    self.codegen_atomic_fetch_nand(args, destination, target)
                }
                "fetch_max" => {
                    debug!("AY codegen: handling stable atomic fetch_max");
                    self.codegen_atomic_fetch_minmax(args, destination, target, true, true)
                }
                "fetch_min" => {
                    debug!("AY codegen: handling stable atomic fetch_min");
                    self.codegen_atomic_fetch_minmax(args, destination, target, false, true)
                }
                "fence" => {
                    debug!("AY codegen: handling stable atomic fence (no-op)");
                    target
                }
                // Stable compare_exchange returns Result<T, T> — different field
                // layout from raw cxchg's (T, bool). Part of #3452.
                "compare_exchange" | "compare_exchange_weak" => {
                    debug!("AY codegen: handling stable atomic compare_exchange");
                    self.codegen_atomic_compare_exchange(args, destination, target)
                }
                // Stable constructor: Atomic*::new(val). repr(transparent) — same
                // layout as inner value. Part of #3452, #3487.
                "new" => {
                    debug!("AY codegen: handling stable atomic new (constructor)");
                    self.codegen_atomic_new(args, destination, target)
                }
                _ => None,
            };
        }
        None
    }
}
