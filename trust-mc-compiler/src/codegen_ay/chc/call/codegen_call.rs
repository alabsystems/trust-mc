// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Call terminator dispatch spine for CHC code generation.
//!
//! Dispatches `TerminatorKind::Call` to specialized handler families:
//! - `codegen_call_kani.rs`: Kani hooks (assert, assume, cover) and models (any)
//! - `codegen_call_numeric.rs`: BigInt / BigRational stubs
//! - `codegen_call_collections.rs`: HashMap, HashSet, BTreeSet, iterators
//! - `codegen_call_alloc.rs`: Heap alloc/dealloc/realloc
//! - `codegen_call_misc.rs`: Pointer/NonZero utility, primitive cmp, unhandled
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

#[path = "codegen_call_c_body.rs"]
mod codegen_call_c_body;
#[path = "codegen_call_foreign.rs"]
mod codegen_call_foreign;
#[path = "codegen_call_libc_mem.rs"]
mod codegen_call_libc_mem;
#[path = "codegen_call_posix_memalign.rs"]
mod codegen_call_posix_memalign;
#[path = "codegen_call_struct_map_accessor.rs"]
mod codegen_call_struct_map_accessor;
#[path = "codegen_call_sysconf.rs"]
pub(in crate::codegen_ay) mod codegen_call_sysconf;

use self::codegen_call_c_body::CallDispatchCBody;
use self::codegen_call_foreign::CallDispatchForeign;
use self::codegen_call_libc_mem::CallDispatchLibcMem;
use self::codegen_call_posix_memalign::CallDispatchPosixMemalign;
use self::codegen_call_struct_map_accessor::CallDispatchStructMapAccessor;
use self::codegen_call_sysconf::CallDispatchSysconf;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_array_solver_shadow::CallDispatchArraySolverShadow;
use super::codegen_call_atomic::CallDispatchAtomic;
use super::codegen_call_block_on::CallDispatchBlockOn;
use super::codegen_call_catch_unwind::CallDispatchCatchUnwind;
use super::codegen_call_closure::CallDispatchClosure;
use super::codegen_call_cmp::CallCmp;
use super::codegen_call_cmp_string::CallCmpString;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_coroutine::CallDispatchCoroutine;
use super::codegen_call_dispatch_collections::CallDispatchCollections;
use super::codegen_call_dispatch_kani::CallDispatchKani;
use super::codegen_call_dispatch_misc::CallDispatchMisc;
use super::codegen_call_dispatch_option_ptr::CallDispatchOptionPtr;
use super::codegen_call_dispatch_overapprox::CallDispatchOverapprox;
use super::codegen_call_fn_inline::CallDispatchFnInline;
use super::codegen_call_fn_ptr::CallDispatchFnPtr;
use super::codegen_call_iter_collect_method::CallDispatchIterCollectMethod;
use super::codegen_call_kani_model::CallKaniModel;
use super::codegen_call_simd::CallDispatchSimd;
use super::codegen_call_struct_clone::CallDispatchStructClone;
use super::codegen_call_struct_map_constructor::CallDispatchStructMapConstructor;
use super::codegen_call_struct_method_passthrough::CallDispatchStructMethodPassthrough;
use super::codegen_call_struct_vec_accessor::CallDispatchStructVecAccessor;
use super::codegen_call_struct_vec_constructor::CallDispatchStructVecConstructor;
use super::codegen_call_vec_builder::CallDispatchVecBuilder;
use super::codegen_call_virtual::CallDispatchVirtual;
use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_rules::CodegenRules;
use super::dispatch_helpers::is_pthread_noop_foreign_call;
use super::{ChcCtx, RelationApp, Rule, RuleBody};
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
#[allow(unused_imports)]
use rustc_public::CrateDef as _;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};
use trust_mc_core::violation::PropertyKind;

/// A diverging (`-> !`) callee that is a KNOWN guaranteed panic: reaching it is
/// a genuine failure, not an encoder give-up. Used to emit error() without a
/// `diverging_call_drop` taint so the CTREX certifies as Genuine. The type-valid
/// case of the assert_* intrinsics returns normally (target=Some) and never
/// reaches the diverging-call handler, so matching here is exact.
pub(in crate::codegen_ay::chc::call) fn is_known_diverging_panic_intrinsic(path: &str) -> bool {
    // Match the real core/std items exactly (generic arguments stripped). A
    // name-suffix match certified a user function such as `user::intrinsics::abort`
    // as a Genuine panic, dropping its diverging_call_drop taint.
    let path = path.split_once("::<").map_or(path, |(item, _)| item);
    if path == "std::process::abort" {
        return true;
    }
    let Some(name) =
        path.strip_prefix("core::intrinsics::").or_else(|| path.strip_prefix("std::intrinsics::"))
    else {
        return false;
    };
    matches!(
        name,
        "abort"
            | "assert_zero_valid"
            | "assert_mem_uninitialized_valid"
            | "assert_uninit_valid"
            | "assert_inhabited"
    )
}

/// Extension trait for the call terminator dispatch spine on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallTerminator {
    /// Handles `TerminatorKind::Call` in CHC transition rule generation.
    ///
    /// Dispatches to specialized handlers in call-family files in priority order.
    /// Returns `true` if any dispatcher handled the call (caller should suppress
    /// unwind edge — dispatched calls fully model call semantics and cannot unwind).
    fn codegen_call_terminator(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallTerminator for ChcCtx<'tcx, 'body> {
    fn codegen_call_terminator(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        // FC-06: stubs, models and intrinsics write through pointer arguments
        // without a checked store path; check those writes against the frame.
        self.modifies_frame_call_check(dcx);
        self.subslice_consumer_fail_closed(dcx);
        self.pointer_move_fail_closed(dcx);
        if self.try_dispatch_call_kani(dcx) {
            return true;
        }
        // The unwinding check below reads the call's ARGUMENTS, as they were
        // before the call. A handler that moves a flattened argument (the
        // iterators `Iterator::eq` consumes) sets that local's slots to the
        // moved-out placeholder in `flattened_field_env`
        // (`invalidate_moved_fn_inline_args`), and the check read them after
        // it: the receiver's remaining length was the placeholder's 0, which
        // discharged Kani's unwinding assertion
        // (`model_call_unwind_iter_eq_dual.rs::z5_eq_slice_other_u3_bug`,
        // `model_call_unwind_dual.rs::u5_iter_eq_u2_bug`: clean proofs once
        // main's placeholder bound every slot, where Kani fails).
        let pre_call_env = self.encode.flattened_field_env.clone();
        // Saved and restored: a dispatcher may dispatch a nested call through
        // this spine, and its outcome must not answer for the outer call.
        let outer = std::mem::replace(&mut self.call_replays_body, false);
        let handled = self.codegen_call_terminator_after_kani(dcx);
        let replayed = std::mem::replace(&mut self.call_replays_body, outer);
        if !replayed {
            let post_call_env =
                std::mem::replace(&mut self.encode.flattened_field_env, pre_call_env);
            self.model_call_unwinding_check(dcx);
            self.encode.flattened_field_env = post_call_env;
        }
        handled
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The dispatch spine after the Kani-function dispatcher
    /// ([`CallTerminator::codegen_call_terminator`]).
    fn codegen_call_terminator_after_kani(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        #[cfg(all(trust_toolchain, version("1.101")))]
        if self.try_native_box_into_raw(dcx) {
            return true;
        }
        #[cfg(all(trust_toolchain, version("1.101")))]
        if self.try_native_maybe_unsafe_access(dcx) {
            return true;
        }
        #[cfg(all(trust_toolchain, version("1.101")))]
        if self.try_native_maybe_uninit_write(dcx) || self.try_native_initialized_handoff(dcx) {
            return true;
        }
        if self.try_native_box_new_uninit(dcx) {
            return true;
        }
        #[cfg(all(trust_toolchain, version("1.101")))]
        self.book_native_maybe_user_callee(dcx);
        if super::inline_str_chars::try_codegen_str_chars(self, dcx)
            || super::inline_str_chars::try_codegen_chars_next(self, dcx)
            || self.try_codegen_native_iterator_size_hint(dcx)
        {
            return true;
        }
        // A comparison whose `==` or order is not its encodings' comparison
        // (a float, a reference or a hand-written `PartialEq` in it) is
        // decided before any handler that compares encodings can claim it
        // (`codegen_call_cmp_semantic.rs`).
        if self.try_dispatch_call_unfaithful_comparison(dcx) {
            return true;
        }
        // Coroutine-owned allocation elisions must run before collection/alloc
        // dispatch so BoxNew does not materialize assertion-irrelevant
        // Pin<Box<Coroutine>> heap arrays.
        if self.try_dispatch_call_coroutine_pre_misc(dcx) {
            return true;
        }

        if self.try_dispatch_call_numeric_collections(dcx) {
            return true;
        }

        if self.try_dispatch_call_option_pointer(dcx) {
            return true;
        }

        if self.try_dispatch_call_overapprox(dcx) {
            return true;
        }

        // Part of #3348: Struct-level Clone::clone for structs with collection fields.
        if self.try_dispatch_call_struct_clone(dcx) {
            return true;
        }

        if self.try_dispatch_call_fixed_unit_array_partial_eq(dcx) {
            return true;
        }

        if self.try_dispatch_call_misc(dcx) {
            return true;
        }

        // Direct libc environment query: no memory side effects, nondet return.
        // Must run before fn_inline/foreign fallback so direct `libc::sysconf`
        // calls do not become undefined-foreign error rules.
        if self.try_dispatch_call_sysconf(dcx) {
            return true;
        }

        if self.try_dispatch_call_closure(dcx) {
            self.call_replays_body = true;
            return true;
        }

        // Part of #3159: Virtual call dispatch (dyn Trait method resolution).
        // Detects InstanceKind::Virtual and devirtualizes to the concrete
        // implementation when there is exactly one reachable impl.
        if self.try_dispatch_call_virtual(dcx) {
            self.call_replays_body = true;
            return true;
        }

        // Part of #3186: pow/wrapping_pow dispatch (before fn_inline).
        // These methods use exponentiation-by-squaring loops in MIR. fn_inline
        // may inline the loop body, producing CHC rules the solver can't handle.
        // Short-circuit with direct encoding: constant-fold or base-2 shift.
        if self.try_dispatch_call_pow(dcx) {
            return true;
        }

        // Part of #3186: div_euclid/rem_euclid dispatch (before fn_inline).
        // Euclidean division/remainder have branching MIR bodies that fn_inline
        // expands into complex CHC rules. Encode directly as ite-guarded
        // bvsdiv/bvsrem (signed) or bvudiv/bvurem (unsigned).
        if self.try_dispatch_call_euclid(dcx) {
            return true;
        }

        // Part of #3293: wrapping_abs/wrapping_neg dispatch (before fn_inline).
        // wrapping_abs has a branching MIR body calling wrapping_neg internally.
        // Without this stub, signed div_euclid/rem_euclid (which call wrapping_abs
        // via MIR inlining) produce unresolvable constraints → CTREX.
        if self.try_dispatch_call_wrapping_abs(dcx) {
            return true;
        }

        // Part of #3300: overflowing_add_signed dispatch (before fn_inline).
        // `ptr.offset()` is inlined by the compiler into calls to
        // `overflowing_add_signed` (not lowered to `BinOp::Offset`).
        // Must be handled before fn_inline to emit correct `(result, overflow)` tuple.
        if self.try_dispatch_call_overflowing_arith(dcx) {
            return true;
        }

        // Saturating arithmetic intrinsics are compiler builtins or thin
        // wrappers. Encode them directly before fn_inline can leave the
        // destination unconstrained.
        if self.try_dispatch_call_saturating_arith(dcx) {
            return true;
        }

        // Part of #3323/#3464: Bit-manipulation and identity intrinsics
        // (black_box, bswap/swap_bytes, bitreverse/reverse_bits, ctlz/cttz,
        // ctpop, rotates, funnel shifts). These are compiler builtins or thin
        // wrappers around builtins; intercept before fn_inline so they do not
        // fall into unknown/unhandled dispatch paths.
        if self.try_dispatch_call_bit_intrinsic(dcx) {
            return true;
        }

        // Part of #3373: Math intrinsic constant folding (before fn_inline).
        // f32/f64 math intrinsics (floor, ceil, round, trunc, sqrt, sin, cos, etc.)
        // are compiler builtins without MIR bodies — fn_inline cannot handle them.
        // Constant-fold when arguments are compile-time constants; otherwise
        // sound over-approximation (destination unconstrained).
        if self.try_dispatch_call_math_intrinsic(dcx) {
            return true;
        }

        // Part of #3435: Atomic intrinsic dispatch (before fn_inline).
        // Atomic intrinsics (atomic_load, atomic_store, atomic_xchg, etc.) are
        // compiler builtins without MIR bodies — fn_inline cannot handle them.
        // Model as sequential operations (same as Kani — single-threaded verifier).
        if self.try_dispatch_call_atomic(dcx) {
            return true;
        }

        // Part of #3441: SIMD intrinsic dispatch (before fn_inline).
        // SIMD intrinsics (simd_add, simd_and, simd_eq, etc.) are compiler
        // builtins without MIR bodies — fn_inline cannot handle them.
        // Encode as element-wise BV operations on array state variables.
        if self.try_dispatch_call_simd(dcx) {
            return true;
        }

        // Part of #3792: SIMD library operations (from_array, to_array, as_array,
        // splat, resize). After transparent type unwrapping, Simd<T,N> and [T;N]
        // have the same Array sort. Must run before fn_inline to avoid Bool-sorted
        // results for Array-sorted destinations.
        if super::codegen_call_simd_lib::try_dispatch_simd_lib_call(self, dcx) {
            return true;
        }

        // Part of #3464: Miscellaneous compiler intrinsics (before fn_inline).
        // typed_swap_nonoverlapping has a default MIR body that rustc expands into
        // 38+ basic blocks of byte-level operations (swap_nonoverlapping_bytes,
        // slice_from_raw_parts_mut, size_of_val_raw). fn_inline would inline this
        // expanded body, producing CHC rules the solver can't handle.
        // Short-circuit with direct encoding: cross-assignment for swap, value
        // propagation for volatile load/store. Also catches forget, arith_offset,
        // and other intrinsics that lack MIR bodies.
        if self.try_dispatch_call_misc_intrinsic(dcx) {
            return true;
        }

        // Part of #3348 Direction 2: Struct-map constructor bridge.
        // Intercepts associated constructors that build structs with embedded map
        // fields (e.g., `MyStruct::new(default)`) and registers embedded-map aux
        // ownership for the destination local. Must run before fn_inline so the
        // aux bridge is populated even when fn_inline could handle the constructor.
        if self.try_dispatch_call_struct_map_constructor(dcx) {
            return true;
        }

        // Part of #3348: struct-Vec constructor bridge.
        // Intercepts constructors for structs with embedded Vec fields
        // (e.g., `CnfClause::unit(lit)` → `Self(vec![lit])`). fn_inline bails
        // on nested Box::new/exchange_malloc, causing P_inf_* fallback.
        // This bridge constrains the flattened Vec state (ptr, len, cap, data)
        // directly, eliminating the need for fn_inline.
        if self.try_dispatch_call_struct_vec_constructor(dcx) {
            return true;
        }

        // Part of #3348: Vec-building function call dispatch.
        // Detects functions whose body constructs a Vec via for-loop-push
        // patterns (e.g., `for i in 0..n { vec.push(f(i)) }`) and emits
        // length/data-constrained Vec results instead of unconstrained fallback.
        // Must run before fn_inline so builder patterns like `Bits::from_u64`
        // are not flattened into opaque projected writes before we can recover
        // the backing-array semantics.
        if self.try_dispatch_call_vec_builder(dcx) {
            return true;
        }

        // Part of #3711: Array IntoIter identity calls.
        // `IntoIter::unsize_mut` and `ManuallyDrop::deref_mut` are transparent
        // reference-forwarding/unwrapping operations on the array iterator path.
        // Without explicit dispatch, these fall through to unconstrained fallback
        // because fn_inline bails on their MIR bodies (projected writes through
        // generic references). Model as identity: dest = arg0.
        if self.try_dispatch_array_iter_identity_call(dcx) {
            return true;
        }

        // Part of #3807: `Pin::new_unchecked` and `Pin::as_mut` are transparent
        // wrapper-construction/forwarding calls. The generic fn-inline walker
        // treats `Rvalue::Ref` as referent-transparent, which collapses
        // `Pin<&mut Coroutine>` to the coroutine value itself and causes
        // result/destination sort mismatches in async `block_on` paths.
        if self.try_dispatch_pin_identity_call(dcx) {
            return true;
        }

        // Part of #3807, #4181: Coroutine body call dispatch.
        // Coroutine state-machine closures have `Pin<&mut CoroutineType>` as self
        // arg. Tries precise Yielded(y) encoding first. If that fails, tries
        // fn_inline as fallback (#3807 Phase 1+2). Sound over-approximation
        // is the last resort.
        if self.try_dispatch_call_coroutine(dcx) {
            return true;
        }

        // Part of #3955: `block_on` is a busy-poll loop around `Future::poll`.
        // Rewrite the Pending backedge away and inline the single-poll Ready path
        // before generic fn_inline sees the unbounded loop.
        if self.try_dispatch_call_block_on(dcx) {
            return true;
        }

        // Part of #4072: `[T]::contains` disjunction before fn_inline.
        // `contains` for non-u8 types (e.g., `[char]::contains`) compiles to
        // `iter().any(|y| *x == *y)` in MIR. fn_inline would inline this into a
        // loop-based iterator pattern (ChunksExact) that PDR cannot solve.
        // Intercept here and emit a finite disjunction over array elements.
        if self.try_dispatch_call_slice_contains_pre_inline(dcx) {
            return true;
        }
        // `Range`/`RangeInclusive::contains` value lowering before fn_inline.
        // The MIR inline pass preserves these calls as a handler boundary
        // (`is_handler_backed_range_contains`), but the CHC `range_contains`
        // handler only ran from the tail catch-all — AFTER fn_inline had already
        // claimed the call and bound its result to a fresh symbolic bool when the
        // `RangeBounds::contains` body exceeded the inline block budget. Running
        // it here makes the preserved boundary reach its handler; the handler
        // returns false (falling through unchanged) when it cannot resolve the
        // range bounds.
        if self.try_dispatch_call_range_contains_pre_inline(dcx) {
            return true;
        }
        // Part of #4050: ArraySolver shadow SMT array dispatch (before fn_inline).
        if self.try_dispatch_call_array_solver_shadow(dcx) {
            return true;
        }

        // Part of #3348: BTreeMap/HashMap accessor and clone-store method dispatch
        // for structs. Run before fn_inline so high-level map get/store semantics
        // are encoded directly instead of expanding BTreeMap internals and drop.
        if self.try_dispatch_call_struct_map_accessor(dcx) {
            return true;
        }

        // Part of #4086/#4203: Pre-inline CMP + flattened tuple PartialEq dispatch.
        if self.try_dispatch_call_cmp_pre_inline(dcx) {
            return true;
        }
        if self.try_dispatch_call_flattened_partial_eq(dcx) {
            return true;
        }

        // Part of #3187/#4073: General-purpose fn inlining + catch_unwind wrapper.
        // Resolves callee to concrete Instance, inlines small function bodies.
        if self.try_dispatch_call_catch_unwind(dcx) {
            self.call_replays_body = true;
            return true;
        }

        // fn-inline sets `call_replays_body` itself: a known-call fast path is
        // a model.
        if self.try_dispatch_call_fn_inline(dcx) {
            return true;
        }

        // Part of #3348: Vec accessor/mutator method dispatch for structs.
        // When a method on a struct with Vec fields performs a simple Vec
        // Index or IndexMut (e.g., `fn get(&self, i) -> T { self.v[i] }`),
        // fn_inline bails because of projected writes and nested collection
        // calls. This dispatcher scans the callee body for Vec access patterns
        // and emits select/store constraints on the caller's Vec state var.
        if self.try_dispatch_call_struct_vec_accessor(dcx) {
            return true;
        }

        // Part of #3348: Iter-map-collect method dispatch for structs with Vec.
        // When a method on a struct with Vec fields does
        // self.field.iter().[zip(other.field.iter())].map(closure).collect(),
        // fn_inline bails (body too complex). This dispatcher detects the
        // pattern, resolves the closure, and emits result Vec with:
        //   - Length preservation: result.len = source.len
        //   - Element-wise forall: idx < len → select(data, idx) = closure(...)
        // Handles Bits::and/or/xor/not and similar BV operation patterns.
        // NOTE: rustc may MIR-inline these methods, so individual iter/map/collect
        // calls appear in the harness body instead of the method call. This dispatcher
        // handles the non-inlined case; the existing iterator adapter infrastructure
        // handles the inlined case.
        if self.try_dispatch_call_iter_collect_method(dcx) {
            return true;
        }

        // Part of #3348: Conservative clone-based encoding for struct methods.
        // When a method on a struct with collection fields returns Self and
        // fn_inline can't handle it (complex nested calls), conservatively copy
        // all struct fields from receiver to destination. This preserves scalar
        // field values (e.g., default_val) that would otherwise be unconstrained,
        // fixing false CTREX in clone-mutate-return method patterns.
        if self.try_dispatch_call_struct_method_passthrough(dcx) {
            return true;
        }

        // Part of #1739: Function pointer call resolution.
        // When the func operand is FnPtr (indirect call through fn pointer),
        // scan the caller's MIR for ClosureFnPointer/ReifyFnPointer casts
        // to resolve the concrete callee and inline its body.
        // An INDIRECT call through a function pointer that reifies a FOREIGN
        // item is still a call to that C function — and `Instance::body()` is
        // `None` for a foreign item, so the inline path below cannot touch it.
        // When the user supplied its definition, encode it exactly as the
        // direct call is encoded; `ForeignItems/extern_fn_ptr.rs` asserts the
        // two agree, which is unprovable while one of them is unconstrained.
        if let Some(symbol) = self.fn_ptr_foreign_link_symbol(dcx)
            && crate::codegen_ay::foreign_defs::c_lib_defines(&symbol)
            && self.try_dispatch_call_c_body(dcx, &symbol)
        {
            return true;
        }

        if self.try_dispatch_call_fn_ptr(dcx) {
            self.call_replays_body = true;
            return true;
        }

        // An indirect call through a fn pointer that reifies a FOREIGN item no
        // `--c-lib` file defines. Kani fails it with "call to foreign "C"
        // function `f` is not currently supported by Kani". `is_foreign_call`
        // below only sees `FnDef` operands, so this call used to reach the
        // tail's anonymous havoc (`call_dispatch_fallback_prebuilt`, "fell
        // through all dispatch stages"), which havocked the result and let a
        // dead-path call fail the harness on a downstream assertion. Mirror the
        // BMC lane (statement/terminator.rs): Kani's check, gated on reaching
        // the call, with no successor edge, never certified Genuine.
        if self.undefined_function_checks
            && let Some(symbol) = self.fn_ptr_foreign_link_symbol(dcx)
            && !crate::codegen_ay::foreign_defs::c_lib_defines(&symbol)
        {
            super::codegen_call_coerce::emit_kani_unsupported_check(
                self,
                dcx.from_app,
                dcx.stmt_constraints,
                dcx.bb_idx,
                super::codegen_call_coerce::kani_unsupported_message(&format!(
                    "call to foreign \"C\" function `{symbol}`"
                )),
            );
            return true;
        }

        // Part of #3736: direct `libc::posix_memalign` FFI model.
        if self.is_foreign_call(dcx.func) && self.try_dispatch_call_posix_memalign(dcx) {
            return true;
        }

        // Part of #3175: direct `libc::{malloc, free, memset}` FFI models. Each
        // routes to the encoder's existing heap model; a shape the model cannot
        // encode exactly returns false and keeps the fail-closed error() below.
        if self.is_foreign_call(dcx.func) && self.try_dispatch_call_libc_mem(dcx) {
            return true;
        }

        // Part of #4067: pthread_* foreign calls are no-ops in single-threaded
        // CHC verification. Kani's MIR InlinePass expands drop_in_place::<Mutex<T>>
        // into the harness body, inserting direct pthread_mutex_{trylock,unlock,init,
        // destroy} calls that bypass the generic_preroutes Mutex drop handler.
        // Model as goto(successor) — sound because Mutex is transparent and these
        // platform sync primitives have no semantic effect.
        if self.is_foreign_call(dcx.func) {
            let callee_path =
                dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
            if callee_path.as_deref().is_some_and(is_pthread_noop_foreign_call) {
                if let Some(target) = dcx.target {
                    let new_output_args = self.build_output_args(dcx.modified_locals, &[]);
                    self.emit_goto_rule_extra(
                        dcx.from_app,
                        *target,
                        &new_output_args,
                        dcx.stmt_constraints,
                        None,
                    );
                }
                return true;
            }
        }

        // Part of #3175: `__CPROVER_havoc_object(p)` is CBMC's havoc primitive
        // that Kani emits for c-ffi tests. Its semantics are identical to
        // `kani::write_any_slim(p)`: make the object `p` points to arbitrary.
        // Model it through the same havoc path rather than the undefined-foreign
        // error() below (which Kani does NOT emit here — the reference oracle is
        // Success). SOUND: havoc is the maximally-conservative over-approximation,
        // so it can never hide a bug (never a missed_bug). If the pointee does
        // not resolve, `try_emit_write_any_slim` returns false and we fall
        // through to the fail-closed error() emission below.
        if self.is_foreign_call(dcx.func) {
            let callee_path =
                dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
            if callee_path.as_deref().is_some_and(|p| p.contains("__CPROVER_havoc_object"))
                && self.try_emit_write_any_slim(dcx)
            {
                return true;
            }
        }

        // A foreign call whose definition the USER SUPPLIED (`-Z c-ffi
        // --c-lib`) is not an unknown-callee error: it is a call to some
        // concrete C function with this prototype. Model it with a sound effect
        // frame — fresh return, havoc of every location the callee could write
        // — instead of collapsing the harness at the call site. Declines (and
        // leaves the fail-closed error() below standing) for a symbol no
        // `--c-lib` file defines, which is what keeps
        // `ForeignItems/missing_fn_fail.rs` failing.
        if self.try_dispatch_call_foreign_model(dcx) {
            return true;
        }

        // Undefined foreign function calls (Part of #3175).
        // Foreign functions not claimed by any dispatcher above are unresolved
        // FFI calls. Emit error() — equivalent to Kani's assert(false) for
        // undefined extern functions — so the verifier produces CTREX if the
        // call is reachable.
        if self.undefined_function_checks && self.is_foreign_call(dcx.func) {
            warn!(
                callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
                bb_idx = dcx.bb_idx,
                "Undefined foreign function call — emitting error()"
            );
            let error_app = RelationApp::new("error", Vec::new());
            let body =
                RuleBody::from_base_and_extra(Some(dcx.from_app.clone()), dcx.stmt_constraints, []);
            self.vc.add_rule(Rule::new(body, error_app));
            return true;
        }

        // Step::forward/backward_unchecked, wrapping arithmetic, unhandled calls.
        // Part of #3470: Fallthrough returns false — caller preserves the unwind
        // edge for fail-closed soundness on unhandled calls.
        if dcx.target.is_some() {
            self.codegen_call_primitive_cmp(dcx);
        } else if let Some((kind, msg)) = self.definite_failure_diverging_call(dcx) {
            // PROVEN-failure diverging callee (`intrinsics::abort`, or an
            // `assert_*::<T>` whose `T` the conservative type-validity oracle
            // proves invalid). Reaching it is a genuine Kani failure gated on
            // block reachability — NOT an encoding artifact. Emit a per-property
            // `error_p{N}` head and DO NOT taint via `diverging_call_drop`.
            //
            // `cond = false` ⇒ the emitted rule is `from ∧ stmt_constraints →
            // error_p{N}` — the same reachability-gated shape the target!=None
            // assert-validity handler uses (misc_intrinsics.rs codegen_assert_validity).
            self.emit_error_rule_for_condition_with_kind(
                dcx.from_app,
                Expr::bool_const(false),
                dcx.stmt_constraints,
                dcx.bb_idx,
                kind,
                Some(msg),
            );
        } else {
            // Diverging call (target=None) not claimed by any dispatcher (#2587).
            // Conservative: emit error() rule so the verifier flags this path
            // if reachable. Without this, the path is silently pruned from
            // verification — unsound when the diverging callee is reachable.
            //
            // KNOWN always-diverging PANIC intrinsics (abort; the
            // assert_*_valid / assert_inhabited compiler intrinsics that the MIR
            // lowered to a guaranteed panic on this monomorphized type — the
            // type-VALID case returns normally with target=Some and never reaches
            // here) are GENUINE panics, not encoder give-ups. Emitting error() is
            // EXACT for them, so do not taint the CTREX with diverging_call_drop:
            // the failure then certifies as Genuine (parity for its oracle=fail
            // tests) instead of EncodingGap. SOUND: error() is fail-closed either
            // way — it never hides a bug; this only fixes the CTREX attribution,
            // not the verdict.
            let genuine_panic =
                dcx.callee_path.as_deref().is_some_and(is_known_diverging_panic_intrinsic);
            if !genuine_panic {
                self.diagnostics.diverging_call_drop.inc();
            }
            warn!(
                callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
                bb_idx = dcx.bb_idx,
                genuine_panic,
                "CHC diverging call (target=None) fell through all dispatchers — emitting error()"
            );
            let error_app = RelationApp::new("error", Vec::new());
            let body =
                RuleBody::from_base_and_extra(Some(dcx.from_app.clone()), dcx.stmt_constraints, []);
            self.vc.add_rule(Rule::new(body, error_app));
        }
        false
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Classify a diverging (target=None) callee as a *proven* verification
    /// failure, so its already-reachability-gated error rule can be credited as a
    /// genuine counterexample instead of a demoted `diverging_call_drop` artifact.
    ///
    /// Returns `Some((kind, message))` only for:
    /// - `core/std::intrinsics::abort` — reaching it is definitionally a Kani
    ///   verification failure.
    /// - `assert_inhabited` / `assert_zero_valid` / `assert_mem_uninitialized_valid`
    ///   whose single generic type argument the conservative rustc type-validity
    ///   oracle proves *definitely* violates the requirement.
    ///
    /// Returns `None` (→ keep the fail-closed `diverging_call_drop` taint) on
    /// anything unresolved, parametric / un-monomorphized, or merely satisfiable —
    /// exactly the conservatism that already governs the target!=None
    /// assert-validity handler (misc_intrinsics.rs `codegen_assert_validity`), whose
    /// oracle this reuses verbatim. Fail-closed: an unproven callee is never
    /// credited Genuine.
    fn definite_failure_diverging_call(
        &self,
        dcx: &DispatchCallContext<'_>,
    ) -> Option<(PropertyKind, String)> {
        let path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func))?;
        // Deliberately narrow: only the compiler intrinsic `abort`. `std::process::abort`
        // / `exit` are handled separately by the driver path classifier and must not be
        // perturbed here.
        if matches!(path.as_str(), "core::intrinsics::abort" | "std::intrinsics::abort") {
            return Some((PropertyKind::Panic, "abort() reached".to_string()));
        }
        // The intrinsic name alone is not authoritative: user crates may
        // legally define (for example) `intrinsics::assert_zero_valid<T>`.
        // Only rustc's core/std intrinsic namespace may discharge the unknown
        // diverging-call taint.
        let method = path
            .strip_prefix("core::intrinsics::")
            .or_else(|| path.strip_prefix("std::intrinsics::"))?;
        let requirement =
            crate::kani_middle::type_validity::validity_requirement_for_intrinsic(method)?;
        let func_ty = dcx.func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(_, substs)) = func_ty.kind() else {
            return None;
        };
        let ty = substs
            .0
            .iter()
            .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(*ty) } else { None })?;
        if matches!(ty.kind(), TyKind::Param(_)) {
            // Un-monomorphized — the validity query cannot answer; fail closed.
            return None;
        }
        if crate::kani_middle::type_validity::assert_requirement_definitely_violated(
            self.tcx,
            ty,
            requirement,
        ) {
            return Some((
                PropertyKind::UndefinedBehavior,
                format!("{method}: type-validity requirement violated (undefined behavior)"),
            ));
        }
        None
    }

    /// A sub-slice with a NONZERO start handed to a call that does not honour
    /// the start: fail closed.
    ///
    /// `&source[a..b]` is materialized with the start recorded in
    /// `subslice_offset`, and the element-access route applies it
    /// (`source.select(idx + offset)`), which is why `s[i]` is exact. Every
    /// OTHER consumer reads the backing array from index zero, so
    /// `s.first() == Some(&1)` and `a[1..3] == [1u8, 2]` verified SUCCESSFUL and
    /// `contains`, `split_first`, `split_last`, `rchunks`, `as_ptr` and
    /// `extend_from_slice` certified Genuine counterexamples for their safe twins
    /// (negative/subslice_offsets.rs, negative/subslice_producers.rs, main
    /// 31793ccc3).
    ///
    /// The allowlist is the routes that DO apply the offset. Everything else —
    /// a modelled slice method, a user function, an unmodelled callee — is
    /// tainted, so those harnesses report an uncertified counterexample or
    /// Unknown instead of a proof or a certificate.
    fn subslice_consumer_fail_closed(&mut self, dcx: &DispatchCallContext<'_>) {
        /// Callee paths whose element access goes through the offset-applying
        /// route, or which read no element at all.
        const HONOURS_SUBSLICE_OFFSET: &[&str] = &[
            "core::slice::index::<impl std::ops::Index<I> for [T]>::index",
            "core::slice::index::<impl std::ops::IndexMut<I> for [T]>::index_mut",
            "std::ops::Index::index",
            "std::ops::IndexMut::index_mut",
            "core::slice::<impl [T]>::len",
            "core::slice::<impl [T]>::is_empty",
            "core::str::<impl str>::len",
            "core::str::<impl str>::is_empty",
            "std::slice::<impl [T]>::len",
            "std::slice::<impl [T]>::is_empty",
        ];
        // The exempt paths are named in full. A `path.ends_with("::len")`
        // suffix test used to stand here, and it skipped the WHOLE taint — the
        // producer clause and every other argument of the call included — for
        // any callee whose path ends in `len`, which a user function or a trait
        // method called `len` satisfies (adversarial review of
        // m3/soundness-fixes-2, 2026-09-14, minor 1).
        if let Some(path) = dcx.callee_path.as_deref()
            && HONOURS_SUBSLICE_OFFSET.contains(&path)
        {
            return;
        }
        let shifted = dcx.args.iter().any(|arg| {
            let (Operand::Copy(p) | Operand::Move(p)) = arg else { return false };
            // Only a SLICE view. `subslice_offset` also accumulates raw-pointer
            // arithmetic (`p.add(k)`) and custom-DST tail reborrows, and those
            // routes read through the offset-applying address lane, so tainting
            // them would demote proofs for no soundness gain.
            let is_slice_ref = p.ty(self.body.locals()).ok().is_some_and(|ty| {
                matches!(
                    ty.kind(),
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                        if matches!(
                            pointee.kind(),
                            TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str)
                        )
                )
            });
            is_slice_ref
                && self
                    .ref_resolution
                    .subslice_offset
                    .get(&p.local)
                    .is_some_and(|off| Self::try_eval_const_bv(off) != Some(0))
        });
        if shifted {
            debug!(
                fn_name = %self.fn_name,
                callee = ?dcx.callee_path,
                "CHC: sub-slice with a nonzero start reaches a consumer that ignores it — fail closed"
            );
            self.record_sound_fallback_reason("subslice_start_ignored_by_consumer");
        }

        // The same defect from the PRODUCER side. These methods hand back a view
        // that does not begin at the source's index 0 — `split_first().1` is
        // `&a[1..]`, `rchunks(3).next()` is `&a[1..4]` — and the model gives the
        // view neither the shifted backing nor a recorded start, so a read at its
        // own index 0 returns the source's element 0:
        // `let (_f, rest) = a.split_first().unwrap(); assert!(rest[0] == 2)` and
        // the `split_last` and `rchunks` twins were certified FAILED
        // (negative/subslice_producers.rs, main 31793ccc3). No argument of theirs
        // carries a `subslice_offset`, so the consumer test above cannot see them.
        // Every slice producer whose returned view does NOT begin at the
        // source's index 0, or whose element route the model does not shift.
        // The list used to name six; `split_at`, `chunks`, `windows`,
        // `strip_prefix` and the rest hand back exactly the same kind of view
        // and were undefended (adversarial review, 2026-09-14, minor 1).
        const VIEW_OFFSET_UNMODELLED: &[&str] = &[
            "split_first",
            "split_last",
            "split_first_mut",
            "split_last_mut",
            "rchunks",
            "rchunks_mut",
            "rchunks_exact",
            "rchunks_exact_mut",
            "split_at",
            "split_at_mut",
            "split_at_unchecked",
            "split_at_mut_unchecked",
            "chunks",
            "chunks_mut",
            "chunks_exact",
            "chunks_exact_mut",
            "array_chunks",
            "array_windows",
            "windows",
            "strip_prefix",
            "strip_suffix",
            "rsplit",
            "rsplit_mut",
            "rsplitn",
            "rsplitn_mut",
            "splitn",
            "splitn_mut",
        ];
        if let Some(path) = dcx.callee_path.as_deref()
            && VIEW_OFFSET_UNMODELLED.contains(&Self::callee_leaf(path))
            && path.contains("slice")
        {
            debug!(
                fn_name = %self.fn_name,
                callee = path,
                "CHC: slice producer whose view offset is not modelled — fail closed"
            );
            self.record_sound_fallback_reason("slice_producer_view_offset_unmodelled");
        }
    }

    /// A call that MOVES a value out of one storage and another in, whose value
    /// type is a POINTER.
    ///
    /// `mem::swap` has an exact handler that exchanges the pointee bindings
    /// (`swap_pointee_bindings`). Its siblings have none: `mem::replace`,
    /// `mem::take`, `ptr::replace`, `Option::replace`, `Option::take`,
    /// `Option::insert` and `Option::get_or_insert*` are INLINED, and the
    /// inline walker knows nothing about pointer identity, so the bindings stay
    /// where they were and a later store through either name writes the wrong
    /// object: `let mut a = &mut x; let old = mem::replace(&mut a, &mut y);
    /// *old = 7; *a = 9; assert!(y == 2)` verified SUCCESSFUL and its safe twin
    /// `assert!(x == 7 && y == 9)` was FAILED [AY:CTREX_CAT:Genuine]
    /// (adversarial review of m3/soundness-fixes-2, 2026-09-14; pre-existing on
    /// main). The bindings of every storage the call can rebind are dropped and
    /// the harness fails closed.
    ///
    /// Only a value type that is ITSELF a pointer, or a shallow carrier of one
    /// (`Option<&mut T>`, `(&T, u8)`), arms the guard: `mem::replace(&mut v,
    /// Vec::new())` moves an owning container, whose buffer identity the model
    /// does not key on a points-at edge, and demoting it would cost proofs for
    /// no soundness gain.
    fn pointer_move_fail_closed(&mut self, dcx: &DispatchCallContext<'_>) {
        const POINTER_MOVING_LEAVES: &[&str] =
            &["replace", "take", "insert", "get_or_insert", "get_or_insert_with", "replace_with"];
        let Some(path) = dcx.callee_path.as_deref() else { return };
        // A resolved callee path carries its generic arguments
        // (`std::mem::replace::<&mut u8>`), so the leaf is what comes before
        // `::<` — taking the last `::` segment outright gives `<&mut u8>` and
        // matches nothing.
        let leaf = Self::callee_leaf(path);
        if !POINTER_MOVING_LEAVES.contains(&leaf) {
            return;
        }
        if !(path.contains("mem::")
            || path.contains("ptr::")
            || path.contains("Option")
            || path.contains("option::"))
        {
            return;
        }
        // The moved value's type: the destination for `replace` / `take`, and
        // the by-value argument for `insert` / `get_or_insert`.
        let mut moved = Vec::new();
        if let Ok(ty) = dcx.destination.ty(self.body.locals()) {
            moved.push(ty);
        }
        for arg in dcx.args {
            if let Ok(ty) = arg.ty(self.body.locals()) {
                moved.push(Self::strip_one_pointer(ty));
            }
        }
        if !moved.iter().any(|ty| Self::ty_is_pointer_move_sensitive(*ty, 0)) {
            return;
        }
        debug!(
            fn_name = %self.fn_name,
            callee = path,
            "CHC: a pointer value moved by a call with no binding transfer — fail closed"
        );
        self.record_sound_fallback_reason("pointer_move_bindings_not_transferred");
        let mut rebound: Vec<usize> = vec![dcx.destination.local];
        for arg in dcx.args {
            let (Operand::Copy(p) | Operand::Move(p)) = arg else { continue };
            rebound.push(p.local);
            if let Some(target) = self.ref_resolution.ref_targets.get(&p.local) {
                rebound.push(target.local);
            }
        }
        for local in rebound {
            self.ref_resolution.clear_path_insensitive_ref_metadata(local);
        }
    }

    /// The callee's own name, without its generic arguments, wherever they sit.
    fn callee_leaf(path: &str) -> &str {
        crate::codegen_ay::chc::modifies_frame::callee_path_leaf(path)
    }

    /// `&mut T` / `*mut T` -> `T`; anything else unchanged.
    fn strip_one_pointer(ty: rustc_public::ty::Ty) -> rustc_public::ty::Ty {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => pointee,
            _ => ty,
        }
    }

    /// Is `ty` a pointer, or a SHALLOW carrier of one? Bounded at depth 2 so
    /// owning containers (`Vec`, `String`, `Box`), whose raw pointer sits
    /// deeper, do not arm the guard.
    fn ty_is_pointer_move_sensitive(ty: rustc_public::ty::Ty, depth: u32) -> bool {
        if depth > 2 {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                tys.iter().any(|t| Self::ty_is_pointer_move_sensitive(*t, depth + 1))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().into_iter().any(|v| {
                v.fields().into_iter().any(|f| {
                    mono_ty::field_ty(&f, &args)
                        .is_none_or(|t| Self::ty_is_pointer_move_sensitive(t, depth + 1))
                })
            }),
            _ => false,
        }
    }
}
