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

#[path = "codegen_call_posix_memalign.rs"]
mod codegen_call_posix_memalign;
#[path = "codegen_call_struct_map_accessor.rs"]
mod codegen_call_struct_map_accessor;
#[path = "codegen_call_sysconf.rs"]
mod codegen_call_sysconf;

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
use ay_bindings::Expr;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::warn;
use trust_mc_core::violation::PropertyKind;

/// A diverging (`-> !`) callee that is a KNOWN guaranteed panic: reaching it is
/// a genuine failure, not an encoder give-up. Used to emit error() without a
/// `diverging_call_drop` taint so the CTREX certifies as Genuine. The type-valid
/// case of the assert_* intrinsics returns normally (target=Some) and never
/// reaches the diverging-call handler, so matching here is exact.
pub(in crate::codegen_ay::chc::call) fn is_known_diverging_panic_intrinsic(path: &str) -> bool {
    path.ends_with("::abort")
        || path.contains("intrinsics::abort")
        || path.contains("assert_zero_valid")
        || path.contains("assert_mem_uninitialized_valid")
        || path.contains("assert_uninit_valid")
        || path.contains("assert_inhabited")
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
        if self.try_dispatch_call_kani(dcx) {
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
            return true;
        }

        // Part of #3159: Virtual call dispatch (dyn Trait method resolution).
        // Detects InstanceKind::Virtual and devirtualizes to the concrete
        // implementation when there is exactly one reachable impl.
        if self.try_dispatch_call_virtual(dcx) {
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
            return true;
        }

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
        if self.try_dispatch_call_fn_ptr(dcx) {
            return true;
        }

        // Part of #3736: direct `libc::posix_memalign` FFI model.
        if self.is_foreign_call(dcx.func) && self.try_dispatch_call_posix_memalign(dcx) {
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
}
