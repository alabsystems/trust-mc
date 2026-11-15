// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Terminator translation for AY codegen.
//!
//! This module handles MIR Terminator analysis for control flow:
//! - Successor block computation with path conditions
//! - SwitchInt branch condition generation
//! - CFG structure analysis (separate from constraint generation)

use super::{
    AssertMessage, BinOp, Expr, IntoOption, Operand, RigidTy, StatementCodegen, SwitchTargets,
    Terminator, TerminatorKind, TerminatorSuccessors, TyKind,
};
use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;
use crate::codegen_ay::types::{bool_sort, int_ty_to_bitvec_width, uint_ty_to_bitvec_width};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use num_bigint::BigInt;
use rustc_public::mir::{BasicBlockIdx, Mutability};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn handled_call_successors(
        &mut self,
        outcome: CallDispatchOutcome,
        func: &Operand,
        target: Option<BasicBlockIdx>,
        term: &Terminator,
    ) -> Option<TerminatorSuccessors> {
        match outcome {
            CallDispatchOutcome::Miss => None,
            CallDispatchOutcome::Continue(next_bb) => Some(vec![(next_bb, None)]),
            CallDispatchOutcome::Diverge => Some(vec![]),
            CallDispatchOutcome::FallthroughToUnsupported => {
                Some(self.unsupported_call_successors(func, target, term))
            }
        }
    }

    pub(in crate::codegen_ay::statement) fn unsupported_call_successors(
        &mut self,
        func: &Operand,
        target: Option<BasicBlockIdx>,
        term: &Terminator,
    ) -> TerminatorSuccessors {
        // Format type string lazily — only allocate when reaching this
        // unsupported fallback (Part of #2267).
        let func_ty_str = func
            .ty(self.body.locals())
            .map_or_else(|_| String::from("unknown"), |ty| format!("{:?}", ty));
        self.ctx.unsupported_with_fallback(
            "Call terminator",
            format!("{:?} (fn: {})", mir_span!(term), func_ty_str),
        );
        target.map(|t| vec![(t, None)]).unwrap_or_default()
    }

    /// BMC: Kani's unwinding assertion on a loop the callee of `func` may
    /// run, where the call was handled by a MODEL (a stub, the abstracted
    /// fallback, the array comparison, virtual and `pow` / math handlers), not
    /// by inlining its body, under a declared unwind bound with unwinding
    /// assertions on. `Vec::contains` over six elements under
    /// `#[kani::unwind(2)]` verified clean where Kani fails `unwinding
    /// assertion loop 0` (walker fail-closed repair round 4, finding 6's class,
    /// `r4_std_models_unwind.rs` `u8_vec_contains_u2`). Fails closed
    /// (`unsupported_with_fallback`) unless the callee runs no loop
    /// (`obligation_free_walk::instance_may_loop`) or the passes of every
    /// loop it runs have a bound `B` (`bmc_model_call_trip_bound`), where the
    /// check is `B < U`, never certified; a reduction states its own
    /// unwinding assertion (`iter_adapters.rs`, `record_reduce_unwinding`).
    pub(in crate::codegen_ay::statement) fn bmc_model_call_unwinding_check(
        &mut self,
        func: &Operand,
        args: &[Operand],
    ) {
        use trust_mc_codegen_stubs::StubKind;
        if std::mem::take(&mut self.stub_stated_unwinding) {
            return;
        }
        let config = &self.ctx.config;
        if !config.has_explicit_unwind || !config.unwinding_assertions {
            return;
        }
        if let Some(path) = self.resolve_callee_path(func)
            && matches!(
                self.stub_registry.lookup(&path),
                Some(StubKind::IterFold | StubKind::IterSum)
            )
        {
            return;
        }
        let stubs = self.ctx.unit_stub_map();
        let may_loop = match func.ty(self.body.locals()).into_option().map(|ty| ty.kind()) {
            Some(TyKind::RigidTy(RigidTy::FnDef(def, args))) => {
                match crate::codegen_ay::obligation_free_walk::resolve_through_stubs(
                    def, &args, &stubs,
                ) {
                    Some(instance) => bmc_instance_may_loop_cached(self.ctx.tcx, instance, &stubs),
                    None => true,
                }
            }
            _ => true,
        };
        if !may_loop {
            return;
        }
        let unwind = u64::from(self.ctx.config.unwind_depth);
        let Some(bound) = self.bmc_model_call_trip_bound(func, args) else {
            self.ctx.unsupported_with_fallback(
                "model_call_loop_under_declared_unwind",
                "a call the BMC encoder models may run a loop past the declared unwind bound",
            );
            return;
        };
        let folded =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&bound).and_then(|value| {
                match value.value() {
                    ay_bindings::ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
                    _ => None,
                }
            });
        if folded.is_some_and(|bound| bound < unwind) {
            debug!(
                ?folded,
                unwind, "BMC modelled call: every loop it runs stays under the declared bound"
            );
            return;
        }
        // `bound < U` where the bound is symbolic: a check, never certified
        // (`bmc_sound_havoc`), since the bound over-approximates the passes
        // (`memchr` stops at the first match).
        self.ctx.bmc_sound_havoc("model_call_loop_unwind_bound");
        let unwind = Expr::bitvec_const(unwind, crate::codegen_ay::types::POINTER_WIDTH);
        self.record_violation_guarded_with_message(
            bound.bvuge(unwind),
            "unwind_assert",
            Some(
                "unwinding assertion loop 0 (a loop in a call the BMC encoder models, under the \
                 declared unwind bound)"
                    .to_string(),
            ),
        );
    }

    /// Kani's unwinding assertion on the loop the kani library's
    /// `Arbitrary::any` runs for a `kani::any()` this lane models as a fresh
    /// value (`shared::kani_any_loops`): `kani::any::<[bool; N]>()` runs `N`
    /// passes, so under a declared unwind `U <= N` with unwinding assertions on
    /// the assertion fails wherever the call is reached. Exact, and so
    /// certified.
    pub(in crate::codegen_ay::statement) fn bmc_kani_any_unwinding_check(
        &mut self,
        destination: &rustc_public::mir::Place,
    ) {
        let config = &self.ctx.config;
        if !config.has_explicit_unwind || !config.unwinding_assertions {
            return;
        }
        let Some(dest_ty) = destination.ty(self.body.locals()).into_option() else {
            return;
        };
        let passes = crate::codegen_ay::shared::kani_any_loops::kani_any_loop_passes(dest_ty);
        if passes < u64::from(self.ctx.config.unwind_depth) {
            return;
        }
        debug!(passes, "BMC kani::any runs a loop past the declared unwind bound");
        self.record_violation_guarded_with_message(
            Expr::bool_const(true),
            "unwind_assert",
            Some(crate::codegen_ay::shared::kani_any_loops::kani_any_unwind_message(passes)),
        );
    }

    /// Kani's unwinding assertion on the comparison loop of an equality the
    /// BMC lane models as one value comparison (`dispatch_raw_eq_and_cmp`:
    /// the `raw_eq` intrinsic, `PartialEq::eq` / `ne` on an array, slice,
    /// `str` or `Vec`). Kani compares bytewise-comparable elements with
    /// CBMC's `memcmp`, one pass per byte, and others with one pass per
    /// element; the byte count (at least one per element) bounds both, as
    /// in the CHC lane's table (`chc/call/codegen_call_model_unwind.rs`).
    /// Under a declared unwind bound `U` with unwinding assertions on, a
    /// count `B` that does not fold below `U` is the check `B < U`, never
    /// certified; a slice whose length the lane cannot read fails closed.
    /// Without it `same::<[u16; 4]>()` and `"hello" == "hello"` under
    /// `unwind(3)` verified clean where Kani fails them (the merge of
    /// fix/chc-walker-fail-closed with main, `model_call_unwind_eq_len_dual.rs`),
    /// and so did `Some([1u16, 2, 3, 4]) == ..` and `Some("hello") == ..` until
    /// the wrappers' parts were read (`shared::compare_loops`,
    /// `model_call_unwind_wrapped_eq_dual.rs`).
    pub(in crate::codegen_ay::statement) fn bmc_compare_unwinding_check(
        &mut self,
        fn_name: &str,
        args: &[Operand],
    ) {
        let compared = self.compared_values.take();
        let config = &self.ctx.config;
        if !config.has_explicit_unwind || !config.unwinding_assertions {
            return;
        }
        let pointer = crate::codegen_ay::types::POINTER_WIDTH;
        let Some(first) = args.first() else {
            return;
        };
        let Some(ty) = first.ty(self.body.locals()).into_option() else {
            return;
        };
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => inner,
            _ => ty,
        };
        let size_of = |ty: rustc_public::ty::Ty| {
            ty.layout().ok().map(|layout| layout.shape().size.bytes() as u64)
        };
        // The loops stop early (`shared::compare_loops`): from the two values
        // the model compared, the condition under which one of them completes
        // the declared bound's passes. A bound read from the types alone
        // failed `[9u8, 2, 3, 4] != [1, 2, 3, 4]` and `"abc" != "ab"` under
        // `unwind(2)` (undecided, or an uncertified failure) where main and
        // Kani prove them (walker fail-closed review, round 2 of the repair
        // after the merge with main, `model_call_unwind_early_exit_dual.rs`).
        if let Some((lhs, rhs)) = compared {
            use crate::codegen_ay::shared::compare_loops::{
                compare_reach, is_const_false, raw_eq_reach,
            };
            let unwind = u64::from(self.ctx.config.unwind_depth);
            let reach = if fn_name.contains("raw_eq") {
                raw_eq_reach(pointee, &lhs, &rhs, unwind, &size_of)
            } else {
                // `codegen_partial_eq_value` reads through every reference level.
                let mut value_ty = pointee;
                while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = value_ty.kind() {
                    value_ty = inner;
                }
                compare_reach(value_ty, &lhs, &rhs, unwind, &size_of)
            };
            if let Some(reach) = reach {
                if is_const_false(&reach.reaches) {
                    return;
                }
                if !reach.exact {
                    self.ctx.bmc_sound_havoc("model_call_loop_unwind_bound");
                }
                self.record_violation_guarded_with_message(
                    reach.reaches,
                    "unwind_assert",
                    Some(
                        "unwinding assertion loop 0 (a comparison loop the BMC encoder models, \
                         under the declared unwind bound)"
                            .to_string(),
                    ),
                );
                return;
            }
        }
        // A float compares element by element (it is not bytewise-comparable).
        let units = |elem: rustc_public::ty::Ty| {
            if matches!(elem.kind(), TyKind::RigidTy(RigidTy::Float(_))) {
                return Some(1);
            }
            size_of(elem).map(|bytes| bytes.max(1))
        };
        let bound = match pointee.kind() {
            _ if fn_name.contains("raw_eq") => match size_of(pointee) {
                Some(bytes) => Some(Expr::bitvec_const(bytes, pointer)),
                None => None,
            },
            TyKind::RigidTy(RigidTy::Array(elem, len)) => {
                let (Some(len), Some(per)) = (len.eval_target_usize().into_option(), units(elem))
                else {
                    return;
                };
                Some(Expr::bitvec_const(len.saturating_mul(per), pointer))
            }
            TyKind::RigidTy(RigidTy::Slice(elem)) => {
                let Some(per) = units(elem) else {
                    return;
                };
                self.slice_len_expr(first)
                    .map(|len| (len, per))
                    .map(|(len, per)| scaled_len(len, per, pointer))
            }
            TyKind::RigidTy(RigidTy::Str) => self.slice_len_expr(first),
            TyKind::RigidTy(RigidTy::Adt(def, adt_args))
                if rustc_public::CrateDef::trimmed_name(&def) == "Vec" =>
            {
                let Some(elem) = adt_args.0.iter().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                }) else {
                    return;
                };
                let Some(per) = units(elem) else {
                    return;
                };
                self.slice_len_expr(first).map(|len| scaled_len(len, per, pointer))
            }
            // `Option`, `Result`, `Box`, a reference or a tuple: the loops of
            // the parts it compares (`shared::compare_loops`). A `str`, slice
            // or `Vec` part's length is not read here, so it fails closed.
            _ if crate::codegen_ay::shared::compare_loops::is_compared_wrapper(pointee) => {
                use crate::codegen_ay::shared::compare_loops::{CompareLoops, compare_loops};
                match compare_loops(pointee, &size_of) {
                    CompareLoops::LoopFree | CompareLoops::Unknown => return,
                    CompareLoops::AtMost(passes) => Some(Expr::bitvec_const(passes, pointer)),
                    CompareLoops::LengthOfAPart => self.option_slice_payload_len(first, pointee),
                }
            }
            // A scalar compares without a loop; anything else is left to the
            // calls its comparison makes.
            _ => return,
        };
        let unwind = u64::from(self.ctx.config.unwind_depth);
        let Some(bound) = bound.filter(|bound| bound.sort().bitvec_width() == Some(pointer)) else {
            self.ctx.unsupported_with_fallback(
                "model_call_loop_under_declared_unwind",
                "a comparison the BMC encoder models runs a loop of unknown length under the \
                 declared unwind bound",
            );
            return;
        };
        let folded =
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&bound).and_then(|value| {
                match value.value() {
                    ay_bindings::ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
                    _ => None,
                }
            });
        if folded.is_some_and(|bound| bound < unwind) {
            return;
        }
        self.ctx.bmc_sound_havoc("model_call_loop_unwind_bound");
        let unwind = Expr::bitvec_const(unwind, pointer);
        self.record_violation_guarded_with_message(
            bound.bvuge(unwind),
            "unwind_assert",
            Some(
                "unwinding assertion loop 0 (a comparison loop the BMC encoder models, under the \
                 declared unwind bound)"
                    .to_string(),
            ),
        );
    }

    /// The bytes `==` on an `Option<&str>` or `Option<&[P]>` (primitive `P`)
    /// compares: the left payload's length (times `size_of::<P>()`) when it is
    /// `Some`, else 0 (`Option::eq` compares payloads only when both are
    /// `Some`, and a `str` or slice compares its bytes only when the lengths
    /// agree, so the left length bounds the loop). `None` for any other shape,
    /// or a value whose length field the lane does not hold: the caller then
    /// fails closed.
    fn option_slice_payload_len(
        &mut self,
        operand: &Operand,
        pointee: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let pointer = crate::codegen_ay::types::POINTER_WIDTH;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = pointee.kind() else {
            return None;
        };
        if !matches!(
            rustc_public::CrateDef::name(&def).as_str(),
            "std::option::Option" | "core::option::Option"
        ) {
            return None;
        }
        let payload_ty = args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;
        let TyKind::RigidTy(RigidTy::Ref(_, unsized_ty, _)) = payload_ty.kind() else {
            return None;
        };
        let per = match unsized_ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => 1,
            TyKind::RigidTy(RigidTy::Slice(elem))
                if matches!(
                    elem.kind(),
                    TyKind::RigidTy(
                        RigidTy::Bool
                            | RigidTy::Char
                            | RigidTy::Int(_)
                            | RigidTy::Uint(_)
                            | RigidTy::Float(_)
                    )
                ) =>
            {
                (elem.layout().ok()?.shape().size.bytes() as u64).max(1)
            }
            _ => return None,
        };
        let value = self.codegen_partial_eq_value(operand)?;
        let option_dt = value.sort().datatype_sort()?.clone();
        if option_dt.constructors.len() != 2 {
            return None;
        }
        let some = option_dt.constructors.iter().find(|ctor| ctor.fields.len() == 1)?;
        let field = some.fields.first()?;
        let slice_dt = field.sort.datatype_sort()?;
        let len_field =
            slice_dt.constructors.first()?.fields.iter().find(|f| f.name == "fld_len")?;
        if len_field.sort.bitvec_width() != Some(pointer) {
            return None;
        }
        let payload = value
            .clone()
            .try_field_select(&option_dt.name, &field.name, field.sort.clone())
            .ok()?;
        let len =
            payload.try_field_select(&slice_dt.name, "fld_len", len_field.sort.clone()).ok()?;
        let is_some = value.try_is_constructor(&option_dt.name, &some.name).ok()?;
        Some(Expr::ite(is_some, scaled_len(len, per, pointer), Expr::bitvec_const(0u64, pointer)))
    }

    /// A pointer-width bound on the back edges of every loop the modelled
    /// callee of `func` runs, the BMC half of the CHC trip-count table
    /// (`chc/call/codegen_call_model_unwind.rs`): `core::slice::memchr::
    /// memchr(x, text)` runs at most `text.len()` passes in each of its loops
    /// (frozen nightly `core/src/slice/memchr.rs`: `memchr_naive`,
    /// `memchr_aligned`'s two-word steps and its tail), and
    /// `SpecFromElem::from_elem(elem, n)` of a primitive element runs
    /// `extend_with`'s one loop of at most `n` passes. Any other callee keeps
    /// the fail-closed fallback. `vec![1u8, .., 6].contains(&x)` under
    /// `unwind(8)` and `vec![x; 4]` under `unwind(5)` failed closed where main
    /// and Kani prove them (walker fail-closed repair round 5,
    /// `model_call_unwind_dual.rs` `u6`, `model_call_unwind_bound_dual.rs`
    /// `b4`).
    fn bmc_model_call_trip_bound(&mut self, func: &Operand, args: &[Operand]) -> Option<Expr> {
        let path = self.resolve_callee_path(func)?;
        let pointer = crate::codegen_ay::types::POINTER_WIDTH;
        let whole_local_or_const = |operand: &Operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => place.projection.is_empty(),
            Operand::Constant(_) => true,
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => false,
        };
        let bound = if path.ends_with("slice::memchr::memchr") {
            let text = args.get(1)?;
            if !whole_local_or_const(text) {
                return None;
            }
            self.slice_len_expr(text)?
        } else if path.contains("BoundedArbitrary") && path.ends_with("bounded_any") {
            // The kani library's `bounded_any::<N>` for `String`, `Vec<P>` and
            // `Box<[P]>` of a primitive `P` (`library/trust-mc/src/
            // bounded_arbitrary.rs`): each loop it runs takes at most `N`
            // passes (the `0..len` fill with `len <= N`, `Utf8Chunks::next` over
            // `N` bytes), and `P::any()` runs none. A map or set's `insert`
            // loop has no such bound and keeps the fail-closed fallback.
            let TyKind::RigidTy(RigidTy::FnDef(_, generics)) =
                func.ty(self.body.locals()).into_option()?.kind()
            else {
                return None;
            };
            let mut n = None;
            let mut container_ok = false;
            for arg in &generics.0 {
                match arg {
                    rustc_public::ty::GenericArgKind::Const(len) => {
                        n = len.eval_target_usize().into_option();
                    }
                    rustc_public::ty::GenericArgKind::Type(ty) => {
                        container_ok = bounded_any_container_is_loop_bounded(*ty);
                    }
                    _ => {}
                }
            }
            if !container_ok {
                return None;
            }
            Expr::bitvec_const(n?, pointer)
        } else if path.contains("SpecFromElem") && path.ends_with("from_elem") {
            let elem = args.first()?.ty(self.body.locals()).into_option()?;
            let primitive = matches!(
                elem.kind(),
                TyKind::RigidTy(
                    RigidTy::Bool
                        | RigidTy::Char
                        | RigidTy::Int(_)
                        | RigidTy::Uint(_)
                        | RigidTy::Float(_)
                )
            );
            let n = args.get(1)?;
            if !primitive || !whole_local_or_const(n) {
                return None;
            }
            match self.mir_usize_constant(n) {
                Some(n) => Expr::bitvec_const(n, pointer),
                None => self.codegen_operand(n)?,
            }
        } else {
            return None;
        };
        debug!(%path, ?bound, "BMC modelled call trip bound");
        (bound.sort().bitvec_width() == Some(pointer)).then_some(bound)
    }

    /// The value of a `usize` operand that is a constant, or a local whose
    /// one definition in the body is a constant and that nothing borrows.
    fn mir_usize_constant(&self, operand: &Operand) -> Option<u64> {
        use rustc_public::mir::{Rvalue, StatementKind};
        let constant_value = |operand: &Operand| match operand {
            Operand::Constant(constant) => constant.const_.eval_target_usize().into_option(),
            _ => None,
        };
        if let Some(value) = constant_value(operand) {
            return Some(value);
        }
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let local = place.local;
        let mut value = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) = rvalue
                    && borrowed.local == local
                {
                    return None;
                }
                if lhs.local != local {
                    continue;
                }
                let Rvalue::Use(defined, ..) = rvalue else {
                    return None;
                };
                if !lhs.projection.is_empty() || value.is_some() {
                    return None;
                }
                value = Some(constant_value(defined)?);
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                return None;
            }
        }
        if (1..=self.body.arg_locals().len()).contains(&local) {
            return None;
        }
        value
    }

    /// Intercept a destructor-path `Call` (`drop_in_place::<T>` /
    /// `<T as Drop>::drop` / `MaybeUninit::<E>::assume_init_drop`) and treat it as a
    /// no-op successor when the dropped type's glue is provably empty or benign —
    /// the Call-terminator counterpart of the `TerminatorKind::Drop` empty-glue skip.
    /// Returns `None` (decline → the existing "Call terminator" fallback stands,
    /// fail-closed) for anything with a real user `Drop` side effect. Keys on the
    /// destructor callee PATH only, never on a public method name like `clear`.

    fn try_codegen_drop_glue_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
        let path = self.resolve_callee_path(func)?;
        let target = target?;

        // Branch A: `assume_init_drop` drops the INNER `E`, not `MaybeUninit<E>`
        // (whose own auto-glue is ALWAYS empty — gating on the receiver pointee here
        // would be UNSOUND for `E: Drop`). Pull `E` from the FnDef substs.
        if path.ends_with("::assume_init_drop") {
            let func_ty = func.ty(self.body.locals()).into_option()?;
            let TyKind::RigidTy(RigidTy::FnDef(_, substs)) = func_ty.kind() else {
                return None;
            };
            let Some(GenericArgKind::Type(inner)) = substs.0.first() else {
                return None;
            };
            let inner = *inner;
            if mono_ty::has_unresolved_params(inner) {
                return None;
            }
            if bmc_ty_trivially_no_drop(inner)
                || bmc_drop_glue_is_empty(inner)
                || bmc_ty_drop_is_benign(inner)
            {
                debug!("assume_init_drop -> no-op (empty/benign inner glue)");
                return Some(target);
            }
            return None;
        }

        // Branch B: `drop_in_place::<T>` / `<T as Drop>::drop`. The dropped type is
        // the pointee of the receiver `&mut T` / `*mut T` (args[0]).
        if !path.contains("drop_in_place") && !path.contains("Drop>::drop") {
            return None;
        }
        let recv_ty = args.first()?.ty(self.body.locals()).into_option()?;
        let dropped_ty = match recv_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return None,
        };
        if mono_ty::has_unresolved_params(dropped_ty) {
            return None;
        }
        // Exactly the Drop-arm predicate set, applied to the Call's dropped type —
        // sound by the same argument already accepted for the Drop terminator.
        if bmc_ty_trivially_no_drop(dropped_ty)
            || bmc_ty_is_hashbrown(dropped_ty)
            || bmc_drop_glue_is_empty(dropped_ty)
            || bmc_ty_drop_is_dealloc_only(dropped_ty)
            || bmc_ty_drop_is_benign(dropped_ty)
            || self.bmc_adt_auto_glue_all_fields_benign(dropped_ty, 0)
        {
            debug!(%path, "drop-glue call -> no-op (empty/benign glue)");
            return Some(target);
        }
        None
    }

    /// Translate a MIR Terminator into AY constraints and return all successor blocks
    /// with their path conditions for proper control flow handling.
    ///
    /// REQUIRES: term is a valid MIR terminator from self.body
    /// ENSURES: Returns (block_idx, path_cond) pairs for all reachable successors
    /// ENSURES: Path conditions are mutually exclusive and exhaustive
    /// ENSURES: Return/Abort terminators return empty vec (no successors)
    pub(in crate::codegen_ay) fn codegen_terminator_with_successors(
        &mut self,
        term: &Terminator,
    ) -> TerminatorSuccessors {
        // A call writes its destination: a pointee entry the handler does not
        // re-insert still describes the previous value (`ref_pointee_table`).
        let reassigned = match &term.kind {
            TerminatorKind::Call { destination, .. }
                if !destination
                    .projection
                    .iter()
                    .any(|p| matches!(p, rustc_public::mir::ProjectionElem::Deref)) =>
            {
                Some(self.ssa_base_name(destination))
            }
            _ => None,
        };
        let generation = self.ref_pointees.generation();
        let successors = self.codegen_terminator_with_successors_inner(term);
        if let Some(key) = reassigned {
            self.ref_pointees.poison_stale_since(&key, generation);
        }
        self.flush_ref_pointee_path_ambiguity();
        successors
    }

    fn codegen_terminator_with_successors_inner(
        &mut self,
        term: &Terminator,
    ) -> TerminatorSuccessors {
        debug!(?term, kind=?term.kind, "AY codegen_terminator_with_successors");
        // Track source span for property locations (#1164).
        self.current_span = Some(mir_span!(term));
        // SwitchInt→variant bridge (#3017): per-branch facts are staged fresh for the
        // current terminator only; clear any stragglers (e.g. a duplicated switch
        // target from the previous terminator) so no stale fact rides a later edge.
        self.pending_edge_variant_facts.clear();

        match &term.kind {
            TerminatorKind::Goto { target } => {
                vec![(*target, None)]
            }

            TerminatorKind::SwitchInt { discr, targets } => {
                self.codegen_switchint_all(discr, targets)
            }

            TerminatorKind::Return => {
                vec![]
            }

            TerminatorKind::Unreachable => {
                // Two very different facts arrive as the same terminator.
                //
                // The loop unroller cuts the back-edge of the last unrolled copy
                // into a synthetic `Unreachable` block: reaching it means the
                // loop wanted an iteration past `--unwind N`, so the BOUND is
                // wrong, not the program. Labelling that `unreachable` sends it
                // down the driver's panic taxonomy ("Failed Checks: panic
                // reached", `[AY:CTREX_CAT:Genuine]`, a concrete-playback test)
                // and tells the user to go debug a bug that does not exist.
                //
                // `unwind_sentinel` recognizes only blocks the unroller itself
                // built (see the six clauses documented there); everything else
                // keeps the original `unreachable` label, so a genuine reachable
                // unreachable still reports as the panic it is.
                if self.unwind_assert_blocks.contains(&self.current_bb) {
                    // Kani-identical description "unwinding assertion loop N"
                    // (pinned by the corpus: diverging_loop, never-return). N is
                    // this body's loop ordinal in sentinel-block order — the
                    // unroller appends one sentinel pair per unrolled loop, so
                    // block order is unroll order (0 for the ubiquitous
                    // single-loop body). The class stays "unwind" and the
                    // driver's raise-the-bound tip keys on the "unwinding
                    // assertion loop" PREFIX, which this preserves; the flag
                    // guidance lives in that tip and in the not-certified note,
                    // not in the check text.
                    let ordinal = {
                        let mut blocks: Vec<usize> =
                            self.unwind_assert_blocks.iter().copied().collect();
                        blocks.sort_unstable();
                        blocks.iter().position(|&b| b == self.current_bb).unwrap_or(0)
                    };
                    self.record_violation_guarded_with_message(
                        Expr::bool_const(true),
                        "unwind_assert",
                        Some(format!("unwinding assertion loop {ordinal}")),
                    );
                } else {
                    // Unreachable code guarded by path condition
                    self.record_violation_guarded(Expr::bool_const(true), "unreachable");
                }
                vec![]
            }

            TerminatorKind::Drop { place, target, .. } => {
                if self.try_native_box_drop(place) {
                    return vec![(*target, None)];
                }
                // Phase 1 (#3499): Record sound fallback for drops on types that
                // may implement Drop. Non-trivial drops are over-approximated as
                // skip, so fallback recording triggers verdict demotion.
                // Part of #3945: hashbrown internal drops are expected when HashMap
                // stubs are active — don't poison the verdict for these.
                // Part of #4112 follow-up: an empty drop shim (per
                // `resolve_drop_in_place`) means the drop is semantically a no-op,
                // so skipping it is exact — no fallback demotion needed. Covers
                // ADTs without Drop glue (NonZero, user structs, closures) that
                // the shallow type-list check misses.
                let drop_ty = place.ty(self.body.locals()).into_option();
                if drop_ty.is_some_and(|ty| {
                    !bmc_ty_trivially_no_drop(ty)
                        && !bmc_ty_is_hashbrown(ty)
                        && !bmc_drop_glue_is_empty(ty)
                        // #3017: a stdlib owning container (Vec/String/Box/VecDeque)
                        // whose element/allocator types run no user Drop deallocates
                        // only — invisible to the BMC value model, so the skip is
                        // exact and must not demote a clean PROOF. The conservative
                        // classifier rejects `Vec<T-with-Drop>` (real T-drops), so
                        // this never silently drops a user side effect.
                        && !bmc_ty_drop_is_dealloc_only(ty)
                        // G2: bmc_ty_drop_is_benign is a strict superset of the #3017
                        // dealloc-only classifier — it also spares Rc/Arc/Weak/Mutex/
                        // RwLock/lock-guard/HashMap/BTreeMap/HashSet/BTreeSet/BinaryHeap
                        // receivers, plus tuple/array/slice elements, closure upvars,
                        // and glue-only struct fields, recursing to reject any real
                        // user Drop. Kept alongside dealloc_only (which it subsumes) so
                        // the canonical #3017 path is preserved rather than removed.
                        && !bmc_ty_drop_is_benign(ty)
                        // tcx-aware last resort: a glue-owning struct/enum with NO user
                        // Drop impl whose fields are all benign (e.g. aterm's Parser).
                        // Sound — its auto glue is exactly the benign field drops.
                        && !self.bmc_adt_auto_glue_all_fields_benign(ty, 0)
                }) {
                    // Name the dropped type: the demotion is otherwise
                    // impossible to attribute from the log alone.
                    let detail = match drop_ty {
                        Some(ty) => format!("non-trivial drop skipped: {ty}"),
                        None => String::from("non-trivial drop skipped"),
                    };
                    self.ctx.unsupported_with_fallback("Drop_side_effects", detail);
                }
                vec![(*target, None)]
            }

            TerminatorKind::Call { func, args, destination, target, .. } => {
                if target.is_some() && self.try_native_box_transfer_call(func, args, destination) {
                    return vec![(target.unwrap(), None)];
                }
                // SwitchInt→variant bridge (#3017): a callee may retag an enum through a
                // mutable-reference argument, so drop facts that could go stale.
                self.kill_variant_facts_for_call(args);
                // FC-06 (BMC): a call destination through a deref is a store.
                self.bmc_modifies_check_deref_store(destination);
                // A sub-slice view with a nonzero start handed to a model that
                // reads the SOURCE array instead of the view's own backing.
                self.bmc_subslice_consumer_fail_closed(func, args);

                // BMC drop-glue Call intercept — the Call-terminator analogue of the
                // `TerminatorKind::Drop` empty/benign-glue skip. A non-empty Drop is
                // lowered to an explicit destructor Call (`drop_in_place::<T>` /
                // `<T as Drop>::drop` / `MaybeUninit::<E>::assume_init_drop`). Skip it
                // as a no-op successor (no fallback demotion) ONLY when the dropped
                // type's glue is provably empty/benign. Placed FIRST — before any
                // dispatcher inlines a container destructor and exposes its non-DAG
                // element-drop loop (e.g. ArrayVec::clear). Fail-closed: declines for
                // any real user Drop side effect, leaving existing handling intact.
                if let Some(next_bb) = self.try_codegen_drop_glue_call(func, args, *target) {
                    return vec![(next_bb, None)];
                }
                // Debug: log collection-related call terminators (#1037, #1609).
                // Only format type string when debug logging is enabled to avoid
                // allocating on every Call terminator (Part of #2267).
                if tracing::enabled!(tracing::Level::DEBUG)
                    && let Ok(ty) = func.ty(self.body.locals())
                {
                    let ty_str = format!("{:?}", ty);
                    if ty_str.contains("Vec")
                        || ty_str.contains("RawVec")
                        || ty_str.contains("BTreeSet")
                        || ty_str.contains("String")
                    {
                        debug!("codegen_terminator CALL: func={}", ty_str);
                    }
                }
                let kani_result =
                    self.try_codegen_kani_call(func, args, destination, *target, term);
                if let Some(successors) =
                    self.handled_call_successors(kani_result, func, *target, term)
                {
                    // FC-06 (BMC): a handler inlines no body, so its stores reach
                    // the frame only through the call's pointer arguments.
                    self.bmc_modifies_classify_handled_call(args, "kani model call");
                    return successors;
                }
                self.stub_stated_unwinding = false;
                let stub_result =
                    self.try_codegen_stdlib_stub_call(func, args, destination, *target);
                if let Some(successors) =
                    self.handled_call_successors(stub_result, func, *target, term)
                {
                    self.bmc_modifies_classify_handled_call(args, "stub call");
                    if target.is_some() {
                        self.bmc_model_call_unwinding_check(func, args);
                    }
                    return successors;
                }

                // Fallback for abstracted functions without explicit stubs (Part of #1691).
                // If the callee matches abstracted prefixes (UTF8 internals, etc.),
                // return a symbolic value instead of marking as unsupported.
                // This handles pre-inlined stdlib code that can't be intercepted earlier.
                if let Some(next_bb) =
                    self.try_codegen_abstracted_fallback(func, destination, *target)
                {
                    self.bmc_modifies_classify_handled_call(args, "abstracted call");
                    self.bmc_model_call_unwinding_check(func, args);
                    return vec![(next_bb, None)];
                }

                // Array/slice comparison dispatch (Part of #3806).
                // Handles PartialOrd::partial_cmp on array-sorted operands and
                // Option::is_some_and with Ordering methods (SIMD PartialOrd).
                if let Some(next_bb) =
                    self.try_codegen_array_cmp_call(func, args, destination, *target)
                {
                    self.bmc_model_call_unwinding_check(func, args);
                    return vec![(next_bb, None)];
                }

                // Virtual call dispatch (Part of #3159).
                // Resolve InstanceKind::Virtual calls to concrete impls
                // and assign a symbolic return value (sound over-approximation).
                if let Some(next_bb) =
                    self.try_codegen_virtual_call(func, args, destination, *target)
                {
                    self.bmc_modifies_classify_handled_call(args, "virtual call");
                    self.bmc_model_call_unwinding_check(func, args);
                    return vec![(next_bb, None)];
                }

                // Integer pow/wrapping_pow dispatch (Part of #3294).
                // These methods use exponentiation-by-squaring loops in MIR
                // that the BMC path cannot inline. Intercept and encode directly:
                // constant-fold, base-2 shift, or symbolic over-approximation.
                if let Some(next_bb) = self.try_codegen_pow_call(func, args, destination, *target) {
                    self.bmc_model_call_unwinding_check(func, args);
                    return vec![(next_bb, None)];
                }

                // wrapping_abs/wrapping_neg/div_euclid/rem_euclid dispatch (Part of #3186).
                // These methods have branching MIR bodies that fall through to the
                // unsupported-construct fallback. Intercept and encode as bitvector ops.
                if let Some(next_bb) =
                    self.try_codegen_math_unary_call(func, args, destination, *target)
                {
                    self.bmc_model_call_unwinding_check(func, args);
                    return vec![(next_bb, None)];
                }

                // Part of #3783: runtime_ptr_ge — pointer comparison within
                // offset_from_unsigned. Without this, BMC records unsupported
                // construct that taints the CHC verdict via demotion.
                if let Some(next_bb) =
                    self.try_codegen_runtime_ptr_ge(func, args, destination, *target)
                {
                    return vec![(next_bb, None)];
                }

                // kani::internal::apply_closure inlining (Layer B).
                // Function contracts (`#[kani::ensures(...)]`) expand to
                // `apply_closure(closure, &value)`. When the MIR pre-inline pass
                // does not flatten this (it only boosts the harness's own body,
                // missing transitively reached contracts), model it as `f(x)` by
                // inlining the closure body directly. Placed before fn_inline so
                // the closure's UN-tupled `&T` argument is seeded correctly rather
                // than via the RustCall tuple path. Declines to `None` (sound
                // fallback stands) — never emits a symbolic result.
                if let Some(next_bb) =
                    self.try_codegen_apply_closure(func, args, destination, *target)
                {
                    return vec![(next_bb, None)];
                }

                // BMC direct function call inlining (Part of #3377).
                // For small concrete FnDef calls that no specialized handler
                // intercepts, inline the callee body via the BMC mini-inliner.
                if let Some(next_bb) =
                    self.try_codegen_fn_inline_call(func, args, destination, *target)
                {
                    return vec![(next_bb, None)];
                }

                // BMC function pointer resolution (Part of #3377).
                // Resolve indirect FnPtr calls by scanning MIR for
                // ReifyFnPointer/ClosureFnPointer casts, then inline.
                if let Some(next_bb) =
                    self.try_codegen_fn_ptr_call(func, args, destination, *target)
                {
                    return vec![(next_bb, None)];
                }

                if let Some(next_bb) =
                    self.try_codegen_sysconf_bmc(func, args, destination, *target)
                {
                    self.bmc_modifies_classify_handled_call(args, "sysconf call");
                    return vec![(next_bb, None)];
                }
                // Part of #3736: direct `libc::posix_memalign` FFI model.
                if self.is_foreign_call(func)
                    && let Some(next_bb) =
                        self.try_codegen_posix_memalign_bmc(func, args, destination, *target)
                {
                    self.bmc_modifies_classify_handled_call(args, "posix_memalign call");
                    return vec![(next_bb, None)];
                }

                // A foreign call whose definition the USER SUPPLIED
                // (`-Z c-ffi --c-lib`) gets the sound effect frame instead of
                // the fail-closed violation below: fresh return, havoc of every
                // pointee it could write, and the successor edge KEPT. Declines
                // for a symbol no `--c-lib` file defines, which is what keeps
                // `ForeignItems/missing_fn_fail.rs` failing.
                if self.is_foreign_call(func)
                    && let Some(next_bb) =
                        self.try_codegen_foreign_effect_frame_bmc(func, args, destination, *target)
                {
                    self.bmc_modifies_classify_handled_call(args, "foreign effect frame");
                    return vec![(next_bb, None)];
                }

                // Undefined foreign function calls (Part of #3175).
                // Foreign functions not handled by any dispatcher above are
                // unresolved FFI calls — emit assert(false) equivalent so the
                // verifier produces CTREX if the call is reachable. The message
                // is Kani's own, naming the symbol, so the corpus text matches
                // and a user sees WHICH call is unsupported.
                if self.ctx.config.undefined_function_checks && self.is_foreign_call(func) {
                    let name = self.callee_display_name(func);
                    self.record_violation_guarded_with_message(
                        Expr::bool_const(true),
                        "unsupported_foreign_function",
                        Some(format!(
                            "call to foreign \"C\" function `{name}` is not currently supported by Kani"
                        )),
                    );
                    // The call's destination is never assigned, so an inlining
                    // caller continues on a FREE value; and the forced check is
                    // an unsupported construct, not a bug in the program. Neither
                    // may be certified Genuine (tools/soundness-duals/
                    // dual_77_dependent.rs). SAT-only: a dead-path call still
                    // discharges to a clean proof.
                    self.ctx.bmc_sound_havoc("unsupported_foreign_function");
                    return vec![];
                }

                // The same obligation for a foreign callee reached through a fn
                // POINTER. `func(x)` on an `extern "C" fn(u32)` pointer carries
                // no FnDef operand, so `is_foreign_call` above cannot see it;
                // the fn-ptr inliner already declined (a foreign item has no
                // MIR). Without this branch the call fell to the generic havoc
                // fallback and the harness failed on its own downstream assert
                // with a raw message — the right verdict for the wrong reason,
                // and the wrong verdict entirely for a harness whose foreign
                // call sits on a dead path: `record_violation_guarded` conjoins
                // the path condition, so a never-taken call discharges instead
                // of failing the harness.
                if self.ctx.config.undefined_function_checks
                    && func
                        .ty(self.body.locals())
                        .into_option()
                        .is_some_and(|t| matches!(t.kind(), TyKind::RigidTy(RigidTy::FnPtr(..))))
                {
                    // Prefer a resolved instance that turned out foreign; fall
                    // back to a foreign reify seen in this body or a parent
                    // scope. `Instance::resolve` fails on extern declarations,
                    // so the instance path alone can never see them.
                    let foreign_name = match self.resolve_bmc_fn_ptr_callee(func) {
                        Some((instance, _)) if self.is_foreign_instance(&instance) => {
                            let n = instance.name();
                            Some(n.rsplit("::").next().unwrap_or(&n).to_string())
                        }
                        Some(_) => None,
                        None => self
                            .resolve_all_foreign_fn_ptr_names()
                            .into_iter()
                            .next()
                            .or_else(|| self.parent_foreign_fn_ptrs.first().cloned()),
                    };
                    if let Some(name) = foreign_name {
                        self.record_violation_guarded_with_message(
                            Expr::bool_const(true),
                            "unsupported_foreign_function",
                            Some(format!(
                                "call to foreign \"C\" function `{name}` is not currently supported by Kani"
                            )),
                        );
                        // Same taint as the FnDef branch above: the destination
                        // stays free and an inlining caller (`call_on` in
                        // dual_77_dependent.rs) reads it, so its downstream
                        // assertion failure is an artifact of the havoc.
                        self.ctx.bmc_sound_havoc("unsupported_foreign_function");
                        return vec![];
                    }
                }

                self.unsupported_call_successors(func, *target, term)
            }

            TerminatorKind::Assert { cond, expected, msg, target, .. } => {
                // `--no-overflow-checks` / `--no-memory-safety-checks` turn this
                // check off: no obligation, and the successor is entered with
                // NO edge condition, so execution goes on (with the wrapped
                // value of an overflowing op) as the CHC lane's
                // `assert_check_disabled` does. Dropping only the check, the
                // label-kind gate did that while still passing the assertion on
                // as the edge condition: every overflowing (or out-of-bounds)
                // execution was pruned, and code after it verified against
                // states the program does reach.
                if self.mir_assert_check_disabled(msg) {
                    return vec![(*target, None)];
                }
                // `--prove-safety-only` checks UB, not panics. Kani turns every
                // `PropertyClass::Assertion` check into a bare assume under the
                // flag (codegen/assert.rs `codegen_assert_assume`), and it files
                // every MIR `Assert` there but the pointer-UB ones, which are
                // `SafetyCheck`. The CHC lane does the same
                // (`emit_assert_error_rule_shared`). Only the check goes: the
                // edge condition below is the assume half. Checked here, BMC
                // failed a harness on an overflow or an index panic that Kani
                // and the CHC lane do not report.
                let assume_only =
                    self.ctx.config.prove_safety_only && !Self::mir_assert_is_safety_check(msg);
                if let AssertMessage::Overflow(op, lhs, rhs) = msg {
                    let lhs_expr = self.codegen_operand(lhs);
                    let rhs_expr = self.codegen_operand(rhs);
                    if assume_only {
                        // No check; the edge condition below still holds.
                    } else if let (Some(lhs_expr), Some(rhs_expr)) = (lhs_expr, rhs_expr) {
                        // For shift operations, only the value operand's (LHS) signedness
                        // matters. For non-shift ops, check both operands.
                        // Use signed fallback when unknown — unsigned is unsound for negative values (#2714)
                        let is_signed = if matches!(
                            op,
                            BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked
                        ) {
                            self.operand_signedness(lhs)
                        } else {
                            self.is_signed_integer_op(lhs, rhs)
                        }
                        .unwrap_or_else(|| {
                            crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                                "codegen_terminator_overflow",
                            )
                        });
                        // A shift overflows on its DISTANCE, not its value, and
                        // `overflow_check` has no case for it -- its fallthrough
                        // reads "Shift, comparison, and bitwise operations don't
                        // overflow", which is true of the other two and false of
                        // this one. rustc emits `Assert { msg: Overflow(Shl, ..) }`
                        // exactly because `a << s` panics when `s >= bit width`,
                        // and returning None here dropped that obligation on the
                        // floor:
                        //
                        //     let r = a << s;   // s unconstrained
                        //     assert!(r >= 0);
                        //     VERIFICATION:- SUCCESSFUL
                        //
                        // for a program that panics at run time. `let _ = a << s`
                        // alone was caught only because it left the harness with
                        // no obligations at all, which the no-checks gate reports
                        // -- the right verdict for the wrong reason, and no help
                        // the moment the harness asserts anything else.
                        if matches!(
                            op,
                            BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked
                        ) {
                            let distance_signed = self.operand_signedness(rhs);
                            // Kani-identical wording: this IS the MIR assert
                            // `Overflow(Shl|Shr)`, whose rustc description the
                            // corpus pins (binop, test2). Both sub-checks are
                            // conjuncts of that one obligation.
                            let message = if matches!(op, BinOp::Shl | BinOp::ShlUnchecked) {
                                "attempt to shift left with overflow"
                            } else {
                                "attempt to shift right with overflow"
                            };
                            self.emit_mir_assert_shift_distance_check(
                                &lhs_expr,
                                &rhs_expr,
                                distance_signed,
                                message,
                            );
                        } else if let Some((no_overflow, label)) =
                            self.overflow_check(*op, &lhs_expr, &rhs_expr, is_signed)
                        {
                            // Enabled (`mir_assert_check_disabled` above), so
                            // recorded whatever the label's kind would say: the
                            // edge condition below assumes it.
                            self.record_violation_guarded_ungated(no_overflow.not(), label, None);
                        }
                    } else {
                        let location = format!("{:?}", mir_span!(term));
                        self.ctx.unsupported_with_fallback("Overflow assert operands", location);
                        // Conservative: record unconditional violation to prevent
                        // false PROOF when overflow check operands are untranslatable.
                        // Mirrors CHC emit_untranslatable_assert_fallback behavior.
                        // It stands for the enabled MIR `Assert`.
                        self.record_violation_guarded_ungated(
                            Expr::bool_const(true),
                            "untranslatable_overflow_assert",
                            None,
                        );
                    }
                    // Propagate assertion as edge condition so target block gets a
                    // non-None path condition. This enables dead_object detection in
                    // blocks reachable only after Assert chains (#762).
                    let overflow_cond = self.codegen_operand(cond);
                    let edge_cond = overflow_cond.map(|c| if *expected { c } else { c.not() });
                    return vec![(*target, edge_cond)];
                }

                if let Some(cond_expr) = self.codegen_operand(cond) {
                    // Coerce non-bool conditions to bool (Part of #3141).
                    // MIR Assert conditions are typically Bool but after inlining
                    // they can be bitvec or int. Coerce via != 0.
                    let bool_cond = if cond_expr.sort().is_bool() {
                        cond_expr
                    } else if cond_expr.sort().is_bitvec() {
                        if let Some(w) = cond_expr.sort().bitvec_width() {
                            cond_expr.ne(Expr::bitvec_const(0u64, w))
                        } else {
                            let location = format!("{:?}", mir_span!(term));
                            self.ctx.unsupported_with_fallback("Assert condition sort", location);
                            // Conservative: record unconditional violation to prevent
                            // false PROOF when assertion condition is untranslatable.
                            // Mirrors CHC emit_untranslatable_assert_fallback behavior.
                            self.record_violation_guarded(
                                Expr::bool_const(true),
                                "untranslatable_assert_bv_width",
                            );
                            return vec![(*target, None)];
                        }
                    } else if cond_expr.sort().is_int() {
                        cond_expr.ne(Expr::int_const(0))
                    } else {
                        let location = format!("{:?}", mir_span!(term));
                        self.ctx.unsupported_with_fallback("Assert condition sort", location);
                        // Conservative: record unconditional violation to prevent
                        // false PROOF when assertion condition sort is unsupported.
                        // Mirrors CHC emit_untranslatable_assert_fallback behavior.
                        self.record_violation_guarded(
                            Expr::bool_const(true),
                            "untranslatable_assert_sort",
                        );
                        return vec![(*target, None)];
                    };
                    let assertion = if *expected { bool_cond } else { bool_cond.not() };
                    let label = Self::assert_label_for_message(msg);
                    // Assert guarded by path condition. Enabled
                    // (`mir_assert_check_disabled` above), so recorded whatever
                    // the label's kind would say: the edge condition below
                    // assumes it. Under `--prove-safety-only` a panic assert is
                    // that assume alone (`assume_only` above).
                    if !assume_only {
                        self.record_violation_guarded_ungated(assertion.clone().not(), label, None);
                    }
                    // Propagate assertion as edge condition so target block
                    // gets a non-None path condition (#762).
                    vec![(*target, Some(assertion))]
                } else {
                    // Conservative: record unconditional violation when the Assert
                    // condition operand cannot be translated. This prevents false
                    // PROOF — the CHC path handles this case via
                    // emit_untranslatable_assert_fallback (nondeterministic error ∨
                    // successor). The BMC equivalent is: always record a violation
                    // (may cause false CTREX) and continue to the target block.
                    self.record_violation_guarded(
                        Expr::bool_const(true),
                        "untranslatable_assert_operand",
                    );
                    vec![(*target, None)]
                }
            }

            TerminatorKind::Resume | TerminatorKind::Abort => {
                let location = format!("{:?}", mir_span!(term));
                self.ctx.unsupported("Resume/Abort terminator", location);
                vec![]
            }

            TerminatorKind::InlineAsm { .. } => {
                // Inline asm is opaque to the encoder and has a real successor
                // (control resumes after the asm). Dropping the edge with a
                // diagnostic-only `unsupported()` would make the post-asm block
                // unreachable in the encoding and could yield a false PROOF.
                // Use the demoting fallback variant so the driver flips any
                // PROOF to FAILURE (fail-closed), mirroring the CHC path.
                // reachability.rs intentionally forwards InlineAsm here to be
                // marked an unsupported construct rather than rejecting earlier.
                let location = format!("{:?}", mir_span!(term));
                self.ctx.unsupported_with_fallback("InlineAsm terminator", location);
                vec![]
            }
        }
    }

    /// Codegen SwitchInt returning all successor blocks with path conditions.
    ///
    /// Each branch returns its target block and the condition to take that branch.
    fn codegen_switchint_all(
        &mut self,
        discr: &Operand,
        targets: &SwitchTargets,
    ) -> TerminatorSuccessors {
        let discr_expr = if let Some(e) = self.codegen_operand(discr) {
            e
        } else {
            let location = format!("{:?}", discr);
            self.ctx.unsupported_with_fallback("SwitchInt discriminant", location);
            return vec![(targets.otherwise(), None)];
        };

        let mut successors = Vec::new();

        // Collect conditions for explicit cases
        let mut case_conditions = Vec::new();

        // SwitchInt→variant bridge (#3017): if the discriminant traces to a bare local
        // recorded as a multi-variant datatype-enum scrutinee, each explicit branch
        // pins the enum's active variant on its target edge.
        let discr_scrut = Self::discr_local_of_operand(discr)
            .and_then(|local| self.discr_of_local.get(&local).cloned());

        for (case_val, target) in targets.branches() {
            // Create condition: discr == case_val
            let cond = if discr_expr.sort().is_bool() {
                match case_val {
                    0 => discr_expr.clone().not(), // discr == false
                    1 => discr_expr.clone(),       // discr == true
                    _ => {
                        // Bool case_val > 1 is impossible in valid Rust MIR (bools are
                        // always 0 or 1). Treat as dead code — the branch is unreachable.
                        // Use `unsupported` (not `_with_fallback`) because false is a sound
                        // fallback: the branch condition is never satisfied. Part of #3141.
                        let location = format!("{:?} (case_val={})", discr, case_val);
                        self.ctx.unsupported("SwitchInt bool case value (dead code)", location);
                        Expr::bool_const(false)
                    }
                }
            } else if discr_expr.sort().is_int() {
                let case_const = self.switchint_int_case_const(discr, case_val);
                discr_expr.clone().eq(case_const)
            } else if let Some(width) = discr_expr.sort().bitvec_width() {
                if width < 128 {
                    // Mask case_val to bitvec width. MIR stores signed discriminants
                    // (e.g., Ordering::Less = -1) as u128::MAX, which exceeds the
                    // bitvec range. Masking gives the correct bit pattern.
                    // Part of #1229: Fix SwitchInt for signed enum discriminants.
                    let mask = (1u128 << width) - 1;
                    let masked_val = case_val & mask;
                    let case_const = Expr::bitvec_const(masked_val, width);
                    discr_expr.clone().eq(case_const)
                } else {
                    let case_const = Expr::bitvec_const(case_val, width);
                    discr_expr.clone().eq(case_const)
                }
            } else {
                let location = format!("{:?}", discr);
                self.ctx.unsupported_with_fallback("SwitchInt discriminant sort", location);
                let sym_name = self.ctx.fresh_name("ay_switchint_cond");
                self.ctx.declare_var(&sym_name, bool_sort())
            };

            case_conditions.push(cond.clone());

            // Stage a variant fact for this branch's target edge (explicit cases only;
            // no `otherwise` fact — Effort-2 scope). MIR-truth case_val→variant mapping.
            if let Some(scrut) = &discr_scrut
                && let Some(ctor_idx) =
                    self.variant_idx_for_case_val(scrut.adt_def, scrut.ctor_names.len(), case_val)
                && let Some(ctor_name) = scrut.ctor_names.get(ctor_idx)
            {
                let fact = super::VariantFact {
                    place_key: scrut.place_key.clone(),
                    dt_name: scrut.dt_name.clone(),
                    ctor_idx,
                    ctor_name: ctor_name.clone(),
                    guard: cond.clone(),
                };
                self.pending_edge_variant_facts.entry(target).or_default().push(fact);
            }

            successors.push((target, Some(cond)));
        }

        // Otherwise branch: none of the explicit cases matched
        let otherwise_cond = if case_conditions.is_empty() {
            None
        } else {
            // otherwise_cond = !case1 && !case2 && ... && !caseN
            case_conditions.into_iter().map(ay_bindings::Expr::not).reduce(ay_bindings::Expr::and)
        };

        successors.push((targets.otherwise(), otherwise_cond));

        debug!("SwitchInt: {} successors (including otherwise)", successors.len());

        successors
    }

    /// SwitchInt→variant bridge (#3017) KILL: a callee may retag an enum through a
    /// `&mut`/`*mut` argument. We cannot cheaply prove which storage is affected, so
    /// on ANY mutable-reference/pointer argument we over-kill ALL live variant facts
    /// (fail-closed). Immutable `&T`/`*const T` args cannot retag a plain enum.
    fn kill_variant_facts_for_call(&mut self, args: &[Operand]) {
        if self.current_variant_facts.is_empty() {
            return;
        }
        let has_mut_ref = args.iter().any(|arg| {
            let (Operand::Copy(p) | Operand::Move(p)) = arg else {
                return false;
            };
            p.ty(self.body.locals()).into_option().is_some_and(|t| {
                matches!(
                    t.kind(),
                    TyKind::RigidTy(
                        RigidTy::Ref(_, _, Mutability::Mut) | RigidTy::RawPtr(_, Mutability::Mut)
                    )
                )
            })
        });
        if has_mut_ref {
            self.current_variant_facts.clear();
        }
    }

    fn switchint_int_case_const(&self, discr: &Operand, case_val: u128) -> Expr {
        let ty = discr.ty(self.body.locals()).into_option();
        let (signed, width) = match ty.as_ref().map(rustc_public::ty::Ty::kind) {
            Some(TyKind::RigidTy(RigidTy::Int(int_ty))) => {
                (Some(true), Some(int_ty_to_bitvec_width(int_ty)))
            }
            Some(TyKind::RigidTy(RigidTy::Uint(uint_ty))) => {
                (Some(false), Some(uint_ty_to_bitvec_width(uint_ty)))
            }
            Some(TyKind::RigidTy(RigidTy::Char)) => (Some(false), Some(32)),
            _ => (None, None), // external enum: TyKind
        };

        let value = match (signed, width) {
            (Some(true), Some(width)) => {
                let masked = if width < 128 { case_val & ((1u128 << width) - 1) } else { case_val };
                if width < 128 {
                    let sign_bit = 1u128 << (width - 1);
                    if (masked & sign_bit) != 0 {
                        let signed_val = masked as i128 - (1i128 << width);
                        BigInt::from(signed_val)
                    } else {
                        BigInt::from(masked)
                    }
                } else {
                    BigInt::from(masked as i128)
                }
            }
            _ => BigInt::from(case_val), // non-enum: tuple
        };

        Expr::int_const(value)
    }

    /// A struct/enum with NO user `Drop` impl whose every field's drop is benign: its
    /// compiler-generated glue is exactly "drop each field", so skipping the Drop
    /// terminator in BMC is a SOUND no-op. Unlike the stable-MIR-only classifiers above
    /// (which fail-closed on any non-empty drop shim because BMC cannot MIR-inline the
    /// glue the way the CHC path does), this consults the REAL `tcx` for the type's
    /// destructor — a user `Drop::drop`, whose effects BMC can't model by skipping. No
    /// destructor ⇒ the glue is purely the (recursively benign) field drops. Spares e.g.
    /// aterm's `Parser` (owns `Vec<u8>` + `ArrayVec` buffers, no `Drop` impl) so a clean
    /// proof is not spuriously demoted by `Drop_side_effects`.
    fn bmc_adt_auto_glue_all_fields_benign(&self, ty: rustc_public::ty::Ty, depth: usize) -> bool {
        use rustc_public::ty::{RigidTy, TyKind};
        if depth > 8 {
            return false;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return false;
        };
        // Unresolved params would ICE the internal query / resolve_drop_in_place (#3942).
        if mono_ty::has_unresolved_params(ty) {
            return false;
        }
        // The crux: a user `Drop` impl (destructor) has observable effects BMC cannot
        // model by skipping. Only auto field-drop glue (no destructor) may be recursed.
        let internal_def = rustc_public::rustc_internal::internal(self.ctx.tcx, def);
        if internal_def.destructor(self.ctx.tcx).is_some() {
            return false;
        }
        def.variants().iter().all(|variant| {
            variant.fields().iter().all(|f| {
                // Rule A (`shared::mono_ty`): the field's type at the ADT's own
                // arguments. A field whose type does not instantiate is not
                // benign (fail closed).
                mono_ty::field_ty(f, &args).is_some_and(|resolved| {
                    bmc_ty_drop_is_benign(resolved)
                        || self.bmc_adt_auto_glue_all_fields_benign(resolved, depth + 1)
                })
            })
        })
    }
}

/// Returns true when the type trivially has no Drop side effects.
/// Primitives, references, raw pointers, function pointers, and function items never need drop.
/// Used by BMC terminator to gate fallback recording on Drop terminators.
/// Exact no-op-drop check: `resolve_drop_in_place` returning an empty shim
/// means the type has no Drop glue at all, so skipping the Drop terminator is
/// semantically exact (not an over-approximation). Guarded against unresolved
/// generic params, which would ICE inside the resolver (#3942 parity).
/// Part of #4112 follow-up.
fn bmc_drop_glue_is_empty(ty: rustc_public::ty::Ty) -> bool {
    mono_ty::drop_in_place(ty).is_some_and(|glue| glue.is_empty_shim())
}

/// True when dropping `ty` runs only compiler-generated field glue: the drop
/// shim recurses into fields via `Drop` terminators and never `Call`s a user
/// `Drop::drop` or an un-allowlisted deallocator. For such a struct/enum the
/// drop is benign iff every field is benign (the caller performs that field
/// recursion), so a non-empty — but `Call`-free — shim must not fail-close.
///
/// SOUND: any shim that *does* contain a `Call` terminator runs a real
/// `Drop::drop` (user side effect) or an un-modeled dealloc and returns false,
/// preserving the conservative `Drop_side_effects` demotion. Guarded against
/// unresolved params (which would ICE `resolve_drop_in_place`, #3942) and a
/// missing shim body (returns false → demote).
fn bmc_adt_drop_is_field_glue_only(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::mir::TerminatorKind;
    let Some(body) = mono_ty::drop_glue_body(ty) else {
        return false;
    };
    body.blocks.iter().all(|bb| !matches!(bb.terminator.kind, TerminatorKind::Call { .. }))
}

/// Is dropping this coroutine a benign no-op for BMC to skip?
///
/// `resolve_drop_in_place` on a coroutine type yields the coroutine's own
/// state-machine drop (`coroutine_drop`): a `switchInt` on the state followed
/// by `Drop` terminators for the locals live in that state. There is no user
/// `Drop` impl to run — a coroutine cannot have one — so the glue is benign
/// exactly when it `Call`s nothing (no `Drop::drop`, no un-modeled dealloc)
/// and every dropped place is itself benign. Fail-closed on unresolved params
/// (which would ICE the resolver, #3942) and on a missing shim body.
///
/// Without this every `async fn` harness was demoted: the proof macro's
/// `kani::block_on(h())` drops the harness coroutine on return, and the
/// `Drop` of a `{async fn body}` always fell to `Drop_side_effects`.
fn bmc_coroutine_drop_is_benign(ty: rustc_public::ty::Ty, depth: usize) -> bool {
    use rustc_public::mir::TerminatorKind;
    if depth > 8 {
        return false;
    }
    let Some(shim) = mono_ty::drop_in_place(ty) else {
        return false;
    };
    if shim.is_empty_shim() {
        return true;
    }
    let Some(body) = shim.callee_body() else {
        return false;
    };
    body.blocks.iter().all(|bb| match &bb.terminator.kind {
        TerminatorKind::Call { .. } => false,
        TerminatorKind::Drop { place, .. } => place
            .ty(body.locals())
            .ok()
            .is_some_and(|dropped| bmc_drop_benign_rec(dropped, depth + 1)),
        _ => true,
    })
}

fn bmc_ty_trivially_no_drop(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Ref(..)
                | RigidTy::RawPtr(..)
                | RigidTy::FnPtr(..)
                | RigidTy::FnDef(..)
                | RigidTy::Never
                | RigidTy::Str
        )
    )
}

/// G2 fix: a Drop is "benign" — skipping it in BMC is a SOUND no-op with no
/// false-PROOF risk — when it is a dealloc-only std collection (`Vec`, `String`,
/// `Box`, `Rc`, `Arc`, `Mutex`, …) or a tuple/array/closure/glue-only struct
/// whose components are all benign.
///
/// Rationale (parity with the canonical CHC predicate
/// `chc/.../transition_drop/no_drop.rs` — #3348/#3495/#3589/#4268, and the same
/// philosophy as [`bmc_ty_is_hashbrown`]): these `Drop` impls only free
/// abstractly-modeled memory / release a platform lock — they have no
/// program-visible side effect and cannot panic, so the conservative BMC
/// `Drop_side_effects` demotion is spurious for them. Without this, dropping a
/// `Vec`-owning local (e.g. aterm's `Parser { osc_data: Vec<u8> }`) demotes
/// every proof, even though BMC already skips the drop identically.
///
/// SOUND because: types with a user `Drop` impl that has side effects have
/// available MIR and are inlined+modeled (their `panic!`/asserts are checked)
/// before reaching this gate; a struct that merely owns drop glue but is NOT an
/// allowlisted collection hits the `!bmc_drop_glue_is_empty` early-return and
/// stays demoted (fail-closed). Only the allowlist and no-glue aggregates are
/// reclassified.
fn bmc_ty_drop_is_benign(ty: rustc_public::ty::Ty) -> bool {
    bmc_drop_benign_rec(ty, 0)
}

fn bmc_drop_benign_rec(ty: rustc_public::ty::Ty, depth: usize) -> bool {
    use rustc_public::CrateDef;
    // Bound recursion on self-referential types (parity with no_drop.rs:58).
    if depth > 8 {
        return false;
    }
    match ty.kind() {
        // Leaf set: never owns Drop glue.
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Ref(..)
            | RigidTy::RawPtr(..)
            | RigidTy::FnPtr(..)
            | RigidTy::FnDef(..)
            | RigidTy::Never
            | RigidTy::Str,
        ) => true,

        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().all(|e| bmc_drop_benign_rec(*e, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _)) => bmc_drop_benign_rec(elem, depth + 1),
        TyKind::RigidTy(RigidTy::Slice(elem)) => bmc_drop_benign_rec(elem, depth + 1),

        // A closure env is benign iff every captured upvar is benign (covers the
        // contract check/replace closure that captures only `&mut self`).
        TyKind::RigidTy(RigidTy::Closure(_, args)) => bmc_closure_upvars_benign(&args, depth),

        // A coroutine (`async` block / `async fn` body) has no destructor of its
        // own; its glue is the compiler-generated state-machine drop that drops
        // whichever locals are live in the suspended state. Benign iff that glue
        // calls nothing and every place it drops is itself benign.
        TyKind::RigidTy(RigidTy::Coroutine(..)) => bmc_coroutine_drop_is_benign(ty, depth),

        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            use rustc_public::ty::GenericArgKind;
            // Dealloc-only std collections / lock guards: their OWN Drop frees
            // only abstractly-modeled memory or releases a platform lock. But
            // dropping a collection also drops its ELEMENTS, so it is benign
            // only when every element/contained type is itself benign. (Unlike
            // the CHC path, BMC cannot MIR-inline `Vec::drop` to expose the
            // element drops separately — `Vec::drop` MIR is unavailable — so we
            // MUST recurse into the type arguments here, or a
            // `Vec<TypeWithPanickingDrop>` would be unsoundly skipped.)
            let name = def.trimmed_name();
            if matches!(
                name.as_str(),
                "Vec" | "RawVec"
                    | "RawVecInner"
                    // ArrayVec/SmallVec are INLINE owning buffers (no heap): their Drop
                    // only drops the `len` initialized elements, so — exactly like Vec —
                    // they are benign iff every element type is benign. The recursion
                    // below into the type args (the element T) rejects
                    // `ArrayVec<T-with-Drop>`, so a user element side effect is never
                    // silently skipped. (aterm's Parser holds inline ArrayVec<u16/u8>
                    // param buffers; their u16/u8 elements run no Drop.)
                    | "ArrayVec"
                    | "ArrayVecImpl"
                    | "SmallVec"
                    | "HashMap"
                    | "RawTable"
                    | "RawTableInner"
                    | "BTreeMap"
                    | "String"
                    | "VecDeque"
                    | "BTreeSet"
                    | "HashSet"
                    | "BinaryHeap"
                    | "Box"
                    | "Rc"
                    | "Arc"
                    | "Weak"
                    | "Mutex"
                    | "RwLock"
                    | "MutexGuard"
                    | "RwLockReadGuard"
                    | "RwLockWriteGuard"
            ) {
                return args.0.iter().all(|ga| match ga {
                    GenericArgKind::Type(t) => bmc_drop_benign_rec(*t, depth + 1),
                    _ => true,
                });
            }
            // Unresolved generic params would ICE resolve_drop_in_place (#3942).
            if mono_ty::has_unresolved_params(ty) {
                return false;
            }
            // A non-empty shim is acceptable ONLY when it is pure compiler
            // field-glue (no user `Drop` impl, no un-allowlisted dealloc): then
            // the type is benign iff every field is benign (checked by the field
            // recursion below). A shim that `Call`s a real `Drop::drop` or an
            // un-modeled deallocator stays conservatively demoted — fail-closed.
            //
            // Without this, a plain user struct/enum that merely *owns* a benign
            // field with drop glue (e.g. PB's `PbConstraint { terms: Vec<PbTerm>,
            // .. }` / `PbObjective { terms: Vec<PbTerm> }`) has a non-empty shim
            // and was demoted, even though BMC skips the drop identically to the
            // benign `Vec` case. CHC reaches the same types via MIR drop
            // elaboration (no_drop.rs:238); BMC cannot inline the glue, so it must
            // recurse the field types here instead. Part of #3017/G2 follow-up.
            if !bmc_drop_glue_is_empty(ty) && !bmc_adt_drop_is_field_glue_only(ty) {
                return false;
            }
            def.variants().iter().all(|variant| {
                variant.fields().iter().all(|f| {
                    // Rule A (`shared::mono_ty`): the field's type at the ADT's
                    // own arguments, or not benign.
                    mono_ty::field_ty(f, &args)
                        .is_some_and(|resolved| bmc_drop_benign_rec(resolved, depth + 1))
                })
            })
        }

        _ => false,
    }
}

/// Benign iff every captured upvar type is benign. Upvar tuple layout mirrors
/// `no_drop.rs` / `codegen_types.rs`: the `Tuple` after the `FnPtr` arg, else
/// the last `Tuple` in the closure's generic args.
fn bmc_closure_upvars_benign(args: &rustc_public::ty::GenericArgs, depth: usize) -> bool {
    use rustc_public::ty::GenericArgKind;
    let upvar_tys: Option<Vec<rustc_public::ty::Ty>> = args
        .0
        .iter()
        .enumerate()
        .find_map(|(pos, arg)| {
            if matches!(arg, GenericArgKind::Type(ty)
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_))))
            {
                match args.0.get(pos + 1) {
                    Some(GenericArgKind::Type(ty)) => match ty.kind() {
                        TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                        _ => None,
                    },
                    _ => None,
                }
            } else {
                None
            }
        })
        .or_else(|| {
            args.0.iter().rev().find_map(|arg| match arg {
                GenericArgKind::Type(ty) => match ty.kind() {
                    TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                    _ => None,
                },
                _ => None,
            })
        });
    match upvar_tys {
        Some(tys) => tys.iter().all(|t| bmc_drop_benign_rec(*t, depth + 1)),
        None => true,
    }
}

/// Part of #3945: hashbrown internal types (Bucket, RawTable, RawTableInner,
/// etc.) leak through drop glue when HashMap stubs are active. Their Drop
/// impls are not modeled by BMC, but recording `unsupported_with_fallback`
/// would poison the verdict for the entire harness. Treat these drops as
/// no-ops — the HashMap is fully abstracted by CHC stubs.
fn bmc_ty_is_hashbrown(ty: rustc_public::ty::Ty) -> bool {
    if let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() {
        let name = def.0.name();
        name.contains("hashbrown::raw::")
            || name.contains("hashbrown::map::")
            || name.contains("hashbrown::set::")
    } else {
        false
    }
}

/// Fully-qualified paths of stdlib owning containers whose `Drop` glue — given
/// drop-irrelevant element/parameter types — has no observable value-level
/// effect beyond freeing heap memory. The BMC value model does not track the
/// allocator, so deallocation is invisible; the terminator handler already
/// *skips* the drop, and for these the skip is observationally exact (#3017).
///
/// Matching is by qualified name (the same mechanism as `bmc_ty_is_hashbrown`).
/// The element/allocator types are checked separately for drop-irrelevance, so
/// e.g. `Vec<T>` only qualifies when `T` itself runs no user `Drop`.
fn bmc_container_drop_is_dealloc_only_by_name(name: &str) -> bool {
    name.starts_with("alloc::vec::Vec")
        || name.starts_with("alloc::string::String")
        || name.starts_with("alloc::boxed::Box")
        || name.starts_with("alloc::collections::vec_deque::VecDeque")
        || name.starts_with("alloc::raw_vec::RawVec")
}

/// True when dropping `ty` runs **no user `Drop` impl** anywhere in its
/// transitive structure — the drop's only effect is heap deallocation, which is
/// invisible to the BMC value model. Skipping such a drop (already done by the
/// `Drop` terminator) is then observationally exact, so it need not demote the
/// verdict via `unsupported_with_fallback`.
///
/// SOUNDNESS: this is the predicate that lets a skipped drop NOT poison a clean
/// PROOF. It must be CONSERVATIVE — any type it cannot *positively* prove
/// dealloc-only falls through to the demoting path (the prior, sound behavior).
/// A `Vec<T>`/`Box<T>` whose `T` carries a user `Drop` is correctly rejected
/// here (its `T`-drops are real side effects the skip would silently lose).
/// Recursion is bounded by the monomorphized type structure (finite); any
/// non-container bottoms out immediately, so self-referential types via `Box`
/// terminate at the first user struct (returning `false`, i.e. demote).
fn bmc_ty_drop_is_dealloc_only(ty: rustc_public::ty::Ty) -> bool {
    if mono_ty::has_unresolved_params(ty) {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            bmc_container_drop_is_dealloc_only_by_name(&def.0.name())
                && args.0.iter().all(|arg| match arg {
                    // Every type parameter (element T, allocator A, …) must itself
                    // run no user Drop; otherwise that drop is a real side effect.
                    rustc_public::ty::GenericArgKind::Type(t) => bmc_ty_drop_is_irrelevant(*t),
                    // Lifetimes carry no drop; const params carry no drop glue.
                    _ => true,
                })
        }
        _ => false,
    }
}

/// A type whose drop has no observable value-level effect: a trivially-undroppable
/// scalar/pointer, a type with no drop glue at all, or itself a dealloc-only
/// owning container. Conservative by construction (built from the conservative
/// `bmc_ty_trivially_no_drop` / `bmc_drop_glue_is_empty` / dealloc-only checks).
fn bmc_ty_drop_is_irrelevant(ty: rustc_public::ty::Ty) -> bool {
    bmc_ty_trivially_no_drop(ty) || bmc_drop_glue_is_empty(ty) || bmc_ty_drop_is_dealloc_only(ty)
}

/// `obligation_free_walk::instance_may_loop`, cached per instance for a unit
/// that stubs nothing (a stubbed unit walks every time).
fn bmc_instance_may_loop_cached(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    instance: rustc_public::mir::mono::Instance,
    stubs: &crate::codegen_ay::obligation_free_walk::StubMap,
) -> bool {
    thread_local! {
        static LOOPS: std::cell::RefCell<std::collections::HashMap<String, bool>> =
            std::cell::RefCell::new(std::collections::HashMap::new());
    }
    if !stubs.is_empty() {
        return crate::codegen_ay::obligation_free_walk::instance_may_loop(tcx, instance, stubs);
    }
    let key = instance.mangled_name();
    if let Some(cached) = LOOPS.with(|loops| loops.borrow().get(&key).copied()) {
        return cached;
    }
    let may_loop = crate::codegen_ay::obligation_free_walk::instance_may_loop(tcx, instance, stubs);
    LOOPS.with(|loops| loops.borrow_mut().insert(key, may_loop));
    may_loop
}

/// `len * per` without wrapping: past the pointer width the count is the
/// most a loop can run.
fn scaled_len(len: Expr, per: u64, pointer: u32) -> Expr {
    if per == 1 {
        return len;
    }
    let per = Expr::bitvec_const(per, pointer);
    let max = Expr::bitvec_const(u64::MAX, pointer);
    Expr::ite(len.clone().bvugt(max.clone().bvudiv(per.clone())), max, len.bvmul(per))
}

/// Is `ty` a container whose kani `bounded_any::<N>` runs only loops of at most
/// `N` passes: `String`, or `Vec<P>` / `Box<[P]>` of a primitive `P`?
fn bounded_any_container_is_loop_bounded(ty: rustc_public::ty::Ty) -> bool {
    let primitive = |ty: rustc_public::ty::Ty| {
        matches!(
            ty.kind(),
            TyKind::RigidTy(
                RigidTy::Bool
                    | RigidTy::Char
                    | RigidTy::Int(_)
                    | RigidTy::Uint(_)
                    | RigidTy::Float(_)
            )
        )
    };
    let first_type_arg = |args: &rustc_public::ty::GenericArgs| {
        args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = rustc_public::CrateDef::name(&def);
            if name == "std::string::String" || name == "alloc::string::String" {
                return true;
            }
            if name == "std::vec::Vec" || name == "alloc::vec::Vec" {
                return first_type_arg(&args).is_some_and(primitive);
            }
            if name == "std::boxed::Box" || name == "alloc::boxed::Box" {
                return first_type_arg(&args).is_some_and(|inner| {
                    matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(elem)) if primitive(elem))
                });
            }
            false
        }
        _ => false,
    }
}
