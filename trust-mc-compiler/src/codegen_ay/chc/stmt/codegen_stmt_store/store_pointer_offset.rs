// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The constant byte offset of a store pointer from the start of its ref
//! target's referent, read off the pointer's MIR definition chain.
//!
//! A `RefTarget` names the referent but not where in it the pointer points:
//! `p.byte_add(3)`, `p.byte_offset(2)` and `p.cast::<u8>().byte_add(1)` inherit
//! the whole referent from `p` through several propagation routes (the pointer
//! identity callees, an object id's owning local), none of which records the
//! byte step. A narrower store through such a pointer was spliced into the
//! referent's FIRST bytes: `*(&mut x as *mut u32 as *mut u8).byte_add(3) = 0`
//! cleared `x`'s low byte, so `assert!(x == 0x1111_1100)` was a clean proof
//! where Kani fails it (third review of fix/chc-false-certificates,
//! 2026-09-27: `ns_byte_add_bug`, `of_byte_add_store_bug`, `o2_byte_sub_bug`).
//!
//! [`ChcCtx::store_pointer_referent_byte_offset`] answers only from the body:
//! every hop must be the pointer local's ONE definition, and the chain must end
//! at a borrow or raw address of exactly the ref target's place. Anything it
//! does not recognise — a parameter, a second definition, a symbolic count, a
//! call it does not know, a pointer loaded from memory — is `None`, and the
//! caller fails closed.

use rustc_public::mir::{
    AggregateKind, BinOp, CastKind, Operand, Place, PointerCoercion, ProjectionElem, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};

use super::super::{ChcCtx, RefTarget};

/// The unsigned integer a constant operand holds, read through the
/// constant-pointer rule (`shared/const_pointer.rs`): relocated bytes are
/// never data, so a pointer constant is `None` and the caller fails closed.
fn const_operand_uint(operand: &Operand) -> Option<u128> {
    let Operand::Constant(const_op) = operand else { return None };
    crate::codegen_ay::shared::const_pointer::const_uint(&const_op.const_)
}

/// `value` as the integer type `ty` holds it: wrapped to its width, read
/// signed for a signed type. `None` for a non-integer type.
fn wrap_to_int_ty(value: i128, ty: Ty) -> Option<i128> {
    use rustc_public::ty::{IntTy, UintTy};
    let (bits, signed): (u32, bool) = match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int)) => (
            match int {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 | IntTy::Isize => 64,
                IntTy::I128 => 128,
            },
            true,
        ),
        TyKind::RigidTy(RigidTy::Uint(uint)) => (
            match uint {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 | UintTy::Usize => 64,
                UintTy::U128 => 128,
            },
            false,
        ),
        TyKind::RigidTy(RigidTy::Bool) => (1, false),
        _ => return None,
    };
    if bits >= 128 {
        return Some(value);
    }
    let modulus = 1i128 << bits;
    let wrapped = value.rem_euclid(modulus);
    Some(if signed && wrapped >= modulus / 2 { wrapped - modulus } else { wrapped })
}

/// Longest definition chain followed before giving up.
const MAX_CHAIN: usize = 64;

/// One whole-local definition of a pointer local.
enum PointerDef<'a> {
    Rvalue(&'a Rvalue),
    Call { func: &'a Operand, args: &'a [Operand] },
}

/// How a pointer-arithmetic callee moves its first argument.
enum OffsetCallee {
    /// Same address (`cast`, `cast_mut`, slice `as_ptr`, `from_ref`, ...).
    Identity,
    /// `count` bytes, unsigned forward (`byte_add`, `wrapping_byte_add`).
    BytesForward,
    /// `count` bytes, unsigned backward (`byte_sub`, `wrapping_byte_sub`).
    BytesBackward,
    /// `count` bytes, signed (`byte_offset`, `wrapping_byte_offset`).
    BytesSigned,
    /// `count` elements of the pointee, unsigned forward (`add`, `wrapping_add`).
    ElemsForward,
    /// `count` elements, unsigned backward (`sub`, `wrapping_sub`).
    ElemsBackward,
    /// `count` elements, signed (`offset`, `wrapping_offset`).
    ElemsSigned,
    /// The `offset` intrinsic (or Kani's model of it, which the inlined
    /// `add` / `byte_add` bodies call): `count` elements of the pointee,
    /// signed when the count is an `isize`.
    IntrinsicOffset,
}

fn classify_offset_callee(path: &str) -> Option<OffsetCallee> {
    if path.contains("rustc_intrinsics::offset") || path.contains("intrinsics::offset") {
        return Some(OffsetCallee::IntrinsicOffset);
    }
    // The raw-pointer method modules (`core::ptr::const_ptr::<impl *const T>`,
    // `mut_ptr::`), not any path containing the substring: `Vec::as_mut_ptr`
    // contains "mut_ptr" and returns the heap buffer's address, not the
    // address of the `&mut v` it takes. Read as an identity hop, a copy through
    // it resolved to the Vec local's own storage at offset 0 and spliced the
    // copied bytes into the Vec handle while `v[0]` kept its old value: a clean
    // proof where Kani fails the program, and a certified false counterexample
    // for its safe twin (self-review of round 10 of
    // fix/chc-false-certificates, probes `q_typed.rs` ty02, ty03; the same on
    // main f5dfb8d48).
    let raw_ptr_method = path.contains("const_ptr::") || path.contains("mut_ptr::");
    let method = path.rsplit("::").next()?;
    // A method name may carry turbofish arguments in some paths (`cast::<u8>`).
    let method = method.split('<').next()?;
    if raw_ptr_method {
        return match method {
            "cast" | "cast_mut" | "cast_const" | "as_ptr" | "as_mut_ptr" => {
                Some(OffsetCallee::Identity)
            }
            "byte_add" | "wrapping_byte_add" => Some(OffsetCallee::BytesForward),
            "byte_sub" | "wrapping_byte_sub" => Some(OffsetCallee::BytesBackward),
            "byte_offset" | "wrapping_byte_offset" => Some(OffsetCallee::BytesSigned),
            "add" | "wrapping_add" => Some(OffsetCallee::ElemsForward),
            "sub" | "wrapping_sub" => Some(OffsetCallee::ElemsBackward),
            "offset" | "wrapping_offset" => Some(OffsetCallee::ElemsSigned),
            _ => None,
        };
    }
    // `<[T]>::as_ptr` / `as_mut_ptr`: the first element's address, which is the
    // slice's (and, through the unsizing borrow, the array's) own.
    if path.contains("slice") && matches!(method, "as_ptr" | "as_mut_ptr") {
        return Some(OffsetCallee::Identity);
    }
    // `ptr::from_ref` / `from_mut` / `addr_of!` helpers: the reference's address.
    // `ptr::from_raw_parts{,_mut}(data, meta)`: the data pointer's address (the
    // inlined `byte_add` rebuilds its result this way, `with_metadata_of`).
    if (path.starts_with("core::ptr::") || path.starts_with("std::ptr::"))
        && matches!(method, "from_ref" | "from_mut" | "from_raw_parts" | "from_raw_parts_mut")
    {
        return Some(OffsetCallee::Identity);
    }
    None
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The blocks reachable from the entry, following a `switchInt` on a
    /// CONSTANT only to the target it selects: the inlined `<*T>::sub` is `if
    /// T::IS_ZST { self } else { offset(self, -count) }` over the constant
    /// `false`, and its dead `self` arm is a second definition of the result.
    fn chain_reachable_blocks(&self) -> Vec<bool> {
        let blocks = &self.body.blocks;
        let mut reachable = vec![false; blocks.len()];
        let mut stack = vec![0usize];
        while let Some(bb) = stack.pop() {
            if bb >= blocks.len() || reachable[bb] {
                continue;
            }
            reachable[bb] = true;
            let terminator = &blocks[bb].terminator;
            if let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind
                && let Some(value) = const_operand_uint(discr)
            {
                let target = targets
                    .branches()
                    .find(|(branch, _)| *branch == value)
                    .map(|(_, target)| target)
                    .unwrap_or_else(|| targets.otherwise());
                stack.push(target);
                continue;
            }
            stack.extend(terminator.successors());
        }
        reachable
    }

    /// The one whole-local definition of `local` in a reachable block, or
    /// `None` when it has none (an argument), more than one, or a partial
    /// write.
    fn sole_pointer_definition(
        &self,
        local: usize,
        reachable: &[bool],
    ) -> Option<PointerDef<'body>> {
        let body: &'body rustc_public::mir::Body = self.body;
        // A write THROUGH the pointer (`(*local) = v`) writes its pointee, not
        // the local.
        let writes_local = |place: &Place| {
            place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        };
        let mut found: Option<PointerDef<'body>> = None;
        for (bb, block) in body.blocks.iter().enumerate() {
            if !reachable.get(bb).copied().unwrap_or(true) {
                continue;
            }
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rhs) if writes_local(lhs) => {
                        if !lhs.projection.is_empty() || found.is_some() {
                            return None;
                        }
                        found = Some(PointerDef::Rvalue(rhs));
                    }
                    StatementKind::SetDiscriminant { place, .. } if writes_local(place) => {
                        return None;
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. }
                    if writes_local(destination) =>
                {
                    if !destination.projection.is_empty() || found.is_some() {
                        return None;
                    }
                    found = Some(PointerDef::Call { func, args: args.as_slice() });
                }
                TerminatorKind::InlineAsm { .. } => return None,
                _ => {}
            }
        }
        found
    }

    /// Whether the pointer local `local` may be written through a pointer to
    /// it, which no count of its MIR definitions sees: its own storage is
    /// borrowed (shared or mutably) or taken by raw address somewhere in the
    /// body.
    ///
    /// A `&raw const` of the local whose every use is an argument of Kani's
    /// shadow-memory bookkeeping (`kani::mem_init::*`, which `-Z uninit-checks`
    /// inserts after each pointer assignment) reads the local's initialization
    /// state and writes nothing to it: counting it made every pointer of an
    /// instrumented body chain-less, and their copies left the tracked path
    /// (`uninit/copy/read_after_copy.rs` lost its Genuine verdict).
    fn pointer_local_written_indirectly(&self, local: usize) -> bool {
        // A borrow of the local's own storage, not of its pointee (`&raw mut
        // (*local)` names the pointee's address and leaves `local` alone).
        let own = |place: &Place| {
            place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        };
        self.body.blocks.iter().flat_map(|b| b.statements.iter()).any(|stmt| match &stmt.kind {
            StatementKind::Assign(dest, Rvalue::AddressOf(mutability, place)) if own(place) => {
                !(matches!(mutability, rustc_public::mir::RawPtrKind::Const)
                    && dest.projection.is_empty()
                    && self.local_used_only_by_shadow_memory(dest.local))
            }
            StatementKind::Assign(_, Rvalue::Ref(_, _, place)) => own(place),
            _ => false,
        })
    }

    /// Whether every mention of `local` after its definition is an argument of
    /// a call into `kani::mem_init`.
    fn local_used_only_by_shadow_memory(&self, local: usize) -> bool {
        use rustc_public::mir::visit::{
            Location, MirVisitor, PlaceContext, statement_location, terminator_location,
        };
        struct Mentions(usize, usize);
        impl MirVisitor for Mentions {
            fn visit_local(
                &mut self,
                l: &rustc_public::mir::Local,
                _ptx: PlaceContext,
                _location: Location,
            ) {
                if *l == self.0 {
                    self.1 += 1;
                }
            }
        }
        let body: &rustc_public::mir::Body = self.body;
        for (bb, block) in body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let mut m = Mentions(local, 0);
                m.visit_statement(stmt, statement_location(body, &bb, si));
                let is_definition = matches!(&stmt.kind,
                    StatementKind::Assign(dest, Rvalue::AddressOf(..))
                        if dest.local == local && dest.projection.is_empty());
                let is_storage = matches!(
                    &stmt.kind,
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
                );
                if m.1 > 0 && !is_definition && !is_storage {
                    return false;
                }
            }
            let mut m = Mentions(local, 0);
            m.visit_terminator(&block.terminator, terminator_location(body, &bb));
            if m.1 == 0 {
                continue;
            }
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
                return false;
            };
            let in_args = args.iter().any(|a| {
                matches!(a, Operand::Copy(p) | Operand::Move(p)
                    if p.local == local && p.projection.is_empty())
            });
            if destination.local == local
                || !in_args
                || !self.resolve_callee_path(func).is_some_and(|path| path.contains("mem_init::"))
            {
                return false;
            }
        }
        true
    }

    /// The integer an operand holds, when the body makes it a constant: a
    /// constant, or a local whose one reachable definition copies, casts, adds,
    /// subtracts or multiplies such constants (the inlined `sub` negates its
    /// count, `SubUnchecked(0_isize, count as isize)`). Signed types read
    /// signed.
    fn chain_const_int(&self, operand: &Operand, reachable: &[bool], depth: usize) -> Option<i128> {
        if depth > 16 {
            return None;
        }
        let ty = operand.ty(self.body.locals()).ok().map(|ty| self.resolve_body_ty(ty));
        match operand {
            Operand::Constant(_) => {
                let raw = const_operand_uint(operand)?;
                wrap_to_int_ty(i128::try_from(raw).ok()?, ty?)
            }
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                let arg_count = self.body.arg_locals().len();
                if place.local == 0 || place.local <= arg_count {
                    return None;
                }
                let value = match self.sole_pointer_definition(place.local, reachable)? {
                    PointerDef::Rvalue(Rvalue::Use(inner, ..)) => {
                        self.chain_const_int(inner, reachable, depth + 1)?
                    }
                    PointerDef::Rvalue(Rvalue::Cast(CastKind::IntToInt, inner, _)) => {
                        self.chain_const_int(inner, reachable, depth + 1)?
                    }
                    // `!3` (a tag mask, `map_addr(|a| a & !3)`): the bitwise
                    // complement, wrapped into the type below.
                    PointerDef::Rvalue(Rvalue::UnaryOp(rustc_public::mir::UnOp::Not, inner)) => {
                        !self.chain_const_int(inner, reachable, depth + 1)?
                    }
                    PointerDef::Rvalue(Rvalue::BinaryOp(op, a, b)) => {
                        let a = self.chain_const_int(a, reachable, depth + 1)?;
                        let b = self.chain_const_int(b, reachable, depth + 1)?;
                        match op {
                            BinOp::Add | BinOp::AddUnchecked => a.checked_add(b)?,
                            BinOp::Sub | BinOp::SubUnchecked => a.checked_sub(b)?,
                            BinOp::Mul | BinOp::MulUnchecked => a.checked_mul(b)?,
                            _ => return None,
                        }
                    }
                    _ => return None,
                };
                wrap_to_int_ty(value, ty?)
            }
            _ => None,
        }
    }

    /// [`Self::chain_const_int`] over the body's reachable blocks: the integer
    /// `operand` holds on every execution, when its single definitions make it
    /// a constant.
    pub(in crate::codegen_ay::chc) fn body_constant_int(&self, operand: &Operand) -> Option<i128> {
        let reachable = self.chain_reachable_blocks();
        self.chain_const_int(operand, &reachable, 0)
    }

    /// Size in bytes of the pointee of a raw pointer or reference type.
    fn chain_pointee_size(&self, ptr_ty: Ty) -> Option<i128> {
        let pointee = match self.resolve_body_ty(ptr_ty).kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        };
        let size = self.resolve_body_ty(pointee).layout().ok()?.shape().size.bytes();
        i128::try_from(size).ok()
    }

    /// The byte offset `count` elements or bytes move a pointer of type
    /// `ptr_ty`, by `kind`.
    fn chain_step(
        &self,
        kind: &OffsetCallee,
        ptr_ty: Ty,
        count: &Operand,
        reachable: &[bool],
    ) -> Option<i128> {
        let value = self.chain_const_int(count, reachable, 0)?;
        // Counts are `usize`/`isize`: the low 64 bits, read unsigned or signed.
        let bits = (value as u128) & u128::from(u64::MAX);
        let unsigned = i128::try_from(bits).ok()?;
        let signed = i128::from(bits as u64 as i64);
        let elem = || self.chain_pointee_size(ptr_ty);
        match kind {
            OffsetCallee::Identity => Some(0),
            OffsetCallee::BytesForward => Some(unsigned),
            OffsetCallee::BytesBackward => Some(-unsigned),
            OffsetCallee::BytesSigned => Some(signed),
            OffsetCallee::ElemsForward => unsigned.checked_mul(elem()?),
            OffsetCallee::ElemsBackward => unsigned.checked_mul(elem()?).map(|b| -b),
            OffsetCallee::ElemsSigned => signed.checked_mul(elem()?),
            OffsetCallee::IntrinsicOffset => {
                let count_is_signed = count.ty(self.body.locals()).ok().is_some_and(|ty| {
                    matches!(self.resolve_body_ty(ty).kind(), TyKind::RigidTy(RigidTy::Int(_)))
                });
                (if count_is_signed { signed } else { unsigned }).checked_mul(elem()?)
            }
        }
    }

    /// The pointer local an operand of a definition chain names: a whole local,
    /// or a field of a tuple or struct local whose one definition in a
    /// reachable block is the aggregate that built it (`(p.byte_add(2),).0`,
    /// `S { p: q }.p`), followed to the operand stored there. A local whose
    /// own storage is borrowed or written in part is no answer.
    fn chain_operand_local(&self, op: &Operand, reachable: &[bool]) -> Option<usize> {
        let mut op = op.clone();
        for _ in 0..8 {
            let (Operand::Copy(place) | Operand::Move(place)) = &op else { return None };
            match place.projection.as_slice() {
                [] => return Some(place.local),
                [ProjectionElem::Field(idx, _)] => {
                    let (kind, ops) = self.chain_aggregate_definition(place.local, reachable)?;
                    match kind {
                        AggregateKind::Tuple | AggregateKind::Closure(..) => {}
                        AggregateKind::Adt(def, variant, _, _, None)
                            if def.kind() == rustc_public::ty::AdtKind::Struct
                                && crate::rustc_public_bridge::IndexedVal::to_index(variant)
                                    == 0 => {}
                        _ => return None,
                    }
                    op = ops.get(*idx)?.clone();
                }
                _ => return None,
            }
        }
        None
    }

    /// The aggregate that built the tuple, struct or closure local `local`
    /// whole: its one definition in a reachable block, through whole copies and
    /// moves of the local and Kani's contract wrappers `kani_force_fn_once` /
    /// `kani_force_fn_once_with_args`, which return their closure argument
    /// unchanged. A closure's fields are its captures, in the aggregate's
    /// operand order, so `(c.0)` of `c = {closure}(&mut p.a)` is that
    /// reference: a contract's `copy_nonoverlapping(&src, &mut p.a, 1)` runs
    /// in a closure that captured `&mut p.a`, and without this hop its
    /// destination had no chain and the copy took the demoting fallback
    /// (`negative/modifies_frame_variants.rs` `copy_nonoverlapping_inside_safe`,
    /// a measured cost of the fourth review's chain-less copy refusal). Every
    /// local on the way must be a body local whose storage is never borrowed.
    fn chain_aggregate_definition(
        &self,
        local: usize,
        reachable: &[bool],
    ) -> Option<(&'body AggregateKind, &'body [Operand])> {
        let arg_count = self.body.arg_locals().len();
        let mut local = local;
        for _ in 0..8 {
            if local == 0 || local <= arg_count || self.pointer_local_written_indirectly(local) {
                return None;
            }
            match self.sole_pointer_definition(local, reachable)? {
                PointerDef::Rvalue(Rvalue::Aggregate(kind, ops)) => {
                    return Some((kind, ops.as_slice()));
                }
                PointerDef::Rvalue(Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..))
                    if src.projection.is_empty() =>
                {
                    local = src.local;
                }
                PointerDef::Call { func, args } => {
                    let path = self.resolve_callee_path(func)?;
                    let name = path.rsplit("::").next().unwrap_or(&path);
                    let name = name.split('<').next().unwrap_or(name);
                    if !matches!(name, "kani_force_fn_once" | "kani_force_fn_once_with_args") {
                        return None;
                    }
                    let [Operand::Copy(src) | Operand::Move(src)] = args else { return None };
                    if !src.projection.is_empty() {
                        return None;
                    }
                    local = src.local;
                }
                _ => return None,
            }
        }
        None
    }

    /// The constant byte offset of the pointer `ptr_local` from the start of
    /// `ref_target`'s referent place, when the pointer's definition chain in
    /// this body establishes one (module documentation); `None` otherwise.
    pub(in crate::codegen_ay::chc) fn store_pointer_referent_byte_offset(
        &self,
        ptr_local: usize,
        ref_target: &RefTarget,
    ) -> Option<i128> {
        let found = self.store_pointer_referent_byte_offset_walk(ptr_local, ref_target);
        tracing::debug!(
            ptr_local,
            ?ref_target,
            ?found,
            "store pointer offset from its definition chain"
        );
        found
    }

    fn store_pointer_referent_byte_offset_walk(
        &self,
        ptr_local: usize,
        ref_target: &RefTarget,
    ) -> Option<i128> {
        let target_place =
            Place { local: ref_target.local, projection: ref_target.projections.clone() };
        let arg_count = self.body.arg_locals().len();
        let n_locals = self.body.locals().len();
        let reachable = self.chain_reachable_blocks();
        let mut cur = ptr_local;
        let mut offset: i128 = 0;
        for _ in 0..MAX_CHAIN {
            if cur == 0 || cur <= arg_count || cur >= n_locals {
                return None;
            }
            if self.pointer_local_written_indirectly(cur) {
                return None;
            }
            let next_local = |op: &Operand| self.chain_operand_local(op, &reachable);
            match self.sole_pointer_definition(cur, &reachable)? {
                PointerDef::Rvalue(rvalue) => match rvalue {
                    Rvalue::Use(op, ..) => cur = next_local(op)?,
                    Rvalue::Cast(kind, op, _) => {
                        match kind {
                            CastKind::PtrToPtr
                            | CastKind::PointerCoercion(
                                PointerCoercion::MutToConstPointer
                                | PointerCoercion::ArrayToPointer
                                | PointerCoercion::Unsize,
                            ) => {}
                            _ => return None,
                        }
                        cur = next_local(op)?;
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        if *place == target_place {
                            return Some(offset);
                        }
                        // A reborrow or raw address of a pointer's pointee
                        // (`&raw mut (*r)`, `&mut (*r)`): the same address as `r`.
                        match place.projection.as_slice() {
                            [ProjectionElem::Deref] => cur = place.local,
                            // `&mut (*r).f`: field path `f` of `r`'s referent. It is
                            // the target place when `r`'s own chain reaches the
                            // target's place without `f` at offset 0, and `f`
                            // completes it (`&mut p.a` of a parameter
                            // `p: &mut Pair`, inlined).
                            [ProjectionElem::Deref, rest @ ..]
                                if rest.iter().all(|p| matches!(p, ProjectionElem::Field(..))) =>
                            {
                                let n = ref_target.projections.len();
                                if rest.len() > n || ref_target.projections[n - rest.len()..] != *rest {
                                    return None;
                                }
                                let prefix = RefTarget {
                                    local: ref_target.local,
                                    projections: ref_target.projections[..n - rest.len()].to_vec(),
                                };
                                return (self.store_pointer_referent_byte_offset_walk(
                                    place.local,
                                    &prefix,
                                ) == Some(0))
                                .then_some(offset);
                            }
                            _ => return None,
                        }
                    }
                    Rvalue::BinaryOp(BinOp::Offset, ptr, count) => {
                        let ptr_ty = ptr.ty(self.body.locals()).ok()?;
                        offset = offset.checked_add(self.chain_step(
                            &OffsetCallee::ElemsSigned,
                            ptr_ty,
                            count,
                            &reachable,
                        )?)?;
                        cur = next_local(ptr)?;
                    }
                    // A thin pointer rebuilt from its data pointer and `()`
                    // metadata (`from_raw_parts`, `with_metadata_of` inlined).
                    Rvalue::Aggregate(AggregateKind::RawPtr(..), ops) if ops.len() == 2 => {
                        cur = next_local(&ops[0])?;
                    }
                    _ => return None,
                },
                PointerDef::Call { func, args } => {
                    let path = self.resolve_callee_path(func)?;
                    let kind = classify_offset_callee(&path)?;
                    let first = args.first()?;
                    let step = match kind {
                        OffsetCallee::Identity => 0,
                        _ => {
                            let ptr_ty = first.ty(self.body.locals()).ok()?;
                            self.chain_step(&kind, ptr_ty, args.get(1)?, &reachable)?
                        }
                    };
                    offset = offset.checked_add(step)?;
                    cur = next_local(first)?;
                }
            }
        }
        None
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether the element offset metadata (`subslice_offset`) of the store
    /// pointer `ptr_local` into an array of `elem_bytes`-byte elements can be
    /// trusted: its definition chain in this body reaches `ref_target`'s place
    /// through identity hops and ELEMENT steps (`add`, `sub`, `offset`, the
    /// `offset` intrinsic) of pointers to `elem_bytes`-byte pointees only, and,
    /// when the counts and the metadata are constants, the steps sum to
    /// `tracked_elems`.
    ///
    /// The metadata counts element steps from a pointer it takes to be at the
    /// target's start. A byte step drops it, so an element step after one
    /// counted from the wrong place: `p.byte_add(2).add(1)` on a `*mut u16`
    /// into a `[u16; 4]` recorded element 1 and wrote there, where the store
    /// writes element 2 (fourth review of fix/chc-false-certificates,
    /// 2026-09-28: `eo_byte_add_then_add_bug` a clean proof and its safe twin a
    /// certified false counterexample, on main and the branch). So did a step
    /// of a pointer cast to another pointee (`eo_add_cast_add_safe`). A chain
    /// the walk cannot follow (a parameter, a field, two definitions) proves
    /// nothing about the steps before it.
    pub(in crate::codegen_ay::chc) fn element_offset_metadata_agrees(
        &self,
        ptr_local: usize,
        ref_target: &RefTarget,
        elem_bytes: i128,
        tracked_elems: Option<i128>,
    ) -> bool {
        let found = self.element_offset_chain(ptr_local, ref_target, elem_bytes);
        tracing::debug!(
            ptr_local,
            ?ref_target,
            elem_bytes,
            ?tracked_elems,
            ?found,
            "element store offset metadata against its definition chain"
        );
        match found {
            None => false,
            Some(chain) => match (chain, tracked_elems) {
                (Some(steps), Some(tracked)) => steps == tracked,
                _ => true,
            },
        }
    }

    /// The element steps from `ref_target`'s place to `ptr_local` — `Some(n)`
    /// when every count is a constant, `Some(None)` when a count is not — or
    /// `None` when the chain is not only identity hops and element steps of
    /// `elem_bytes`-byte pointees ending at that place.
    fn element_offset_chain(
        &self,
        ptr_local: usize,
        ref_target: &RefTarget,
        elem_bytes: i128,
    ) -> Option<Option<i128>> {
        let target_place =
            Place { local: ref_target.local, projection: ref_target.projections.clone() };
        let arg_count = self.body.arg_locals().len();
        let n_locals = self.body.locals().len();
        let reachable = self.chain_reachable_blocks();
        let mut cur = ptr_local;
        let mut elems: Option<i128> = Some(0);
        let next_local = |op: &Operand| self.chain_operand_local(op, &reachable);
        // One element step of the pointer operand `ptr` by `count`, signed or
        // not: its pointee must be an element.
        let step = |ptr: &Operand, count: &Operand, signed: Option<bool>, backward: bool| {
            let ptr_ty = ptr.ty(self.body.locals()).ok()?;
            if self.chain_pointee_size(ptr_ty)? != elem_bytes {
                return None;
            }
            let signed = signed.unwrap_or_else(|| {
                count.ty(self.body.locals()).ok().is_some_and(|ty| {
                    matches!(self.resolve_body_ty(ty).kind(), TyKind::RigidTy(RigidTy::Int(_)))
                })
            });
            Some(self.chain_const_int(count, &reachable, 0).map(|value| {
                let bits = (value as u128) & u128::from(u64::MAX);
                let n = if signed { i128::from(bits as u64 as i64) } else { bits as i128 };
                if backward { -n } else { n }
            }))
        };
        for _ in 0..MAX_CHAIN {
            if cur == 0 || cur <= arg_count || cur >= n_locals {
                return None;
            }
            if self.pointer_local_written_indirectly(cur) {
                return None;
            }
            let moved: Option<i128> = match self.sole_pointer_definition(cur, &reachable)? {
                PointerDef::Rvalue(rvalue) => match rvalue {
                    Rvalue::Use(op, ..) => {
                        cur = next_local(op)?;
                        Some(0)
                    }
                    Rvalue::Cast(kind, op, _) => {
                        match kind {
                            CastKind::PtrToPtr
                            | CastKind::PointerCoercion(
                                PointerCoercion::MutToConstPointer
                                | PointerCoercion::ArrayToPointer
                                | PointerCoercion::Unsize,
                            ) => {}
                            _ => return None,
                        }
                        cur = next_local(op)?;
                        Some(0)
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        if *place == target_place {
                            return Some(elems);
                        }
                        match place.projection.as_slice() {
                            [ProjectionElem::Deref] => {
                                cur = place.local;
                                Some(0)
                            }
                            _ => return None,
                        }
                    }
                    Rvalue::BinaryOp(BinOp::Offset, ptr, count) => {
                        let moved = step(ptr, count, Some(true), false)?;
                        cur = next_local(ptr)?;
                        moved
                    }
                    Rvalue::Aggregate(AggregateKind::RawPtr(..), ops) if ops.len() == 2 => {
                        cur = next_local(&ops[0])?;
                        Some(0)
                    }
                    _ => return None,
                },
                PointerDef::Call { func, args } => {
                    let path = self.resolve_callee_path(func)?;
                    let first = args.first()?;
                    let moved = match classify_offset_callee(&path)? {
                        OffsetCallee::Identity => Some(0),
                        OffsetCallee::ElemsForward => step(first, args.get(1)?, Some(false), false)?,
                        OffsetCallee::ElemsBackward => step(first, args.get(1)?, Some(false), true)?,
                        OffsetCallee::ElemsSigned => step(first, args.get(1)?, Some(true), false)?,
                        OffsetCallee::IntrinsicOffset => step(first, args.get(1)?, None, false)?,
                        OffsetCallee::BytesForward
                        | OffsetCallee::BytesBackward
                        | OffsetCallee::BytesSigned => return None,
                    };
                    cur = next_local(first)?;
                    moved
                }
            };
            elems = match (elems, moved) {
                (Some(total), Some(step)) => total.checked_add(step),
                _ => None,
            };
        }
        None
    }

    /// The local a pointer operand copies, through whole copies and moves.
    fn copied_pointer_root(&self, operand: &Operand, reachable: &[bool]) -> Option<usize> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        let arg_count = self.body.arg_locals().len();
        let mut cur = place.local;
        for _ in 0..MAX_CHAIN {
            if cur == 0 || cur <= arg_count {
                return Some(cur);
            }
            match self.sole_pointer_definition(cur, reachable) {
                Some(PointerDef::Rvalue(Rvalue::Use(
                    Operand::Copy(src) | Operand::Move(src),
                    ..,
                ))) if src.projection.is_empty() => {
                    cur = src.local;
                }
                _ => return Some(cur),
            }
        }
        None
    }

    /// Whether the integer operand `address` is `pointer.addr()` under bitwise
    /// operations with constants that leave its top 16 bits (its region)
    /// alone — `|` or `^` with a constant below 2^48, `&` with a constant whose
    /// top 16 bits are all set — by definitions in this body: the tag
    /// arithmetic of `p.map_addr(|a| a | TAG)` and back. `p.with_addr` of such
    /// an address is never far (heap/stack_address.rs `with_addr_value`).
    pub(in crate::codegen_ay::chc) fn address_keeps_pointer_region(
        &self,
        address: &Operand,
        pointer: &Operand,
    ) -> bool {
        let reachable = self.chain_reachable_blocks();
        let Some(root) = self.copied_pointer_root(pointer, &reachable) else { return false };
        let arg_count = self.body.arg_locals().len();
        let mut operand = address.clone();
        const HIGH16: i128 = 0xFFFF << 48;
        for _ in 0..MAX_CHAIN {
            let (Operand::Copy(place) | Operand::Move(place)) = &operand else { return false };
            if place.local == 0 || place.local <= arg_count {
                return false;
            }
            let (local, field) = match place.projection.as_slice() {
                [] => (place.local, None),
                [ProjectionElem::Field(idx, _)] => (place.local, Some(*idx)),
                _ => return false,
            };
            let Some(def) = self.sole_pointer_definition(local, &reachable) else { return false };
            if let (Some(idx), PointerDef::Rvalue(Rvalue::Aggregate(AggregateKind::Tuple, ops))) =
                (field, &def)
            {
                match ops.get(idx) {
                    Some(op) => operand = op.clone(),
                    None => return false,
                }
                continue;
            }
            if field.is_some() {
                return false;
            }
            match def {
                PointerDef::Rvalue(Rvalue::Use(inner, ..)) => operand = inner.clone(),
                PointerDef::Rvalue(Rvalue::BinaryOp(op, a, b)) => {
                    let (term, constant) = match (
                        self.chain_const_int(&b, &reachable, 0),
                        self.chain_const_int(&a, &reachable, 0),
                    ) {
                        (Some(k), _) => (a, k),
                        (None, Some(k)) => (b, k),
                        _ => return false,
                    };
                    let k = constant & ((1i128 << 64) - 1);
                    let keeps = match op {
                        BinOp::BitOr | BinOp::BitXor => k & HIGH16 == 0,
                        BinOp::BitAnd => k & HIGH16 == HIGH16,
                        _ => false,
                    };
                    if !keeps {
                        return false;
                    }
                    operand = term.clone();
                }
                PointerDef::Rvalue(Rvalue::Cast(CastKind::Transmute, inner, _)) => {
                    return self.copied_pointer_root(&inner, &reachable) == Some(root);
                }
                PointerDef::Call { func, args } => {
                    let Some(path) = self.resolve_callee_path(&func) else { return false };
                    if !path.ends_with("::addr") {
                        return false;
                    }
                    return args
                        .first()
                        .and_then(|arg| self.copied_pointer_root(arg, &reachable))
                        == Some(root);
                }
                _ => return false,
            }
        }
        false
    }

    /// `k` when the integer operand `address` is `pointer.addr() + k` (or
    /// `- k`, or `pointer.addr()` itself) for the same pointer value `pointer`,
    /// by definitions in this body: `p.with_addr(p.addr() + 2)` and the
    /// inlined `p.map_addr(|a| a + 2)` move `p` by 2 bytes and keep its
    /// provenance, whatever the base address is.
    pub(in crate::codegen_ay::chc) fn address_is_pointer_addr_plus(
        &self,
        address: &Operand,
        pointer: &Operand,
    ) -> Option<i128> {
        let reachable = self.chain_reachable_blocks();
        let root = self.copied_pointer_root(pointer, &reachable)?;
        let arg_count = self.body.arg_locals().len();
        let mut operand = address.clone();
        let mut delta: i128 = 0;
        for _ in 0..MAX_CHAIN {
            let (Operand::Copy(place) | Operand::Move(place)) = &operand else { return None };
            if place.local == 0 || place.local <= arg_count {
                return None;
            }
            // `(_t.0)` of an overflow-checked add (`_t = CheckedAdd(x, k)`), or
            // a field of a tuple the body built (the inlined closure's argument
            // tuple in `map_addr`).
            let (local, field) = match place.projection.as_slice() {
                [] => (place.local, None),
                [ProjectionElem::Field(idx, _)] => (place.local, Some(*idx)),
                _ => return None,
            };
            let def = self.sole_pointer_definition(local, &reachable)?;
            if let (Some(idx), PointerDef::Rvalue(Rvalue::Aggregate(AggregateKind::Tuple, ops))) =
                (field, &def)
            {
                operand = ops.get(idx)?.clone();
                continue;
            }
            let through_checked = match field {
                None => false,
                Some(0) => true,
                Some(_) => return None,
            };
            match def {
                PointerDef::Rvalue(Rvalue::Use(inner, ..)) if !through_checked => {
                    operand = inner.clone();
                }
                PointerDef::Rvalue(
                    Rvalue::BinaryOp(op, a, b) | Rvalue::CheckedBinaryOp(op, a, b),
                ) => {
                    let is_checked_tuple =
                        matches!(def, PointerDef::Rvalue(Rvalue::CheckedBinaryOp(..)));
                    if is_checked_tuple != through_checked {
                        return None;
                    }
                    let k = self.chain_const_int(b, &reachable, 0)?;
                    delta = match op {
                        BinOp::Add | BinOp::AddUnchecked => delta.checked_add(k)?,
                        BinOp::Sub | BinOp::SubUnchecked => delta.checked_sub(k)?,
                        _ => return None,
                    };
                    operand = a.clone();
                }
                PointerDef::Rvalue(Rvalue::Cast(CastKind::Transmute, inner, _))
                    if !through_checked =>
                {
                    return (self.copied_pointer_root(inner, &reachable)? == root).then_some(delta);
                }
                PointerDef::Call { func, args } if !through_checked => {
                    let path = self.resolve_callee_path(func)?;
                    if !path.ends_with("::addr") {
                        return None;
                    }
                    return (self.copied_pointer_root(args.first()?, &reachable)? == root)
                        .then_some(delta);
                }
                _ => return None,
            }
        }
        None
    }
}
