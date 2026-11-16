// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Logical Vec mutations do not establish matching physical buffer bytes or
//! allocation size. Taking a new pointer after the mutation does not repair
//! that mismatch. Keep this ordering inside the existing raw-access boundary.

use std::collections::HashSet;

use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use rustc_public::{CrateDef, rustc_internal};

use super::ChcCtx;
use super::vec_buffer_access::{BufferRoot, Site};
use super::vec_buffer_shared_types::VecBufferTypeMemo;
use crate::codegen_ay::stubs::StubKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn vec_callee_is_sysroot_alloc(&self, func: &Operand) -> bool {
        let Ok(ty) = func.ty(self.body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else { return false };
        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(
            self.tcx,
            rustc_internal::internal(self.tcx, def.def_id()),
        )
    }

    pub(super) fn vec_call_initializes_buffer(&self, func: &Operand) -> bool {
        if !self.vec_callee_is_sysroot_alloc(func) {
            return false;
        }
        if matches!(
            self.detect_stub(func),
            Some(
                StubKind::VecNew
                    | StubKind::VecWithCapacity
                    | StubKind::VecFromElem
                    | StubKind::VecFromSlice
                    | StubKind::SliceIntoVec
            )
        ) {
            return true;
        }
        // Native vec! transfers an initialized Box<[T; N]> allocation. Use
        // the same authenticated diagnostic/signature boundary as codegen.
        let Some(TyKind::RigidTy(RigidTy::FnDef(def, args))) =
            func.ty(self.body.locals()).ok().map(|ty| ty.kind())
        else {
            return false;
        };
        let Ok(instance) = Instance::resolve(def, &args) else { return false };
        use crate::codegen_ay::shared::native_box_init::{NativeInitKind, native_init_boundary};
        native_init_boundary(self.tcx, &instance)
            .is_some_and(|boundary| matches!(boundary.kind, NativeInitKind::VecArray))
    }

    pub(super) fn vec_change_before_accessor(
        &self,
        reach: &[HashSet<usize>],
        root: &BufferRoot,
        type_memo: &mut VecBufferTypeMemo,
    ) -> Option<Site> {
        // Include whole-move ancestors: mutate v; let w = v; w.as_ptr().
        // A flow-insensitive alias join may conservatively refuse reinitialized
        // owners; it never removes an existing reason or creates authority.
        let mut aliases = HashSet::from([root.vec_local]);
        loop {
            let before = aliases.len();
            for block in &self.body.blocks {
                for statement in &block.statements {
                    // The accessor may reborrow an owner reference or raw
                    // handle created after the mutation. Follow its origin as
                    // well as moves, rather than stopping at the handle local.
                    if let StatementKind::Assign(
                        lhs,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) = &statement.kind
                        && lhs.projection.is_empty()
                        && aliases.contains(&lhs.local)
                    {
                        aliases.insert(place.local);
                    }
                    if let StatementKind::Assign(lhs, rvalue) = &statement.kind
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs), ..) => {
                                if aliases.contains(&lhs.local) {
                                    aliases.insert(rhs.local);
                                }
                                if rhs.projection.is_empty() && aliases.contains(&rhs.local) {
                                    aliases.insert(lhs.local);
                                }
                            }
                            Rvalue::Aggregate(_, operands) if aliases.contains(&lhs.local) => {
                                // A field-carried owner keeps its history. A
                                // conservative base-local join can refuse an
                                // unrelated sibling field, but cannot erase debt.
                                for operand in operands {
                                    if let Operand::Copy(place) | Operand::Move(place) = operand {
                                        aliases.insert(place.local);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            if before == aliases.len() {
                break;
            }
        }
        self.vec_change_sites(&aliases, true, type_memo).into_iter().find(|at| {
            if at.block == root.call_block {
                at.index < self.body.blocks[root.call_block].statements.len()
            } else {
                reach.get(at.block).is_some_and(|blocks| blocks.contains(&root.call_block))
            }
        })
    }

    /// Only actual collection query stubs, used solely as a receiver. A
    /// mutable slice, arbitrary shared-reference call or drop is not exempt.
    /// String accessors without such a stub remain conservative here.
    pub(super) fn vec_call_only_queries_buffer(
        &self,
        func: &Operand,
        args: &[Operand],
        mentions: &impl Fn(&Operand) -> bool,
    ) -> bool {
        args.first().is_some_and(mentions)
            && !args.iter().skip(1).any(mentions)
            && self.vec_callee_is_sysroot_alloc(func)
            && matches!(
                self.detect_stub(func),
                Some(
                    StubKind::VecAsPtr
                        | StubKind::VecAsMutPtr
                        | StubKind::VecLen
                        | StubKind::VecCapacity
                        | StubKind::VecIsEmpty
                )
            )
    }
}
