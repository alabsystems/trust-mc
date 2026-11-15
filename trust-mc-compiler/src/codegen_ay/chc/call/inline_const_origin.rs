// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded source tracing in the current MIR body's operand namespace.

use super::ChcCtx;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

/// A typed MIR &str constant's byte count, independent of whether its data
/// pointer has an allocation (the valid empty case can be dangling).
pub(super) fn literal_str_byte_len(operand: &Operand) -> Option<usize> {
    let Operand::Constant(value) = operand else { return None };
    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = value.const_.ty().kind() else {
        return None;
    };
    if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
        return None;
    }
    usize::try_from(
        const_pointer::const_bytes(&value.const_)?.stored_word(const_pointer::PTR_BYTES)?,
    )
    .ok()
}

/// An unsized reference carrier can be rebound through a mutable alias without
/// gaining another whole-local definition. Follow only single, unaliased
/// copies/casts until the caller establishes a value from type or constant metadata.
pub(super) fn unaliased_origin<T>(
    ctx: &ChcCtx<'_, '_>,
    input: &Operand,
    known_value: impl Fn(&Operand) -> Option<T>,
) -> Option<T> {
    use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
    let mut input = input;
    for _ in 0..8 {
        if let Some(value) = known_value(input) {
            return Some(value);
        }
        let (Operand::Copy(place) | Operand::Move(place)) = input else { return None };
        let local = place.local;
        if !place.projection.is_empty() || ctx.local_has_multiple_whole_definitions(local) {
            return None;
        }
        let mut source = None;
        for block in &ctx.body.blocks {
            for statement in &block.statements {
                let StatementKind::Assign(lhs, value) = &statement.kind else { continue };
                if matches!(value, Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) if borrowed.local == local)
                {
                    return None;
                }
                if lhs.local == local {
                    if !lhs.projection.is_empty() || source.is_some() {
                        return None;
                    }
                    source = Some(match value {
                        Rvalue::Use(source, ..) | Rvalue::Cast(_, source, _) => source,
                        _ => return None,
                    });
                }
            }
            if matches!(&block.terminator.kind, TerminatorKind::Call { destination, .. } if destination.local == local)
            {
                return None;
            }
        }
        input = source?;
    }
    None
}
