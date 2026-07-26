// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Metadata propagation helpers for inline statement execution.

use rustc_public::mir::{Operand, Rvalue};

use super::super::ChcCtx;

pub(super) fn propagate_inline_subslice_metadata(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    dest_local: usize,
) {
    let src_local = match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) if src.projection.is_empty() => {
            Some(src.local)
        }
        Rvalue::Cast(_, operand, _) => match operand {
            Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => Some(src.local),
            _ => None,
        },
        Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src) => Some(src.local),
        _ => None,
    };
    let Some(src_local) = src_local else { return };
    if let Some(len) = ctx.ref_resolution.subslice_len.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_len.insert(dest_local, len);
    }
    if let Some(offset) = ctx.ref_resolution.subslice_offset.get(&src_local).cloned() {
        ctx.ref_resolution.subslice_offset.insert(dest_local, offset);
    }
}
