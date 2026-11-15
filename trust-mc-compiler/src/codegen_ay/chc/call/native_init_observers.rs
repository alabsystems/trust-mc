// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Logical object numbers are not native address bits. Only the compiler's
//! actual null/alignment safety observers may consume a native address word.

use super::native_init_custody::place;
use rustc_public::mir::{AssertMessage, TerminatorKind};
use std::collections::HashSet;

pub(super) fn supported(kind: &TerminatorKind, numbers: &HashSet<usize>) -> bool {
    match kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            !place(discr).is_some_and(|p| numbers.contains(&p.local))
        }
        TerminatorKind::Assert { cond, msg, .. }
            if place(cond).is_some_and(|p| numbers.contains(&p.local)) =>
        {
            matches!(
                msg,
                AssertMessage::MisalignedPointerDereference { .. }
                    | AssertMessage::NullPointerDereference
                    | AssertMessage::NullReferenceConstructed
            )
        }
        _ => true,
    }
}
