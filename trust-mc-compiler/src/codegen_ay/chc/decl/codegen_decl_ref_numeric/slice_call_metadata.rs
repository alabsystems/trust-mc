// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Slice and string call metadata pre-propagation for CHC reference analysis.

use std::collections::HashSet;

use rustc_public::mir::TerminatorKind;
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Pre-propagate metadata through `<[T]>::as_ptr/as_mut_ptr` call terminators.
    ///
    /// The raw-pointer destination may be dereferenced in a later MIR block that
    /// is encoded before the call block. Recording the side-table metadata here
    /// makes the deref translation order-independent.
    pub(super) fn collect_slice_as_ptr_call_metadata(&mut self) {
        let mut propagations = Vec::new();
        for bb in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            if !self.detect_slice_as_ptr_call(func) {
                continue;
            }
            let Some(arg) = args.first().cloned() else { continue };
            propagations.push((destination.local, arg));
        }

        for (dest_local, arg) in propagations {
            self.propagate_slice_as_ptr_metadata(dest_local, &arg);
            debug!(dest_local, "collect_slice_as_ptr_call_metadata: propagated backing metadata");
        }
    }

    /// Pre-propagate metadata through `str::as_bytes` call terminators.
    ///
    /// `as_bytes` returns a `[u8]` view of the same backing storage. Pre-seeding
    /// the destination slice keeps later `bytes[i]` reads precise even when the
    /// indexing block is encoded before the call block.
    pub(super) fn collect_str_as_bytes_call_metadata(&mut self) {
        let mut propagations = Vec::new();
        for bb in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            if !self.detect_str_as_bytes_call(func) {
                continue;
            }
            let Some(arg) = args.first().cloned() else { continue };
            propagations.push((destination.local, arg));
        }

        let modified_locals = HashSet::new();
        for (dest_local, arg) in propagations {
            if self.propagate_str_as_bytes_metadata(dest_local, &arg, &modified_locals) {
                debug!(dest_local, "collect_str_as_bytes_call_metadata: propagated byte backing");
            }
        }
    }
}
