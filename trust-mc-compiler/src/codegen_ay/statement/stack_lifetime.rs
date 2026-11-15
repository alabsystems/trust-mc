// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Allocation-qualified stack lifetime ownership across BMC inline frames.

use super::{PointeeLookup, StatementCodegen};
use std::collections::BTreeMap;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct StackStorageOwner {
    pub(super) base: Arc<str>,
    pub(super) frame: Arc<str>,
    pub(super) local: usize,
    pub(super) has_field_projection: bool,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum StackOwnerRefusal {
    Bound,
    Malformed,
    Cycle,
}

pub(super) type QualifiedLifetimes = BTreeMap<Arc<str>, Option<bool>>;
const MAX_CAPTURED_OWNERS: usize = 4096;

impl StatementCodegen<'_, '_, '_> {
    /// A plain local/field names its own allocation, even if its stored value
    /// is itself a pointer. Only explicit dereference suffixes chase a pointer.
    /// Unresolved dereferences, heap/synthetic leaves and cycles have no proved
    /// stack owner and must never be replaced by the pointer holder's index.
    pub(super) fn resolve_stack_storage_owner(
        pointees: &impl PointeeLookup,
        input: &str,
    ) -> Result<Option<StackStorageOwner>, StackOwnerRefusal> {
        if input.len() > 1024 * 1024 {
            return Err(StackOwnerRefusal::Bound);
        }
        let mut current = input.to_owned();
        let mut bytes_left = 1024usize * 1024;
        let mut has_field_projection = false;
        let mut seen = std::collections::HashSet::new();
        for _ in 0..32 {
            bytes_left = bytes_left.checked_sub(current.len()).ok_or(StackOwnerRefusal::Bound)?;
            if !seen.insert(current.clone()) {
                return Err(StackOwnerRefusal::Cycle);
            }
            let Some((frame, tail)) = current.rsplit_once("::local_") else {
                return Ok(None);
            };
            if frame.is_empty() {
                return Err(StackOwnerRefusal::Malformed);
            }
            let end = tail.find(|c: char| !c.is_ascii_digit()).unwrap_or(tail.len());
            if end == 0 {
                return Err(StackOwnerRefusal::Malformed);
            }
            let local = tail[..end].parse::<usize>().map_err(|_| StackOwnerRefusal::Malformed)?;
            if local.to_string() != tail[..end] {
                return Err(StackOwnerRefusal::Malformed);
            }
            let suffix = &tail[end..];
            if !suffix.is_empty() && !suffix.starts_with('_') {
                return Err(StackOwnerRefusal::Malformed);
            }
            has_field_projection |= suffix.contains("_field_");
            if let Some(deref) = suffix.rfind("_deref") {
                let before = &suffix[..deref];
                let after = &suffix[deref + "_deref".len()..];
                let key = format!("{frame}::local_{local}{before}");
                let Some(target) = pointees.lookup_pointee(&key) else {
                    return Ok(None);
                };
                if target.len().checked_add(after.len()).ok_or(StackOwnerRefusal::Bound)?
                    > bytes_left
                {
                    return Err(StackOwnerRefusal::Bound);
                }
                current = format!("{target}{after}");
                continue;
            }
            return Ok(Some(StackStorageOwner {
                base: Arc::from(crate::codegen_ay::names::local_name(frame, local)),
                frame: Arc::from(frame),
                local,
                has_field_projection,
            }));
        }
        Err(StackOwnerRefusal::Bound)
    }

    pub(super) fn stack_owner_is_live(&self, owner: &StackStorageOwner) -> Option<bool> {
        if owner.frame.as_ref() == self.ctx.current_fn_name() {
            self.stack_local_is_live(owner.local)
        } else {
            self.qualified_storage_lifetimes.get(&owner.base).copied().flatten()
        }
    }

    /// A synchronous inline callee observes the caller's current scope. Keep
    /// fully qualified keys; an absent/truncated entry remains unknown.
    pub(super) fn capture_qualified_storage_lifetimes(&self) -> QualifiedLifetimes {
        self.qualified_storage_lifetimes_with_current(false)
    }

    fn qualified_storage_lifetimes_with_current(&self, expired: bool) -> QualifiedLifetimes {
        let frame = self.ctx.current_fn_name();
        let mut result: QualifiedLifetimes = self
            .qualified_storage_lifetimes
            .iter()
            .filter(|(base, _)| {
                base.rsplit_once("::local_").is_none_or(|(owner, _)| owner != frame)
            })
            .map(|(key, value)| (Arc::clone(key), *value))
            .collect();
        let mut bytes_left = 1024usize * 1024;
        for local in 0..self.body.locals().len() {
            if result.len() >= MAX_CAPTURED_OWNERS {
                break;
            }
            let Some(left) = bytes_left.checked_sub(frame.len().saturating_add(32)) else { break };
            bytes_left = left;
            let base = Arc::from(crate::codegen_ay::names::local_name(frame, local));
            result
                .insert(base, if expired { Some(false) } else { self.stack_local_is_live(local) });
        }
        result
    }

    /// The inline frame's values may escape, its stack allocations cannot.
    /// Caller-owned entries are preserved; every exported local owner of this
    /// returning frame is explicitly dead, including its return-slot storage.
    pub(super) fn completed_inline_storage_lifetimes(&self) -> QualifiedLifetimes {
        self.qualified_storage_lifetimes_with_current(true)
    }
}
