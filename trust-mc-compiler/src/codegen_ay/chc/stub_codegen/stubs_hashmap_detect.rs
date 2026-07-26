// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashMap/BTreeMap/TrustMcMap stub detection helpers.
//! Converted from include!() to proper module per #2595.
//!
//! Extracted from stubs_hashmap.rs per #2246.

use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::trace;

use super::ChcCtx;
use super::stubs::StubKind;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detects if a function call is a HashMap method using type-based detection.
    ///
    /// Part of #788: HashMap interception for CHC codegen.
    /// Part of #797: Tightened detection gating to prefer def-path lookup.
    /// Returns the StubKind if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_hashmap_stub(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<StubKind> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return None, // external enum: TyKind
        };
        // Resolve callee path once for Phase 1 and Phase 1.5 (#2286 MEDIUM).
        let callee_path = self.resolve_callee_path(func);

        // Phase 1: Try def-path based lookup via StubRegistry (most precise)
        // This avoids false positives from name-only matching
        if let Some(ref path) = callee_path
            && let Some(stub) = self.stub_registry.lookup(path)
        {
            // Map TrustMcMap/BTreeMap stubs to HashMap equivalents (same SMT Array model).
            // Non-map stubs (BigInt, etc.) return None from to_hashmap_equivalent().
            if let Some(mapped) = stub.to_hashmap_equivalent() {
                return Some(mapped);
            }
            trace!(?stub, "detect_hashmap_stub: non-HashMap stub from registry");
        }

        // Phase 1.5: Check for hashbrown internals (#798)
        // When HashMap operations are inlined during std compilation, we see
        // hashbrown internal calls instead. Map these back to HashMap stubs.
        let fn_name = fn_def.trimmed_name();
        if let Some(ref path) = callee_path
            && path.contains("hashbrown::")
            && let Some(stub) = self.detect_hashbrown_stub(path, args)
        {
            return Some(stub);
        }

        // Phase 2: Fall back to type-based detection when def-path unavailable
        // This handles cases where rustc doesn't provide full path info

        // Check if any argument type is HashMap, BTreeMap, or TrustMcMap
        let is_hashmap_call = args.iter().any(|arg| {
            if let Ok(arg_ty) = arg.ty(self.body.locals()) {
                Self::type_is_hashmap(&arg_ty)
            } else {
                false
            }
        });

        // Type-based detection requires HashMap argument type
        if !is_hashmap_call {
            return None;
        }

        // Match by short function name + HashMap receiver (fallback)
        match fn_name.as_str() {
            "new" | "default" => Some(StubKind::HashMapNew),
            "insert" => Some(StubKind::HashMapInsert),
            "get" => Some(StubKind::HashMapGet),
            "get_mut" => Some(StubKind::HashMapGetMut),
            "contains_key" => Some(StubKind::HashMapContainsKey),
            "remove" => Some(StubKind::HashMapRemove),
            "len" => Some(StubKind::HashMapLen),
            "is_empty" => Some(StubKind::HashMapIsEmpty),
            "clear" => Some(StubKind::HashMapClear),
            "clone" => Some(StubKind::HashMapClone),
            _ => {
                // non-enum: &str (fn_name)
                trace!(%fn_name, "detect_hashmap_stub: unmatched method on HashMap type");
                None
            }
        }
    }

    /// Detects hashbrown internal functions and maps them to HashMap stubs.
    ///
    /// Part of #798: MIR inlining prevention - hashbrown internal detection.
    /// When rustc inlines HashMap operations during std compilation, we see
    /// internal hashbrown calls. This function recognizes those patterns.
    fn detect_hashbrown_stub(&self, fn_name: &str, args: &[Operand]) -> Option<StubKind> {
        // Resolve receiver type once — avoids 8 redundant type resolutions (#2286 MEDIUM).
        let has_hashmap_receiver = args.first().is_some_and(|r| self.is_hashmap_receiver(r));

        // Match hashbrown internal functions to HashMap operations
        // Pattern: hashbrown::raw::RawTable or hashbrown::map::HashMap internals
        if (fn_name.contains("find_or_find_insert_slot")
            || fn_name.contains("find_or_find_insert_index")
            || fn_name.contains("insert_at_index")
            || (fn_name.contains("insert") && fn_name.contains("hashbrown")))
            && has_hashmap_receiver
        {
            return Some(StubKind::HashMapInsert);
        }
        if fn_name.contains("get") && fn_name.contains("hashbrown") && has_hashmap_receiver {
            return Some(StubKind::HashMapGet);
        }
        if fn_name.contains("find") && !fn_name.contains("insert") && has_hashmap_receiver {
            return Some(StubKind::HashMapGet);
        }
        if fn_name.contains("remove") && fn_name.contains("hashbrown") && has_hashmap_receiver {
            return Some(StubKind::HashMapRemove);
        }
        if fn_name.contains("len") && fn_name.contains("hashbrown") && has_hashmap_receiver {
            return Some(StubKind::HashMapLen);
        }
        if fn_name.contains("is_empty") && fn_name.contains("hashbrown") && has_hashmap_receiver {
            return Some(StubKind::HashMapIsEmpty);
        }
        if fn_name.contains("clear") && fn_name.contains("hashbrown") && has_hashmap_receiver {
            return Some(StubKind::HashMapClear);
        }
        // Part of #1812: Iterator detection for hashbrown internals
        if (fn_name.contains("into_iter_from")
            || fn_name.contains("into_iter")
            || (fn_name.contains("::iter") && !fn_name.contains("next")))
            && fn_name.contains("hashbrown")
            && has_hashmap_receiver
        {
            return Some(StubKind::HashMapIntoIter);
        }
        // next_impl / next advance the iterator (no receiver check needed)
        if (fn_name.contains("next_impl") || fn_name.ends_with("::next"))
            && fn_name.contains("hashbrown")
        {
            return Some(StubKind::HashMapIterNext);
        }
        trace!(%fn_name, "detect_hashbrown_stub: unmatched hashbrown function");
        None
    }

    /// Check if operand has a HashMap-like receiver type.
    ///
    /// Part of #798: MIR inlining prevention - hashbrown internal detection.
    /// Returns true if type name contains "HashMap", "RawTable<(", "hashbrown",
    /// or other HashMap/hashbrown-related patterns.
    fn is_hashmap_receiver(&self, operand: &Operand) -> bool {
        let ty = match operand.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        Self::type_is_hashmap_or_hashbrown(&ty)
    }

    /// Check if a type is HashMap, hashbrown, or related internal type.
    ///
    /// Part of #798: Extended from type_is_hashmap to include hashbrown internals.
    fn type_is_hashmap_or_hashbrown(ty: &rustc_public::ty::Ty) -> bool {
        // First check standard HashMap types
        if Self::type_is_hashmap(ty) {
            return true;
        }

        // Check for hashbrown internal types
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.trimmed_name();
                // hashbrown::raw::RawTable<(K, V)> or hashbrown::map::* types
                // Part of #1812: Also include iterator types (RawIter*, IntoIter)
                name.contains("RawTable")
                    || name.contains("hashbrown")
                    || name.contains("Bucket")
                    || name.contains("RawIter")
                    || name.contains("IntoIter")
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                Self::type_is_hashmap_or_hashbrown(&inner)
            }
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                Self::type_is_hashmap_or_hashbrown(&inner)
            }
            // No logging: type predicates are called on every type; only ADT/Ref/RawPtr can match.
            _ => false, // external enum: TyKind
        }
    }
}
