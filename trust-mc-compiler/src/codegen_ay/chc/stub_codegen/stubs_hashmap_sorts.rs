// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashMap/BTreeMap/TrustMcMap sort extraction helper.
//!
//! Split from stubs_hashmap_translate.rs per #3199.

use ay_bindings::Sort;
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use super::codegen_types::CodegenTypes;
use super::types::int_sort;
use super::{ChcCtx, record_type_sort_fallback};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Extracts key and value sorts from a HashMap/BTreeMap/TrustMcMap type.
    /// Returns (key_sort, value_sort) or None if not a map type.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn extract_hashmap_sorts(
        ty: rustc_public::ty::Ty,
    ) -> Option<(Sort, Sort)> {
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            let name = def.trimmed_name();
            if name == "HashMap" || name == "BTreeMap" || name == "TrustMcMap" {
                let key_sort = args
                    .0
                    .first()
                    .and_then(|arg| match arg {
                        GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                        _ => None,
                    })
                    .unwrap_or_else(|| {
                        record_type_sort_fallback("extract_hashmap_sorts key sort");
                        int_sort()
                    });

                let val_sort = args
                    .0
                    .get(1)
                    .and_then(|arg| match arg {
                        GenericArgKind::Type(ty) => Self::translate_ty(*ty),
                        _ => None,
                    })
                    .unwrap_or_else(|| {
                        record_type_sort_fallback("extract_hashmap_sorts value sort");
                        int_sort()
                    });

                return Some((key_sort, val_sort));
            }
        }
        None
    }
}
