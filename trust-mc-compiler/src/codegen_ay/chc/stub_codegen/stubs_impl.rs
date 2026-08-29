// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub interception implementations — type detection functions.
//! Converted from include!() to proper module per #2595.
//!
//! This module contains methods for detecting library stub types.
//! Split per #1880 for reviewability into:
//!   - stubs_impl.rs (this file): Detection functions (BigInt/BigUint/BigRational + collection type checks)
//!   - stubs_alloc.rs: Heap allocation intrinsics (Part of #1100)
//!   - stubs_collections.rs: HashMap/HashSet/BTreeSet (Part of #788)
//!   - stubs_util.rs: Option helpers and shared utilities
//!   - stubs_math.rs: BigInt/BigRational translation (Part of #734, #911)
//!   - stubs_iterators.rs: Iterator intrinsics, Vec iter, HashMap iter
//!
//! Originally split from codegen.rs per #1353.

use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, trace, warn};

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::stub_method_tables::{
    BIGINT_METHOD_STUBS, BIGRATIONAL_METHOD_STUBS, MethodStubSpec, lookup_method_stub,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    // =========================================================================
    // BigInt stub interception (Part of #734)
    // =========================================================================

    /// Resolve a call operand to its canonical def path.
    pub(in crate::codegen_ay::chc) fn resolve_callee_path(&self, func: &Operand) -> Option<String> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };

        let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
        let def_id =
            instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
        let internal_def_id = rustc_internal::internal(self.tcx, def_id);
        Some(self.tcx.def_path_str(internal_def_id))
    }

    /// Fallback callee name recovery: extract def path from FnDef's def_id
    /// directly, bypassing Instance::resolve.
    ///
    /// Used when `resolve_callee_path` returns `None` for const-generic unstable
    /// intrinsics where `Instance::resolve` may fail. Part of #3741.
    pub(in crate::codegen_ay::chc) fn resolve_fn_def_name(&self, func: &Operand) -> Option<String> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return None,
        };
        let internal_def_id = rustc_internal::internal(self.tcx, fn_def.def_id());
        Some(self.tcx.def_path_str(internal_def_id))
    }

    /// Check if the callee is a foreign (FFI) function.
    ///
    /// Returns `true` if the call operand resolves to a foreign item (extern fn).
    /// Used to detect undefined FFI calls that should emit error() instead of
    /// the unconstrained fallback. Part of #3175.
    ///
    /// Uses `tcx.is_foreign_item()` on the FnDef's def_id directly, bypassing
    /// Instance::resolve which can fail for extern declarations without bodies.
    /// Pattern from kani_middle/attributes/mod.rs:801.
    pub(in crate::codegen_ay::chc) fn is_foreign_call(&self, func: &Operand) -> bool {
        let func_ty = match func.ty(self.body.locals()) {
            Ok(ty) => ty,
            Err(_) => return false,
        };
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return false,
        };
        let internal_def_id = rustc_internal::internal(self.tcx, fn_def.def_id());
        self.tcx.is_foreign_item(internal_def_id)
    }

    /// Single-lookup stub detection: resolve callee and look up in registry.
    ///
    /// Returns the `StubKind` if the callee is a known stub, `None` otherwise.
    /// Dispatch modules should call this once, then route on the result.
    /// Part of #2408.
    pub(in crate::codegen_ay::chc) fn detect_stub(&self, func: &Operand) -> Option<StubKind> {
        let callee_path =
            self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
        if let Some(stub) = self.detect_string_eq_shared_impl(func, &callee_path) {
            return Some(stub);
        }
        self.stub_registry.lookup(&callee_path)
    }

    /// Filtered stub detector: resolve callee, look up in registry, apply predicate.
    ///
    /// All production dispatch modules have migrated to `detect_stub` + predicate
    /// checks (Part of #2408 T2-T6). Retained for test harnesses.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay::chc) fn detect_stub_matching(
        &self,
        func: &Operand,
        filter: fn(StubKind) -> bool,
    ) -> Option<StubKind> {
        let stub = self.detect_stub(func)?;
        filter(stub).then_some(stub)
    }

    /// Generic numeric method detector shared by BigInt and BigRational.
    fn detect_numeric_stub_by_method(
        &self,
        func: &Operand,
        args: &[Operand],
        type_predicate: fn(&rustc_public::ty::Ty) -> bool,
        method_table: &'static [MethodStubSpec],
        family: &'static str,
    ) -> Option<StubKind> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return None, // external enum: TyKind
        };
        let fn_name = fn_def.trimmed_name();

        let is_numeric_call = args.iter().any(|arg| {
            if let Ok(arg_ty) = arg.ty(self.body.locals()) {
                type_predicate(&arg_ty)
            } else {
                false
            }
        });

        let is_numeric_return = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) => fn_args.0.iter().any(|arg| {
                if let GenericArgKind::Type(ty) = arg { type_predicate(&ty) } else { false }
            }),
            _ => false, // external enum: TyKind
        };

        if !is_numeric_call && !is_numeric_return {
            return None;
        }

        trace!(
            "detect_{family}_stub fn={} is_call={} is_return={}",
            fn_name, is_numeric_call, is_numeric_return
        );

        let short_name = fn_name.rsplit("::").next().unwrap_or(&fn_name);
        let stub = lookup_method_stub(method_table, short_name);
        if stub.is_none() {
            warn!(
                %family,
                %short_name,
                %fn_name,
                "unhandled numeric method in type-based stub detection"
            );
        }

        trace!("detect_{family}_stub result={:?}", stub);
        if let Some(ref s) = stub {
            debug!(?fn_name, ?s, "detected {family} stub via type-based detection");
        }

        stub
    }

    /// Detects if a function operand is a BigInt stub using type-based detection.
    ///
    /// This uses type-based detection because `def_path_str` returns trait paths
    /// like `One::one` instead of full implementation paths like
    /// `<num_bigint::BigInt as num_traits::One>::one`.
    ///
    /// Returns the StubKind if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_bigint_stub(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<StubKind> {
        self.detect_numeric_stub_by_method(
            func,
            args,
            Self::type_name_contains_bigint,
            BIGINT_METHOD_STUBS,
            "bigint",
        )
    }

    /// Check if a type's trimmed name matches any target names, traversing refs.
    fn type_matches_names(ty: &rustc_public::ty::Ty, names: &[&str]) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.trimmed_name();
                names.contains(&name.as_str())
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Self::type_matches_names(&inner, names),
            // No logging: type predicates are called on every type; only ADT/Ref can match.
            _ => false, // external enum: TyKind
        }
    }

    /// Check if a type name contains BigInt or BigUint.
    pub(in crate::codegen_ay::chc) fn type_name_contains_bigint(ty: &rustc_public::ty::Ty) -> bool {
        Self::type_matches_names(ty, &["BigInt", "BigUint"])
    }

    fn type_contains_str(ty: &rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                Self::type_contains_str(&inner)
            }
            TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(|arg| {
                matches!(arg, GenericArgKind::Type(inner_ty) if Self::type_contains_str(&inner_ty))
            }),
            _ => false, // external enum: TyKind
        }
    }

    /// `str` after stripping references/raw pointers — and NOT inside an ADT.
    ///
    /// The companion of [`Self::type_contains_str`] without its `Adt` arm. The
    /// difference is the whole point: `Option<&str>` CONTAINS a `str` but is not
    /// one, and comparing two `Option<&str>` is enum equality, not string
    /// equality.
    fn ty_is_str_after_refs(ty: &rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => true,
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                Self::ty_is_str_after_refs(&inner)
            }
            _ => false, // external enum: TyKind
        }
    }

    fn detect_string_eq_shared_impl(&self, func: &Operand, callee_path: &str) -> Option<StubKind> {
        if !callee_path.ends_with("::eq") || !callee_path.contains("PartialEq") {
            return None;
        }

        let func_ty = func.ty(self.body.locals()).ok()?;
        if !matches!(func_ty.kind(), TyKind::RigidTy(RigidTy::FnDef(_, _))) {
            return None;
        }

        // Route on the RECEIVER TYPE, not on "a `str` appears somewhere in the
        // generic args".
        //
        // The old predicate was `fn_args.iter().any(type_contains_str)`, and
        // `type_contains_str` recurses into ADT generic arguments. So
        // `<Option<&str> as PartialEq>::eq` was compiled as STRING equality over
        // two `&Option<&str>` thin pointers. `resolve_string_backing`
        // (codegen_call_string_backing.rs) then correctly refuses them, the
        // comparison result becomes a FREE Bool, and the assertion is discharged
        // against nothing — the harness reports a counterexample built on a value
        // the solver invented.
        //
        // Measured before this change (shipped binary, --ay-chc):
        //     let a: Option<&str> = None; assert!(a == None);   FAILED, string_eq_imprecise=1
        //     let a: Option<u8>  = None; assert!(a == None);    SUCCESSFUL   (control)
        //     let a = "h";               assert!(a == "h");     SUCCESSFUL   (precise eq works)
        // The `Option<u8>` control shows the enum comparison is fine; only the
        // presence of `str` INSIDE the enum broke it.
        //
        // `PartialEq::eq` takes `&self`, so the monomorphised first input is
        // `&&str` for a `&str` receiver and `&Option<&str>` for the enum. Testing
        // it after stripping references keeps genuine string comparisons on the
        // precise byte-array path and sends everything else back to ordinary
        // structural equality. `fn_sig` precedent: kani_middle/transform/contracts.rs.
        let fn_sig = func_ty.kind().fn_sig()?;
        let binder = fn_sig.skip_binder();
        let receiver = binder.inputs().first()?;
        Self::ty_is_str_after_refs(receiver).then_some(StubKind::StringEq)
    }

    /// Detect if a type is a tracked collection for CHC length tracking (Part of #1814, #1632).
    ///
    /// Returns Some((kind, def_name)) where kind is "hashmap", "hashset", or "vec",
    /// and def_name is the full type name. Returns None for non-collection types.
    ///
    /// # Contracts
    ///
    /// REQUIRES: `ty` is a valid rustc type from the current compilation context.
    /// ENSURES: Returns Some(("hashmap", name)) for HashMap/BTreeMap/TrustMcMap types.
    /// ENSURES: Returns Some(("hashset", name)) for HashSet/BTreeSet types.
    /// ENSURES: Returns Some(("vec", name)) for Vec types.
    /// ENSURES: Returns Some(("string", name)) for String types.
    /// ENSURES: Returns None for all other types.
    /// ENSURES: Result kind is always "hashmap", "hashset", "vec", or "string" when Some.
    pub(in crate::codegen_ay::chc) fn detect_collection_type(
        ty: rustc_public::ty::Ty,
    ) -> Option<(&'static str, String)> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.trimmed_name();
                let full_name = def.0.name();

                // HashMap variants: std::collections::HashMap, hashbrown::HashMap
                if name == "HashMap" || name == "BTreeMap" || name == "TrustMcMap" {
                    return Some(("hashmap", full_name));
                }

                // HashSet variants: std::collections::HashSet, hashbrown::HashSet
                if name == "HashSet" || name == "BTreeSet" {
                    return Some(("hashset", full_name));
                }

                // Vec: Part of #1632 — track Vec length for push/pop/len stubs
                if name == "Vec" {
                    return Some(("vec", full_name));
                }

                // String: track logical length like Vec/String stubs expect.
                if name == "String" {
                    return Some(("string", full_name));
                }

                None
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => {
                // Check through references (e.g., &mut HashMap)
                Self::detect_collection_type(inner)
            }
            // No logging: type predicates are called on every type; only ADT/Ref can match.
            _ => None, // external enum: TyKind
        }
    }

    /// Resolve the pointee type for a dereference.
    ///
    /// Supports references, raw pointers, and pointer-like wrappers.
    /// Used by deref loads/stores so Box<T>/Rc<T>/Arc<T> writes hit heap arrays (#1112, #3589).
    pub(in crate::codegen_ay::chc) fn deref_pointee_ty(
        ty: rustc_public::ty::Ty,
    ) -> Option<rustc_public::ty::Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
            TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => Some(inner),
            // Box/Rc/Arc are ADT wrappers that dereference to their first type argument.
            // Keep the match exact on fully-qualified paths to avoid false positives on
            // user-defined wrappers with the same trimmed names.
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let wrapper_name = def.name();
                let is_shared_wrapper = matches!(
                    wrapper_name.as_str(),
                    "std::boxed::Box"
                        | "alloc::boxed::Box"
                        | "std::rc::Rc"
                        | "alloc::rc::Rc"
                        | "std::sync::Arc"
                        | "alloc::sync::Arc"
                );
                if is_shared_wrapper {
                    return args
                        .0
                        .iter()
                        .find_map(|arg| {
                            if let GenericArgKind::Type(inner_ty) = arg {
                                Some(*inner_ty)
                            } else {
                                None
                            }
                        })
                        .or_else(|| {
                            warn!(?ty, %wrapper_name, "pointer wrapper without type argument");
                            Some(ty)
                        });
                }
                // NonNull<T>/Unique<T>: transparent pointer wrappers.
                if def.trimmed_name() == "NonNull" || def.trimmed_name() == "Unique" {
                    return args.0.iter().find_map(|arg| {
                        if let GenericArgKind::Type(inner_ty) = arg {
                            Some(*inner_ty)
                        } else {
                            None
                        }
                    });
                }
                warn!(?ty, "Deref on non-pointer type");
                None
            }
            _ => {
                // external enum: TyKind
                warn!(?ty, "Deref on non-pointer type");
                None
            }
        }
    }

    /// Check if a type name contains BigUint.
    pub(in crate::codegen_ay::chc) fn type_name_contains_biguint(
        ty: &rustc_public::ty::Ty,
    ) -> bool {
        Self::type_matches_names(ty, &["BigUint"])
    }

    /// Check if a type name contains BigRational or Ratio.
    /// Part of #911: BigRational interception for CHC codegen.
    pub(in crate::codegen_ay::chc) fn type_name_contains_bigrational(
        ty: &rustc_public::ty::Ty,
    ) -> bool {
        // num_rational uses Ratio<T> where T = BigInt for BigRational.
        // Note: bare "Rational" excluded — too broad, intercepts user-defined types
        // (e.g., standalone Rational structs in ay self-verify harnesses). Part of #3766.
        Self::type_matches_names(ty, &["BigRational", "Ratio"])
    }

    /// Detects if a function call is a BigRational method using type-based detection.
    ///
    /// Part of #911: BigRational interception for CHC codegen.
    /// Returns the StubKind if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_bigrational_stub(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<StubKind> {
        self.detect_numeric_stub_by_method(
            func,
            args,
            Self::type_name_contains_bigrational,
            BIGRATIONAL_METHOD_STUBS,
            "bigrational",
        )
    }

    /// Check if a type is HashMap, BTreeMap, or TrustMcMap.
    ///
    /// Part of #788: HashMap interception for CHC codegen.
    pub(in crate::codegen_ay::chc) fn type_is_hashmap(ty: &rustc_public::ty::Ty) -> bool {
        Self::type_matches_names(ty, &["HashMap", "BTreeMap", "TrustMcMap"])
    }

    /// Detect iterator adapter `next()` calls by receiver type.
    ///
    /// Part of #4112: `Instance::resolve` on trait method calls like
    /// `<FlatMap<I,U,F> as Iterator>::next` strips the Self type, producing
    /// a generic path like `Iterator::next` that the stub registry cannot
    /// match. This type-based detector checks the first argument's type
    /// (the `&mut self` receiver) for known adapter ADT names and maps
    /// them to the correct StubKind.
    ///
    /// Returns `Some(StubKind)` if the call is an adapter next(), `None` otherwise.
    pub(in crate::codegen_ay::chc) fn detect_adapter_next_by_receiver_type(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<StubKind> {
        // Only match functions named "next".
        let func_ty = func.ty(self.body.locals()).ok()?;
        let fn_def = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => def,
            _ => return None,
        };
        let fn_name = fn_def.trimmed_name();
        if !fn_name.ends_with("next") {
            return None;
        }

        // Check receiver (first arg) type through references.
        let receiver = args.first()?;
        let receiver_ty = receiver.ty(self.body.locals()).ok()?;
        let adapter_name = Self::extract_adapter_name(&receiver_ty)?;

        let stub = match adapter_name {
            "FlatMap" | "Flatten" | "FlattenCompat" => StubKind::FlattenNext,
            "Map" => StubKind::MapNext,
            "Filter" => StubKind::FilterNext,
            "FilterMap" => StubKind::FilterMapNext,
            "Zip" => StubKind::ZipNext,
            "Chain" => StubKind::ChainNext,
            _ => return None,
        };

        debug!(
            %fn_name,
            %adapter_name,
            ?stub,
            "detected adapter next() via receiver type (Part of #4112)"
        );
        Some(stub)
    }

    /// Extract iterator adapter type name from a type, traversing references.
    ///
    /// Returns the trimmed ADT name if it matches a known iterator adapter,
    /// `None` otherwise.
    fn extract_adapter_name(ty: &rustc_public::ty::Ty) -> Option<&'static str> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                let name = def.trimmed_name();
                match name.as_str() {
                    "FlatMap" => Some("FlatMap"),
                    "Flatten" => Some("Flatten"),
                    "FlattenCompat" => Some("FlattenCompat"),
                    "Map" => Some("Map"),
                    "Filter" => Some("Filter"),
                    "FilterMap" => Some("FilterMap"),
                    "Zip" => Some("Zip"),
                    "Chain" => Some("Chain"),
                    _ => None,
                }
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Self::extract_adapter_name(&inner),
            _ => None,
        }
    }
}
