// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code used for resolve type / trait names

use crate::kani_middle::resolve::{ResolveError, resolve_path, validate_kind};
use quote::ToTokens;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::Mutability;
use rustc_public::rustc_internal;
use rustc_public::ty::{FloatTy, IntTy, Region, RegionKind, RigidTy, Ty, UintTy};
use rustc_span::def_id::LocalDefId;
use std::str::FromStr;
use strum_macros::{EnumString, IntoStaticStr};
use syn::{Expr, ExprLit, Lit, Type, TypePath};
use tracing::{debug, debug_span};

/// Attempts to resolve a type from a type expression.
pub(crate) fn resolve_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    current_module: LocalDefId,
    typ: &syn::Type,
) -> Result<Ty, ResolveError<'tcx>> {
    let _span = debug_span!("resolve_ty", ?typ).entered();
    debug!(?typ, ?current_module, "resolve_ty");
    let unsupported = |kind: &'static str| Err(ResolveError::UnsupportedPath { kind });
    let invalid = |kind: &'static str| {
        Err(ResolveError::InvalidPath {
            msg: format!("Expected a type, but found {kind} `{}`", typ.to_token_stream()),
        })
    };
    #[warn(non_exhaustive_omitted_patterns)]
    match typ {
        Type::Path(TypePath { qself, path }) => {
            if (*qself).is_some() {
                return unsupported("nested qualified paths");
            }
            if let Some(primitive) =
                path.get_ident().and_then(|ident| PrimitiveIdent::from_str(&ident.to_string()).ok())
            {
                Ok(primitive.into())
            } else {
                let def_id = resolve_path(tcx, current_module, path)?;
                validate_kind!(
                    tcx,
                    def_id,
                    "type",
                    DefKind::Struct | DefKind::Union | DefKind::Enum
                )?;
                Ok(rustc_internal::stable(tcx.type_of(def_id)).value)
            }
        }
        Type::Array(array) => {
            let elem_ty = resolve_ty(tcx, current_module, &array.elem)?;
            let len = parse_len(&array.len).map_err(|msg| ResolveError::InvalidPath { msg })?;
            Ty::try_new_array(elem_ty, len.try_into().expect("array length should fit")).map_err(
                |err| ResolveError::InvalidPath { msg: format!("Cannot instantiate array. {err}") },
            )
        }
        Type::Paren(inner) => resolve_ty(tcx, current_module, &inner.elem),
        Type::Ptr(ptr) => {
            let elem_ty = resolve_ty(tcx, current_module, &ptr.elem)?;
            let mutability =
                if ptr.mutability.is_some() { Mutability::Mut } else { Mutability::Not };
            Ok(Ty::new_ptr(elem_ty, mutability))
        }
        Type::Reference(reference) => {
            let elem_ty = resolve_ty(tcx, current_module, &reference.elem)?;
            let mutability =
                if reference.mutability.is_some() { Mutability::Mut } else { Mutability::Not };
            Ok(Ty::new_ref(Region { kind: RegionKind::ReErased }, elem_ty, mutability))
        }
        Type::Slice(slice) => {
            let elem_ty = resolve_ty(tcx, current_module, &slice.elem)?;
            Ok(Ty::from_rigid_kind(RigidTy::Slice(elem_ty)))
        }
        Type::Tuple(tuple) => {
            let elems = tuple
                .elems
                .iter()
                .map(|elem| resolve_ty(tcx, current_module, elem))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Ty::new_tuple(&elems))
        }
        Type::Never(_) => Ok(Ty::from_rigid_kind(RigidTy::Never)),
        Type::BareFn(_) => unsupported("bare function"),
        Type::Macro(_) => invalid("macro"),
        Type::Group(_) => invalid("group paths"),
        Type::ImplTrait(_) => invalid("trait impl paths"),
        Type::Infer(_) => invalid("inferred paths"),
        Type::TraitObject(_) => invalid("trait object paths"),
        Type::Verbatim(_) => unsupported("unknown paths"),
        _ => {
            // external enum: Type (syn)
            unreachable!("all known syn::Type variants are handled; encountered unknown variant")
        }
    }
}

/// Enumeration of existing primitive types that are not parametric.
#[derive(Copy, Clone, Debug, Eq, PartialEq, IntoStaticStr, EnumString)]
#[strum(serialize_all = "lowercase")]
pub(super) enum PrimitiveIdent {
    Bool,
    Char,
    F16,
    F32,
    F64,
    F128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    Str,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

/// Convert a primitive ident into a primitive `Ty`.
impl From<PrimitiveIdent> for Ty {
    fn from(value: PrimitiveIdent) -> Self {
        match value {
            PrimitiveIdent::Bool => Ty::bool_ty(),
            PrimitiveIdent::Char => Ty::from_rigid_kind(RigidTy::Char),
            PrimitiveIdent::F16 => Ty::from_rigid_kind(RigidTy::Float(FloatTy::F16)),
            PrimitiveIdent::F32 => Ty::from_rigid_kind(RigidTy::Float(FloatTy::F32)),
            PrimitiveIdent::F64 => Ty::from_rigid_kind(RigidTy::Float(FloatTy::F64)),
            PrimitiveIdent::F128 => Ty::from_rigid_kind(RigidTy::Float(FloatTy::F128)),
            PrimitiveIdent::I8 => Ty::signed_ty(IntTy::I8),
            PrimitiveIdent::I16 => Ty::signed_ty(IntTy::I16),
            PrimitiveIdent::I32 => Ty::signed_ty(IntTy::I32),
            PrimitiveIdent::I64 => Ty::signed_ty(IntTy::I64),
            PrimitiveIdent::I128 => Ty::signed_ty(IntTy::I128),
            PrimitiveIdent::Isize => Ty::signed_ty(IntTy::Isize),
            PrimitiveIdent::Str => Ty::from_rigid_kind(RigidTy::Str),
            PrimitiveIdent::U8 => Ty::unsigned_ty(UintTy::U8),
            PrimitiveIdent::U16 => Ty::unsigned_ty(UintTy::U16),
            PrimitiveIdent::U32 => Ty::unsigned_ty(UintTy::U32),
            PrimitiveIdent::U64 => Ty::unsigned_ty(UintTy::U64),
            PrimitiveIdent::U128 => Ty::unsigned_ty(UintTy::U128),
            PrimitiveIdent::Usize => Ty::unsigned_ty(UintTy::Usize),
        }
    }
}

/// Checks if a Path segment represents a primitive.
///
/// Note that this function will return false for expressions that cannot be parsed as a type.
pub(super) fn is_primitive<T>(path: &T) -> bool
where
    T: ToTokens,
{
    let token = path.to_token_stream();
    let Ok(typ) = syn::parse2(token) else { return false };
    is_type_primitive(&typ)
}

/// Checks if a type is a primitive including composite ones.
pub(super) fn is_type_primitive(typ: &syn::Type) -> bool {
    #[warn(non_exhaustive_omitted_patterns)]
    match typ {
        Type::Array(_)
        | Type::Ptr(_)
        | Type::Reference(_)
        | Type::Slice(_)
        | Type::Never(_)
        | Type::Tuple(_) => true,
        Type::Path(TypePath { qself: Some(qself), path }) => {
            path.segments.is_empty() && is_type_primitive(&qself.ty)
        }
        Type::Path(TypePath { qself: None, path }) => path
            .get_ident()
            .is_some_and(|ident| PrimitiveIdent::from_str(&ident.to_string()).is_ok()),
        Type::BareFn(_)
        | Type::Group(_)
        | Type::ImplTrait(_)
        | Type::Infer(_)
        | Type::Macro(_)
        | Type::Paren(_)
        | Type::TraitObject(_)
        | Type::Verbatim(_) => false,
        _ => {
            // external enum: Type (syn)
            unreachable!("all known syn::Type variants are handled; encountered unknown variant")
        }
    }
}

/// Parse the length of the array.
/// We currently only support a constant length.
fn parse_len(len: &Expr) -> Result<usize, String> {
    if let Expr::Lit(ExprLit { lit: Lit::Int(lit), .. }) = len
        && matches!(lit.suffix(), "" | "usize")
        && let Ok(val) = usize::from_str(lit.base10_digits())
    {
        return Ok(val);
    }
    Err(format!("Expected a `usize` constant, but found `{}`", len.to_token_stream()))
}

#[cfg(test)]
mod tests {
    use super::{PrimitiveIdent, is_primitive, is_type_primitive, parse_len};
    use std::str::FromStr;
    use syn::{Expr, Type};

    fn ty(input: &str) -> Type {
        syn::parse_str(input).expect("test type should parse")
    }

    fn expr(input: &str) -> Expr {
        syn::parse_str(input).expect("test expression should parse")
    }

    #[test]
    fn primitive_ident_from_str_accepts_known_identifier() {
        assert_eq!(PrimitiveIdent::from_str("u32"), Ok(PrimitiveIdent::U32));
    }

    #[test]
    fn primitive_ident_from_str_rejects_unknown_identifier() {
        assert!(PrimitiveIdent::from_str("Vec").is_err());
    }

    #[test]
    fn is_type_primitive_accepts_scalar_and_composite_primitives() {
        assert!(is_type_primitive(&ty("bool")));
        assert!(is_type_primitive(&ty("f64")));
        assert!(is_type_primitive(&ty("[u8; 4]")));
        assert!(is_type_primitive(&ty("*const i32")));
        assert!(is_type_primitive(&ty("&mut str")));
        assert!(is_type_primitive(&ty("[u16]")));
        assert!(is_type_primitive(&ty("(u8, bool)")));
        assert!(is_type_primitive(&ty("!")));
    }

    #[test]
    fn is_type_primitive_rejects_paren_and_non_primitive_paths() {
        assert!(!is_type_primitive(&ty("(u8)")));
        assert!(!is_type_primitive(&ty("std::vec::Vec<u8>")));
    }

    #[test]
    fn is_primitive_handles_non_type_tokens() {
        let type_path: syn::Path = syn::parse_str("u32").expect("path should parse");
        assert!(is_primitive(&type_path));

        let arithmetic_expr: Expr = syn::parse_str("1 + 2").expect("expr should parse");
        assert!(!is_primitive(&arithmetic_expr));
    }

    #[test]
    fn parse_len_accepts_unsuffixed_and_usize_literals() {
        assert_eq!(parse_len(&expr("4")), Ok(4));
        assert_eq!(parse_len(&expr("12usize")), Ok(12));
    }

    #[test]
    fn parse_len_rejects_non_usize_suffixes() {
        let err = parse_len(&expr("3u8")).expect_err("u8 literal should be rejected");
        assert!(err.contains("Expected a `usize` constant"));
    }

    #[test]
    fn parse_len_rejects_non_literal_expressions() {
        let err = parse_len(&expr("N + 1")).expect_err("expression should be rejected");
        assert!(err.contains("Expected a `usize` constant"));
    }
}
