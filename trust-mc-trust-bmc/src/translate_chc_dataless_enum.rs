// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact register carriers for constructed dataless enums. An outer enum type
//! establishes no entry tag shape, width or membership in the interpreter.

use super::*;
use trust_ir::ty::{EnumDef, EnumTagEncoding};

const MAX_DATALESS_ENUM_VARIANTS: usize = 4096;

fn definition<'m>(module: &'m Module, ty: &Ty) -> Option<(&'m EnumDef, Ty)> {
    let Ty::Enum(id) = ty else { return None };
    // Enum IDs need not be table ordinals. Neither a missing ID nor a duplicate
    // definition may acquire another nominal type's carrier.
    let def = module.enum_def(*id)?;
    if module.enums.iter().filter(|candidate| candidate.id == *id).count() != 1
        || def.variants.is_empty()
        || def.variants.len() > MAX_DATALESS_ENUM_VARIANTS
        || def.discriminants.len() > def.variants.len()
        || def.variants.iter().any(|variant| !variant.fields.is_empty())
    {
        return None;
    }
    // Do not replace a normative malformed/unsupported descriptor with the
    // canonical fallback. Niche and tagless memory have no model in this slice.
    if def
        .layout
        .as_ref()
        .is_some_and(|layout| !matches!(layout.encoding, EnumTagEncoding::Direct { .. }))
    {
        return None;
    }
    let tag = def.canonical_tag_repr()?.ty();
    module.enum_layout_shape(*id).ok()?;
    Some((def, tag))
}

pub(super) fn tag_type(module: &Module, ty: &Ty) -> Option<Ty> {
    definition(module, ty).map(|(_, tag)| tag)
}

pub(super) fn constant_tag(module: &Module, ty: &Ty, value: &Constant) -> Option<(Ty, i128)> {
    let (def, tag) = definition(module, ty)?;
    let Constant::Aggregate(fields) = value else { return None };
    let [Constant::Int(discriminant)] = fields.as_slice() else { return None };
    def.effective_discriminants()?.contains(discriminant).then_some((tag, *discriminant))
}

pub(super) fn variant_tag(
    module: &Module,
    ty: &Ty,
    variant: Option<u32>,
    fields: &[ValueId],
) -> Option<(Ty, i128)> {
    let (def, tag) = definition(module, ty)?;
    if !fields.is_empty() {
        return None;
    }
    let discriminants = def.effective_discriminants()?;
    Some((tag, *discriminants.get(usize::try_from(variant?).ok()?)?))
}

pub(super) fn binding(tag: (Ty, i128)) -> Option<AggregateValue> {
    let (ty, discriminant) = tag;
    let scalar =
        normalize_expr_to_exact_ty(&const_to_expr(&ty, &Constant::Int(discriminant))?, &ty)?;
    Some(AggregateValue { fields: vec![ValueBinding::Scalar(scalar)] })
}

/// Select the already-established tag carrier, preserving its exact type and
/// the selected source value. This creates no entry shape/initialization fact.
pub(super) fn select_binding(
    module: &Module,
    ty: &Ty,
    cond: &Expr,
    then_value: &ValueBinding,
    else_value: &ValueBinding,
) -> Option<AggregateValue> {
    tag_type(module, ty)?;
    if !binding_matches_ty_at(module, then_value, ty, 0)
        || !binding_matches_ty_at(module, else_value, ty, 0)
    {
        return None;
    }
    let ValueBinding::Aggregate(selected) = then_value.select_by(cond, else_value)? else {
        return None;
    };
    Some(selected)
}

/// The new carrier is a register transport, not an enum memory model or a
/// license to overwrite the discriminant. Both direct and summary dispatch
/// pass through this guard before interpreting any of these instructions.
pub(super) fn refused_operation(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::InsertField { ty: Ty::Enum(_), .. }
            | Inst::Cast { src_ty: Ty::Enum(_), .. }
            | Inst::Cast { dst_ty: Ty::Enum(_), .. }
            | Inst::Alloca { ty: Ty::Enum(_), .. }
            | Inst::Load { ty: Ty::Enum(_), .. }
            | Inst::Store { ty: Ty::Enum(_), .. }
            | Inst::GEP { pointee_ty: Ty::Enum(_), .. }
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::ty::{EnumLayoutDescriptor, EnumTagRepr, EnumVariant};
    use trust_ir::value::EnumId;

    fn module(id: u32) -> Module {
        let mut module = Module::new("dataless_nominal_guard");
        module.enums.push(
            EnumDef::new(
                EnumId::new(id),
                "Sparse",
                ["A", "B"]
                    .into_iter()
                    .map(|name| EnumVariant {
                        name: name.into(),
                        fields: vec![],
                        field_names: vec![],
                    })
                    .collect(),
            )
            .with_discriminants(vec![Some(-5), Some(7)])
            .with_repr(EnumTagRepr::I16),
        );
        module
    }

    #[test]
    fn dataless_guard_uses_sparse_nominal_ids_and_exact_discriminants() {
        let module = module(17);
        let ty = Ty::Enum(EnumId::new(17));
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(tag_type(&module, &ty), Some(Ty::I16));
        assert_eq!(variant_tag(&module, &ty, Some(0), &[]), Some((Ty::I16, -5)));
        assert_eq!(variant_tag(&module, &ty, Some(1), &[]), Some((Ty::I16, 7)));
        assert!(variant_tag(&module, &ty, Some(2), &[]).is_none());
        assert!(variant_tag(&module, &ty, None, &[]).is_none());
        assert!(variant_tag(&module, &ty, Some(1), &[ValueId::new(0)]).is_none());
        assert!(tag_type(&module, &Ty::Enum(EnumId::new(0))).is_none());
        for value in [
            Constant::Aggregate(vec![Constant::Int(1)]),
            Constant::Aggregate(vec![Constant::Bool(true)]),
            Constant::Aggregate(vec![]),
            Constant::Aggregate(vec![Constant::Int(7), Constant::Int(0)]),
        ] {
            assert!(constant_tag(&module, &ty, &value).is_none());
        }
    }

    #[test]
    fn dataless_guard_does_not_promote_payloads_bad_layouts_or_aliases() {
        let valid = module(0);
        let ty = Ty::Enum(EnumId::new(0));
        let mut payload = valid.clone();
        payload.enums[0].variants[0].fields.push(Ty::Unit);
        assert!(trust_ir_build::validate_module(&payload).is_empty());
        assert!(tag_type(&payload, &ty).is_none(), "a ZST payload is still a payload");
        let mut duplicate = valid.clone();
        duplicate.enums.push(duplicate.enums[0].clone());
        assert!(tag_type(&duplicate, &ty).is_none());
        let mut empty = valid.clone();
        empty.enums[0].variants.clear();
        assert!(tag_type(&empty, &ty).is_none());
        let mut narrow = valid.clone();
        narrow.enums[0].repr = Some(EnumTagRepr::U8);
        assert!(tag_type(&narrow, &ty).is_none(), "negative discriminant cannot be truncated");
        let mut direct = valid.clone();
        direct.enums[0].layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 2,
            align: 2,
            variant_field_offsets: vec![vec![], vec![]],
        });
        assert_eq!(tag_type(&direct, &ty), Some(Ty::I16));
        direct.enums[0].layout.as_mut().unwrap().size = 1;
        assert!(tag_type(&direct, &ty).is_none(), "no fallback from malformed normative layout");
        let mut nested = valid.clone();
        assert!(super::super::composite_shape_of(&nested, &Ty::Tuple(vec![ty.clone()]),).is_none());
        let id = nested.add_type(ty.clone()).unwrap();
        assert!(super::super::composite_shape_of(&nested, &Ty::Array(id, 2)).is_none());
    }
}
