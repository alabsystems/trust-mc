// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exact finite lengths without treating a static origin as a current cursor.

use super::super::inline_const_origin::{literal_str_byte_len, unaliased_origin};
use super::ChcCtx;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use rustc_public::{CrateDef, rustc_internal};

/// A proven exact length for an unadvanced array iterator or literal Chars.
/// The state fields can remain symbolic even when MIR establishes N. Follow
/// only single definitions/copies and genuine core iter constructors; ANY
/// address or borrow of a carrier can advance/rebind it, so those decline.
/// Nested body operands are never interpreted in the outer body's namespace.
pub(super) fn unadvanced_iterator_len(
    ctx: &ChcCtx<'_, '_>,
    arg: &Operand,
    locals: &[LocalDecl],
) -> Option<usize> {
    use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
    if !std::ptr::eq(locals, ctx.body.locals()) {
        return None;
    }
    let mut operand = arg;
    for _ in 0..8 {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return None };
        let local = place.local;
        if !place.projection.is_empty() || ctx.local_has_multiple_whole_definitions(local) {
            return None;
        }
        let mut copied = None;
        let mut constructor = None;
        for block in &ctx.body.blocks {
            for statement in &block.statements {
                if let StatementKind::Assign(lhs, value) = &statement.kind {
                    if matches!(value, Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) if borrowed.local == local)
                    {
                        return None;
                    }
                    if lhs.local == local {
                        if !lhs.projection.is_empty() {
                            return None;
                        }
                        let Rvalue::Use(source, ..) = value else { return None };
                        copied = Some(source);
                    }
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                if !destination.projection.is_empty() || constructor.is_some() || copied.is_some() {
                    return None;
                }
                constructor = Some((func, args));
            }
        }
        if let Some(source) = copied {
            if constructor.is_some() {
                return None;
            }
            operand = source;
            continue;
        }
        let (func, inputs) = constructor?;
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
            ctx.resolve_body_ty(func.ty(locals).ok()?).kind()
        else {
            return None;
        };
        let instance = Instance::resolve(def, &generics).ok()?;
        let input = inputs.first()?;
        if crate::kani_middle::std_abstraction::is_core_str_chars(ctx.tcx, &instance) {
            // Chars equality compares UTF-8 byte suffixes. This is the literal's
            // byte length, never its scalar count or a post-advance cursor.
            return unaliased_origin(ctx, input, literal_str_byte_len)
                .filter(|length| *length <= ChcCtx::SLICE_EQ_EXPAND_MAX_ELEMS);
        }
        let def = rustc_internal::internal(ctx.tcx, instance.def.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(ctx.tcx, def)
            || !matches!(ctx.tcx.item_name(def).as_str(), "iter" | "iter_mut")
        {
            return None;
        }
        return unaliased_origin(ctx, input, |operand| {
            ChcCtx::const_usize_from_expr(&ctx.static_slice_len_from_operand(operand)?)
        })
        .filter(|length| *length <= ChcCtx::SLICE_EQ_EXPAND_MAX_ELEMS);
    }
    None
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::chc::codegen_types::CodegenTypes;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use rustc_public::mir::TerminatorKind;

    #[test]
    fn finite_float_length_requires_an_unadvanced_unaliased_origin() {
        const SOURCE: &str = r#"
            pub fn initial(a: &[f32; 2], b: &[f32; 2]) -> bool { a.iter().eq(b.iter()) }
            pub fn moved(a: &[f32; 2], b: &[f32; 2]) -> bool {
                let original = a.iter(); let moved = original; moved.eq(b.iter())
            }
            pub fn advanced(a: &[f32; 2], b: &[f32; 2]) -> bool {
                let mut left = a.iter(); left.next(); left.eq(b.iter())
            }
            pub fn borrowed(a: &[f32; 2], b: &[f32; 2]) -> bool {
                let mut left = a.iter(); let reference = &mut left; reference.next(); left.eq(b.iter())
            }
            pub fn input(a: core::slice::Iter<'_, f32>, b: core::slice::Iter<'_, f32>) -> bool { a.eq(b) }
            pub fn unsized_origin(a: &[f32; 2], b: &[f32; 2]) -> bool {
                let slice: &[f32] = a; slice.iter().eq(b.iter())
            }
            pub fn rebound(a: &[f32; 2], b: &[f32; 3], choose: bool) -> bool {
                let mut slice: &[f32] = a;
                let mut other: &[f32] = a;
                let selected = if choose { &mut slice } else { &mut other };
                *selected = b;
                slice.iter().eq(b.iter())
            }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            for (name, expected) in [
                ("initial", Some(2)),
                ("moved", Some(2)),
                ("advanced", None),
                ("borrowed", None),
                ("input", None),
                ("unsized_origin", Some(2)),
                ("rebound", None),
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                let args = body
                    .blocks
                    .iter()
                    .find_map(|block| match &block.terminator.kind {
                        TerminatorKind::Call { func, args, .. }
                            if chc
                                .resolve_fn_def_name(func)
                                .is_some_and(|path| path.ends_with("::eq")) =>
                        {
                            Some(args)
                        }
                        _ => None,
                    })
                    .expect("Iterator::eq call");
                assert_eq!(
                    unadvanced_iterator_len(&chc, &args[0], body.locals()),
                    expected,
                    "{name}"
                );
                if expected.is_some() {
                    let nested = body.locals().to_vec();
                    assert_eq!(
                        unadvanced_iterator_len(&chc, &args[0], &nested),
                        None,
                        "nested operand namespace must not be outer MIR"
                    );
                }
            }
        });
    }

    #[test]
    fn chars_literal_lengths_are_bytes_and_decline_after_aliasing_or_advance() {
        const SOURCE: &str = r#"
            pub fn literal() -> bool { "é🦀".chars().eq("é🐍".chars()) }
            pub fn copied() -> bool {
                let original = "é🦀".chars(); let copied = original;
                copied.eq("é🐍".chars())
            }
            pub fn advanced() -> bool {
                let mut source = "é🦀".chars(); source.next(); source.eq("🦀".chars())
            }
            pub fn dynamic(source: &str) -> bool { source.chars().eq("é🦀".chars()) }
            pub fn rebound(choose: bool) -> bool {
                let mut source = "é"; let mut other = "é";
                let selected = if choose { &mut source } else { &mut other };
                *selected = "é🦀";
                source.chars().eq("é🦀".chars())
            }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            for (name, expected) in [
                ("literal", Some(6)),
                ("copied", Some(6)),
                ("advanced", None),
                ("dynamic", None),
                ("rebound", None),
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                let args = body
                    .blocks
                    .iter()
                    .find_map(|block| match &block.terminator.kind {
                        TerminatorKind::Call { func, args, .. }
                            if chc
                                .resolve_fn_def_name(func)
                                .is_some_and(|path| path.ends_with("::eq")) =>
                        {
                            Some(args)
                        }
                        _ => None,
                    })
                    .expect("Iterator::eq call");
                assert_eq!(
                    unadvanced_iterator_len(&chc, &args[0], body.locals()),
                    expected,
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn either_proven_literal_bound_is_usable_only_in_its_own_body() {
        const SOURCE: &str = r#"
            pub fn suffix(source: &str) -> bool {
                let mut left = source.chars(); left.next(); left.eq("y".chars())
            }
            pub fn exhausted(source: &str) -> bool {
                let mut left = source.chars(); left.next(); left.eq("".chars())
            }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            for (name, length) in [("suffix", 1), ("exhausted", 0)] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
                let (func, args) = body
                    .blocks
                    .iter()
                    .find_map(|block| match &block.terminator.kind {
                        TerminatorKind::Call { func, args, .. }
                            if chc
                                .resolve_fn_def_name(func)
                                .is_some_and(|path| path.ends_with("::eq")) =>
                        {
                            Some((func, args))
                        }
                        _ => None,
                    })
                    .unwrap();
                assert_eq!(unadvanced_iterator_len(&chc, &args[0], body.locals()), None);
                assert_eq!(unadvanced_iterator_len(&chc, &args[1], body.locals()), Some(length));
                let sort = ChcCtx::translate_ty(args[0].ty(body.locals()).unwrap()).unwrap();
                let values = [
                    ay_bindings::Expr::var("left", sort.clone()),
                    ay_bindings::Expr::var("right", sort),
                ];
                let path = chc.resolve_fn_def_name(func).unwrap();
                let expr = super::super::inline_iterator_eq_expr(
                    &chc,
                    func,
                    &path,
                    &values,
                    args,
                    body.locals(),
                )
                .unwrap();
                assert!(!expr.to_string().contains("forall"), "finite right bound: {name}");
                let nested_locals = body.locals().to_vec();
                let expr = super::super::inline_iterator_eq_expr(
                    &chc,
                    func,
                    &path,
                    &values,
                    args,
                    &nested_locals,
                )
                .unwrap();
                assert!(expr.to_string().contains("forall"), "never borrow an outer body's bound");
            }
        });
    }

    #[test]
    fn preprocessing_preserves_only_the_authenticated_supported_boundaries() {
        const SOURCE: &str = r#"
            pub fn floats(a: &[f32], b: &[f32]) -> bool { a.iter().eq(b.iter()) }
            pub fn chars(a: &str, b: &str) -> bool { a.chars().eq(b.chars()) }
            pub fn adapted(a: &[u8], b: &[u8]) -> bool { a.iter().rev().eq(b.iter()) }
            pub fn chars_next(a: &str) -> Option<char> { a.chars().next() }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            for (name, preserve_eq) in [("floats", true), ("chars", true), ("adapted", false)] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                let mut saw_eq = false;
                for block in &body.blocks {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        continue;
                    };
                    let Ok(ty) = func.ty(body.locals()) else { continue };
                    let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = ty.kind() else {
                        continue;
                    };
                    let instance = Instance::resolve(def, &generics).unwrap();
                    if def.name().ends_with("::eq") {
                        saw_eq = true;
                        assert_eq!(
                            crate::kani_middle::std_abstraction::preserve_core_iterator_boundary(
                                ctx.tcx, &instance
                            ),
                            preserve_eq,
                            "{name}"
                        );
                    }
                    if def.name().ends_with("::chars") {
                        assert!(crate::kani_middle::std_abstraction::is_core_str_chars(
                            ctx.tcx, &instance
                        ));
                        assert!(
                            crate::kani_middle::std_abstraction::preserve_core_iterator_boundary(
                                ctx.tcx, &instance
                            )
                        );
                    }
                }
                assert!(saw_eq, "{name} must exercise equality");
            }
        });
    }
    #[test]
    fn preprocessing_keeps_real_chars_next_as_a_stateful_boundary() {
        with_test_ay_ctx_for_source(
            "pub fn probe(a: &str) -> Option<char> { a.chars().next() }",
            |ctx| {
                let body = find_instance_by_suffix(ctx.tcx, "probe").callee_body().unwrap();
                let mut saw_next = false;
                for block in &body.blocks {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        continue;
                    };
                    let Ok(ty) = func.ty(body.locals()) else { continue };
                    let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = ty.kind() else {
                        continue;
                    };
                    if def.name().ends_with("::next") {
                        saw_next = true;
                        let instance = Instance::resolve(def, &generics).unwrap();
                        assert!(crate::kani_middle::std_abstraction::is_core_chars_next(
                            ctx.tcx, &instance
                        ));
                        assert!(
                            crate::kani_middle::std_abstraction::preserve_core_iterator_boundary(
                                ctx.tcx, &instance
                            )
                        );
                    }
                }
                assert!(saw_next);
            },
        );
    }
}
