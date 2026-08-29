// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Guard (b) of the C front-end: CHECK the C prototype against the Rust
//! `extern` declaration before any C body is allowed to speak for a call.
//!
//! Kani's own comment in `ForeignItems/extern_fn_ptr.rs` concedes that it
//! "trusts that the extern declaration is compatible with the C definition"
//! and that a mismatch surfaces only as a CBMC type error. Trusting is not an
//! option here: the front-end's single soundness obligation is to never
//! MIS-TRANSLATE, and an incompatible declaration is precisely a
//! mis-translation waiting to be believed. So every scalar width, every
//! signedness, every pointer shape and every aggregate FIELD OFFSET is
//! compared, and a mismatch refuses the symbol back to the sound effect frame
//! rather than encoding a body for the wrong signature.
//!
//! Offsets are compared against rustc's OWN computed layout, not against a
//! `#[repr(C)]` attribute. That makes the check independent of what the
//! attribute claims: whatever representation rustc actually chose must agree,
//! byte for byte, with the platform C ABI layout of the C struct.

use rustc_public::CrateDef;
use rustc_public::abi::FieldsShape;
use rustc_public::ty::{AdtKind, FnSig, IntTy, RigidTy, Ty, TyKind, UintTy};

use crate::c_ffi::{CFunc, CProgram, CTarget, CTy};

/// How a checked C parameter is supplied from the Rust call site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay) enum CArgShape {
    /// A by-value integer or `_Bool`.
    Scalar,
    /// A by-value aggregate whose layout was checked field-for-field.
    Struct,
    /// A `T*`. `nullable` marks the Rust side as `Option<&T>`, where NULL is a
    /// representable value and the C body's null test is therefore live.
    Pointer { nullable: bool },
}

/// How a checked C return value lands in the Rust destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay) enum CRetShape {
    /// `void`, or the `struct Unit` stand-in Kani's C shims return, against a
    /// zero-sized Rust type. The C return expression carries no information.
    Unit,
    Scalar {
        bits: u32,
        signed: bool,
    },
}

#[derive(Debug, Clone)]
pub(in crate::codegen_ay) struct CProtoMatch {
    /// Shapes of the NAMED parameters, in order. For a variadic prototype this
    /// covers `sig.inputs()` exactly; the trailing actuals carry no declared
    /// type on either side and are typed from the CALL SITE instead.
    pub params: Vec<CArgShape>,
    pub ret: CRetShape,
    /// Both sides declare `...`. The call site then has MORE arguments than
    /// `params`, and the extra ones are reachable only through `va_arg`.
    pub variadic: bool,
}

/// Depth limit for the recursive type walk. A self-referential C struct
/// (`struct node { struct node *next; }`) would otherwise recurse forever;
/// exceeding the limit is a refusal, never an acceptance.
const MAX_TY_DEPTH: u32 = 8;

/// Check `cfunc` against the Rust signature `sig`.
///
/// `None` — refuse to the effect frame — on any arity, width, signedness,
/// pointer-shape, or aggregate-layout disagreement, on a `...` that only ONE
/// side declares, and on any return shape outside the accepted set.
///
/// A variadic prototype is checked on its NAMED prefix only, because that is
/// all either side declares: Rust's `...` carries no types and C's `...`
/// carries no types. The trailing actuals are typed from the call site by
/// [`variadic_actual_parts`], which is the only authority that exists for
/// them.
pub(in crate::codegen_ay) fn check_prototype(
    cfunc: &CFunc,
    sig: &FnSig,
    program: &CProgram,
    target: CTarget,
) -> Option<CProtoMatch> {
    // One side variadic and the other not is a prototype MISMATCH, exactly
    // like a width disagreement: the two declarations describe different
    // functions and neither may speak for the other.
    if cfunc.variadic != sig.c_variadic {
        return None;
    }
    let inputs = sig.inputs();
    if inputs.len() != cfunc.params.len() {
        return None;
    }
    let mut params = Vec::with_capacity(inputs.len());
    for (cparam, rust_ty) in cfunc.params.iter().zip(inputs.iter()) {
        params.push(arg_shape(&cparam.ty, *rust_ty, program, target, 0)?);
    }
    let ret = ret_shape(&cfunc.ret, sig.output(), program, target)?;
    Some(CProtoMatch { params, ret, variadic: cfunc.variadic })
}

/// Width and signedness a call-site actual has AFTER the C default argument
/// promotions (C17 6.5.2.2p6), which is the type `va_arg` must be asked for.
///
/// `None` for anything the promotions are not defined over here — a pointer, an
/// aggregate, a float, a 128-bit integer. Refusing is the whole point: a
/// `va_arg` whose type does not match the promoted actual is UB, and guessing
/// which one the programmer meant is the mis-translation this front-end exists
/// to avoid.
pub(in crate::codegen_ay) fn variadic_actual_parts(
    rust: Ty,
    target: CTarget,
) -> Option<(u32, bool)> {
    let (bits, signed) = rust_int_parts(rust, target)?;
    // `_Bool` and every integer narrower than `int` promote to `int`.
    if bits < 32 {
        return Some((32, true));
    }
    // C has no 128-bit integer type in this fragment, so there is no promoted
    // type to name.
    (bits <= 64).then_some((bits, signed))
}

fn arg_shape(
    c: &CTy,
    rust: Ty,
    program: &CProgram,
    target: CTarget,
    depth: u32,
) -> Option<CArgShape> {
    match c {
        CTy::Bool | CTy::Int { .. } => scalar_matches(c, rust, target).then_some(CArgShape::Scalar),
        CTy::Ptr(_) => {
            if pointer_matches(c, rust, program, target, depth) {
                Some(CArgShape::Pointer { nullable: false })
            } else if nullable_pointer_matches(c, rust, program, target, depth) {
                Some(CArgShape::Pointer { nullable: true })
            } else {
                None
            }
        }
        CTy::Struct(tag) => {
            struct_matches(tag, rust, program, target, depth).then_some(CArgShape::Struct)
        }
        // `va_list` as a PARAMETER is the `vprintf` shape: the caller's list is
        // forwarded, and this lane has no forwarded list to bind. Refuse.
        CTy::Void | CTy::VaList => None,
    }
}

fn ret_shape(c: &CTy, rust: Ty, program: &CProgram, target: CTarget) -> Option<CRetShape> {
    match c {
        CTy::Void => is_zero_sized(rust).then_some(CRetShape::Unit),
        // Kani's C shims return `struct Unit` where the Rust side returns `()`
        // (their own comment: a CBMC type-checking workaround). An INCOMPLETE
        // struct carries no fields and no size, so the value is
        // information-free — accept it only against a zero-sized Rust type.
        CTy::Struct(tag) if !program.structs.contains_key(tag) => {
            is_zero_sized(rust).then_some(CRetShape::Unit)
        }
        CTy::Int { bits, signed } => scalar_matches(c, rust, target)
            .then_some(CRetShape::Scalar { bits: *bits, signed: *signed }),
        CTy::Bool => {
            scalar_matches(c, rust, target).then_some(CRetShape::Scalar { bits: 1, signed: false })
        }
        // A by-value aggregate return, or a returned pointer, is Tier 2: the
        // lowering has no way to build the value, so refusing keeps the
        // allowlist honest. `va_list` is not a returnable type at all.
        CTy::Struct(_) | CTy::Ptr(_) | CTy::VaList => None,
    }
}

fn is_zero_sized(ty: Ty) -> bool {
    ty.layout().ok().is_some_and(|l| l.shape().size.bytes() == 0)
}

/// Bit width and signedness of a Rust integer / `bool`.
fn rust_int_parts(ty: Ty, target: CTarget) -> Option<(u32, bool)> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool) => Some((1, false)),
        TyKind::RigidTy(RigidTy::Int(i)) => Some(match i {
            IntTy::I8 => (8, true),
            IntTy::I16 => (16, true),
            IntTy::I32 => (32, true),
            IntTy::I64 => (64, true),
            IntTy::I128 => (128, true),
            IntTy::Isize => (target.pointer_bits, true),
        }),
        TyKind::RigidTy(RigidTy::Uint(u)) => Some(match u {
            UintTy::U8 => (8, false),
            UintTy::U16 => (16, false),
            UintTy::U32 => (32, false),
            UintTy::U64 => (64, false),
            UintTy::U128 => (128, false),
            UintTy::Usize => (target.pointer_bits, false),
        }),
        _ => None,
    }
}

/// Does a C scalar type match a Rust scalar type exactly?
///
/// Exposed for the static-initializer pin: a `--c-lib` object may only supply
/// the initial value of a foreign static whose declared type it actually
/// agrees with.
pub(in crate::codegen_ay) fn scalar_ty_matches(c: &CTy, rust: Ty, target: CTarget) -> bool {
    scalar_matches(c, rust, target)
}

fn scalar_matches(c: &CTy, rust: Ty, target: CTarget) -> bool {
    match c {
        CTy::Bool => matches!(rust.kind(), TyKind::RigidTy(RigidTy::Bool)),
        CTy::Int { bits, signed } => {
            // `bool` is NOT an acceptable stand-in for a C integer: its Rust
            // value space is {0,1} and the C body may produce anything.
            !matches!(rust.kind(), TyKind::RigidTy(RigidTy::Bool))
                && rust_int_parts(rust, target) == Some((*bits, *signed))
        }
        _ => false,
    }
}

/// Pointee of a Rust reference or raw pointer, if the pointer is THIN. A fat
/// pointer (slice, `str`, `dyn Trait`) has a second word C knows nothing
/// about, so it never matches a C `T*`.
fn thin_pointee(ty: Ty) -> Option<Ty> {
    let pointee = match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            inner
        }
        _ => return None,
    };
    let layout = pointee.layout().ok()?;
    layout.shape().is_sized().then_some(pointee)
}

fn pointer_matches(c: &CTy, rust: Ty, program: &CProgram, target: CTarget, depth: u32) -> bool {
    let CTy::Ptr(inner) = c else { return false };
    let Some(pointee) = thin_pointee(rust) else { return false };
    pointee_matches(inner, pointee, program, target, depth + 1)
}

/// `Option<&T>` / `Option<*mut T>` against a C `T*`.
///
/// Rust guarantees the null-pointer optimization for these: `Some(&x)` is the
/// address and `None` is NULL, in one pointer-sized word. That is exactly the
/// C representation, so the C body's `if (p)` test is meaningful. Verified
/// here rather than assumed: the layout must actually be one pointer wide.
fn nullable_pointer_matches(
    c: &CTy,
    rust: Ty,
    program: &CProgram,
    target: CTarget,
    depth: u32,
) -> bool {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = rust.kind() else { return false };
    if def.kind() != AdtKind::Enum || def.trimmed_name() != "Option" {
        return false;
    }
    let variants = def.variants();
    if variants.len() != 2 {
        return false;
    }
    let Ok(layout) = rust.layout() else { return false };
    if layout.shape().size.bytes() as u64 != u64::from(target.pointer_bits / 8) {
        return false;
    }
    let mut payloads = variants.iter().flat_map(|v| v.fields());
    let Some(payload) = payloads.next() else { return false };
    if payloads.next().is_some() {
        return false;
    }
    // The field's declared type is the GENERIC parameter (`T`); it has to be
    // instantiated with this `Option`'s arguments before it can be compared.
    pointer_matches(c, payload.ty_with_args(&args), program, target, depth)
}

fn pointee_matches(c: &CTy, rust: Ty, program: &CProgram, target: CTarget, depth: u32) -> bool {
    if depth > MAX_TY_DEPTH {
        return false;
    }
    match c {
        CTy::Bool | CTy::Int { .. } => scalar_matches(c, rust, target),
        CTy::Struct(tag) => struct_matches(tag, rust, program, target, depth),
        CTy::Ptr(_) => pointer_matches(c, rust, program, target, depth),
        // `void *` has no pointee type to check, so nothing about the target
        // can be established. Refuse. `va_list *` likewise: no representation,
        // so no pointee to compare.
        CTy::Void | CTy::VaList => false,
    }
}

/// Compare a C struct tag against a Rust ADT, byte for byte.
///
/// Size, alignment, field count, per-field TYPE and per-field OFFSET must all
/// agree. This is what separates `takes_struct2` (`f.i + f.i2` = 20) from
/// `takes_struct_ptr2` (`f->i + f->c` = 19) in the corpus: the two differ only
/// by which offset the second addend is read from.
fn struct_matches(tag: &str, rust: Ty, program: &CProgram, target: CTarget, depth: u32) -> bool {
    if depth > MAX_TY_DEPTH {
        return false;
    }
    let Some(cdef) = program.structs.get(tag) else { return false };
    let Some((csize, calign)) = program.size_align(&CTy::Struct(tag.to_owned()), target) else {
        return false;
    };
    let Some(coffsets) = program.field_offsets(tag, target) else { return false };

    let TyKind::RigidTy(RigidTy::Adt(def, args)) = rust.kind() else { return false };
    if def.kind() != AdtKind::Struct {
        return false;
    }
    let Ok(layout) = rust.layout() else { return false };
    let shape = layout.shape();
    if shape.size.bytes() as u64 != csize || shape.abi_align != calign {
        return false;
    }
    let FieldsShape::Arbitrary { offsets } = shape.fields else { return false };
    let variants = def.variants();
    let Some(variant) = variants.first() else { return false };
    let fields = variant.fields();
    if fields.len() != cdef.fields.len() || offsets.len() != fields.len() {
        return false;
    }
    for (idx, cfield) in cdef.fields.iter().enumerate() {
        if offsets[idx].bytes() as u64 != coffsets[idx] {
            return false;
        }
        // Instantiated with the ADT's own arguments: a generic field's
        // declared type is a parameter, which matches nothing.
        if !pointee_matches(&cfield.ty, fields[idx].ty_with_args(&args), program, target, depth + 1)
        {
            return false;
        }
    }
    true
}
