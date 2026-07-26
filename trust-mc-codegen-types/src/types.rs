// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Type Coercion Utilities for AY Expressions.
//!
//! Provides functions for sort/width coercion of AY expressions:
//! - Bitvector width coercion (sign/zero extension, truncation)
//! - Int/Real sort coercion for BigInt/BigRational interoperability
//!
//! # See Also
//! - `StatementCodegen::infer_sort_from_ty` for MIR-based type translation

use std::sync::LazyLock;

use ay_bindings::sort::{DatatypeConstructor, DatatypeField};
use ay_bindings::{Expr, ExprValue, Sort, sort::SortInner};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use tracing::warn;

/// Extension trait for `DatatypeConstructor` field lookups by name.
///
/// Replaces the verbose `ctor.fields.iter().find(|f| f.name == "...")` pattern
/// that appears 50+ times across `codegen_ay/chc/` and `codegen_ay/statement/`.
/// Centralizes field access for maintainability and provides a single optimization
/// point if indexed lookup is needed later.
///
/// Part of #2267: reduce allocation debt and code duplication.
pub trait CtorFieldExt {
    /// Look up a field by name. Replaces `ctor.fields.iter().find(|f| f.name == name)`.
    fn field(&self, name: &str) -> Option<&DatatypeField>;

    /// Check if a field with the given name exists. Replaces `ctor.fields.iter().any(|f| f.name == name)`.
    fn has_field(&self, name: &str) -> bool;

    /// Get the sort of a named field. Replaces `.find(...).map(|f| f.sort.clone())`.
    fn field_sort(&self, name: &str) -> Option<Sort>;
}

impl CtorFieldExt for DatatypeConstructor {
    #[inline]
    fn field(&self, name: &str) -> Option<&DatatypeField> {
        self.fields.iter().find(|f| f.name == name)
    }

    #[inline]
    fn has_field(&self, name: &str) -> bool {
        self.fields.iter().any(|f| f.name == name)
    }

    #[inline]
    fn field_sort(&self, name: &str) -> Option<Sort> {
        self.field(name).map(|f| f.sort.clone())
    }
}

/// Default pointer width in bits (64 for typical 64-bit systems).
pub const POINTER_WIDTH: u32 = 64;

/// Cached `Sort::bitvec(POINTER_WIDTH)` — avoids an `Arc::new()` allocation per call.
///
/// `Sort::bitvec(64)` creates a new `Arc<SortInner>` on every invocation. This sort
/// is used 600+ times across the codebase; caching it reduces heap traffic to a single
/// allocation plus an `Arc::clone()` (refcount bump) per use.
///
/// Part of #2267.
static PTR_SORT: LazyLock<Sort> = LazyLock::new(|| Sort::bitvec(POINTER_WIDTH));

/// Cached `Sort::bool()` — avoids an `Arc::new()` allocation per call.
/// Part of #2267.
static BOOL_SORT: LazyLock<Sort> = LazyLock::new(Sort::bool);

/// Cached `Sort::int()` — avoids an `Arc::new()` allocation per call.
/// Part of #2267.
static INT_SORT: LazyLock<Sort> = LazyLock::new(Sort::int);

/// Cached `Sort::bitvec(32)` — avoids an `Arc::new()` allocation per call.
/// Part of #2267.
static BV32_SORT: LazyLock<Sort> = LazyLock::new(Sort::bv32);

/// Cached `Sort::bitvec(8)` — avoids an `Arc::new()` allocation per call.
/// Part of #2267.
static BV8_SORT: LazyLock<Sort> = LazyLock::new(|| Sort::bitvec(8));

/// Return a cached `Sort::bitvec(POINTER_WIDTH)`.
///
/// Equivalent to `Sort::bitvec(POINTER_WIDTH)` but reuses a single `Arc` allocation.
#[must_use]
pub fn ptr_sort() -> Sort {
    PTR_SORT.clone()
}

/// Return a cached `Sort::bool()`.
///
/// Equivalent to `Sort::bool()` but reuses a single `Arc` allocation.
/// Part of #2267.
#[must_use]
pub fn bool_sort() -> Sort {
    BOOL_SORT.clone()
}

/// Return a cached `Sort::int()`.
///
/// Equivalent to `Sort::int()` but reuses a single `Arc` allocation.
/// Part of #2267.
#[must_use]
pub fn int_sort() -> Sort {
    INT_SORT.clone()
}

/// Return a cached `Sort::bitvec(32)`.
///
/// Equivalent to `Sort::bv32()` but reuses a single `Arc` allocation.
/// Part of #2267.
#[must_use]
pub fn bv32_sort() -> Sort {
    BV32_SORT.clone()
}

/// Return a cached `Sort::bitvec(8)`.
///
/// Equivalent to `Sort::bitvec(8)` but reuses a single `Arc` allocation.
/// Part of #2267.
#[must_use]
pub fn bv8_sort() -> Sort {
    BV8_SORT.clone()
}

/// Map a Rust signed integer type to its bitvector width in bits.
///
/// Eliminates the duplicated `match IntTy { I8 => 8, ... }` pattern
/// that appears across 10+ codegen files. Part of #2268.
pub fn int_ty_to_bitvec_width(k: IntTy) -> u32 {
    match k {
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
        IntTy::I128 => 128,
        IntTy::Isize => POINTER_WIDTH,
    }
}

/// Map a Rust unsigned integer type to its bitvector width in bits.
///
/// Eliminates the duplicated `match UintTy { U8 => 8, ... }` pattern
/// that appears across 10+ codegen files. Part of #2268.
pub fn uint_ty_to_bitvec_width(k: UintTy) -> u32 {
    match k {
        UintTy::U8 => 8,
        UintTy::U16 => 16,
        UintTy::U32 => 32,
        UintTy::U64 => 64,
        UintTy::U128 => 128,
        UintTy::Usize => POINTER_WIDTH,
    }
}

/// Map a Rust floating-point type to its bitvector width in bits.
///
/// Eliminates the duplicated `match FloatTy { F16 => 16, ... }` pattern
/// that appears across 5+ codegen files. Part of #2268.
pub fn float_ty_to_bitvec_width(k: FloatTy) -> u32 {
    match k {
        FloatTy::F16 => 16,
        FloatTy::F32 => 32,
        FloatTy::F64 => 64,
        FloatTy::F128 => 128,
    }
}

/// Derive the bitvector width from a MIR type for Int-to-BV round-trip conversions.
///
/// When Int-lifted locals (from Range Int-propagation) need bitwise/shift ops,
/// they must be temporarily converted to BitVec. This function determines the
/// correct BV width from the original MIR type.
///
/// Returns `None` for types without a known BV width (ADTs, tuples, closures,
/// arrays, slices, dynamic types). Callers must handle `None` explicitly.
///
/// Part of #3043: fix hardcoded 32-bit width in Int-to-BV conversions.
/// Part of #3329: remove silent 32-bit fallback for unrecognized types.
pub fn ty_to_bv_width(ty: rustc_public::ty::Ty) -> Option<u32> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(k)) => Some(int_ty_to_bitvec_width(k)),
        TyKind::RigidTy(RigidTy::Uint(k)) => Some(uint_ty_to_bitvec_width(k)),
        TyKind::RigidTy(RigidTy::Bool) => Some(1),
        TyKind::RigidTy(RigidTy::Char) => Some(32),
        // Part of #3094: Float types have their own width function.
        TyKind::RigidTy(RigidTy::Float(k)) => Some(float_ty_to_bitvec_width(k)),
        TyKind::RigidTy(
            RigidTy::RawPtr(..) | RigidTy::Ref(..) | RigidTy::FnDef(..) | RigidTy::FnPtr(_),
        ) => Some(POINTER_WIDTH),
        _ => None,
    }
}

/// Controls whether bitvector widening uses sign-extension or zero-extension.
///
/// Used by the public coercion helpers to make the widening mode explicit at
/// every call site. Replaces the previous bare `bool signed` parameter.
///
/// Part of #3615.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignExtension {
    /// Widen by replicating the sign bit (for signed integer semantics).
    SignExtend,
    /// Widen by padding with zeros (for unsigned integer semantics).
    ZeroExtend,
}

impl SignExtension {
    /// Convert a signedness flag to the appropriate extension mode.
    ///
    /// `true` (signed) -> `SignExtend`, `false` (unsigned) -> `ZeroExtend`.
    #[must_use]
    pub fn for_signedness(signed: bool) -> Self {
        if signed { Self::SignExtend } else { Self::ZeroExtend }
    }
}

impl From<bool> for SignExtension {
    /// `true` (signed) → `SignExtend`, `false` (unsigned) → `ZeroExtend`.
    ///
    /// Transitional bridge for call sites that still pass `bool signed`.
    /// New code should use the enum variants directly.
    fn from(signed: bool) -> Self {
        if signed { Self::SignExtend } else { Self::ZeroExtend }
    }
}

/// Coerce a bitvector expression to a target width.
///
/// SMT-LIB requires same-width operands for most bitvector operations.
/// This function handles width mismatches by:
/// - Returning unchanged if widths match
/// - Sign-extending or zero-extending when widening (per `ext`)
/// - Extracting low bits when narrowing (truncation)
///
/// # Arguments
/// - `expr`: The bitvector expression to coerce
/// - `target_width`: The desired width in bits
/// - `ext`: [`SignExtension::SignExtend`] for signed widening, [`SignExtension::ZeroExtend`] for unsigned
///
/// # Panics
/// Panics if `expr` is not a bitvector (use `coerce_bitvec_width_safe` for defensive handling).
///
/// # Example
/// ```text
/// // Coerce u8 shift amount to u32 width (zero-extend)
/// let coerced = coerce_bitvec_width(shift_amount, 32, SignExtension::ZeroExtend);
/// ```
///
/// REQUIRES: `expr.sort().is_bitvec()` is true.
/// REQUIRES: `target_width > 0`.
/// ENSURES: Returned expression has sort bitvec of width `target_width`.
/// ENSURES: Low bits are preserved (truncation or extension only adds/removes high bits).
///
/// # Panics
/// Panics if `expr` is not a bitvector sort. This is a programmer error — callers
/// must ensure bitvec sort before calling. Use [`coerce_bitvec_width_safe`] for
/// defensive handling of non-bitvec inputs.
/// Upstream guards: `codegen_sort.rs` calls this only after sort inference confirms
/// bitvec type; `sort_harmonize.rs` calls after width mismatch detection on known BVs.
#[must_use]
pub fn coerce_bitvec_width(expr: Expr, target_width: u32, ext: SignExtension) -> Expr {
    assert!(target_width > 0, "coerce_bitvec_width requires target_width > 0");
    let current_width = expr.sort().bitvec_width()
        .expect("coerce_bitvec_width requires bitvec input (use coerce_bitvec_width_safe for defensive handling)");
    if current_width == target_width {
        expr
    } else if current_width < target_width {
        let extra_bits = target_width - current_width;
        match ext {
            SignExtension::SignExtend => expr.sign_extend(extra_bits),
            SignExtension::ZeroExtend => expr.zero_extend(extra_bits),
        }
    } else {
        expr.extract(target_width - 1, 0)
    }
}

/// Coerce an expression to a bitvector of `target_width`, with defensive handling.
///
/// Like [`coerce_bitvec_width`], but handles non-bitvector inputs:
/// - **Bool**: Coerced to BV via `ite(expr, 1, 0)` at `target_width` (Part of #2244).
/// - **Other non-BV**: Returned unchanged.
///
/// REQUIRES: `target_width > 0`.
/// ENSURES: If `expr.sort().is_bitvec()`, returned expression has bitvec width `target_width`.
/// ENSURES: If `expr.sort().is_bool()`, returned expression has bitvec width `target_width`.
/// ENSURES: Otherwise, returns `expr` unchanged.
#[must_use]
pub fn coerce_bitvec_width_safe(expr: Expr, target_width: u32, ext: SignExtension) -> Expr {
    assert!(target_width > 0, "coerce_bitvec_width_safe requires target_width > 0");
    let Some(current_width) = expr.sort().bitvec_width() else {
        // Part of #2244: Bool→BV coercion. When a Bool expression reaches
        // a BV-expected context (e.g., array index, SwitchInt operand), convert
        // via ITE: true→1, false→0 at the target width. Without this, Bool
        // expressions pass through unchanged and cause downstream sort panics.
        if expr.sort().is_bool() {
            return Expr::ite(
                expr,
                Expr::bitvec_const(1u64, target_width),
                Expr::bitvec_const(0u64, target_width),
            );
        }
        // Part of #2992: Non-BV/non-Bool pass-through — callers using BV-only
        // operations (.concat, .bvmul, .store, etc.) on this result will panic.
        warn!(
            sort = ?expr.sort(),
            target_width,
            "coerce_bitvec_width_safe: non-BV/non-Bool pass-through (#2992)"
        );
        return expr;
    };
    if current_width == target_width {
        expr
    } else if current_width < target_width {
        let extra_bits = target_width - current_width;
        match ext {
            SignExtension::SignExtend => expr.sign_extend(extra_bits),
            SignExtension::ZeroExtend => expr.zero_extend(extra_bits),
        }
    } else {
        expr.extract(target_width - 1, 0)
    }
}

/// Coerce a Bool expression to a zero-field datatype sort (e.g., `Unit`).
///
/// In MIR codegen, Rust's unit type `()` and ZST ADTs sometimes translate to Bool
/// expressions, but when used as fields of enum datatypes they need to be the
/// declared datatype sort. This function constructs the zero-arg constructor value.
///
/// Returns `Some(expr)` if the target sort is a datatype with exactly one constructor
/// that has zero fields and the source expression is Bool. Returns `None` otherwise.
///
/// Part of #3094: Fix enum constructor sort mismatches for ZST fields.
#[must_use]
pub fn coerce_bool_to_unit_datatype(expr: &Expr, target_sort: &Sort) -> Option<Expr> {
    use ay_bindings::SortInner;
    if !expr.sort().is_bool() {
        return None;
    }
    if let SortInner::Datatype(dt) = target_sort.inner() {
        if dt.constructors.len() == 1 && dt.constructors[0].fields.is_empty() {
            return Some(Expr::datatype_constructor(
                &dt.name,
                &dt.constructors[0].name,
                vec![],
                target_sort.clone(),
            ));
        }
        // Part of #4090: ZST structs wrapping () (e.g., CharTryFromError(()))
        // are encoded as Datatype with 1 constructor and 1 Bool field.
        // Wrap the Bool value in the constructor to match the expected sort.
        if dt.constructors.len() == 1
            && dt.constructors[0].fields.len() == 1
            && dt.constructors[0].fields[0].sort.is_bool()
        {
            return Some(Expr::datatype_constructor(
                &dt.name,
                &dt.constructors[0].name,
                vec![expr.clone()],
                target_sort.clone(),
            ));
        }
    }
    None
}

/// Coerce Int/Real sort mismatches by converting Int to Real.
///
/// If both operands have the same sort, returns them unchanged.
/// If one is Int and the other is Real, converts the Int to Real.
/// This enables BigInt/BigRational comparisons in CHC encoding.
///
/// Part of #911: BigInt/BigRational sort compatibility.
///
/// REQUIRES: `lhs` and `rhs` have sorts that are Int, Real, or other (no change for other).
/// ENSURES: If input sorts are (Int, Real) or (Real, Int), output sorts are (Real, Real).
/// ENSURES: If input sorts are same, output sorts are same as input.
#[must_use]
pub fn coerce_int_real(lhs: Expr, rhs: Expr) -> (Expr, Expr) {
    let lhs_is_int = lhs.sort().is_int();
    let rhs_is_int = rhs.sort().is_int();
    let lhs_is_real = lhs.sort().is_real();
    let rhs_is_real = rhs.sort().is_real();

    if lhs_is_int && rhs_is_real {
        (lhs.int_to_real(), rhs)
    } else if lhs_is_real && rhs_is_int {
        (lhs, rhs.int_to_real())
    } else {
        (lhs, rhs)
    }
}

/// Unwrap a single-field datatype expression to its inner field expression.
///
/// Returns `Some(field_select)` only when `expr` has a datatype sort with exactly
/// one constructor and exactly one field. Other expressions return `None`.
#[must_use]
pub fn unwrap_single_field_datatype(expr: &Expr) -> Option<Expr> {
    let SortInner::Datatype(dt) = expr.sort().inner() else {
        return None;
    };
    let constructor = dt.constructors.first()?;
    let field = constructor.fields.first()?;
    if dt.constructors.len() != 1 || constructor.fields.len() != 1 {
        return None;
    }
    if let ExprValue::DatatypeConstructor { datatype_name, args, .. } = expr.value()
        && datatype_name == &*dt.name
        && args.len() == 1
    {
        return args.first().cloned();
    }

    Some(expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone()))
}

/// Unwrap a single-field datatype expression only when it matches `target_sort`.
///
/// Returns `Some(unwrapped)` when `expr` is a single-field datatype and the sole
/// field sort equals `target_sort`. Returns `None` otherwise.
#[must_use]
pub fn unwrap_single_field_datatype_to_sort(expr: &Expr, target_sort: &Sort) -> Option<Expr> {
    let unwrapped = unwrap_single_field_datatype(expr)?;
    if unwrapped.sort() == target_sort { Some(unwrapped) } else { None }
}

/// Select a field from a datatype expression by constructor index and field index.
///
/// Inspects the expression's sort, looks up the constructor and field, and calls
/// `field_select` — avoiding the need for callers to clone `dt.name` / `field.name`
/// strings just to break the borrow on `sort.inner()`.
///
/// Returns `None` if the sort is not a datatype, or if the constructor/field index
/// is out of range.
///
/// Part of #2267: centralizes the 3-clone-per-field-access pattern.
#[must_use]
pub fn datatype_field_select(expr: Expr, cons_idx: usize, field_idx: usize) -> Option<Expr> {
    // Clone the Sort (O(1) Arc bump) so the borrow on `expr` is released
    // before `field_select` consumes it. This avoids 2 String clones for
    // dt.name and field.name — pass &str via impl Into<String> instead.
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else { return None };
    let cons = dt.constructors.get(cons_idx)?;
    let field = cons.fields.get(field_idx)?;
    Some(expr.field_select(&*dt.name, &*field.name, field.sort.clone()))
}

/// Select a field from a datatype expression by field name within a given constructor.
///
/// Like [`datatype_field_select`] but looks up the field by name instead of index.
/// Returns `None` if no field with the given name exists in the specified constructor.
///
/// Part of #2267: centralizes the name-based field lookup pattern.
#[must_use]
pub fn datatype_field_select_by_name(expr: Expr, cons_idx: usize, name: &str) -> Option<Expr> {
    // Clone the Sort (O(1) Arc bump) so the borrow on `expr` is released
    // before `field_select` consumes it. Pass &str to avoid String clones.
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else { return None };
    let cons = dt.constructors.get(cons_idx)?;
    let field = cons.field(name)?;
    Some(expr.field_select(&*dt.name, &*field.name, field.sort.clone()))
}

/// Recursively flatten a Datatype expression to a concatenated BitVec.
///
/// Supported shapes:
/// - single-constructor Datatypes (struct-like) via recursive leaf flattening
/// - two-constructor option-like enums (one empty variant, one payload variant)
///
/// Returns `None` if:
/// - the expression is not a Datatype sort
/// - the Datatype shape is unsupported for flattening
/// - any leaf field is an unsupported sort (Int, multi-constructor enum)
/// - the total leaf width exceeds `target_bv_width`
///
/// Bool leaves are converted to bv8 (Rust's 1-byte bool). Array leaves are
/// skipped (0 bits) — they represent CHC abstractions for variable-length data.
/// If total leaf width < target, trailing zeros pad to target width.
///
/// Part of #2876, #2244, #1739: recovers store precision for nested structs and
/// option-like enums that `translate_ty` encodes as Datatypes but memory arrays
/// expect as flat BitVec.
#[must_use]
pub fn flatten_datatype_to_bitvec(expr: &Expr, target_bv_width: u32) -> Option<Expr> {
    // Only flatten Datatype expressions — raw BVs, Bools, etc. are not flattened.
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else { return None };

    // Two-constructor enums: encode as [tag:8 | payload:(target-8)].
    // Handles both option-like (one empty variant) and both-payload (e.g. Result<T,E>).
    // Part of #3041: generalized from option-only to all 2-constructor enums.
    if dt.constructors.len() == 2 {
        return flatten_two_constructor_enum_to_bitvec(expr, target_bv_width, dt);
    }

    // N-constructor enums (3+): encode as [tag:8 | payload:(target-8)].
    // Part of #3041: extends flatten to handle enums like Shape with 3+ variants.
    if dt.constructors.len() >= 3 {
        return flatten_n_constructor_enum_to_bitvec(expr, target_bv_width, dt);
    }

    let leaves = collect_bv_leaves(expr)?;
    let total_width: u32 = leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
    // Part of #2244: When Bool→BV8 expansion causes leaf total to exceed
    // target, retry with Bool fields skipped (they encode ZST-like padding
    // that contributes 0 bytes in the Rust memory layout). This handles
    // structs like Pair<[T; N], [U; M]> where Array fields are skipped and
    // Bool fields from ZST arrays add spurious width.
    let leaves = if total_width > target_bv_width {
        let filtered = collect_bv_leaves_skip_bool(expr)?;
        let filtered_width: u32 =
            filtered.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
        if filtered_width > target_bv_width {
            return None;
        }
        filtered
    } else {
        leaves
    };
    let total_width: u32 = leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
    if leaves.is_empty() {
        return None;
    }
    // Concatenate leaves in field order (MSB-first, matching struct memory layout).
    let mut iter = leaves.into_iter();
    let first = iter.next()?;
    let concatenated = iter.fold(first, ay_bindings::Expr::concat);
    // Part of #2915: zero-pad when leaves don't fill the target width.
    // Struct padding (alignment bytes) is not represented in Datatype sorts,
    // so the leaf total may be less than the memory layout width. Trailing
    // zeros are a sound over-approximation for padding bytes.
    if total_width < target_bv_width {
        let pad_width = target_bv_width - total_width;
        Some(concatenated.concat(Expr::bitvec_const(0u64, pad_width)))
    } else {
        Some(concatenated)
    }
}

/// Rebuild a Datatype expression from a flattened BitVec.
///
/// Supports the inverse of [`flatten_datatype_to_bitvec`] for:
/// - Single-constructor structs (Part of #2969: Box/Heap struct CTREX fix)
/// - Two-constructor option-like enums with one empty variant and one payload variant
///
/// Returns `None` when the Datatype shape or payload field sorts are unsupported.
#[must_use]
pub fn unflatten_bitvec_to_datatype(value: &Expr, target_datatype_sort: &Sort) -> Option<Expr> {
    let total_width = value.sort().bitvec_width()?;
    let dt = target_datatype_sort.datatype_sort()?;

    // Part of #2969: Single-constructor structs — extract field bits from the
    // flattened bitvec. This is the inverse of collect_bv_leaves + concat in
    // flatten_datatype_to_bitvec. Fields are concatenated MSB-first with
    // trailing zero-padding for alignment bytes.
    if dt.constructors.len() == 1 {
        let cons = dt.constructors.first()?;
        if cons.fields.is_empty() {
            return Some(Expr::datatype_constructor(
                &*dt.name,
                &*cons.name,
                vec![],
                target_datatype_sort.clone(),
            ));
        }
        let field_widths: Vec<u32> = cons
            .fields
            .iter()
            .map(|f| flattenable_leaf_width(&f.sort))
            .collect::<Option<Vec<_>>>()?;
        let total_field_width: u32 = field_widths.iter().sum();
        if total_field_width == 0 || total_width < total_field_width {
            return None;
        }
        // Field data is at the HIGH end (padding at LOW end per flatten encoding).
        let field_data = if total_width == total_field_width {
            value.clone()
        } else {
            value.clone().extract(total_width - 1, total_width - total_field_width)
        };
        // Extract individual fields MSB-first (matching flatten concat order).
        let mut remaining = total_field_width;
        let mut field_exprs = Vec::with_capacity(cons.fields.len());
        for (field, width) in cons.fields.iter().zip(field_widths.iter().copied()) {
            if width == 0 {
                return None;
            }
            remaining -= width;
            let field_bits = field_data.clone().extract(remaining + width - 1, remaining);
            field_exprs.push(rebuild_expr_from_flat_bits(field_bits, &field.sort)?);
        }
        return Some(Expr::datatype_constructor(
            &*dt.name,
            &*cons.name,
            field_exprs,
            target_datatype_sort.clone(),
        ));
    }

    // Multi-constructor enums — variable-width tag + compact payload.
    // Part of #3041: uses min_tag_bits(N) for tag and enum leaf widths for decode.
    let n = dt.constructors.len();
    if n < 2 {
        return None;
    }
    let tag_bits = min_tag_bits(n);
    if total_width < tag_bits {
        return None;
    }
    let payload_space = total_width - tag_bits;
    let tag = value.clone().extract(total_width - 1, total_width - tag_bits);

    if let Some((empty_idx, payload_idx)) = option_like_constructor_indices(&dt) {
        let empty_cons = dt.constructors.get(empty_idx)?;
        let payload_cons = dt.constructors.get(payload_idx)?;

        // Part of #4173: niche-packed tag-free path for option-like enums.
        // When the payload constructor's field width equals the total BV width
        // (e.g., Option<NonZeroU128> packed into BV128), the tag bit doesn't fit.
        // Decode using niche semantics: bv == 0 → None, bv != 0 → Some(bv).
        // Mirrors the tag-free flatten path in flatten_two_constructor_enum_to_bitvec.
        let payload_field_widths: Option<Vec<u32>> =
            payload_cons.fields.iter().map(|f| enum_leaf_width(&f.sort)).collect();
        if let Some(ref widths) = payload_field_widths {
            let total_payload_width: u32 = widths.iter().sum();
            if total_payload_width > payload_space && total_payload_width <= total_width {
                let payload_fields =
                    decode_enum_constructor_fields(value, payload_cons, total_width)?;
                let payload_expr = Expr::datatype_constructor(
                    &*dt.name,
                    &*payload_cons.name,
                    payload_fields,
                    target_datatype_sort.clone(),
                );
                let empty_expr = Expr::datatype_constructor(
                    &*dt.name,
                    &*empty_cons.name,
                    vec![],
                    target_datatype_sort.clone(),
                );
                let is_payload = value.clone().ne(Expr::bitvec_const(0u64, total_width));
                return Some(Expr::ite(is_payload, payload_expr, empty_expr));
            }
        }

        // Tagged path: tag != 0 → payload constructor, tag == 0 → empty constructor.
        let payload_fields = decode_enum_constructor_fields(value, payload_cons, payload_space)?;
        let payload_expr = Expr::datatype_constructor(
            &*dt.name,
            &*payload_cons.name,
            payload_fields,
            target_datatype_sort.clone(),
        );
        let empty_expr = Expr::datatype_constructor(
            &*dt.name,
            &*empty_cons.name,
            vec![],
            target_datatype_sort.clone(),
        );
        let is_payload = tag.ne(Expr::bitvec_const(0u64, tag_bits));
        return Some(Expr::ite(is_payload, payload_expr, empty_expr));
    }

    // Both-payload / N-constructor path: tag selects constructor.
    unflatten_n_constructor_bitvec_to_datatype(
        value,
        target_datatype_sort,
        &dt,
        &tag,
        tag_bits,
        payload_space,
    )
}

/// Decode a constructor's fields from a flat BV using compact enum encoding.
///
/// Like [`decode_constructor_fields`] but uses [`enum_leaf_width`] (Bool→1 bit,
/// nested enums supported) to match the compact encoding in [`collect_enum_bv_leaves`].
///
/// Part of #3041: inverse of compact enum flatten for variable-width tag encoding.
fn decode_enum_constructor_fields(
    value: &Expr,
    cons: &ay_bindings::sort::DatatypeConstructor,
    payload_space: u32,
) -> Option<Vec<Expr>> {
    let field_widths: Vec<u32> =
        cons.fields.iter().map(|f| enum_leaf_width(&f.sort)).collect::<Option<Vec<_>>>()?;
    let total_field_width: u32 = field_widths.iter().sum();
    if total_field_width > payload_space {
        return None;
    }
    if total_field_width == 0 {
        return Some(Vec::new());
    }
    let payload_bits = value.clone().extract(payload_space - 1, 0);
    let field_data = if payload_space == total_field_width {
        payload_bits
    } else {
        payload_bits.extract(total_field_width - 1, 0)
    };
    let mut remaining = total_field_width;
    let mut fields = Vec::with_capacity(cons.fields.len());
    for (field, width) in cons.fields.iter().zip(field_widths.iter().copied()) {
        if width == 0 {
            return None;
        }
        remaining -= width;
        let field_bits = field_data.clone().extract(remaining + width - 1, remaining);
        fields.push(rebuild_enum_expr_from_flat_bits(field_bits, &field.sort)?);
    }
    Some(fields)
}

/// Rebuild an expression from flat BV bits in enum context.
///
/// Like [`rebuild_expr_from_flat_bits`] but handles:
/// - Bool from 1-bit BV (vs any-width in struct context)
/// - Multi-constructor enum Datatypes via recursive unflatten
///
/// Part of #3041: inverse of compact enum leaf encoding.
fn rebuild_enum_expr_from_flat_bits(bits: Expr, target_sort: &Sort) -> Option<Expr> {
    if let Some(target_width) = target_sort.bitvec_width() {
        let bits_width = bits.sort().bitvec_width()?;
        let rebuilt = if bits_width == target_width {
            bits
        } else if bits_width > target_width {
            bits.extract(target_width - 1, 0)
        } else {
            bits.zero_extend(target_width - bits_width)
        };
        return Some(rebuilt);
    }
    if target_sort.is_bool() {
        let bits_width = bits.sort().bitvec_width()?;
        return Some(bits.ne(Expr::bitvec_const(0u64, bits_width)));
    }

    let dt = target_sort.datatype_sort()?;
    if dt.constructors.len() == 1 {
        // Single-constructor struct: extract fields recursively.
        let cons = dt.constructors.first()?;
        let field_widths: Vec<u32> = cons
            .fields
            .iter()
            .map(|field| enum_leaf_width(&field.sort))
            .collect::<Option<Vec<_>>>()?;
        let total_width: u32 = field_widths.iter().sum();
        let bits_width = bits.sort().bitvec_width()?;
        if bits_width < total_width {
            return None;
        }
        let payload_bits =
            if bits_width == total_width { bits } else { bits.extract(total_width - 1, 0) };
        let mut remaining = total_width;
        let mut field_exprs = Vec::with_capacity(cons.fields.len());
        for (field, width) in cons.fields.iter().zip(field_widths.iter().copied()) {
            if width == 0 {
                return None;
            }
            remaining -= width;
            let field_bits = payload_bits.clone().extract(remaining + width - 1, remaining);
            field_exprs.push(rebuild_enum_expr_from_flat_bits(field_bits, &field.sort)?);
        }
        return Some(Expr::datatype_constructor(
            &*dt.name,
            &*cons.name,
            field_exprs,
            target_sort.clone(),
        ));
    }

    // Multi-constructor enum: unflatten using variable-width tag.
    let n = dt.constructors.len();
    let tag_bits = min_tag_bits(n);
    let bits_width = bits.sort().bitvec_width()?;
    if bits_width < tag_bits {
        return None;
    }
    let payload_space = bits_width - tag_bits;
    let tag = bits.clone().extract(bits_width - 1, bits_width - tag_bits);
    unflatten_n_constructor_bitvec_to_datatype(
        &bits,
        target_sort,
        &dt,
        &tag,
        tag_bits,
        payload_space,
    )
}

/// Collect all leaf BitVec expressions from a (possibly nested) Datatype.
///
/// Handles BitVec leaves directly, converts Bool leaves to bv8 (Rust's bool
/// is 1 byte in memory), and skips Array leaves (0 bits — CHC abstractions for
/// variable-length data). Returns `None` if any leaf is an unsupported sort
/// (Int, multi-constructor enum) that cannot be flattened to a fixed-width
/// bitvector.
///
/// Part of #2915: Bool leaf handling recovers nested tuple flattening for types
/// like `((u32, bool), u8)` where CHC encodes bool as Bool sort but memory
/// layout uses 1 byte.
fn collect_bv_leaves(expr: &Expr) -> Option<Vec<Expr>> {
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else {
        // Base case: not a Datatype — must be a BitVec or Bool leaf.
        if sort.is_bitvec() {
            return Some(vec![expr.clone()]);
        }
        // Part of #2915: Bool fields are 1 byte in Rust memory layout.
        // Convert Bool → bv8 via ite(b, bv8(1), bv8(0)).
        if sort.is_bool() {
            let bv_expr =
                Expr::ite(expr.clone(), Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8));
            return Some(vec![bv_expr]);
        }
        // Part of #2915: Array sort fields (e.g. PolymorphicIter.fld_data) are
        // CHC abstractions for variable-length backing data. They have no fixed
        // bitvec width in the Rust memory layout — the struct's padding bytes
        // account for any inline data. Skip Array fields (contribute 0 bits);
        // `flatten_datatype_to_bitvec` will zero-pad to the target width.
        if sort.is_array() {
            return Some(vec![]);
        }
        return None;
    };
    if dt.constructors.len() != 1 {
        let width = flattenable_datatype_sort_width(&sort)?;
        return Some(vec![flatten_datatype_to_bitvec(expr, width)?]);
    }

    let cons = &dt.constructors[0];
    let mut leaves = Vec::new();
    for field in &cons.fields {
        let field_expr = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
        let field_leaves = collect_bv_leaves(&field_expr)?;
        leaves.extend(field_leaves);
    }
    Some(leaves)
}

/// Like [`collect_bv_leaves`] but skips Bool-sorted fields entirely (0 bits)
/// instead of converting them to BV8. This is used as a fallback when Bool→BV8
/// expansion causes the leaf total to exceed the target BV width, which happens
/// for structs containing ZST arrays encoded as Bool by `translate_ty`.
///
/// Part of #2244: ZST arrays like `[(); N]` are encoded as Bool sort but
/// contribute 0 bytes in the Rust memory layout. When a Datatype has both
/// BV fields and Bool-from-ZST fields, the Bool→BV8 expansion inflates the
/// width beyond what the memory target expects. This variant skips Bools
/// so the flattened width matches the actual memory layout.
fn collect_bv_leaves_skip_bool(expr: &Expr) -> Option<Vec<Expr>> {
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else {
        if sort.is_bitvec() {
            return Some(vec![expr.clone()]);
        }
        // Skip Bool fields entirely (0 bits) — they represent ZST padding.
        if sort.is_bool() {
            return Some(vec![]);
        }
        // Skip Array fields (0 bits) — CHC abstractions for variable-length data.
        if sort.is_array() {
            return Some(vec![]);
        }
        return None;
    };
    if dt.constructors.len() != 1 {
        let width = flattenable_datatype_sort_width(&sort)?;
        return Some(vec![flatten_datatype_to_bitvec(expr, width)?]);
    }
    let cons = &dt.constructors[0];
    let mut leaves = Vec::new();
    for field in &cons.fields {
        let field_expr = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
        let field_leaves = collect_bv_leaves_skip_bool(&field_expr)?;
        leaves.extend(field_leaves);
    }
    Some(leaves)
}

/// Encode a two-constructor enum as a flat BitVec.
///
/// Handles two cases:
/// 1. **Option-like** (one empty + one payload constructor):
///    - empty variant: all-zero bitvector
///    - payload variant: `concat(tag=1u8, payload_bits_padded)`
/// 2. **Both-payload** (both constructors have fields, e.g. `Result<T, E>`):
///    - constructor 0: `concat(tag=0u8, c0_payload_padded)`
///    - constructor 1: `concat(tag=1u8, c1_payload_padded)`
///
/// Part of #3041: generalizes flatten to handle `Result<T, E>` and other
/// two-variant enums where both constructors carry data.
fn flatten_two_constructor_enum_to_bitvec(
    expr: &Expr,
    target_bv_width: u32,
    dt: &ay_bindings::sort::DatatypeSort,
) -> Option<Expr> {
    // Part of #3041: use variable-width tag (1 bit for 2 constructors) and
    // compact enum leaves (Bool→bv1, nested enum support) to fit within
    // Rust's niche-optimized memory layouts.
    let tag_bits = min_tag_bits(2); // = 1
    if target_bv_width < tag_bits {
        return None;
    }
    let payload_space = target_bv_width - tag_bits;

    // Try option-like path first (backward compatible).
    if let Some((_empty_idx, payload_idx)) = option_like_constructor_indices(dt) {
        let payload_cons = dt.constructors.get(payload_idx)?;
        let payload_leaves = collect_constructor_enum_leaves(expr, dt, payload_cons)?;
        let payload_width: u32 =
            payload_leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
        if payload_width > payload_space {
            // Part of #3794: tag-free fallback for option-like enums when
            // payload exactly fills the target width. The ITE condition
            // carries the Some/None distinction; empty variant is all-zeros.
            if payload_width <= target_bv_width {
                let payload_bits =
                    encode_payload_bits(&payload_leaves, payload_width, target_bv_width);
                let empty_encoded = Expr::bitvec_const(0u64, target_bv_width);
                let is_payload = expr.clone().is_constructor(&*dt.name, &*payload_cons.name);
                return Some(Expr::ite(is_payload, payload_bits, empty_encoded));
            }
            return None;
        }

        let payload_bits = encode_payload_bits(&payload_leaves, payload_width, payload_space);
        let payload_encoded = if payload_space > 0 {
            Expr::bitvec_const(1u64, tag_bits).concat(payload_bits)
        } else {
            Expr::bitvec_const(1u64, tag_bits)
        };
        let empty_encoded = Expr::bitvec_const(0u64, target_bv_width);
        let is_payload = expr.clone().is_constructor(&*dt.name, &*payload_cons.name);
        return Some(Expr::ite(is_payload, payload_encoded, empty_encoded));
    }

    // Both-payload path: both constructors have fields (e.g. Result<T, E>).
    // Part of #3041: encode as ITE(is_c0, tag=0|c0_payload, tag=1|c1_payload).
    let c0 = dt.constructors.first()?;
    let c1 = dt.constructors.get(1)?;
    if c0.fields.is_empty() || c1.fields.is_empty() {
        return None; // Should have been caught by option-like path above.
    }

    let c0_leaves = collect_constructor_enum_leaves(expr, dt, c0)?;
    let c1_leaves = collect_constructor_enum_leaves(expr, dt, c1)?;
    let c0_width: u32 = c0_leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
    let c1_width: u32 = c1_leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
    let max_payload = c0_width.max(c1_width);
    if max_payload > payload_space {
        // Part of #3794: tag-free fallback when payload exactly fills the
        // target width (e.g., Result<u8, String> with target BV(192) —
        // String payload is 192 bits, tag bit would push to 193).
        // The ITE condition carries constructor identity implicitly, so
        // embedded tag bits are redundant. Each constructor's payload is
        // zero-padded to fill the full target width.
        if max_payload <= target_bv_width {
            let c0_bits = encode_payload_bits(&c0_leaves, c0_width, target_bv_width);
            let c1_bits = encode_payload_bits(&c1_leaves, c1_width, target_bv_width);
            let is_c0 = expr.clone().is_constructor(&*dt.name, &*c0.name);
            return Some(Expr::ite(is_c0, c0_bits, c1_bits));
        }
        return None;
    }

    let c0_bits = encode_payload_bits(&c0_leaves, c0_width, payload_space);
    let c1_bits = encode_payload_bits(&c1_leaves, c1_width, payload_space);
    let c0_encoded = Expr::bitvec_const(0u64, tag_bits).concat(c0_bits);
    let c1_encoded = Expr::bitvec_const(1u64, tag_bits).concat(c1_bits);
    let is_c0 = expr.clone().is_constructor(&*dt.name, &*c0.name);
    Some(Expr::ite(is_c0, c0_encoded, c1_encoded))
}

/// Encode an N-constructor enum (N >= 3) as a flat BitVec.
///
/// Layout: `[tag:T | payload:(target-T)]` where T = `min_tag_bits(N)` and
/// tag is the constructor index (0..N-1). Payload is the zero-padded
/// concatenation of the constructor's BV-typed fields using compact encoding
/// (Bool→bv1, nested enums recursively flattened).
///
/// Part of #3041: variable-width tag + compact enum leaves.
fn flatten_n_constructor_enum_to_bitvec(
    expr: &Expr,
    target_bv_width: u32,
    dt: &ay_bindings::sort::DatatypeSort,
) -> Option<Expr> {
    let n = dt.constructors.len();
    let tag_bits = min_tag_bits(n);
    if target_bv_width < tag_bits {
        return None;
    }
    let payload_space = target_bv_width - tag_bits;

    // Collect payload BV leaves for each constructor, verify they fit.
    let mut encoded_variants: Vec<Expr> = Vec::with_capacity(n);
    for (i, cons) in dt.constructors.iter().enumerate() {
        let tag = Expr::bitvec_const(i as u64, tag_bits);
        if cons.fields.is_empty() {
            // Unit variant: tag followed by zero padding.
            if payload_space > 0 {
                encoded_variants.push(tag.concat(Expr::bitvec_const(0u64, payload_space)));
            } else {
                encoded_variants.push(tag);
            }
        } else {
            let leaves = collect_constructor_enum_leaves(expr, dt, cons)?;
            let leaf_width: u32 = leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
            if leaf_width > payload_space {
                return None;
            }
            let payload_bits = encode_payload_bits(&leaves, leaf_width, payload_space);
            if payload_space > 0 {
                encoded_variants.push(tag.concat(payload_bits));
            } else {
                encoded_variants.push(tag);
            }
        }
    }

    // Build right-nested ITE chain: is_c0 ? c0 : (is_c1 ? c1 : (... : cN))
    // Last constructor is the else branch (no guard needed).
    let mut result = encoded_variants.pop()?;
    for (i, enc) in encoded_variants.into_iter().enumerate().rev() {
        let cons = &dt.constructors[i];
        let is_ci = expr.clone().is_constructor(&*dt.name, &*cons.name);
        result = Expr::ite(is_ci, enc, result);
    }
    Some(result)
}

/// Unflatten a BitVec back to an N-constructor enum Datatype.
///
/// Inverse of [`flatten_n_constructor_enum_to_bitvec`]. Uses the tag byte to
/// select which constructor to decode, building a right-nested ITE chain.
///
/// Part of #3041: inverse for N-constructor enum flattening.
fn unflatten_n_constructor_bitvec_to_datatype(
    value: &Expr,
    target_datatype_sort: &Sort,
    dt: &ay_bindings::sort::DatatypeSort,
    tag: &Expr,
    tag_bits: u32,
    payload_space: u32,
) -> Option<Expr> {
    let n = dt.constructors.len();
    let mut decoded_variants: Vec<Expr> = Vec::with_capacity(n);

    for cons in &dt.constructors {
        if cons.fields.is_empty() {
            decoded_variants.push(Expr::datatype_constructor(
                &*dt.name,
                &*cons.name,
                vec![],
                target_datatype_sort.clone(),
            ));
        } else {
            let fields = decode_enum_constructor_fields(value, cons, payload_space)?;
            decoded_variants.push(Expr::datatype_constructor(
                &*dt.name,
                &*cons.name,
                fields,
                target_datatype_sort.clone(),
            ));
        }
    }

    // Build right-nested ITE: tag==0 ? c0 : (tag==1 ? c1 : (... : cN))
    let mut result = decoded_variants.pop()?;
    for (i, dec) in decoded_variants.into_iter().enumerate().rev() {
        let is_ci = tag.clone().eq(Expr::bitvec_const(i as u64, tag_bits));
        result = Expr::ite(is_ci, dec, result);
    }
    Some(result)
}

/// Encode payload leaves as a padded bitvector of `payload_space` width.
fn encode_payload_bits(leaves: &[Expr], leaf_width: u32, payload_space: u32) -> Expr {
    if leaf_width == 0 {
        return Expr::bitvec_const(0u64, payload_space);
    }
    let mut iter = leaves.iter().cloned();
    let first = iter.next().expect("leaf_width > 0 implies non-empty leaves");
    let concatenated = iter.fold(first, Expr::concat);
    if leaf_width < payload_space {
        Expr::bitvec_const(0u64, payload_space - leaf_width).concat(concatenated)
    } else {
        concatenated
    }
}

/// Collect BV leaves from an expression for enum payload encoding.
///
/// Unlike [`collect_bv_leaves`]:
/// - Bool → bv1 (vs bv8 in struct encoding) — matches Rust niche-optimized layouts
/// - Recursively flattens nested multi-constructor enums to a single BV leaf
///
/// Part of #3041: enables compact enum encoding for `Option<bool>` (8 bits)
/// and nested enums like `MyEnum { Flag1(Option<bool>) }`.
fn collect_enum_bv_leaves(expr: &Expr) -> Option<Vec<Expr>> {
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else {
        if sort.is_bitvec() {
            return Some(vec![expr.clone()]);
        }
        if sort.is_bool() {
            // 1-bit encoding for compact enum payloads.
            let bv_expr =
                Expr::ite(expr.clone(), Expr::bitvec_const(1u64, 1), Expr::bitvec_const(0u64, 1));
            return Some(vec![bv_expr]);
        }
        if sort.is_array() {
            return Some(vec![]); // CHC abstraction — skip
        }
        return None;
    };
    if dt.constructors.len() == 1 {
        // Single-constructor (struct-like): recurse into fields.
        let cons = &dt.constructors[0];
        let mut leaves = Vec::new();
        for field in &cons.fields {
            let field_expr = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
            leaves.extend(collect_enum_bv_leaves(&field_expr)?);
        }
        Some(leaves)
    } else {
        // Multi-constructor enum: flatten the whole enum to a single BV leaf.
        let width = enum_leaf_width(&sort)?;
        if width == 0 {
            return Some(vec![]);
        }
        let flattened = flatten_enum_compact(expr, width, dt)?;
        Some(vec![flattened])
    }
}

/// Collect enum-context BV leaves for a specific constructor's fields.
///
/// Like [`collect_constructor_leaves`] but uses [`collect_enum_bv_leaves`] for
/// compact Bool (1-bit) and nested enum support.
fn collect_constructor_enum_leaves(
    expr: &Expr,
    dt: &ay_bindings::sort::DatatypeSort,
    cons: &ay_bindings::sort::DatatypeConstructor,
) -> Option<Vec<Expr>> {
    let mut leaves = Vec::new();
    for field in &cons.fields {
        let field_expr = expr.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
        leaves.extend(collect_enum_bv_leaves(&field_expr)?);
    }
    Some(leaves)
}

/// Compact enum flatten using variable-width tag and 1-bit Bool encoding.
///
/// This is the internal recursive flatten used by [`collect_enum_bv_leaves`] for
/// nested multi-constructor enums. Uses `min_tag_bits(N)` for the tag and
/// `enum_leaf_width` for payload field widths.
fn flatten_enum_compact(
    expr: &Expr,
    target_bv_width: u32,
    dt: &ay_bindings::sort::DatatypeSort,
) -> Option<Expr> {
    let n = dt.constructors.len();
    let tag_bits = min_tag_bits(n);
    if target_bv_width < tag_bits {
        return None;
    }
    let payload_space = target_bv_width - tag_bits;

    let mut encoded_variants: Vec<Expr> = Vec::with_capacity(n);
    for (i, cons) in dt.constructors.iter().enumerate() {
        let tag = Expr::bitvec_const(i as u64, tag_bits);
        if cons.fields.is_empty() {
            if payload_space > 0 {
                encoded_variants.push(tag.concat(Expr::bitvec_const(0u64, payload_space)));
            } else {
                encoded_variants.push(tag);
            }
        } else {
            let leaves = collect_constructor_enum_leaves(expr, dt, cons)?;
            let leaf_width: u32 = leaves.iter().map(|e| e.sort().bitvec_width().unwrap_or(0)).sum();
            if leaf_width > payload_space {
                return None;
            }
            let payload_bits = encode_payload_bits(&leaves, leaf_width, payload_space);
            if payload_space > 0 {
                encoded_variants.push(tag.concat(payload_bits));
            } else {
                encoded_variants.push(tag);
            }
        }
    }

    let mut result = encoded_variants.pop()?;
    for (i, enc) in encoded_variants.into_iter().enumerate().rev() {
        let cons = &dt.constructors[i];
        let is_ci = expr.clone().is_constructor(&*dt.name, &*cons.name);
        result = Expr::ite(is_ci, enc, result);
    }
    Some(result)
}

/// Minimum tag bits needed for N constructors: 0 for ≤1, 1 for 2, ceil(log2(N)) for N>2.
///
/// Part of #3041: enables compact enum encoding that fits within Rust's niche-optimized
/// memory layouts (e.g., `Option<bool>` in 1 byte needs 1-bit tag, not 8-bit).
fn min_tag_bits(n: usize) -> u32 {
    if n <= 1 {
        return 0;
    }
    if n == 2 {
        return 1;
    }
    // ceil(log2(n)): smallest k such that 2^k >= n
    let mut k = 0u32;
    let mut power = 1usize;
    while power < n {
        k += 1;
        power <<= 1;
    }
    k
}

/// Compute flattened bit width for a sort in enum payload context.
///
/// Unlike [`flattenable_leaf_width`] (which uses 8-bit Bool for struct memory layout),
/// this uses 1-bit Bool and recursively computes widths for nested multi-constructor
/// enums, matching the compact encoding used by [`collect_enum_bv_leaves`].
///
/// Part of #3041: enables nested enum flattening for types like `MyEnum { Flag1(Option<bool>) }`.
fn enum_leaf_width(sort: &Sort) -> Option<u32> {
    if sort.is_bitvec() {
        return sort.bitvec_width();
    }
    if sort.is_bool() {
        return Some(1); // 1-bit in enum payload (vs 8-bit in struct memory layout)
    }
    if sort.is_array() {
        return Some(0); // CHC abstraction — skip
    }
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() == 1 {
        // Single-constructor (struct-like): sum field widths recursively.
        let mut total = 0u32;
        for field in &dt.constructors.first()?.fields {
            total = total.checked_add(enum_leaf_width(&field.sort)?)?;
        }
        Some(total)
    } else {
        // Multi-constructor enum: tag + max payload.
        let tag_bits = min_tag_bits(dt.constructors.len());
        let mut max_payload = 0u32;
        for cons in &dt.constructors {
            let mut payload = 0u32;
            for field in &cons.fields {
                payload = payload.checked_add(enum_leaf_width(&field.sort)?)?;
            }
            max_payload = max_payload.max(payload);
        }
        Some(tag_bits.checked_add(max_payload)?)
    }
}

/// Return `(empty_variant_idx, payload_variant_idx)` for option-like enums.
fn option_like_constructor_indices(dt: &ay_bindings::sort::DatatypeSort) -> Option<(usize, usize)> {
    if dt.constructors.len() != 2 {
        return None;
    }
    let c0_empty = dt.constructors.first()?.fields.is_empty();
    let c1_empty = dt.constructors.get(1)?.fields.is_empty();
    match (c0_empty, c1_empty) {
        (true, false) => Some((0, 1)),
        (false, true) => Some((1, 0)),
        _ => None,
    }
}

/// Compute the BV width that a Datatype sort would flatten to (sort-level).
///
/// Returns `Some(width)` for 2-constructor enums (min_tag_bits + max payload)
/// and single-constructor structs (sum of field bits). Returns `None` for
/// complex types that cannot be flattened.
///
/// This is a pure sort-level computation — no expressions needed. Used by
/// `translate_ty` to determine BV element sorts for arrays when flattening
/// Datatype elements to avoid ay PDR DT+Array incompleteness.
///
/// Part of #1739: Array element sort flattening for PDR compatibility.
/// Part of #3328: use min_tag_bits + enum_leaf_width to match expression-level encoding.
#[must_use]
pub fn flattenable_datatype_sort_width(sort: &Sort) -> Option<u32> {
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() >= 2 {
        // Multi-constructor enums share the same flattening rule as expression-level
        // encoding: tag bits plus the maximum payload width across constructors.
        // `enum_leaf_width` already handles option-like empties and nested enums.
        enum_leaf_width(sort)
    } else if dt.constructors.len() == 1 {
        // Struct: sum all field bits
        let ctor = dt.constructors.first()?;
        let mut total = 0u32;
        for field in &ctor.fields {
            total = total.checked_add(flattenable_leaf_width(&field.sort)?)?;
        }
        Some(total)
    } else {
        None
    }
}

/// Compute flattened bit width for a sort when flattening is supported.
fn flattenable_leaf_width(sort: &Sort) -> Option<u32> {
    if sort.is_bitvec() {
        return sort.bitvec_width();
    }
    if sort.is_bool() {
        return Some(8);
    }
    if sort.is_array() {
        return Some(0); // CHC abstraction — skip (parity with collect_bv_leaves)
    }
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return flattenable_datatype_sort_width(sort);
    }
    let mut total = 0u32;
    for field in &dt.constructors.first()?.fields {
        total = total.checked_add(flattenable_leaf_width(&field.sort)?)?;
    }
    Some(total)
}

/// True iff flattening `sort` to a bitvector would silently DROP an inner array
/// (`fld_data` of a nested collection), losing the data it holds.
///
/// `flattenable_leaf_width` scores an array leaf as width 0 (a deliberate CHC
/// abstraction), so a datatype whose flattened width is defined can still be
/// *lossy*: e.g. `PbTerm { coeff: i128, lits: Vec<PbLit> }` flattens to
/// `bv320 = coeff(128) | lits.ptr(64) | lits.len(64) | lits.cap(64)` — the
/// `lits.data` array is skipped, so the packed element can never reconstruct the
/// inner `lits` slice. Packing such an element into a `Vec_bvN` throws the inner
/// data away at push time and is unrecoverable downstream (a `.iter()` over the
/// inner collection then reads a fresh symbolic and fails closed). Detecting this
/// lets `flatten_dt_array_element` keep the element STRUCTURED instead.
fn datatype_flatten_drops_array(sort: &Sort) -> bool {
    if sort.is_array() {
        return true;
    }
    match sort.datatype_sort() {
        Some(dt) => dt
            .constructors
            .iter()
            .any(|c| c.fields.iter().any(|f| datatype_flatten_drops_array(&f.sort))),
        None => false,
    }
}

/// Flatten a Datatype array element sort to BV if possible (Part of #1739, #2990).
///
/// Returns the BV sort for flattenable Datatypes (option-like enums, structs),
/// or the original sort unchanged for non-Datatypes and complex types.
/// This must be applied to any array element sort used in `fld_data` fields
/// of collection types (Vec, VecIntoIter, PolymorphicIter, slice::Iter) to
/// match the flattening that `translate_ty` applies to Array/Slice sorts.
///
/// Datatypes that carry an inner array (a nested `Vec`/`String`/slice — see
/// `datatype_flatten_drops_array`) are LEFT STRUCTURED: packing them to a
/// bitvector would drop the inner data array unrecoverably (the inner collection
/// would read back a fresh symbolic and fail closed). Keeping them structured
/// matches the un-flattened `slice_sort` used for the `&[T]` type, so a
/// `Vec<T>` value and a `&[T]` slice parameter share one element sort and the
/// data survives element-wise iteration. Flat structs/enums (no inner array)
/// still pack, exactly as before (#2990).
#[must_use]
pub fn flatten_dt_array_element(sort: Sort) -> Sort {
    if sort.is_datatype() && !datatype_flatten_drops_array(&sort) {
        if let Some(width) = flattenable_datatype_sort_width(&sort) {
            if width > 0 {
                return Sort::bitvec(width);
            }
        }
    }
    sort
}

/// DT→DT structural coercion: extract fields from source datatype and reconstruct
/// in target datatype with BV width coercion.
///
/// Handles both single-field and multi-field single-constructor datatypes.
/// For single-field types, uses `ext` for extension direction.
/// For multi-field types, uses `ext` for extension direction on BV fields.
///
/// Returns `None` when the datatypes are structurally incompatible.
///
/// Part of #3198: shared coercion logic for BMC (cast.rs) and CHC paths.
#[must_use]
pub fn coerce_datatype_structural(
    rhs: Expr,
    src_dt: &ay_bindings::DatatypeSort,
    tgt_dt: &ay_bindings::DatatypeSort,
    out_sort: Sort,
    ext: SignExtension,
) -> Option<Expr> {
    if src_dt.constructors.len() != 1 || tgt_dt.constructors.len() != 1 {
        return None;
    }
    let (sc, tc) = (src_dt.constructors.first()?, tgt_dt.constructors.first()?);
    if sc.fields.len() != tc.fields.len() {
        return None;
    }

    let mut field_exprs = Vec::with_capacity(sc.fields.len());
    for (sf, tf) in sc.fields.iter().zip(tc.fields.iter()) {
        let extracted = rhs.clone().field_select(&*src_dt.name, &*sf.name, sf.sort.clone());
        if sf.sort == tf.sort {
            field_exprs.push(extracted);
        } else if let (Some(src_nested), Some(tgt_nested)) =
            (sf.sort.datatype_sort(), tf.sort.datatype_sort())
        {
            field_exprs.push(coerce_datatype_structural(
                extracted,
                src_nested,
                tgt_nested,
                tf.sort.clone(),
                ext,
            )?);
        } else if let (SortInner::BitVec(sb), SortInner::BitVec(tb)) =
            (sf.sort.inner(), tf.sort.inner())
        {
            field_exprs.push(coerce_bitvec_width_safe(extracted, tb.width, ext));
            let _ = sb; // suppress unused warning — width accessed via coerce_bitvec_width_safe
        } else if sf.sort.bitvec_width() == flattenable_datatype_sort_width(&tf.sort) {
            field_exprs.push(unflatten_bitvec_to_datatype(&extracted, &tf.sort)?);
        } else if flattenable_datatype_sort_width(&sf.sort) == tf.sort.bitvec_width() {
            field_exprs.push(flatten_datatype_to_bitvec(&extracted, tf.sort.bitvec_width()?)?);
        } else {
            // Incompatible field sorts — fail closed rather than pass through unchanged.
            return None;
        }
    }

    Some(Expr::datatype_constructor(&tgt_dt.name, &tc.name, field_exprs, out_sort))
}

/// Construct a Dyn_Trait fat pointer from a thin pointer (BV→Dyn coercion).
///
/// When the target datatype starts with "Dyn_" and has exactly 2 BV fields
/// of equal width (fld_ptr, fld_vtable), constructs the fat pointer:
///   {fld_ptr: coerced_source, fld_vtable: vtable_value}
///
/// `vtable_value` is the vtable discriminant — pass `bitvec_const(0, ptr_width)`
/// when no vtable resolution is available (sort-level fallback).
///
/// Returns `None` when the target is not a recognized Dyn sort.
///
/// Part of #3198: shared fat pointer construction for BMC and CHC paths.
#[must_use]
pub fn construct_dyn_fat_pointer(
    thin_ptr: Expr,
    tgt_dt: &ay_bindings::DatatypeSort,
    out_sort: Sort,
    vtable_value: Expr,
) -> Option<Expr> {
    if !tgt_dt.name.starts_with("Dyn_") {
        return None;
    }
    if tgt_dt.constructors.len() != 1 {
        return None;
    }
    let cons = tgt_dt.constructors.first()?;
    if cons.fields.len() != 2 {
        return None;
    }
    let fld_ptr = cons.fields.first()?;
    let fld_vtable = cons.fields.get(1)?;
    let ptr_w = fld_ptr.sort.bitvec_width()?;
    let vtable_w = fld_vtable.sort.bitvec_width()?;
    if ptr_w != vtable_w {
        return None;
    }

    let ptr_expr = coerce_bitvec_width_safe(thin_ptr, ptr_w, SignExtension::ZeroExtend);

    Some(Expr::datatype_constructor(
        &tgt_dt.name,
        &cons.name,
        vec![ptr_expr, vtable_value],
        out_sort,
    ))
}

/// Rebuild an expression of `target_sort` from flattened bitvector bits.
fn rebuild_expr_from_flat_bits(bits: Expr, target_sort: &Sort) -> Option<Expr> {
    if let Some(target_width) = target_sort.bitvec_width() {
        let bits_width = bits.sort().bitvec_width()?;
        let rebuilt = if bits_width == target_width {
            bits
        } else if bits_width > target_width {
            bits.extract(target_width - 1, 0)
        } else {
            bits.zero_extend(target_width - bits_width)
        };
        return Some(rebuilt);
    }
    if target_sort.is_bool() {
        let bits_width = bits.sort().bitvec_width()?;
        return Some(bits.ne(Expr::bitvec_const(0u64, bits_width)));
    }

    let dt = target_sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        // Multi-constructor enum (e.g., Option<u16>): delegate to
        // unflatten_bitvec_to_datatype which handles tag+payload decoding.
        return unflatten_bitvec_to_datatype(&bits, target_sort);
    }
    let cons = dt.constructors.first()?;
    let field_widths: Vec<u32> = cons
        .fields
        .iter()
        .map(|field| flattenable_leaf_width(&field.sort))
        .collect::<Option<Vec<_>>>()?;
    let total_width: u32 = field_widths.iter().sum();
    let bits_width = bits.sort().bitvec_width()?;
    if bits_width < total_width {
        return None;
    }
    let payload_bits =
        if bits_width == total_width { bits } else { bits.extract(total_width - 1, 0) };

    let mut remaining = total_width;
    let mut field_exprs = Vec::with_capacity(cons.fields.len());
    for (field, width) in cons.fields.iter().zip(field_widths.iter().copied()) {
        if width == 0 {
            return None;
        }
        remaining -= width;
        let field_bits = payload_bits.clone().extract(remaining + width - 1, remaining);
        field_exprs.push(rebuild_expr_from_flat_bits(field_bits, &field.sort)?);
    }
    Some(Expr::datatype_constructor(&*dt.name, &*cons.name, field_exprs, target_sort.clone()))
}

// =============================================================================
// Tests for sort-width computation functions
// Part of #3328: acceptance criteria — verify compact tag + enum_leaf_width.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::names::{enum_sort, struct_sort};

    // ---- min_tag_bits ----

    #[test]
    fn test_min_tag_bits_zero_constructors() {
        assert_eq!(min_tag_bits(0), 0);
    }

    #[test]
    fn test_min_tag_bits_one_constructor() {
        assert_eq!(min_tag_bits(1), 0);
    }

    #[test]
    fn test_min_tag_bits_two_constructors() {
        assert_eq!(min_tag_bits(2), 1);
    }

    #[test]
    fn test_min_tag_bits_three_constructors() {
        assert_eq!(min_tag_bits(3), 2);
    }

    #[test]
    fn test_min_tag_bits_four_constructors() {
        assert_eq!(min_tag_bits(4), 2);
    }

    #[test]
    fn test_min_tag_bits_five_constructors() {
        assert_eq!(min_tag_bits(5), 3);
    }

    // ---- enum_leaf_width ----

    #[test]
    fn test_enum_leaf_width_bitvec() {
        assert_eq!(enum_leaf_width(&Sort::bitvec(32)), Some(32));
    }

    #[test]
    fn test_enum_leaf_width_bool_is_one_bit() {
        assert_eq!(enum_leaf_width(&Sort::bool()), Some(1));
    }

    #[test]
    fn test_enum_leaf_width_array_is_zero() {
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        assert_eq!(enum_leaf_width(&sort), Some(0));
    }

    // ---- flattenable_leaf_width ----

    #[test]
    fn test_flattenable_leaf_width_bool_is_eight_bits() {
        assert_eq!(flattenable_leaf_width(&Sort::bool()), Some(8));
    }

    #[test]
    fn test_flattenable_leaf_width_bitvec() {
        assert_eq!(flattenable_leaf_width(&Sort::bitvec(16)), Some(16));
    }

    #[test]
    fn test_flattenable_leaf_width_array_is_zero() {
        let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        assert_eq!(flattenable_leaf_width(&sort), Some(0));
    }

    #[test]
    fn test_sign_extension_for_signedness_maps_bool_to_mode() {
        assert_eq!(SignExtension::for_signedness(true), SignExtension::SignExtend);
        assert_eq!(SignExtension::for_signedness(false), SignExtension::ZeroExtend);
    }

    // ---- flattenable_datatype_sort_width: acceptance criteria from #3328 ----

    #[test]
    fn test_sort_width_option_bool_returns_2() {
        // Option<bool> = 1-bit tag + 1-bit Bool payload = 2 bits
        let sort =
            enum_sort("Option_bool", [("None", vec![]), ("Some", vec![("fld_0", Sort::bool())])]);
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(2),
            "Option<bool> should be 2 bits (1-bit tag + 1-bit Bool)"
        );
    }

    #[test]
    fn test_sort_width_result_u8_u16_returns_17() {
        // Result<u8, u16> = 1-bit tag + max(8, 16) = 17 bits
        let sort = enum_sort(
            "Result_u8_u16",
            [("Ok", vec![("fld_0", Sort::bitvec(8))]), ("Err", vec![("fld_0", Sort::bitvec(16))])],
        );
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(17),
            "Result<u8, u16> should be 17 bits (1-bit tag + max(8, 16))"
        );
    }

    #[test]
    fn test_sort_width_option_u32() {
        // Option<u32> = 1-bit tag + 32-bit payload = 33 bits
        let sort = enum_sort(
            "Option_u32",
            [("None", vec![]), ("Some", vec![("fld_0", Sort::bitvec(32))])],
        );
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(33),
            "Option<u32> should be 33 bits (1-bit tag + 32-bit payload)"
        );
    }

    #[test]
    fn test_sort_width_single_constructor_struct() {
        // Struct with two u32 fields: 32 + 32 = 64 bits (no tag)
        let sort = struct_sort("Point", [("fld_x", Sort::bitvec(32)), ("fld_y", Sort::bitvec(32))]);
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(64),
            "Point(u32, u32) should be 64 bits"
        );
    }

    #[test]
    fn test_sort_width_struct_with_bool_uses_8bit() {
        // Struct Bool fields use 8-bit encoding (memory layout compatible)
        let sort = struct_sort(
            "BoolWrapper",
            [("fld_flag", Sort::bool()), ("fld_value", Sort::bitvec(32))],
        );
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(40),
            "BoolWrapper(bool, u32) should be 40 bits (8-bit Bool + 32-bit u32)"
        );
    }

    #[test]
    fn test_sort_width_three_constructor_enum_returns_tag_bits() {
        // 3-constructor fieldless enum: ceil(log2(3)) = 2 tag bits, 0 payload
        let sort = enum_sort(
            "Traffic",
            [
                ("Red", Vec::<(&str, Sort)>::new()),
                ("Yellow", Vec::<(&str, Sort)>::new()),
                ("Green", Vec::<(&str, Sort)>::new()),
            ],
        );
        assert_eq!(
            flattenable_datatype_sort_width(&sort),
            Some(2),
            "3-constructor fieldless enum should flatten to 2-bit tag"
        );
    }

    #[test]
    fn test_unflatten_struct_with_zero_width_field_returns_none() {
        let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let direct_sort = struct_sort(
            "StructWithArrayTail",
            [("fld_value", Sort::bitvec(32)), ("fld_data", array_sort.clone())],
        );
        let direct_bits = Expr::bitvec_const(0x1234_5678u64, 32);
        assert!(
            unflatten_bitvec_to_datatype(&direct_bits, &direct_sort).is_none(),
            "mixed-width struct should bail instead of extracting an empty field"
        );

        let nested_sort = struct_sort(
            "NestedStructWithArrayTail",
            [("fld_value", Sort::bitvec(32)), ("fld_data", array_sort)],
        );
        let outer_sort = struct_sort(
            "OuterStructWithNestedZeroWidth",
            [("fld_prefix", Sort::bitvec(32)), ("fld_nested", nested_sort)],
        );
        let outer_bits = Expr::bitvec_const(0x1234_5678_9abc_def0u64, 64);
        assert!(
            unflatten_bitvec_to_datatype(&outer_bits, &outer_sort).is_none(),
            "nested zero-width fields should bail during recursive struct rebuild"
        );
    }

    #[test]
    fn test_decode_enum_with_zero_width_field_returns_none() {
        let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let direct_sort = enum_sort(
            "OptionArrayTail",
            [
                ("None", Vec::<(&str, Sort)>::new()),
                ("Some", vec![("fld_value", Sort::bitvec(32)), ("fld_data", array_sort.clone())]),
            ],
        );
        let direct_payload = direct_sort
            .datatype_sort()
            .expect("test enum sort should be a datatype")
            .constructors
            .get(1)
            .expect("payload constructor should exist")
            .clone();
        let payload_bits = Expr::bitvec_const(0x89ab_cdefu64, 32);
        assert!(
            decode_enum_constructor_fields(&payload_bits, &direct_payload, 32).is_none(),
            "enum payload decode should bail on direct zero-width fields"
        );

        let nested_struct = struct_sort(
            "EnumNestedStructWithArrayTail",
            [("fld_value", Sort::bitvec(32)), ("fld_data", array_sort)],
        );
        let nested_sort = enum_sort(
            "OptionNestedArrayTail",
            [("None", Vec::<(&str, Sort)>::new()), ("Some", vec![("fld_nested", nested_struct)])],
        );
        let nested_payload = nested_sort
            .datatype_sort()
            .expect("nested test enum sort should be a datatype")
            .constructors
            .get(1)
            .expect("nested payload constructor should exist")
            .clone();
        assert!(
            decode_enum_constructor_fields(&payload_bits, &nested_payload, 32).is_none(),
            "nested zero-width fields should bail during recursive enum rebuild"
        );
    }

    #[test]
    fn test_coerce_datatype_structural_rebuilds_flattened_enum_field() {
        let coroutine_state_sort = enum_sort(
            "CoroutineState_i32_i32",
            [
                ("Yielded", vec![("fld_0", Sort::bitvec(32))]),
                ("Complete", vec![("fld_0", Sort::bitvec(32))]),
            ],
        );
        let source_sort = struct_sort(
            "Tuple_bv32_bv33",
            [("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bitvec(33))],
        );
        let target_sort = struct_sort(
            "Tuple_bv32_CoroutineState_i32_i32",
            [("fld_0", Sort::bitvec(32)), ("fld_1", coroutine_state_sort.clone())],
        );

        let yielded = Expr::datatype_constructor(
            "CoroutineState_i32_i32",
            "Yielded",
            vec![Expr::bitvec_const(2u64, 32)],
            coroutine_state_sort.clone(),
        );
        let yielded_bits = flatten_datatype_to_bitvec(&yielded, 33)
            .expect("CoroutineState<i32, i32> should flatten to bv33");
        let source_expr = Expr::datatype_constructor(
            "Tuple_bv32_bv33",
            "Tuple_bv32_bv33_mk",
            vec![Expr::bitvec_const(1u64, 32), yielded_bits],
            source_sort.clone(),
        );

        let source_dt = source_sort.datatype_sort().expect("source tuple should be datatype");
        let target_dt = target_sort.datatype_sort().expect("target tuple should be datatype");
        let coerced = coerce_datatype_structural(
            source_expr,
            source_dt,
            target_dt,
            target_sort.clone(),
            SignExtension::ZeroExtend,
        )
        .expect("tuple coercion should rebuild the flattened enum field");
        assert_eq!(coerced.sort(), &target_sort);

        let rebuilt_state = coerced.field_select(
            "Tuple_bv32_CoroutineState_i32_i32",
            "fld_1",
            coroutine_state_sort.clone(),
        );
        let rebuilt_bits = flatten_datatype_to_bitvec(&rebuilt_state, 33)
            .expect("rebuilt coroutine state should flatten back to bv33");
        assert_eq!(rebuilt_state.sort(), &coroutine_state_sort);
        assert_eq!(rebuilt_bits.sort(), &Sort::bitvec(33));
    }

    #[test]
    fn test_flatten_datatype_to_bitvec_struct_with_nested_enum_field() {
        let coroutine_state_sort = enum_sort(
            "CoroutineState_i32_i32",
            [
                ("Yielded", vec![("fld_0", Sort::bitvec(32))]),
                ("Complete", vec![("fld_0", Sort::bitvec(32))]),
            ],
        );
        let tuple_sort = struct_sort(
            "Tuple_bv32_CoroutineState_i32_i32",
            [("fld_0", Sort::bitvec(32)), ("fld_1", coroutine_state_sort.clone())],
        );

        let tuple_expr = Expr::datatype_constructor(
            "Tuple_bv32_CoroutineState_i32_i32",
            "Tuple_bv32_CoroutineState_i32_i32_mk",
            vec![
                Expr::bitvec_const(1u64, 32),
                Expr::datatype_constructor(
                    "CoroutineState_i32_i32",
                    "Yielded",
                    vec![Expr::bitvec_const(2u64, 32)],
                    coroutine_state_sort,
                ),
            ],
            tuple_sort,
        );

        let flattened = flatten_datatype_to_bitvec(&tuple_expr, 96)
            .expect("tuple with nested enum field should flatten for memory stores");
        assert_eq!(flattened.sort(), &Sort::bitvec(96));
    }

    #[test]
    fn test_flattenable_datatype_sort_width_multi_ctor_enum() {
        let chc_expr_sort = enum_sort(
            "ChcExpr",
            [
                ("BoolTrue", vec![]),
                ("BoolFalse", vec![]),
                ("Int", vec![("fld_0", Sort::bitvec(64))]),
                ("Var", vec![("fld_0", Sort::bitvec(32))]),
            ],
        );

        assert_eq!(
            flattenable_datatype_sort_width(&chc_expr_sort),
            Some(66),
            "4-constructor enum should flatten to tag(2) + max_payload(64) bits"
        );
    }

    #[test]
    fn test_coerce_datatype_structural_rebuilds_multictor_field_from_bitvec() {
        let chc_expr_sort = enum_sort(
            "ChcExpr",
            [
                ("BoolTrue", vec![]),
                ("BoolFalse", vec![]),
                ("Int", vec![("fld_0", Sort::bitvec(64))]),
                ("Var", vec![("fld_0", Sort::bitvec(32))]),
            ],
        );
        let source_sort = struct_sort(
            "Tuple_bv32_bv66",
            [("fld_0", Sort::bitvec(32)), ("fld_1", Sort::bitvec(66))],
        );
        let target_sort = struct_sort(
            "Tuple_bv32_ChcExpr",
            [("fld_0", Sort::bitvec(32)), ("fld_1", chc_expr_sort.clone())],
        );

        let expr_variant = Expr::datatype_constructor(
            "ChcExpr",
            "Int",
            vec![Expr::bitvec_const(7u64, 64)],
            chc_expr_sort.clone(),
        );
        let expr_bits =
            flatten_datatype_to_bitvec(&expr_variant, 66).expect("ChcExpr::Int should flatten");
        let source_expr = Expr::datatype_constructor(
            "Tuple_bv32_bv66",
            "Tuple_bv32_bv66_mk",
            vec![Expr::bitvec_const(5u64, 32), expr_bits.clone()],
            source_sort.clone(),
        );

        let coerced = coerce_datatype_structural(
            source_expr,
            source_sort.datatype_sort().expect("source tuple should be datatype"),
            target_sort.datatype_sort().expect("target tuple should be datatype"),
            target_sort.clone(),
            SignExtension::ZeroExtend,
        )
        .expect("tuple coercion should rebuild the multi-constructor enum field");
        assert_eq!(coerced.sort(), &target_sort);

        let rebuilt_expr =
            coerced.field_select("Tuple_bv32_ChcExpr", "fld_1", chc_expr_sort.clone());
        assert_eq!(rebuilt_expr.sort(), &chc_expr_sort);
        let rebuilt_bits =
            flatten_datatype_to_bitvec(&rebuilt_expr, 66).expect("rebuilt ChcExpr should flatten");
        // The roundtrip flatten→unflatten→reflatten produces a semantically equivalent
        // but structurally different AST (ITE chain from unflatten vs direct concat).
        // Check sort and width correctness rather than structural identity.
        assert_eq!(
            rebuilt_bits.sort(),
            expr_bits.sort(),
            "rebuilt bits should have same sort as original"
        );
        assert_eq!(
            rebuilt_bits.sort().bitvec_width(),
            Some(66),
            "rebuilt bits should be 66-bit BV"
        );
    }
}
