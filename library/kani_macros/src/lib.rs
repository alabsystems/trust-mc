// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// #![feature(register_tool)]
// #![register_tool(kanitool)]
// Frustratingly, it's not enough for our crate to enable these features, because we need all
// downstream crates to enable these features as well.
// So we have to enable this on the commandline (see kani-rustc) with:
//   RUSTFLAGS="-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(kanitool)"
#![cfg_attr(kani_sysroot, feature(proc_macro_diagnostic, proc_macro_span))]
#![allow(clippy::unwrap_used)] // upstream Kani proc-macro code; abort is the only error path
mod derive;
mod derive_bounded;

// proc_macro::quote is nightly-only, so we'll cobble things together instead
use proc_macro::TokenStream;
use proc_macro_error2::proc_macro_error;

#[cfg(kani_sysroot)]
use sysroot as attr_impl;

#[cfg(not(kani_sysroot))]
use regular as attr_impl;

/// Marks a Kani proof harness
///
/// For async harnesses, this will call [`block_on`](https://model-checking.github.io/kani/crates/doc/kani/futures/fn.block_on.html) to drive the future to completion (see its documentation for more information).
///
/// If you want to spawn tasks in an async harness, you have to pass a schedule to the `#[kani::proof]` attribute,
/// e.g. `#[kani::proof(schedule = kani::RoundRobin::default())]`.
///
/// This will wrap the async function in a call to [`block_on_with_spawn`](https://model-checking.github.io/kani/crates/doc/kani/futures/fn.block_on_with_spawn.html) (see its documentation for more information).
#[proc_macro_error]
#[proc_macro_attribute]
pub fn proof(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::proof(attr, item)
}

/// Marks a native Trust harness: **parameters are the nondeterministic inputs**.
///
/// The transitional native harness spelling of the trust superproject's
/// two-language spec-surface design (2026-07-09, E7,
/// §12.2, R2): instead of a zero-argument `#[kani::proof]` fn with
/// `kani::any()` lets, the harness declares its nondet inputs as ordinary
/// parameters, and the bare spec vocabulary (`any`, `assume`) is in scope in
/// the body with zero imports.
///
/// ```text
/// #[kani::harness]
/// fn check_binary_search(xs: [u32; 8], key: u32) {
///     assume(is_sorted(&xs));
///     if let Some(i) = binary_search(&xs, key) { assert!(xs[i] == key); }
/// }
/// ```
///
/// Under verification this expands to a zero-argument `#[kanitool::proof]`
/// harness whose preamble binds each parameter via `kani::any()` — exactly the
/// machinery `#[kani::proof]` uses, so verdicts are **identical by
/// construction** with the legacy spelling. Harness *modifier* attributes
/// (`#[kani::unwind]`, `#[kani::solver]`, `#[kani::stub]`,
/// `#[kani::should_panic]`) compose with `#[harness]` unchanged.
///
/// Parameter types must implement `kani::Arbitrary` (the same requirement as
/// `kani::any()`). `self`, `async`, and generic parameters are rejected.
#[proc_macro_error]
#[proc_macro_attribute]
pub fn harness(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::harness(attr, item)
}

/// Specifies that a proof harness is expected to panic.**
///
/// This attribute allows users to exercise *negative verification*.
/// It's analogous to how
/// [`#[should_panic]`](https://doc.rust-lang.org/rust-by-example/testing/unit_testing.html#testing-panics)
/// allows users to exercise [negative testing](https://en.wikipedia.org/wiki/Negative_testing)
/// for Rust unit tests.
///
/// # Limitations
///
/// The `#[kani::should_panic]` attribute verifies that there are one or more failed checks related to panics.
/// At the moment, it's not possible to pin it down to specific panics.
#[proc_macro_attribute]
pub fn should_panic(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::should_panic(attr, item)
}

/// Specifies that a function contains recursion for contract instrumentation.**
///
/// This attribute is only used for function-contract instrumentation. Kani uses
/// this annotation to identify recursive functions and properly instantiate
/// `kani::any_modifies` to check such functions using induction.
#[proc_macro_attribute]
pub fn recursion(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::recursion(attr, item)
}

/// Set Loop unwind limit for proof harnesses
/// The attribute `#[kani::unwind(arg)]` can only be called alongside `#[kani::proof]`.
/// arg - Takes in a integer value (u32) that represents the unwind value for the harness.
#[allow(clippy::too_long_first_doc_paragraph)]
#[proc_macro_attribute]
pub fn unwind(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::unwind(attr, item)
}

/// Specify a function/method stub pair to use for proof harness
///
/// The attribute `#[kani::stub(original, replacement)]` can only be used alongside `#[kani::proof]`.
///
/// # Arguments
/// * `original` - The function or method to replace, specified as a path.
/// * `replacement` - The function or method to use as a replacement, specified as a path.
#[proc_macro_attribute]
pub fn stub(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::stub(attr, item)
}

/// Define a reusable set of stubs.
///
/// Stub sets can be selected on a proof harness with `#[kani::use_stub_set(name)]`.
#[proc_macro]
pub fn stub_set(item: TokenStream) -> TokenStream {
    attr_impl::stub_set(item)
}

/// Apply a reusable stub set to a proof harness.
///
/// The argument names a `kani::stub_set!` declaration in the current crate.
/// This is equivalent to attaching every stub in that set to the harness.
#[proc_macro_attribute]
pub fn use_stub_set(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::use_stub_set(attr, item)
}

/// Select the SMT solver to use with AY for this harness
///
/// The attribute `#[kani::solver(arg)]` can only be used alongside `#[kani::proof]`.
///
/// arg - name of solver, e.g. z3, cvc5
#[proc_macro_attribute]
pub fn solver(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::solver(attr, item)
}

/// Mark an API as unstable. This should only be used inside the Kani sysroot.
/// See https://model-checking.github.io/kani/rfc/rfcs/0006-unstable-api.html for more details.
#[doc(hidden)]
#[proc_macro_attribute]
pub fn unstable_feature(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::unstable(attr, item)
}

/// Allow users to auto generate `Arbitrary` implementations by using
/// `#[derive(Arbitrary)]` macro.
///
/// ## Type safety specification with the `#[safety_constraint(...)]` attribute
///
/// When using `#[derive(Arbitrary)]` on a struct, the
/// `#[safety_constraint(<cond>)]` attribute can be added to either the struct
/// or its fields (but not both) to indicate a type safety invariant condition
/// `<cond>`. Since `kani::any()` is always expected to produce type-safe
/// values, **adding `#[safety_constraint(...)]` to the struct or any of its
/// fields will further constrain the objects generated with `kani::any()`**.
///
/// For example, the `check_positive` harness in this code is expected to
/// pass:
///
/// ```text
/// #[derive(kani::Arbitrary)]
/// struct AlwaysPositive {
///     #[safety_constraint(*inner >= 0)]
///     inner: i32,
/// }
///
/// #[kani::proof]
/// fn check_positive() {
///     let val: AlwaysPositive = kani::any();
///     assert!(val.inner >= 0);
/// }
/// ```
///
/// But using the `#[safety_constraint(...)]` attribute can lead to vacuous
/// results when the values are over-constrained. For example, in this code
/// the `check_positive` harness will pass too:
///
/// ```text
/// #[derive(kani::Arbitrary)]
/// struct AlwaysPositive {
///     #[safety_constraint(*inner >= 0 && *inner < i32::MIN)]
///     inner: i32,
/// }
///
/// #[kani::proof]
/// fn check_positive() {
///     let val: AlwaysPositive = kani::any();
///     assert!(val.inner >= 0);
/// }
/// ```
///
/// Unfortunately, we made a mistake when specifying the condition because
/// `*inner >= 0 && *inner < i32::MIN` is equivalent to `false`. This results
/// in the relevant assertion being unreachable:
///
/// ```text
/// Check 1: check_positive.assertion.1
///         - Status: UNREACHABLE
///         - Description: "assertion failed: val.inner >= 0"
///         - Location: src/main.rs:22:5 in function check_positive
/// ```
///
/// As usual, we recommend users to defend against these behaviors by using
/// `kani::cover!(...)` checks and watching out for unreachable assertions in
/// their project's code.
///
/// ### Adding `#[safety_constraint(...)]` to the struct as opposed to its fields
///
/// As mentioned earlier, the `#[safety_constraint(...)]` attribute can be added
/// to either the struct or its fields, but not to both. Adding the
/// `#[safety_constraint(...)]` attribute to both the struct and its fields will
/// result in an error.
///
/// In practice, only one type of specification is need. If the condition for
/// the type safety invariant involves a relation between two or more struct
/// fields, the struct-level attribute should be used. Otherwise, using the
/// `#[safety_constraint(...)]` on field(s) is recommended since it helps with readability.
///
/// For example, if we were defining a custom vector `MyVector` and wanted to
/// specify that the inner vector's length is always less than or equal to its
/// capacity, we should do it as follows:
///
/// ```text
/// #[derive(Arbitrary)]
/// #[safety_constraint(vector.len() <= *capacity)]
/// struct MyVector<T> {
///     vector: Vec<T>,
///     capacity: usize,
/// }
/// ```
///
/// However, if we were defining a struct whose fields are not related in any
/// way, we would prefer using the `#[safety_constraint(...)]` attribute on its
/// fields:
///
/// ```text
/// #[derive(Arbitrary)]
/// struct PositivePoint {
///     #[safety_constraint(*x >= 0)]
///     x: i32,
///     #[safety_constraint(*y >= 0)]
///     y: i32,
/// }
/// ```
#[proc_macro_error]
#[proc_macro_derive(Arbitrary, attributes(safety_constraint))]
pub fn derive_arbitrary(item: TokenStream) -> TokenStream {
    derive::expand_derive_arbitrary(item)
}

/// Allow users to generate `BoundedArbitrary` implementations by using the
/// `#[derive(BoundedArbitrary)]` macro.
///
/// ## Specifying bounded fields
///
/// By default, every field of a struct is required to derive `Arbitrary`, not
/// `BoundedArbitrary`. This is because there is no general way to determine if a
/// particular field should be bounded or not. You must annotate the fields you want
/// to be bounded using the `#[bounded]` attribute.
///
/// For example, we only want the vector field in the following definition to be
/// bounded.
///
/// ```text
/// #[derive(BoundedArbitrary)]
/// struct MyVector<T> {
///     #[bounded]
///     vector: Vec<T>,
///     capacity: usize
/// }
/// ```
///
/// ## Safety
///
/// Using `BoundedArbitrary` makes proofs incomplete. It is useful for increasing
/// confidence that some code is correct, but does not prove that absolutely.
#[proc_macro_error]
#[proc_macro_derive(BoundedArbitrary, attributes(bounded))]
pub fn derive_bounded_arbitrary(item: TokenStream) -> TokenStream {
    derive_bounded::expand_derive_bounded_arbitrary(item)
}

/// Allow users to auto generate `Invariant` implementations by using
/// `#[derive(Invariant)]` macro.
///
/// ## Type safety specification with the `#[safety_constraint(...)]` attribute
///
/// When using `#[derive(Invariant)]` on a struct, the
/// `#[safety_constraint(<cond>)]` attribute can be added to either the struct
/// or its fields (but not both) to indicate a type safety invariant condition
/// `<cond>`. This will ensure that the type-safety condition gets additionally
/// checked when using the `is_safe()` method automatically generated by the
/// `#[derive(Invariant)]` macro.
///
/// For example, the `check_positive` harness in this code is expected to
/// fail:
///
/// ```text
/// #[derive(kani::Invariant)]
/// struct AlwaysPositive {
///     #[safety_constraint(*inner >= 0)]
///     inner: i32,
/// }
///
/// #[kani::proof]
/// fn check_positive() {
///     let val = AlwaysPositive { inner: -1 };
///     assert!(val.is_safe());
/// }
/// ```
///
/// This is not too surprising since the type safety invariant that we indicated
/// is not being taken into account when we create the `AlwaysPositive` object.
///
/// As mentioned, the `is_safe()` methods generated by the
/// `#[derive(Invariant)]` macro check the corresponding `is_safe()` method for
/// each field in addition to any type safety invariants specified through the
/// `#[safety_constraint(...)]` attribute.
///
/// For example, for the `AlwaysPositive` struct from above, we will generate
/// the following implementation:
///
/// ```text
/// impl kani::Invariant for AlwaysPositive {
///     fn is_safe(&self) -> bool {
///         let obj = self;
///         let inner = &obj.inner;
///         true && *inner >= 0 && inner.is_safe()
///     }
/// }
/// ```
///
/// Note: the assignments to `obj` and `inner` are made so that we can treat the
/// fields as if they were references.
///
/// ### Adding `#[safety_constraint(...)]` to the struct as opposed to its fields
///
/// As mentioned earlier, the `#[safety_constraint(...)]` attribute can be added
/// to either the struct or its fields, but not to both. Adding the
/// `#[safety_constraint(...)]` attribute to both the struct and its fields will
/// result in an error.
///
/// In practice, only one type of specification is need. If the condition for
/// the type safety invariant involves a relation between two or more struct
/// fields, the struct-level attribute should be used. Otherwise, using the
/// `#[safety_constraint(...)]` is recommended since it helps with readability.
///
/// For example, if we were defining a custom vector `MyVector` and wanted to
/// specify that the inner vector's length is always less than or equal to its
/// capacity, we should do it as follows:
///
/// ```text
/// #[derive(Invariant)]
/// #[safety_constraint(vector.len() <= *capacity)]
/// struct MyVector<T> {
///     vector: Vec<T>,
///     capacity: usize,
/// }
/// ```
///
/// However, if we were defining a struct whose fields are not related in any
/// way, we would prefer using the `#[safety_constraint(...)]` attribute on its
/// fields:
///
/// ```text
/// #[derive(Invariant)]
/// struct PositivePoint {
///     #[safety_constraint(*x >= 0)]
///     x: i32,
///     #[safety_constraint(*y >= 0)]
///     y: i32,
/// }
/// ```
#[proc_macro_error]
#[proc_macro_derive(Invariant, attributes(safety_constraint))]
pub fn derive_invariant(item: TokenStream) -> TokenStream {
    derive::expand_derive_invariant(item)
}

/// Add a precondition to this function.
///
/// This is part of the function contract API, for more general information see
/// the [module-level documentation](../kani/contracts/index.html).
///
/// The contents of the attribute is a condition over the input values to the
/// annotated function. All Rust syntax is supported, even calling other
/// functions, but the computations must be side effect free, e.g. it cannot
/// perform I/O or use mutable memory.
///
/// Kani requires each function that uses a contract (this attribute or
/// [`ensures`][macro@ensures]) to have at least one designated
/// [`proof_for_contract`][macro@proof_for_contract] harness for checking the
/// contract.
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::requires(attr, item)
}

/// Add a postcondition to this function.
///
/// This is part of the function contract API, for more general information see
/// the [module-level documentation](../kani/contracts/index.html).
///
/// The contents of the attribute is a closure that captures the input values to
/// the annotated function and the input to the function is the return value of
/// the function passed by reference. All Rust syntax is supported, even calling
/// other functions, but the computations must be side effect free, e.g. it
/// cannot perform I/O or use mutable memory.
///
/// Kani requires each function that uses a contract (this attribute or
/// [`requires`][macro@requires]) to have at least one designated
/// [`proof_for_contract`][macro@proof_for_contract] harness for checking the
/// contract.
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::ensures(attr, item)
}

/// Designates this function as a harness to check a function contract.
///
/// The argument to this macro is the relative path (e.g. `foo` or
/// `super::some_mod::foo` or `crate::SomeStruct::foo`) to the function, the
/// contract of which should be checked.
///
/// This is part of the function contract API, for more general information see
/// the [module-level documentation](../kani/contracts/index.html).
#[proc_macro_attribute]
pub fn proof_for_contract(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::proof_for_contract(attr, item)
}

/// `stub_verified(TARGET)` is a harness attribute (to be used on
/// [`proof`][macro@proof] or [`proof_for_contract`][macro@proof_for_contract]
/// function) that replaces all occurrences of `TARGET` reachable from this
/// harness with a stub generated from the contract on `TARGET`.
///
/// The target of `stub_verified` *must* have a contract. More information about
/// how to specify a contract for your function can be found
/// [here](../contracts/index.html#specification-attributes-overview).
///
/// You may use multiple `stub_verified` attributes on a single harness.
///
/// This is part of the function contract API, for more general information see
/// the [module-level documentation](../kani/contracts/index.html).
#[proc_macro_attribute]
pub fn stub_verified(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::stub_verified(attr, item)
}

/// Declaration of an explicit write-set for the annotated function.
///
/// This is part of the function contract API, for more general information see
/// the [module-level documentation](../kani/contracts/index.html).
///
/// The contents of the attribute is a series of comma-separated expressions referencing the
/// arguments of the function. Each expression is expected to return a pointer type, i.e. `*const T`,
/// `*mut T`, `&T` or `&mut T`. The pointed-to type must implement
/// [`Arbitrary`](../kani/arbitrary/trait.Arbitrary.html).
///
/// All Rust syntax is supported, even calling other functions, but the computations must be side
/// effect free, e.g. it cannot perform I/O or use mutable memory.
///
/// Kani requires each function that uses a contract to have at least one designated
/// [`proof_for_contract`][macro@proof_for_contract] harness for checking the
/// contract.
#[proc_macro_attribute]
pub fn modifies(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::modifies(attr, item)
}

/// Add a loop invariant to this loop.
///
/// The contents of the attribute is a condition that should be satisfied at the
/// beginning of every iteration of the loop.
/// All Rust syntax is supported, even calling other functions, but
/// the computations must be side effect free, e.g. it cannot perform I/O or use
/// mutable memory.
#[proc_macro_attribute]
pub fn loop_invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::loop_invariant(attr, item)
}

/// Specify memory locations that a loop may modify.
///
/// The contents of the attribute is a comma-separated list of expressions
/// representing memory locations (pointers, references, or slices) that may
/// be written to during loop execution. Used with `loop_invariant` to enable
/// unbounded verification of loops.
///
/// Supported target types:
/// - Raw pointers: `&var as *const _`
/// - References: `&var`, `&array`
/// - Slices: `&array[start..end]`, `slice_from_raw_parts(ptr, len)`
///
/// See the Loop Contracts documentation for detailed examples.
#[proc_macro_attribute]
pub fn loop_modifies(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::loop_modifies(attr, item)
}

/// Specify a loop variant expression that must decrease on each iteration.
///
/// trust-mc parses this Kani-compatible attribute and passes it through the loop
/// contract metadata path, but termination checking for decreases clauses is not
/// implemented yet. Verification fails with an explicit unsupported diagnostic
/// instead of silently ignoring the clause.
#[proc_macro_attribute]
pub fn loop_decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    attr_impl::loop_decreases(attr, item)
}

/// This module implements Kani attributes in a way that only Kani's compiler can understand.
/// This code should only be activated when pre-building Kani's sysroot.
#[cfg(kani_sysroot)]
mod sysroot {
    use proc_macro_error2::{abort, abort_call_site};

    mod contracts;
    mod loop_contracts;

    pub(crate) use contracts::{ensures, modifies, proof_for_contract, requires, stub_verified};
    pub(crate) use loop_contracts::{loop_decreases, loop_invariant, loop_modifies};

    use super::*;

    use {
        quote::{format_ident, quote},
        syn::parse::{Parse, ParseStream},
        syn::{ItemFn, Token, parenthesized, parse_macro_input},
    };

    /// Annotate the harness with a #[kanitool::<name>] with optional arguments.
    macro_rules! kani_attribute {
        ($name:ident) => {
            pub(crate) fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
                let args = proc_macro2::TokenStream::from(attr);
                let fn_item = parse_macro_input!(item as ItemFn);
                let attribute = format_ident!("{}", stringify!($name));
                quote!(
                    #[kanitool::#attribute(#args)]
                    #fn_item
                ).into()
            }
        };
        ($name:ident, no_args) => {
            pub(crate) fn $name(attr: TokenStream, item: TokenStream) -> TokenStream {
                assert!(attr.is_empty(), "`#[kani::{}]` does not take any arguments currently", stringify!($name));
                let fn_item = parse_macro_input!(item as ItemFn);
                let attribute = format_ident!("{}", stringify!($name));
                quote!(
                    #[kanitool::#attribute]
                    #fn_item
                ).into()
            }
        };
    }

    struct ProofOptions {
        schedule: Option<syn::Expr>,
    }

    impl Parse for ProofOptions {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.is_empty() {
                Ok(ProofOptions { schedule: None })
            } else {
                let ident = input.parse::<syn::Ident>()?;
                if ident != "schedule" {
                    abort_call_site!("`{}` is not a valid option for `#[kani::proof]`.", ident;
                        help = "did you mean `schedule`?";
                        note = "for now, `schedule` is the only option for `#[kani::proof]`.";
                    );
                }
                let _ = input.parse::<syn::Token![=]>()?;
                let schedule = Some(input.parse::<syn::Expr>()?);
                Ok(ProofOptions { schedule })
            }
        }
    }

    pub(crate) fn proof(attr: TokenStream, item: TokenStream) -> TokenStream {
        let proof_options = parse_macro_input!(attr as ProofOptions);
        let fn_item = parse_macro_input!(item as ItemFn);
        let attrs = fn_item.attrs;
        let vis = fn_item.vis;
        let sig = fn_item.sig;
        let body = fn_item.block;

        let kani_attributes = quote!(
            #[allow(dead_code)]
            #[kanitool::proof]
        );

        if sig.asyncness.is_none() {
            if proof_options.schedule.is_some() {
                abort_call_site!(
                    "`#[kani::proof(schedule = ...)]` can only be used with `async` functions.";
                    help = "did you mean to make this function `async`?";
                );
            }
            // Adds `#[kanitool::proof]` and other attributes
            quote!(
                #kani_attributes
                #(#attrs)*
                #vis #sig #body
            )
            .into()
        } else {
            // For async functions, it translates to a synchronous function that calls `kani::block_on`.
            // Specifically, it translates
            // ```text
            // #[kani::proof]
            // #[attribute]
            // pub async fn harness() { ... }
            // ```
            // to
            // ```text
            // #[kanitool::proof]
            // #[attribute]
            // pub fn harness() {
            //   async fn harness() { ... }
            //   kani::block_on(harness())
            //   // OR
            //   kani::spawnable_block_on(harness(), schedule)
            //   // where `schedule` was provided as an argument to `#[kani::proof]`.
            // }
            // ```
            if !sig.inputs.is_empty() {
                abort!(
                    sig.inputs,
                    "`#[kani::proof]` cannot be applied to async functions that take arguments for now";
                    help = "try removing the arguments";
                );
            }
            let mut modified_sig = sig.clone();
            modified_sig.asyncness = None;
            let fn_name = &sig.ident;
            let schedule = proof_options.schedule;
            let block_on_call = if let Some(schedule) = schedule {
                quote!(kani::block_on_with_spawn(#fn_name(), #schedule))
            } else {
                quote!(kani::block_on(#fn_name()))
            };
            quote!(
                #kani_attributes
                #(#attrs)*
                #vis #modified_sig {
                    #sig #body
                    #block_on_call
                }
            )
            .into()
        }
    }

    /// The native-harness rewrite (two-language design E7/R2): parameters
    /// become `kani::any()` bindings, the bare vocabulary (`any`, `assume`)
    /// is imported into the body scope, and the result is a zero-argument
    /// `#[kanitool::proof]` harness — the same marker `#[kani::proof]` emits,
    /// so discovery, metadata, driving, and verdicts are shared code.
    pub(crate) fn harness(attr: TokenStream, item: TokenStream) -> TokenStream {
        if !attr.is_empty() {
            abort_call_site!("`#[kani::harness]` does not take any arguments";
                help = "harness modifiers stay separate: `#[kani::unwind(n)]`, `#[kani::solver(...)]`, `#[kani::stub(...)]`";
            );
        }
        let fn_item = parse_macro_input!(item as ItemFn);
        let attrs = fn_item.attrs;
        let vis = fn_item.vis;
        let mut sig = fn_item.sig;
        let body = fn_item.block;

        if sig.asyncness.is_some() {
            abort!(
                sig,
                "`#[kani::harness]` does not support `async` yet";
                help = "use `#[kani::proof]` (optionally with `schedule = ...`) for async harnesses";
            );
        }
        if !sig.generics.params.is_empty() {
            abort!(
                sig.generics,
                "`#[kani::harness]` functions must be monomorphic";
                help = "instantiate the generic parameters in a concrete harness";
            );
        }

        let mut preamble = proc_macro2::TokenStream::new();
        for input in &sig.inputs {
            match input {
                syn::FnArg::Typed(pat_ty) => {
                    let pat = &pat_ty.pat;
                    let ty = &pat_ty.ty;
                    preamble.extend(quote!(let #pat: #ty = kani::any();));
                }
                syn::FnArg::Receiver(recv) => {
                    abort!(recv, "`#[kani::harness]` cannot take `self`");
                }
            }
        }
        sig.inputs.clear();

        quote!(
            #[allow(dead_code)]
            #[kanitool::proof]
            #(#attrs)*
            #vis #sig {
                #[allow(unused_imports)]
                use kani::{any, assume};
                #preamble
                #body
            }
        )
        .into()
    }

    kani_attribute!(should_panic, no_args);
    kani_attribute!(recursion, no_args);
    kani_attribute!(solver);
    kani_attribute!(stub);

    struct StubSetDecl {
        vis: syn::Visibility,
        name: syn::Ident,
        entries: syn::punctuated::Punctuated<StubSetEntry, Token![,]>,
    }

    enum StubSetEntry {
        Stub { original: syn::TypePath, replacement: syn::TypePath },
        UseStubSet { path: syn::TypePath },
    }

    impl Parse for StubSetDecl {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let vis = input.parse()?;
            let name = input.parse()?;
            let entries = if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                input.parse_terminated(StubSetEntry::parse, Token![,])?
            } else {
                let content;
                parenthesized!(content in input);
                content.parse_terminated(StubSetEntry::parse, Token![,])?
            };
            Ok(Self { vis, name, entries })
        }
    }

    impl Parse for StubSetEntry {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let entry_kind: syn::Ident = input.parse()?;
            let content;
            parenthesized!(content in input);
            if entry_kind == "stub" {
                let original = content.parse()?;
                content.parse::<Token![,]>()?;
                let replacement = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("expected exactly two path arguments"));
                }
                Ok(Self::Stub { original, replacement })
            } else if entry_kind == "use_stub_set" {
                let path = content.parse()?;
                if !content.is_empty() {
                    return Err(content.error("expected exactly one path argument"));
                }
                Ok(Self::UseStubSet { path })
            } else {
                // Reproduce the offending entry verbatim so the diagnostic names
                // exactly what the user wrote, e.g. `unknown_entry (a , b)`.
                // Render the arguments by joining top-level tokens with single
                // spaces (e.g. `real_fn , mock_fn`) so the diagnostic text is
                // deterministic regardless of the token backend's source spacing.
                let args = content
                    .parse::<proc_macro2::TokenStream>()?
                    .into_iter()
                    .map(|tt| tt.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                Err(syn::Error::new(
                    entry_kind.span(),
                    format!(
                        "unknown entry in stub set: `{entry_kind} ({args})`. Expected `stub(...)` or `use_stub_set(...)`"
                    ),
                ))
            }
        }
    }

    pub(crate) fn stub_set(item: TokenStream) -> TokenStream {
        // NB: do not use `parse_macro_input!` / `syn::Error::to_compile_error`
        // here. Those emit `::core::compile_error!{…}`, and the leading-colon
        // `::core` path fails to resolve in trust-mc's harness compilation
        // (surfacing as a misleading E0433 that hides the real message). Emit an
        // *unqualified* `compile_error!` (a built-in in the prelude) instead.
        let StubSetDecl { vis, name, entries } = match syn::parse::<StubSetDecl>(item) {
            Ok(decl) => decl,
            Err(err) => {
                let msg = err.to_string();
                let span = err.span();
                return quote::quote_spanned!(span=> compile_error!{ #msg }).into();
            }
        };
        let attributes = entries.iter().map(|entry| match entry {
            StubSetEntry::Stub { original, replacement } => quote!(
                #[kanitool::stub(#original, #replacement)]
            ),
            StubSetEntry::UseStubSet { path } => quote!(
                #[kanitool::use_stub_set = stringify!(#path)]
            ),
        });
        quote!(
            #[allow(dead_code)]
            #[kanitool::stub_set]
            #(#attributes)*
            #vis fn #name() {}
        )
        .into()
    }

    pub(crate) fn use_stub_set(attr: TokenStream, item: TokenStream) -> TokenStream {
        let args = proc_macro2::TokenStream::from(attr);
        let item = proc_macro2::TokenStream::from(item);
        quote!(
            #[kanitool::use_stub_set = stringify!(#args)]
            #item
        )
        .into()
    }
    /// Accept any item (fn/enum/trait/struct) — not just `ItemFn` (#3659).
    pub(crate) fn unstable(attr: TokenStream, item: TokenStream) -> TokenStream {
        let args = proc_macro2::TokenStream::from(attr);
        let item = proc_macro2::TokenStream::from(item);
        quote!(#[kanitool::unstable(#args)] #item).into()
    }

    kani_attribute!(unwind);
}

/// This module provides dummy implementations of Kani attributes which cannot be interpreted by
/// other tools such as MIRI and the regular rust compiler.
///
/// This allow users to use code marked with Kani attributes, for example, for IDE code inspection.
#[cfg(not(kani_sysroot))]
mod regular {
    use super::*;
    /// Encode a noop proc macro which ignores the given attribute.
    macro_rules! no_op {
        ($name:ident) => {
            pub(crate) fn $name(_attr: TokenStream, item: TokenStream) -> TokenStream {
                item
            }
        };
    }

    /// Add #[allow(dead_code)] to a proof harness to avoid dead code warnings.
    pub(crate) fn proof(_attr: TokenStream, item: TokenStream) -> TokenStream {
        let mut result = TokenStream::new();
        result.extend("#[allow(dead_code)]".parse::<TokenStream>().unwrap());
        result.extend(item);
        result
    }

    /// Outside verification a native harness is dead code, like `proof`. The
    /// parameters stay as written (nothing calls the fn), but the bare
    /// vocabulary (`any`, `assume`) must still resolve for the crate to
    /// compile — so the body-scope import is injected here too.
    pub(crate) fn harness(_attr: TokenStream, item: TokenStream) -> TokenStream {
        let fn_item = syn::parse_macro_input!(item as syn::ItemFn);
        let attrs = fn_item.attrs;
        let vis = fn_item.vis;
        let sig = fn_item.sig;
        let body = fn_item.block;
        quote::quote!(
            #[allow(dead_code, unused_variables)]
            #(#attrs)*
            #vis #sig {
                #[allow(unused_imports)]
                use kani::{any, assume};
                #body
            }
        )
        .into()
    }

    no_op!(should_panic);
    no_op!(recursion);
    no_op!(solver);
    no_op!(stub);
    no_op!(use_stub_set);
    no_op!(unstable);
    no_op!(unwind);
    no_op!(requires);
    no_op!(ensures);
    no_op!(modifies);
    no_op!(proof_for_contract);
    no_op!(stub_verified);
    no_op!(loop_decreases);
    no_op!(loop_invariant);
    no_op!(loop_modifies);

    pub(crate) fn stub_set(_item: TokenStream) -> TokenStream {
        TokenStream::new()
    }
}
