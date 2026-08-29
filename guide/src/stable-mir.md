# Transition to StableMIR

We have partnered with the Rust compiler team in the initiative to introduce stable
APIs to the compiler that can be used by third-party tools, which is known as the
[Stable MIR Project](https://github.com/rust-lang/project-stable-mir), or just StableMIR.
This means that we are starting to use the new APIs introduced by this project as is,
despite them not being stable yet.

### StableMIR APIs

For now, the StableMIR APIs are exposed as a crate in the compiler named `rustc_public`.
This crate includes the definition of structures and methods to be stabilized,
which are expected to become the stable APIs in the compiler.
To reduce the migration burden, these APIs are somewhat close to the original compiler interfaces.
However, some changes have been made to make these APIs cleaner and easier to use.

For example:
1. The usage of the compiler context (aka `TyCtxt`) is transparent to the user.
   The StableMIR implementation caches this context in a thread local variable,
   and retrieves it whenever necessary.
    - Because of that, code that uses the StableMIR has to be invoked inside a `run` call.
2. The `DefId` has been specialized into multiple types,
   making its usage less error prone. E.g.:
   `FnDef` represents the definition of a function,
   while `StaticDef` is the definition of a static variable.
   - Note that the same `DefId` may be mapped to different definitions according to its context.
     For example, an `InstanceDef` and a `FnDef` may represent the same function definition.
3. Methods that used to be exposed as part of `TyCtxt` are now part of a type.
   Example, the function `TyCtxt.instance_mir` is now `Instance::body`.
4. There is no need for explicit instantiation (monomorphization) of items from an`Instance::body`.
   This method already instantiates all types and resolves all constants before converting
   it to stable APIs.


### Performance

Since the new APIs require converting internal data to a stable representation,
the APIs were also designed to avoid needless conversions,
and to allow extra information to be retrieved on demand.

For example, `Ty` is just an identifier, while `TyKind` is a structure that can be retrieved via `Ty::kind` method.
The `TyKind` is a more structured object, thus,
it is only generated when the `kind` method is invoked.
Since this translation is not cached,
many of the functions that the rust compiler used to expose in `Ty`,
is now only part of `TyKind`.
The reason being that there is no cache for the `TyKind`,
and users should do the caching themselves to avoid needless translations.

From our initial experiments with the transition of the reachability algorithm to use StableMIR,
there is a small penalty of using StableMIR over internal rust compiler APIs.
However, they are still fairly efficient and it did not impact the overall compilation time.

### Interface with internal APIs

To reduce the burden of migrating to StableMIR,
and to allow StableMIR to be used together with internal APIs,
there are two helpful methods to convert StableMIR constructs to internal rustc and back:
  - `rustc_internal::internal()`: Convert a Stable item into an internal one.
  - `rustc_internal::stable()`: Convert an internal item into a Stable one.

Both of these methods are inside `rustc_public_bridge` crate in the `rustc_internal`
module inside the compiler.
Note that there is no plan to stabilize any of these methods,
and there's also no guarantee on its support and coverage.

The conversion is not implemented for all items, and some conversions may be incomplete.
Please proceed with caution when using these methods.

Besides that, do not invoke any other `rustc_public_bridge` methods, except for `run`.
This crate's methods are not meant to be invoked externally.
Note that, the method `run` will also eventually be replaced by a Stable driver.

### Creating and modifying StableMIR items

For now, StableMIR should only be used to get information from the compiler.
Do not try to create or modify items directly, as it may not work.
This may result in incorrect behavior or an internal compiler error (ICE).

## Naming conventions in trust-mc

As we adopt StableMIR, we would like to introduce a few conventions to make it easier to maintain the code.
Whenever there is a name conflict, for example, `Ty` or `codegen_ty`,
use a suffix to indicate which API you are using.
`Stable` for StableMIR and `Internal` for `rustc` internal APIs.

A module should either default its naming to Stable APIs or Internal APIs.
I.e.: Modules that have been migrated to StableMIR don't need to add the `Stable` suffix to stable items.
While those that haven't been migrated, should add `Stable`, but no `Internal` is needed.

For example, the `codegen::typ` module will likely include methods:

`codegen_ty(&mut self, Ty)` and `codegen_ty_stable(&mut, TyStable)` to handle
internal and stable APIs.

## MIR Encoding and Availability

### When MIR is Encoded

Rust metadata can include encoded MIR, but this is optional and depends on how the crate was built:

1. **Default builds**: rustc only encodes `optimized_mir` for items that are:
   - Generic (needs monomorphization)
   - Marked `#[inline]`
   - Reachable from other crates

2. **Check builds** (`cargo check`): MIR encoding is skipped entirely

3. **With `-Z always-encode-mir`**: MIR is encoded for all functions with implementations

### trust-mc's Sysroot Configuration

trust-mc builds its sysroot with `-Z always-encode-mir` (see `tools/build-trust-mc/src/sysroot.rs:173`).
This ensures MIR bodies are available for stdlib functions during verification.

### When `Instance::body()` Returns None

Even with `-Z always-encode-mir`, certain categories of functions will never have MIR bodies:

| Category | Example | Why |
|----------|---------|-----|
| Foreign items | `extern "C" fn printf(...)` | Implementation is external |
| Intrinsics without fallback | `transmute`, `size_of` | Compiler magic |
| Trait methods without default | `trait Foo { fn bar(); }` | Only signature declared |
| Compiler shims | Drop glue, closure adapters | Generated on-demand |

### Impact on Verification

Functions without MIR bodies cannot be inlined by transformation passes.
They are handled at codegen time as:
- Intrinsics with special SMT semantics
- Foreign calls with stubs or unsupported markers
- trust-mc function stubs (if configured)

The `FunctionInlinePass` logs warnings when stdlib functions lack MIR bodies,
which can help identify unexpected missing implementations.

### References

- Rust Compiler Dev Guide: [Libraries and metadata](https://rustc-dev-guide.rust-lang.org/backend/libs-and-metadata.html)
- Sysroot build configuration: `tools/build-trust-mc/src/sysroot.rs:173`
- FunctionInlinePass diagnostics: `trust-mc-compiler/src/kani_middle/transform/inline/mod.rs`
