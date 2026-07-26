# trust-mc Compiler

This crate contains the trust-mc compiler, which transforms Rust MIR into
verification conditions via the AY/SMT-LIB2 backend (`codegen_ay`).

This binary should not be used on its own and should be invoked via `trust-mc` or
`cargo trust-mc` commands.

### Notes for developers

This binary can be built like a regular cargo package. There is no need to
bootstrap it anymore.
