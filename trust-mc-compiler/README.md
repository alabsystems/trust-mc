# trust-mc Compiler

This crate contains the trust-mc compiler, which transforms Rust MIR into
verification conditions via the AY/SMT-LIB2 backend (`codegen_ay`).

This binary should not be used on its own and should be invoked via `trust-mc` or
`targo trust-mc` commands.

### Notes for developers

This binary can be built like a regular package on the Trust toolchain
(`targo --unverified build -p trust-mc-compiler`; the seal ships the rustc-dev
libraries it links). There is no need to bootstrap it anymore.
