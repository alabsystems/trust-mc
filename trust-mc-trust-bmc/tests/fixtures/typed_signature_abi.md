# trust-ir v60 typed signature ABI golden

`typed_signature_abi.module.json` is a byte-identical copy of trust-ir's
conformance golden `crates/trust-ir-conformance/tests/fixtures/typed_signature_abi.json`
at trust-ir `7e350a122a2fd01bdb27b26dc501afe1e18c30fc` (the pin in this
workspace's manifests). It is a module with one function type that records a
typed signature ABI (wire v60 `FuncTy::abi`) trust-ir's validator accepts: an
`aarch64-apple-darwin` `C` signature with an ignored argument, a sign-extended
`i8`, a pair, a cast, a caller-copied indirect argument and a hidden result,
and the target it was recorded for.

`src/tests/typed_signature_abi.rs` attaches that signature to trust-mc's own
fixtures to check that every trust-mc entry refuses typed ABI transport
(`src/signature_abi.rs`). It is a structural input, not proof evidence.
