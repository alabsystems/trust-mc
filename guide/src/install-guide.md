# Installation

trust-mc is currently installed by building from source. Supported platforms:

* `x86_64-unknown-linux-gnu` (Most Linux distributions)
* `x86_64-apple-darwin` (Intel Mac OS)
* `aarch64-apple-darwin` (Apple Silicon Mac OS)

To use trust-mc in your GitHub CI workflows, see [GitHub CI](./install-github-ci.md).

## Dependencies

The following must already be installed:

* Rust nightly toolchain installed via `rustup`. trust-mc requires a specific nightly version pinned in `rust-toolchain.toml`. The toolchain will be installed automatically when building trust-mc.
* AY solver binary in PATH. AY is trust-mc's sole verification backend.

## Installing the latest version

Clone the repository and build:

```bash
git clone https://github.com/alabsystems/trust-mc.git
cd trust-mc
cargo build-dev -- --release
```

Then run setup to install supporting libraries:
```bash
cargo run --release --bin cargo-trust-mc -- trust-mc setup
```

The setup step will download supporting libraries and configure the verification toolchain under `target/trust-mc/` in the repository directory.
A custom path can be specified at runtime using the `TRUST_MC_SYSROOT` environment variable.

Add trust-mc to your PATH by adding the scripts directory:
```bash
export PATH=$(pwd)/scripts:$PATH
```

## Checking your installation

After you've installed trust-mc,
you can try running it by creating a test file:

```rust
// File: test.rs
#[kani::proof]
fn main() {
    assert!(1 == 2);
}
```

Run trust-mc on the single file:

```
trust-mc test.rs
```

You should get a result like this one:

```
[...]
RESULTS:
Check 1: main.assertion.1
         - Status: FAILURE
         - Description: "assertion failed: 1 == 2"
[...]
VERIFICATION:- FAILED
```

Fix the test and you should see a result like this one:

```
[...]
VERIFICATION:- SUCCESSFUL
```

## Next steps

If you're learning trust-mc for the first time, you may be interested in our [tutorial](trust-mc-tutorial.md).
