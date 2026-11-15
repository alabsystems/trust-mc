# Installation

trust-mc is currently installed by building from source. Supported platforms:

* `x86_64-unknown-linux-gnu` (Most Linux distributions)
* `x86_64-apple-darwin` (Intel Mac OS)
* `aarch64-apple-darwin` (Apple Silicon Mac OS)

To use trust-mc in your GitHub CI workflows, see [GitHub CI](./install-github-ci.md).

## Dependencies

The following must already be installed:

* The [Trust](https://github.com/alabsystems/trust) toolchain named by the `channel` in `rust-toolchain.toml` (`trust`): `targo`, `trustc`, `tippy`, `trustfmt`. rustup cannot fetch it; install a sealed Trust toolchain (the default [trust](https://github.com/alabsystems/trust)'s own `INSTALL.md` documents, produced by its `scripts/promote-toolchain.sh`). Build with `targo --unverified <cmd>` (development, no proof claim) or `targo trust <cmd>` (verified).
* AY solver binary in PATH. AY is trust-mc's sole verification backend.

## Installing the latest version

Clone the repository and build the engine plus its library sysroot:

```bash
git clone https://github.com/alabsystems/trust-mc.git
cd trust-mc
targo --unverified build-dev --release
```

That produces `target/trust-mc/` — the verification engine
(`trust-mc-driver`), the rustc driver (`trust-mc-compiler`), and the
pre-compiled libraries the compiler needs (`lib/`, `no_core/lib`,
`playback/lib`). Install the user-facing commands:

> **Standard-library sources.** `build-dev` rebuilds std with the rustc driver
> (`-Z build-std`). A Trust toolchain that ships no standard-library sources
> takes them from a trust checkout at the compiler's own commit: add
> `--trust-checkout <trust checkout>` after `build-dev` (or set
> `TRUST_MC_TRUST_CHECKOUT`).

```bash
targo --unverified install --path .   # trust-mc, cargo-trust-mc, targo-trust-mc
```

Then put the AY solver on your PATH — bounded runs invoke it as a
subprocess, and the engine checks for it before every verification:

```bash
git clone https://github.com/alabsystems/ay.git ../ay
(cd ../ay && targo --unverified build --release -p ay --features cli)
export PATH="$PWD/../ay/target/release:$PATH"
```

Confirm the result, which names every piece and the command that fixes a
missing one:

```bash
trust-mc doctor
```

The engine is found via `$TRUST_MC_SYSROOT`, else the nearest
`target/trust-mc` walking up from the working directory or the executable,
else a release bundle under `${KANI_HOME:-~/.kani}`. Set `TRUST_MC_SYSROOT`
to use a sysroot from anywhere.

> `trust-mc setup` installs a *published release bundle* instead of building
> from source. Releases are published — `v0.6.0` is the current one, verified
> 2026-08-30 — but they are signed source snapshots (`SHA256SUMS` plus its
> signature), not per-platform sysroot bundles, so there is still nothing for
> `setup` to fetch. Build from source for now.

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
