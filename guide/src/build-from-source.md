# Installing from source code

> If you were able to [install trust-mc](install-guide.md) normally, you do not need to build trust-mc from source.
> You probably want to proceed to the [trust-mc tutorial](trust-mc-tutorial.md).

## Dependencies

In general, the following dependencies are required to build trust-mc from source.

> **NOTE**: These dependencies may be installed by running the scripts shown
> below and don't need to be manually installed.

1. Cargo installed via [rustup](https://rustup.rs/)
2. [AY](https://github.com/alabsystems/ay) (trust-mc's native verification backend)

> **NOTE**: AY is trust-mc's default and only supported backend in current builds
> (`--backend` accepts `auto` and `ay`). CBMC content in this repository is
> retained as historical upstream reference, not as an active runtime backend.

> **NOTE**: the `scripts/setup/` dependency installers referenced below are
> inherited from upstream Kani and are **not present** in this repository.
> Install rustup from <https://rustup.rs/>, link the toolchain named in
> `rust-toolchain.toml`, and build the AY solver separately (see
> [Installation](./install-guide.md)) so the `ay` binary is on your PATH.

trust-mc has been tested in [Ubuntu](#install-dependencies-on-ubuntu) and [macOS](#install-dependencies-on-macos) platforms.

### AY dependency strategy

trust-mc uses **git+rev dependencies** to AY by default (pinned in `Cargo.toml`), which
ensures reproducible builds. Path dependencies (`../ay/crates/*`) can be used for
rapid co-development when a sibling AY checkout is available.

**Default setup (git+rev deps):**
```bash
git clone https://github.com/alabsystems/trust-mc.git
cd trust-mc
cargo build  # uses pinned AY rev from Cargo.toml
```

**Co-development setup (path deps):**

To use a local AY checkout for rapid co-development:

1. Clone both repos as siblings:
   ```bash
   git clone https://github.com/alabsystems/ay.git
   ```
2. The committed `[patch."https://github.com/alabsystems/ay.git"]` table in
   `Cargo.toml` already redirects the audited AY packages to that sibling.
   Check out the desired pushed commit there, keep it clean, and update the
   uniform manifest authority with
   `scripts/bump-ay-pin.py <40-char-rev> <version>`. Then run
   `scripts/check-ay-pin.sh` and the complete
   `scripts/ay-bump-canary.sh`; the latter performs the native API checks,
   rebuilds the dev sysroot once, and executes the version-sensitive corpus
   canaries against that build.

> **NOTE**: When reporting verification metrics or benchmarks, always record the
> AY commit hash used. Path dependencies are not reproducible across clones.

The measurement runners never fetch, pull, or check out the sibling AY tree.
Align it explicitly before a run; `scripts/check-ay-pin.sh` fails if its clean
HEAD is not the declared authority.

See `Cargo.toml` comments for full rationale.

### Install dependencies on Ubuntu

Support is available for Ubuntu 20.04, 22.04, and 24.04.
The simplest way to install dependencies (especially if you're using a fresh VM)
is following our CI scripts:

```
# git clone git@github.com:alabsystems/trust-mc.git
git clone https://github.com/alabsystems/trust-mc.git
cd trust-mc
 # For Ubuntu 20.04, use: `./scripts/setup/ubuntu-20.04/install_deps.sh`
./scripts/setup/ubuntu/install_deps.sh
# If you haven't already (or from https://rustup.rs/):
./scripts/setup/install_rustup.sh
source $HOME/.cargo/env
```

### Install dependencies on macOS

Support is available for macOS 11. You need to have [Homebrew](https://brew.sh/) installed already.

```
# git clone git@github.com:alabsystems/trust-mc.git
git clone https://github.com/alabsystems/trust-mc.git
cd trust-mc
./scripts/setup/macos/install_deps.sh
# If you haven't already (or from https://rustup.rs/):
./scripts/setup/install_rustup.sh
source $HOME/.cargo/env
```

## Build and test trust-mc

Build the trust-mc package using:

```
cargo build-dev -- --release
```
to compile with optimizations turned on or using:
```
cargo build-dev
```
to compile in debug/development mode.

There is no monolithic regression wrapper. Run the Rust units and the
fail-closed AY corpus gates explicitly:

```
cargo test --workspace --no-fail-fast
./scripts/ay-compiletest.sh expected
./scripts/ay-soundness-gate.sh
```

## Adding trust-mc to your path

To use a locally-built trust-mc from anywhere, add the trust-mc scripts to your path:

```bash
export PATH=$(pwd)/scripts:$PATH
```

## Next steps

If you're learning trust-mc for the first time, you may be interested in our [tutorial](trust-mc-tutorial.md).
