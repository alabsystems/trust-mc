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

> **NOTE**: The setup scripts below install additional solvers for regression
> and benchmark workflows (cvc5, kissat) plus optional CBMC. They do **not**
> install the AY solver. Install AY separately and ensure the `ay` binary is in
> your PATH.

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
2. Uncomment the `[patch]` section in `.cargo/config.toml` to override
   git deps with your local AY checkout, then use `cargo build-dev`.
   to update pinned revisions, then run `./scripts/ay-bump-canary.sh` before
   trusting the new pin. The canary's first gate checks
   `cargo check -p trust-mc-driver --all-targets --features "ay,ay-chc-native"`
   so future `ay-chc` API visibility drift is caught early.

> **NOTE**: When reporting verification metrics or benchmarks, always record the
> AY commit hash used. Path dependencies are not reproducible across clones.

`scripts/ay-compiletest.sh` normally preserves its historical developer
convenience of auto-pulling a sibling `../ay` checkout before running. For
reproducible or self-contained runs, set `AY_SELF_CONTAINED=1`; Trust
full-verify/release environments enable this behavior automatically. In that
mode the script will not fetch or pull the sibling AY checkout unless
`AY_ALLOW_PULL=1` is set explicitly. `AY_NO_PULL=1` remains the force-off switch
and takes precedence.

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

Then, optionally, run the regression tests:

```
./scripts/trust-mc-regression.sh
```

This script has a lot of noisy output, but on a successful run you'll see at the end of the execution:

```
All trust-mc regression tests completed successfully.
```

## Adding trust-mc to your path

To use a locally-built trust-mc from anywhere, add the trust-mc scripts to your path:

```bash
export PATH=$(pwd)/scripts:$PATH
```

## Next steps

If you're learning trust-mc for the first time, you may be interested in our [tutorial](trust-mc-tutorial.md).
