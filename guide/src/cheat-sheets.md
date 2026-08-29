# Command cheat sheets

Development work in the trust-mc project depends on multiple tools. Regardless of
your familiarity with the project, the commands below may be useful for
development purposes.

## trust-mc

### Build

```bash
# Error "'rustc' panicked at 'failed to lookup `SourceFile` in new context'"
# or similar error? Cleaning artifacts might help.
# Otherwise, comment the line below.
cargo clean
cargo build-dev
```

### Test

```bash
# Rust units and fail-closed AY corpus gates
cargo test --workspace --no-fail-fast
./scripts/ay-compiletest.sh expected
./scripts/ay-soundness-gate.sh
```

```bash
# Delete regression test caches (Linux)
rm -r build/x86_64-unknown-linux-gnu/tests/
```

```bash
# Delete regression test caches (macOS)
rm -r build/x86_64-apple-darwin/tests/
```

```bash
# Test suite run (we can only run one at a time)
# cargo run -p compiletest -- --suite ${suite} --mode ${mode}
cargo run -p compiletest -- --suite expected --mode expected
```

```bash
# Build the user guide (mdBook)
cd guide
mdbook build
```

### Debug

These can help understand what trust-mc is generating or encountering on an example or test file:

```bash
# Enable `debug!` macro logging output when running trust-mc:
trust-mc --debug file.rs
```

```bash
# Use TRUST_MC_LOG for a finer-grained control of the source and verbosity of logs.
# E.g.: The command below will print all logs from the kani_middle module.
# (KANI_LOG is also accepted as a deprecated fallback.)
TRUST_MC_LOG="kani_compiler::kani_middle=trace" trust-mc file.rs
```

```bash
# Generate a ${INPUT}.kani.mir file with a human-friendly MIR dump
# for all reachable items (functions, types) included in verification.
RUSTFLAGS="--emit mir" trust-mc ${INPUT}.rs
```

The `TRUST_MC_REACH_DEBUG` environment variable can be used to debug trust-mc's reachability analysis.
If defined, trust-mc will generate a DOT graph `${INPUT}.dot` with the graph traversed during reachability analysis.
If defined and not empty, the graph will be filtered to end at functions that contain the substring
from `TRUST_MC_REACH_DEBUG`.

Note that this will only work on debug builds.

```bash
# Generate a DOT graph ${INPUT}.dot with the graph traversed during reachability analysis
TRUST_MC_REACH_DEBUG= trust-mc ${INPUT}.rs

# Generate a DOT graph ${INPUT}.dot with the sub-graph traversed during the reachability analysis
# that connects to the given target.
TRUST_MC_REACH_DEBUG="${TARGET_ITEM}" trust-mc ${INPUT}.rs
```

## CBMC (Historical Reference)

> **Historical note**: Current trust-mc releases support `--backend=auto|ay` only.
> `--backend=cbmc` is rejected by the CLI.
> The standalone `trust-mc` front door REJECTS `--cbmc-args`, a CBMC `--solver`
> name and `--synthesize-loop-contracts` by name (usage error, exit 2) and
> prints the AY alternative; the engine keeps them as warned no-ops for
> `cargo trust-mc` drop-in scripts, where they do not affect AY verification.
> The commands below are standalone CBMC tool examples from upstream workflows.

Current trust-mc policy for legacy Kani/CBMC flags:

```bash
# Rejected by name by the `trust-mc` front door, with the AY alternative
# (still accepted as warned no-ops by the engine under `cargo trust-mc`):
trust-mc file.rs --cbmc-args --object-bits 8
trust-mc file.rs --solver kissat
trust-mc file.rs --synthesize-loop-contracts

# Rejected because trust-mc cannot produce CBMC/C artifacts:
trust-mc file.rs --gen-c
trust-mc file.rs --write-json-symtab

# Use trust-mc-native solver selection instead:
trust-mc file.rs --backend=ay --smt-solver=auto
```

```bash
# See CBMC IR from a C file (goto binary output):
goto-cc file.c -o file.out
# goto-cc emits a goto binary consumed by CBMC tooling.
goto-instrument --print-internal-representation file.out
# or (for json symbol table)
cbmc --show-symbol-table --json-ui file.out
# or (an alternative concise format)
cbmc --show-goto-functions file.out
```
```bash
# Recover C from a goto binary
goto-instrument --dump-c file.out > file.gen.c
```

## Git

The trust-mc project follows the [squash and merge option](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/incorporating-changes-from-a-pull-request/about-pull-request-merges#squash-and-merge-your-pull-request-commits) for pull request merges.
As a result:
 1. The title of your pull request will become the main commit message.
 2. The messages from commits in your pull request will appear by default as a bulleted list in the main commit message body.

But the main commit message body is editable at merge time, so you don't have to worry about "typo fix" messages because these can be removed before merging.

```bash
# Set up your git fork
git remote add fork git@github.com:${USER}/trust-mc.git
```

```bash
# Reset everything. Don't have any uncommitted changes!
git clean -xffd
git submodule foreach --recursive git clean -xffd
git submodule update --init
```

```bash
# Need to update local branch (e.g. for an open pull request?)
git fetch origin
git merge origin/main
# Or rebase, but that requires a force push,
# and because we squash and merge, an extra merge commit in a PR doesn't hurt.
```

```bash
# Checkout a pull request locally without the github cli
git fetch origin pull/$ID/head:pr/$ID
git switch pr/$ID
```

```bash
# Push to someone else's pull request
git origin add $USER $GIR_URL_FOR_THAT_USER
git push $USER $LOCAL_BRANCH:$THEIR_PR_BRANCH_NAME
```

```bash
# Search only git-tracked files
git grep codegen_panic
```

```bash
# Accidentally commit to main?
# "Move" commit to a branch:
git checkout -b my_branch
# Fix main:
git branch --force main origin/main
```
