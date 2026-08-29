# GitHub CI

trust-mc can be run in GitHub CI using a workflow.
The workflow below is written for the `ubuntu-22.04` runner; because it builds
trust-mc from source, the same steps work on any platform the tool supports (see
[Installation](./install-guide.md)).

## Using trust-mc in your GitHub workflow

trust-mc does not currently have a pre-built GitHub Action. To use trust-mc in CI, build from source as shown below.

The following workflow will checkout your repository, build trust-mc from source, and run `targo trust-mc` on your code.

```yaml
name: trust-mc CI
on:
  pull_request:
  push:
jobs:
  run-trust-mc:
    runs-on: ubuntu-22.04
    steps:
      - name: 'Checkout your code.'
        uses: actions/checkout@v4

      - name: 'Clone trust-mc and use its toolchain'
        run: |
          git clone https://github.com/alabsystems/trust-mc.git /tmp/trust-mc

      - name: 'Build and install trust-mc from source'
        run: |
          cd /tmp/trust-mc
          cargo run --release -p build-trust-mc -- build-dev --release
          cargo install --path .   # trust-mc, cargo-trust-mc, targo-trust-mc

      - name: 'Run trust-mc on your code.'
        run: cargo trust-mc
```

> **NOTE**: `rust-toolchain.toml` pins `channel = "trust"`, a locally linked
> custom toolchain that rustup cannot fetch, so `setup-rust-toolchain` with
> `toolchain-file:` will not resolve it. A runner has to provide that toolchain
> before the build step above will work.

This builds trust-mc from source and runs verification on your crate.

### Options

Common `targo trust-mc` options include:
- `--output-format=terse` to generate terse output.
- `--tests` to run on proofs inside the `test` module (needed for running Bolero).
- `--workspace` to run on all crates within your repository.
- `--smt-solver=ay` to explicitly select the AY solver (alias: `--ay-solver`).

See `targo trust-mc --help` for a full list of options.

## FAQ
- **trust-mc takes too long for my CI**: Try running trust-mc on a
  [schedule](https://docs.github.com/en/actions/using-workflows/events-that-trigger-workflows#schedule)
  with desired frequency.
- **trust-mc Silently Crashes with no logs**: Few possible reasons:
  - trust-mc ran out of RAM. GitHub offers up to 7GB of RAM, but trust-mc may
    use more. Run locally to confirm.
  - GitHub terminates jobs longer than 6 hours.
  - Otherwise, consider filing an issue [here](https://github.com/alabsystems/trust-mc/issues).
