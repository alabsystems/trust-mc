# Performance comparisons with `benchcomp`

> **NOTE**: `benchcomp` is not checked into this repository — there is no
> `tools/benchcomp` directory. This page (and the `benchcomp` reference pages)
> describes the tool as inherited from upstream Kani; the commands below will
> not run until it is vendored back in.

While trust-mc includes a performance regression suite under `tests/perf`, you may wish to test trust-mc's performance using your own benchmarks or with particular versions of trust-mc.
You can use the `benchcomp` tool in the trust-mc repository to run several 'variants' of a command on one or more benchmark suites; automatically parse the results of each of those suites; and take actions or emit visualizations based on those results.

## Example use-cases

1. Run one or more benchmark suites with the current and previous versions of trust-mc.
   Exit with a return code of 1 or print a custom summary to the terminal if any benchmark regressed by more than a user-configured amount.
1. Run benchmark suites using several historical versions of trust-mc and emit a graph of performance over time.
1. Run benchmark suites using different SAT solvers, command-line flags, or environment variables.

## Features

Benchcomp provides the following features to support your performance-comparison workflow:

* **Automatically copies benchmark suites into a fresh directories** before running with each variant, to ensure that built artifacts do not affect subsequent runtimes
* **Parses the results of different 'kinds' of benchmark suite** and combines those results into a single unified format.
  This allows you to run benchmarks from external repositories, suites of pre-compiled GOTO-binaries, and other kinds of benchmark all together and view their results in a single dashboard.
* **Driven by a single configuration file** that can be sent to colleagues or checked into a repository to be used in continuous integration.
* **Extensible,** allowing you to write your own parsers and visualizations.
* **Caches all previous runs** and allows you to re-create visualizations for the latest run without actually re-running the suites.

## Quick start

Here's how the suite would be run twice, comparing the last release tag with the current HEAD.

```
cd $TRUST_MC_SRC_DIR
git worktree add new HEAD
git worktree add old $(git describe --tags --abbrev=0)

tools/benchcomp/bin/benchcomp --config tools/benchcomp/configs/perf-regression.yaml
```

This uses a `perf-regression.yaml` configuration file.
After running the suite twice, the configuration file terminates `benchcomp` with a return code of 1 if any of the benchmarks regressed on metrics such as `success` (a boolean), `solver_runtime`, and `number_vccs` (numerical).
Additionally, the config file directs benchcomp to print out a Markdown table.

The rest of this documentation describes how to modify `benchcomp` for your own use cases, including writing a configuration file; writing a custom parser for your benchmark suite; and writing a custom visualization to examine the results of a performance comparison.
