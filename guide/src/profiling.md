# Profiling trust-mc's Performance

To profile trust-mc's performance at a fine-grained level, we use a tool called [`samply`](https://github.com/mstange/samply) that allows the compiler & driver to periodically record the current stack trace, allowing us to construct flamegraphs of where they are spending most of their time.

## Install samply
First, install `samply` using [the instructions](https://github.com/mstange/samply?tab=readme-ov-file#installation) from their repo. The easier methods include installing a prebuilt binary or installing from crates.io.


## Running trust-mc for profiling output
1. First, build trust-mc from source with `cargo build-dev --profile profiling` to ensure you are getting all release mode optimizations without stripping useful debug info.
2. Then, you can profile the trust-mc compiler on a crate of your choice by [exporting trust-mc to your local PATH](build-from-source.md#adding-trust-mc-to-your-path) and  running `FLAMEGRAPH=[OPTION] targo trust-mc` within the crate.

The `FLAMEGRAPH` environment variable is read in exactly one place (`FLAMEGRAPH_ENV_VAR` in [`session/cargo.rs`](../../trust-mc-driver/src/session/cargo.rs)), and the only value acted on is `compiler`, which profiles each time the compiler is called. Nothing instruments the driver itself today, so `FLAMEGRAPH=driver` does nothing.

We have to instrument the driver and compiler separately because samply's instrumentation usually cannot handle detecting the subprocess the driver uses to call the compiler.

Our default sampling rate is *8000 Hz*, set by `FLAMEGRAPH_SAMPLING_RATE` in [`session/cargo.rs`](../../trust-mc-driver/src/session/cargo.rs); change it there.

> Note: Specifically when profiling the compiler, ensure you are running `cargo clean` immediately before `targo trust-mc`, or parts of the workspace may not be recompiled by the trust-mc compiler.


## Displaying profiling output
This will create a new `flamegraphs` directory in the crate, containing one `compiler-{crate_name}-{timestamp}.json.gz` file for each crate in the workspace. Run `samply load flamegraphs/XXX.json.gz` on any of these to open a local server that will display the file's flamegraph.

Once the server has opened, you'll see a display with the list of threads in rows at the top, and a flamegraph for the currently selected thread at the bottom. There is typically only one process when profiling the driver. When profiling the compiler, the process that runs the compiler and handles all codegen is usually at the very bottom of the thread window.

In the flamegraph view, I've found it very useful to right click on a function of interest and select "focus on subtree only" so that it zooms in and you can more clearly see the callees it uses. This can then be undone with the breadcrumb trail at the top of the flamegraph.
