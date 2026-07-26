# Concrete Playback

When the result of a certain check comes back as a `FAILURE`, trust-mc offers the `concrete-playback` option to help debug. This feature generates a Rust unit test case that plays back a failing proof harness using a concrete counterexample.

When concrete playback is enabled, trust-mc will generate unit tests for assertions that failed during verification,
as well as cover statements that are reachable.

These tests can then be executed using trust-mc's playback subcommand.

## Usage

In order to enable this feature, run trust-mc with the `-Z concrete-playback --concrete-playback=[print|inplace]` flag.

> **Note:** Concrete playback in trust-mc runs on the AY backend (`--backend=auto` by default, or `--backend=ay`).
> Example: `trust-mc test.rs --backend=ay -Z concrete-playback --concrete-playback=print`

After getting a verification failure, trust-mc will generate a Rust unit test case that plays back a failing
proof harness with a concrete counterexample.
The concrete playback modes mean the following:
* `print`: trust-mc will just print the unit test to stdout.
You will then need to copy this unit test into the same module as your proof harness.
This is also helpful if you just want to quickly find out which values were assigned by `kani::any()` calls.
* `inplace`: trust-mc will automatically copy the unit test into your source code.
Before running this mode, you might find it helpful to have your existing code committed to `git`.
That way, you can easily remove the unit test with `git revert`.
Note that trust-mc will not copy the unit test into your source code if it detects
that the exact same test already exists.

After the unit test is in your source code, you can run it with the `playback` subcommand.
To debug it, there are a couple of options:
* You can try the [Kani VSCode extension](https://github.com/model-checking/kani-vscode-extension)
(compatible with trust-mc).
* Otherwise, you can debug the unit test on the command line.

To manually compile and run the test, you can use trust-mc's `playback` subcommand:
```
cargo trust-mc playback -Z concrete-playback -- ${unit_test_func_name}
```

The output from this command is similar to `cargo test`.
The output will have a line in the beginning like
`Running unittests {files} ({binary})`.

You can further debug the binary with tools like `rust-gdb` or `lldb`.

## Example

Running `trust-mc -Z concrete-playback --concrete-playback=print` on the following source file:
```rust
#[kani::proof]
fn proof_harness() {
    let a: u8 = kani::any();
    let b: u16 = kani::any();
    assert!(a / 2 * 2 == a &&
            b / 2 * 2 == b);
}
```
yields a concrete playback Rust unit test similar to the one below:
```rust
#[test]
fn kani_concrete_playback_proof_harness_16220658101615121791() {
    let concrete_vals: Vec<Vec<u8>> = vec![
        // 133
        vec![133],
        // 35207
        vec![135, 137],
    ];
    kani::concrete_playback_run(concrete_vals, proof_harness);
}
```
Here, `133` and `35207` are the concrete values that, when substituted for `a` and `b`,
cause an assertion failure.
`vec![135, 137]` is the byte array representation of `35207`.

`kani::concrete_playback_run` is the generated helper used by these playback
tests. Ordinary verification builds keep that symbol available so generated
tests can remain in source, but the non-playback implementation is only a
compile-compatibility stub and will panic if executed. Run generated playback
tests with `trust-mc playback` or `cargo trust-mc playback`, not from proof harness
execution in verification mode.

## Request for comments

This feature is experimental and is therefore subject to change.
If you have ideas for improving the user experience of this feature,
please [file an issue](https://github.com/alabsystems/trust-mc/issues/new/choose).

## Limitations

* This feature does not generate unit tests for failing non-panic checks (e.g., UB checks).
This is because checks would not trigger runtime errors during concrete playback.
trust-mc generates warning messages for this.
* This feature does not support generating unit tests for multiple assertion failures within the same harness.
This limitation might be removed in the future.
trust-mc generates warning messages for this.
* This feature requires that you use the same trust-mc version to generate the test and to playback.
Any extra compilation option used during verification must be used during playback.
