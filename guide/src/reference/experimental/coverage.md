# Coverage

Recall our `estimate_size` example from [First steps](../../tutorial-first-steps.md),
where we wrote a proof harness constraining the range of inputs to integers less than 4096:

```rust
{{#include ../../tutorial/first-steps-v2/src/lib.rs:kani}}
```

We must wonder if we've really fully tested our function.
What if we revise the function, but forget to update the assumption in our proof harness to cover the new range of inputs?

Fortunately, trust-mc is able to report a coverage metric for each proof harness.
In the `first-steps-v2` directory, try running:

```
targo trust-mc --coverage -Z source-coverage --harness verify_success
```

which verifies the harness, then prints coverage information for each line.
In this case, we see that each line of `estimate_size` has a nonzero coverage count, indicating that our proof harness provides full coverage.
The raw coverage checks use `COVERED` and `UNCOVERED` statuses; the human-readable report renders those checks as per-line counts and highlights any uncovered source spans.

Try changing the assumption in the proof harness to `x < 2048`.
Now the harness won't be testing all possible cases.
Rerun the command.
You'll see line 24 reported with a zero coverage count, with the uncovered source span highlighted:

```
  24|    0| ```        return 9;'''
```

which indicates that the proof no longer covers line 24, which addresses the case where `x >= 2048`.

Coverage remains experimental and is not included in the current 100% replacement-proof claim.
In particular, the checked out-of-bounds coverage fixture documents a known limitation where a failing bounds check can still cause the surrounding function body to be reported as `COVERED` instead of marking the failing access as `UNCOVERED`.
