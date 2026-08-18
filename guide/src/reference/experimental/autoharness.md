# Automatic Harness Generation

Recall the harness for `estimate_size` that we wrote in [First Steps](../../tutorial-first-steps.md):
```rust
{{#include ../../tutorial/first-steps-v1/src/lib.rs:kani}}
```

This harness first declares a local variable `x` using `kani::any()`, then calls `estimate_size` with argument `x`.
Many proof harnesses follow this predictable format—to verify a function `foo`, we create arbitrary values for each of `foo`'s arguments, then call `foo` on those arguments.

The `autoharness` subcommand leverages this observation to automatically generate harnesses and run trust-mc against them.
trust-mc scans the crate for functions whose arguments all implement the `kani::Arbitrary` trait, generates harnesses for them, then runs them.
These harnesses are internal to trust-mc—i.e., trust-mc does not make any changes to your source code.

## Usage
Run either:
```
# targo trust-mc autoharness -Z autoharness
```
or
```
# trust-mc autoharness -Z autoharness <FILE>
```

If trust-mc detects that all of a function `foo`'s arguments implement `kani::Arbitrary`, it will generate and run a `#[kani::proof]` harness, which prints:

```
Autoharness: Checking function foo against all possible inputs...
<VERIFICATION RESULTS>
```

However, if trust-mc detects that `foo` has a [function contract](./contracts.md), it will instead generate a `#[kani::proof_for_contract]` harness and verify the contract:
```
Autoharness: Checking function foo's contract against all possible inputs...
<VERIFICATION RESULTS>
```

Similarly, trust-mc will detect the presence of [loop contracts](./loop-contracts.md) and verify them.

Thus, `-Z autoharness` implies `-Z function-contracts` and `-Z loop-contracts`, i.e., opting into the experimental
autoharness feature means that you are also opting into the function contracts and loop contracts features.

trust-mc generates and runs these harnesses internally—the user only sees the verification results.

### Options
The `autoharness` subcommand has options `--include-pattern [REGEX]` and `--exclude-pattern [REGEX]` to include and exclude particular functions using regular expressions.
When matching, trust-mc prefixes the function's path with the crate name. For example, a function `foo` in the `my_crate` crate will be matched as `my_crate::foo`.

The selection algorithm is as follows:
- If only `--include-pattern`s are provided, include a function if it matches any of the provided patterns.
- If only `--exclude-pattern`s are provided, include a function if it does not match any of the provided patterns.
- If both are provided, include a function if it matches an include pattern *and* does not match any of the exclude patterns. Note that this implies that the exclude pattern takes precedence, i.e., if a function matches both an include pattern and an exclude pattern, it will be excluded.

Here are some examples:

```bash
# Include functions containing foo but not bar
trust-mc autoharness -Z autoharness --include-pattern 'foo' --exclude-pattern 'bar'

# Include my_crate::foo exactly
trust-mc autoharness -Z autoharness --include-pattern '^my_crate::foo$'

# Include functions in the foo module, but not in foo::bar
trust-mc autoharness -Z autoharness --include-pattern 'foo::.*' --exclude-pattern 'foo::bar::.*'

# Include functions starting with test_, but not if they're in a private module
trust-mc autoharness -Z autoharness --include-pattern 'test_.*' --exclude-pattern '.*::private::.*'

# This ends up including nothing since all foo::bar matches will also contain bar.
# trust-mc will emit a warning that these options conflict.
trust-mc autoharness -Z autoharness --include-pattern 'foo::bar' --exclude-pattern 'bar'
```

Note that because trust-mc prefixes function paths with the crate name, some patterns might match more than you expect.
For example, given a function `foo_top_level` inside crate `my_crate`, the regex `.*::foo_.*` will match `foo_top_level`, since trust-mc interprets it as `my_crate::foo_top_level`.
To match only `foo_` functions inside modules, use a more specific pattern, e.g. `.*::[^:]+::foo_.*`.

Autoharness also accepts a `--list` argument, which runs the [list subcommand](../list.md) including automatic harnesses.

For a full list of options, run `trust-mc autoharness --help`.

## Example
Using the `estimate_size` example from [First Steps](../../tutorial-first-steps.md) again:
```rust
{{#include ../../tutorial/first-steps-v1/src/lib.rs:code}}
```

We get:

```
# targo trust-mc autoharness -Z autoharness
Autoharness: Checking function estimate_size against all possible inputs...
RESULTS:
Check 3: estimate_size.assertion.1
         - Status: FAILURE
         - Description: "Oh no, a failing corner case!"
[...]

Verification failed for - estimate_size
Complete - 0 successfully verified functions, 1 failures, 1 total.
```

## Request for comments
This feature is experimental and is therefore subject to change.
If you have ideas for improving the user experience of this feature,
please [file an issue](https://github.com/alabsystems/trust-mc/issues/new/choose).

## Limitations
### Arguments Implementing Arbitrary
trust-mc will only generate an automatic harness for a function if it can represent each of its arguments nondeterministically, without bounds.
In technical terms, each of the arguments needs to implement the `Arbitrary`
trait or be capable of deriving it, or be a reference (mutable or immutable)
where any of the prior requirements is fulfilled by the referenced type.
trust-mc will detect if a struct or enum could implement `Arbitrary` and derive it automatically.
Note that this automatic derivation feature is only available for autoharness.

### Generic Functions
The current implementation does not generate harnesses for generic functions.
For example, given:
```rust
fn foo<T: Eq>(x: T, y: T) {
    if x == y {
        panic!("x and y are equal");
    }
}
```
trust-mc would report that no functions were eligible for automatic harness generation.

If, however, some caller of `foo` is eligible for an automatic harness, then a monomorphized version of `foo` may still be reachable during verification.
For instance, if we add `main`:
```rust
fn main() {
    let x: u8 = 2;
    let y: u8 = 2;
    foo(x, y);
}
```
and run the autoharness subcommand, we get:
```
Autoharness: Checking function main against all possible inputs...

Failed Checks: x and y are equal
 File: "src/lib.rs", line 3, in foo::<u8>

VERIFICATION:- FAILED
```
