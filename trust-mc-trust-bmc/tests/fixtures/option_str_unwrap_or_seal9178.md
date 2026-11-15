# Source-generated fat-pointer merge slot

`option_str_unwrap_or_seal9178.module.json` preserves the exact
`core::option::Option::<&str>::unwrap_or` function and all type tables from the
Trust 9178 native diagnostic dump of the adjacent `.rs` source. Other functions
and their proof obligations/certificates/diagnostics were removed. The frozen
module is 5.8 KB; it is a structural regression input, not proof evidence. Its
`Assume` still requires live source-generation authority at the native gate.

Actual command, from the trust-mc repository root (source/output were in ignored
target paths during capture):

```sh
'$HOME/Library/Application Support/aterm/pkg/store/trust/9178/bin/trustc' \
  --crate-type lib --emit metadata \
  --out-dir target/trust-verification-20260917/extract-match-dump \
  -Ztrust-dump=native-bundle:target/trust-verification-20260917/extract-match-dump \
  target/trust-verification-20260917/extract_match.rs
```

Compiler: `d75f13f978b5d5deecaa274d51dfee1dfe495036`. Bounded diagnostic run:
exit 1, 0.885 seconds, 205 MiB peak RSS; 120-second/4096-MiB limits not exceeded.
No Targo certification is claimed. The command record and log are
`target/trust-verification-20260917/extract-match-dump-compiler.{json,log}`.

Source bundle: `trust-native-bundle-4cbc1dc3a0b315c8-52ba7181e1fb180e.json`,
SHA-256 `3618366f3f7676ce2de4c1bbc26e74e7547153603d0fb51d1c9c3d277fc0d9e0`.
Frozen module SHA-256:
`ea7aac79f061a8ff89a79dd92a7c2a69a2767a20aa09af64a95fe512e7c4aa61`.

The real slot is `%4`, allocated in block 0, stored on both switch arms (blocks
2 and 3), and loaded after the join in block 4. Tests require allocation
admission for this initialized direct-access shape and rejection after removing
either arm's store. They do not turn the opaque fat-pointer value into a precise
value or authenticate the saved module's semantic claims.
