# Provenance note for the counted rows of 2026-09-18

## The protocol log says `1 dirty` — here is exactly what that was

At launch (19:05:05) the measurement worktree `/home/ayates/tmc-fix/coord-row/trust-mc` had one modified file:

    tools/kani-domination/burndown-ledger.jsonl

It carried **two bogus rows appended by an earlier false start** of this same protocol (see below). I reverted that
file to its committed state at ~19:07, while the run was in its first minutes. The worktree has been clean since.

**This cannot have affected any verdict.** The ledger is an output artifact, not an input: it is not compiled into
`bin/trust-mc-driver` or `bin/trust-mc-compiler`, and the runner neither reads nor consults it while measuring. No
source file was modified at any point during the run — `git status` on every `*/src` path was empty at launch and
is empty now.

## The false start, recorded so the two reverted rows are never mistaken for data

The first attempt of this protocol reported `exit=0` with 1134 rows per lane **in 14 seconds** and appended two
ledger rows reading `parity=1/1096 (0.1%)` with `error=1095`. Cause: the protocol hardcoded the ay CLI path to the
pre-bump revision `45cc58c69` and then asserted the binary matched that same hardcoded literal — so the guard
passed while pointing at the wrong solver. The driver refuses an off-pin ay CLI, so every unit errored at 50 ms.

Both rows were reverted before any commit; the committed ledger never left 69 rows, on this machine or the remote.

Fixes now in the protocol, both verified by content rather than by exit code:
* the pin is DERIVED from `tools/tuple.toml` and the assertion compares the resolved binary against that value;
* a run whose units are >20% `error` is refused regardless of row count (**count is not content**).

## How this run was verified as real, before it was trusted

Not by its exit code. By the runner's own header naming the solver it actually resolved
(`trust-mc-ay-cli-7bb59d28b`, matching the declared pin), by **zero** units erroring at 50 ms where previously all
1134 did, and by a plausible verdict mix with walls from 552 ms to 33 s.
