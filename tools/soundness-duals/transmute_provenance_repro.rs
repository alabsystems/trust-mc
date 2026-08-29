// Audit repro: transmute / pointer-provenance / type-punning false-Safe probe.
//
// Oracle: MIXED — score PER HARNESS, not per file:
//   bool_invalid_transmute_FALSE_SAFE     MUST FAIL (invalid bool byte 2)
//   char_invalid_transmute_CONTROL_caught MUST FAIL (lone surrogate)
//   provenance_roundtrip_CONTROL_failclosed  MAY VERIFY — see below
// kani-flags: -Z valid-value-checks
//
// STATUS 2026-08-24: the FINDING BELOW IS FIXED — this file is now a REGRESSION
// GUARD, not an open defect. Re-measured with `-Z valid-value-checks`:
// `bool_invalid_transmute_FALSE_SAFE` reports
//   Check 1: "Undefined Behavior: Invalid value of type `bool`" -> FAILED
// i.e. the invalid byte 2 IS caught. The narrative below describes the ORIGINAL
// defect and is kept for provenance; do not read it as current behaviour.
//
// The requirement used to be stated in PROSE only ("Run: ... -Z
// valid-value-checks"), so the dual wall ran this file with NO flags, no checks
// were emitted at all, and it scored as a bogus P0 for years. It now declares
// `kani-flags:` above.
//
// FINDING (primary, HARNESS `bool_invalid_transmute_FALSE_SAFE`):
//   trust-mc's BV->Bool transmute lowering is VALUE-NORMALIZING, not
//   bit-preserving: `Cast(Transmute, u8, bool)` is lowered to `(x != 0)`
//     * BMC:  trust-mc-compiler/src/codegen_ay/statement/cast.rs:302-304
//     * CHC:  trust-mc-compiler/src/codegen_ay/chc/stmt/codegen_stmt_copy.rs:88-93
//   Byte value 2 and byte value 1 both map to `true`. The original invalid
//   bitpattern is UNRECOVERABLE afterward. The `-Z valid-value-checks`
//   validity instrumentation (check_values/mod.rs:819-839) inserts
//   `value = Cast(Transmute, x, bool); assert( *(&value as *const u8) in 0..=1 )`
//   but the byte it reads back is the materialized bool (0/1), never 2.
//   => trust-mc-with-flag proves VERIFICATION: SUCCESSFUL.
//   Real Rust: immediate UB. Kani-with-flag: reports the invalid-value FAILURE.

#[kani::proof]
fn bool_invalid_transmute_FALSE_SAFE() {
    // Concrete so there is no ambiguity about reachability.
    let x: u8 = 2; // neither 0 nor 1 -> invalid bool
    let b: bool = unsafe { core::mem::transmute::<u8, bool>(x) };
    // In trust-mc, b == (2 != 0) == true. The validity check reads back byte
    // 1 (materialized `true`), which satisfies 0..=1 -> discharged vacuously.
    core::hint::black_box(b);
}

// CONTROL A (char): SAME construction, but char maps to Sort::bitvec(32)
//   (trust-mc-compiler/src/codegen_ay/statement/sort_inference.rs:65), so the
//   transmute is a BV32 IDENTITY that PRESERVES the invalid value. The very
//   same validity instrumentation reads back 0xD800 and the multi-range char
//   check [0..=0xD7FF] u [0xE000..=0x10FFFF] correctly FAILS.
//   This isolates the defect to the Bool-sort normalization, not the pass.
#[kani::proof]
fn char_invalid_transmute_CONTROL_caught() {
    let x: u32 = 0xD800; // lone surrogate -> invalid char
    let c: char = unsafe { core::mem::transmute::<u32, char>(x) };
    core::hint::black_box(c);
}

// CONTROL B (provenance, DEFAULT mode / memory-safety checks): FAIL-CLOSED.
//   int -> ptr goes through CastKind::PointerWithExposedProvenance, which
//   invalidates obj_valid[obj_id] (#3350,
//   trust-mc-compiler/src/codegen_ay/chc/stmt/codegen_stmt_rvalue_ref/cast_dispatch.rs:54-68)
//   so the deref's obj_valid select is `false` -> CTREX (sound; even over-
//   conservative for legit round-trips). OOB via preserved-obj_id arithmetic
//   is separately caught by the offset<size bounds check in heap_access_checks.
//   Included to show candidate 2 is NOT a false-Safe in the default config.
//
//   STATUS 2026-08-24: this harness now VERIFIES, and that is CORRECT, not a
//   missed bug. The program is SAFE — a legitimate expose-then-reconstruct
//   round-trip where `y == 42` — and the comment above already concedes the
//   old CTREX was "over-conservative for legit round-trips". The fail-closed
//   over-approximation has since been tightened, so the expectation recorded
//   here (FAILED) is STALE. Kept as a precision guard: if it ever flips back to
//   FAILED, the over-approximation returned.
#[kani::proof]
fn provenance_roundtrip_CONTROL_failclosed() {
    let x: u32 = 42;
    let addr: usize = &x as *const u32 as usize;
    let p: *const u32 = addr as *const u32; // PointerWithExposedProvenance
    let y: u32 = unsafe { *p };
    core::hint::black_box(y);
}
