// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and the `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: the havoc-read gate (trust-mc-driver
// direct_smt_cex/havoc_reads.rs, havoc_taint.rs) keeps a CHC counterexample
// `Genuine` only when the violated check does not DEPEND on a value no clause
// defines. Each harness here first reads such a value: the payload of a
// reference joined from two `Some(&x)` constants, which the encoder reads from
// a typed memory cell no clause writes (review_r17_aggregate_field_join.rs).
// The first version of the gate (fix/chc-false-certificates, 2026-09-26)
// refused every counterexample with such a read anywhere in the violated
// check's backward cone, and looked up an unattributed `chc.0` failure as
// property 0's `error_p0`; its review (2026-09-27, probes g7/g1/g2/g6) found:
// - bug_independent_after_freed_read, a real `x != 7` bug after an unrelated
//   freed read on the only path (through a tautological `v as u16 <= 255`
//   guard), lost its Genuine label: its cut-system replay refused a slot that
//   carried the freed value in one clause and a computed one in another;
// - bug_unattributed_after_freed_read, a real `unreachable_unchecked` whose
//   counterexample names no check, was refused over `error_p0: not
//   declared`, and a clean-coned but unviolated `error_p0` could have been
//   certified `Clean` for a counterexample nothing showed violated it.
// The labels are not gated (the expectations are verdicts); the file pins that
// the gate's data-dependence rules never turn these verdicts, and that the
// should_panic twin of a counterexample resting on the freed read is refused
// (V6) rather than accepted as the expected panic.
//
// The joined `Some(&x)` payload is exact since the value-semantic payload fix
// (chc_value_ref_payload_dual.rs), so the first four rows no longer read a
// freed value at all. The `_byte_view` rows keep the gate exercised end to end
// with a read the encoder still frees: a byte of a `u32` read through a
// pointer cast to `*const u8` and advanced by `add(1)`, which loads the `u8`
// typed memory at an address no clause writes (review probe
// g4_heap_typed.rs `stack_u8_view_*`). When that read becomes exact these rows
// need another freed read.

#[kani::proof]
fn bug_independent_after_freed_read() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    let mut v = 0u8;
    if let Some(r) = o {
        v = *r;
    }
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    assert!(x != 7);
}

#[kani::proof]
fn safe_independent_after_freed_read() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    let mut v = 0u8;
    if let Some(r) = o {
        v = *r;
    }
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    kani::assume(x != 7);
    assert!(x != 7);
}

#[kani::proof]
fn bug_unattributed_after_freed_read() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    let mut v = 0u8;
    if let Some(r) = o {
        v = *r;
    }
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    if x == 7 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

#[kani::proof]
#[kani::should_panic]
fn sp_payload_join() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o: Option<&u8> = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!((*r == 1) == b);
    }
}

#[kani::proof]
fn bug_independent_after_byte_view() {
    let w: u32 = 0x0403_0201;
    let q = &w as *const u32 as *const u8;
    let v = unsafe { *q.add(1) };
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    assert!(x != 7);
}

#[kani::proof]
fn safe_independent_after_byte_view() {
    let w: u32 = 0x0403_0201;
    let q = &w as *const u32 as *const u8;
    let v = unsafe { *q.add(1) };
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    kani::assume(x != 7);
    assert!(x != 7);
}

#[kani::proof]
fn bug_unattributed_after_byte_view() {
    let w: u32 = 0x0403_0201;
    let q = &w as *const u32 as *const u8;
    let v = unsafe { *q.add(1) };
    assert!(v as u16 <= 255);
    let x: u32 = kani::any();
    if x == 7 {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

#[kani::proof]
#[kani::should_panic]
fn sp_byte_view() {
    let w: u32 = 0x0403_0201;
    let q = &w as *const u32 as *const u8;
    let v = unsafe { *q.add(1) };
    assert!(v == 2);
}
