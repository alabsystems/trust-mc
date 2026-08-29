// KNOWN BROKEN — trust-mc proves these CLEAN. Kani fails them.
//
// Oracle per harness (see below): every one is TOLERATED today and MUST FAIL
// once stack-frame escape analysis lands. Flip the annotations then — they are
// the gate that keeps this fixed.
//
//   escape_reborrow_read   - MUST FAIL: reborrow into dead callee storage.
//   escape_reborrow_via_fn - MUST FAIL: same, across a call boundary.
//   escape_println_unsafe  - TOLERATED
//   escape_value_load      - MUST FAIL: caught today; this is the REGRESSION guard.
//
// `escape_println_unsafe` is STILL KNOWN BROKEN (the deref is consumed by
// format-args, which reaches the pointee through a lane this check does not
// see). Change its annotation to `MUST FAIL` the moment that path is covered — that turns this file into the gate that keeps them fixed. Do not
// write the words MUST FAIL on those lines before then: `harness_oracle` tests
// for MUST FAIL BEFORE it tests for TOLERATED, so a line carrying both scores
// the harness as an unfixed bug and the wall reports a P0 (learned the hard
// way — this exact file did it).
//
// WHY THIS FILE EXISTS
//
// `dies()` returns a pointer to its own local. Every harness below dereferences
// it after the frame is gone — textbook use-after-scope. Kani reports
// "dereference failure: pointer invalid" / "dead object" for all of them.
// trust-mc proves three of them with [AY:PROOF_QUALIFIERS:clean].
//
// This is the root cause of FIVE missed-bug harnesses found by
// tools/soundness-duals/harness_inversion_scan.py, TWO of which sit inside rows
// the burndown scores as `parity`:
//     expected/dangling-ptr-println/main.rs   (parity)  unsafe_block, general_unsafe
//     expected/ptr_to_ref_cast/slice/test.rs  (parity)  check_with_byte_add_fail
//     expected/ptr_to_ref_cast/invalid/test.rs          check_size_of_val
//     expected/uninit/intrinsics/intrinsics.rs          check_typed_swap_nonoverlapping_safe
//
// WHY IT IS NOT PATCHABLE (three attempts, all reverted — see
// memory/dangling-stack-reborrow-missed-bug.md)
//
// The VC contains NO memory cells: `dies()` is inlined, its local becomes an
// ordinary state var, and the "dangling" pointer is just a live variable still
// holding its value. THERE IS NOTHING TO INVALIDATE. Deref resolution is also a
// CASCADE (ref_targets -> referent_local -> collection lane -> memory), so
// gating one lane hands the pointer to the next — and diverts the CAUGHT cases
// off the lane whose obligation catches them (that attempt turned
// `escape_value_load` from FAILED into a clean proof).
//
// The fix is escape analysis: a pointer derived from a callee local must stop
// resolving to that local's state var once the frame returns.

fn dies() -> *mut i32 {
    let mut x: i32 = 2;
    &mut x as *mut i32
}

/// CAUGHT today. Keep it that way: a "fix" that makes this pass is a regression,
/// which is exactly what the refuse-to-resolve attempt did.
#[kani::proof]
fn escape_value_load() {
    let p = dies();
    let v = unsafe { *p };
    assert!(v == 2);
}

/// MISSED: reborrow to a reference, then read through it.
#[kani::proof]
fn escape_reborrow_read() {
    let p = dies();
    let r: &i32 = unsafe { &*p };
    assert!(*r == 2);
}

/// MISSED: the reborrow crosses a call boundary.
#[kani::proof]
fn escape_reborrow_via_fn() {
    fn read(r: &i32) -> i32 {
        *r
    }
    let p = dies();
    let v = read(unsafe { &*p });
    assert!(v == 2);
}

/// MISSED: the deref is consumed by format-args, which takes `&*p`.
#[kani::proof]
fn escape_println_unsafe() {
    let p = dies();
    unsafe {
        println!("{}", *p);
    }
}
