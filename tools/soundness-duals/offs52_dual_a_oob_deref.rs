// KEYSTONE #52 DUAL (a) — offset OOB on a stack array via one-past-end DEREF.
// MUST FAIL: `p.add(4)` on [i32;4] is the legal one-past-end pointer (the
// offset alloc-bound check `result_offset <= 16` PASSES), but dereferencing
// it is UB — the DEREF-site strict bound (`offset + 4 <= 16`) must catch it.
// If the widened stack-provenance lane suppresses the demotion AND the
// deref-site check chain fails to engage, this proves SUCCESSFUL = false-Safe
// factory => the widening must be reverted/narrowed.

#[kani::proof]
fn dual_a_offset_oob_stack_deref() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let p: *const i32 = arr.as_ptr();
    unsafe {
        let x = *p.add(4); // one-past-end deref: UB — MUST FAIL
        core::hint::black_box(x);
    }
}
