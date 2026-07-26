// Dual for P4 fix 3 (volatile_load/store precise Vec cascade).
// Must FAIL: volatile_store writes 7, so the loaded value cannot be 2.
// A store encoding that drops the write (leaving the old data array value)
// would falsely prove this.
#![feature(core_intrinsics)]

#[kani::proof]
fn dual_volatile_store_wrong_value() {
    let mut vec = vec![1u32, 2];
    unsafe {
        let vec_ptr = vec.as_mut_ptr();
        std::intrinsics::volatile_store(vec_ptr.add(1), 7);
        let val = std::intrinsics::volatile_load(vec_ptr.add(1));
        // Real value: 7. This assert is WRONG and must FAIL.
        assert_eq!(val, 2);
    }
}
