#![crate_name = "core"]
pub mod sync {
    pub mod atomic {
        pub fn as_ptr(_: &std::sync::atomic::AtomicU32) -> *mut u32 {
            std::ptr::null_mut()
        }
    }
}
static CELLS: [std::sync::atomic::AtomicU32; 2] =
    [std::sync::atomic::AtomicU32::new(11), std::sync::atomic::AtomicU32::new(23)];
#[kani::proof]
fn fake_core_safe() {
    assert!(sync::atomic::as_ptr(&CELLS[1]).is_null(), "user core function returns null");
}
#[kani::proof]
fn fake_core_wrong_address() {
    assert!(
        !sync::atomic::as_ptr(&CELLS[1]).is_null(),
        "user core function is not Atomic identity"
    );
}
