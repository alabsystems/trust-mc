// Exact whole [u32; N] -> [char; N] views preserve bits, not Unicode validity.
// Valid-value checks must reject invalid scalars before an assertion can hide them.
// Views outside the zero-offset, unmodified-owner lane remain conservative.
#![allow(unused_assignments)]

#[kani::proof]
fn unicode_boundaries_are_preserved() {
    let words = [0u32, 0xD7FF, 0xE000, 0x10FFFF];
    let chars = unsafe { *(&words as *const [u32; 4] as *const [char; 4]) };
    assert!(chars[0] as u32 == 0);
    assert!(chars[1] as u32 == 0xD7FF);
    assert!(chars[2] as u32 == 0xE000);
    assert!(chars[3] as u32 == 0x10FFFF);
}

#[kani::proof]
fn valid_view_does_not_prove_wrong_value() {
    let words = [65u32, 66];
    let chars = unsafe { *(&words as *const [u32; 2] as *const [char; 2]) };
    assert!(chars[1] == 'C');
}

#[kani::proof]
fn symbolic_high_scalars_are_preserved() {
    let word = kani::any::<u32>();
    kani::assume(word >= 0xE000 && word <= 0x10FFFF);
    let words = [65u32, word];
    let chars = unsafe { *(&words as *const [u32; 2] as *const [char; 2]) };
    assert!(chars[0] == 'A');
    assert!(chars[1] as u32 == word);
}

#[kani::proof]
fn first_surrogate_is_invalid() {
    let words = [0xD800u32, 65];
    let _chars = unsafe { *(&words as *const [u32; 2] as *const [char; 2]) };
}

#[kani::proof]
fn last_surrogate_is_invalid() {
    let words = [65u32, 0xDFFF];
    let _chars = unsafe { *(&words as *const [u32; 2] as *const [char; 2]) };
}

#[kani::proof]
fn above_unicode_max_is_invalid() {
    let words = [65u32, 0x110000];
    let _chars = unsafe { *(&words as *const [u32; 2] as *const [char; 2]) };
}

#[kani::proof]
fn alias_write_safe_is_not_misreported() {
    let mut words = [65u32, 66];
    let pointer = core::ptr::addr_of!(words);
    unsafe { core::ptr::addr_of_mut!(words).cast::<u32>().add(1).write(67) };
    let chars = unsafe { *(pointer as *const [char; 2]) };
    assert!(chars[1] == 'C');
}

#[kani::proof]
fn alias_write_must_not_reuse_old_value() {
    let mut words = [65u32, 66];
    let pointer = core::ptr::addr_of!(words);
    unsafe { core::ptr::addr_of_mut!(words).cast::<u32>().add(1).write(67) };
    let chars = unsafe { *(pointer as *const [char; 2]) };
    assert!(chars[1] == 'B');
}

#[kani::proof]
fn nonzero_window_safe_is_not_misreported() {
    let words = [64u32, 65, 66];
    let pointer = core::ptr::addr_of!(words).cast::<u32>();
    let chars = unsafe { *(pointer.add(1) as *const [char; 2]) };
    assert!(chars[0] == 'A' && chars[1] == 'B');
}

#[kani::proof]
fn nonzero_window_must_not_use_array_base() {
    let words = [64u32, 65, 66];
    let pointer = core::ptr::addr_of!(words).cast::<u32>();
    let chars = unsafe { *(pointer.add(1) as *const [char; 2]) };
    assert!(chars[0] as u32 == 64);
}

#[kani::proof]
fn shorter_view_safe_is_not_misreported() {
    let words = [65u32, 66, 67];
    let chars = unsafe { *(&words as *const [u32; 3] as *const [char; 2]) };
    assert!(chars[0] == 'A' && chars[1] == 'B');
}

#[kani::proof]
fn shorter_view_must_not_prove_wrong_value() {
    let words = [65u32, 66, 67];
    let chars = unsafe { *(&words as *const [u32; 3] as *const [char; 2]) };
    assert!(chars[1] == 'C');
}

#[kani::proof]
fn reassigned_owner_safe_is_not_misreported() {
    let mut words = [65u32, 66];
    let pointer = core::ptr::addr_of!(words);
    words = [67, 68];
    let chars = unsafe { *(pointer as *const [char; 2]) };
    assert!(chars[0] == 'C' && chars[1] == 'D');
}

#[kani::proof]
fn reassigned_owner_must_not_reuse_initializer() {
    let mut words = [65u32, 66];
    let pointer = core::ptr::addr_of!(words);
    words = [67, 68];
    let chars = unsafe { *(pointer as *const [char; 2]) };
    assert!(chars[0] == 'A');
}
