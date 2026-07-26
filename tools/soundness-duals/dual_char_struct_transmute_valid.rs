// CHAR struct-wrapper transmute dual (false-positive twin of
// dual_char_struct_transmute_invalid).
//
// Transmuting a VALID `char` bit-pattern (`0x41` == 'A') into a `#[repr(C)]`
// single-field struct wrapper `OneField<char>` and using it MUST verify
// SUCCESSFULLY — the struct-wrapper validity read must not spuriously reject a
// valid value.
//
// Oracle: MUST be SUCCESSFUL.
// kani-flags: -Z valid-value-checks
#[repr(C)]
struct OneField<T>(T);

#[kani::proof]
fn struct_transmute_valid_char() {
    let good: u32 = 0x41; // 'A' -> valid char
    let w: OneField<char> = unsafe { std::mem::transmute(OneField(good)) };
    std::hint::black_box(w);
}
