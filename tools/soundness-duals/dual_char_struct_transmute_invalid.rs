// CHAR struct-wrapper transmute dual (missed-bug tripwire).
//
// Transmuting an INVALID `char` bit-pattern (`0xD800`, a UTF-16 surrogate that
// is not a valid Unicode scalar value) into a `#[repr(C)]` single-field struct
// wrapper `OneField<char>` and using it MUST be detected as an invalid value.
// If the struct-wrapper validity read ever swallows this into a SUCCESS, the
// value-validity model is unsound.
//
// Oracle: MUST be FAILED — "Invalid value of type `OneField<char>`".
// kani-flags: -Z valid-value-checks
#[repr(C)]
struct OneField<T>(T);

#[kani::proof]
fn struct_transmute_invalid_char() {
    let bad: u32 = 0xD800; // UTF-16 surrogate -> invalid char
    let w: OneField<char> = unsafe { std::mem::transmute(OneField(bad)) };
    std::hint::black_box(w);
}
