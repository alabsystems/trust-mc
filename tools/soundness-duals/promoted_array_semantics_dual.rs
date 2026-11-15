// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[derive(Clone, Copy)]
struct Parity(u8);
impl PartialEq for Parity {
    fn eq(&self, rhs: &Self) -> bool {
        self.0 % 2 == rhs.0 % 2
    }
}

#[derive(Clone, Copy)]
struct Divides(u8);
impl PartialEq for Divides {
    fn eq(&self, rhs: &Self) -> bool {
        self.0 % rhs.0 == 0
    }
}

#[kani::proof]
fn literal_equality_uses_element_body() {
    assert!([Parity(1), Parity(2)] == [Parity(3), Parity(4)]);
}

#[kani::proof]
fn literal_equal_values_are_not_unequal() {
    assert!([Parity(1), Parity(2)] != [Parity(3), Parity(4)]);
}

#[kani::proof]
fn literal_different_values_are_not_equal() {
    assert!([Parity(1), Parity(2)] == [Parity(2), Parity(4)]);
}

#[kani::proof]
fn literal_short_circuit_skips_later_panic() {
    assert!([Divides(1), Divides(4)] != [Divides(2), Divides(0)]);
}

#[kani::proof]
fn literal_first_divisor_zero_must_fail() {
    let _ = [Divides(1), Divides(4)] == [Divides(0), Divides(2)];
}

#[kani::proof]
fn literal_reached_later_divisor_zero_must_fail() {
    let _ = [Divides(4), Divides(4)] != [Divides(2), Divides(0)];
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Padded {
    tag: u8,
    value: u32,
}
impl PartialEq for Padded {
    fn eq(&self, rhs: &Self) -> bool {
        self.tag == rhs.tag && self.value % 2 == rhs.value % 2
    }
}

#[kani::proof]
fn literal_padded_fields_use_rust_layout() {
    assert!([Padded { tag: 7, value: 1 }] == [Padded { tag: 7, value: 3 }]);
}

#[kani::proof]
fn literal_padded_wrong_tag_must_fail() {
    assert!([Padded { tag: 7, value: 1 }] == [Padded { tag: 8, value: 3 }]);
}

const OFFSET_VALUES: [Parity; 3] = [Parity(9), Parity(1), Parity(2)];
const OFFSET_TAIL: &[Parity; 2] =
    unsafe { &*(OFFSET_VALUES.as_ptr().add(1) as *const [Parity; 2]) };

#[kani::proof]
fn nested_reference_window_safe_is_not_misreported() {
    assert!(OFFSET_TAIL == &[Parity(3), Parity(4)]);
}

#[kani::proof]
fn nested_reference_wrong_window_is_not_certified() {
    assert!(OFFSET_TAIL == &[Parity(9), Parity(1)]);
}

#[inline(never)]
fn compare_generic<T: PartialEq, const N: usize>(lhs: &[T; N], rhs: &[T; N]) -> bool {
    lhs == rhs
}

#[kani::proof]
fn literal_generic_wrapper_keeps_element_types() {
    assert!(compare_generic(&[Parity(1), Parity(2)], &[Parity(3), Parity(4)]));
}

#[kani::proof]
fn literal_closure_keeps_element_types() {
    let compare = || [Parity(1), Parity(2)] == [Parity(3), Parity(4)];
    assert!(compare());
}

struct NeverCompared;
impl PartialEq for NeverCompared {
    fn eq(&self, _: &Self) -> bool {
        panic!("empty array must not evaluate an element")
    }
}

#[kani::proof]
fn literal_empty_array_does_not_call_element() {
    let lhs: [NeverCompared; 0] = [];
    let rhs: [NeverCompared; 0] = [];
    assert!(lhs == rhs);
}

#[derive(Clone, Copy)]
struct NonComplementary(u8);
impl PartialEq for NonComplementary {
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
    fn ne(&self, _: &Self) -> bool {
        false
    }
}

#[kani::proof]
fn literal_custom_ne_keeps_its_semantics() {
    assert!([NonComplementary(1)] == [NonComplementary(2)]);
}

#[derive(Clone, Copy)]
struct AddressSensitive(u8);
impl PartialEq for AddressSensitive {
    fn eq(&self, rhs: &Self) -> bool {
        self as *const Self as usize == rhs as *const Self as usize
    }
}

#[kani::proof]
fn literal_address_sensitive_eq_is_not_value_equality() {
    let lhs = [AddressSensitive(1)];
    let rhs = [AddressSensitive(1)];
    assert!(lhs != rhs);
}

#[kani::proof]
fn literal_over_bound_remains_unmodeled() {
    assert!([Parity(1); 17] == [Parity(3); 17]);
}

#[kani::proof]
#[kani::unwind(1)]
fn literal_explicit_unwind_is_not_suppressed() {
    assert!([Parity(1), Parity(2)] == [Parity(3), Parity(4)]);
}

#[inline(never)]
fn read_offset_window(value: &[Parity; 2]) -> [Parity; 2] {
    *value
}

#[kani::proof]
fn literal_nonzero_window_uses_its_offset() {
    assert!(read_offset_window(OFFSET_TAIL) == [Parity(3), Parity(4)]);
}

#[kani::proof]
fn literal_nonzero_window_is_not_base() {
    assert!(read_offset_window(OFFSET_TAIL) == [Parity(9), Parity(1)]);
}

#[inline(never)]
fn replace_window(value: &mut &'static [Parity; 2]) {
    *value = &[Parity(8), Parity(9)];
}

#[kani::proof]
fn replaced_reference_reads_the_new_window() {
    let mut pointer = OFFSET_TAIL;
    replace_window(&mut pointer);
    assert!(read_offset_window(pointer) == [Parity(8), Parity(9)]);
}

#[kani::proof]
fn replaced_reference_must_not_keep_the_old_window() {
    let mut pointer = OFFSET_TAIL;
    replace_window(&mut pointer);
    assert!(read_offset_window(pointer) == [Parity(1), Parity(2)]);
}

struct Writes(std::cell::Cell<u8>);
impl PartialEq for Writes {
    fn eq(&self, rhs: &Self) -> bool {
        self.0.set(9);
        self.0.get() == rhs.0.get()
    }
}

#[kani::proof]
fn effectful_element_body_is_not_erased() {
    let lhs = [Writes(std::cell::Cell::new(1))];
    let rhs = [Writes(std::cell::Cell::new(9))];
    let _ = lhs == rhs;
    assert!(lhs[0].0.get() == 9);
}

#[kani::proof]
fn effectful_element_body_must_not_keep_old_value() {
    let lhs = [Writes(std::cell::Cell::new(1))];
    let rhs = [Writes(std::cell::Cell::new(9))];
    let _ = lhs == rhs;
    assert!(lhs[0].0.get() == 1);
}

const LIVE_LONG_TEXT: &str =
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

#[kani::proof]
fn live_long_string_keeps_its_byte_refusal() {
    let index: usize = kani::any();
    kani::assume(index < LIVE_LONG_TEXT.len());
    assert!(LIVE_LONG_TEXT.as_bytes()[index] == b'a');
}

#[kani::proof]
fn live_long_string_must_not_certify_wrong_bytes() {
    let index: usize = kani::any();
    kani::assume(index < LIVE_LONG_TEXT.len());
    assert!(LIVE_LONG_TEXT.as_bytes()[index] == b'b');
}

const PADDED_WINDOWS: [Padded; 2] =
    [Padded { tag: 9, value: 0x11111111 }, Padded { tag: 7, value: 0x44444444 }];
const PADDED_TAIL: &[Padded; 1] =
    unsafe { &*(PADDED_WINDOWS.as_ptr().add(1) as *const [Padded; 1]) };

#[inline(never)]
fn copy_padded_window(value: &[Padded; 1]) -> [Padded; 1] {
    *value
}

#[kani::proof]
fn copied_padded_field_byte_uses_actual_layout() {
    let owned = copy_padded_window(PADDED_TAIL);
    // repr(C) places the initialized u32 field at byte offset 4. Equal bytes
    // make this independent of endianness; padding bytes are never read.
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x44);
}

#[kani::proof]
fn copied_padded_field_byte_is_not_the_tag() {
    let owned = copy_padded_window(PADDED_TAIL);
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 7);
}

#[kani::proof]
fn copied_padded_tag_byte_uses_actual_layout() {
    let owned = copy_padded_window(PADDED_TAIL);
    let tag = unsafe { owned.as_ptr().cast::<u8>().read() };
    assert!(tag == 7);
}

#[kani::proof]
fn copied_padded_tag_byte_is_not_the_value() {
    let owned = copy_padded_window(PADDED_TAIL);
    let tag = unsafe { owned.as_ptr().cast::<u8>().read() };
    assert!(tag == 0x44);
}

#[kani::proof]
fn mutated_padded_byte_must_observe_the_write() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    unsafe {
        owned.as_mut_ptr().cast::<u8>().add(4).write(0x55);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x55);
}

#[kani::proof]
fn mutated_padded_byte_must_not_keep_the_initializer() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    unsafe {
        owned.as_mut_ptr().cast::<u8>().add(4).write(0x55);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x44);
}

#[inline(never)]
unsafe fn replace_through_const(pointer: *const Padded) {
    unsafe {
        (*pointer.cast_mut()).value = 0x55555555;
    }
}

#[kani::proof]
fn const_typed_writer_must_observe_the_write() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    let pointer = core::ptr::addr_of_mut!(owned).cast::<Padded>().cast_const();
    unsafe {
        replace_through_const(pointer);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x55);
}

#[kani::proof]
fn const_typed_writer_must_not_keep_the_initializer() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    let pointer = core::ptr::addr_of_mut!(owned).cast::<Padded>().cast_const();
    unsafe {
        replace_through_const(pointer);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x44);
}

#[kani::proof]
fn intrinsic_copy_must_observe_the_write() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    let replacement = Padded { tag: 7, value: 0x55555555 };
    let target = core::ptr::addr_of!(owned).cast::<Padded>().cast_mut();
    unsafe {
        core::ptr::copy_nonoverlapping(core::ptr::addr_of!(replacement), target, 1);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x55);
}

#[kani::proof]
fn intrinsic_copy_must_not_keep_the_initializer() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    let replacement = Padded { tag: 7, value: 0x55555555 };
    let target = core::ptr::addr_of!(owned).cast::<Padded>().cast_mut();
    unsafe {
        core::ptr::copy_nonoverlapping(core::ptr::addr_of!(replacement), target, 1);
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x44);
}

#[kani::proof]
fn copied_padded_u16_uses_initialized_field_bytes() {
    let owned = copy_padded_window(PADDED_TAIL);
    let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u16>().read() };
    assert!(word == 0x4444);
}

#[kani::proof]
fn copied_padded_u16_is_not_the_tag() {
    let owned = copy_padded_window(PADDED_TAIL);
    let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u16>().read() };
    assert!(word == 7);
}

#[kani::proof]
fn copied_padded_u32_uses_initialized_field_bytes() {
    let owned = copy_padded_window(PADDED_TAIL);
    let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u32>().read() };
    assert!(word == 0x44444444);
}

#[kani::proof]
fn copied_padded_u32_is_not_the_tag() {
    let owned = copy_padded_window(PADDED_TAIL);
    let word = unsafe { owned.as_ptr().cast::<u8>().add(4).cast::<u32>().read() };
    assert!(word == 7);
}

#[kani::proof]
fn copied_padded_last_initialized_byte_is_exact() {
    let owned = copy_padded_window(PADDED_TAIL);
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(7).read() };
    assert!(byte == 0x44);
}

#[kani::proof]
fn copied_padded_padding_byte_is_not_certified() {
    let owned = copy_padded_window(PADDED_TAIL);
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(1).read() };
    assert!(byte == 0);
}

#[kani::proof]
fn copied_padded_one_past_read_must_fail() {
    let owned = copy_padded_window(PADDED_TAIL);
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(8).read() };
    assert!(byte == 0);
}

#[kani::proof]
fn copied_padded_unaligned_u16_is_not_certified() {
    let owned = copy_padded_window(PADDED_TAIL);
    let word = unsafe { owned.as_ptr().cast::<u8>().add(5).cast::<u16>().read() };
    assert!(word == 0x4444);
}

struct DropWriter(*mut u8);
impl Drop for DropWriter {
    fn drop(&mut self) {
        unsafe {
            self.0.write(0x55);
        }
    }
}

#[kani::proof]
fn destructor_write_must_observe_the_write() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    {
        let pointer = core::ptr::addr_of!(owned).cast::<u8>();
        let _guard = DropWriter(unsafe { pointer.add(4).cast_mut() });
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x55);
}

#[kani::proof]
fn destructor_write_must_not_keep_the_initializer() {
    let mut owned = copy_padded_window(PADDED_TAIL);
    {
        let pointer = core::ptr::addr_of!(owned).cast::<u8>();
        let _guard = DropWriter(unsafe { pointer.add(4).cast_mut() });
    }
    let byte = unsafe { owned.as_ptr().cast::<u8>().add(4).read() };
    assert!(byte == 0x44);
}

#[kani::proof]
fn raw_u8_write_then_read_correct() {
    let mut values = [1u8, 2];
    unsafe {
        values.as_mut_ptr().add(1).write(3);
    }
    assert!(unsafe { values.as_ptr().add(1).read() } == 3);
}

#[kani::proof]
fn raw_u8_write_then_read_wrong_old() {
    let mut values = [1u8, 2];
    unsafe {
        values.as_mut_ptr().add(1).write(3);
    }
    assert!(unsafe { values.as_ptr().add(1).read() } == 2);
}

#[kani::proof]
fn raw_u16_write_then_read_correct() {
    let mut values = [0x1111u16, 0x2222];
    unsafe {
        values.as_mut_ptr().add(1).write(0x3333);
    }
    assert!(unsafe { values.as_ptr().add(1).read() } == 0x3333);
}

#[kani::proof]
fn raw_u16_write_then_read_wrong_old() {
    let mut values = [0x1111u16, 0x2222];
    unsafe {
        values.as_mut_ptr().add(1).write(0x3333);
    }
    assert!(unsafe { values.as_ptr().add(1).read() } == 0x2222);
}

// Same pointee type does not establish an element-memory cell when a byte
// offset starts inside an element. These are valid unaligned reads, not UB.
#[kani::proof]
fn unaligned_same_type_read_is_not_misreported() {
    let values = [0x1122u16, 0x3344];
    let word = unsafe { values.as_ptr().cast::<u8>().add(1).cast::<u16>().read_unaligned() };
    let expected = if cfg!(target_endian = "little") { 0x4411 } else { 0x2233 };
    assert!(word == expected);
}

#[kani::proof]
fn unaligned_same_type_read_is_not_certified() {
    let values = [0x1122u16, 0x3344];
    let word = unsafe { values.as_ptr().cast::<u8>().add(1).cast::<u16>().read_unaligned() };
    assert!(word == 0x1122);
}

#[kani::proof]
fn aligned_byte_step_same_type_read_correct() {
    let values = [0x1122u16, 0x3344];
    assert!(unsafe { values.as_ptr().byte_add(2).read() } == 0x3344);
}

#[kani::proof]
fn aligned_byte_step_same_type_read_wrong_first() {
    let values = [0x1122u16, 0x3344];
    assert!(unsafe { values.as_ptr().byte_add(2).read() } == 0x1122);
}
#[kani::proof]
fn large_same_element_read_correct() {
    let mut values = [0x3344u16; 300];
    values[299] = 0x5566;
    assert!(unsafe { values.as_ptr().add(299).read() } == 0x5566);
}
#[kani::proof]
fn large_same_element_read_wrong_first() {
    let mut values = [0x3344u16; 300];
    values[299] = 0x5566;
    assert!(unsafe { values.as_ptr().add(299).read() } == 0x3344);
}
#[kani::proof]
fn large_symbolic_element_read_correct() {
    let x = kani::any::<u16>();
    let values = [x; 300];
    assert!(unsafe { values.as_ptr().add(299).read() } == x);
}
#[kani::proof]
fn large_symbolic_element_read_wrong() {
    let x = kani::any::<u16>();
    let values = [x; 300];
    assert!(unsafe { values.as_ptr().add(299).read() } != x);
}

#[kani::proof]
fn large_mutable_view_does_not_reuse_another_arrays_cells() {
    let mut other = [11u16, 12];
    unsafe {
        other.as_mut_ptr().add(1).write(13);
    }
    let x = kani::any::<u16>();
    let mut values = [x; 300];
    let pointer = values.as_mut_ptr();
    assert!(unsafe { other.as_ptr().add(1).read() } == 13);
    assert!(unsafe { pointer.add(299).read() } == x);
}

#[kani::proof]
fn large_mutable_view_does_not_certify_unseeded_cells() {
    let mut other = [11u16, 12];
    unsafe {
        other.as_mut_ptr().add(1).write(13);
    }
    let x = kani::any::<u16>();
    let mut values = [x; 300];
    let pointer = values.as_mut_ptr();
    assert!(unsafe { other.as_ptr().add(1).read() } == 13);
    assert!(unsafe { pointer.add(299).read() } != x);
}
