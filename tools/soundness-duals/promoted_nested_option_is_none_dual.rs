// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Original nested promoted Option method controls, retained without guard substitution.

const NATIVE_NONE_BOOL_BYTE: u8 = unsafe { core::mem::transmute(None::<bool>) };

#[kani::proof]
fn nested_compound_none_raw_byte_uses_native_niche_safe() {
    let value = &(123u64, (9u8, None::<bool>));
    assert!(value.1.1.is_none());
    let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
    assert!(byte == NATIVE_NONE_BOOL_BYTE);
}

#[kani::proof]
fn nested_compound_none_raw_byte_is_not_typed_zero_bug() {
    let value = &(123u64, (9u8, None::<bool>));
    assert!(value.1.1.is_none());
    let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
    assert!(byte == 0);
}

#[kani::proof]
fn nested_some_false_predicate_safe() {
    let value = &(123u64, (9u8, Some(false)));
    assert!(!value.1.1.is_none());
    assert!(value.1.1.is_some());
    assert!(matches!(value.1.1, Some(false)));
}

#[kani::proof]
fn nested_some_false_is_not_none_bug() {
    let value = &(123u64, (9u8, Some(false)));
    assert!(value.1.1.is_none());
}

#[kani::proof]
fn nested_option_tuple_payload_safe() {
    let value = &(123u64, (9u8, Some((257u16, false))));
    assert!(value.1.1.is_some());
    assert!(matches!(value.1.1, Some((257, false))));
}

#[kani::proof]
fn nested_option_tuple_wrong_payload_bug() {
    let value = &(123u64, (9u8, Some((257u16, false))));
    assert!(value.1.1.is_some());
    assert!(matches!(value.1.1, Some((258, false))));
}

#[kani::proof]
fn nested_option_reborrow_keeps_address_safe() {
    let value = &(123u64, (9u8, None::<bool>));
    let alias = &*value;
    let option = &alias.1.1;
    let again = &*option;
    let before = core::ptr::addr_of!(value.1.1);
    assert!(again.is_none());
    let after = core::ptr::addr_of!(*again);
    assert!(before == after);
}

mod lookalike {
    #[allow(dead_code)]
    pub enum Option<T> {
        None,
        Some(T),
    }
    impl<T> Option<T> {
        pub fn is_none(&self) -> bool {
            panic!("custom Option predicate must execute");
        }
    }
}

#[kani::proof]
fn nested_custom_option_method_panic_bug() {
    let value = &(123u64, (9u8, lookalike::Option::<bool>::None));
    let _ = value.1.1.is_none();
}

trait OtherPredicate {
    fn is_none(&self) -> bool;
}
impl OtherPredicate for Option<bool> {
    fn is_none(&self) -> bool {
        panic!("custom trait predicate must execute");
    }
}

#[kani::proof]
fn nested_custom_trait_method_panic_bug() {
    let value = &(123u64, (9u8, None::<bool>));
    let _ = OtherPredicate::is_none(&value.1.1);
}
