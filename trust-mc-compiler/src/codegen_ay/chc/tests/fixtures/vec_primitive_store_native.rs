// Native-MIR source only. No proof attributes or CLI registrations.
#[inline(never)]
pub fn native_alias_identity(values: &Vec<u8>) -> &Vec<u8> {
    values
}
#[inline(never)]
pub fn native_opaque_publish(_: &Vec<u8>) {}

pub fn physical_store_then_fresh_getter_safe() {
    let mut values = vec![1u64];
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9);
}
pub fn physical_store_then_fresh_getter_bug() {
    let mut values = vec![1u64];
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 1);
}

pub fn native_copied_shared_old3_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let r2 = r;
    unsafe {
        *pointer = 9;
    }
    assert!(r2[0] == 3);
}

pub fn native_copied_shared_new9_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let r2 = r;
    unsafe {
        *pointer = 9;
    }
    assert!(r2[0] == 9);
}

pub fn native_reborrowed_shared_old3_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let rr = &*r;
    unsafe {
        *pointer = 9;
    }
    assert!(rr[0] == 3);
}

pub fn native_reborrowed_shared_new9_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let rr = &*r;
    unsafe {
        *pointer = 9;
    }
    assert!(rr[0] == 9);
}

pub fn native_aggregate_shared_old3_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let carrier = (r,);
    unsafe {
        *pointer = 9;
    }
    assert!(carrier.0[0] == 3);
}

pub fn native_aggregate_shared_new9_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    let carrier = (r,);
    unsafe {
        *pointer = 9;
    }
    assert!(carrier.0[0] == 9);
}

pub fn native_returned_shared_old3_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = native_alias_identity(&values);
    unsafe {
        *pointer = 9;
    }
    assert!(r[0] == 3);
}

pub fn native_returned_shared_new9_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = native_alias_identity(&values);
    unsafe {
        *pointer = 9;
    }
    assert!(r[0] == 9);
}

// Parameters may alias; this is a boundary control, not a Safe/Bug claim.
pub fn native_parameter_alias_old3_refusal(values: &mut Vec<u8>, reader: &Vec<u8>) {
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer = 9;
    }
    assert!(reader[0] == 3);
}

// Parameters may alias; this is a boundary control, not a Safe/Bug claim.
pub fn native_parameter_alias_new9_refusal(values: &mut Vec<u8>, reader: &Vec<u8>) {
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer = 9;
    }
    assert!(reader[0] == 9);
}

// Parameters may alias; this is a boundary control, not a Safe/Bug claim.
pub fn native_parameter_carrier_old3_refusal(values: &mut Vec<u8>, readers: (&Vec<u8>,)) {
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer = 9;
    }
    assert!(readers.0[0] == 3);
}

// Parameters may alias; this is a boundary control, not a Safe/Bug claim.
pub fn native_parameter_carrier_new9_refusal(values: &mut Vec<u8>, readers: (&Vec<u8>,)) {
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer = 9;
    }
    assert!(readers.0[0] == 9);
}

pub fn native_opaque_escape_before_store_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    native_opaque_publish(&values);
    unsafe {
        *pointer = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[inline(never)]
pub fn native_retarget_opaque(pointer: &mut *mut u8, replacement: *mut u8) {
    *pointer = replacement;
}
#[inline(always)]
pub fn native_retarget_inline(pointer: &mut *mut u8, replacement: *mut u8) {
    *pointer = replacement;
}

pub fn native_retarget_opaque_old4_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_opaque(&mut pointer, b.as_mut_ptr());
    unsafe {
        *pointer = 9;
    }
    assert!(b[0] == 4);
}

pub fn native_retarget_opaque_new9_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_opaque(&mut pointer, b.as_mut_ptr());
    unsafe {
        *pointer = 9;
    }
    assert!(b[0] == 9);
}

pub fn native_retarget_inline_old4_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_inline(&mut pointer, b.as_mut_ptr());
    unsafe {
        *pointer = 9;
    }
    assert!(b[0] == 4);
}

pub fn native_retarget_inline_new9_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_inline(&mut pointer, b.as_mut_ptr());
    unsafe {
        *pointer = 9;
    }
    assert!(b[0] == 9);
}

pub fn native_retarget_copied_old4_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_opaque(&mut pointer, b.as_mut_ptr());
    let copied = pointer;
    unsafe {
        *copied = 9;
    }
    assert!(b[0] == 4);
}

pub fn native_retarget_copied_new9_custody_negative() {
    let mut a = vec![3u8];
    let mut b = vec![4u8];
    let mut pointer = a.as_mut_ptr();
    native_retarget_opaque(&mut pointer, b.as_mut_ptr());
    let copied = pointer;
    unsafe {
        *copied = 9;
    }
    assert!(b[0] == 9);
}
