// Secondary adversarial dual (byte-order gate): this program is BUGGY.
// Real semantics: id_from_coerce(outer) & 0xFF == inner_id, NOT outer_id,
// so the assert is violated whenever outer_id != inner_id.
// Oracle: VERIFICATION must be FAILED (genuine bug), both before and after
// the unsize_dyn alias fix. A field0-at-LSB (wrong-endian) scatter would
// falsely prove it.
use std::ops::Deref;

pub trait Identity {
    fn id(&self) -> u16;
}

pub struct Outer<T: ?Sized> {
    pub outer_id: u8,
    pub inner: T,
}

pub struct Inner {
    pub id: u8,
}

impl<T> Identity for Outer<T>
where
    T: ?Sized + Identity,
{
    fn id(&self) -> u16 {
        ((self.outer_id as u16) << 8) + (self.inner.id() as u16)
    }
}

impl Identity for Inner {
    fn id(&self) -> u16 {
        self.id.into()
    }
}

pub fn id_from_coerce<T>(identity: T) -> u16
where
    T: Deref<Target = dyn Identity>,
{
    identity.id()
}

#[kani::proof]
fn check_low_byte_buggy() {
    let inner_id = kani::any();
    let outer_id = kani::any();
    let outer: Box<dyn Identity> = Box::new(Outer { inner: Inner { id: inner_id }, outer_id });
    // BUG: the real low byte is inner_id, not outer_id.
    assert_eq!(id_from_coerce(outer) & 0xFF, outer_id.into());
}
