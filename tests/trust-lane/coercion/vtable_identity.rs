// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trait-object metadata through `Box`, `Rc`, `Arc`, `NonNull` (pattern-typed on Trust) and `&`,
//! as route duals. `id` is a per-impl constant, so it is decided by WHICH vtable the coercion
//! stored. A virtual call BMC cannot resolve used to leave its result free without counting it:
//! `nonnull_id_holds` was refuted by a counterexample certified Genuine, and a callee that
//! panics (`nonnull_panicking_callee_refuted`) went unseen.

use std::any::Any;
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;

trait Shape {
    fn area(&self) -> u32;
    fn id(&self) -> u8;
}

struct Square(u32);
struct Tri(u32);
struct Wide(u64, u8);

impl Shape for Square {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
    fn id(&self) -> u8 {
        1
    }
}

impl Shape for Tri {
    fn area(&self) -> u32 {
        self.0
    }
    fn id(&self) -> u8 {
        2
    }
}

impl Shape for Wide {
    fn area(&self) -> u32 {
        self.1 as u32
    }
    fn id(&self) -> u8 {
        3
    }
}

#[kani::proof]
fn box_id_holds() {
    let b: Box<dyn Shape> = Box::new(Tri(3));
    assert!(b.id() == 2, "box vtable");
}

#[kani::proof]
fn box_id_refuted() {
    let b: Box<dyn Shape> = Box::new(Tri(3));
    assert!(b.id() == 1, "box vtable");
}

#[kani::proof]
fn rc_id_holds() {
    let r: Rc<dyn Shape> = Rc::new(Tri(3));
    assert!(r.id() == 2, "rc vtable");
}

#[kani::proof]
fn rc_id_refuted() {
    let r: Rc<dyn Shape> = Rc::new(Tri(3));
    assert!(r.id() == 1, "rc vtable");
}

#[kani::proof]
fn arc_id_holds() {
    let a: Arc<dyn Shape> = Arc::new(Tri(3));
    assert!(a.id() == 2, "arc vtable");
}

#[kani::proof]
fn arc_id_refuted() {
    let a: Arc<dyn Shape> = Arc::new(Tri(3));
    assert!(a.id() == 1, "arc vtable");
}

#[kani::proof]
fn nonnull_id_holds() {
    let mut t = Tri(3);
    let p: NonNull<dyn Shape> = NonNull::from(&mut t);
    assert!(unsafe { p.as_ref() }.id() == 2, "nonnull vtable");
}

#[kani::proof]
fn nonnull_id_refuted() {
    let mut t = Tri(3);
    let p: NonNull<dyn Shape> = NonNull::from(&mut t);
    assert!(unsafe { p.as_ref() }.id() == 1, "nonnull vtable");
}

#[kani::proof]
fn box_choice_holds() {
    let c: bool = kani::any();
    let b: Box<dyn Shape> = if c { Box::new(Square(2)) } else { Box::new(Tri(2)) };
    assert!(b.id() == if c { 1 } else { 2 }, "box vtable follows the value");
}

#[kani::proof]
fn box_choice_refuted() {
    let c: bool = kani::any();
    let b: Box<dyn Shape> = if c { Box::new(Square(2)) } else { Box::new(Tri(2)) };
    assert!(b.id() == 1, "box vtable follows the value");
}

#[kani::proof]
fn rc_choice_refuted() {
    let c: bool = kani::any();
    let r: Rc<dyn Shape> = if c { Rc::new(Square(2)) } else { Rc::new(Tri(2)) };
    assert!(r.id() == 2, "rc vtable follows the value");
}

#[kani::proof]
fn box_size_of_val_holds() {
    let b: Box<dyn Shape> = Box::new(Square(2));
    assert!(std::mem::size_of_val(&*b) == 4, "vtable size");
}

#[kani::proof]
fn box_size_of_val_refuted() {
    let b: Box<dyn Shape> = Box::new(Square(2));
    assert!(std::mem::size_of_val(&*b) == 8, "vtable size");
}

#[kani::proof]
fn rc_align_of_val_holds() {
    let r: Rc<dyn Shape> = Rc::new(Wide(1, 2));
    assert!(std::mem::align_of_val(&*r) == 8, "vtable align");
}

#[kani::proof]
fn rc_align_of_val_refuted() {
    let r: Rc<dyn Shape> = Rc::new(Wide(1, 2));
    assert!(std::mem::align_of_val(&*r) == 1, "vtable align");
}

#[kani::proof]
fn box_any_holds() {
    let b: Box<dyn Any> = Box::new(7u32);
    assert!(b.downcast_ref::<u32>() == Some(&7), "type_id through the vtable");
}

#[kani::proof]
fn box_any_refuted() {
    let b: Box<dyn Any> = Box::new(7u32);
    assert!(b.downcast_ref::<u64>().is_some(), "type_id through the vtable");
}

#[kani::proof]
fn rc_any_refuted() {
    let r: Rc<dyn Any> = Rc::new(7u32);
    assert!(r.downcast_ref::<i32>().is_some(), "type_id through the vtable");
}

trait A {
    fn a(&self) -> u8;
}
trait B {
    fn b(&self) -> u8;
}
trait Sub: A + B {
    fn s(&self) -> u8;
}
struct S;
impl A for S {
    fn a(&self) -> u8 {
        10
    }
}
impl B for S {
    fn b(&self) -> u8 {
        20
    }
}
impl Sub for S {
    fn s(&self) -> u8 {
        30
    }
}

#[kani::proof]
fn upcast_box_holds() {
    let x: Box<dyn Sub> = Box::new(S);
    let y: Box<dyn B> = x;
    assert!(y.b() == 20, "upcast vtable");
}

#[kani::proof]
fn upcast_box_refuted() {
    let x: Box<dyn Sub> = Box::new(S);
    let y: Box<dyn B> = x;
    assert!(y.b() == 10, "upcast vtable");
}

#[kani::proof]
fn upcast_rc_holds() {
    let x: Rc<dyn Sub> = Rc::new(S);
    let y: Rc<dyn B> = x;
    assert!(y.b() == 20, "upcast vtable");
}

#[kani::proof]
fn upcast_rc_refuted() {
    let x: Rc<dyn Sub> = Rc::new(S);
    let y: Rc<dyn B> = x;
    assert!(y.b() == 10, "upcast vtable");
}

#[kani::proof]
fn upcast_ref_holds() {
    let s = S;
    let x: &dyn Sub = &s;
    let y: &dyn B = x;
    assert!(y.b() == 20, "upcast vtable");
}

#[kani::proof]
fn upcast_ref_refuted() {
    let s = S;
    let x: &dyn Sub = &s;
    let y: &dyn B = x;
    assert!(y.b() == 10, "upcast vtable");
}

trait Tick {
    fn tick(&self) -> u8;
}

struct Boom;
struct Calm;
struct Mild;

impl Tick for Boom {
    fn tick(&self) -> u8 {
        panic!("boom")
    }
}

impl Tick for Calm {
    fn tick(&self) -> u8 {
        1
    }
}

impl Tick for Mild {
    fn tick(&self) -> u8 {
        2
    }
}

#[kani::proof]
fn nonnull_panicking_callee_refuted() {
    let mut boom = Boom;
    let p: NonNull<dyn Tick> = NonNull::from(&mut boom);
    let _ = unsafe { p.as_ref() }.tick();
}

#[kani::proof]
fn nonnull_calm_callee_holds() {
    let mut calm = Calm;
    let p: NonNull<dyn Tick> = NonNull::from(&mut calm);
    let t = unsafe { p.as_ref() }.tick();
    let mild: &dyn Tick = &Mild;
    assert!(t == 1 && mild.tick() == 2, "calm and mild ticks");
}
