#![allow(dead_code)]
// Three arithmetic ops -> the direct lane should emit overflow/div asserts.
pub fn f(a: i32, b: i32) -> i32 {
    let s = a + b;
    let d = a / b;
    s * d
}
