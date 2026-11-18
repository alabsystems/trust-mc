// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Native classification probes only; the original 16 semantic cases are separate.
#![allow(dead_code)]
use external_vec_lookalike::{EvilVec, LibraryVec, alloc::vec::Vec as ForeignVec};
type AliasVec = std::vec::Vec<u64>;
pub fn standard_len(v: &std::vec::Vec<u64>) -> usize {
    v.len()
}
pub fn standard_capacity(v: &std::vec::Vec<u64>) -> usize {
    v.capacity()
}
pub fn standard_is_empty(v: &std::vec::Vec<u64>) -> bool {
    v.is_empty()
}
pub fn standard_as_ptr(v: &std::vec::Vec<u64>) -> *const u64 {
    v.as_ptr()
}
pub fn standard_as_mut_ptr(v: &mut std::vec::Vec<u64>) -> *mut u64 {
    v.as_mut_ptr()
}
pub fn standard_as_slice(v: &std::vec::Vec<u64>) -> &[u64] {
    v.as_slice()
}
pub fn standard_as_mut_slice(v: &mut std::vec::Vec<u64>) -> &mut [u64] {
    v.as_mut_slice()
}
pub fn standard_deref(v: &std::vec::Vec<u64>) -> &[u64] {
    core::ops::Deref::deref(v)
}
pub fn standard_deref_mut(v: &mut std::vec::Vec<u64>) -> &mut [u64] {
    core::ops::DerefMut::deref_mut(v)
}
pub fn alias_len(v: &AliasVec) -> usize {
    v.len()
}
pub fn alias_capacity(v: &AliasVec) -> usize {
    v.capacity()
}
pub fn alias_is_empty(v: &AliasVec) -> bool {
    v.is_empty()
}
pub fn alias_as_ptr(v: &AliasVec) -> *const u64 {
    v.as_ptr()
}
pub fn alias_as_mut_ptr(v: &mut AliasVec) -> *mut u64 {
    v.as_mut_ptr()
}
pub fn alias_as_slice(v: &AliasVec) -> &[u64] {
    v.as_slice()
}
pub fn alias_as_mut_slice(v: &mut AliasVec) -> &mut [u64] {
    v.as_mut_slice()
}
pub fn alias_deref(v: &AliasVec) -> &[u64] {
    core::ops::Deref::deref(v)
}
pub fn alias_deref_mut(v: &mut AliasVec) -> &mut [u64] {
    core::ops::DerefMut::deref_mut(v)
}
pub fn reexport_len(v: &LibraryVec<u64>) -> usize {
    v.len()
}
pub fn reexport_capacity(v: &LibraryVec<u64>) -> usize {
    v.capacity()
}
pub fn reexport_is_empty(v: &LibraryVec<u64>) -> bool {
    v.is_empty()
}
pub fn reexport_as_ptr(v: &LibraryVec<u64>) -> *const u64 {
    v.as_ptr()
}
pub fn reexport_as_mut_ptr(v: &mut LibraryVec<u64>) -> *mut u64 {
    v.as_mut_ptr()
}
pub fn reexport_as_slice(v: &LibraryVec<u64>) -> &[u64] {
    v.as_slice()
}
pub fn reexport_as_mut_slice(v: &mut LibraryVec<u64>) -> &mut [u64] {
    v.as_mut_slice()
}
pub fn reexport_deref(v: &LibraryVec<u64>) -> &[u64] {
    core::ops::Deref::deref(v)
}
pub fn reexport_deref_mut(v: &mut LibraryVec<u64>) -> &mut [u64] {
    core::ops::DerefMut::deref_mut(v)
}
pub fn external_len(v: &ForeignVec<u64>) -> usize {
    v.len()
}
pub fn external_capacity(v: &ForeignVec<u64>) -> usize {
    v.capacity()
}
pub fn external_is_empty(v: &ForeignVec<u64>) -> bool {
    v.is_empty()
}
pub fn external_as_ptr(v: &ForeignVec<u64>) -> *const u64 {
    v.as_ptr()
}
pub fn external_as_mut_ptr(v: &mut ForeignVec<u64>) -> *mut u64 {
    v.as_mut_ptr()
}
pub fn external_as_slice(v: &ForeignVec<u64>) -> &[u64] {
    v.as_slice()
}
pub fn foreign_trait_len(v: &LibraryVec<u64>) -> usize {
    EvilVec::len(v)
}
pub fn virtual_len(v: &dyn EvilVec) -> usize {
    v.len()
}
pub fn indirect_len(f: fn(&LibraryVec<u64>) -> usize, v: &LibraryVec<u64>) -> usize {
    f(v)
}
pub fn unresolved_len<T: EvilVec>(v: &T) -> usize {
    EvilVec::len(v)
}
#[inline(never)]
fn generic_deref<T: core::ops::Deref<Target = [u64]>>(v: &T) -> &[u64] {
    core::ops::Deref::deref(v)
}
#[inline(never)]
fn generic_deref_mut<T: core::ops::DerefMut<Target = [u64]>>(v: &mut T) -> &mut [u64] {
    core::ops::DerefMut::deref_mut(v)
}
pub fn adapted_deref(v: &LibraryVec<u64>) -> &[u64] {
    generic_deref(v)
}
pub fn adapted_deref_mut(v: &mut LibraryVec<u64>) -> &mut [u64] {
    generic_deref_mut(v)
}
