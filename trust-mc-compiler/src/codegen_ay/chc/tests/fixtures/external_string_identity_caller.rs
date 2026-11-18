// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(dead_code)]
extern crate external_vec_lookalike;
use external_vec_lookalike::{LibraryString, alloc::string::String as ForeignString};
use std::string::String as Alias;

pub fn standard_new() -> std::string::String {
    std::string::String::new()
}
pub fn alias_new() -> Alias {
    Alias::new()
}
pub fn reexport_new() -> LibraryString {
    LibraryString::new()
}
pub fn standard_default() -> std::string::String {
    Default::default()
}
pub fn alias_default() -> Alias {
    Default::default()
}
pub fn reexport_default() -> LibraryString {
    Default::default()
}
pub fn standard_len(value: &std::string::String) -> usize {
    value.len()
}
pub fn alias_len(value: &Alias) -> usize {
    value.len()
}
pub fn reexport_len(value: &LibraryString) -> usize {
    value.len()
}
pub fn standard_is_empty(value: &std::string::String) -> bool {
    value.is_empty()
}
pub fn alias_is_empty(value: &Alias) -> bool {
    value.is_empty()
}
pub fn reexport_is_empty(value: &LibraryString) -> bool {
    value.is_empty()
}
pub fn standard_as_str(value: &std::string::String) -> &str {
    value.as_str()
}
pub fn alias_as_str(value: &Alias) -> &str {
    value.as_str()
}
pub fn reexport_as_str(value: &LibraryString) -> &str {
    value.as_str()
}
pub fn standard_deref(value: &std::string::String) -> &str {
    std::ops::Deref::deref(value)
}
pub fn alias_deref(value: &Alias) -> &str {
    std::ops::Deref::deref(value)
}
pub fn reexport_deref(value: &LibraryString) -> &str {
    std::ops::Deref::deref(value)
}
pub fn standard_deref_mut(value: &mut std::string::String) -> &mut str {
    std::ops::DerefMut::deref_mut(value)
}
pub fn alias_deref_mut(value: &mut Alias) -> &mut str {
    std::ops::DerefMut::deref_mut(value)
}
pub fn reexport_deref_mut(value: &mut LibraryString) -> &mut str {
    std::ops::DerefMut::deref_mut(value)
}
pub fn standard_from(value: &str) -> LibraryString {
    LibraryString::from(value)
}
pub fn standard_clone(value: &LibraryString) -> LibraryString {
    value.clone()
}
pub fn standard_to_owned(value: &str) -> LibraryString {
    value.to_owned()
}
pub fn standard_to_string(value: &LibraryString) -> LibraryString {
    value.to_string()
}
pub fn standard_str_eq(lhs: &&str, rhs: &&str) -> bool {
    std::cmp::PartialEq::eq(lhs, rhs)
}
pub fn standard_cow(value: &std::borrow::Cow<'_, str>) -> LibraryString {
    value.to_string()
}

pub fn foreign_new() -> ForeignString {
    ForeignString::new()
}
pub fn foreign_default() -> ForeignString {
    Default::default()
}
pub fn foreign_len(value: &ForeignString) -> usize {
    value.len()
}
pub fn foreign_is_empty(value: &ForeignString) -> bool {
    value.is_empty()
}
pub fn foreign_deref(value: &ForeignString) -> &str {
    std::ops::Deref::deref(value)
}
pub fn foreign_trait_len(value: &LibraryString) -> usize {
    external_vec_lookalike::EvilString::len(value)
}
pub fn foreign_trait_is_empty(value: &LibraryString) -> bool {
    external_vec_lookalike::EvilString::is_empty(value)
}
pub fn foreign_bounded() -> ForeignString {
    <ForeignString as external_vec_lookalike::BoundedString>::bounded_any::<3>()
}
pub fn foreign_cow(value: &external_vec_lookalike::Cow<str>) -> LibraryString {
    value.to_string()
}
pub fn indirect_len(function: fn(&LibraryString) -> usize, value: &LibraryString) -> usize {
    function(value)
}
pub fn virtual_len(value: &dyn external_vec_lookalike::EvilString) -> usize {
    value.len()
}
pub fn identities(_: LibraryString, _: Alias, _: std::string::String, _: ForeignString) {}
