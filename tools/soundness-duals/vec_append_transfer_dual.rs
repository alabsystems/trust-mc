// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

#[kani::proof]
pub fn append_literal_safe() {
    let mut dst = vec![0u64];
    let mut src = vec![3u64];
    dst.append(&mut src);
    assert!(dst[1] == 3);
}

#[kani::proof]
pub fn append_literal_bug() {
    let mut dst = vec![0u64];
    let mut src = vec![3u64];
    dst.append(&mut src);
    assert!(dst[1] == 0);
}

#[kani::proof]
pub fn append_updated_source_safe() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64];
    src[0] = 11;
    dst.append(&mut src);
    assert!(dst[0] == 7 && dst[1] == 11 && src.len() == 0);
    // Append the now-empty source again: its own fields and the query sidecar
    // must agree that no elements move.
    dst.append(&mut src);
    assert!(dst.len() == 2 && dst[1] == 11);
}

#[kani::proof]
pub fn append_updated_source_bug() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64];
    src[0] = 11;
    dst.append(&mut src);
    assert!(dst[1] == 3);
}

#[kani::proof]
pub fn append_empty_destination_safe() {
    let mut dst = Vec::new();
    let mut src = vec![3u64];
    dst.append(&mut src);
    assert!(dst[0] == 3 && dst.len() == 1 && src.is_empty());
}

#[kani::proof]
pub fn append_empty_destination_bug() {
    let mut dst = Vec::new();
    let mut src = vec![3u64];
    dst.append(&mut src);
    assert!(dst[0] != 3);
}

#[kani::proof]
pub fn append_buffer_alias_refusal() {
    let mut dst = vec![7u64];
    let pointer = dst.as_ptr();
    let mut src = vec![3u64];
    dst.append(&mut src);
    // Reallocation may invalidate this pointer. The existing buffer mutation
    // guard must continue to refuse a decisive result through the old alias.
    assert!(unsafe { *pointer } == 7);
}

#[kani::proof]
pub fn append_cleared_source_safe() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64, 11u64];
    src.clear();
    dst.append(&mut src);
    assert!(dst.len() == 1 && dst[0] == 7);
}

#[kani::proof]
pub fn append_cleared_source_bug() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64, 11u64];
    src.clear();
    dst.append(&mut src);
    assert!(dst.len() == 3);
}

#[kani::proof]
pub fn append_truncated_source_safe() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64, 11u64];
    src.truncate(1);
    dst.append(&mut src);
    assert!(dst.len() == 2 && dst[1] == 3);
}

#[kani::proof]
pub fn append_truncated_source_bug() {
    let mut dst = vec![7u64];
    let mut src = vec![3u64, 11u64];
    src.truncate(1);
    dst.append(&mut src);
    assert!(dst.len() == 3);
}

#[kani::proof]
pub fn append_partial_remove_refusal() {
    let mut src = vec![1u64, 2u64];
    src.remove(0);
    let mut dst = vec![9u64];
    dst.append(&mut src);
    // The real first moved element is 2. A partial remove model must retain
    // its refusal rather than proving the stale pre-remove value is 1.
    assert!(dst[1] == 1);
}
