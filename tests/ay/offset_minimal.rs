// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: offset_minimal=PROOF
// NOTE: offset_minimal gained PROOF at ay 8a4a9bcc2.
//! Diagnostic: any_where with simple bound (no Vec capture).

#[kani::proof]
fn offset_minimal() {
    let offset: usize = kani::any_where(|o: &usize| *o <= 2);
    assert!(offset <= 2);
}
