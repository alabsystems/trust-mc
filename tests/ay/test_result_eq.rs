// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

#[kani::proof]
fn main() {
    let r: Result<bool, bool> = Ok(true);
    assert!(r == Ok(true));
}
