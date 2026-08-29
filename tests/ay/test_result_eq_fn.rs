// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: PROOF

fn make_ok() -> Result<bool, bool> {
    Ok(true)
}

#[kani::proof]
fn main() {
    let r = make_ok();
    assert!(r == Ok(true));
}
