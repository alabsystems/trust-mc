// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// kani-expect: PROOF
// NOTE: All harnesses demoted PROOF→UNKNOWN by false proof defense (ay#8578).
use std::sync::Arc;
#[kani::proof]
fn test_arc_u32() {
    let _s: Arc<u32> = Arc::new(42u32);
}
