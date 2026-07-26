// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// compile-flags: --edition 2018
// kani-flags: --no-unwinding-checks

use kani::futures::{JoinHandle, SchedulingAssumption, SchedulingStrategy};

struct Custom;

impl SchedulingStrategy for Custom {
    fn pick_task(&mut self, _num_tasks: usize) -> (usize, SchedulingAssumption) {
        (0, SchedulingAssumption::CannotAssumeRunning)
    }
}

fn takes_handle(_: JoinHandle) {}

#[kani::proof]
fn main() {
    let _strategy: Option<&dyn SchedulingStrategy> = None;
    let _ = kani::RoundRobin::default();
    let _ = SchedulingAssumption::CannotAssumeRunning;
    let _handle: Option<JoinHandle> = None;
    let _ = takes_handle as fn(JoinHandle);
    let _ = Custom;
}
