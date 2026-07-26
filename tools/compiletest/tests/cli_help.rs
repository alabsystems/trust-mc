// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::process::Command;

#[test]
fn help_exits_successfully() {
    let compiletest = env!("CARGO_BIN_EXE_compiletest");

    let output = Command::new(compiletest).arg("--help").output().expect("run compiletest --help");

    assert!(
        output.status.success(),
        "compiletest --help exited unsuccessfully\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Usage:"),
        "expected Usage line in stdout\nstdout:\n{}\nstderr:\n{}",
        stdout,
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(!stdout.contains("--ignored"), "test suppression option must not be exposed");
    assert!(!stdout.contains("fixme"), "file-name selection mode must not be exposed");
}
