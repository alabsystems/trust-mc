// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::property_model::{CheckStatus, Property, TraceItem};

pub(crate) const UNSUPPORTED_CONSTRUCT_DESC: &str = "is not currently supported by trust_mc";
const UNWINDING_ASSERT_DESC: &str = "unwinding assertion loop";
const UNWINDING_ASSERT_REC_DESC: &str = "recursion unwinding assertion";

pub(crate) fn build_failure_message(description: &str, trace: &Option<Vec<TraceItem>>) -> String {
    let backup_failure_message = format!("Failed Checks: {description}\n");
    let Some(failure_trace) = trace else {
        return backup_failure_message;
    };
    let Some(last_item) = failure_trace.last() else {
        return backup_failure_message;
    };
    let Some(failure_source) = &last_item.source_location else {
        return backup_failure_message;
    };

    if let Some(failure_file) = &failure_source.file
        && let Some(failure_function) = &failure_source.function
        && let Some(failure_line) = &failure_source.line
    {
        return format!(
            "Failed Checks: {description}\n File: \"{failure_file}\", line {failure_line}, in {failure_function}\n"
        );
    }
    backup_failure_message
}

pub(crate) fn has_check_failure(properties: &[Property], description: &str) -> bool {
    for prop in properties {
        if prop.status == CheckStatus::Failure && prop.description.contains(description) {
            return true;
        }
    }
    false
}

pub(crate) fn has_unwinding_assertion_failures(properties: &[Property]) -> bool {
    has_check_failure(properties, UNWINDING_ASSERT_DESC)
        || has_check_failure(properties, UNWINDING_ASSERT_REC_DESC)
}
