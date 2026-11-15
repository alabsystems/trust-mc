// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn slot(ordinal: usize, guard: &str, value: &str, replayable: &str) -> String {
    format!(
        "(ay_playback_guard_{ordinal} {guard})\n\
         (ay_playback_value_{ordinal} {value})\n\
         (ay_playback_replayable_{ordinal} {replayable})\n"
    )
}

fn model(count: usize, slots: &str) -> String {
    format!("sat\n((ay_playback_count (_ bv{count} 64))\n{slots})")
}

#[test]
fn skipped_conditional_u16_does_not_shift_failing_u8_input() {
    // b = false; assume(!b); if b { any::<u16>() }; x = any::<u8>(); assert!(x != 7).
    let output = model(
        3,
        &[
            slot(0, "true", "false", "true"),
            slot(1, "false", "#xbeef", "true"),
            slot(2, "true", "#x07", "true"),
        ]
        .concat(),
    );
    let trace = parse_kani_any_trace(&output).expect("complete guarded stream");
    let bits: Vec<_> =
        trace.iter().map(|item| item.value.as_ref().unwrap().binary.as_deref().unwrap()).collect();
    assert_eq!(bits, ["00000000", "00000111"]);
}

#[test]
fn creation_order_is_independent_of_model_output_order() {
    let output = model(
        3,
        &[
            slot(2, "true", "#x03", "true"),
            slot(0, "true", "#x01", "true"),
            slot(1, "true", "#x02", "true"),
        ]
        .concat(),
    );
    let trace = parse_kani_any_trace(&output).unwrap();
    let bits: Vec<_> =
        trace.iter().map(|item| item.value.as_ref().unwrap().binary.as_deref().unwrap()).collect();
    assert_eq!(bits, ["00000001", "00000010", "00000011"]);
}

#[test]
fn only_explicit_complete_empty_streams_are_accepted() {
    assert_eq!(parse_kani_any_trace(&model(0, "")).unwrap().len(), 0);
    assert!(parse_kani_any_trace("sat").is_none());
    assert!(parse_kani_any_trace("sat\n((ay_any_0 #x07))").is_none());
    assert!(parse_kani_any_trace(&model(1, "")).is_none());
}

#[test]
fn truncated_malformed_duplicate_and_unknown_markers_refuse_whole_stream() {
    let complete = model(1, &slot(0, "true", "#x07", "true"));
    let cases = [
        complete.replace("(ay_playback_guard_0 true)", ""),
        complete.replace("(ay_playback_value_0 #x07)", ""),
        complete.replace("(ay_playback_replayable_0 true)", ""),
        complete.replace("guard_0 true", "guard_0 unknown"),
        complete.replace("replayable_0 true", "replayable_0 unknown"),
        complete.replace("value_0 #x07", "value_0 #xzz"),
        complete.replace("value_0 #x07", "value_0 #b1"),
        complete.replace("value_0 #x07", "value_0 (_ bv1 8 extra)"),
        complete.replace("value_0 #x07", "value_0 (_ bv1x 8)"),
        complete.replace("value_0 #x07", "value_0 (_ bv1 4294967295)"),
        complete.replace("value_0 #x07", "value_0 _ bv1 8"),
        complete.replace("value_0 #x07", "value_0 #x07 #x08"),
        complete.replace("value_0 #x07", "value_0 (UnknownConstructor 7)"),
        complete.replace("guard_0", "guard_00"),
        complete.replace("(_ bv1 64)", "(_ bv1 8)"),
        complete[..complete.len() - 1].to_string(),
        format!("{complete}\n(ay_playback_guard_0 true)"),
        format!("{complete}\n(ay_playback_guard_1"),
        format!("{complete}\n(ay_playback_other_0 true)"),
    ];
    for output in cases {
        assert!(parse_kani_any_trace(&output).is_none(), "must refuse {output}");
    }
    for value in ["#xzz", "#bzz", "(_ bv1x 8)", "#x07 #x08"] {
        let output = model(1, &slot(0, "false", value, "true"));
        assert!(parse_kani_any_trace(&output).is_none(), "must refuse {output}");
    }
}

#[test]
fn inactive_unsupported_values_are_skipped_but_active_ones_refuse() {
    for value in ["(UnknownConstructor 7)", "((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)"]
    {
        assert!(parse_kani_any_trace(&model(1, &slot(0, "true", value, "true"))).is_none());
        assert!(
            parse_kani_any_trace(&model(1, &slot(0, "false", value, "true"))).unwrap().is_empty()
        );
    }
    assert!(parse_kani_any_trace(&model(1, &slot(0, "true", "true", "false"))).is_none());
    assert!(
        parse_kani_any_trace(&model(1, &slot(0, "false", "true", "false"))).unwrap().is_empty()
    );
}
