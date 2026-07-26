// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! SMT model value parsing for trace extraction.

use std::borrow::Cow;
use std::collections::HashMap;

use crate::property_model::{RawSourceLocation, TraceArrayValue, TraceData, TraceItem, TraceValue};

/// Parse kani::any_raw values from solver output into trace items.
///
/// Extracts (ay_any_N value) pairs from get-value output and converts them
/// to TraceItem format for concrete playback.
///
/// REQUIRES: output is solver output containing (ay_any_* value) entries (may be empty)
/// REQUIRES: value formats are bitvector (#b, #x, (_ bvN W)), bool, or array models
/// ENSURES: each ay_any entry with parseable value produces exactly one TraceItem
/// ENSURES: returned TraceItems have step_type == "assignment"
/// ENSURES: returned TraceItems have function == "kani::any_raw_internal::<ay>"
pub(crate) fn parse_kani_any_trace(output: &str) -> Vec<TraceItem> {
    let pairs = extract_named_pairs(output, "ay_any_");
    let mut items = Vec::new();

    for (idx, (_name, value)) in pairs.into_iter().enumerate() {
        if let Some(trace_value) = trace_value_from_model_value(&value) {
            items.push(TraceItem {
                step_type: Cow::Borrowed("assignment"),
                lhs: Some(format!("goto_symex$$return_value{idx}")),
                source_location: Some(RawSourceLocation {
                    column: None,
                    file: None,
                    function: Some("kani::any_raw_internal::<ay>".to_string()),
                    line: None,
                }),
                value: Some(trace_value),
            });
        }
    }

    items
}

/// Extract `(name value)` pairs for a given prefix from SMT solver output.
pub(super) fn extract_named_pairs(output: &str, prefix: &str) -> Vec<(String, String)> {
    let mut pairs = Vec::new();
    let needle = format!("({prefix}");
    let mut offset = 0;

    while let Some(start_rel) = output[offset..].find(&needle) {
        let start = offset + start_rel;
        let mut depth = 0usize;
        let mut end = None;

        for (idx, ch) in output[start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        end = Some(start + idx + 1);
                        break;
                    }
                }
                _ => {}
            }
        }

        let Some(end_idx) = end else {
            break;
        };

        let inner = output[start + 1..end_idx - 1].trim();
        let (name, value) = split_name_value(inner);
        if let (Some(name), Some(value)) = (name, value) {
            pairs.push((name, value));
        }

        offset = end_idx;
    }

    pairs
}

fn split_name_value(s: &str) -> (Option<String>, Option<String>) {
    let mut chars = s.char_indices();
    let mut name_end = None;
    let mut name_start = None;

    for (idx, ch) in &mut chars {
        if !ch.is_whitespace() {
            name_start = Some(idx);
            break;
        }
    }

    if let Some(start) = name_start {
        for (idx, ch) in s[start..].char_indices() {
            if ch.is_whitespace() {
                name_end = Some(start + idx);
                break;
            }
        }
    }

    let Some(start) = name_start else {
        return (None, None);
    };
    let end = name_end.unwrap_or(s.len());
    let name = s[start..end].trim().to_string();
    let value = s[end..].trim();
    if value.is_empty() {
        return (Some(name), None);
    }

    (Some(name), Some(value.to_string()))
}

pub(super) fn trace_value_from_model_value(value: &str) -> Option<TraceValue> {
    let trimmed = value.trim();
    if trimmed == "true" || trimmed == "false" {
        let bit = if trimmed == "true" { '1' } else { '0' };
        let bits: String = std::iter::repeat_n(bit, 1).collect();
        let padded = format!("{:0>8}", bits);
        return Some(TraceValue {
            binary: Some(padded),
            data: Some(TraceData::Bool(trimmed == "true")),
            width: Some(8),
            elements: None,
        });
    }

    if let Some(bits) = trimmed.strip_prefix("#b") {
        return Some(TraceValue {
            binary: Some(bits.to_string()),
            data: Some(TraceData::NonBool(format!("#b{bits}"))),
            width: Some(bits.len() as u32),
            elements: None,
        });
    }

    if let Some(hex) = trimmed.strip_prefix("#x") {
        let bits = hex_to_bits(hex)?;
        return Some(TraceValue {
            binary: Some(bits),
            data: Some(TraceData::NonBool(format!("#x{hex}"))),
            width: Some((hex.len() * 4) as u32),
            elements: None,
        });
    }

    if let Some((dec, width)) = parse_bv_sexpr(trimmed) {
        let bits = decimal_to_bits(&dec, width);
        return Some(TraceValue {
            binary: Some(bits),
            data: Some(TraceData::NonBool(dec.to_owned())),
            width: Some(width),
            elements: None,
        });
    }

    // Try parsing as SMT array model (#271)
    if let Some(array_val) = parse_array_model(trimmed) {
        return Some(array_val);
    }

    None
}

fn parse_bv_sexpr(value: &str) -> Option<(&str, u32)> {
    let trimmed = value.trim();
    let inner =
        trimmed.strip_prefix('(').and_then(|s| s.strip_suffix(')')).unwrap_or(trimmed).trim();
    let mut parts = inner.split_whitespace();
    let head = parts.next()?;
    let bv = parts.next()?;
    let width = parts.next()?;

    if head != "_" || !bv.starts_with("bv") {
        return None;
    }

    let dec = bv.trim_start_matches("bv");
    let width = width.parse::<u32>().ok()?;
    Some((dec, width))
}

fn hex_to_bits(hex: &str) -> Option<String> {
    use std::fmt::Write;
    let mut bits = String::with_capacity(hex.len() * 4);
    for ch in hex.chars() {
        let val = ch.to_digit(16)?;
        write!(bits, "{val:04b}").ok()?;
    }
    Some(bits)
}

fn decimal_to_bits(dec: &str, width: u32) -> String {
    let mut digits: Vec<u8> = dec.chars().filter_map(|c| c.to_digit(10).map(|v| v as u8)).collect();
    if digits.is_empty() {
        return "0".to_string();
    }

    let mut bits = Vec::new();
    // Part of #2042: Track start index instead of Vec::remove(0) which is O(n).
    let mut start = 0;
    while digits[start..].iter().any(|&d| d != 0) {
        let mut carry = 0u8;
        for d in &mut digits[start..] {
            let num = carry * 10 + *d;
            *d = num / 2;
            carry = num % 2;
        }
        bits.push(carry);
        while start < digits.len() && digits[start] == 0 {
            start += 1;
        }
    }

    let mut bit_str: String =
        bits.into_iter().rev().map(|b| if b == 0 { '0' } else { '1' }).collect();
    if bit_str.is_empty() {
        bit_str.push('0');
    }

    let width_usize = width as usize;
    if bit_str.len() < width_usize {
        let pad_len = width_usize - bit_str.len();
        bit_str.reserve(pad_len);
        // Insert zeros at the front without allocating a second String.
        bit_str.insert_str(0, &"0".repeat(pad_len));
    }

    bit_str
}

/// Parse SMT array model into TraceValue with elements. (#271)
///
/// Supports:
/// - Constant arrays: `((as const (Array K V)) default_value)`
/// - Store chains: `(store base idx val)` (recursively parsed)
///
/// For arrays, we extract stored element values. The array size is not known
/// from the model alone, so we return elements for explicitly stored indices.
fn parse_array_model(value: &str) -> Option<TraceValue> {
    let trimmed = value.trim();

    // Check for constant array: ((as const (Array ...)) val)
    if trimmed.starts_with("((as const") {
        return parse_const_array(trimmed);
    }

    // Check for store chain: (store ...)
    if trimmed.starts_with("(store ") {
        return parse_store_chain(trimmed);
    }

    None
}

/// Parse constant array: `((as const (Array K V)) default_value)`
fn parse_const_array(value: &str) -> Option<TraceValue> {
    // Find the default value (after the closing paren of the sort)
    // Format: ((as const (Array K V)) default_value)
    let inner = value.strip_prefix('(')?.strip_suffix(')')?;

    // Find the closing paren of (as const (Array K V))
    let mut depth = 0;
    let mut as_const_end = None;
    for (i, ch) in inner.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    as_const_end = Some(i + 1);
                    break;
                }
            }
            _ => {}
        }
    }

    let end_idx = as_const_end?;
    let default_str = inner[end_idx..].trim();

    // Parse the default value
    let default_val = trace_value_from_model_value(default_str)?;

    // For constant arrays, return as a single-element array representation
    // The actual array size needs to come from harness metadata
    Some(TraceValue {
        binary: None,
        data: None,
        width: None,
        elements: Some(vec![TraceArrayValue { value: default_val }]),
    })
}

/// Parse store chain: `(store base idx val)` recursively
fn parse_store_chain(value: &str) -> Option<TraceValue> {
    let mut elements: Vec<(u64, TraceValue)> = Vec::new();
    let mut current = value.trim();

    // Recursively extract (store base idx val) entries
    while current.starts_with("(store ") {
        let inner = current.strip_prefix("(store ")?.strip_suffix(')')?.trim();

        // Parse: base idx val (base can be nested store or const array)
        // We need to find the boundaries carefully due to nested parens
        let (base, rest) = split_first_sexpr(inner)?;
        let (idx_str, val_str) = split_first_sexpr(rest.trim())?;

        // Parse index and value
        if let (Some(idx), Some(val)) =
            (parse_index_value(idx_str.trim()), trace_value_from_model_value(val_str.trim()))
        {
            elements.push((idx, val));
        }

        current = base.trim();
    }

    // If we have elements, return them (sorted by index, deduplicated)
    // Note: In SMT, later stores shadow earlier ones. Since we process outside-in,
    // the first occurrence of each index is the winning value. We use a HashMap
    // to ensure only the first (winning) value for each index is kept.
    if !elements.is_empty() {
        let mut deduped: HashMap<u64, TraceValue> = HashMap::new();
        for (idx, val) in elements {
            // Only insert if not already present (first/outer wins)
            deduped.entry(idx).or_insert(val);
        }
        let mut sorted: Vec<_> = deduped.into_iter().collect();
        sorted.sort_by_key(|(idx, _)| *idx);
        let trace_elements: Vec<TraceArrayValue> =
            sorted.into_iter().map(|(_, val)| TraceArrayValue { value: val }).collect();

        return Some(TraceValue {
            binary: None,
            data: None,
            width: None,
            elements: Some(trace_elements),
        });
    }

    None
}

/// Split the first S-expression from the remaining string.
fn split_first_sexpr(s: &str) -> Option<(&str, &str)> {
    let trimmed = s.trim();

    if trimmed.starts_with('(') {
        // Find matching closing paren
        let mut depth = 0;
        for (i, ch) in trimmed.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some((&trimmed[..=i], &trimmed[i + 1..]));
                    }
                }
                _ => {}
            }
        }
        None
    } else {
        // Not a paren-expression, find next whitespace
        let end = trimmed.find(char::is_whitespace).unwrap_or(trimmed.len());
        Some((&trimmed[..end], &trimmed[end..]))
    }
}

/// Parse an index value from SMT model (bitvector or decimal).
fn parse_index_value(s: &str) -> Option<u64> {
    let trimmed = s.trim();

    // Try hex: #xN
    if let Some(hex) = trimmed.strip_prefix("#x") {
        return u64::from_str_radix(hex, 16).ok();
    }

    // Try binary: #bN
    if let Some(bin) = trimmed.strip_prefix("#b") {
        return u64::from_str_radix(bin, 2).ok();
    }

    // Try (_ bvN W) format
    if let Some((dec, _)) = parse_bv_sexpr(trimmed) {
        return dec.parse().ok();
    }

    // Try plain decimal
    trimmed.parse().ok()
}
