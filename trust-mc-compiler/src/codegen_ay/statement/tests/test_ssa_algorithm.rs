// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Algorithm-level SSA versioning tests using SsaVersionTracker mock.
//!
//! These tests verify the SSA naming ALGORITHM in isolation (monotonicity,
//! uniqueness, injectivity) without requiring MIR context construction.
//! MIR-driven integration tests live in `tests/ssa.rs`.
//!
//! Extracted from ssa.rs inline tests per design:
//! designs/2026-02-24-ssa-rs-decomposition.md

use std::collections::HashMap;

/// Simulates the SSA versioning logic for isolated testing.
///
/// # Design Note
/// This mirrors the HashMap-based versioning in `StatementCodegen`.
/// Testing the actual production code requires MIR context construction,
/// which is complex. These tests verify the ALGORITHM is correct; the
/// debug assertions in production code verify the implementation matches.
///
/// If these tests pass but production fails debug assertions, the
/// implementation diverged from the tested algorithm.
struct SsaVersionTracker {
    versions: HashMap<String, u32>,
}

impl SsaVersionTracker {
    fn new() -> Self {
        Self { versions: HashMap::new() }
    }

    /// Get current version and increment (mirrors next_ssa_version)
    fn next_version(&mut self, var_name: &str) -> u32 {
        let version = self.versions.entry(var_name.to_string()).or_insert(0);
        let current = *version;
        *version = current.checked_add(1).expect("SSA version overflow");
        current
    }

    /// Get SSA name (mirrors ssa_name_from_base)
    fn ssa_name(&mut self, base_name: &str, increment: bool) -> String {
        if increment {
            let version = self.next_version(base_name);
            format!("{}_{}", base_name, version)
        } else {
            let next_version = *self.versions.get(base_name).unwrap_or(&0);
            let version = next_version.saturating_sub(1);
            format!("{}_{}", base_name, version)
        }
    }
}

#[test]
fn test_ssa_version_monotonic_increase() {
    let mut tracker = SsaVersionTracker::new();

    // First allocation returns 0
    assert_eq!(tracker.next_version("x"), 0);
    // Second allocation returns 1
    assert_eq!(tracker.next_version("x"), 1);
    // Third allocation returns 2
    assert_eq!(tracker.next_version("x"), 2);

    // Versions are strictly increasing
    let mut prev = tracker.next_version("x");
    for _ in 0..10 {
        let curr = tracker.next_version("x");
        assert!(curr > prev, "Version must be strictly increasing");
        prev = curr;
    }
}

#[test]
fn test_ssa_version_independence_per_variable() {
    let mut tracker = SsaVersionTracker::new();

    // Different variables have independent versioning
    assert_eq!(tracker.next_version("a"), 0);
    assert_eq!(tracker.next_version("b"), 0);
    assert_eq!(tracker.next_version("c"), 0);

    // Incrementing one doesn't affect others
    assert_eq!(tracker.next_version("a"), 1);
    assert_eq!(tracker.next_version("a"), 2);
    assert_eq!(tracker.next_version("b"), 1); // b allocates version 1 (independent of a)
    assert_eq!(tracker.next_version("c"), 1); // c allocates version 1 (independent of a, b)
}

#[test]
fn test_ssa_name_with_increment() {
    let mut tracker = SsaVersionTracker::new();

    // With increment=true, allocates new versions
    assert_eq!(tracker.ssa_name("fn::local_0", true), "fn::local_0_0");
    assert_eq!(tracker.ssa_name("fn::local_0", true), "fn::local_0_1");
    assert_eq!(tracker.ssa_name("fn::local_0", true), "fn::local_0_2");
}

#[test]
fn test_ssa_name_without_increment_returns_current() {
    let mut tracker = SsaVersionTracker::new();

    // Edge case: before any allocation, returns version 0 even though none was allocated.
    // This matches production code behavior (saturating_sub(1) on 0 = 0).
    // In practice, increment=false is only called after at least one allocation.
    assert_eq!(tracker.ssa_name("fn::local_0", false), "fn::local_0_0");

    // Allocate version 0
    assert_eq!(tracker.ssa_name("fn::local_0", true), "fn::local_0_0");

    // Without increment, returns the most recent (version 0)
    assert_eq!(tracker.ssa_name("fn::local_0", false), "fn::local_0_0");

    // Allocate version 1
    assert_eq!(tracker.ssa_name("fn::local_0", true), "fn::local_0_1");

    // Without increment, returns the most recent (version 1)
    assert_eq!(tracker.ssa_name("fn::local_0", false), "fn::local_0_1");
}

#[test]
fn test_ssa_name_uniqueness() {
    let mut tracker = SsaVersionTracker::new();
    let mut seen = std::collections::HashSet::new();

    // Generate 100 SSA names for the same base
    for _ in 0..100 {
        let name = tracker.ssa_name("fn::local_0", true);
        assert!(
            seen.insert(name.clone()),
            "SSA name should be unique: {} was already generated",
            name
        );
    }

    // Generate names for different bases
    for base in &["fn::local_1", "fn::local_2", "fn::local_0_field_0"] {
        for _ in 0..10 {
            let name = tracker.ssa_name(base, true);
            assert!(seen.insert(name.clone()), "SSA name should be unique across bases: {}", name);
        }
    }
}

#[test]
fn test_ssa_name_format() {
    let mut tracker = SsaVersionTracker::new();

    let name = tracker.ssa_name("test::var", true);

    // Name should end with _N where N is a valid u32
    assert!(name.contains('_'));
    let suffix = name.rsplit('_').next().expect("rsplit always returns at least one element");
    assert!(suffix.parse::<u32>().is_ok(), "Suffix should be a valid u32: {}", suffix);
}

/// Test format validation with complex base names matching production patterns.
/// Production generates names like: fn::local_0_field_1_deref
#[test]
fn test_ssa_name_format_complex_bases() {
    let mut tracker = SsaVersionTracker::new();

    // Base names with multiple underscore segments (from projections)
    let complex_bases = [
        "fn::local_0_field_0",
        "fn::local_1_field_2_field_3",
        "fn::local_0_deref",
        "fn::local_0_field_0_deref",
        "fn::local_0_variant_1",
        "fn::local_0_idx_by_1",
        "fn::local_0_cidx_5",
        "fn::local_0_cidx_end_3",
        "fn::local_0_subslice_1_5",
        "fn::local_0_cast",
    ];

    for base in &complex_bases {
        let name = tracker.ssa_name(base, true);

        // Verify format: must end with _N where N is version number
        assert!(name.contains('_'), "Name should contain underscore: {}", name);
        let suffix = name.rsplit('_').next().expect("rsplit always returns at least one element");
        assert!(
            suffix.parse::<u32>().is_ok(),
            "Complex base '{}' produces name '{}' with invalid suffix '{}'",
            base,
            name,
            suffix
        );

        // Verify the name starts with the base
        assert!(name.starts_with(base), "Name '{}' should start with base '{}'", name, base);
    }
}

/// Test that version suffix is distinguishable from base name patterns.
/// Edge case: base name ending in digits should still produce unique names.
#[test]
fn test_ssa_name_digit_suffix_disambiguation() {
    let mut tracker = SsaVersionTracker::new();

    // Base name that ends in digits (e.g., from local index)
    let name_v0 = tracker.ssa_name("fn::local_99", true);
    let name_v1 = tracker.ssa_name("fn::local_99", true);

    assert_eq!(name_v0, "fn::local_99_0");
    assert_eq!(name_v1, "fn::local_99_1");

    // Different base name that looks similar
    let other_v0 = tracker.ssa_name("fn::local_9", true);
    assert_eq!(other_v0, "fn::local_9_0");

    // Verify uniqueness despite similar patterns
    assert_ne!(name_v0, other_v0, "Names from different bases must differ");
}

// === Part of #1442: Formal proof tests for SSA versioning uniqueness ===

/// Exhaustive uniqueness test across many bases and versions.
///
/// This is a "poor man's property test" that checks global uniqueness
/// across 950 generated names (19 bases × 50 versions).
///
/// Part of #1442: SSA versioning uniqueness proof.
#[test]
fn test_ssa_global_uniqueness_exhaustive() {
    let mut tracker = SsaVersionTracker::new();
    let mut all_names = std::collections::HashSet::new();

    // Generate comprehensive base names covering all projection types
    let base_patterns = [
        // Simple locals (common case)
        "fn::local_0",
        "fn::local_1",
        "fn::local_255",
        // Field projections (struct access)
        "fn::local_0_field_0",
        "fn::local_0_field_1",
        "fn::local_0_field_0_field_1",
        // Deref projections (pointer dereference)
        "fn::local_0_deref",
        "fn::local_0_field_0_deref",
        // Variant projections (enum matching)
        "fn::local_0_variant_0",
        "fn::local_0_variant_1",
        // Index projections (array indexing)
        "fn::local_0_idx_by_0",
        "fn::local_0_idx_by_1",
        // Constant index projections (slice patterns)
        "fn::local_0_cidx_0",
        "fn::local_0_cidx_end_0",
        // Subslice projections
        "fn::local_0_subslice_0_1",
        "fn::local_0_subslice_end_0_1",
        // Cast projections
        "fn::local_0_cast",
        // Complex nested projections
        "fn::local_0_field_0_deref_field_1",
        "other::local_0", // Different function names
    ];

    // Generate 50 versions for each base pattern
    for base in &base_patterns {
        for _ in 0..50 {
            let name = tracker.ssa_name(base, true);
            assert!(
                all_names.insert(name.clone()),
                "UNIQUENESS VIOLATION: '{}' was generated twice (base: {})",
                name,
                base
            );
        }
    }

    // Total: 19 bases * 50 versions = 950 unique names verified
    assert_eq!(all_names.len(), base_patterns.len() * 50);
    assert_eq!(base_patterns.len(), 19, "Update comment if pattern count changes");
}

/// Test interleaved allocation pattern (simulates real control flow).
///
/// Real programs alternate between variables, not sequentially allocate
/// all versions of one variable. This tests that interleaved access
/// doesn't break uniqueness.
///
/// Part of #1442: SSA versioning uniqueness proof.
#[test]
fn test_ssa_interleaved_allocation_pattern() {
    let mut tracker = SsaVersionTracker::new();
    let mut all_names = std::collections::HashSet::new();

    let bases = ["fn::x", "fn::y", "fn::z"];

    // Simulate interleaved access pattern like real control flow:
    // With (round + i) % 3 != 0: y_0, z_0, x_0, y_1, x_1, z_1, y_2, z_2, x_2...
    for round in 0..100 {
        for (i, base) in bases.iter().enumerate() {
            // Access pattern varies by round to test different orderings
            let access_this_round = (round + i) % 3 != 0;
            if access_this_round {
                let name = tracker.ssa_name(base, true);
                assert!(
                    all_names.insert(name.clone()),
                    "Interleaved allocation produced duplicate: {}",
                    name
                );
            }
        }
    }

    // With (round + i) % 3 != 0, exactly 2 of 3 bases access each round
    // 100 rounds * 2 accesses/round = 200 unique names
    assert_eq!(all_names.len(), 200, "Expected exactly 200 unique names from interleaving");
}

/// Mathematical proof that SSA naming is injective (no collisions).
///
/// Proof outline:
/// - base_A_N and base_B_M are equal iff base_A == base_B AND N == M
/// - Since N is monotonically increasing per base, and bases are distinct,
///   no two calls can produce the same name.
///
/// This test verifies the key lemma: different bases with same version
/// produce different names (bases don't collide).
///
/// Part of #1442: SSA versioning uniqueness proof.
#[test]
fn test_ssa_injectivity_proof() {
    let mut tracker = SsaVersionTracker::new();

    // Lemma 1: Same base, different versions => different names
    let name_0 = tracker.ssa_name("fn::local_0", true);
    let name_1 = tracker.ssa_name("fn::local_0", true);
    assert_ne!(name_0, name_1, "Lemma 1 violation: same base, different versions");

    // Lemma 2: Different bases, same version number => different names
    // Reset with fresh tracker
    let mut tracker2 = SsaVersionTracker::new();
    let a_0 = tracker2.ssa_name("fn::local_0", true);
    let b_0 = tracker2.ssa_name("fn::local_1", true);
    assert_ne!(a_0, b_0, "Lemma 2 violation: different bases, version 0");

    // Lemma 3: Confusable base patterns don't collide
    // "fn::local_10" vs "fn::local_1" + version 0 could look similar
    let mut tracker3 = SsaVersionTracker::new();
    let short_v0 = tracker3.ssa_name("fn::local_1", true); // "fn::local_1_0"
    let long_v0 = tracker3.ssa_name("fn::local_10", true); // "fn::local_10_0"
    assert_ne!(short_v0, long_v0, "Lemma 3 violation: confusable bases");

    // The names differ in their base portion before the version suffix
    assert_eq!(short_v0, "fn::local_1_0");
    assert_eq!(long_v0, "fn::local_10_0");
}

/// Test that version counter state is correctly maintained.
///
/// This verifies the internal HashMap state matches what we expect,
/// which is crucial for the monotonicity guarantee.
///
/// Part of #1442: SSA versioning uniqueness proof.
#[test]
#[allow(clippy::unwrap_used)]
fn test_ssa_version_counter_state() {
    let mut tracker = SsaVersionTracker::new();

    // Initially empty
    assert!(tracker.versions.is_empty());

    // After first allocation, version advances to 1 (next to allocate)
    let _ = tracker.ssa_name("fn::x", true);
    assert_eq!(*tracker.versions.get("fn::x").unwrap(), 1);

    // After second allocation, version advances to 2
    let _ = tracker.ssa_name("fn::x", true);
    assert_eq!(*tracker.versions.get("fn::x").unwrap(), 2);

    // Different variable has independent counter
    let _ = tracker.ssa_name("fn::y", true);
    assert_eq!(*tracker.versions.get("fn::y").unwrap(), 1);
    assert_eq!(*tracker.versions.get("fn::x").unwrap(), 2); // x unchanged

    // Non-increment read doesn't advance counter
    let _ = tracker.ssa_name("fn::x", false);
    assert_eq!(*tracker.versions.get("fn::x").unwrap(), 2); // still 2
}

/// Test edge cases: empty, tricky, and long base names.
///
/// Verifies SSA naming handles unusual but valid base names correctly.
/// Part of #1442: SSA versioning uniqueness proof.
#[test]
fn test_ssa_edge_case_base_names() {
    let mut tracker = SsaVersionTracker::new();
    let mut seen = std::collections::HashSet::new();

    // Edge case 1: Empty base name (not possible in production since ssa_base_name
    // always produces non-empty names, but tests the algorithm handles it gracefully)
    let empty_v0 = tracker.ssa_name("", true);
    assert_eq!(empty_v0, "_0", "Empty base should produce _0");
    assert!(seen.insert(empty_v0));

    // Edge case 2: Base name that looks like a version suffix
    let tricky_v0 = tracker.ssa_name("_0", true);
    assert_eq!(tricky_v0, "_0_0", "Base '_0' should produce '_0_0'");
    assert!(seen.insert(tricky_v0));

    // Edge case 3: Very long base name
    let long_base = "fn::local_".to_string() + &"x".repeat(100);
    let long_v0 = tracker.ssa_name(&long_base, true);
    assert!(long_v0.ends_with("_0"), "Long base should end with version suffix");
    assert!(seen.insert(long_v0));

    // All edge cases produce unique names
    assert_eq!(seen.len(), 3);
}
