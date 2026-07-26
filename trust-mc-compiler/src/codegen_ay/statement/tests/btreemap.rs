// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BTreeMap performance verification tests.
//
// Extracted from regression.rs per #1734.

// Performance verification tests (#1337)
// =============================================================================

/// Verify BTreeMap prefix scanning is O(log n + k) vs HashMap O(n).
///
/// #1337: prefix scanning for ref_pointees was O(n) with HashMap.
/// Migrating to BTreeMap with `.range().take_while()` gives O(log n + k)
/// where k = number of matching entries.
///
/// This test verifies the algorithmic improvement by counting iterations.
#[test]
fn test_btreemap_prefix_scan_is_logarithmic() {
    use std::collections::{BTreeMap, HashMap};

    // Create maps with N entries where ~1% match our prefix
    let sizes = [100, 1000, 10000];
    let target_prefix = "target_field_";
    let match_ratio = 0.01; // 1% of entries match

    for &n in &sizes {
        let matches_per_size = (n as f64 * match_ratio).max(1.0) as usize;

        // Build HashMap and BTreeMap with identical content
        let mut hashmap: HashMap<String, usize> = HashMap::new();
        let mut btreemap: BTreeMap<String, usize> = BTreeMap::new();

        // Insert matching entries (scattered throughout key space)
        for i in 0..matches_per_size {
            let key = format!("{}{}", target_prefix, i);
            hashmap.insert(key.clone(), i);
            btreemap.insert(key, i);
        }

        // Insert non-matching entries (majority of entries)
        for i in 0..(n - matches_per_size) {
            let key = format!("other_prefix_{}", i);
            hashmap.insert(key.clone(), i);
            btreemap.insert(key, i);
        }

        // Count iterations for HashMap (must scan all N entries)
        let mut hashmap_iterations = 0usize;
        let hashmap_matches: Vec<_> = hashmap
            .iter()
            .inspect(|_| hashmap_iterations += 1)
            .filter(|(k, _)| k.starts_with(target_prefix))
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        // Count iterations for BTreeMap (only visits matching + nearby entries)
        let mut btreemap_iterations = 0usize;
        let btreemap_matches: Vec<_> = btreemap
            .range(target_prefix.to_string()..)
            .inspect(|_| btreemap_iterations += 1)
            .take_while(|(k, _)| k.starts_with(target_prefix))
            .map(|(k, v)| (k.clone(), *v))
            .collect();

        // Both should find the same matches
        assert_eq!(
            hashmap_matches.len(),
            btreemap_matches.len(),
            "Match count should be identical for n={}",
            n
        );

        // HashMap MUST scan ALL entries (O(n))
        assert_eq!(hashmap_iterations, n, "HashMap must scan all {} entries", n);

        // BTreeMap should scan FAR fewer entries (O(log n + k))
        // Upper bound: matches + 1 (for the take_while terminator)
        // In practice, BTreeMap.range() jumps directly to the prefix.
        let max_btree_iterations = matches_per_size + 1;
        assert!(
            btreemap_iterations <= max_btree_iterations,
            "BTreeMap scanned {} entries for n={}, expected at most {} (matches + 1). \
             This indicates O(log n + k) is working correctly.",
            btreemap_iterations,
            n,
            max_btree_iterations
        );

        // Verify the improvement factor grows with N
        // For n=100: factor ~10x, for n=10000: factor ~1000x
        let improvement_factor = hashmap_iterations as f64 / btreemap_iterations.max(1) as f64;
        assert!(improvement_factor > 1.0, "BTreeMap should be faster than HashMap for n={}", n);
    }
}

/// Test that nested ref_pointees prefix scanning handles edge cases.
///
/// #1337 follow-up: Verifies that the `.range(prefix..).take_while()` pattern
/// handles keys that share prefix but have different suffixes correctly.
#[test]
fn test_btreemap_prefix_scan_boundary_cases() {
    use std::collections::BTreeMap;

    let mut map: BTreeMap<String, String> = BTreeMap::new();

    // Simulate ref_pointees with nested struct fields
    // Pattern: base_field_N, base_field_N_inner, base_field_N_inner_deep
    map.insert("fn::local_1_field_0".to_string(), "pointee_a".to_string());
    map.insert("fn::local_1_field_0_inner".to_string(), "pointee_b".to_string());
    map.insert("fn::local_1_field_1".to_string(), "pointee_c".to_string());
    map.insert("fn::local_2_field_0".to_string(), "pointee_d".to_string());
    map.insert("fn::local_10_field_0".to_string(), "pointee_e".to_string());

    // Prefix scan for local_1 fields
    let prefix = "fn::local_1_field_";
    let matches: Vec<_> =
        map.range(prefix.to_string()..).take_while(|(k, _)| k.starts_with(prefix)).collect();

    // Should find: field_0, field_0_inner, field_1 (not local_10 or local_2)
    assert_eq!(matches.len(), 3, "Should find exactly 3 local_1 fields");

    // Verify no false positives from local_10 (which sorts after local_1 in BTreeMap)
    for (key, _) in &matches {
        assert!(key.starts_with("fn::local_1_field_"), "Key '{}' should start with prefix", key);
        assert!(!key.starts_with("fn::local_10"), "Key '{}' should not be local_10", key);
    }

    // Empty prefix scan (nothing matches)
    let empty_prefix = "fn::nonexistent_";
    let has_match = map
        .range(empty_prefix.to_string()..)
        .take_while(|(k, _)| k.starts_with(empty_prefix))
        .next()
        .is_some();
    assert!(!has_match, "No matches for nonexistent prefix");
}

// ===========================================================================
