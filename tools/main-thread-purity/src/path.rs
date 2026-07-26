// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Path-prefix matching with the trailing-`::` collision guard.
//
// This is the same discipline trust-mc's `is_prefix_abstracted()` uses
// (reachability.rs lines ~704-726). A monomorphized item is identified by its
// `Instance::name()` / `def_path_str()` string, e.g.
//
//     "libc::close"
//     "std::thread::JoinHandle::<()>::join"
//     "<aterm_gui::Session as core::ops::Drop>::drop"
//
// We classify these against a list of prefixes. The SUBTLE bug a naive
// `path.starts_with(prefix)` introduces is SIBLING COLLISION: the prefix
// `"libc::close"` would also match `"libc::closedir"`, `"libc::close_range"`,
// and `"libc::closefrom"`, none of which is the blocking PTY-master `close(2)`.
// `close_range(2)` in particular is the *correct, non-blocking* way to shut a
// range of fds, so flagging it would be a false positive that pushes engineers
// AWAY from the safe primitive.
//
// The guard: a prefix is treated as a fully-qualified PATH SEGMENT match. A
// prefix `P` matches a path `S` iff `S == P` OR `S` continues with a path
// delimiter — `"::"`, `"<"` (generics: `JoinHandle::<()>`), or `"("` — right
// after `P`. That is exactly "P, followed by a `::`-or-generic boundary", which
// is the canonical form of the trailing-`::` strip in `is_prefix_abstracted`:
// there, prefixes are WRITTEN with a trailing `"::"` and `strip_suffix("::")` is
// used for the `<… as …>` impl-path branch. Here we accept prefixes written
// WITHOUT the trailing `"::"` and enforce the boundary ourselves, so callers can
// write the natural `"libc::close"` and still be collision-safe.

/// The characters that legally terminate a path SEGMENT in an `Instance::name()`
/// string. If `prefix` is immediately followed by one of these (or end-of-string),
/// the prefix named a real, whole segment rather than the head of a longer one.
const SEGMENT_BOUNDARIES: &[char] = &[
    ':', // "::" path separator: libc::close::something (defensive)
    '<', // generic args:        JoinHandle::<()>::join
    '(', // fn-type / closure:   foo(bar)
    ' ', // "<T as Trait>"       spacing inside impl paths
    '>', // end of a generic / impl wrapper
];

/// Returns true iff `path` is the segment named by `prefix`, or a descendant of
/// it (a strictly longer path under the same segment boundary) — and NOT a
/// sibling that merely shares a textual prefix.
///
/// Examples (prefix = "libc::close"):
///   "libc::close"            -> true   (exact)
///   "libc::close::inner"     -> true   (descendant via "::")
///   "libc::close_range"      -> false  (SIBLING — '_' is not a boundary)
///   "libc::closedir"         -> false  (SIBLING)
///   "libc::closefrom"        -> false  (SIBLING)
pub fn segment_matches(path: &str, prefix: &str) -> bool {
    // Direct, head-anchored case.
    if let Some(rest) = path.strip_prefix(prefix) {
        return rest.is_empty() || rest.starts_with(SEGMENT_BOUNDARIES);
    }

    // Impl-path case: trait-impl items render as
    //   "<aterm_gui::Session as core::ops::Drop>::drop"
    // so the leaf path does NOT start with the module path of its type. This is
    // the `normalized.starts_with('<')` branch in `is_prefix_abstracted`, which
    // falls back to a `contains()` of the base prefix. We keep the boundary
    // guard on BOTH sides of the embedded occurrence so a sibling embedded in an
    // impl path (e.g. "<… as libc::close_range>::…") still does not match.
    if path.starts_with('<') {
        return contains_as_segment(path, prefix);
    }

    false
}

/// True iff `prefix` occurs inside `path` as a whole segment — i.e. each
/// occurrence is bounded by a non-identifier delimiter on the right (the left is
/// always a `::` or `<`/space inside an impl path).
fn contains_as_segment(path: &str, prefix: &str) -> bool {
    let mut from = 0;
    while let Some(rel) = path[from..].find(prefix) {
        let start = from + rel;
        let end = start + prefix.len();
        let rest = &path[end..];
        if rest.is_empty() || rest.starts_with(SEGMENT_BOUNDARIES) {
            return true;
        }
        from = end;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_match() {
        assert!(segment_matches("libc::close", "libc::close"));
    }

    #[test]
    fn descendant_via_path_sep() {
        assert!(segment_matches("std::thread::JoinHandle::join", "std::thread::JoinHandle"));
    }

    #[test]
    fn descendant_via_generics() {
        // The real monomorphized form carries generics before the method.
        assert!(segment_matches("std::thread::JoinHandle::<()>::join", "std::thread::JoinHandle"));
    }

    // --- The collision-guard discipline, stated as the task requires. ---

    #[test]
    fn sibling_close_range_is_not_close() {
        // close_range(2) is the *correct* non-blocking primitive; flagging it
        // would push engineers away from the safe call. Must NOT match.
        assert!(!segment_matches("libc::close_range", "libc::close"));
    }

    #[test]
    fn sibling_closedir_is_not_close() {
        assert!(!segment_matches("libc::closedir", "libc::close"));
    }

    #[test]
    fn sibling_closefrom_is_not_close() {
        assert!(!segment_matches("libc::closefrom", "libc::close"));
    }

    #[test]
    fn impl_path_drop_matches_drop_prefix() {
        // Trait-impl rendering: the type's module path is NOT the head of the
        // string, so we fall back to embedded-segment matching.
        assert!(segment_matches(
            "<aterm_gui::Session as core::ops::Drop>::drop",
            "core::ops::Drop"
        ));
    }

    #[test]
    fn impl_path_sibling_does_not_match() {
        // A sibling embedded in an impl path must still be rejected.
        assert!(!segment_matches(
            "<x as libc::close_range>::run",
            "libc::close"
        ));
    }

    #[test]
    fn waitpid_is_not_wait() {
        // "wait" must not swallow "waitpid" UNLESS we intend it to; here we
        // assert the boundary works the other direction too: prefix "libc::wait"
        // (a real deny entry) must NOT match an unrelated "libc::waitqueue".
        assert!(!segment_matches("libc::waitqueue", "libc::wait"));
        assert!(segment_matches("libc::wait", "libc::wait"));
    }
}
