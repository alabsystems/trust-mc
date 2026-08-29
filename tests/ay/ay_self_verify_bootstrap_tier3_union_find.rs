// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
// kani-expect: UNKNOWN
// kani-expect: ay_euf_find_in_bounds=PROOF

//! AY self-verification bootstrap Tier 3a: Union-Find harnesses from ay-theories/euf.
//!
//! These harnesses verify the Union-Find data structure that forms the backbone
//! of ay's EUF (Equality with Uninterpreted Functions) theory solver. The
//! Union-Find implements union-by-rank without path compression.
//!
//! Ported from `ay-theories/euf/src/types.rs` and `ay-theories/euf/src/verification.rs`.
//! Flat-scalar encoding: Vec replaced with fixed-capacity arrays.
//! Loop-free find: while-loop replaced with explicit unrolled steps to avoid
//! Spacer invariant synthesis (max 3 hops for N=4).
//!
//! Part of #3766: Run AY's 258 Kani harnesses through trust_mc.

const N: usize = 4;

/// Standalone mirror of ay's Union-Find with union-by-rank.
/// Fixed-size arrays, no path compression.
struct UnionFind {
    parent: [u32; N],
    rank: [u32; N],
    size: usize,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self { parent: [0, 1, 2, 3], rank: [0; N], size: n }
    }

    /// Element-by-element reset avoids array-literal field assignment encoding
    /// gap in CHC (full `self.parent = [0,1,2,3]` produces Genuine CTREX).
    fn reset(&mut self) {
        self.parent[0] = 0;
        self.parent[1] = 1;
        self.parent[2] = 2;
        self.parent[3] = 3;
        self.rank[0] = 0;
        self.rank[1] = 0;
        self.rank[2] = 0;
        self.rank[3] = 0;
    }

    fn ensure_size(&mut self, n: usize) {
        if n > self.size && n <= N {
            self.size = n;
        }
    }

    /// Loop-free find: unrolled to max 3 hops (sufficient for N=4).
    /// Avoids while-loop that requires Spacer invariant synthesis.
    fn find(&self, x: u32) -> u32 {
        let mut curr = x;
        // Hop 1
        let next = self.parent[curr as usize];
        if next == curr {
            return curr;
        }
        curr = next;
        // Hop 2
        let next = self.parent[curr as usize];
        if next == curr {
            return curr;
        }
        curr = next;
        // Hop 3 (max depth for N=4 with union-by-rank)
        let next = self.parent[curr as usize];
        if next == curr {
            return curr;
        }
        next
    }

    fn union(&mut self, x: u32, y: u32) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx != ry {
            let rx_rank = self.rank[rx as usize];
            let ry_rank = self.rank[ry as usize];
            if rx_rank < ry_rank {
                self.parent[rx as usize] = ry;
            } else if rx_rank > ry_rank {
                self.parent[ry as usize] = rx;
            } else {
                self.parent[ry as usize] = rx;
                self.rank[rx as usize] = rx_rank + 1;
            }
        }
    }
}

// ============================================================
// ay-theories/euf — Union-Find correctness
// ============================================================

/// Port of ay::euf::proof_union_makes_equivalent (reduced to n=4)
#[kani::proof]
fn ay_euf_union_makes_equivalent() {
    let mut uf = UnionFind::new(4);

    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(x < 4 && y < 4);

    uf.union(x, y);

    let rx = uf.find(x);
    let ry = uf.find(y);
    assert!(rx == ry, "After union, find(x) must equal find(y)");
}

/// Port of ay::euf::proof_find_idempotent (reduced to n=4)
#[kani::proof]
fn ay_euf_find_idempotent() {
    let uf = UnionFind::new(4);

    let x: u32 = kani::any();
    kani::assume(x < 4);

    let r1 = uf.find(x);
    let r2 = uf.find(r1);
    assert!(r1 == r2, "find must be idempotent");
}

/// Port of ay::euf::proof_find_in_bounds (reduced to n=4)
#[kani::proof]
fn ay_euf_find_in_bounds() {
    let uf = UnionFind::new(4);

    let x: u32 = kani::any();
    kani::assume(x < 4);

    let r = uf.find(x);
    assert!(r < 4, "find must return a valid index");
}

/// Port of ay::euf::proof_union_transitive (reduced to n=4)
#[kani::proof]
fn ay_euf_union_transitive() {
    let mut uf = UnionFind::new(4);

    let x: u32 = kani::any();
    let y: u32 = kani::any();
    let z: u32 = kani::any();
    kani::assume(x < 4 && y < 4 && z < 4);

    uf.union(x, y);
    uf.union(y, z);

    let rx = uf.find(x);
    let rz = uf.find(z);
    assert!(rx == rz, "Union must be transitive");
}

/// Port of ay::euf::proof_reset_restores_identity (reduced to n=4)
#[kani::proof]
fn ay_euf_reset_restores_identity() {
    let mut uf = UnionFind::new(4);

    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(x < 4 && y < 4 && x != y);

    uf.union(x, y);
    assert!(uf.find(x) == uf.find(y));

    uf.reset();

    let rx = uf.find(x);
    let ry = uf.find(y);
    assert!(rx == x, "After reset, find(x) == x");
    assert!(ry == y, "After reset, find(y) == y");
}

/// Port of ay::euf::proof_ensure_size_preserves_structure
#[kani::proof]
fn ay_euf_ensure_size_preserves_structure() {
    let mut uf = UnionFind::new(2);

    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(x < 2 && y < 2);

    uf.union(x, y);
    let rep_before = uf.find(x);

    uf.ensure_size(4);

    let rep_after = uf.find(x);
    assert!(rep_before == rep_after, "ensure_size must preserve structure");

    let new_elem: u32 = kani::any();
    kani::assume(new_elem >= 2 && new_elem < 4);
    assert!(uf.find(new_elem) == new_elem, "New elements are self-representative");
}

/// Port of ay::euf::proof_rank_bounded (reduced to n=4)
#[kani::proof]
fn ay_euf_rank_bounded() {
    let mut uf = UnionFind::new(4);

    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let c: u32 = kani::any();
    kani::assume(a < 4 && b < 4 && c < 4);

    uf.union(a, b);
    uf.union(b, c);

    // For n=4, max rank is 2 (log2(4))
    assert!(uf.rank[0] <= 2, "Rank must be bounded by log2(n)");
    assert!(uf.rank[1] <= 2, "Rank must be bounded by log2(n)");
    assert!(uf.rank[2] <= 2, "Rank must be bounded by log2(n)");
    assert!(uf.rank[3] <= 2, "Rank must be bounded by log2(n)");
}

/// Union-Find symmetry — union(x,y) and union(y,x) produce same equivalence
#[kani::proof]
fn ay_euf_union_symmetric() {
    let x: u32 = kani::any();
    let y: u32 = kani::any();
    kani::assume(x < 2 && y < 2);

    let mut uf1 = UnionFind::new(2);
    uf1.union(x, y);

    let mut uf2 = UnionFind::new(2);
    uf2.union(y, x);

    // Both should produce equivalent classes
    assert!(uf1.find(x) == uf1.find(y));
    assert!(uf2.find(x) == uf2.find(y));
}
