// Oracle: every harness MUST be CERTIFIED OBLIGATION-FREE — zero checks, the
// compiler's certificate, and D16's visible exit-0 verdict
// (`VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)`
// with the proof qualifier `no_checks=compiler_certified_obligation_free`).
//
// WHY THIS FILE EXISTS
//
// `obligation_free_stmt_dual.rs` holds one STATEMENT obligation site per
// harness and must FAIL. Each harness below is the twin of one of those site
// kinds: the same statement shape with nothing to prove. The walk in
// `codegen_ay/obligation_free_walk.rs` must still certify it, and the
// encoders must still emit nothing for it, or the statement rule has widened
// past the encoder's — and every such widening is a Kani-parity cost that
// looks like soundness. `expected/arith-offset-overflow/main.rs` is the
// corpus row the wrapping-offset twin stands for.
//
// A refused twin is INCONCLUSIVE (no checks), exit 1 on a program with
// nothing to prove: the gate scores it `false-failure` /
// `obligation-free-not-certified`. A twin that emits a check is not a twin:
// `unknown` / `obligation-free-twin-has-checks`, and the harness needs
// re-thinking, not the walk.
//
// No `kani::any()` here. Its hook is not one the walk vouches for, and under
// CHC it emits obligations of its own, so a twin that read a symbolic value
// would be refused for a reason unrelated to the statement it stands for.
// Results go through `sink`, a local `#[inline(never)]` function with an
// empty body, so rustc's MIR optimisations cannot remove the statement
// before either the encoder or the walk sees it.

/// Keeps its argument alive through rustc's MIR optimisations. Obligation-free
/// by inspection, and the walk inspects it.
#[inline(never)]
fn sink<T>(_value: T) {}

// Twin of `bug_unchecked_add_overflows` / `bug_unchecked_mul_overflows`:
// wrapping integer arithmetic is a plain `Add` / `Mul` / `Sub` inside core,
// and bit operations are total.
#[kani::proof]
fn safe_wrapping_arithmetic() {
    let a: u32 = 7;
    let r = a.wrapping_add(u32::MAX).wrapping_mul(3).wrapping_sub(1);
    sink(r ^ (a & 5 | a));
}

// Twin of `bug_offset_leaves_the_object`: the WRAPPING offset is
// `arith_offset`, which is legal out of bounds and emits no obligation.
#[kani::proof]
fn safe_wrapping_pointer_offset() {
    let a = [1u32, 2];
    let p: *const u32 = a.as_ptr();
    sink(p.wrapping_add(5));
}

// Twin of `bug_raw_read_through_null` / `bug_raw_write_through_null`: a
// dereference through a REFERENCE is valid by construction.
#[kani::proof]
fn safe_reference_deref() {
    let x = 5u32;
    let mut y = 6u32;
    let r = &x;
    let m = &mut y;
    *m = *r;
    sink(*r);
    sink(*m);
}

// Twin of the signed `Neg` site (refused at the unit level, where
// `-C overflow-checks=off` isolates it): `wrapping_neg` is `0.wrapping_sub(x)`
// inside core, a plain `Sub`.
#[kani::proof]
fn safe_wrapping_negation() {
    let x: i32 = i32::MIN;
    sink(x.wrapping_neg());
}

// Twin of the `Index` site: a `ConstantIndex` projection from a slice
// pattern, which rustc has already checked, and `Len` through a reference.
// (A `rest @ ..` binding — `Subslice` on an array — is not here: the BMC
// encoder demotes it as `unconstrained_assignment` and the CHC lane emits
// two checks for it, so it is not a zero-check twin in either lane.)
#[kani::proof]
fn safe_pattern_index() {
    let v = [1u32, 2, 3];
    let [first, _, last] = v;
    let s: &[u32] = &v;
    sink(first ^ last ^ s.len() as u32);
}

// Twin of `bug_dyn_pointer_comparison`: comparing THIN pointers is a pure
// function of their addresses.
#[kani::proof]
fn safe_thin_pointer_comparison() {
    let x = 1u32;
    let p: *const u32 = &x;
    let q: *const u32 = &x;
    sink(p == q);
}

// Twin of the transmute / float-cast sites (fail-closed at the unit level):
// integer and pointer-to-address casts have nothing to prove.
#[kani::proof]
fn safe_integer_casts() {
    let x = 300u32;
    let p: *const u32 = &x;
    sink((x as u8, x as i64, p as usize));
}

// Twin of the unchecked-arithmetic sites from the other side: a
// `CheckedBinaryOp` whose overflow flag nobody asserts on proves nothing and
// needs nothing.
#[kani::proof]
fn safe_unasserted_overflow_flag() {
    let a = 7u32;
    sink(a.overflowing_add(u32::MAX));
}
