# Intrinsics

The tables below try to summarize the current support in trust-mc for Rust intrinsics.
We define the level of support similar to how we indicate [Rust feature support](../rust-feature-support.md):
 * **Yes**: The intrinsic is expected to work for covered regression cases. This is not a replacement-quality guarantee for every use.
 * **Partial**: The intrinsic is at least partially supported. We are aware of some issue with it.
 * **No**: The intrinsic is not supported.

In general, code generation for unsupported intrinsics follows the rule
described in [Rust feature support - Code generation for unsupported
features](../rust-feature-support.md#code-generation-for-unsupported-features).

Any intrinsic not appearing in the tables below is considered not supported.
Please [open a feature request](https://github.com/alabsystems/trust-mc/issues/new?assignees=&labels=%5BC%5D+Feature+%2F+Enhancement&template=feature_request.md&title=)
if your code depends on an unsupported intrinsic.

### Compiler intrinsics

Name | Support | Notes |
--- | --- | --- |
abort | Yes | |
add_with_overflow | Yes | |
arith_offset | Yes | |
assert_inhabited | Yes | |
assert_uninit_valid | Yes | |
assert_zero_valid | Yes | |
assume | Yes | |
atomic_and_seqcst | Partial | See [Atomics](#atomics) |
atomic_and_acquire | Partial | See [Atomics](#atomics) |
atomic_and_acqrel | Partial | See [Atomics](#atomics) |
atomic_and_release | Partial | See [Atomics](#atomics) |
atomic_and_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_acqrel_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchg_acqrel_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_acqrel_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchg_acquire_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchg_acquire_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_acquire_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchg_relaxed_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchg_relaxed_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_relaxed_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchg_release_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchg_release_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_release_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchg_seqcst_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchg_seqcst_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchg_seqcst_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acqrel_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acqrel_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acqrel_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acquire_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acquire_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_acquire_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_relaxed_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_relaxed_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_relaxed_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_release_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_release_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_release_seqcst | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_seqcst_acquire | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_seqcst_relaxed | Partial | See [Atomics](#atomics) |
atomic_cxchgweak_seqcst_seqcst | Partial | See [Atomics](#atomics) |
atomic_fence_seqcst | Partial | See [Atomics](#atomics) |
atomic_fence_acquire | Partial | See [Atomics](#atomics) |
atomic_fence_acqrel | Partial | See [Atomics](#atomics) |
atomic_fence_release | Partial | See [Atomics](#atomics) |
atomic_load_seqcst | Partial | See [Atomics](#atomics) |
atomic_load_acquire | Partial | See [Atomics](#atomics) |
atomic_load_relaxed | Partial | See [Atomics](#atomics) |
atomic_load_unordered | Partial | See [Atomics](#atomics) |
atomic_max_seqcst | Partial | See [Atomics](#atomics) |
atomic_max_acquire | Partial | See [Atomics](#atomics) |
atomic_max_acqrel | Partial | See [Atomics](#atomics) |
atomic_max_release | Partial | See [Atomics](#atomics) |
atomic_max_relaxed | Partial | See [Atomics](#atomics) |
atomic_min_seqcst | Partial | See [Atomics](#atomics) |
atomic_min_acquire | Partial | See [Atomics](#atomics) |
atomic_min_acqrel | Partial | See [Atomics](#atomics) |
atomic_min_release | Partial | See [Atomics](#atomics) |
atomic_min_relaxed | Partial | See [Atomics](#atomics) |
atomic_nand_seqcst | Partial | See [Atomics](#atomics) |
atomic_nand_acquire | Partial | See [Atomics](#atomics) |
atomic_nand_acqrel | Partial | See [Atomics](#atomics) |
atomic_nand_release | Partial | See [Atomics](#atomics) |
atomic_nand_relaxed | Partial | See [Atomics](#atomics) |
atomic_or_seqcst | Partial | See [Atomics](#atomics) |
atomic_or_acquire | Partial | See [Atomics](#atomics) |
atomic_or_acqrel | Partial | See [Atomics](#atomics) |
atomic_or_release | Partial | See [Atomics](#atomics) |
atomic_or_relaxed | Partial | See [Atomics](#atomics) |
atomic_singlethreadfence_seqcst | Partial | See [Atomics](#atomics) |
atomic_singlethreadfence_acquire | Partial | See [Atomics](#atomics) |
atomic_singlethreadfence_acqrel | Partial | See [Atomics](#atomics) |
atomic_singlethreadfence_release | Partial | See [Atomics](#atomics) |
atomic_store_seqcst | Partial | See [Atomics](#atomics) |
atomic_store_release | Partial | See [Atomics](#atomics) |
atomic_store_relaxed | Partial | See [Atomics](#atomics) |
atomic_store_unordered | Partial | See [Atomics](#atomics) |
atomic_umax_seqcst | Partial | See [Atomics](#atomics) |
atomic_umax_acquire | Partial | See [Atomics](#atomics) |
atomic_umax_acqrel | Partial | See [Atomics](#atomics) |
atomic_umax_release | Partial | See [Atomics](#atomics) |
atomic_umax_relaxed | Partial | See [Atomics](#atomics) |
atomic_umin_seqcst | Partial | See [Atomics](#atomics) |
atomic_umin_acquire | Partial | See [Atomics](#atomics) |
atomic_umin_acqrel | Partial | See [Atomics](#atomics) |
atomic_umin_release | Partial | See [Atomics](#atomics) |
atomic_umin_relaxed | Partial | See [Atomics](#atomics) |
atomic_xadd_seqcst | Partial | See [Atomics](#atomics) |
atomic_xadd_acquire | Partial | See [Atomics](#atomics) |
atomic_xadd_acqrel | Partial | See [Atomics](#atomics) |
atomic_xadd_release | Partial | See [Atomics](#atomics) |
atomic_xadd_relaxed | Partial | See [Atomics](#atomics) |
atomic_xchg_seqcst | Partial | See [Atomics](#atomics) |
atomic_xchg_acquire | Partial | See [Atomics](#atomics) |
atomic_xchg_acqrel | Partial | See [Atomics](#atomics) |
atomic_xchg_release | Partial | See [Atomics](#atomics) |
atomic_xchg_relaxed | Partial | See [Atomics](#atomics) |
atomic_xor_seqcst | Partial | See [Atomics](#atomics) |
atomic_xor_acquire | Partial | See [Atomics](#atomics) |
atomic_xor_acqrel | Partial | See [Atomics](#atomics) |
atomic_xor_release | Partial | See [Atomics](#atomics) |
atomic_xor_relaxed | Partial | See [Atomics](#atomics) |
atomic_xsub_seqcst | Partial | See [Atomics](#atomics) |
atomic_xsub_acquire | Partial | See [Atomics](#atomics) |
atomic_xsub_acqrel | Partial | See [Atomics](#atomics) |
atomic_xsub_release | Partial | See [Atomics](#atomics) |
atomic_xsub_relaxed | Partial | See [Atomics](#atomics) |
blackbox | Yes | |
bitreverse | Yes | |
breakpoint | Yes | |
bswap | Yes | |
caller_location | No | |
ceilf32 | Yes | |
ceilf64 | Yes | |
copy | Yes | |
copy_nonoverlapping | Yes | |
copysignf32 | Yes | |
copysignf64 | Yes | |
cosf32 | Partial | Results are overapproximated |
cosf64 | Partial | Results are overapproximated |
ctlz | Yes | |
ctlz_nonzero | Yes | |
ctpop | Partial | Supported for covered cases; edge-case proof coverage is incomplete |
cttz | Yes | |
cttz_nonzero | Yes | |
discriminant_value | Yes | |
drop_in_place | No | |
exact_div | Yes | |
exp2f32 | Partial | Results are overapproximated |
exp2f64 | Partial | Results are overapproximated |
expf32 | Partial | Results are overapproximated |
expf64 | Partial | Results are overapproximated |
fabsf32 | Yes | |
fabsf64 | Yes | |
fadd_fast | Yes | |
fdiv_fast | Partial | [#1553](https://github.com/alabsystems/trust-mc/issues/1553) |
float_to_int_unchecked | Yes | |
floorf32 | Yes | |
floorf64 | Yes | |
fmaf32 | Partial | Results are overapproximated |
fmaf64 | Partial | Results are overapproximated |
fmul_fast | Partial | [#1553](https://github.com/alabsystems/trust-mc/issues/1553) |
forget | Yes | |
frem_fast | No | |
fsub_fast | Yes | |
likely | Yes | |
log10f32 | Partial | Results are overapproximated |
log10f64 | Partial | Results are overapproximated |
log2f32 | Partial | Results are overapproximated |
log2f64 | Partial | Results are overapproximated |
logf32 | Partial | Results are overapproximated |
logf64 | Partial | Results are overapproximated |
maxnumf32 | Yes | |
maxnumf64 | Yes | |
align_of | Yes | |
align_of_val | Yes | |
minnumf32 | Yes | |
minnumf64 | Yes | |
move_val_init | No | |
mul_with_overflow | Yes | |
needs_drop | Yes | |
nontemporal_store | No | |
offset | Partial | Doesn't check [all UB conditions](https://doc.rust-lang.org/std/primitive.pointer.html#safety-2) |
powf32 | Partial | Results are overapproximated |
powf64 | Partial | Results are overapproximated |
powif32 | Partial | Results are overapproximated |
powif64 | Partial | Results are overapproximated |
prefetch_read_data | No | |
prefetch_read_instruction | No | |
prefetch_write_data | No | |
prefetch_write_instruction | No | |
ptr_guaranteed_eq | Yes | |
ptr_guaranteed_ne | Yes | |
ptr_offset_from | Partial | Doesn't check [all UB conditions](https://doc.rust-lang.org/std/primitive.pointer.html#safety-4) |
raw_eq | Partial | Cannot detect [uninitialized memory](#uninitialized-memory) |
round_ties_even_f16 | No | |
round_ties_even_f32 | Partial | BMC_SAFE coverage exists, but this is not a proof of full replacement behavior |
round_ties_even_f64 | Partial | BMC_SAFE coverage exists, but this is not a proof of full replacement behavior |
round_ties_even_f128 | No | |
rotate_left | Yes | |
rotate_right | Yes | |
roundf32 | Partial | BMC_SAFE coverage exists, but this is not a proof of full replacement behavior |
roundf64 | Partial | BMC_SAFE coverage exists, but this is not a proof of full replacement behavior |
rustc_peek | No | |
saturating_add | Yes | |
saturating_sub | Yes | |
sinf32 | Partial | Results are overapproximated |
sinf64 | Partial | Results are overapproximated |
size_of | Yes | |
size_of_val | Yes | |
sqrtf32 | Partial | Results are overapproximated |
sqrtf64 | Partial | Results are overapproximated |
sub_with_overflow | Yes | |
transmute | Partial | Doesn't check [all UB conditions](https://doc.rust-lang.org/nomicon/transmutes.html) |
truncf32 | Yes | |
truncf64 | Yes | |
try | No | [#1550](https://github.com/alabsystems/trust-mc/issues/1550) |
type_id | Yes | |
type_name | Yes | |
typed_swap_nonoverlapping | Yes | |
unaligned_volatile_load | No | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
unaligned_volatile_store | No | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
unchecked_add | Yes | |
unchecked_div | Yes | |
unchecked_mul | Yes | |
unchecked_rem | Yes | |
unchecked_shl | Yes | |
unchecked_shr | Yes | |
unchecked_sub | Yes | |
unlikely | Yes | |
unreachable | Yes | |
variant_count | Yes | |
volatile_copy_memory | No | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
volatile_copy_nonoverlapping_memory | No | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
volatile_load | Partial | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
volatile_set_memory | No | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
volatile_store | Partial | See [Notes - Concurrency](../rust-feature-support.md#concurrency) |
wrapping_add | Yes | |
wrapping_mul | Yes | |
wrapping_sub | Yes | |
write_bytes | Yes | |

#### Atomics

All atomic intrinsics are compiled as an atomic block where the operation is
performed. But as noted in [Notes - Concurrency](../rust-feature-support.md#concurrency), trust-mc support for
concurrent verification is limited and not used by default. Verification on code
containing atomic intrinsics should not be trusted given that trust-mc assumes the
code to be sequential.

### Platform intrinsics

Intrinsics from [the `platform_intrinsics` feature](https://rust-lang.github.io/rfcs/1199-simd-infrastructure.html#operations).

Name | Support | Notes |
--- | --- | --- |
`simd_add` | Partial | SIMD coverage is incomplete |
`simd_and`  | Partial | SIMD coverage is incomplete |
`simd_div`  | Partial | SIMD coverage is incomplete |
`simd_eq`  | Partial | SIMD coverage is incomplete |
`simd_extract`  | Partial | SIMD coverage is incomplete |
`simd_ge`  | Partial | SIMD coverage is incomplete |
`simd_gt`  | Partial | SIMD coverage is incomplete |
`simd_insert`  | Partial | SIMD coverage is incomplete |
`simd_le`  | Partial | SIMD coverage is incomplete |
`simd_lt`  | Partial | SIMD coverage is incomplete |
`simd_mul`  | Partial | SIMD coverage is incomplete |
`simd_ne`  | Partial | SIMD coverage is incomplete |
`simd_or`  | Partial | SIMD coverage is incomplete |
`simd_rem`  | Partial | SIMD coverage is incomplete; doesn't check for floating point overflow [#1552](https://github.com/alabsystems/trust-mc/issues/1552) |
`simd_shl`  | Partial | SIMD coverage is incomplete |
`simd_shr`  | Partial | SIMD coverage is incomplete |
`simd_shuffle*`  | Partial | SIMD coverage is incomplete |
`simd_sub`  | Partial | SIMD coverage is incomplete |
`simd_xor`  | Partial | SIMD coverage is incomplete |
