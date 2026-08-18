// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Provenance newtypes: is this `Expr` an ADDRESS or a VALUE?
//!
//! # Why this module exists
//!
//! In `codegen_ay` an [`Expr`] is a bare bitvector. Nothing in the type
//! distinguishes `0x1000` *the address of a local* from `0x1000` *the integer
//! stored in that local*. The two are structurally identical once the producer
//! has returned, so roughly 270 sites across `codegen_ay` re-derive the answer
//! from heuristics:
//!
//! - pointer-width checks ("this is 64 bits wide, so it is probably a pointer"),
//! - deref-identity tests ("dereferencing it yields the same sort, so it must
//!   have been an address"),
//! - address recovery ("walk back to the place expression and re-synthesize the
//!   address we should have been handed in the first place").
//!
//! Every one of those is a guess. The fact being guessed at is *known at the
//! PRODUCER* — the site that built the expression knew perfectly well whether it
//! was emitting a location or a loaded datum — and is lost before the CONSUMER
//! ever sees it. [`Val`] and [`Loc`] carry that fact across the gap instead of
//! forcing each consumer to reconstruct it.
//!
//! # Why it matters
//!
//! This ambiguity is the shared root of two otherwise unrelated-looking failure
//! classes:
//!
//! - **False positives.** A consumer that reads an address as a value (or vice
//!   versa) constrains the wrong term, so the solver reports a counterexample
//!   for a program that is in fact correct.
//! - **Fabricated proofs.** The same confusion in the other direction drops or
//!   misaligns a constraint, and the model checker "proves" an assertion that is
//!   actually violated. The slot-misalignment defects are instances of this.
//!
//! Single-site fixes have measured **0 wins out of 5 attempts**. That is not bad
//! luck: patching one heuristic does not add the missing fact, it only moves
//! which consumer guesses wrong. The fact has to be carried structurally, which
//! is what these types do.
//!
//! # The rule
//!
//! [`Val`] and [`Loc`] are distinct types and there is no `From` impl, no
//! `Deref`, and no blanket conversion between them. The **only** legal crossings
//! are the two operations that genuinely change what an expression denotes:
//!
//! - **load**: `Loc` -> `Val` — read the storage the address points at.
//! - **address-of**: place -> `Loc` — take the address of a place.
//!
//! Anything else that turns one into the other is the bug this module exists to
//! prevent. Both wrappers are `#[repr(transparent)]` around [`Expr`], so the
//! distinction costs nothing at run time; it exists purely for the type checker.
//!
//! # Status
//!
//! Wave 1 ("values misgated on pointer width") is converted: the iterator
//! `has_remaining` predicate, the Vec dangling-provenance constraints, the
//! offset count-fold, the `Layout::dangling` construction and the closure
//! capture bridge now carry [`Val`] / [`Loc`] instead of re-deriving provenance
//! from a width test.
//!
//! Wave 2 ("single-caller address recovery") establishes the `-> Option<Loc>`
//! return idiom on the encoder's address-recovery producers:
//! `normalize_deref_address_expr`, `deref_addr_via_ref_target_recovery`,
//! `recover_unsafe_cell_referent_address`, `recover_cell_referent_address` and
//! `normalize_kani_mem_pointer_expr`, plus the `Cell`/`RefCell` load/store
//! emitters that consume them. Two address-recovery width re-tests were deleted
//! outright, having been proven redundant against the new
//! `translate_ref_to_address` ENSURES clause.
//!
//! Wave 4 ("fat-pointer consumers") retires the width tests that *read* a
//! double-width bitvector as a `(data, metadata)` pair. `extract_pointer_storage_expr`
//! now returns [`Loc`], `extract_embedded_vtable_expr` returns [`Val`], the two
//! raw-pointer component decoders return `(Loc, Option<Val>)`, and the Box /
//! Rc / Arc drop paths take the address half from a decode instead of a width
//! coincidence. See `ptr_repr.rs` for what the metadata half now refuses to
//! fabricate.
//!
//! Wave 5 ("transparent-wrapper / deref-identity") types the datatype field
//! projection pair. `ChcCtx::datatype_field_select` now takes and returns
//! [`Val`], and `ChcCtx::datatype_field_update` takes a [`Val`] container and a
//! [`Val`] replacement, which pins down what the `NonNull`/`Unique`/`Box`
//! passthrough actually hands back: the pointer **datum** held by the wrapper,
//! never an address of storage. The four copies of the width test that decided
//! "is this bv the flattened form of a transparent wrapper?" now call the one
//! documented [`is_transparent_pointer_wrapper_repr`] below, so the read side
//! and the write side can no longer drift apart and write the wrong slot.
//!
//! Wave 6 ("inline place resolution") types what the inline body walker does
//! with a `Deref`-rooted place. `inline_ref_place_to_expr` now returns
//! [`crate::codegen_ay::chc::call::inline_shared::place::InlineRefExpr`], which
//! separates the lane that genuinely *mints* an address (base pointer plus the
//! projection's byte offsets) from the lane that hands the referenced place's
//! own term straight back because references are transparent in this encoding.
//! The walker's three load sites decide "is this term an address?" from the MIR
//! type — a raw-pointer deref, or a datatype-shaped pointee under a bare
//! pointer-width term — and then ask `PtrRepr::thin_address` only for the
//! *shape*. [`MaybeLoc`] below closes the receiver-acceptance half.
//!
//! Wave 7 ("fail-open obligation gates") is the soundness wave: every site it
//! touches *dropped an obligation* when a width test missed, which is the exact
//! shape a fabricated proof is made of. `emit_offset_overflow_check` now takes
//! `(&Loc, &Val)` — two adjacent operands, one address and one value, that were
//! trivially swappable as bare `Expr`s — and the `RawVec` datatype is built
//! through one `(Loc, Val)` constructor instead of two anonymous slots in a
//! `Vec<Expr>`. Four obligations stopped being gated on a width coincidence and
//! are now gated on whether an address could be *decoded* at all: the raw-ptr
//! deref `use_after_free_check`, the offset path's `pointer_invalid`, the CHC
//! `obj_valid` check (which tested a hard-coded `64`, not even `POINTER_WIDTH`),
//! and the `refused_ptr_widening` veto, which now asks `PtrRepr` for a pointer
//! *shape* rather than testing one direction of the width mismatch.
//!
//! Wave 8 ("static / const allocation decoding") is the one wave where the
//! missing fact was never actually missing. A `rustc_public` `Allocation`
//! carries `provenance.ptrs` — a table naming exactly which byte offsets of an
//! initializer image hold pointers — and the decoder ignored it in favour of
//! `width == POINTER_WIDTH`. `read_scalar_from_allocation` now returns an
//! `AllocScalar` whose tag comes from that table, `read_pointer_like_from_allocation`
//! returns one too, and the addresses minted for referent objects
//! (`resolve_pointer_static_init`, `resolve_static_target_init_expr`,
//! `alloc_dst_pointer_fallback`, the `fn` pointer identity) are [`Loc`] from the
//! point of minting. The typed-memory mirror's `(value, address)` pair —
//! `register_static_memory_init_entries` and `push_static_memory_init_entry` —
//! is the wave-13 shape in miniature and now takes `(Val, Loc)`. The four
//! remaining thin/fat width comparisons collapsed into
//! [`crate::codegen_ay::ptr_repr::PtrSlot`], a classification of the *declared
//! sort* rather than of a term, and both packing sites go through
//! [`crate::codegen_ay::ptr_repr::PtrRepr::into_packed`] so the
//! `[metadata | data]` order is stated once.
//!
//! Wave 9 ("known-call and stub pointer receivers") types the slice/subslice
//! address pipeline and the atomic receiver pair. `resolve_subslice_source_addr`
//! returns [`Loc`] and its thin/fat width partition collapsed into one total
//! `PtrRepr::into_data`; `SubsliceMaterialization::fresh_addr` and the
//! `subslice_addr_cache` carry [`Loc`] end to end, which let
//! `emit_subslice_destination` stop re-measuring the width of its own
//! allocation and pack through [`crate::codegen_ay::ptr_repr::PtrRepr::into_packed`].
//! `ResolvedSliceBacking`'s three fields became [`Val`], stating that a resolved
//! slice backing is element storage, a count and an index — never an address —
//! and that the `Loc -> Val` crossing happens once, at the load inside the
//! resolver. `emit_atomic_mem_store_transition` takes `(Val, MaybeLoc)` instead
//! of two adjacent transposable `Expr`s, and `atomic_load_from_memory` returns
//! [`Val`]. Four more width-as-provenance tests (`ptr::is_null`,
//! `slice::as_ptr`, the `Vec::len` memory fallback, the nested-call havoc)
//! now ask `PtrRepr`/`PtrSlot` for a *shape* while the callee signature or the
//! MIR type supplies the provenance.
//!
//! Two Wave 9 sites are deliberately NOT converted, because no type decides
//! them: `codegen_call_atomic.rs`'s load partition (§4 item 1 — an
//! `AtomicUsize` holds a pointer or an integer depending on run-time history,
//! which needs an `AtomicCell` tag written by the last store) and
//! `nested_call_fallback.rs`'s pointer-shaped havoc (§4 item 6 — an unmodelled
//! call's return provenance is genuinely unknown and must fail closed, which is
//! a coverage change). Both are annotated in place.
//!
//! Wave 11 ("address producers") types the two functions that MINT addresses,
//! so every downstream tag is now inherited rather than re-derived.
//! `ChcCtx::translate_ref_to_address` — address-of on a MIR `Place` — returns
//! [`Loc`], and so does `dyn_coercion::extract_pointer_expr`, which peels a
//! declared `fld_ptr` role off a pointer-wrapper datatype. Between them they
//! feed ~56 call sites, and the wave added no tag anywhere else: the six
//! `Loc::of_address` calls it introduces are the two producers' own return
//! points, a promoted constant's `concat(obj_id, 0)` allocation base, and one
//! byte-offset arithmetic result on an address, while four re-tags at consumers
//! were deleted outright. `ChcCtx::slice_as_ptr_data_expr` came along as a
//! derived producer — all four of its lanes were already addresses.
//!
//! The width test this retires by construction is the one at
//! `modifies_frame_ref_store_check`, which re-read a 128-bit
//! `translate_ref_to_address` result as a fat pointer and took its low half.
//! That branch was unreachable: the producer's ENSURES (allocation base
//! `concat(bv32, bv32)`, deref lanes normalized through
//! `normalize_deref_address_expr`, width-preserving `bvadd` projections) makes
//! every result exactly [`POINTER_WIDTH`], which is now stated in the type.
//!
//! What Wave 11 explicitly does NOT fix is `extract_pointer_expr`'s ≤ 4-field
//! fallback — "the first pointer-width field of a small datatype is the
//! pointer". The datatype declaration carries no field roles, so no type on
//! that function can decide it; it needs the field-role table of §4 item 7,
//! the same keystone as the slot-layout authority. It is annotated in place.
//! (Wave 18 built that table and deleted the fallback — see below.)
//!
//! Wave 12 ("keystone A: the load") types the encoder's ONLY legal `Loc -> Val`
//! crossing. `ChcCtx::load_from_memory` now reads `Loc -> Option<Val>`, and
//! `ptr_receiver_mem::load_from_memory` — the second definition, the receiver
//! side — reads `&MaybeLoc -> Option<Val>`, which is what its callers actually
//! know: two of them already held a `MaybeLoc` and were unwrapping it with
//! `as_addr_expr` on the way in, while the other two hand over a translated
//! call argument or byte arithmetic on a bare parameter and now say
//! [`MaybeLoc::Unknown`] out loud. The `Deref` arm of the projection walker
//! mints its address exactly once, from the MIR type (`deref_pointee_ty` has
//! just succeeded, so the term is a pointer's own term), and threads that one
//! `Loc` through the provenance bound checks, the field-offset byte arithmetic
//! and the whole-struct load, which previously each re-derived it.
//!
//! Wave 13 ("keystone B: the store") types the address half of
//! `ChcCtx::build_memory_store`. The two leading parameters were adjacent,
//! same-typed, bare `Expr`s — one an address, one a datum — which is the
//! canonical shape of the slot-misalignment defect class, and transposing them
//! type-checked. **Only one of the two has to be typed for the swap to become a
//! compile error**, which is why the value slot deliberately stays an `Expr`:
//! tagging it `Val::of_value` at every call site would always "be right" (a
//! store's value operand is a value by role, whatever bit pattern it carries)
//! and would therefore teach the type system nothing — the tag would be
//! asserted by the store instead of carried from whatever produced the datum.
//! The value side becomes honest when the value producers return [`Val`].
//!
//! Wave 13b ("the laundering audit") asked one question of every tag the
//! preceding waves introduced: **does the surrounding code actually establish
//! what the tag asserts?** A tag that does not is strictly worse than the width
//! test it replaced — it moves the guess *inside* the type system, so the
//! refactor looks finished while every bug survives. Ten sites failed, all of
//! the same two shapes: a tag applied to a COERCED term (`coerce_to_ptr_width`
//! substitutes the literal `FALLBACK_PTR` for non-bitvec sorts and zero-extends
//! narrow ones; `coerce_bitvec_width_safe` does the same widening), and a tag
//! applied on the failure arm of a decoder that had just declined to recognize
//! the term (`PtrRepr::classify(..).map_or_else(|| Loc::of_address(x), ..)`, on
//! two paths that go on to FREE whatever the tag names).
//!
//! The two worst were `ptr::offset`'s base pointer in
//! `statement/dispatch/ptr_arithmetic.rs`, whose comment claimed the MIR type
//! had been checked for `RawPtr`/`Ref` "above" when the `match` had a `_ => 1`
//! arm and an `else { 1 }` arm and nothing bailed. The tagged term fed
//! `PtrRepr::classify` and `heap_is_allocated` for the `pointer_invalid`
//! obligation, i.e. exactly the `is_value_widened_into_address` fabrication
//! [`is_value_widened_into_address`] refuses by name one module over. Each site
//! now either establishes the fact (the MIR type is *required*, and the address
//! is decoded structurally from the UNCOERCED term) or fails closed through the
//! demotion counter. `docs/addr-vs-value-conversion-queue.md` §3 wave 13b
//! records the full table, including the two sites that were examined and kept.
//!
//! Wave 14 ("the MIR type already knew") adds the second original source of the
//! fact, [`mir_ty_denotes_address`]: a local's Rust type decides outright
//! whether its CHC term is a pointer, and three width heuristics were guessing
//! at something `translate_adt_ty` had already settled. The inline drop walker
//! no longer hands an opaque `ptr_sort()` ADT — a `Cow`, an `Alignment`, a
//! `Drain`, any of the dozen iterator adapters, or a plain `usize` — to drop
//! glue as its `&mut Self`; the CHC slice-index pointer arm is now selected by
//! provenance carried from the one resolution lane that can stop at a pointer,
//! instead of being the `match`'s width-shaped fallback; and
//! `ChcCtx::load_ptr_from_memory` returns [`MaybeLoc`], which separates its
//! typed-array select (an address by the memory model's own construction) from
//! its store-to-load forwarding lane (the last datum stored at that address,
//! under a key shared by every type array). The nested-closure capture peeler
//! stops asking "is this pointer-width?" and asks the question that is actually
//! decidable — "could this be the referent's own value?" — which is what made
//! it walk past the answer for a `&usize` capture.
//!
//! Wave 14 also leaves two sites ALONE with their guards intact, and that is
//! the honest outcome rather than an unfinished one:
//! `fn_trait_dispatch::resolve_mut_ref_value_args` (the arg arrives from
//! `translate_operand_with_modified`, the same wall the `*_untyped` shims are
//! parked against) and `projected_assign::inline_deref_target_addr` (the MIR
//! premise is real but #3980 overwrites the term it describes, so the fix is
//! walker plumbing, not a tag). Both say so in place.
//!
//! Wave 15 ("the two laundered tags") closes the two sites the wave-13b audit
//! found and wave 14 left open — the ones where the tag asserted more than the
//! code established, i.e. where the retyping had made a pre-existing guess look
//! finished. Neither was re-tagged; both were fixed at the guess.
//!
//! * `codegen_call_dispatch_dyn::extract_pointer_storage_expr`'s fallback tagged
//!   a datatype's FIRST field as an address whenever that field was any
//!   bitvector — not even [`POINTER_WIDTH`]. Its precondition is what condemns
//!   it: it ran EXACTLY when `extract_pointer_expr` had declined, i.e. on a
//!   datatype with no declared `fld_ptr` and more than four fields — the shape
//!   the `<= 4` bound exists to refuse, and the shape of #4099 (`DtSolver`'s
//!   `fld_scope_len` as a base address). DELETED. Restricting it to
//!   pointer-width fields would only have produced dead code that
//!   `extract_pointer_expr`'s own `<= 4` lane already claims. `None` routes
//!   every caller to a lane it already had, and the one caller that had been
//!   relying on the guess (`resolve_chained_box_deref_ptr`) now supplies its own
//!   fallback from the MIR type it had already matched (`Box`/`Unique`/`NonNull`)
//!   plus a representation check.
//! * `dyn_coercion::extract_pointer_expr`'s already-thin lane tagged EVERY
//!   bitvector as an address, which is why roughly ten callers using
//!   `extract_pointer_expr(..).is_some()` as a pointer TEST were being told
//!   "yes" for `bv1`, `bv8` and `bv32` terms alike. The lane now admits only the
//!   two shapes an address can have ([`crate::codegen_ay::ptr_repr::PtrSlot`])
//!   and refuses [`is_value_widened_into_address`]; the provenance itself is
//!   stated as PROPAGATED, on the same contract
//!   [`crate::codegen_ay::ptr_repr::PtrRepr::classify`] already carries, with
//!   the callers that supply it named. Callers that drop the tag are unaffected
//!   (`.unwrap_or(expr)` returns the same term either way); callers that keep it
//!   fail closed instead of receiving a fabricated address.
//!
//! Wave 15 also resolved the four self-labelled UNCLEAR sites, one per
//! disposition:
//!
//! * `codegen_call_cell::recover_cell_referent_address` — ESTABLISH. Its doc had
//!   always *claimed* the operand was "address-BY-TYPE" and nothing checked it;
//!   [`mir_ty_denotes_address`] is now required, which together with the
//!   pre-existing `T`-narrower-than-pointer gate excludes both known ways this
//!   path can be handed a non-address.
//! * `codegen_call_unsafe_cell`'s store-to-load FORWARDING lane — ESTABLISH.
//!   `store_forward_map` now records the type key each store wrote through, so
//!   `load_ptr_from_memory` answers `Known` on a key match (the typed-array
//!   argument) and `Unknown` on a mismatch — which is exactly the
//!   `u64`-read-as-an-address case, and now fails closed instead of passing a
//!   width test. The wave-13 decision to leave the store's VALUE operand untyped
//!   is untouched: what is recorded is the declared type of the store.
//! * `projected_assign::inline_deref_target_addr` — PROPAGATE, partially. The
//!   pointee type its three callers already held is now passed in, and a
//!   non-pointer-width pointee proves the #3980 value substitution cannot have
//!   produced this term. The pointer-width-pointee case remains an UNRESOLVED
//!   WALL, labelled in place; refusing it is not the safe direction (the
//!   functional lane loses the write just as silently), so the fix stays walker
//!   plumbing and the behaviour is unchanged.
//! * `fn_trait_dispatch::resolve_mut_ref_value_args` — RETREAT, kept. There is
//!   still no producer to thread a tag from, and it mints no [`Loc`]; it now
//!   cross-references the consumer that shares its discriminator so the two
//!   halves of #3980 cannot drift.
//!
//! Wave 16 ("what the census could and could not see") is two halves, and the
//! second half matters more than the first.
//!
//! **The census residual.** Every one of the 53 remaining census hits was read
//! and classified. Only twelve were genuine address-vs-value guards; the rest
//! are comments describing guards earlier waves retired, the two sanctioned
//! predicates themselves, or tests that were never about provenance (`bool`
//! vs `bv1` sort unification, `bv8` region element sorts, an enum discriminant
//! byte, the packed `Layout` `bv128`, a `char`'s 32 bits, the split-pointer's
//! own `concat(bv32, bv32)` halves). Eight of the twelve were retired here, all
//! by funnelling an inline copy into the one documented classification:
//!
//! * four more copies of "was a transparent wrapper flattened to this bv?" —
//!   the `Field` and `Downcast` arms of `statement/place_projection.rs` and the
//!   two `flattened_tuples` / `local_N_field_K` arms of `statement/place.rs` —
//!   now call [`is_transparent_pointer_wrapper_repr`], joining the four the
//!   wave-5 sweep found. Six of the eight known copies live on the read side,
//!   which is exactly how a read/write pair drifts;
//! * four declared-slot width tests became
//!   [`crate::codegen_ay::ptr_repr::PtrSlot`] queries: the inline drop walker's
//!   `fld_ptr` arm (whose sibling two lines up already asked `PtrSlot`),
//!   `NonNull::from_raw_parts`' destination, the `Cell` referent recovery's
//!   shape filter, and `refused_ptr_widening`'s leading term. All four ask
//!   about a *sort*, which nothing widens, and none of them decides provenance.
//!
//! None of the eight changes behaviour — each replaced predicate is the
//! substituted one's literal body — and that is the point: what they buy is
//! that the next edit to the shared predicate reaches every copy.
//!
//! **What the census cannot see.** The tracked `rg` counts one spelling. The
//! fabrication this module exists to prevent is usually written in another:
//! `expr.extract(127, 64)` guarded by a width test, i.e. *reading the high half
//! of a double-width term as metadata*. Wave 4 converted six such sites and the
//! sweep was believed complete; four more were found here, three of them added
//! **after** wave 4 landed. Each read a
//! [`crate::codegen_ay::ptr_repr::PtrRepr`] `WidenedThin` term's extension
//! padding as a value the program had computed:
//!
//! * `codegen_call_virtual_inline/pointer_wrapper.rs` handed the padding back
//!   as a **vtable id**, pinning dynamic dispatch to whichever candidate holds
//!   it — the identical defect wave 4 fixed one function over;
//! * `inline_shared/rvalue_ptr.rs`'s `PtrMetadata` returned it as a **length**,
//!   which for a zero-extension is `0` and makes every bounds obligation over
//!   it trivially satisfiable;
//! * `inline_shared/place.rs`'s `Field(1)` on a pointer-typed place returned it
//!   as the pointer's metadata half;
//! * `codegen_call_cmp_ord.rs` (#4131) **ordered** two wide pointers on it,
//!   the third copy of the defect the `raw_pointer_*_components` decoders and
//!   `try_translate_inline_wide_pointer_binop` already had fixed.
//!
//! All four now ask `PtrRepr`, which yields metadata for a genuine `Fat` only;
//! each declines into a lane it already had (the vtable-id-from-type lane, the
//! `fld_len` / `translate_ptr_metadata` producers, the walker's bail-closed
//! lane, the caller's generic comparison). `Field(0)` and the data lane are
//! untouched — [`crate::codegen_ay::ptr_repr::PtrRepr::data`] is total.
//!
//! **Two of this class were examined and deliberately left standing**, and the
//! reason is the honest one rather than an oversight: the shadow-memory
//! `fat_len` decoders, `statement/kani_shadow_mem.rs::shadow_mem_ptr` and its
//! CHC twin `codegen_call_kani_model_mem_init.rs::mem_init_ptr`, both read the
//! high half as a slice length off a bare width test. Refusing is not the safe
//! direction at either: the BMC one fails CLOSED, so a refusal flips every
//! harness that reaches it to `FAILED`, and the CHC one fails OPEN by stated
//! policy, so a refusal blesses the tracked byte instead. Both are coverage
//! changes that have to be measured against the burndown — the same reason
//! [`MaybeLoc::Unknown`] is still permissive — and both now say so in place.
//!
//! The four census guards that remain genuine are all previously-annotated
//! walls, unchanged: the `raw_eq` `Unreported` lane, `extract_pointer_expr`'s
//! `<= 4`-field fallback (closed by wave 18), the `AtomicUsize` load partition,
//! and `resolve_mut_ref_value_args`.
//!
//! Wave 17 ("the last laundered tag") closes the one direct `Val -> Loc`
//! unwrap left in the encoder, in the static/const decoder wave 8 built.
//!
//! `codegen_decl_static_alloc::read_pointer_like_from_allocation`'s
//! unresolved-relocation fallback read the slot at the *declared* sort width and
//! then re-tagged whatever came back:
//!
//! ```text
//! Some(AllocScalar::Value(val)) => Loc::of_address(val.into_expr()),
//! None                          => Loc::of_address(bitvec_const(0, width)),
//! ```
//!
//! Its reachability is what condemned it. The branch runs only after the
//! provenance table has already answered "yes, a pointer starts here", so
//! `read_scalar_from_allocation` can reach its `Value` arm for exactly one
//! reason: its own filter found that the read does not COVER the pointer slot —
//! the case its doc describes as "a byte of a pointer, which is a datum and not
//! an address". The tag therefore asserted the negation of the contract it read
//! through. For the shape that actually triggers it, a fat-pointer slot, the
//! fabricated address was the whole `2 * POINTER_WIDTH` packed word, handed to
//! `PtrRepr::from_declared_roles` as the *data* half — which would then pack a
//! 192-bit "pointer" out of a 128-bit data half and a 64-bit metadata half. The
//! `None` arm fabricated a null address out of a truncated initializer image.
//!
//! Fixed by ESTABLISHING, not re-tagging. `unresolved_relocation_address` asks
//! for exactly the pointer slot — `POINTER_WIDTH` bits at the relocation's own
//! offset, the same slot the metadata read skips past — so the provenance table
//! can confirm the read covers a pointer and hand back a `Ptr`; the address is
//! then inherited from that reader rather than minted here. Nothing else can
//! produce a `Loc` on this path: a `Value` answer and a byte-range failure both
//! return `None`, which routes the static to the `static_init_incomplete`
//! demotion — an unconstrained initial value, already audited as a sound
//! widening and fail-closed by the driver's Step-C. A fat-pointer slot keeps its
//! coverage and gains a correctly-sized data half.
//!
//! The same audit question — *does the code establish what it reports?* — found
//! one more fabrication on the write side of the same decoder, and it is the
//! `Val` half rather than the `Loc` half.
//! `codegen_decl_static.rs`'s fat-pointer static built its metadata as
//! `read_composite_from_bytes(..).unwrap_or_else(|| bitvec_const(0, ..))` and
//! handed the result to `PtrRepr::from_declared_roles`, whose contract is that
//! the caller has *read the roles off the declaration and is reporting them*.
//! A zero substituted for a failed read reports a length the program never
//! computed, and a zero length is the shape that manufactures a PROOF: every
//! bounds obligation over the referent becomes trivially satisfiable. The read
//! can only fail when the initializer image is shorter than the fat-pointer
//! slot, so declining costs nothing a real `&str` / `&[T]` static has, and the
//! static then falls through to the same `static_init_incomplete` widening.
//!
//! Wave 17 also re-read the census residual end to end, and found no fifth
//! actionable guard: of the 45 hits, four are genuine address-vs-value decisions
//! and all four are the walls wave 16 already annotated (the `raw_eq`
//! `Unreported` lane, `extract_pointer_expr`'s `<= 4`-field fallback, the
//! `AtomicUsize` load partition, `resolve_mut_ref_value_args`). Each needs a
//! fact no local edit has — respectively: a `codegen_place` that reports which
//! lane produced its result, the per-datatype field-role table of §4 item 7, an
//! `AtomicCell` tag written by the last store, and a typed return on
//! `translate_operand_with_modified`. Retiring any of them by narrowing its
//! predicate would be a coverage change wearing a retyping's clothes. (Wave 18
//! retired the second by SUPPLYING the missing fact at the declaration, which
//! is the only way one of these four ever comes down.) The other
//! 41 hits are comments about retired guards, the two sanctioned predicates, or
//! tests that were never about provenance — `bool`/`bv1` sort unification, the
//! `bv8` region and discriminant sorts, the packed `Layout` word, a `char`'s 32
//! bits, the split-pointer's own concat halves, and width-FIT tests that choose
//! whether to coerce rather than what a term denotes.
//!
//! Wave 18 ("the declaration carries the fact") closes the oldest of those four
//! walls — `dyn_coercion::extract_pointer_expr`'s ≤ 4-field fallback, the one
//! every prior wave annotated as unfixable *by a type*. It was: no signature on
//! that function can decide which `bv64` field of a datatype is the pointer.
//! But the fact was never missing, only discarded — one module over, at the
//! declaration, where `translate_adt_sort` and `translate_ty`'s tuple and
//! closure arms hold the MIR type of every field they declare and then keep
//! nothing but its name and sort.
//!
//! Those four declaration sites now record, per field, whether that field holds
//! an ADDRESS ([`mir_ty_denotes_address`] on the field's own MIR type) into
//! [`crate::codegen_ay::field_roles`] — §4 item 7's per-datatype field-role
//! table, keyed by `(sort name, field name)`, with a disagreement between two
//! declarations POISONING the entry rather than picking a winner (`Option_bv64`
//! is genuinely produced by both `Option<*mut u8>` and `Option<usize>`).
//! `extract_pointer_expr` reads that table, and the guess is DELETED: no lane
//! of it infers a role from a shape any more. `PtrSlot::Thin` survives inside
//! the new lane as what it has always been — a representation test, choosing
//! whether this decoder is the right one for a declared address, never whether
//! the term is an address.
//!
//! Two consequences are deliberate and neither is a retyping's silent coverage
//! change. Datatypes whose leading pointer-width field is a LENGTH — the
//! `IndexRange`/`Layout`/`VecIntoIter`-`fld_pos` family, and every
//! `struct S(usize, *mut u8)` — stop yielding an address, which is the
//! fabrication the wave exists to end. Datatypes with MORE than four fields but
//! exactly one declared address field start yielding one, which the `<= 4`
//! blast-radius bound had been suppressing along with the defect. A datatype
//! with two declared addresses answers `None`: which of them is "the" pointer
//! is precisely the question position was being used to answer.
//!
//! What is NOT in the table is the honest residual: sorts the encoder
//! synthesizes with no MIR type to read — stub datatypes, coroutine state
//! machines, sorts rebuilt by name — record nothing, and an unrecorded field is
//! *unknown*, not *value*. Those consumers take the demotion lane they already
//! had. Three walls remain (the `raw_eq` `Unreported` lane, the `AtomicUsize`
//! load partition, `resolve_mut_ref_value_args`), each still needing a fact no
//! local edit has.
//!
//! Wave 19 ("the three sites that rested on an unchecked premise") takes the
//! remaining self-labelled UNCLEAR tags. Each one *minted* a [`Loc`] (or a
//! [`Val`]) on a premise the site itself could not check, which is an assertion
//! wearing a comment's clothes. None of the three is left asserting.
//!
//! * `codegen_call_atomic`'s load partition — **CLOSED, and §4 item 1's own
//!   diagnosis was wrong.** That item said an `AtomicUsize` holds either a
//!   pointer bit-pattern or an integer depending on run-time history, so no
//!   static fact decides the branch, and asked for an `AtomicCell` tag written
//!   by the last store. Checked: that information does not exist and would not
//!   have helped — `store_forward_map` records the store's DECLARED type key,
//!   which is `usize` under either reading. The branch was never asking what
//!   the atomic holds. It asks whether `resolve_ref_or_const_referent`
//!   DEREFERENCED or handed back the operand's own term, and its six tiers
//!   already know: tiers 1–4.5 resolve *through* the reference to the
//!   referent's datum, tiers 5–6 return the operand's own translated term,
//!   which for a reference operand is the POINTER. That is a compile-time fact
//!   about which tier answered, known at the producer and discarded on the way
//!   out. `Referent::{Value, Unreported}` carries it, and both the
//!   `bitvec_width() == Some(64)` test and the `has_ref_target` proxy (asked of
//!   a *different* function that can disagree with the tier that actually
//!   answered) are deleted from the partition. `Unreported` is not a claim of
//!   addresshood — the Mem lane it feeds still says [`MaybeLoc::Unknown`].
//! * `codegen_call_cell::recover_cell_referent_address`'s route 2 — the
//!   operand-translator wall, PARKED HONESTLY. Wave 15 established what it
//!   could (the MIR type must denote an address, `T` narrower than
//!   [`POINTER_WIDTH`] excludes both known dematerialization lanes,
//!   [`is_value_widened_into_address`] excludes the third), but three facts and
//!   a shape test are a *filter*, not a producer's report, and
//!   `Loc::of_address` asserted one anyway. It now returns [`MaybeLoc`]:
//!   route 1 is `Known` (a real `(obj_id, offset)` from the ref-resolution
//!   cascade), route 2 is `Unknown`, and the Cell load/store emitters take the
//!   `MaybeLoc` and put the `Unknown` lane on the `#[deprecated]` untyped shims
//!   — exactly the residual those shims are alive for. The encoding is
//!   unchanged; refusing instead would decline the whole interception into the
//!   fail-closed Cell quarantine, which is a coverage change to be measured
//!   against the burndown rather than smuggled in here.
//! * `projected_assign::inline_deref_target_addr` — the NAMED premise is now
//!   PROVED, and the real residual turns out to be a different producer. The
//!   site said its tag rested on the MIR premise alone because
//!   `resolve_mut_ref_value_args` (#3980) might have substituted the pointee's
//!   VALUE for the arg's term. It cannot have: that function substitutes only
//!   under `is_address`, which *requires* `pointee_sort.bitvec_width() !=
//!   Some(POINTER_WIDTH)`, and the term it writes has exactly that
//!   `pointee_sort` — so a substituted term is never `bv(POINTER_WIDTH)` and
//!   never survives this function's shape test; an untranslatable pointee makes
//!   it `continue`; and its case (b) writes nothing at all. What *can* put a
//!   non-address in a pointer-typed local's term is the walker's own
//!   transparent-reference lane: `inline_ref_place_to_expr` returns
//!   `InlineRefExpr::Transparent` — the referenced place's own term — and that
//!   fact is dropped one call later at `inline_shared/rvalue.rs`'s
//!   `.map(InlineRefExpr::into_expr)`, because `local_exprs` is still
//!   `HashMap<usize, Expr>`. For `&mut x` with `x: usize`/`*mut T`/`Box<T>` the
//!   transparent term is pointer-width and indistinguishable here. The
//!   ESTABLISHED lane keeps its [`Loc`]; the wall lane returns
//!   [`MaybeLoc::Unknown`] and its load/store go through the untyped shims.
//!   Refusing is still NOT the safe direction (the functional lane loses the
//!   write just as silently), so the behaviour is unchanged and the fix stays
//!   walker plumbing — now with the producer named.
//!
//! Two walls remain: the `raw_eq` `Unreported` lane and
//! `resolve_mut_ref_value_args` (whose arg still arrives from
//! `translate_operand_with_modified`, the same wall the `*_untyped` shims are
//! parked against). Both mint no tag.
//!
//! # Two shims are alive on purpose
//!
//! `load_from_memory_untyped` and `build_memory_store_untyped` are
//! `#[deprecated]`, and their surviving callers are the *finding*, not
//! unfinished chores. Each is a site where no honest `Loc` exists: the
//! `MaybeLoc::Unknown` lanes inside `ptr_receiver_mem` (§4 item 10 — making
//! `Unknown` fail closed is a coverage change that has to be measured against
//! the burndown, not smuggled into a retyping wave), and a tail of call-side
//! addresses that arrive from `translate_operand_with_modified`, which serves
//! every operand in the encoder and reports nothing about what it returned.
//! `cargo check` prints the exact list; writing `Loc::of_address` at any of them
//! to silence the warning would be the refactor failing.
//!
//! # A measurement correction that changes the campaign's own scoreboard
//!
//! The number this campaign has been tracking — the census `rg` over
//! `codegen_ay/` for a sort's bit-width compared against `Some(..)` — counts
//! **unit-test assertions**, and they dominate it. (Spelling the pattern out
//! here would add one more hit to the very number being reported, which is its
//! own small illustration of how literal the metric is.) Measured across three
//! tree states:
//!
//! | tree | tracked census | in `chc/tests/**` | in encoder code |
//! |---|---|---|---|
//! | pre-campaign | 316 | 224 | **92** |
//! | after waves 1-5 | 302 | 224 | **78** |
//! | after waves 6-11 | 292 | 224 | **68** |
//! | after waves 12-15 | 277 | 224 | **53** |
//! | after wave 16 | 269 | 224 | **45** |
//!
//! The test population is *exactly constant* at 224 in every tree: it is pure
//! noise, inert with respect to every wave. So the retirement to date is
//! **47 of 92 encoder guards (51%)**, not the "24 of 273 (9%)" the waves-6-11
//! commit message reported — both the numerator's denominator and the survey's
//! 273 counted assertions as guards.
//!
//! **Wave 16 corrects the estimate this section made of its own remainder.**
//! "~30 genuine address-vs-value guards left" was a projection from sampling;
//! reading all 53 survivors one by one found **twelve**, of which eight were
//! retired and four are annotated walls (see the wave-16 note above). The other
//! 41 are comments, the two sanctioned predicates, or width tests that were
//! never about provenance. Two consequences for whoever scores this next:
//!
//! * the census is now nearly exhausted as a *source of work* — 45 hits, ~4
//!   actionable, and every one of those four needs a fact no local edit has;
//! * it was never a complete measure of the wall. Wave 16 found and retired
//!   four fabrication sites (`extract(127, 64)` behind a width test) that the
//!   census does not count at all, and left two more standing deliberately.
//!   Scoring the campaign by this `rg` from here on will report progress on the
//!   spelling rather than on the defect.
//!
//! The remaining waves are listed in `docs/addr-vs-value-conversion-queue.md`.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Does a local of this MIR type hold an ADDRESS, rather than a datum that
/// merely happens to be pointer-width?
///
/// # Why a MIR-type predicate belongs in this module
///
/// [`Val`] and [`Loc`] carry provenance *once it is known*. This is one of the
/// two places the fact is originally knowable — the other being an address-of
/// on a place. The Rust type of a local decides it outright: a `&T`, `*mut T`,
/// `Box<T>`, `NonNull<T>`, `Unique<T>`, `Rc<T>`, `Arc<T>` or `Weak<T>` local's
/// CHC term IS the pointer it holds, because `translate_adt_ty` flattens every
/// one of those wrappers to a bare `ptr_sort()` (see
/// `chc/decl/codegen_types_adt.rs`: "Rc/Arc/Weak -> bv64 sort (pointer
/// wrapper)"). Everything else that lands on `bv(POINTER_WIDTH)` — a `usize`,
/// an `Alignment`, a `Cow`, and the dozen opaque iterator adapters that
/// `translate_adt_ty` also collapses to `ptr_sort()` — is a VALUE, and a width
/// test cannot tell the two groups apart.
///
/// # It is deliberately a *whitelist*
///
/// The failure this predicate exists to prevent is admitting a value as an
/// address, so an unrecognized type must answer `false`. Callers that answer
/// `false` are expected to take their existing fail-closed lane (a havoced
/// destination, a fresh symbolic address, a constrained-symbolic fallback) —
/// never to fabricate.
///
/// Pass a type that has already been through `ChcCtx::resolve_body_ty`: an
/// unresolved `TyKind::Param` answers `false`, which is the safe direction but
/// is also needlessly imprecise.
pub(crate) fn mir_ty_denotes_address(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let name = def.trimmed_name();
            let short = name.rsplit("::").next().unwrap_or(name.as_str());
            // Box / Unique / NonNull, plus the reference-counted wrappers that
            // `translate_adt_ty` gives the identical `ptr_sort()` treatment.
            is_pointer_wrapper_adt(&name) || matches!(short, "Rc" | "Arc" | "Weak")
        }
        _ => false,
    }
}

/// True when `expr` is a symbolic sub-pointer-width VALUE widened into
/// pointer width (`zero_extend`/`sign_extend` of a narrow non-constant).
///
/// # Why this lives next to [`Loc`]
///
/// This is the predicate that decides whether a [`Loc::of_address`] tag would
/// be a FABRICATION rather than a fact, so it belongs with the tag it guards.
/// Such expressions are never real storage addresses: the split-pointer model's
/// obj_id (the upper 32 bits) is forced to 0 / sign-fill, i.e. the null object.
/// They arise wherever a narrow datum is laundered through a pointer-sorted
/// slot — ref-dematerialization flattening a `Cell<u32>` payload, an assignment
/// coercion zero-extending into a pointer-sorted local, or a `coerce_to_ptr_width`
/// call on an operand that was never pointer-shaped.
///
/// Constant widenings are exempt: literal addresses (e.g. `0 as *const T`) keep
/// the legacy null-deref check behavior.
pub(crate) fn is_value_widened_into_address(expr: &Expr) -> bool {
    match expr.value() {
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. } => {
            inner.sort().bitvec_width().is_some_and(|w| w < POINTER_WIDTH)
                && !matches!(inner.value(), ExprValue::BitVecConst { .. })
        }
        _ => false,
    }
}

/// Is `sort` the representation a *transparent pointer wrapper* is flattened to?
///
/// `NonNull<T>`, `Unique<T>` and `Box<T>` are single-field wrappers around a raw
/// pointer, and `translate_ty` erases the wrapper: the CHC term for such a local
/// is a bare `bv(POINTER_WIDTH)`, not a one-field datatype. MIR still projects
/// `Field(0)` (and sometimes `Downcast(0)`) through the erased wrapper, so those
/// projections have to be the identity.
///
/// # This is a REPRESENTATION test, not a provenance test
///
/// It answers "was a wrapper flattened to this bv?" — it does **not** answer "is
/// this bv an address?". Deliberately so: the same `bv64` shape is also a plain
/// `u64`, and no width test can separate the two. That is what [`Val`] and
/// [`Loc`] are for. Keeping the two questions apart is the whole point; a caller
/// that needs an address must obtain one from an address producer, not from this
/// predicate returning `true`.
///
/// # Why it is shared
///
/// Four sites asked this question with their own inline copy of
/// `sort.is_bitvec() && sort.bitvec_width() == Some(POINTER_WIDTH)`: the select
/// and update halves of the CHC datatype projection, and the `Downcast` and
/// `Field` halves of the BMC post-deref projection. Two of those four are a
/// read/write pair — if the read side treats the whole `bv64` as field 0 and the
/// write side does not, the write lands in a different slot than the read, which
/// is the slot-misalignment shape that has fabricated proofs before. One
/// definition makes that drift impossible.
///
/// The predicate is intentionally exactly as narrow as the copies it replaces.
/// Widening it (for instance to every `is_pointer_wrapper_adt` name) is a
/// corpus-wide behaviour change and is out of scope for a retyping wave.
pub(crate) fn is_transparent_pointer_wrapper_repr(sort: &Sort) -> bool {
    sort.is_bitvec() && sort.bitvec_width() == Some(POINTER_WIDTH)
}

/// A **value**: an integer, a loaded datum, the result of an arithmetic op.
///
/// A `Val` denotes the datum itself, not somewhere the datum lives. Construct it
/// with [`Val::of_value`] at the site that knows the expression is a value.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub(crate) struct Val(Expr);

impl Val {
    /// Tags `expr` as a value, at the producer that knows it is one.
    ///
    /// Callers must only use this where the value provenance is *known* — not
    /// where it is being assumed because the alternative was inconvenient.
    pub(crate) fn of_value(expr: Expr) -> Self {
        Self(expr)
    }

    /// Consumes the wrapper and returns the underlying expression.
    pub(crate) fn into_expr(self) -> Expr {
        self.0
    }

    /// Borrows the underlying expression without dropping the provenance tag.
    pub(crate) fn as_expr(&self) -> &Expr {
        &self.0
    }
}

/// An **address**: an expression that points at storage.
///
/// A `Loc` denotes *where* a datum lives. Reading through it is a load, which is
/// the only legal way to obtain a [`Val`] from it. Construct it with
/// [`Loc::of_address`] at the site that knows the expression is an address.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub(crate) struct Loc(Expr);

impl Loc {
    /// Tags `expr` as an address, at the producer that knows it is one.
    ///
    /// Callers must only use this where the address provenance is *known* —
    /// typically an address-of on a place, or an address threaded through from
    /// another `Loc`.
    pub(crate) fn of_address(expr: Expr) -> Self {
        Self(expr)
    }

    /// Consumes the wrapper and returns the underlying expression.
    pub(crate) fn into_expr(self) -> Expr {
        self.0
    }

    /// Borrows the underlying expression without dropping the provenance tag.
    pub(crate) fn as_expr(&self) -> &Expr {
        &self.0
    }
}

/// An address slot fed by two producers, only one of which knows it is one.
///
/// # The site this exists for
///
/// `ptr_receiver_mem::receiver_mem_target` resolves an atomic / volatile
/// intrinsic's pointer argument to `(address, pointee_ty)`. Two shapes reach
/// that slot:
///
/// * a **synthesized** `concat(obj_id, 0)` built from a traced allocation id —
///   an address by construction, with nothing to guess about;
/// * whatever `translate_operand_with_modified` returns for the same operand —
///   provenance genuinely unknown, because that function serves every operand
///   in the encoder and does not report what it produced.
///
/// Collapsed to a bare `Expr` the two are indistinguishable downstream, so the
/// slot was filtered by `bitvec_width() == Some(64)`: a test that is vacuous on
/// the first shape (the concat is always `bv64`) and a guess on the second. See
/// `docs/addr-vs-value-conversion-queue.md` §4 item 10.
///
/// # What is and is not fixed here
///
/// This type carries the distinction — that is the missing fact, and it is now
/// available to every consumer. It does **not** yet make [`MaybeLoc::Unknown`]
/// fail closed, which is what §4 item 10 ultimately asks for: refusing the
/// unknown shape drops encoding coverage for heap-backed receivers, and a
/// coverage change has to be measured against the burndown rather than smuggled
/// into a retyping wave. Consumers therefore still proceed on both arms, via
/// the deliberately conspicuous [`MaybeLoc::as_addr_expr`] /
/// [`MaybeLoc::into_addr_expr`] — grep those two names to find every place the
/// residual guess is still made.
#[derive(Clone, Debug)]
pub(crate) enum MaybeLoc {
    /// Built by the encoder as an address. No guess involved.
    Known(Loc),
    /// Produced by a translation that does not report provenance.
    Unknown(Expr),
}

impl MaybeLoc {
    /// Borrows the address expression, dropping the Known/Unknown distinction.
    ///
    /// Every call site is an unfinished §4 item 10; see the type docs.
    pub(crate) fn as_addr_expr(&self) -> &Expr {
        match self {
            Self::Known(loc) => loc.as_expr(),
            Self::Unknown(expr) => expr,
        }
    }

    /// Consumes the wrapper, dropping the Known/Unknown distinction.
    ///
    /// Every call site is an unfinished §4 item 10; see the type docs.
    pub(crate) fn into_addr_expr(self) -> Expr {
        match self {
            Self::Known(loc) => loc.into_expr(),
            Self::Unknown(expr) => expr,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Loc, MaybeLoc, Val};
    use ay_bindings::{Expr, Sort};
    use std::any::TypeId;

    fn sample_value() -> Expr {
        Expr::bitvec_const(42u128, 32)
    }

    fn sample_address() -> Expr {
        Expr::var("_1_addr", Sort::bitvec(64))
    }

    /// `Val::of_value` wraps without altering the expression.
    #[test]
    fn val_construction_preserves_expr() {
        let expr = sample_value();
        let val = Val::of_value(expr.clone());
        assert_eq!(val.as_expr(), &expr);
    }

    /// `Loc::of_address` wraps without altering the expression.
    #[test]
    fn loc_construction_preserves_expr() {
        let expr = sample_address();
        let loc = Loc::of_address(expr.clone());
        assert_eq!(loc.as_expr(), &expr);
    }

    /// `of_value` -> `into_expr` is the identity on the wrapped expression.
    #[test]
    fn val_into_expr_round_trips() {
        let expr = sample_value();
        assert_eq!(Val::of_value(expr.clone()).into_expr(), expr);
    }

    /// `of_address` -> `into_expr` is the identity on the wrapped expression.
    #[test]
    fn loc_into_expr_round_trips() {
        let expr = sample_address();
        assert_eq!(Loc::of_address(expr.clone()).into_expr(), expr);
    }

    /// `as_expr` borrows the same expression `into_expr` would hand back.
    #[test]
    fn as_expr_agrees_with_into_expr() {
        let val = Val::of_value(sample_value());
        let borrowed = val.as_expr().clone();
        assert_eq!(val.into_expr(), borrowed);

        let loc = Loc::of_address(sample_address());
        let borrowed = loc.as_expr().clone();
        assert_eq!(loc.into_expr(), borrowed);
    }

    /// Cloning a wrapper preserves both the provenance and the expression.
    #[test]
    fn wrappers_clone() {
        let val = Val::of_value(sample_value());
        assert_eq!(val.clone().into_expr(), val.into_expr());

        let loc = Loc::of_address(sample_address());
        assert_eq!(loc.clone().into_expr(), loc.into_expr());
    }

    /// The whole point: `Val` and `Loc` are *distinct* types, so the compiler
    /// rejects passing an address where a value is expected. There is no `From`,
    /// no `Deref`, and no blanket conversion between them — the only legal
    /// crossings are an explicit load or an explicit address-of.
    #[test]
    fn val_and_loc_are_distinct_types() {
        assert_ne!(TypeId::of::<Val>(), TypeId::of::<Loc>());
    }

    /// Wrapping the *same* expression in the two tags yields two values that no
    /// signature can confuse, even though the payloads are equal.
    #[test]
    fn same_expr_two_provenances_stay_separate() {
        let expr = sample_value();
        let val = Val::of_value(expr.clone());
        let loc = Loc::of_address(expr.clone());
        // Payloads match ...
        assert_eq!(val.as_expr(), loc.as_expr());
        // ... but the wrappers are different types, so `fn f(_: Val)` cannot be
        // called with `loc`. That is enforced at compile time, not here.
        assert_eq!(val.into_expr(), expr);
        assert_eq!(loc.into_expr(), expr);
    }

    /// A `MaybeLoc` keeps the two producers apart even though both accessors
    /// hand back the same expression.
    #[test]
    fn maybe_loc_keeps_the_two_producers_apart() {
        let known = MaybeLoc::Known(Loc::of_address(sample_address()));
        let unknown = MaybeLoc::Unknown(sample_address());

        assert!(matches!(known, MaybeLoc::Known(_)));
        assert!(matches!(unknown, MaybeLoc::Unknown(_)));
        assert_eq!(known.as_addr_expr(), unknown.as_addr_expr());
        assert_eq!(known.into_addr_expr(), unknown.into_addr_expr());
    }

    /// Both wrappers are `Debug`, so provenance shows up in diagnostics.
    #[test]
    fn wrappers_are_debug() {
        assert!(format!("{:?}", Val::of_value(sample_value())).starts_with("Val("));
        assert!(format!("{:?}", Loc::of_address(sample_address())).starts_with("Loc("));
    }
}
