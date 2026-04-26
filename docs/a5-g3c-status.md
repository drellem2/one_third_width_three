# A5-G3c-followup status (mg-7268)

**Status (2026-04-26):** §5 + §6 complete, §7 ~30% complete, §8 not
started. Build is clean, no sorry/axioms.

## What's shipped (`cc89b21`)

* **§5** — `enumPredPreWarshallOf_eq`: imperative two-`for`-loop reduces
  to `addEdgesList + List.foldl maskedFreeBody` form. Helpers:
  `forIn_forced_eq_addEdgesList`, `forIn_free_eq_foldl_maskedFreeBody`,
  `maskedFreeBody_dite_eq` (bridges `Array.getD` ↔ `dite`).
* **§6** — bit characterization (`testBit_enumPredPreWarshallOf_imp`,
  `_of_forced`, `_of_free`).
* **§7 partial** — rectangle abstraction `pushRect`,
  `mem_pushRect` (full iff), `pushRect_size`, `jLoopBody`,
  `mem_pushRect_mono`, `mem_jLoopBody_mono`,
  `mem_foldl_jLoopBody_mono`, `forIn_inner_two_loops_true/false`
  (inner two for-loops factor through `pushRect`).

## What's blocked

The `enumPartition` do-block elaborates its two `mut` variables
(`freeUV`, `forcedUV`) into a single `MProd` state. My
`forIn_inner_two_loops_*` lemmas are stated in terms of
`Array × Array` (`Prod`), not `MProd`, so they don't directly compose
with the outer two-loop reduction.

Bridging requires either:

(a) Restating all §7 helpers (`pushRect`-based body, `jLoopBody`,
    monotonicity) in terms of `MProd (Array (Nat × Nat))
    (Array (Nat × Nat))` instead of `Array × Array`. This is a
    mechanical rewrite (~80 LOC) but every `(state.1, state.2.push x)`
    becomes `⟨state.fst, state.snd.push x⟩`, etc., and the
    `forIn_inner_two_loops_*` proofs need their `show ... = (..., ...)`
    forms updated.

(b) Proving an `MProd ↔ Prod` bridge lemma at the join point, then
    leaving §7 helpers as-is. Possibly cleaner but the bridge has its
    own subtleties (the `forIn` body arity differs).

I attempted (a) once and hit cascading type errors in the inner-loop
helpers — the `state.1.push (a, b)` notation doesn't resolve when
`state : MProd ...`. Reverted to keep the build clean.

## What's still needed (estimated ~250 LOC)

Even with the MProd bridge fixed:

* **§7 full** — `enumPartition_eq_foldl` (loop reduction to nested
  foldl over `(i, j)`), `mem_enumForcedUVOf_iff`,
  `mem_enumFreeUVOf_iff`. Estimated ~120 LOC remaining.
* **§7 supporting** — `freeUVOf L = enumFreeUVOf L.w (bandSizes L)`
  (the spec flags this as needing either a structural proof or a
  refactor of `freeUVOf`'s definition; refactor likely simpler since
  `closureCanonical_predMaskOf` and `maskOf_lt_two_pow_size` use
  `freeUVOf` only abstractly via `.size`/`.getD k (0,0)`).
  Estimated ~50 LOC for the refactor + ripple-fix.
* **§8** — `enumPredAtMaskOf_eq_predMaskOf` itself, combining §6, §7,
  and `forced_lt`/`predMaskOf_warshall`/`closureCanonical_predMaskOf`.
  Estimated ~80 LOC.

## Recommendation

Spawn a sub-followup `mg-7268-followup` with:

1. The MProd bridge (or restate §7 helpers in MProd).
2. `enumPartition_eq_foldl` + membership iff.
3. `freeUVOf` refactor.
4. §8 final equality.

The shipped pieces (§5, §6, §7 rectangles) provide a tested foundation
for the next polecat to build on.

## No-axiom check

`#print axioms width3_one_third_two_thirds` is unchanged.  Build is
clean with no `sorry`, `admit`, or new axiom additions.
