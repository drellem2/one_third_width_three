# State — OneThird S1-B: Step 1 Lean port part 2 (mg-2e24)

**Ticket:** mg-2e24 — OneThird-S1-B: Step 1 Lean port part 2 — BK move
classification and bad-set boundary bounds.
**Phase:** FULL REFACTOR Phase 2, Wave-1 (Piece-1 Steps 1-6 cascade
port), per `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.1.
**Depends:** mg-faf8 (corrected MA-Sig signature contract — landed).
**Session:** 1. **Verdict:** GREEN — part (iii) ported in full;
part (iv) structural backbone ported in full; one paper-side
imprecision in part (iv) surfaced and reported (not ill-posed, does
not block).

## Scope delivered

S1-B is parts (iii) and (iv) of `thm:interface` (`step1.tex`), the
local interface theorem for a width-3 rich pair `(x, y)`. Parts (i)
and (ii) (coordinate map + good/bad fiber partition) are S1-A
(mg-30e3); the corollaries are S1-C (mg-bcf2); assembly is S1-D
(mg-794c). All four are parallel Wave-1 tickets; S1-B writes into two
fresh files so it does not collide with the parallel S1-A port.

### `lean/OneThird/Step1/BKMoves.lean` — part (iii), BK move classification

Faithful, fully-proved (no `sorry`, no new axiom) port of part (iii)
(`step1.tex:155-173`). The structural core is `BKAdj.swapPair`: a
single BK move reverses the strict order of *exactly* the swapped
incomparable pair `{a, b}` and preserves every other ordered pair.
From that:

- `bkSwap_signMarker_eq` / `bkSwap_iCoord_eq` / `bkSwap_jCoord_eq` —
  the sign / first / second coordinate are preserved unless the
  swapped pair is `{x, y}` / `{x, c}` / `{y, c}` respectively
  (`c` a common neighbour).
- `bkSwap_signFlip` — swapping `{x, y}` flips `σ`, fixes `(i, j)`.
- `bkSwap_iCoord_shift` / `bkSwap_jCoord_shift` — swapping `{x, c}` /
  `{y, c}` shifts `i` / `j` by exactly `±1`, fixes the rest.
- `bkMove_classification` — the headline trichotomy: every BK move
  either fixes `(i, j, σ)`, flips `σ` only, shifts `i` by `±1` only,
  or shifts `j` by `±1` only. `HasWidthAtMost α 3` enters only to
  rule out a swap of two common neighbours (`commonNbhd` is a chain).

**Refinement of the paper.** Read literally, `step1.tex` part (iii)
case (a) ("internal grid step") also covers the *mixed* swap of a
common neighbour with an external element; the port shows that swap
in fact preserves `(i, j, σ)` (a "grid step of `0`"). The precise
truth — `(i, j, σ)` is altered *only* by the three special swap
types — is what `bkMove_classification` states. This is a strict
refinement of the paper's prose, not a contradiction.

### `lean/OneThird/Step1/BadSet.lean` — part (iv), bad-set boundary bounds

Faithful, fully-proved (no `sorry`, no new axiom) port of the
structural backbone of part (iv) (`step1.tex:174-194`):

- `commonNbhdFinset_comparable` — common neighbours are pairwise
  comparable (`lem:CNchain-width3` in `Finset` form).
- `incomp_of_between` / `incompLocus_ordConvex` — order-convexity of
  the incomparability locus `I(z)` (`step1.tex:307-311`): the common
  neighbours incomparable to a fixed `z` form a contiguous
  sub-interval of the chain.
- `card_externalFinset` — `|Z| = n - t - 2` (`step1.tex:301`).
- `collinear_fiber_card_le` / `collinear_fiber_card_le'` — the
  per-fiber bound (`step1.tex:352-358`): a raw fiber whose `π`-image
  is confined to one axis-parallel line and which is
  `(localCoord, σ)`-injective has `≤ t + 1` elements. This is the
  boundary-cardinality content: every raw fiber meeting `Bad_{x,y}`
  is one-dimensional, hence carries at most `t + 1` extensions.

These are exactly the load-bearing ingredients of the paper's
`|Bad_{x,y}| = O(n · t)` bound: `K = O(1)` strips, each a union of
`O(n)` raw fibers, each fiber `≤ t + 1`.

## Finding — paper-side imprecision in part (iv) (reported, non-blocking)

`step1.tex:308-311` claims the incomparability locus
`I(z) := {k : z ∥ c_k}` of an **external** element `z` has
**length** `≤ 2`, citing a width-`4` antichain inside
`{x, y, z} ∪ {c_{k_1}, c_{k_2}, c_{k_3}}`.

A literal check does not support the length bound. The common
neighbours `c_k` are pairwise comparable (they are a chain), so any
antichain inside that set contains **at most one** `c_k`; a `4`-element
antichain would therefore have to be `{x, y, z, c_k}`, which requires
`z ∥ x` **and** `z ∥ y` — i.e. `z ∈ commonNbhd x y`. But `z` is
*external* (`z ∉ {x, y} ∪ C(x, y)`), so `z` is comparable to `x` or
to `y`, and no such `4`-antichain exists. Width `3` yields only the
**order-convexity** of `I(z)`, not `|I(z)| ≤ 2`.

**Impact.** `incomp_of_between` (order-convexity) is ported in full
and is correct. The unproven step is the `O(1)` *length* bound on
`I(z)`; with only convexity one gets `|I(z)| ≤ t`, degrading the
paper's `|Bad| = O(n · t)` to `O(n · t²)`. In the rich regime used
by Corollaries `cor:overlap` / `cor:triple-overlap`
(`|F_{x,y}| ≥ c · n²`, `t = Θ(n)`, `|F_{x,y}|` factorially large)
`O(n · t²)` still establishes `|Bad| = o(|F_{x,y}|)`, so the
qualitative "bad set is lower-dimensional" conclusion is unaffected;
only the sharp constant in the exponent is at stake.

**This is not an ill-posed target and does not block S1-B.** The
part-(iv) target ("`Bad` is one-dimensional", per-fiber `≤ t + 1`,
external count `n - t - 2`) is well-posed and fully ported; the gap
is a one-line over-claim in a sub-step of the paper's counting
argument. It is flagged here and mailed to `human` for the Step 1
assembly ticket (S1-D, mg-794c) to decide: (a) supply a corrected
`I(z)`-length argument, (b) accept the `O(n · t²)` bound (sufficient
downstream), or (c) carry `|I(z)| ≤ 2` as a small documented
axiom/hypothesis at the assembly site.

## Non-vacuity

The non-triviality bar (concrete width-3 non-chain `α`, no
`Subsingleton`-on-empty baseline) is met by `Antichain3`, the
discrete order on `Fin 3` — the same witness type the parallel S1-A
port (mg-30e3) lands in `OneThird/Step1/GroundSet.lean`, reused here
rather than redefined. `bkMove_classification_nonvacuous` proves
`Antichain3` is width-`3`, non-chain, with `a0 ∥ a1` a rich pair
whose common-neighbour finset `{a2}` is non-empty — so the special
swaps `{a0,a1}`, `{a0,a2}`, `{a1,a2}` driving every branch of
`bkMove_classification` are realizable.
`badSet_structure_nonvacuous` instantiates the part-(iv) chain lemma
on the same poset. (`Antichain3` has no external element, so its
`externalFinset` is empty — correct, since a pure antichain has no
external elements; a non-empty external set needs `≥ 4` elements,
which is a setting fact, not a vacuity.)

## Build

`lake build` clean (mathlib `v4.29.1` cache). New files imported into
`lean/OneThird.lean`. No `sorry`, no new axiom, no change to the
headline or to any existing file's content. Only linter warnings
(`unusedSectionVars` / `unusedDecidableInType`), consistent with the
existing tree (`OneThird/Mathlib/BKGraph.lean` etc.).

## Hand-off to S1-D (mg-794c)

`bkMove_classification` and the part-(iv) structural lemmas are ready
for the `thm:interface` assembly. S1-D should decide the `I(z)`
length-bound question above before stating the sharp
`|Bad_{x,y}| = O(n · t)` form of part (iv).
