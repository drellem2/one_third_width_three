# OneThird-S5-A G1-G2 Session 1 state report — grounded forms landed

**Ticket:** mg-b21f (FULL REFACTOR Phase 2, Wave-1; Piece-1 Steps-1-6
cascade port; scoped by mg-d8c7 §2.1 / §5.2 under S5-A; depends on
mg-faf8).
**Verdict:** **GREEN — substantively landed.** Step 5 G1
(`lem:endpoint-mono`) and G2 (`lem:convex-overlap`) ports completed and
*grounded*: the abstract endpoint families are wired to genuine poset
incomparability intervals, and the whole G1→G2 chain is instantiated
**non-vacuously** on a concrete width-3 non-chain poset. Full
`lake build` clean.

---

## §0. TL;DR

* **G1 (`lem:endpoint-mono`, `step5.tex:252-353`)** was already a
  faithful abstract port in `Step5/EndpointMono.lean` (`interval_form`,
  `alphaIdx`/`betaIdx` monotone). Left unchanged — verified against the
  paper and confirmed correct (the lemma uses only transitivity, per
  `rem:G1-counterexample`).
* **G2 (`lem:convex-overlap`, `step5.tex:355-506`)** — `ConvexOverlap.lean`
  previously stopped at `convex_overlap_structural` (rows order-convex +
  threshold monotonicity), explicitly disclaiming the dichotomy. This
  session **completes G2**: 2D order-convexity of the overlap region,
  column order-convexity, monotone row endpoints `L_i`/`U_i`, the band
  around a nondecreasing envelope (Step 4), and the rich-or-banded
  dichotomy `convex_overlap` (the actual `lem:convex-overlap`).
* **Grounding** — new file `Step5/G1G2Grounded.lean` bridges the
  abstract `Fin p → ℤ` endpoint families to the genuine `C`-coordinate
  incomparability-interval endpoints of a poset triple
  (`endpoint_mono_grounded`, `convex_overlap_grounded`).
* **Non-vacuity bar met.** Instantiated on `W3 := Fin 3 × Fin 3`
  (product order) — a genuine width-3 non-chain poset
  (`W3_widthAtMost_three`, `W3_not_chain` both proved, not assumed).
  `g1_g2_grounded_concrete` exhibits: a non-empty incomparability
  interval, a *strictly* increasing `β`-endpoint family (G1
  monotonicity exercised, not constant), and a non-empty rich set
  (`richPair_concrete`). No `Subsingleton`/empty baseline anywhere.
* **No new axioms, no `sorry`, no headline-path change.** All additions
  are pure interval geometry + a concrete instance; downstream
  (`Dichotomy.lean` etc.) unaffected (additions only).

## §1. Inventory delta

```
EndpointMono.lean      166 LoC  (unchanged — already faithful)
ConvexOverlap.lean     306 → 639 LoC  (+333; G2 completion)
G1G2Grounded.lean      new, 277 LoC   (grounding + concrete instance)
OneThird.lean          +1 import line
```

**Net polecat output:** ~610 LoC of Lean + this state doc.

## §2. G1 — assessment (no change required)

`EndpointMono.lean` already ports `lem:endpoint-mono` faithfully:
`interval_form` (`lem:interval-form`, `step5.tex:32-40`), the
lower/upper-set monotonicity facts, and `endpoint_mono` — the four
endpoint indices `alphaIdx`/`betaIdx` weakly increasing on the poset
order, witnessing `D₁(T) = E₁(T) = 0` (`rem:G1-constants`). Re-read
against `step5.tex:252-331`; the proof correctly uses only transitivity
(`rem:G1-counterexample` — the counterexample/width-3 hypothesis is
*not* used by G1). No defect found; no change.

## §3. G2 — what was completed

Pre-session `ConvexOverlap.lean` provided the "structural ingredients"
(`rich_implies_crit`, `critRow_orderConvex`, threshold monotonicity,
`convex_overlap_row_card_le`) but `convex_overlap_structural`'s own
docstring states it is only "the structural half" — the actual
`lem:convex-overlap` dichotomy was **not** stated. Added:

| Symbol | Role (`step5.tex`) |
|---|---|
| `critRow` | the criterion row as a `Finset (Fin q)` |
| `richRow_subset_critRow` | rich row ⊆ criterion row (banding `critRow` bands `richRow`) |
| `crit_orderConvex_2d` | **2D order-convexity** of the overlap region (`step5.tex:421-422`, the "doubly monotone staircase") |
| `critCol_orderConvex` | columns order-convex (symmetric to rows) |
| `critRow_min'_mono` / `critRow_max'_mono` | `L_i`/`U_i` nondecreasing in `i` (`step5.tex:416-417`) |
| `bandWidth`, `bandEnvelope` | `W⋆` and the nondecreasing envelope `f` (`step5.tex:425-432`) |
| `convex_overlap_band` | conclusion (b): rich set in a width-`W⋆` band around `f` |
| `convex_overlap` | the full `lem:convex-overlap` dichotomy (a)∨(b) |

The endpoint-monotonicity proofs (`critRow_min'_mono` etc.) use a clean
criterion-based argument (no explicit initial/final-segment
bookkeeping). The band envelope is the running maximum of the row
minima — monotone by construction, equal to the row minimum on every
non-empty row — and the band width `W⋆` is the genuine maximum
criterion-row width, *not* the trivial whole-range width `q`.

### Scope note — quantitative `K`-bound deliberately not claimed

The paper's `eq:G2-K` (`K ≤ ℓ_I⋆ + ℓ_J⋆ − 2T + O(E₀)`,
`step5.tex:445-454`) is the *quantitative* half of G2 and, per
`rem:G2-structural`, is separated from the structural content; per
`rem:G2-application` its collapse to `K = K(T)` is supplied downstream
by G3 + the 1/3–2/3 hypothesis. `convex_overlap_band` therefore
delivers `K = W⋆` (max criterion-row width) as a genuine, well-defined
quantity, but does not assert the `ℓ⋆`-bound — that is correctly the
job of the G3/`thm:step5` tickets (S5-B / S5-E), which consume these
monotone row endpoints. This is the `rem:G2-structural` structural /
quantitative split, not a vacuous routing.

## §4. Grounding (`G1G2Grounded.lean`)

* `endpointFamily_alphaIdx_monotone` / `endpointFamily_betaIdx_monotone`
  / `endpoint_mono_grounded` — G1 lifted to index families: monotone
  chain enumerations `a : Fin p → α`, `b : Fin q → α` give monotone
  `C`-coordinate endpoint families.
* `convex_overlap_grounded` — G2 dichotomy on the *genuine*
  incomparability-interval endpoint families; G1 discharges G2's
  monotonicity hypotheses.

## §5. Non-vacuous instantiation (`mg-b21f` acceptance bar)

`W3 := Fin 3 × Fin 3` (product order), Dilworth-decomposed into three
length-3 chains `chainA`, `chainB`, `chainC`. `g1_g2_grounded_concrete`
bundles, all proved (not assumed):

1. `HasWidthAtMost W3 3` (via first-coordinate injectivity of antichains)
   and `¬ IsChainPoset W3`;
2. the `β`-endpoint family of `chainA` is monotone **and strictly
   increasing** (`betaIdx … 0 = 0 < 2 = betaIdx … 2`) — G1
   monotonicity is exercised, not satisfied by a constant family;
3. the incomparability interval `IC(chainA 1)` on `chainC` is non-empty;
4. the `convex_overlap_grounded` dichotomy holds, and the rich set is
   non-empty (`richPair_concrete`: `(chainA 2, chainB 2)` rich at
   `T = 1`).

No `Subsingleton`-on-empty baseline; `p = q = 3`; intervals genuinely
non-empty and genuinely varying. The acceptance bar is met.

## §6. No gap-discovery

Default-skeptical re-read of `step5.tex:252-506` (G1 + G2) against the
Lean port surfaced **no ill-posed target** and **no missing mathlib
dependency**. One paper looseness noted for downstream awareness (not
blocking this ticket): the `eq:G2-K` index-count bound implicitly
assumes the `γ`-family is injective; with a non-strict-monotone `γ` the
index span of a corridor is not bounded by its coordinate width. This
only affects the *quantitative* `K`-bound (out of scope here, §3) — the
structural dichotomy and the band with `K = W⋆` are unaffected. S5-E
(`thm:step5`) consuming `convex_overlap` should source the `ℓ⋆`-bound
from G3 + the counterexample hypothesis as `rem:G2-application`
prescribes.

## §7. Build

`lake build` (full OneThird tree) clean. `ConvexOverlap`,
`G1G2Grounded`, and all downstream modules compile; no new warnings.
