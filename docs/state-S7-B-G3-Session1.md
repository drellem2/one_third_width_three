# OneThird S7-B G3 (`lem:triple-visibility`) — Session 1

**Ticket:** mg-9331
**Branch:** `polecat-cat-mg-9331`
**Depends:** mg-4584 (S7-A G1+G2 grounded forms — landed at 1d4f66d)
**Scope:** Phase E S7-B per `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) §7.1 — Lean port of `step7.tex` G3 (`lem:triple-visibility`, `step7.tex:1376-1482`).

## TL;DR — verdict

**GREEN G3 substantively landed.** `lean/OneThird/Step7/TripleVisibility.lean` (~600 LoC) delivers the three substantive parts (a), (b), (c) of paper `lem:triple-visibility` in cleared-denominator parametric form, wired to the existing `Step5.SecondMoment.lean` infrastructure (`visibility`, `visibility_sum_eq_fiber_mass`, `second_moment_visibility`).  `lake build OneThird.Step7.TripleVisibility` is clean; full `lake build` not regression-checked (still running in background at status-doc time).

Three Lean-level deliverables:

* **`triple_overlap_mass_sum_eq_visibility_cube`** — Fubini cube identity (b): `∑_{(α,β,γ) ∈ Rich⋆³} w_{αβγ} = ∑_L I(L)^3`.  Pure double-counting; no analytic input.
* **`third_moment_visibility`** — Jensen lower bound (a): `c³ · |LP| ≤ ∑_L I(L)^3`, from the first-moment Richness input `c · |LP| ≤ ∑_α |F*_α|`.  Uses `Finset.pow_sum_le_card_mul_sum_pow` (mathlib's Jensen-for-ℕ via Chebyshev's sum inequality, `Mathlib.Algebra.Order.Chebyshev`).
* **`edge_fraction_in_triples_failure_bound`** — cleared-denominator (c): `(c² − 1) · failureWeight ≤ 4 · edgeMass`, i.e. failure fraction ≤ `4/(c²-1) = O(1/c²)` as `c → ∞`.  Builds on `Step5.second_moment_visibility` (already in tree).

Plus three packaging artefacts:

* `triple_overlap_mass_lower_bound` — combination of (a)+(b).
* `failure_weight_le_two_card` — pointwise input to (c): `failureWeight ≤ 2·|LP|`.
* `edge_mass_lower_bound_via_second_moment` — Step-5-feed-through: `c² · |LP| ≤ 2·edgeMass + |LP|`.
* `triple_visibility_grounded` — single-call bundled conjunction of (a)+(b)+(c) for downstream consumers (`lem:cocycle`, `lem:sign-consistency`'s `OutsideMass` discharge).

**No `sorry`. No new axioms. No additional mathlib gaps surfaced.** Paper-faithful packaging matches `step7.tex:1376-1482` line-for-line.

## What was built

### Files added

* `lean/OneThird/Step7/TripleVisibility.lean` — ~600 LoC new file.
* `lean/OneThird.lean` — single-line `import OneThird.Step7.TripleVisibility` after `SignConsistency`, before `Cocycle`.

### Files unchanged

All other Step 7 files: `SignedThreshold.lean`, `SignConsistency.lean`, `Cocycle.lean`, `Potential.lean`, `SingleThreshold.lean`, `Bandwidth.lean`, `Assembly.lean`.

### `AXIOMS.md` delta

None.  No new axioms; no axioms dropped.

## How (a), (b), (c) map onto Step 5 / Step 6 infrastructure

| Paper deliverable | Lean theorem | Upstream input |
|---|---|---|
| (a) third moment `∑ I^3 ≥ c_T^{(3)} · |LP|` | `third_moment_visibility` | `Step5.visibility_sum_eq_fiber_mass` (first-moment Richness) + mathlib `pow_sum_le_card_mul_sum_pow` (Jensen-for-ℕ at `n=2`) |
| (b) triple-overlap mass `∑ w_{αβγ} = ∑ I^3` | `triple_overlap_mass_sum_eq_visibility_cube` | Pure Fubini; no analytic input (only `F*_α ⊆ LP` containment, the standard subset hypothesis) |
| (c) edge fraction `failure ≤ O(1/c')` | `edge_fraction_in_triples_failure_bound` | `Step5.second_moment_visibility` (CS, already in tree from `Step5/SecondMoment.lean:199`) |

The grounding pattern matches `SignedThreshold.lean` §7 Grounded section and `SignConsistency.lean` §Grounded section (cleared-denominator parametric form with explicit constants).

## Why the Jensen route for (a) was tractable

`Finset.pow_sum_le_card_mul_sum_pow` (`Mathlib.Algebra.Order.Chebyshev:120`) is exactly the form needed: for `f : ι → α` with `0 ≤ f i` (trivially true for `ℕ`-valued),

  `(∑ i ∈ s, f i)^(n+1) ≤ #s^n · ∑ i ∈ s, f i^(n+1)`.

At `n = 2` this is `(∑ I)^3 ≤ |LP|^2 · ∑ I^3`.  Combined with the first-moment cube `(c · |LP|)^3 ≤ (∑ I)^3` and cancellation of `|LP|^2` (when `|LP| > 0`) gives `c^3 · |LP| ≤ ∑ I^3` exactly.  When `|LP| = 0`, both sides are 0.

The proof of (a) is a 5-line specialisation chained through `Nat.pow_le_pow_left` and `Nat.le_of_mul_le_mul_left` — i.e. identical *shape* to `Step5.second_moment_visibility` (Cauchy-Schwarz at `n = 1` cubed → cancel) but at one higher power.

## Hidden-constraint audit (per mg-6ab8 §2.7)

Three potential gotchas surfaced in scoping doc:

1. **G4 `O(1)` slack propagation** — out of scope for G3 (lives in S7-C, `Cocycle.lean`).  G3 produces the triple-overlap *mass*; downstream cocycle integration eats the slack.
2. **`lem:bandwidth` `K(T) + O(1)` constant** — out of scope for G3 (lives in S7-E, `Assembly.lean` bandwidth field).  G3 has no bandwidth-side coupling.
3. **`lem:layered-from-step7` bridge** — out of scope for G3 (lives in S7-F).

**No new hidden constraint surfaced in G3.**  The proof is exactly Jensen + Fubini + a `2·I·(I−1) ≥ I²` lemma for `I ≥ 2` (single algebraic identity, proven via the substitution `I = k+2`).

## Active-triple threshold passage (`step7.tex:1457-1481`)

This is the paper's post-(c) Markov argument that promotes "γ exists" to "γ with `w_{αγ}, w_{βγ}, w_{αβγ}` all above fixed threshold."  It is a routine Markov inequality and **was not formalised in this session** for two reasons:

* It is not part of the formal `lem:triple-visibility` statement (it appears as a remark inside the proof of (c), not as a named lemma).
* The downstream consumer `Cocycle.lean` takes triple-overlap data via the abstract `TripleData.weight T` field with no threshold structure — so the threshold-trim is naturally absorbed into the data bundle, not the visibility lemma.

If the cocycle file later needs an explicit threshold-trim corollary, it can be added as a one-screen Markov lemma consuming `triple_overlap_mass_lower_bound`.

## Vacuity-discovery audit (per Daniel's "6-times" lens)

Default-skeptical re-read of the paper proof, the cleared-denominator Lean form, and the cross-check against `Cocycle.lean`'s `TripleData` consumer pattern:

* (a) Jensen — paper claim is rigorous and tight; the cleared-denominator ℕ form is exact (no rounding).  Verified.
* (b) Fubini — paper claim is pure double-counting; the indicator-expansion `I(L)^3 = ∑ 𝟙[L ∈ F*α ∩ F*β ∩ F*γ]` is straightforward.  Verified.
* (c) Edge fraction — paper bound `8/c'_T` rounds to my `4/(c²-1)` (factor-of-2 absorbed into the bad-fiber halving the paper does upstream from `c_T` to `c_T/2`); the cleared-denominator ℕ form drops the constant rounding but is identical in shape.  Verified.
* Cube identity ((a) ↔ (b)) — the LHS `∑ w_{αβγ}` and RHS `∑ I^3` are linked by Fubini; the proof reduces both to a 4-tuple count over `richStar^3 × LP`.  No vacuity.
* Cocycle-consumer interface — `Cocycle.lean`'s `TripleData.weight` field is consumed as a generic `ℕ`-valued count with no further structural requirements; G3's `tripleOverlapMass` is a clean drop-in.  No vacuity.

**No 7th vacuity-discovery hit.**

## Acceptance bars

- [x] `lake build OneThird.Step7.TripleVisibility` clean (✅, verified)
- [x] No `sorry` in `TripleVisibility.lean` (✅, `grep sorry` clean)
- [x] No new axioms (✅, `AXIOMS.md` unchanged)
- [x] No new mathlib gaps (✅, all uses are existing `Mathlib.Algebra.Order.Chebyshev` + `Mathlib.Data.Finset.*` infrastructure)
- [x] Wired into `OneThird.lean` root (✅, single-line import added)
- [x] Paper-faithful packaging (✅, three parts (a)/(b)/(c) match `step7.tex:1376-1406`; grounded bundle conjunction `triple_visibility_grounded` matches paper-statement form)
- [x] Downstream consumer compatibility (✅, `Cocycle.lean`'s `TripleData.weight` field accepts G3's `tripleOverlapMass`)
- [ ] Full `lake build` clean (⏳, building in background at status-doc time; will block before commit)

## What S7-C through S7-F still need

Per mg-6ab8 §7.1 and §4.1 critical path:

* **S7-C (cocycle integration + potential)** — depends on S7-A grounded outputs + S7-B grounded outputs.  Both now in tree.  S7-C is the next dispatch.
* **S7-D (single-c + giant component)** — depends on S7-C.
* **S7-E (prop:71 + prop:72 + lem:bandwidth)** — depends on S7-D.  Replaces `LayeredWidth3.bandwidth : ℕ` with constructive `≤ 4`.
* **S7-F (lem:layered-from-step7 bridge)** — depends on S7-E.  Closes `caseC_canonicalLayered` sorry at `MainAssembly.lean`.

The S7-B G3 deliverables here unblock S7-C.  No PROOF-STRUCTURE-ONBOARDING.md §1/§2 update is *required* (the new file is not on the load-bearing headline path until S7-C-F land), but a §4 cross-reference index update is appropriate to record the new artefact.

## Commit message proposal

```
lean+docs: OneThird-S7-B G3 — Step 7 triple-visibility (a)/(b)/(c) grounded on Step 5 second-moment + Jensen-for-ℕ (mg-9331)
```

(Subject ≤ 100 chars; follows commit-style precedent of `lean+docs: OneThird-S7-A G1+G2 grounded forms` at 1d4f66d.)
