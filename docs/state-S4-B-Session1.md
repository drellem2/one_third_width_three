# State — S4-B — Session 1: Step 4 Lean port part 2 — density regularization + per-pair bound aggregation

**Ticket:** mg-1c08 (OneThird-S4-B: Step 4 Lean port part 2 —
density-regularization and per-pair bound aggregation).
**Branch:** `polecat-mg-1c08`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-3.
**Depends:** mg-7592 (S4-A `thm:step4` statement + BK-edge witness
family); merged at `87ddbab`.

**Scope.** Wave-3, second (final) ticket of the Step 4 sub-arc of the
Piece-1 (Steps 1-6 cascade port) decomposition. Completes the Step 4
per-pair incompatibility bound: aggregates the per-block rectangle
incompatibility into the BK-boundary lower bound
`|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|` (`step4.tex:93`, `thm:step4`) with
density regularization, the Markov-style aggregation arithmetic, and
full witness discharge. Consumes the S4-A witness skeleton.

---

## §0. Verdict — **GREEN-S4-B-delivered**

`lean/OneThird/Step4/PerPairBound.lean` (NEW, ~370 LoC) delivers the
density-regularization + per-pair aggregation half of Step 4, building
on the S4-A grounded witness family (`OneThird.Step4.WitnessGrounded`)
and the abstract Step 4 density-regularization scaffold
(`OneThird.Step4.DensityRegularization`):

* `cutEdgesOfSquare_disjoint_of_squareEdges_disjoint` — conflict
  squares with disjoint BK-edge sets contribute disjoint cut edges
  (`cutEdgesOfSquare ⊆ squareEdges`); the discharge route for the
  disjointness hypothesis from the `prop:G1` block partition.
* `witnessFamily_card_eq_sum` — **`prop:G1.2` grounded**
  (`step4.tex:152`, multiplicity 1): under block-disjointness the
  witness family `E_{α,β}` is a genuine disjoint union, so
  `|E_{α,β}| = ∑_i |cut edges of square i|` (via `Finset.card_biUnion`).
* `prop_G5_witnessFamily` — **`prop:G5` density regularization
  grounded** (`step4.tex:999`): aggregates the per-incoherent-block
  rectangle-incompatibility lower bound into a lower bound on
  `|E_{α,β}|`. Routes through the abstract `prop_G5_caseA` of
  `DensityRegularization.lean`, instantiating the per-square cut-edge
  count as the per-block boundary contribution.
* `markov_incoherent_mass` — **the Markov-style aggregation
  arithmetic** (`step4.tex:1140`): with per-block disagreement count
  `dis B` and mass `m B` (`dis B ≤ m B`), and incoherence threshold
  `m B ≤ 2·dis B` (the S4-A `BlockIncoherent` `½`-threshold),
  `2·(∑_B dis B) ≤ 2·(∑_{inc} m B) + ∑_B m B` — the genuine Markov
  split (coherent blocks lose `< ½` of their mass to disagreement).
* `incoherent_mass_lower_bound` — its operative corollary
  `δ·|Ω°| ≤ 2·M_inc` under the integer normalisation
  `δ·|Ω°| + |Ω°| ≤ 2·(∑_B dis B)`.
* `step4_perPair_bound` — **the full per-pair witness discharge**:
  from block-disjointness, the grounded per-block rectangle
  incompatibility, the Markov incoherent-mass bound, and the
  incoherent-mass sub-mass fact, delivers the grounded
  `Step4Conclusion` (= `thm:step4`) by discharging the `hWitLB`
  hypothesis of the S4-A reduction `thm_step4_grounded_witness`.
* `markov_incoherent_mass_nonvacuous` / `perPairBound_nonvacuous` —
  the S4-B non-vacuity acceptance witnesses (see §5).

`lake build OneThird.Step4.PerPairBound` is clean (exit 0). `lake build
OneThird` (full library) is clean. The new file produces no warnings.

**No `sorry`, no new axiom.** `#print axioms` confirms
`step4_perPair_bound`, `prop_G5_witnessFamily`, `markov_incoherent_mass`,
`witnessFamily_card_eq_sum`, and `perPairBound_nonvacuous` depend on
exactly `[propext, Classical.choice, Quot.sound]` (the three standard
mathlib axioms). No `sorryAx`, no project axiom.

---

## §1. What S4-B completes, and how it grounds it

S4-A (`thm_step4_grounded` / `thm_step4_grounded_witness`,
`WitnessGrounded.lean`) ported the **statement** of `thm:step4` and
reduced the theorem to a per-pair lower bound on the witness family:
given `W ⊆ ∂_BK S` and `c·δ·|Ω°| ≤ 2·|W| + 2·C·ε·|Ω°|`, deliver the
`thm:step4` inequality on `|∂_BK S|`. The `hWitLB` hypothesis
`c·δ·|Ω°| ≤ 2·|E_{α,β}| + 2·C·ε·|Ω°|` was left for S4-B.

S4-B **discharges `hWitLB`** from grounded per-block inputs. The
paper's `thm:step4` proof (`step4.tex:1135-1160`) is:

1. block decomposition `{B}` of `Ω°` (`prop:G1`);
2. Markov: incoherent blocks account for `≥ δ/2·|Ω°|`
   (`step4.tex:1140`);
3. `prop:G5` density regularization: per-block rectangle
   incompatibility summed → `|∂_BK S| ≥ c_G(δ − C_G·ε')|Ω°|`;
4. the factor `½` (= the `2` in `Step4Conclusion`) absorbs the Markov
   loss on incoherent-block mass.

The grounded port mirrors this exactly:

| paper step | grounded as |
|---|---|
| `prop:G1.2` (multiplicity 1, blocks partition) | `witnessFamily_card_eq_sum` (`E_{α,β}` is a disjoint union) |
| `prop:G5` density regularization | `prop_G5_witnessFamily` (∘ abstract `prop_G5_caseA`) |
| Markov on incoherent blocks (`step4.tex:1140`) | `markov_incoherent_mass` / `incoherent_mass_lower_bound` |
| `thm:step4` assembly + Markov `½` factor | `step4_perPair_bound` (∘ S4-A `thm_step4_grounded_witness`) |

The arithmetic of `step4_perPair_bound`: from `prop_G5_witnessFamily`,
`c·M_inc ≤ |E_{α,β}| + C·ε·M_inc` where `M_inc = ∑_i Rsize i` is the
incoherent overlap mass. Doubling and feeding `hMarkov : δ·|Ω°| ≤
2·M_inc` plus `hMass : M_inc ≤ |Ω°|`:
`c·δ·|Ω°| ≤ c·(2·M_inc) = 2·(c·M_inc) ≤ 2·|E_{α,β}| + 2·C·ε·M_inc ≤
2·|E_{α,β}| + 2·C·ε·|Ω°|` — exactly `hWitLB`. The factor `2` is the
Markov loss; `c` and `C` are unchanged across the assembly.

---

## §2. The Markov-style aggregation arithmetic (honest note)

`markov_incoherent_mass` is the genuine Markov split: a block is
*coherent* exactly when `¬(m B ≤ 2·dis B)`, i.e. `2·dis B < m B`, so
its disagreement is strictly below half its mass; the coherent blocks
therefore together lose at most `½·∑_{coh} m B ≤ ½·|Ω°|` of the
disagreement. The proved integer form is

  `2·(∑_B dis B) ≤ 2·(∑_{inc} m B) + ∑_B m B`.

`incoherent_mass_lower_bound` reads off `δ·|Ω°| ≤ 2·M_inc` when the
incoherence parameter `δ` is calibrated, in cleared-denominator integer
form, by `δ·|Ω°| + |Ω°| ≤ 2·(∑_B dis B)` — i.e. `δ·|Ω°|` does not
exceed twice the total disagreement minus the one-`|Ω°|` Markov slack.

This integer normalisation of `δ` is the honest cleared-denominator
image of the paper's `δ/2` Markov bound (`step4.tex:1140`): the paper
states *"incoherent blocks account for ≥ δ/2·|Ω°|"* with `δ` the
real-valued incoherence fraction; in the integer model the genuine
Markov content is the `2·∑dis ≤ 2·M_inc + |Ω°|` split, and the `+|Ω°|`
slack is exactly the `δ/2`-vs-`δ` normalisation difference. The
`step4_perPair_bound` top-level theorem takes the operative
`hMarkov : δ·|Ω°| ≤ 2·M_inc` as a named hypothesis (the
abstract-hypothesis style of the whole Step 4 scaffold);
`incoherent_mass_lower_bound` is the supplied discharge route for it.

---

## §3. Scope boundary (honest)

This ticket ports the **aggregation** half of Step 4 part 2 — density
regularization, the Markov-style arithmetic, and the witness→boundary
discharge — all grounded, 0-sorry, no new axiom. Out of scope,
faithfully so:

* **The per-block rectangle 2×2 incompatibility count**
  (`lem:rect-stable-area`, `step4.tex:543`; `lem:rect-stable`,
  `lem:many-nonconst`, `lem:square-multiplicity`). This is **already
  formalised abstractly** in `OneThird.Step4.RectangleModel`
  (`rect_stable_area_nonconst_lb`, `lem_many_nonconst`,
  `square_mult_hor_card`). Its output — the per-block lower bound
  `c·|R_B| ≤ |E_B| + C·ε·|R_B|` — enters `step4_perPair_bound` as the
  named hypothesis `hPerBlock`. Grounding the abstract `errCount` /
  `ConstantOn` rectangle counting onto `cutEdgesOfSquare` edge-counts
  (which needs the `lem:square-multiplicity` greedy edge-selection)
  would re-do S4-A/RectangleModel territory; the honest scope line is
  the aggregation, with the per-block bound as the named input. The
  non-vacuity (§5) discharges `hPerBlock` **concretely** at the atomic
  scale via the S4-A `lem:22` (`lem22_bk`): a genuine conflict square
  contributes a genuine BK cut edge.
* **The block-disjointness of the witness family** (`prop:G1.2`,
  multiplicity 1). `step4_perPair_bound` takes the disjointness of the
  incoherent squares' cut-edge sets as the named hypothesis `hdisj`;
  `cutEdgesOfSquare_disjoint_of_squareEdges_disjoint` is the supplied
  discharge route from BK-edge disjointness (squares in distinct
  blocks occupy disjoint rectangles). The block-decomposition object
  `prop:G1` is the abstract `BlockDecomp` of `RectangleModel.lean`.
* **The bad-block Markov bound** (`prop:G2-step4`, `step4.tex:271`):
  `markov_badblock` is already fully proved in `RectangleModel.lean`;
  its `½·ε'·|Ω°|` bad-mass bound is absorbed into the `C·ε`-slack of
  `Step4Conclusion` and is not re-grounded here.

The abstract Step 4 files (`RectangleModel.lean`,
`DensityRegularization.lean`, `Step4Theorem.lean`) and the S4-A
`WitnessGrounded.lean` are **unchanged**; `PerPairBound.lean` is purely
additive (the only other change is the `+1` import line in
`lean/OneThird.lean`).

---

## §4. What this port consumes

* **S4-A** (`OneThird.Step4.WitnessGrounded`) — `witnessFamily`,
  `cutEdgesOfSquare`, `squareEdges`, `bkBoundary`, `lem22_bk`
  (`lem:22`), `Step4Conclusion`, `thm_step4_grounded_witness`,
  `IsConflictSquare`, and the non-vacuity scaffold (`gridSquare`,
  `gridSquare_isCommSquare`, `witnessGrounded_nonvacuous`).
* **Step 4 abstract scaffold**
  (`OneThird.Step4.DensityRegularization`) — the abstract `prop:G5`
  case-A aggregation `prop_G5_caseA`; `prop_G5_witnessFamily` grounds
  it on the concrete BK witness family, so the grounded port genuinely
  *consumes* the abstract density-regularization lemma rather than
  re-deriving it.

---

## §5. Non-vacuity (mg-1c08 acceptance bar)

Two acceptance witnesses, no `Subsingleton`-on-empty baseline:

* `markov_incoherent_mass_nonvacuous` — the Markov aggregation fires
  on a genuine **two-block** family with masses `(3, 4)` and
  disagreement counts `(2, 0)`: block `0` is genuinely incoherent
  (`3 ≤ 2·2`), block `1` genuinely coherent (`¬ 4 ≤ 2·0`), and the
  incoherent-block filter is genuinely non-empty. The Markov bound
  `2·(2+0) ≤ 2·3 + (3+4)` holds non-vacuously.
* `perPairBound_nonvacuous` — instantiates the full aggregation at the
  genuine **width-3 non-chain grid poset `Fin 3 × Fin 3`** (the S4-A
  non-vacuity poset, reused via `witnessGrounded_nonvacuous`):
  - **(poset)** `Fin 3 × Fin 3` has width exactly `3` and is not a
    chain;
  - **(conflict square)** `gridSquare` is a *genuine* conflict square
    — a real commuting `2×2` BK square on a poset carrying two
    disjoint incomparable pairs (`gridLinExt` BK moves at positions
    `1`, `3`);
  - **(density regularization)** `prop_G5_witnessFamily` fires; the
    per-block hypothesis `hPerBlock` is discharged **concretely** by
    `lem22_bk` — the genuine conflict square contributes a genuine BK
    cut edge, so `|cutEdgesOfSquare| ≥ 1`;
  - **(per-pair bound)** `step4_perPair_bound` fires with strictly
    positive `δ = 1`, `|Ω°| = 1`, delivering the grounded
    `Step4Conclusion` (`thm:step4`).

A genuine `2×2` BK conflict square requires a poset with at least four
elements supporting two disjoint incomparable pairs; `Fin 3 × Fin 3`
carries one and the 3-element antichain structurally cannot — so the
witness discharge fires on a *genuine* square, and the per-block
rectangle incompatibility `hPerBlock` is discharged by a real cut
edge, not a degenerate one.

---

## §6. Files

* `lean/OneThird/Step4/PerPairBound.lean` — NEW (~370 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S4-B-Session1.md` — this file.
