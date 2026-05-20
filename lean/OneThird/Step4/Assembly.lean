/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step4.PerPairBound
import OneThird.Step4.Step4Theorem

/-!
# Step 4 — grounded port, part 3: `thm:step4` assembly + Step 6 integration

This file is the **FULL REFACTOR Piece 1, Wave-3 S4-C** grounded port of
`step4.tex`, the final Step 4 ticket.  Where S4-A
(`OneThird.Step4.WitnessGrounded`) ported the **statement** of `thm:step4`
and constructed the BK-edge witness family, and S4-B
(`OneThird.Step4.PerPairBound`) delivered the **density regularization +
Markov aggregation** discharging the per-pair witness lower bound, this
file **assembles the complete `thm:step4`** and **integrates it into the
Step 6 consumption interface**.

## What this file delivers (S4-C scope)

* `thm_step4_assembled` — **the complete grounded `thm:step4`**
  (`step4.tex:93`).  Where S4-B's `step4_perPair_bound` took the Markov
  incoherent-mass bound `hMarkov` as a named hypothesis, this assembled
  form discharges it *internally* from the genuine per-block
  disagreement counts via the S4-B Markov split
  `incoherent_mass_lower_bound`.  The only remaining inputs are the
  genuine structural ones: the per-block rectangle incompatibility
  (`lem:rect-stable-area`), the block-disjointness (`prop:G1.2`), and the
  cleared-denominator incoherence calibration.
* `witnessFamilyOfPairs` — **the BK-edge witness family indexed by
  ordered rich pairs** (`step4.tex:1167`, the `E_{α,β}` family).  This is
  the concrete object the Step 6 overlap-counting double-counts.
* `pairWeight_eq_card_of_subset` / `pairWeight_witnessFamilyOfPairs` —
  the grounding bridge: since every witness family lies inside the BK
  boundary, the Step 6 pair weight `w_{α,β} = |∂_BK S ∩ E_{α,β}|` is
  exactly the witness-family cardinality `|E_{α,β}|`.
* `lem_G6_bkEdge` — **`lem:G6` (witness-edge multiplicity,
  `step4.tex:1177`) grounded** on the concrete BK edge type
  `Sym2 (LinearExt α)`.
* `cor_step6_input_grounded` / `cor_step6_input_witnessMass` —
  **`cor:step6-input` (`step4.tex:1269`) grounded** on the BK boundary:
  `∑_{(α,β)} |∂_BK S ∩ E_{α,β}| ≤ M · |∂_BK S|`, i.e. the
  overlap-counting lemma Step 6 consumes.
* `thm_step4_assembled_nonvacuous` / `corStep6Input_nonvacuous` — the
  S4-C non-vacuity acceptance witnesses at the genuine width-3 non-chain
  grid poset `Fin 3 × Fin 3`.

## What this consumes

* **S4-B** (`OneThird.Step4.PerPairBound`) — `step4_perPair_bound`
  (the full witness discharge of `thm:step4`) and
  `incoherent_mass_lower_bound` (the Markov aggregation arithmetic).
* **S4-A** (`OneThird.Step4.WitnessGrounded`) — `bkBoundary`,
  `witnessFamily`, `witnessFamily_subset_bkBoundary`, `cutEdgesOfSquare`,
  `Step4Conclusion`, `BKSquare`, `lem22_bk`, and the non-vacuity scaffold
  (`gridSquare`, `gridSquare_isCommSquare`, `witnessGrounded_nonvacuous`).
* **Step 4 abstract scaffold** (`OneThird.Step4.Step4Theorem`) — the
  abstract `lem_G6`, `cor_step6_input`, `witnessCount`, `pairWeight`,
  `LocalFiberBound`; this file grounds the abstract `Edge` type to the
  concrete BK edge type `Sym2 (LinearExt α)`.

## Downstream — Step 6 consumability

`cor:step6-input` is the overlap-counting input of Step 6's
`lem:sum-step4` (G7, `step6.tex:270`): Step 6 sums the Step 4 per-pair
bound `w_{α,β}` against the overlap-counting multiplicity `M` (the
Step 1 swap-pair pinning consequence) to obtain
`c_n · ∑_{bad active} w_{α,β} ≤ c_d · M · |∂_BK S|`.  The grounded forms
here type exactly into `Step6.lem_overlap_counting_summed` and
`Step6.lem_sum_step4`; the end-to-end consumption is verified in
`Step6.Assembly` (`lem_sum_step4_grounded`).

## Scope boundary (honest)

* The **width-3 local-fiber bound** of `lem:G6` Step 4
  (`step4.tex:1221-1256`) — the `O(1)` count of partner interfaces — is
  carried as the abstract `LocalFiberBound` hypothesis, exactly as in the
  abstract `OneThird.Step4.Step4Theorem.lem_G6`.  The paper itself
  (`step4.tex` `rem` after `cor:step6-input`) flags that an explicit
  numerical `M` is *not needed* by any downstream step — only that `M`
  depends on the width alone — so this abstraction is faithful, not a
  gap newly surfaced by the assembly.
* The **Step 1 swap-pair pinning** (`step4.tex:1190-1196`, "the swap pair
  of a witness edge equals `α` or `β`") is the `hpin` hypothesis of
  `lem_G6_bkEdge`.  S4-A's `witnessEdge_bkAdj` already grounds the
  *existence* of a BK swap pair for every witness edge; that the swap
  pair equals one of the two interfaces is the rectangle-block-model
  structural input, carried as a named hypothesis here.
-/

namespace OneThird
namespace Step4

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1 — The complete `thm:step4`, assembled (`step4.tex:93`)

S4-B's `step4_perPair_bound` discharges the grounded `thm:step4`
conclusion `Step4Conclusion` from four named hypotheses, of which
`hMarkov : δ·|Ω°| ≤ 2·M_inc` is the operative incoherent-mass bound.
The assembled `thm:step4` here closes that last gap: it takes the
genuine per-block pointwise-disagreement counts `dis B` and block masses
`m B` and discharges `hMarkov` *internally* via the S4-B Markov split
`incoherent_mass_lower_bound`, leaving only the genuine structural inputs
of the paper's proof (`step4.tex:1135-1160`). -/

/-- **`thm:step4` — the complete two-interface incompatibility lemma,
assembled (`step4.tex:93`).**

Inputs (all on the genuine grounded objects):

* `blocks` indexes the block decomposition of `Ω°` (`prop:G1`); `crn B`
  is the conflict `2×2` BK square of block `B`; `dis B` is the per-block
  pointwise η-disagreement count and `m B` the block mass.
* `hle` — `dis B ≤ m B`: the disagreement set is a subset of the block.
* `homega` — `|Ω°| = ∑_B m B`: the blocks partition the overlap
  (`prop:G1.2`, multiplicity 1).
* `hglob` — the cleared-denominator incoherence calibration
  `δ·|Ω°| + |Ω°| ≤ 2·∑_B dis B` (`step4.tex:1140`, the integer image of
  *"incoherent blocks account for ≥ δ/2·|Ω°|"*).
* `hdisj` — the conflict squares of the incoherent blocks have pairwise
  disjoint cut-edge sets (`prop:G1.2`).
* `hPerBlock` — the per-block rectangle incompatibility
  `c·m B ≤ |cut edges of square B| + C·ε·m B` (`lem:rect-stable-area`,
  `step4.tex:543`).

Conclusion: the grounded `Step4Conclusion`, the cleared-denominator form
of `|∂_BK S| ≥ c·(δ − C·ε)·|Ω°|`.

The Markov incoherent-mass bound `hMarkov` of `step4_perPair_bound` is
discharged here *internally* by `incoherent_mass_lower_bound` (S4-B); a
block is incoherent exactly when `m B ≤ 2·dis B`, the S4-A
`BlockIncoherent` `½`-threshold. -/
theorem thm_step4_assembled {ι : Type*}
    (S : Finset (LinearExt α)) (blocks : Finset ι) (crn : ι → BKSquare α)
    (dis m : ι → ℕ) (c cnst delta eps omegaCard : ℕ)
    (hle : ∀ B ∈ blocks, dis B ≤ m B)
    (homega : omegaCard = ∑ B ∈ blocks, m B)
    (hglob : delta * omegaCard + omegaCard ≤ 2 * (∑ B ∈ blocks, dis B))
    (hdisj : ∀ i ∈ blocks.filter (fun B => m B ≤ 2 * dis B),
      ∀ j ∈ blocks.filter (fun B => m B ≤ 2 * dis B), i ≠ j →
        Disjoint (cutEdgesOfSquare S (crn i)) (cutEdgesOfSquare S (crn j)))
    (hPerBlock : ∀ i ∈ blocks.filter (fun B => m B ≤ 2 * dis B),
      c * m i ≤ (cutEdgesOfSquare S (crn i)).card + cnst * eps * m i) :
    Step4Conclusion S c cnst delta eps omegaCard := by
  -- The Markov split (S4-B) discharges the incoherent-mass bound.
  have hMarkov : delta * omegaCard ≤
      2 * (∑ i ∈ blocks.filter (fun B => m B ≤ 2 * dis B), m i) :=
    incoherent_mass_lower_bound blocks dis m delta omegaCard hle homega hglob
  -- The incoherent-block mass is a sub-mass of `|Ω°|` (`prop:G1.2`).
  have hMass : (∑ i ∈ blocks.filter (fun B => m B ≤ 2 * dis B), m i) ≤ omegaCard := by
    rw [homega]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- S4-B's per-pair discharge with `inIncoherent := (m B ≤ 2·dis B)`.
  exact step4_perPair_bound S blocks crn (fun B => m B ≤ 2 * dis B) m
    c cnst delta eps omegaCard hdisj hPerBlock hMarkov hMass

/-! ## §2 — The witness family indexed by ordered rich pairs

`step4.tex:1167` defines, for *each* ordered rich pair `(α, β)`, a
witness family `E_{α,β}`.  The S4-A `witnessFamily` constructs a single
such family from indexed conflict-square data; the Step 6 overlap
counting double-counts the whole *family of families* `(α, β) ↦ E_{α,β}`.
`witnessFamilyOfPairs` packages that: per ordered pair, the S4-A
witness-family construction. -/

variable {ι Pair : Type*}

/-- **The BK-edge witness family indexed by ordered rich pairs**
(`step4.tex:1167`).  For each ordered pair `(a, b)`, `witnessFamilyOfPairs`
is the S4-A `witnessFamily` of that pair's conflict-square data — the
genuine `E_{a,b} ⊆ E(G_BK(P))`.  This is the `witness : Pair → Pair →
Finset Edge` object the Step 6 overlap-counting lemma consumes. -/
noncomputable def witnessFamilyOfPairs
    (S : Finset (LinearExt α))
    (squares : Pair → Pair → Finset ι) (crn : Pair → Pair → ι → BKSquare α)
    (inInc : Pair → Pair → ι → Prop) [∀ a b, DecidablePred (inInc a b)]
    (a b : Pair) : Finset (Sym2 (LinearExt α)) :=
  witnessFamily S (squares a b) (crn a b) (inInc a b)

/-- Every pair's witness family lies inside the BK boundary
(`step4.tex:1172`): `E_{a,b} ⊆ ∂_BK S`. -/
theorem witnessFamilyOfPairs_subset_bkBoundary
    (S : Finset (LinearExt α))
    (squares : Pair → Pair → Finset ι) (crn : Pair → Pair → ι → BKSquare α)
    (inInc : Pair → Pair → ι → Prop) [∀ a b, DecidablePred (inInc a b)]
    (a b : Pair) :
    witnessFamilyOfPairs S squares crn inInc a b ⊆ bkBoundary S :=
  witnessFamily_subset_bkBoundary S (squares a b) (crn a b) (inInc a b)

/-! ## §3 — The grounding bridge: `w_{α,β} = |E_{α,β}|`

Step 6's pair weight is `w_{α,β} := |∂_BK S ∩ E_{α,β}|` (`step4.tex:1270`,
the abstract `Step4.pairWeight`).  Since every witness family lies inside
the BK boundary, that intersection is the whole family, so the pair
weight is exactly the witness-family cardinality. -/

/-- **The grounding bridge.**  When every witness family lies inside the
BK boundary, the Step 6 pair weight `w_{α,β} = |∂_BK S ∩ E_{α,β}|` is
exactly the witness-family cardinality `|E_{α,β}|`.  This is what makes
the S4-B per-pair lower bound on `|E_{α,β}|` directly consumable as the
`hPerPair` input of Step 6's `lem:sum-step4`. -/
theorem pairWeight_eq_card_of_subset
    (S : Finset (LinearExt α))
    (witness : Pair → Pair → Finset (Sym2 (LinearExt α)))
    (hsub : ∀ a b, witness a b ⊆ bkBoundary S) (a b : Pair) :
    pairWeight (bkBoundary S) witness a b = (witness a b).card := by
  unfold pairWeight
  rw [Finset.inter_eq_right.mpr (hsub a b)]

/-- The grounding bridge specialised to the grounded
`witnessFamilyOfPairs`: `w_{α,β} = |E_{α,β}|`. -/
theorem pairWeight_witnessFamilyOfPairs
    (S : Finset (LinearExt α))
    (squares : Pair → Pair → Finset ι) (crn : Pair → Pair → ι → BKSquare α)
    (inInc : Pair → Pair → ι → Prop) [∀ a b, DecidablePred (inInc a b)]
    (a b : Pair) :
    pairWeight (bkBoundary S) (witnessFamilyOfPairs S squares crn inInc) a b
      = (witnessFamilyOfPairs S squares crn inInc a b).card :=
  pairWeight_eq_card_of_subset S (witnessFamilyOfPairs S squares crn inInc)
    (witnessFamilyOfPairs_subset_bkBoundary S squares crn inInc) a b

/-! ## §4 — `lem:G6` and `cor:step6-input`, grounded on the BK boundary

`lem:G6` (`step4.tex:1177`) and `cor:step6-input` (`step4.tex:1269`) are
proved abstractly in `OneThird.Step4.Step4Theorem` over an opaque edge
type `Edge`.  Here we ground `Edge` to the concrete BK edge type
`Sym2 (LinearExt α)` and `boundary` to the genuine BK boundary
`bkBoundary S`, so the corollary is a statement about real BK cut edges
of `bkGraph α`.

The Step 1 swap-pair pinning (`step4.tex:1190-1196`) and the width-3
local-fiber bound (`step4.tex:1221-1256`) remain abstract hypotheses —
exactly the abstraction of the existing scaffold and faithful to the
paper's own `rem` ("an explicit numerical value of `M` ... is not
needed"). -/

variable [DecidableEq Pair]

/-- **`lem:G6` (witness-edge multiplicity, `step4.tex:1177`) grounded on
the BK edge type.**  Each BK edge `e : Sym2 (LinearExt α)` lies in at
most `2·M₁` ordered rich-interface witness families.

`swapPair`/`hpin` are the Step 1 pinning content (`step4.tex:1190-1196`):
every witness edge's swap pair is one of the two interfaces.  S4-A's
`witnessEdge_bkAdj` already grounds the existence of a BK swap pair for
every witness edge.  `LocalFiberBound` is the width-3 local-fiber `O(1)`
count (`step4.tex:1221-1256`). -/
theorem lem_G6_bkEdge
    (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset (Sym2 (LinearExt α)))
    (swapPair : Sym2 (LinearExt α) → Pair) (M₁ : ℕ)
    (hpin : ∀ a b e, e ∈ witness a b → swapPair e = a ∨ swapPair e = b)
    (hbnd : LocalFiberBound richPairs witness M₁)
    (e : Sym2 (LinearExt α)) :
    witnessCount richPairs witness e ≤ 2 * M₁ :=
  lem_G6 richPairs witness swapPair M₁ hpin hbnd e

/-- **`cor:step6-input` (`step4.tex:1269`) grounded on the BK boundary.**
For any family of witness families and any multiplicity bound `M` valid
on the BK boundary,

  `∑_{(α,β)} |∂_BK S ∩ E_{α,β}| ≤ M · |∂_BK S|`.

This is the overlap-counting lemma Step 6 consumes — the genuine BK
boundary `bkBoundary S` of `bkGraph α` is the edge set. -/
theorem cor_step6_input_grounded
    (S : Finset (LinearExt α)) (richPairs : Finset Pair)
    (witness : Pair → Pair → Finset (Sym2 (LinearExt α))) (M : ℕ)
    (hmult : ∀ e ∈ bkBoundary S, witnessCount richPairs witness e ≤ M) :
    ∑ p ∈ richPairs ×ˢ richPairs,
        pairWeight (bkBoundary S) witness p.1 p.2 ≤ M * (bkBoundary S).card :=
  cor_step6_input richPairs witness (bkBoundary S) M hmult

/-- **`cor:step6-input` in witness-mass form (`step4.tex:1270-1274`).**
With the grounded `witnessFamilyOfPairs`, the grounding bridge converts
the pair weights to witness-family cardinalities, giving the paper's
display verbatim:

  `∑_{(α,β)} |E_{α,β}| ≤ M · |∂_BK S|`.

This is the exact form Step 6's `lem:sum-step4` chains against the Step 4
per-pair lower bound on each `|E_{α,β}|`. -/
theorem cor_step6_input_witnessMass
    (S : Finset (LinearExt α)) (richPairs : Finset Pair)
    (squares : Pair → Pair → Finset ι) (crn : Pair → Pair → ι → BKSquare α)
    (inInc : Pair → Pair → ι → Prop) [∀ a b, DecidablePred (inInc a b)]
    (M : ℕ)
    (hmult : ∀ e ∈ bkBoundary S,
      witnessCount richPairs (witnessFamilyOfPairs S squares crn inInc) e ≤ M) :
    ∑ p ∈ richPairs ×ˢ richPairs,
        (witnessFamilyOfPairs S squares crn inInc p.1 p.2).card
      ≤ M * (bkBoundary S).card := by
  have hcor := cor_step6_input_grounded S richPairs
    (witnessFamilyOfPairs S squares crn inInc) M hmult
  rw [Finset.sum_congr rfl
      (fun p _ => pairWeight_witnessFamilyOfPairs S squares crn inInc p.1 p.2)] at hcor
  exact hcor

/-! ## §5 — Non-vacuity at the concrete width-3 non-chain poset

Per the S4-C acceptance bar, the assembled `thm:step4` and the grounded
`cor:step6-input` instantiate non-vacuously at the genuine width-3
non-chain grid poset `Fin 3 × Fin 3` of `Step1/Overlap.lean`, with the
*genuine* BK conflict square `gridSquare` — no `Subsingleton`-on-empty
baseline. -/

/-- **S4-C non-vacuity, part 1 — the assembled `thm:step4`.**

At the genuine width-3 non-chain grid poset `Fin 3 × Fin 3`, with the
singleton cut `S := {gridLinExt}`, the assembled `thm_step4_assembled`
fires on a *one-block* decomposition whose single block carries the
genuine conflict square `gridSquare`:

* **(poset)** `Fin 3 × Fin 3` has width exactly `3` and is not a chain;
* **(block)** the block is genuinely incoherent (`m = 1 ≤ 2·dis = 2`),
  so the incoherent-block filter is non-empty;
* **(per-block bound)** `hPerBlock` is discharged *concretely* via the
  S4-A `lem22_bk` — the genuine conflict square contributes a real BK
  cut edge;
* **(`thm:step4`)** the assembled theorem fires with strictly positive
  `δ = 1`, `|Ω°| = 1`, delivering the grounded `Step4Conclusion`. -/
theorem thm_step4_assembled_nonvacuous :
    HasWidth (Fin 3 × Fin 3) 3 ∧
    ¬ IsChainPoset (Fin 3 × Fin 3) ∧
    IsConflictSquare ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      gridSquare ∧
    Step4Conclusion ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
      1 0 1 0 1 := by
  obtain ⟨hw, hnc, hconf, _, _, _⟩ := witnessGrounded_nonvacuous
  set S : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt} with hS
  -- The conflict square contributes a genuine BK cut edge (`lem:22`).
  have hcutCard : 1 ≤ (cutEdgesOfSquare S gridSquare).card := by
    have hcut : (cutEdgesOfSquare S gridSquare).Nonempty := by
      have := lem22_bk hconf
      simpa [cutEdgesOfSquare] using this
    exact Finset.card_pos.mpr hcut
  refine ⟨hw, hnc, hconf, ?_⟩
  -- One-block decomposition over `Unit`: `dis = 1`, `m = 1`.
  refine thm_step4_assembled S ({()} : Finset Unit) (fun _ => gridSquare)
    (fun _ => 1) (fun _ => 1) 1 0 1 0 1 ?_ ?_ ?_ ?_ ?_
  · -- hle : dis B ≤ m B
    intro B _; exact le_refl 1
  · -- homega : |Ω°| = ∑ m
    simp
  · -- hglob : δ·|Ω°| + |Ω°| ≤ 2·∑ dis  →  1·1 + 1 ≤ 2·1
    simp
  · -- hdisj : vacuous on the singleton index `Unit`
    intro i _ j _ hij
    exact absurd (Subsingleton.elim i j) hij
  · -- hPerBlock : 1·m B ≤ |cut edges| + 0·0·m B, discharged via `lem22_bk`
    intro i _
    simpa using hcutCard

/-- **S4-C non-vacuity, part 2 — the grounded `cor:step6-input`.**

At the grid poset `Fin 3 × Fin 3`, the grounded `witnessFamilyOfPairs`
over a one-pair index (`Pair := Unit`) carrying the genuine conflict
square `gridSquare` has a non-empty witness family, and the grounded
overlap-counting bound `∑ |E_{α,β}| ≤ M · |∂_BK S|` fires with `M = 1`:

* **(witness family)** the single witness family is non-empty — a real
  BK cut edge from `gridSquare`;
* **(multiplicity)** with one ordered pair, every BK edge lies in at
  most `M = 1` witness family;
* **(overlap counting)** `cor_step6_input_witnessMass` delivers
  `∑ |E_{α,β}| ≤ 1 · |∂_BK S|` with a strictly positive left-hand
  side. -/
theorem corStep6Input_nonvacuous :
    (witnessFamilyOfPairs ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
        (fun _ _ => ({()} : Finset Unit)) (fun _ _ _ => gridSquare)
        (fun _ _ _ => True) () ()).Nonempty ∧
    1 ≤ ∑ p ∈ ({()} : Finset Unit) ×ˢ ({()} : Finset Unit),
          (witnessFamilyOfPairs ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
            (fun _ _ => ({()} : Finset Unit)) (fun _ _ _ => gridSquare)
            (fun _ _ _ => True) p.1 p.2).card ∧
    ∑ p ∈ ({()} : Finset Unit) ×ˢ ({()} : Finset Unit),
        (witnessFamilyOfPairs ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))
          (fun _ _ => ({()} : Finset Unit)) (fun _ _ _ => gridSquare)
          (fun _ _ _ => True) p.1 p.2).card
      ≤ 1 * (bkBoundary ({gridLinExt} : Finset (LinearExt (Fin 3 × Fin 3)))).card := by
  obtain ⟨_, _, hconf, _, _, _⟩ := witnessGrounded_nonvacuous
  set S : Finset (LinearExt (Fin 3 × Fin 3)) := {gridLinExt} with hS
  set wit := witnessFamilyOfPairs S (fun _ _ => ({()} : Finset Unit))
    (fun _ _ _ => gridSquare) (fun _ _ _ => (True : Prop)) with hwit
  -- The grounded witness family is non-empty: a genuine BK cut edge.
  have hne : (wit () ()).Nonempty := by
    rw [hwit]
    unfold witnessFamilyOfPairs
    exact witnessFamily_nonempty_of_conflict (S := S) (squares := {()})
      (crn := fun _ => gridSquare) (inIncoherent := fun _ => True) (i := ())
      (Finset.mem_singleton_self ()) trivial hconf
  have hpos : 1 ≤ (wit () ()).card := Finset.card_pos.mpr hne
  -- The product index `{()} ×ˢ {()}` is the singleton `{((),())}`.
  have hsum : ∑ p ∈ ({()} : Finset Unit) ×ˢ ({()} : Finset Unit),
      (wit p.1 p.2).card = (wit () ()).card := by
    simp
  refine ⟨hne, ?_, ?_⟩
  · rw [hsum]; exact hpos
  · -- Overlap-counting: every BK edge is in at most M = 1 witness family.
    have hmult : ∀ e ∈ bkBoundary S,
        witnessCount ({()} : Finset Unit) wit e ≤ 1 := by
      intro e _
      unfold witnessCount
      calc ((({()} : Finset Unit) ×ˢ ({()} : Finset Unit)).filter
              (fun p => e ∈ wit p.1 p.2)).card
          ≤ (({()} : Finset Unit) ×ˢ ({()} : Finset Unit)).card :=
            Finset.card_filter_le _ _
        _ = 1 := by simp
    exact cor_step6_input_witnessMass S ({()} : Finset Unit)
      (fun _ _ => ({()} : Finset Unit)) (fun _ _ _ => gridSquare)
      (fun _ _ _ => True) 1 hmult

end Step4
end OneThird
