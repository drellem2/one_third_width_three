/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import OneThird.Poset
import OneThird.LinearExtension
import OneThird.RichPair
import OneThird.Step1.Corollaries
import OneThird.Step2.Conclusion
import OneThird.Step3.Step3Theorem
import OneThird.Step4.Step4Theorem
import OneThird.Step5.Dichotomy
import OneThird.Step6.Assembly
import OneThird.Step7.Assembly

/-!
# Bridge: Steps 1–7 abstract theorems, specialised to a finite poset

The Step 1–7 files prove their results in the abstract
numeric / `Finset`-level style used throughout the Lean scaffold:
the hypotheses are `ℕ`-valued inequalities and abstract `Finset`s
over caller-supplied index types (`Pair`, `Edge`, `LinExt`, …), and
the conclusions are similarly abstract.  For example, `thm_step6`
(`Step6/Assembly.lean:246`) proves a pure arithmetic disjunction on
`ℕ` — no poset appears in its statement.

This file wires each step's top-level abstract theorem to the actual
poset data: fixing `α : Type*` with `[PartialOrder α] [Fintype α]
[DecidableEq α]`, we specialise the index types to poset-native
carriers (`LinearExt α`, `α × α`, pair Finsets of `α`) and the
numeric quantities to poset-level counts (`edgeBoundary S`,
`visibility richPairs Fstar L`, `Fintype.card α`, …).

Each bridge theorem's proof is a one-line invocation of the
corresponding abstract step theorem.  No new mathematical content is
produced — the file is pure plumbing — but it makes the intended
poset-level shape of every step explicit in Lean, and closes the gap
flagged in the audit (`README.md`, "Verdict" §4): the Step 1–7
abstract statements now have named poset-specialised counterparts
that downstream work can target when constructing `MainTheoremInputs`.

## Structure

One section per step.  Each section opens the relevant `Step N`
namespace so the abstract theorem can be referenced briefly.

* `Bridge.step1` — Step 1 local interface theorem (already poset-level
  in `OneThird.localInterfaceTheorem`; we alias it for symmetry with
  the other steps).
* `Bridge.step2_conclusion` — Step 2 output (`thm:step2`) with fibers
  indexed by `α × α` and BK-boundary `B ⊆ LinearExt α`.
* `Bridge.step3` — Step 3 assembly (`thm:step3`) with overlap states
  drawn from `LinearExt α`.
* `Bridge.step4` — Step 4 cleared-denominator inequality (`thm:step4`)
  with BK boundary of a cut `S ⊆ LinearExt α`.
* `Bridge.step5` / `Bridge.step5_second_moment` — Step 5 dichotomy
  (`thm:step5`) with rich-pair visibility on `LinearExt α`.
* `Bridge.step6` — Step 6 dichotomy (`thm:step6`) with BK-boundary
  of a cut `S ⊆ LinearExt α`.
* `Bridge.step7` — Step 7 assembly (`thm:step7`) with
  `Pair := α × α`, `Edge := LinearExt α × LinearExt α`,
  `Vertex := α`.

All proofs are sorry-free.
-/

namespace OneThird
namespace Bridge

open Finset
open scoped BigOperators

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### Step 1 -/

/-- **Step 1 bridge** — the local interface theorem of `step1.tex`
§`sec:step1-main`, re-exported on a finite poset `α`.

`OneThird.localInterfaceTheorem` (in `RichPair.lean`) is already
stated at the poset level; we re-expose it here so that every step
has a uniform `Bridge.stepN` entry point. -/
theorem step1 (hP : HasWidthAtMost α 3)
    (T : ℕ) (x y : α) (hxy : IsRich T x y) :
    (∀ L : LinearExt α,
        (localCoord x y L).1 ≤ commonNbhdLength x y ∧
        (localCoord x y L).2 ≤ commonNbhdLength x y) ∧
    (goodFiberSet x y ∪ badSet x y = Finset.univ) ∧
    (Disjoint (goodFiberSet x y) (badSet x y)) :=
  OneThird.localInterfaceTheorem hP T x y hxy

/-! ### Step 2 -/

/-- **Step 2 bridge** — `thm:step2` (`step2.tex`) specialised with
the fiber index set drawn from pairs of `α` and the BK-boundary
cut `B` drawn from `LinearExt α`.

The abstract `Step2.Conclusion.step2_conclusion` takes generic
`R : Finset α'` and `B : Finset β` as index sets.  In the Step 8
usage these become the rich-pair family (parameterised by pairs
`α × α`) and a BK-boundary set on linear extensions.  The bridge
fixes the substitution and threads the abstract theorem. -/
theorem step2_conclusion
    (R : Finset (α × α)) (B : Finset (LinearExt α))
    (internal : (α × α) → (LinearExt α) → Prop) [DecidableRel internal]
    {K : ℕ} (hK : Step2.FiberAvg.BoundedMultiplicity R B internal K)
    {η : ℕ} (hη : 0 < η)
    (D A : (α × α) → Finset (ℤ × ℤ))
    (hAD : ∀ r ∈ R, A r ⊆ D r)
    (fibMass : (α × α) → ℕ)
    {κ m : ℕ} (hBκ : B.card ≤ κ * m) :
    η * (∑ r ∈ Step2.PerFiber.badFiberSet R B internal η fibMass, fibMass r)
        ≤ K * κ * m ∧
    (∀ r ∈ R, ∃ M : Finset (ℤ × ℤ),
      Step2.WeakGrid.IsStaircasePlus (D r) M ∧
      (symmDiff (A r) M).card ≤ (D r).card) :=
  Step2.Conclusion.step2_conclusion R B internal hK hη D A hAD fibMass hBκ

/-! ### Step 3 -/

/-- **Step 3 bridge** — `thm:step3` (`step3.tex:1024`) specialised
with the regular-overlap state space drawn from `LinearExt α`.

The paper's overlap `Ω_{αβ} ⊆ L(P)` naturally lives inside linear
extensions; this bridge fixes `γ := LinearExt α` in the abstract
`Step3.step3_theorem`. -/
theorem step3
    (Ωreg : Finset (LinearExt α))
    (ηxy ηuv : LinearExt α → Step3.Sign)
    (κa κb θstar_xy θstar_uv : Step3.Sign)
    (Xxy Xuv : Finset (LinearExt α))
    (hXxy : Xxy ⊆ Ωreg) (hXuv : Xuv ⊆ Ωreg)
    (hηxy : ∀ L ∈ Ωreg \ Xxy, ηxy L = κa)
    (hηuv : ∀ L ∈ Ωreg \ Xuv, ηuv L = κb) :
    (∑ L ∈ Ωreg, Step3.corrProduct ηxy ηuv L =
      (Ωreg.card : ℤ) - 2 * ((Step3.disagreeSet Ωreg ηxy ηuv).card : ℤ)) ∧
    (∀ L ∈ Ωreg \ (Xxy ∪ Xuv),
        ηxy L = Step3.psiBij κa θstar_xy θstar_xy ∧
        ηuv L = Step3.psiBij κb θstar_uv θstar_uv) ∧
    ((Ωreg \ (Xxy ∪ Xuv)).card + (Xxy ∪ Xuv).card = Ωreg.card) :=
  Step3.step3_theorem Ωreg ηxy ηuv κa κb θstar_xy θstar_uv
    Xxy Xuv hXxy hXuv hηxy hηuv

/-! ### Step 4 -/

/-- **Step 4 bridge** — `thm:step4` (`step4.tex:93`) specialised with
the BK-boundary count replacing the abstract `boundaryBK` argument.

The abstract `Step4.thm_step4` takes `boundaryBK : ℕ` as a bare
integer.  At the poset level this is the `edgeBoundary S` of a cut
`S ⊆ LinearExt α`.  The bridge supplies that substitution. -/
theorem step4
    (Omega_card delta epsPrime cG CG : ℕ)
    (S : Finset (LinearExt α))
    (hcG : 0 < cG)
    (hG5 : cG * delta * Omega_card ≤
           2 * edgeBoundary S + 2 * CG * epsPrime * Omega_card) :
    cG * delta * Omega_card ≤
      2 * edgeBoundary S + 2 * CG * epsPrime * Omega_card :=
  Step4.thm_step4 Omega_card delta epsPrime (edgeBoundary S) cG CG hcG hG5

/-! ### Step 5 -/

/-- **Step 5 bridge (Rich-or-Collapse dichotomy)** — `thm:step5`
(`step5.tex:77`) specialised with the rich/row index types drawn
from the three Dilworth chains' position indices.

The abstract `Step5.thm_step5` takes abstract `p, q, r : ℕ`
(chain cardinalities).  For a width-≤ 3 poset `α` the three chain
cardinalities satisfy `p + q + r ≤ Fintype.card α`.  The bridge
fixes the ambient poset and leaves the three chain sizes as caller
parameters — the paper expects these to be supplied by a Dilworth
decomposition. -/
theorem step5
    {p q r : ℕ}
    (richCount_AB cT_AB : ℕ) (fAB : Fin p → ℤ) (KAB : ℤ)
    (rich_AB : Fin p → Finset (Fin q))
    (dich_AB : Step5.SingleTripleMany richCount_AB cT_AB p q ∨
               Step5.SingleTripleBanded rich_AB fAB KAB)
    (richCount_AC cT_AC : ℕ) (fAC : Fin p → ℤ) (KAC : ℤ)
    (rich_AC : Fin p → Finset (Fin r))
    (dich_AC : Step5.SingleTripleMany richCount_AC cT_AC p r ∨
               Step5.SingleTripleBanded rich_AC fAC KAC)
    (richCount_BC cT_BC : ℕ) (fBC : Fin q → ℤ) (KBC : ℤ)
    (rich_BC : Fin q → Finset (Fin r))
    (dich_BC : Step5.SingleTripleMany richCount_BC cT_BC q r ∨
               Step5.SingleTripleBanded rich_BC fBC KBC)
    (LP : Finset (LinearExt α)) (fiberSum c_R : ℕ)
    (hG4_AB : Step5.SingleTripleMany richCount_AB cT_AB p q →
      Step5.Step5Richness LP.card fiberSum c_R)
    (hG4_AC : Step5.SingleTripleMany richCount_AC cT_AC p r →
      Step5.Step5Richness LP.card fiberSum c_R)
    (hG4_BC : Step5.SingleTripleMany richCount_BC cT_BC q r →
      Step5.Step5Richness LP.card fiberSum c_R)
    (hG5 : Step5.SingleTripleBanded rich_AB fAB KAB →
           Step5.SingleTripleBanded rich_AC fAC KAC →
           Step5.SingleTripleBanded rich_BC fBC KBC →
           Step5.Step5Collapse p q) :
    Step5.Step5Richness LP.card fiberSum c_R ∨ Step5.Step5Collapse p q :=
  Step5.thm_step5
    richCount_AB cT_AB fAB KAB rich_AB dich_AB
    richCount_AC cT_AC fAC KAC rich_AC dich_AC
    richCount_BC cT_BC fBC KBC rich_BC dich_BC
    LP.card fiberSum c_R hG4_AB hG4_AC hG4_BC hG5

/-- **Step 5 bridge (second-moment form)** — `thm:step5_second_moment`
specialised to a rich-pair family on `α × α` with fibers drawn from
`LinearExt α`.

The visibility count `visibility richPairs Fstar L` and the rich-pair
fibers `Fstar` are now poset-native: fixing `LinExt := LinearExt α`
and `Pair := α × α`, the abstract Step 5 second-moment theorem
produces the exact `c² · |LP| ≤ ∑_L I(L)²` bound that Step 6
consumes. -/
theorem step5_second_moment
    {p q r : ℕ}
    (richCount_AB cT_AB : ℕ) (fAB : Fin p → ℤ) (KAB : ℤ)
    (rich_AB : Fin p → Finset (Fin q))
    (dich_AB : Step5.SingleTripleMany richCount_AB cT_AB p q ∨
               Step5.SingleTripleBanded rich_AB fAB KAB)
    (richCount_AC cT_AC : ℕ) (fAC : Fin p → ℤ) (KAC : ℤ)
    (rich_AC : Fin p → Finset (Fin r))
    (dich_AC : Step5.SingleTripleMany richCount_AC cT_AC p r ∨
               Step5.SingleTripleBanded rich_AC fAC KAC)
    (richCount_BC cT_BC : ℕ) (fBC : Fin q → ℤ) (KBC : ℤ)
    (rich_BC : Fin q → Finset (Fin r))
    (dich_BC : Step5.SingleTripleMany richCount_BC cT_BC q r ∨
               Step5.SingleTripleBanded rich_BC fBC KBC)
    (richPairs : Finset (α × α))
    (Fstar : (α × α) → Finset (LinearExt α))
    (LP : Finset (LinearExt α)) (c_R : ℕ)
    (hsub : ∀ β ∈ richPairs, Fstar β ⊆ LP)
    (hG4_AB : Step5.SingleTripleMany richCount_AB cT_AB p q →
      c_R * LP.card ≤ ∑ β ∈ richPairs, (Fstar β).card)
    (hG4_AC : Step5.SingleTripleMany richCount_AC cT_AC p r →
      c_R * LP.card ≤ ∑ β ∈ richPairs, (Fstar β).card)
    (hG4_BC : Step5.SingleTripleMany richCount_BC cT_BC q r →
      c_R * LP.card ≤ ∑ β ∈ richPairs, (Fstar β).card)
    (hG5 : Step5.SingleTripleBanded rich_AB fAB KAB →
           Step5.SingleTripleBanded rich_AC fAC KAC →
           Step5.SingleTripleBanded rich_BC fBC KBC →
           Step5.Step5Collapse p q) :
    (c_R ^ 2 * LP.card ≤
        ∑ L ∈ LP, (Step5.visibility richPairs Fstar L) ^ 2) ∨
      Step5.Step5Collapse p q :=
  Step5.thm_step5_second_moment
    richCount_AB cT_AB fAB KAB rich_AB dich_AB
    richCount_AC cT_AC fAC KAC rich_AC dich_AC
    richCount_BC cT_BC fBC KBC rich_BC dich_BC
    richPairs Fstar LP c_R hsub hG4_AB hG4_AC hG4_BC hG5

/-! ### Step 6 -/

/-- **Step 6 bridge (dichotomy)** — `thm:step6` (`step6.tex:481`)
specialised with the BK-boundary count of a cut `S ⊆ LinearExt α`
replacing the abstract `boundary` argument.

The abstract `Step6.thm_step6` yields a numeric disjunction; the
bridge substitutes `boundary := edgeBoundary S` so that the
output's first disjunct is a statement about the BK conductance of
`S`. -/
theorem step6
    (sumBadW M c_n c_d δ_n δ_d : ℕ)
    (S : Finset (LinearExt α))
    (hSum : c_n * sumBadW ≤ c_d * M * edgeBoundary S) :
    (c_n * δ_n * M ≤ c_d * M * δ_d * edgeBoundary S) ∨
      (δ_d * sumBadW ≤ δ_n * M) :=
  Step6.thm_step6 sumBadW M (edgeBoundary S) c_n c_d δ_n δ_d hSum

/-- **Step 6 bridge (rich-closure corollary)** — `thm:step6_rich_closure`
specialised with a BK-boundary cut and a volume count derived from
`LinearExt α`.

This is the form consumed by the Step 8 assembly: under a strict
low-conductance hypothesis, only the coherence branch can occur. -/
theorem step6_rich_closure
    (sumBadW M c_n c_d δ_n δ_d c_R : ℕ)
    (S : Finset (LinearExt α)) (volS : ℕ)
    (hSum : c_n * sumBadW ≤ c_d * M * edgeBoundary S)
    (hRich : c_R ^ 2 * volS ≤ M)
    (hLow : c_n * δ_n * c_R ^ 2 * volS > c_d * M * δ_d * edgeBoundary S) :
    δ_d * sumBadW ≤ δ_n * M :=
  Step6.thm_step6_rich_closure sumBadW M (edgeBoundary S) volS
    c_n c_d δ_n δ_d c_R hSum hRich hLow

/-! ### Step 7 -/

/-- **Step 7 bridge** — `thm:step7` (`step7.tex:1276`) specialised with
all three abstract carrier types fixed to poset-native choices:

* `Vertex := α` (elements of the poset carry the vertex potential `a`);
* `Edge := LinearExt α × LinearExt α` (BK-adjacent pairs carry the
  signed weight `δ_e` and tolerance defect);
* `Pair := α × α` (rich incomparable pairs carry the bandwidth
  gradient `Δ_xy` and adjacency mass `p_xy`).

The abstract `Step7.thm_step7` produces the `balanced` conclusion
from the combined `prop:71`/`prop:72`/`prop:73` inputs. The bridge
threads these inputs through the above substitution. -/
theorem step7
    (P : Step7.PotentialData α (LinearExt α × LinearExt α))
    (edges treeEdges shortEdges longEdges edgesWalk :
      Finset (LinearExt α × LinearExt α))
    (refEdge : LinearExt α × LinearExt α) (C₁ K₁ : ℕ)
    (goodPairs : Finset
      ((LinearExt α × LinearExt α) × (LinearExt α × LinearExt α)))
    (hTree : P.TreeIntegrationHyp treeEdges)
    (hCyc : P.CycleBoundHyp shortEdges C₁)
    (hDecomp : Step7.PotentialData.LongDecompositionHyp edges
      treeEdges shortEdges longEdges)
    (hPair : (Step7.FiberThresholdData.ofPotential P).PairClosenessHyp
      goodPairs K₁)
    (hWalk : Step7.FiberThresholdData.WalkWitness3
      refEdge edgesWalk goodPairs)
    (hWalkSub : edgesWalk ⊆ edges)
    (e_n e_d M₀ : ℕ)
    (hLong : e_d * ∑ e ∈ longEdges, P.edgeWeight e ≤ e_n * M₀)
    (hExc : e_d * ∑ e ∈ edges \ edgesWalk, P.edgeWeight e ≤ e_n * M₀)
    (D : Step7.BandwidthData (α × α))
    (bpairs richPairs : Finset (α × α)) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d : ℕ)
    (hBSub : richPairs ⊆ bpairs)
    (hBud : D.VarBudgetHyp bpairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀)
    (balanced inducedCex : Prop)
    (hReduction : Step7.Prop73Reduction richPairs balanced inducedCex)
    (hMin : inducedCex) :
    balanced :=
  Step7.thm_step7
    P edges treeEdges shortEdges longEdges edgesWalk
    refEdge C₁ K₁ goodPairs
    hTree hCyc hDecomp hPair hWalk hWalkSub
    e_n e_d M₀ hLong hExc
    D bpairs richPairs c₀ hc₀ b_n b_d c_n c_d
    hBSub hBud hRich
    balanced inducedCex hReduction hMin

/-- **Step 7 bridge (layered decomposition)** — Prop. 7.2
(`step7.tex:1175`) specialised with rich pairs on `α × α`.

The abstract `Step7.prop_72` produces a `LayeredWidth3` packaging
of the rich-pair Finset; the bridge fixes the carrier to `α × α`. -/
theorem step7_layered
    (D : Step7.BandwidthData (α × α))
    (pairs richPairs : Finset (α × α)) (c₀ : ℕ) (hc₀ : 0 < c₀)
    (b_n b_d c_n c_d M₀ : ℕ)
    (hSub : richPairs ⊆ pairs)
    (hBud : D.VarBudgetHyp pairs b_n b_d M₀)
    (hRich : D.RichnessHyp richPairs c_n c_d M₀) :
    ∃ (L : Step7.LayeredWidth3 richPairs),
      L.bandwidth = c₀ ∧
      c₀ * c_n * (b_d * L.richPairsOut.card) * M₀ ≤
        c_d * (b_n * M₀) :=
  Step7.prop_72 D pairs richPairs c₀ hc₀ b_n b_d c_n c_d M₀
    hSub hBud hRich

end Bridge
end OneThird
