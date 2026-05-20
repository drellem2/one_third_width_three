/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step5.Dichotomy
import OneThird.Step5.G1G2Grounded

/-!
# Step 5 — Rich-or-Collapse dichotomy: grounded form and a non-vacuous instance

FULL REFACTOR Phase 2, Wave-1 (`mg-d4bb`, scoped by `mg-d8c7` §2.1 /
§5.2 under S5-D; depends on `mg-faf8`). This file *grounds* the abstract
Rich-or-Collapse dichotomy of `Dichotomy.lean` (`thm:step5`,
`step5.tex:74`): it connects the per-triple dichotomy hypotheses
consumed by the abstract `thm_step5` to the **genuine `C`-coordinate
incomparability-interval geometry** of a poset, reusing the G1+G2
grounding already established by `mg-b21f` (`G1G2Grounded.lean`), and
then exercises the full three-triple Rich-or-Collapse assembly on a
**concrete width-3 non-chain poset**.

## What the grounding does

* `gRichRow` — the rich-row family of a genuine poset triple `(X, Y | Z)`,
  i.e. `richRow` (`ConvexOverlap.lean`) wired to the actual
  `alphaIdx`/`betaIdx` interval endpoints (`EndpointMono.lean`).

* `prop_single_triple_grounded` — `prop:single-triple` (`step5.tex:106`)
  on the genuine incomparability-interval endpoint families of a poset
  triple. The G2 monotonicity hypotheses of `convex_overlap` are
  discharged by G1, so the only input is the chain enumerations being
  monotone.

* `dichotomy_grounded` — the genuine geometric content of `thm:step5`
  Steps 2-3 (`step5.tex:212-246`): for a width-3 poset with three
  monotone Dilworth chains, *either* at least one of the three ordered
  triples has many rich pairs, *or* all three triples are banded. The
  three per-triple dichotomies are discharged from genuine geometry —
  there are **no opaque hypotheses**.

* `thm_step5_grounded` — the full `thm:step5` packaging: the G4
  fiber-mass closure (`FiberMass.lean`, separately ticketed; invoked at
  `step5.tex:233`) upgrades a "many rich pairs" outcome to the Richness
  conclusion (R); the three simultaneous banded outcomes are the
  Collapse conclusion (C).

## Non-vacuity (`mg-d4bb` acceptance bar)

`dichotomy_grounded_concrete` instantiates the whole assembly on
`W3 := Fin 3 × Fin 3` (product order) — the genuine width-3 non-chain
9-element poset of `mg-b21f`, Dilworth-decomposed into three length-3
chains. On this instance the dichotomy fires non-vacuously: the rich
set is genuinely non-empty (`(chainA 2, chainB 2)` is rich at `T = 1`,
hence `(2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2`), the `β`
endpoint family genuinely *strictly* increases, and the full
Rich-or-Collapse dichotomy holds with genuine band data. No
`Subsingleton`/empty baseline is used anywhere.
-/

namespace OneThird
namespace Step5

open Finset

/-! ## §G.1. The rich row of a genuine poset triple -/

section Grounded

variable {α : Type*} [Preorder α]

/-- The **rich-row family** of a genuine poset triple `(X, Y | Z)`.
`gRichRow Z x y T i` is the set of indices `j` such that the pair
`(x i, y j)` is rich at threshold `T`, measured by the overlap length
of their `Z`-coordinate incomparability intervals
`[alphaIdx Z (x i), betaIdx Z (x i)]` and
`[alphaIdx Z (y j), betaIdx Z (y j)]`.

This is `richRow` (`ConvexOverlap.lean`) wired to the actual
`alphaIdx`/`betaIdx` interval endpoints of `EndpointMono.lean`: the
abstract endpoint families consumed by `convex_overlap` are replaced
by the genuine `C`-coordinate geometry of the poset. -/
noncomputable def gRichRow (Z : Finset α) {p q : ℕ}
    (x : Fin p → α) (y : Fin q → α) (T : ℤ) : Fin p → Finset (Fin q) :=
  richRow (fun i => (alphaIdx Z (x i) : ℤ)) (fun i => (betaIdx Z (x i) : ℤ))
          (fun j => (alphaIdx Z (y j) : ℤ)) (fun j => (betaIdx Z (y j) : ℤ)) T

/-- **`gRichRow` membership.** `j ∈ gRichRow Z x y T i` iff the pair
`(x i, y j)` is rich at threshold `T` for the `Z`-coordinate interval
geometry. -/
theorem mem_gRichRow {Z : Finset α} {p q : ℕ}
    {x : Fin p → α} {y : Fin q → α} {T : ℤ} {i : Fin p} {j : Fin q} :
    j ∈ gRichRow Z x y T i ↔
      RichPair (fun i => (alphaIdx Z (x i) : ℤ))
               (fun i => (betaIdx Z (x i) : ℤ))
               (fun j => (alphaIdx Z (y j) : ℤ))
               (fun j => (betaIdx Z (y j) : ℤ)) T i j :=
  mem_richRow

/-! ## §G.2. `prop:single-triple` on genuine poset geometry -/

/-- **`prop:single-triple` (grounded)** (`step5.tex:106`).

For a genuine poset triple — reference chain `Z : Finset α`, chain
enumerations `x : Fin p → α`, `y : Fin q → α`, both monotone — and any
density constant `c` and rich-pair count `richCount`, the single-triple
dichotomy holds on the *actual* incomparability-interval geometry:
*either* the rich set is dense (`SingleTripleMany`), *or* it is banded
around a nondecreasing envelope (`SingleTripleBanded`).

The G2 monotonicity hypotheses of `convex_overlap` are discharged by
the G1 grounding (`endpoint_mono_grounded`, via `convex_overlap_grounded`);
the caller need only supply the two chain enumerations being monotone. -/
theorem prop_single_triple_grounded (Z : Finset α) {p q : ℕ}
    (x : Fin p → α) (y : Fin q → α) (hx : Monotone x) (hy : Monotone y)
    {T : ℤ} (hT : 1 ≤ T) (c richCount : ℕ) :
    SingleTripleMany richCount c p q ∨
    ∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧
      SingleTripleBanded (gRichRow Z x y T) f K := by
  rcases convex_overlap_grounded Z x y hx hy hT c richCount with hmany | hband
  · exact Or.inl hmany
  · obtain ⟨f, K, hK, hmono, hbd⟩ := hband
    exact Or.inr ⟨f, K, hK, hmono, hbd⟩

/-! ## §G.3. The Rich-or-Collapse dichotomy on genuine poset geometry -/

/-- **`thm:step5` Steps 2-3 (grounded, Rich-or-Collapse core)**
(`step5.tex:212-246`).

For a width-3 poset with a Dilworth decomposition into three monotone
chains `a : Fin p → α`, `b : Fin q → α`, `cc : Fin r → α` — together
with the three chains-as-finsets `Aref`, `Bref`, `Cref` carrying the
reference geometry — the Rich-or-Collapse dichotomy holds:

* **(R)** at least one of the three ordered triples `(A,B|C)`,
  `(A,C|B)`, `(B,C|A)` has many rich pairs; *or*
* **(C)** all three triples are banded around nondecreasing envelopes.

Each per-triple dichotomy is `prop_single_triple_grounded` on the
genuine `alphaIdx`/`betaIdx` interval geometry of the corresponding
reference chain. There are **no opaque hypotheses** — this theorem is
the genuine geometric content of `thm:step5`'s case split (`step5.tex`
Step 2 + Step 3), with the per-triple dichotomies discharged rather
than assumed (contrast the abstract `thm_step5` of `Dichotomy.lean`,
which takes the three `dich_*` disjunctions as inputs). -/
theorem dichotomy_grounded {p q r : ℕ}
    (a : Fin p → α) (b : Fin q → α) (cc : Fin r → α)
    (Aref Bref Cref : Finset α)
    (ha : Monotone a) (hb : Monotone b) (hc : Monotone cc)
    {T : ℤ} (hT : 1 ≤ T)
    (cAB cAC cBC richCountAB richCountAC richCountBC : ℕ) :
    -- (R): some ordered triple has many rich pairs
    (SingleTripleMany richCountAB cAB p q ∨
     SingleTripleMany richCountAC cAC p r ∨
     SingleTripleMany richCountBC cBC q r) ∨
    -- (C): all three triples are banded
    ((∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Cref a b T) f K) ∧
     (∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Bref a cc T) f K) ∧
     (∃ (f : Fin q → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Aref b cc T) f K)) := by
  rcases prop_single_triple_grounded Cref a b ha hb hT cAB richCountAB with
    hAB | hAB
  · exact Or.inl (Or.inl hAB)
  · rcases prop_single_triple_grounded Bref a cc ha hc hT cAC richCountAC with
      hAC | hAC
    · exact Or.inl (Or.inr (Or.inl hAC))
    · rcases prop_single_triple_grounded Aref b cc hb hc hT cBC richCountBC with
        hBC | hBC
      · exact Or.inl (Or.inr (Or.inr hBC))
      · exact Or.inr ⟨hAB, hAC, hBC⟩

/-- **`thm:step5` — Rich-or-Collapse (grounded, full packaging)**
(`step5.tex:74`).

The full Rich-or-Collapse theorem. The three per-triple dichotomies are
discharged from genuine geometry by `dichotomy_grounded`; a "many rich
pairs" outcome on any triple is upgraded to the Richness conclusion (R)
by the G4 fiber-mass closure (`hG4_*` — the separately-ticketed
`lem:fiber-mass` of `FiberMass.lean`, invoked at `step5.tex:233`); and
the three simultaneous banded outcomes are the Collapse conclusion (C).

Faithful to the paper proof (`step5.tex:197-246`): Step 1 (G3) fixes
the Dilworth decomposition — here the three monotone chains —, Step 2
applies the per-triple dichotomy, Step 3 routes the "many rich" branch
through G4 to (R) and the "all banded" branch to (C). -/
theorem thm_step5_grounded {p q r : ℕ}
    (a : Fin p → α) (b : Fin q → α) (cc : Fin r → α)
    (Aref Bref Cref : Finset α)
    (ha : Monotone a) (hb : Monotone b) (hc : Monotone cc)
    {T : ℤ} (hT : 1 ≤ T)
    (cAB cAC cBC richCountAB richCountAC richCountBC : ℕ)
    (LP_card fiberSum c_R : ℕ)
    (hG4_AB : SingleTripleMany richCountAB cAB p q →
      Step5Richness LP_card fiberSum c_R)
    (hG4_AC : SingleTripleMany richCountAC cAC p r →
      Step5Richness LP_card fiberSum c_R)
    (hG4_BC : SingleTripleMany richCountBC cBC q r →
      Step5Richness LP_card fiberSum c_R) :
    Step5Richness LP_card fiberSum c_R ∨
    ((∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Cref a b T) f K) ∧
     (∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Bref a cc T) f K) ∧
     (∃ (f : Fin q → ℤ) (K : ℤ), 0 ≤ K ∧
        SingleTripleBanded (gRichRow Aref b cc T) f K)) := by
  rcases dichotomy_grounded a b cc Aref Bref Cref ha hb hc hT
      cAB cAC cBC richCountAB richCountAC richCountBC with hR | hC
  · rcases hR with hAB | hAC | hBC
    · exact Or.inl (hG4_AB hAB)
    · exact Or.inl (hG4_AC hAC)
    · exact Or.inl (hG4_BC hBC)
  · exact Or.inr hC

end Grounded

/-! ## §G.4. Non-vacuous instantiation at a concrete width-3 poset

`W3 := Fin 3 × Fin 3` with the product order — a genuine width-3,
non-chain, 9-element poset (`W3_widthAtMost_three`, `W3_not_chain`,
both established by `mg-b21f` in `G1G2Grounded.lean`). Its three "rows"
`{0} × Fin 3`, `{1} × Fin 3`, `{2} × Fin 3` are a Dilworth
decomposition into length-3 chains. On the resulting three ordered
triples the Rich-or-Collapse dichotomy fires with non-trivial data —
see `dichotomy_grounded_concrete`. -/

section ConcreteWitness

/-- Third Dilworth chain `C = {2} × Fin 3`, enumerated monotonically as
`Fin 3 → W3`. The reference-finset form `chainC` (`G1G2Grounded.lean`)
carries the same three elements. -/
def chainCenum : Fin 3 → W3 := fun i => (2, i)

theorem chainCenum_monotone : Monotone chainCenum := by
  intro i i' h; exact Prod.le_def.mpr ⟨le_refl _, h⟩

/-- First Dilworth chain `A = {0} × Fin 3` as a reference finset. -/
def chainAref : Finset W3 := {(0, 0), (0, 1), (0, 2)}

/-- Second Dilworth chain `B = {1} × Fin 3` as a reference finset. -/
def chainBref : Finset W3 := {(1, 0), (1, 1), (1, 2)}

/-- **Non-vacuity, rich row.** The rich row of the genuine triple
`(A, B | C)` at index `2` and threshold `T = 1` is non-empty: index `2`
belongs to it, because `(chainA 2, chainB 2)` is a genuine rich pair
(`richPair_concrete`, `mg-b21f`). The grounded dichotomy therefore
operates on a genuinely populated rich set — not a `Subsingleton`/empty
baseline. -/
theorem gRichRow_chainAB_two_nonempty :
    (2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2 :=
  mem_gRichRow.mpr richPair_concrete

/-- **`thm:step5` grounded, instantiated and verified non-vacuous**
(`mg-d4bb`).

On the concrete width-3 non-chain poset `W3` with its Dilworth triple
`(chainA, chainB, chainCenum)` and reference chains
`(chainAref, chainBref, chainC)`, the grounded Rich-or-Collapse
dichotomy holds and fires with non-trivial content:

1. `W3` is genuinely width-3 and not a chain;
2. the `β`-endpoint family of chain `A` on `C` is genuinely *strictly*
   increasing (`betaIdx … 0 < betaIdx … 2`) — the interval geometry
   genuinely varies, it is not constant;
3. the rich row of the triple `(A, B | C)` is genuinely non-empty
   (`(2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2`);
4. the full `dichotomy_grounded` Rich-or-Collapse dichotomy holds on the
   three genuine ordered triples.

No `Subsingleton`-on-empty baseline is used: `p = q = r = 3`, the
poset has 9 elements, and the rich set is genuinely populated. -/
theorem dichotomy_grounded_concrete :
    HasWidthAtMost W3 3 ∧ ¬ IsChainPoset W3 ∧
    betaIdx chainC (chainA 0) < betaIdx chainC (chainA 2) ∧
    (2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2 ∧
    ((SingleTripleMany 0 1 3 3 ∨ SingleTripleMany 0 1 3 3 ∨
        SingleTripleMany 0 1 3 3) ∨
      ((∃ (f : Fin 3 → ℤ) (K : ℤ), 0 ≤ K ∧
          SingleTripleBanded (gRichRow chainC chainA chainB 1) f K) ∧
       (∃ (f : Fin 3 → ℤ) (K : ℤ), 0 ≤ K ∧
          SingleTripleBanded (gRichRow chainBref chainA chainCenum 1) f K) ∧
       (∃ (f : Fin 3 → ℤ) (K : ℤ), 0 ≤ K ∧
          SingleTripleBanded (gRichRow chainAref chainB chainCenum 1) f K))) :=
  ⟨W3_widthAtMost_three, W3_not_chain,
   betaIdx_chainA_strict_mono, gRichRow_chainAB_two_nonempty,
   dichotomy_grounded chainA chainB chainCenum chainAref chainBref chainC
     chainA_monotone chainB_monotone chainCenum_monotone (le_refl (1 : ℤ))
     1 1 1 0 0 0⟩

end ConcreteWitness

end Step5
end OneThird
