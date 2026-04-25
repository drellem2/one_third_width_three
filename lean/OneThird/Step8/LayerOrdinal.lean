/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Mathlib.LinearExtension.Subtype
import OneThird.Step8.LayeredReduction

/-!
# Step 8 — Layer-ordinal-sum reducibility (F1–F3)

Formalises the paper's *layer-ordinal reducible* predicate and the
data required by downstream Step 8 items (F2–F5 of `sec:g4-balanced-pair`).

## Main definitions

* `Step8.LayerOrdinalReducible L k` — paper `def:layer-reducible`
  (`step8.tex:2580-2593`): a layered poset `Q` is *layer-ordinal
  reducible at band index `k`* if every cross-pair `(u, v)` with
  `L.band u ≤ k` and `k < L.band v` satisfies `u <_Q v`. Equivalently,
  `Q = (M_1 ∪ ⋯ ∪ M_k) ⊕ (M_{k+1} ∪ ⋯ ∪ M_r)` as posets.

* `Step8.LayerOrdinalIrreducible L` — paper `def:layer-reducible`,
  irreducibility clause (`step8.tex:2591-2592`): `L` is not reducible
  at any `k ∈ [1, L.K - 1]`.

* `Step8.OrdinalDecompOfReducible L k h` — paper `lem:reducible-witness`
  (`step8.tex:2595-2619`): from a reducibility hypothesis `h`, package
  the band-split `Q_1 := L_{≤k}`, `Q_2 := L_{>k}` as an
  `OrdinalDecomp α` with empty middle piece.

* `Step8.linExtEquivOfReducible` — paper `cor:reducibility-transfer`
  (`step8.tex:2621-2654`), bijection statement: the *factorisation
  transfer* `LinearExt α ≃ LinearExt ↥Q_1 × LinearExt ↥Q_2` as a
  `Fintype` bijection. Derived from `OrdinalDecomp.tripleEquiv`
  (`lem:ordinal-factorisation`, `step8.tex:2404-2418`) by stripping the
  trivial middle factor.

* `Step8.numLinExt_factorOfReducible` — counting corollary of
  `cor:reducibility-transfer`: `numLinExt α = numLinExt ↥Q_1 * numLinExt ↥Q_2`.

* `Step8.exists_adjacent_not_lt_of_irreducible` — **`lem:irr-adjacent`**
  (`step8.tex:2461-2478`): an irreducible layered decomposition with
  all bands non-empty and depth `≥ 2` has an adjacent band index `i`
  and a cross-pair `(u, v) ∈ M_i × M_{i+1}` with `¬ (u < v)`. This is
  the F2 transitivity lemma.

* `Step8.hasBalancedPair_of_layered_strongInduction` — **F3**: the
  well-founded recursion framework for the iterated reduction of
  `lem:layered-balanced` (`step8.tex:2839-2891`). Strong induction on
  `Fintype.card α`: a step hypothesis that closes each case (A/B/C)
  using the induction hypothesis on strictly smaller layered width-3
  posets yields `HasBalancedPair α` unconditionally. F4 (Case B
  ordinal-sum transfer) and F5 (Case C2 in-situ proposition) supply
  the specific hook instances at call-site.

## Reference

`step8.tex` §`sec:g4-balanced-pair` (`step8.tex:1612-1625`), paper
Definition *layer-ordinal-sum reducible* added in A1 (mg-17e1);
Lemma `lem:irr-adjacent` (`step8.tex:2461-2478`) added in A3;
strong-induction proof of `lem:layered-balanced`
(`step8.tex:2839-2891`) restructured in A3 / mg-ec58.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

namespace Step8

/-! ### §1 — The predicate -/

/-- **Layer-ordinal reducible**.
Lean counterpart of paper `def:layer-reducible`
(`step8.tex:2580-2593`).

A layered poset `Q = M_1 ⊔ ⋯ ⊔ M_r` (presented here as a
`LayeredDecomposition α`) is *layer-ordinal reducible at index `k`*
if every cross-pair `(u, v)` with `u ∈ M_i, v ∈ M_j`, `i ≤ k < j`,
satisfies `u <_Q v`. Equivalently,
`Q = (M_1 ∪ ⋯ ∪ M_k) ⊕ (M_{k+1} ∪ ⋯ ∪ M_r)` as posets — all
layer-crossing comparabilities across the cut `k ∣ k+1` are directed
upward.

In the `LayeredDecomposition` representation, `i ≤ k < j` reads as
`L.band u ≤ k` and `k < L.band v`. -/
def LayerOrdinalReducible (L : LayeredDecomposition α) (k : ℕ) : Prop :=
  ∀ u v : α, L.band u ≤ k → k < L.band v → u < v

/-! ### §2 — `OrdinalDecomp α` from a reducibility witness -/

/-- **Reducibility witness → `OrdinalDecomp α`**.
Lean counterpart of paper `lem:reducible-witness`
(`step8.tex:2595-2619`): from a layer-ordinal-reducible decomposition
at index `k`, build the ordinal-sum decomposition witness
`D_k := (M_1 ∪ ⋯ ∪ M_k, ∅, M_{k+1} ∪ ⋯ ∪ M_r) ∈ OrdinalDecomp(Q)`.

From a `LayerOrdinalReducible L k` witness, package the two
band-split pieces
* `Q_1 := {z : α | L.band z ≤ k}` (the `Lower` part),
* `Q_2 := {z : α | k < L.band z}` (the `Upper` part),

as an `OrdinalDecomp α` whose middle piece is empty. The
reducibility hypothesis discharges the `Lower < Upper` element-wise
comparability field; the band-trichotomy on `L.band z` discharges
cover and disjointness. -/
def OrdinalDecompOfReducible (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) : OrdinalDecomp α where
  Lower := (Finset.univ : Finset α).filter (fun z => L.band z ≤ k)
  Mid := ∅
  Upper := (Finset.univ : Finset α).filter (fun z => k < L.band z)
  hCover := by
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      Finset.notMem_empty, true_and, or_false, iff_true]
    omega
  hDisjLM := Finset.disjoint_empty_right _
  hDisjLU := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
    omega
  hDisjMU := Finset.disjoint_empty_left _
  hLM_lt := fun _ _ _ hyM => absurd hyM (Finset.notMem_empty _)
  hLU_lt := by
    intro u hu v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact h u v hu hv
  hMU_lt := fun _ hx _ _ => absurd hx (Finset.notMem_empty _)

/-- Convenience: under `OrdinalDecompOfReducible`, the middle piece is
`∅` by definition. -/
@[simp]
lemma OrdinalDecompOfReducible_Mid (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) :
    (OrdinalDecompOfReducible L k h).Mid = (∅ : Finset α) := rfl

/-- Membership in the `Lower` (= `Q_1`) piece. -/
@[simp]
lemma mem_OrdinalDecompOfReducible_Lower (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) (z : α) :
    z ∈ (OrdinalDecompOfReducible L k h).Lower ↔ L.band z ≤ k := by
  simp only [OrdinalDecompOfReducible, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-- Membership in the `Upper` (= `Q_2`) piece. -/
@[simp]
lemma mem_OrdinalDecompOfReducible_Upper (L : LayeredDecomposition α) (k : ℕ)
    (h : LayerOrdinalReducible L k) (z : α) :
    z ∈ (OrdinalDecompOfReducible L k h).Upper ↔ k < L.band z := by
  simp only [OrdinalDecompOfReducible, Finset.mem_filter, Finset.mem_univ,
    true_and]

/-! ### §3 — Factorisation transfer `L(Q) ≃ L(Q_1) × L(Q_2)` -/

/-- **Factorisation transfer `L(Q) ≃ L(Q_1) × L(Q_2)`**.
Lean counterpart of paper `cor:reducibility-transfer`
(`step8.tex:2621-2654`), bijection statement.

The `Fintype`-bijection Lean version of the paper's
`L(Q) = L(Q_1) × L(Q_2)` identity for a layer-ordinal reducible
layered poset `Q`. Built from `OrdinalDecomp.tripleEquiv`
(`lem:ordinal-factorisation`, `step8.tex:2404-2418`) applied to the
witness `D_k` of `lem:reducible-witness`, by stripping the trivial
middle factor (the unique linear extension of the empty sub-poset).

The forward direction sends a linear extension `L` of `α` to the
pair of restrictions `(L|_{Q_1}, L|_{Q_2})`; the backward direction
concatenates two linear extensions via `OrdinalDecomp.concat`, using
any fixed linear extension of the empty middle piece (which is
unique up to equality, so well-defined). -/
noncomputable def linExtEquivOfReducible
    (L : LayeredDecomposition α) (k : ℕ) (h : LayerOrdinalReducible L k) :
    LinearExt α ≃
      LinearExt ↥(OrdinalDecompOfReducible L k h).Lower ×
        LinearExt ↥(OrdinalDecompOfReducible L k h).Upper := by
  classical
  set D := OrdinalDecompOfReducible L k h with hD_def
  -- The middle piece `D.Mid` is `∅`, so `LinearExt ↥D.Mid` is a
  -- subsingleton (unique up to equality, by vacuous extensionality on
  -- the empty subtype). Use `szpilrajn` to pick a canonical element,
  -- and `concat_restrict` to identify it with the restriction of any
  -- given linear extension.
  have hMid_sub : Subsingleton (LinearExt ↥D.Mid) := by
    refine ⟨fun a b => ?_⟩
    apply LinearExt.ext
    apply Equiv.ext
    intro x
    -- `x : ↥D.Mid = ↥∅`; its membership property is `x.val ∈ ∅`, absurd.
    exact absurd x.property (Finset.notMem_empty _)
  let eMid : LinearExt ↥D.Mid := LinearExt.szpilrajn _
  refine
    { toFun := fun Lext => ⟨D.restrictLower Lext, D.restrictUpper Lext⟩
      invFun := fun p => D.concat p.1 eMid p.2
      left_inv := ?_
      right_inv := ?_ }
  · -- left_inv: `concat (restrictLower L) eMid (restrictUpper L) = L`.
    -- Use `concat_restrict` after identifying `eMid` with
    -- `restrictMid L` via the subsingleton.
    intro Lext
    have heq : eMid = D.restrictMid Lext := @Subsingleton.elim _ hMid_sub _ _
    rw [heq]
    exact D.concat_restrict Lext
  · -- right_inv: restricting the `concat` recovers the original pair.
    intro p
    rcases p with ⟨LL, LU⟩
    simp only [Prod.mk.injEq]
    exact ⟨D.restrictLower_concat LL eMid LU,
           D.restrictUpper_concat LL eMid LU⟩

/-- **Counting factorisation**.
Counting corollary of paper `cor:reducibility-transfer`
(`step8.tex:2621-2654`); two-piece specialisation of the
`|L(P)| = |L(P_-)| · |L(P_0)| · |L(P_+)|` cardinality conclusion of
`lem:ordinal-factorisation` (`step8.tex:2416-2417`) with the empty
middle piece collapsed.

The number of linear extensions of `α` factors as the product of
the counts on the two pieces `Q_1` and `Q_2` of a layer-ordinal
reducible decomposition. -/
theorem numLinExt_factorOfReducible
    (L : LayeredDecomposition α) (k : ℕ) (h : LayerOrdinalReducible L k) :
    numLinExt α =
      numLinExt ↥(OrdinalDecompOfReducible L k h).Lower *
        numLinExt ↥(OrdinalDecompOfReducible L k h).Upper := by
  unfold numLinExt
  rw [Fintype.card_congr (linExtEquivOfReducible L k h), Fintype.card_prod]

/-! ### §4 — Irreducibility ⇒ adjacent incomparable cross-pair (F2) -/

/-- **Layer-ordinal-sum irreducibility** (`step8.tex:2273`).

A layered decomposition is *layer-ordinal-sum irreducible* if there
is no band index `k ∈ [1, L.K − 1]` at which it is reducible in the
sense of `LayerOrdinalReducible`. Equivalently, every "cut" of `Q`
along a band boundary fails to be directed upward.

Paper: Definition~\ref{def:layer-reducible} (`step8.tex:2261-2274`). -/
def LayerOrdinalIrreducible (L : LayeredDecomposition α) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < L.K → ¬ LayerOrdinalReducible L k

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Lemma `lem:irr-adjacent`** (`step8.tex:2461-2478`), Lean form.

If `L` is layer-ordinal-sum irreducible (not reducible at any band
index `k ∈ [1, L.K − 1]`), has depth `L.K ≥ 2`, and every band
`M_1, …, M_K` is non-empty, then there exists an adjacent band index
`i ∈ [1, L.K − 1]` and a cross-pair `(u, v) ∈ M_i × M_{i+1}` with
`¬ (u < v)`.

**Relation to paper.** The paper's conclusion asks for `(u, v)`
*incomparable* in `Q`. The Lean form `¬ (u < v)` is what
irreducibility directly provides: the reverse-direction ruling-out
`¬ (v < u)` is argued in the paper via "(L2)", which is a property of
the cross-band direction in the §sec:g4 setup but not an axiom of
`LayeredDecomposition` in Lean. Downstream callers who also have
"cross-band comparabilities are upward" can combine this with the
returned `¬ (u < v)` to obtain full incomparability.

**Proof (paper, `step8.tex:2470-2478`).** Contradiction: assume every
adjacent cross-pair `u ∈ M_i, v ∈ M_{i+1}` has `u <_Q v`. By
transitivity (chaining through intermediate non-empty bands), for any
`i < j` and any `u ∈ M_i, v ∈ M_j` we obtain `u <_Q v`. In
particular `L` is reducible at `k = 1` (valid since `L.K ≥ 2`),
contradicting `hIrr 1`. -/
theorem exists_adjacent_not_lt_of_irreducible
    (L : LayeredDecomposition α)
    (hK : 2 ≤ L.K)
    (hIrr : LayerOrdinalIrreducible L)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) :
    ∃ (i : ℕ) (u v : α),
      1 ≤ i ∧ i < L.K ∧
      L.band u = i ∧ L.band v = i + 1 ∧ ¬ (u < v) := by
  classical
  -- Proof by contradiction on the existence of an adjacent obstruction.
  by_contra hContra
  push Not at hContra
  -- hContra : ∀ i u v, 1 ≤ i → i < L.K → band u = i → band v = i+1 → u < v.
  -- Derive the reducibility witness at k = 1.
  refine hIrr 1 (le_refl 1) hK ?_
  intro u v hu hv
  -- From `L.band u ≤ 1` and `L.band u ≥ 1` (by `band_pos`), get `band u = 1`.
  have hu1 : L.band u = 1 := le_antisymm hu (L.band_pos u)
  have hvK : L.band v ≤ L.K := L.band_le v
  -- Chain the adjacent-step hypothesis via non-empty intermediate bands.
  -- Claim: for every `j ∈ [2, L.K]` and every `w ∈ M_j`, we have `u < w`.
  suffices hChain :
      ∀ j : ℕ, 2 ≤ j → j ≤ L.K →
        ∀ w : α, L.band w = j → u < w by
    exact hChain (L.band v) hv hvK v rfl
  intro j hj2
  induction j, hj2 using Nat.le_induction with
  | base =>
    -- j = 2: direct from `hContra` at i = 1.
    intro _ w hbw
    exact hContra 1 u w (le_refl 1) hK hu1 hbw
  | succ j hj2 IH =>
    -- j ≥ 2, step from j to j+1. Chain through M_j via hNonempty.
    intro hj1K w hbw
    have hjK : j ≤ L.K := by omega
    have h1j : 1 ≤ j := by omega
    have hjLtK : j < L.K := by omega
    obtain ⟨w', hw'⟩ := hNonempty j h1j hjK
    have hbw' : L.band w' = j := by
      rw [LayeredDecomposition.mem_bandSet] at hw'
      exact hw'
    have h1 : u < w' := IH hjK w' hbw'
    have h2 : w' < w := hContra j w' w h1j hjLtK hbw' hbw
    exact lt_trans h1 h2

/-! ### §5 — F3: Well-founded recursion framework for iterated reduction -/

set_option linter.unusedVariables false in
/-- **F3: Strong induction on `Fintype.card α` for `HasBalancedPair`.**

The well-founded recursion framework underlying the paper's strong
induction in the proof of `lem:layered-balanced` (`step8.tex:2839-2891`,
restructured by A3 / mg-ec58).

**Shape of the hypothesis.** Given a step function `hStep` that produces
`HasBalancedPair α` for every non-chain layered width-3 poset `α`,
*using an induction hypothesis on strictly smaller types* (any
`β` with `Fintype.card β < Fintype.card α` that is itself a non-chain
layered width-3 poset also has a balanced pair), the framework delivers
the conclusion unconditionally.

**Case structure (paper, `step8.tex:2838-2891`).** The `hStep` hook is
meant to be discharged by the case split:

* **Case A (K = 1)**: direct antichain argument (no IH needed). This
  mirrors `step8.tex:2847-2849`.

* **Case B (`L` reducible at some `k`)**: apply the IH to the non-chain
  factor `P_j` of the ordinal-sum decomposition `P = P_1 ⊕ P_2`, then
  transfer via `L(P) ≃ L(P_1) × L(P_2)` (the F4 / OrdinalChainLift
  infrastructure). Corresponds to `step8.tex:2851-2861`.

* **Case C (`L` irreducible, K ≥ 2)**: pick an incomparable pair,
  window-localise via `windowLocalization`. Either
  * **C1 (`W ⊊ X`)**: IH applies to `P|_W` (strict size descent), and
    `hasBalancedPair_lift` transfers the balanced pair back. This
    mirrors `step8.tex:2879-2883`.
  * **C2 (`W = X`)**: `P` itself is of bounded size, and the in-situ
    balanced-pair proposition (`prop:in-situ-balanced`, F5) applies.
    Corresponds to `step8.tex:2885-2888`.

**Why this packaging.** Separating the recursion skeleton from the
case-closing steps lets F4 (chained `OrdinalDecomp` lift for Case B)
and F5 (generalised `lem_layered_balanced_subtype` for Case C2)
evolve independently: each lands as a callable lemma that slots into
`hStep`, without touching the recursion driver itself.

**Reference.** `step8.tex:2911-2921` (`rem:old-vs-new`): "the
`well-founded recursion framework for iterated reduction' (work item
F3) ... [is] the Lean image of the outer induction on `|X|`."

**Proof.** Strong induction on `Fintype.card α`, packaged via
`Nat.strong_induction_on` with the type parameter generalised inside the
inductive step. -/
theorem hasBalancedPair_of_layered_strongInduction.{u}
    (hStep : ∀ (α : Type u) [PartialOrder α] [Fintype α]
        [DecidableEq α] (L : LayeredDecomposition α),
        2 ≤ Fintype.card α →
        ¬ OneThird.IsChainPoset α →
        (∀ (β : Type u) [PartialOrder β] [Fintype β]
             [DecidableEq β] (LB : LayeredDecomposition β),
          Fintype.card β < Fintype.card α →
          2 ≤ Fintype.card β →
          ¬ OneThird.IsChainPoset β →
          OneThird.HasBalancedPair β) →
        OneThird.HasBalancedPair α) :
    ∀ (α : Type u) [PartialOrder α] [Fintype α]
      [DecidableEq α] (L : LayeredDecomposition α),
      2 ≤ Fintype.card α →
      ¬ OneThird.IsChainPoset α →
      OneThird.HasBalancedPair α := by
  -- Strong induction on the numeric `Fintype.card α`, generalising over α.
  suffices h : ∀ n : ℕ, ∀ (α : Type u) [PartialOrder α] [Fintype α]
      [DecidableEq α] (L : LayeredDecomposition α),
      Fintype.card α = n →
      2 ≤ Fintype.card α →
      ¬ OneThird.IsChainPoset α →
      OneThird.HasBalancedPair α by
    intro α _ _ _ L h2 hNC
    exact h (Fintype.card α) α L rfl h2 hNC
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α _ _ _ L hcard h2 hNotChain
    refine hStep α L h2 hNotChain ?_
    intro β _ _ _ LB hβLt h2β hNCβ
    -- `Fintype.card β < Fintype.card α = n`, so IH applies at `Fintype.card β`.
    rw [hcard] at hβLt
    exact ih (Fintype.card β) hβLt β LB rfl h2β hNCβ

set_option linter.unusedVariables false in
/-- **F3 corollary — cardinality-bounded form.**

Variant of `hasBalancedPair_of_layered_strongInduction` that exposes the
cardinality bound `n` as an explicit parameter. Useful at call-sites that
already carry a bound on `Fintype.card α` (e.g., after window-localising
to a window of size `≤ 3(3w + 1)`).

The proof is the same strong induction, phrased with `Fintype.card α ≤ n`
instead of implicit universal quantification. -/
theorem hasBalancedPair_of_layered_strongInduction_le.{u}
    (hStep : ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
        (L : LayeredDecomposition α),
        2 ≤ Fintype.card α →
        ¬ OneThird.IsChainPoset α →
        (∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
             (LB : LayeredDecomposition β),
          Fintype.card β < Fintype.card α →
          2 ≤ Fintype.card β →
          ¬ OneThird.IsChainPoset β →
          OneThird.HasBalancedPair β) →
        OneThird.HasBalancedPair α) :
    ∀ (n : ℕ) (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
      (L : LayeredDecomposition α),
      Fintype.card α ≤ n →
      2 ≤ Fintype.card α →
      ¬ OneThird.IsChainPoset α →
      OneThird.HasBalancedPair α := by
  intro n α _ _ _ L _hle h2 hNC
  exact hasBalancedPair_of_layered_strongInduction hStep α L h2 hNC

end Step8
end OneThird
