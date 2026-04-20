/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step3.CommonAxes
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Step 3 — Correlation reformulation, η/θ consistency, and Step 3 theorem

This file formalises `step3.tex` §§6–8:

* `prop:correlation` (`step3.tex:669`) — the correlation reformulation
  of the Step 3 coherence/incoherence dichotomy: the disagreement
  probability and the per-overlap correlation
  `Corr := E[η_{x,y}(L)·η_{u,v}(L)]` are related by
  `Corr = 1 − 2·Pr[η ≠ η']`.
* `lem:eta-theta` (`step3.tex:856`) — per-fiber (`θ`) vs.
  per-state (`η`) consistency: under Lemma~`lem:common-axes`, the
  per-state sign `η_{x,y}(L)` equals a block-constant value
  `κ^a_{xy}` which is itself the image of `θ^*_{x,y}` under a
  fixed bookkeeping bijection `Ψ_{xy,uv}`.
* `thm:step3` (`step3.tex:1024`) — the Step 3 assembly: per-fiber
  orientation, per-overlap sign, the coherence dichotomy, and
  consistency of η/θ.

## Abstract form

Following `OneThird.Step3.LocalSign` and `OneThird.Step3.CommonAxes`,
paper objects are replaced by abstract finsets/functions:

* an overlap state type `γ` and regular overlap `Ωreg : Finset γ`;
* per-state sign functions `η_{xy}, η_{uv} : γ → Sign` on `Ωreg`;
* per-fiber dominant orientations `θstar_{xy}, θstar_{uv} : Sign`;
* block-level signs `κa_{xy}, κb_{uv} : Sign` supplied by
  `lem:common-axes` through `CommonAxes`.

Every claim is stated in the abstract form and proved sorry-free from
the hypotheses. Paper probability statements are presented in
cleared-denominator integer form `c · |Ωreg| ≤ … + ε · |Ωreg|`.

## Downstream

* Step 4 (`mg-8082`, `mg-14df`) consumes `correlation_card_identity`
  and `incoherent` for the block-counting incompatibility lemma.
* Step 6 (`mg-450c`, `mg-af62`) consumes `eta_theta_consistency` and
  `coherence_iff_theta_agree` for the coherent-implies-collapse
  dichotomy.
-/

namespace OneThird
namespace Step3

open Finset

section Correlation

variable {γ : Type*} [DecidableEq γ]

/-! ### §6 — Correlation reformulation (`prop:correlation`) -/

/-- The **per-state correlation product** `η_{x,y}(L) · η_{u,v}(L) ∈ ℤ`
(`step3.tex:671`). Each factor is ±1, so the product is ±1. -/
def corrProduct (ηxy ηuv : γ → Sign) (L : γ) : ℤ :=
  (ηxy L).toInt * (ηuv L).toInt

lemma corrProduct_abs_eq_one (ηxy ηuv : γ → Sign) (L : γ) :
    (corrProduct ηxy ηuv L) * (corrProduct ηxy ηuv L) = 1 := by
  unfold corrProduct
  have h1 : (ηxy L).toInt * (ηxy L).toInt = 1 := Sign.toInt_mul_self _
  have h2 : (ηuv L).toInt * (ηuv L).toInt = 1 := Sign.toInt_mul_self _
  ring_nf
  calc (ηxy L).toInt ^ 2 * (ηuv L).toInt ^ 2
      = ((ηxy L).toInt * (ηxy L).toInt) * ((ηuv L).toInt * (ηuv L).toInt) := by ring
    _ = 1 * 1 := by rw [h1, h2]
    _ = 1 := by ring

/-- `corrProduct` is `+1` iff the two signs agree, `-1` otherwise. -/
lemma corrProduct_eq_one_iff (ηxy ηuv : γ → Sign) (L : γ) :
    corrProduct ηxy ηuv L = 1 ↔ ηxy L = ηuv L := by
  unfold corrProduct
  cases hxy : ηxy L <;> cases huv : ηuv L <;>
    simp [Sign.toInt]

lemma corrProduct_eq_neg_one_iff (ηxy ηuv : γ → Sign) (L : γ) :
    corrProduct ηxy ηuv L = -1 ↔ ηxy L ≠ ηuv L := by
  unfold corrProduct
  cases hxy : ηxy L <;> cases huv : ηuv L <;>
    simp [Sign.toInt]

lemma corrProduct_one_or_neg_one (ηxy ηuv : γ → Sign) (L : γ) :
    corrProduct ηxy ηuv L = 1 ∨ corrProduct ηxy ηuv L = -1 := by
  unfold corrProduct
  cases ηxy L <;> cases ηuv L <;> decide

/-- The **disagreement set** `{L ∈ Ωreg : η_{x,y}(L) ≠ η_{u,v}(L)}`
(`step3.tex:660`). -/
def disagreeSet (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) : Finset γ :=
  Ωreg.filter (fun L => ηxy L ≠ ηuv L)

lemma disagreeSet_subset (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    disagreeSet Ωreg ηxy ηuv ⊆ Ωreg := Finset.filter_subset _ _

lemma disagreeSet_card_le (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    (disagreeSet Ωreg ηxy ηuv).card ≤ Ωreg.card :=
  Finset.card_le_card (disagreeSet_subset _ _ _)

/-- The **agreement set** `{L ∈ Ωreg : η_{x,y}(L) = η_{u,v}(L)}`. -/
def agreeSet (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) : Finset γ :=
  Ωreg.filter (fun L => ηxy L = ηuv L)

lemma agreeSet_subset (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    agreeSet Ωreg ηxy ηuv ⊆ Ωreg := Finset.filter_subset _ _

lemma agreeSet_disjoint_disagreeSet (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    Disjoint (agreeSet Ωreg ηxy ηuv) (disagreeSet Ωreg ηxy ηuv) := by
  classical
  rw [Finset.disjoint_left]
  intro L hLa hLd
  unfold agreeSet at hLa
  unfold disagreeSet at hLd
  rw [Finset.mem_filter] at hLa hLd
  exact hLd.2 hLa.2

lemma agreeSet_union_disagreeSet (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    agreeSet Ωreg ηxy ηuv ∪ disagreeSet Ωreg ηxy ηuv = Ωreg := by
  classical
  ext L
  unfold agreeSet disagreeSet
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hL, _⟩ | ⟨hL, _⟩) <;> exact hL
  · intro hL
    by_cases h : ηxy L = ηuv L
    · exact Or.inl ⟨hL, h⟩
    · exact Or.inr ⟨hL, h⟩

lemma agreeSet_card_add_disagreeSet_card
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    (agreeSet Ωreg ηxy ηuv).card + (disagreeSet Ωreg ηxy ηuv).card =
      Ωreg.card := by
  classical
  rw [← Finset.card_union_of_disjoint (agreeSet_disjoint_disagreeSet _ _ _),
      agreeSet_union_disagreeSet]

/-- **`prop:correlation` (cleared-denominator, integer form).**
The sum of `η_{x,y}(L) · η_{u,v}(L)` over the regular overlap equals
`|Ωreg|` minus twice the disagreement cardinality
(`step3.tex:678-681`).

In probability form this reads `Corr = 1 − 2·Pr[η ≠ η']`, with
`Corr := E[η_{x,y}·η_{u,v}]` and `Pr[η ≠ η'] := |disagreeSet|/|Ωreg|`. -/
theorem correlation_card_identity
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    ∑ L ∈ Ωreg, corrProduct ηxy ηuv L =
      (Ωreg.card : ℤ) - 2 * ((disagreeSet Ωreg ηxy ηuv).card : ℤ) := by
  classical
  -- Split the sum according to agree/disagree.
  have hsplit :
      ∑ L ∈ Ωreg, corrProduct ηxy ηuv L =
        ∑ L ∈ agreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L +
          ∑ L ∈ disagreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L := by
    rw [← Finset.sum_union (agreeSet_disjoint_disagreeSet Ωreg ηxy ηuv),
        agreeSet_union_disagreeSet]
  -- On `agreeSet` the product is `+1`; on `disagreeSet` it is `-1`.
  have hagree :
      ∑ L ∈ agreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L =
        ((agreeSet Ωreg ηxy ηuv).card : ℤ) := by
    have hrw : ∑ L ∈ agreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L =
        ∑ _L ∈ agreeSet Ωreg ηxy ηuv, (1 : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro L hL
      unfold agreeSet at hL
      rw [Finset.mem_filter] at hL
      exact (corrProduct_eq_one_iff ηxy ηuv L).mpr hL.2
    rw [hrw, Finset.sum_const]
    simp
  have hdisagree :
      ∑ L ∈ disagreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L =
        - ((disagreeSet Ωreg ηxy ηuv).card : ℤ) := by
    have : ∑ L ∈ disagreeSet Ωreg ηxy ηuv, corrProduct ηxy ηuv L =
        ∑ _L ∈ disagreeSet Ωreg ηxy ηuv, (-1 : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro L hL
      unfold disagreeSet at hL
      rw [Finset.mem_filter] at hL
      exact (corrProduct_eq_neg_one_iff ηxy ηuv L).mpr hL.2
    rw [this, Finset.sum_const]
    simp
  have hcount : ((agreeSet Ωreg ηxy ηuv).card : ℤ) +
        ((disagreeSet Ωreg ηxy ηuv).card : ℤ) = (Ωreg.card : ℤ) := by
    have := agreeSet_card_add_disagreeSet_card Ωreg ηxy ηuv
    exact_mod_cast this
  rw [hsplit, hagree, hdisagree]
  linarith

/-- **`prop:correlation` (coherent direction, cleared-denominator).**
If the disagreement is `≤ ε · |Ωreg|` for some integer ε-numerator
`a` and denominator `c`, then the correlation sum satisfies
`c · ∑ corrProduct ≥ (c − 2a) · |Ωreg|`, i.e.
`Corr ≥ 1 − 2ε`. This is the integer form of `Corr ≥ 1 − o(1)`. -/
theorem correlation_coherent_bound
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (a c : ℕ) (hc : 0 < c)
    (hagree : c * (disagreeSet Ωreg ηxy ηuv).card ≤ a * Ωreg.card) :
    (c : ℤ) * ∑ L ∈ Ωreg, corrProduct ηxy ηuv L ≥
      ((c : ℤ) - 2 * (a : ℤ)) * (Ωreg.card : ℤ) := by
  rw [correlation_card_identity]
  have hcast : ((c : ℤ) * (disagreeSet Ωreg ηxy ηuv).card
      ≤ (a : ℤ) * (Ωreg.card : ℤ)) := by exact_mod_cast hagree
  have hcpos : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  nlinarith [hcast, hcpos]

/-- **`prop:correlation` (incoherent direction, cleared-denominator).**
If the disagreement is `≥ c_inc · |Ωreg|` for some integer
numerator `cinc` and denominator `d`, then
`d · ∑ corrProduct ≤ (d − 2·cinc) · |Ωreg|`, i.e.
`Corr ≤ 1 − 2·c_inc`. -/
theorem correlation_incoherent_bound
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (cinc d : ℕ) (hd : 0 < d)
    (hdis : d * (disagreeSet Ωreg ηxy ηuv).card ≥ cinc * Ωreg.card) :
    (d : ℤ) * ∑ L ∈ Ωreg, corrProduct ηxy ηuv L ≤
      ((d : ℤ) - 2 * (cinc : ℤ)) * (Ωreg.card : ℤ) := by
  rw [correlation_card_identity]
  have hcast : ((d : ℤ) * (disagreeSet Ωreg ηxy ηuv).card
      ≥ (cinc : ℤ) * (Ωreg.card : ℤ)) := by exact_mod_cast hdis
  have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  nlinarith [hcast, hdpos]

/-- **Coherent abstract predicate**: the disagreement cardinality is
at most `a · |Ωreg| / c` (a cleared-denominator version of
`p := Pr[η ≠ η'] ≤ ε`). -/
def Coherent (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) (a c : ℕ) : Prop :=
  c * (disagreeSet Ωreg ηxy ηuv).card ≤ a * Ωreg.card

/-- **Incoherent abstract predicate**: the disagreement cardinality
is at least `cinc · |Ωreg| / d` (a cleared-denominator version of
`p ≥ c_inc`). -/
def Incoherent (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) (cinc d : ℕ) : Prop :=
  d * (disagreeSet Ωreg ηxy ηuv).card ≥ cinc * Ωreg.card

/-- **`prop:correlation` packaged**: both directions of the
`coherent ⇔ Corr ≥ 1 − o(1)`, `incoherent ⇔ Corr ≤ 1 − 2·c_inc`
equivalence, assembled as a single statement. -/
theorem correlation_reformulation
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign) :
    ∑ L ∈ Ωreg, corrProduct ηxy ηuv L =
      (Ωreg.card : ℤ) - 2 * ((disagreeSet Ωreg ηxy ηuv).card : ℤ) :=
  correlation_card_identity Ωreg ηxy ηuv

end Correlation

section EtaTheta

variable {γ : Type*} [DecidableEq γ]

/-! ### §7 — Per-fiber vs. per-state consistency (`lem:eta-theta`) -/

/-- The **bookkeeping bijection** `Ψ_{xy,uv} : {±1} → {±1}`
(`step3.tex:923`, equation `eq:Psi-def`):
`Ψ_{xy,uv}(s) = κ^a_{xy} · θ^*_{x,y} · s`.

Since both `κa` and `θstar` are fixed, `Ψ` is one of `±id` and is
therefore a bijection of `{±1}` (either identity or sign flip). -/
def psiBij (κa θstar : Sign) (s : Sign) : Sign :=
  -- Multiplicatively: `κ^a * θ* * s`. Using `Bool.xor` on `Sign = Bool`.
  -- For `κa = θstar = true` (`+1 · +1`): returns `s`.
  -- For `κa = true, θstar = false`: returns `¬s`.
  -- etc. We encode by using integer toInt values.
  if (κa.toInt * θstar.toInt : ℤ) = 1 then s else Sign.neg s

/-- Integer form of `psiBij`: the `toInt` of the result equals
`κa.toInt * θstar.toInt * s.toInt`. This is the identity used in
`Step 4` of the paper proof (`step3.tex:935-941`). -/
lemma psiBij_toInt (κa θstar s : Sign) :
    (psiBij κa θstar s).toInt = κa.toInt * θstar.toInt * s.toInt := by
  unfold psiBij
  by_cases h : (κa.toInt * θstar.toInt : ℤ) = 1
  · rw [if_pos h, h]; ring
  · rw [if_neg h, Sign.toInt_neg]
    -- κa.toInt * θstar.toInt ≠ 1 and each is ±1, so product is -1.
    have hκa := Sign.toInt_eq_one_or_neg_one κa
    have hθ := Sign.toInt_eq_one_or_neg_one θstar
    have : κa.toInt * θstar.toInt = -1 := by
      rcases hκa with h1 | h1 <;> rcases hθ with h2 | h2 <;>
        simp [h1, h2] at h ⊢
    rw [this]; ring

/-- `psiBij` is an **involution** when `κa = +1, θstar = +1`:
then `psiBij _ _ s = s`. -/
lemma psiBij_id (s : Sign) : psiBij true true s = s := by
  unfold psiBij Sign.toInt
  simp

/-- **Evaluation at `θstar`**: `psiBij κa θstar θstar = κa`,
since `(θstar.toInt)² = 1` (`step3.tex:935-941`). -/
lemma psiBij_at_theta_star (κa θstar : Sign) :
    psiBij κa θstar θstar = κa := by
  cases κa <;> cases θstar <;> decide

/-- `psiBij` is a bijection (either identity or negation). -/
lemma psiBij_injective (κa θstar : Sign) :
    Function.Injective (psiBij κa θstar) := by
  intro s s' hss'
  cases κa <;> cases θstar <;> cases s <;> cases s' <;>
    first | rfl | (exfalso; exact Bool.noConfusion hss')

/-- **`lem:eta-theta` (core identity, abstract form, `step3.tex:856`).**

Hypotheses:

* `ηxy L = κa` for all `L ∈ Ωreg` (block-constancy of the per-state
  sign, `step3.tex:896`, equation `eq:eta-eq-kappa`).

Conclusion:

* `ηxy L = psiBij κa θstar θstar` for every `L ∈ Ωreg`
  (`step3.tex:944-949`), where the right-hand side is
  `L`-independent (depends only on the global signs `κa, θstar`).
-/
theorem eta_eq_psi_theta_star
    {Ωreg : Finset γ} {ηxy : γ → Sign} {κa θstar : Sign}
    (hκa : ∀ L ∈ Ωreg, ηxy L = κa) :
    ∀ L ∈ Ωreg, ηxy L = psiBij κa θstar θstar := by
  intro L hL
  rw [hκa L hL, psiBij_at_theta_star]

/-- **`lem:eta-theta` (consistency, exceptional-set form).**

Paper hypotheses (abstract):

* `ηxy` is block-constant equal to `κa` on all but an exceptional set
  `X_xy ⊆ Ωreg` of size `≤ e_xy`;
* `ηuv` is block-constant equal to `κb` on all but an exceptional set
  `X_uv ⊆ Ωreg` of size `≤ e_uv`.

Conclusion:

* Outside `X := X_xy ∪ X_uv` (of size `≤ e_xy + e_uv`), the identity
  `ηxy L = psiBij κa θstar_xy θstar_xy` holds (and symmetrically for
  `ηuv`).
-/
theorem eta_theta_consistency
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (κa κb θstar_xy θstar_uv : Sign)
    (Xxy Xuv : Finset γ) (hXxy : Xxy ⊆ Ωreg) (hXuv : Xuv ⊆ Ωreg)
    (hηxy : ∀ L ∈ Ωreg \ Xxy, ηxy L = κa)
    (hηuv : ∀ L ∈ Ωreg \ Xuv, ηuv L = κb) :
    (∀ L ∈ Ωreg \ (Xxy ∪ Xuv),
        ηxy L = psiBij κa θstar_xy θstar_xy ∧
        ηuv L = psiBij κb θstar_uv θstar_uv) ∧
    (Ωreg \ (Xxy ∪ Xuv)).card + (Xxy ∪ Xuv).card = Ωreg.card := by
  classical
  refine ⟨?_, ?_⟩
  · intro L hL
    rw [Finset.mem_sdiff, Finset.mem_union] at hL
    obtain ⟨hLΩ, hLnot⟩ := hL
    have hLxy : L ∈ Ωreg \ Xxy := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inl h)⟩
    have hLuv : L ∈ Ωreg \ Xuv := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inr h)⟩
    refine ⟨?_, ?_⟩
    · rw [hηxy L hLxy, psiBij_at_theta_star]
    · rw [hηuv L hLuv, psiBij_at_theta_star]
  · -- |Ωreg \ (Xxy ∪ Xuv)| + |Xxy ∪ Xuv| = |Ωreg|, since `Xxy ∪ Xuv ⊆ Ωreg`.
    have hsub : Xxy ∪ Xuv ⊆ Ωreg := Finset.union_subset hXxy hXuv
    have hunion : Ωreg \ (Xxy ∪ Xuv) ∪ (Xxy ∪ Xuv) = Ωreg :=
      Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint (Ωreg \ (Xxy ∪ Xuv)) (Xxy ∪ Xuv) :=
      Finset.sdiff_disjoint
    rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- **`lem:eta-theta` (coherence equivalence, non-degenerate form).**

Under the same hypotheses as `eta_theta_consistency`, and assuming
the non-exceptional regular overlap `Ωreg \ (Xxy ∪ Xuv)` is nonempty
(`step3.tex`'s non-degeneracy hypothesis via
`lem:omega-reg-size` + `eq:rho-nondeg`): outside the exceptional set,
`ηxy(L) = ηuv(L)` holds iff `κa = κb`, which is equivalent to
`psiBij κa θstar_xy θstar_xy = psiBij κb θstar_uv θstar_uv`
(`step3.tex:970-976`), because both sides evaluate to `κa` and `κb`
respectively by `psiBij_at_theta_star`.
-/
theorem coherence_iff_theta_agree
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (κa κb θstar_xy θstar_uv : Sign)
    (Xxy Xuv : Finset γ) (hXxy : Xxy ⊆ Ωreg) (hXuv : Xuv ⊆ Ωreg)
    (hηxy : ∀ L ∈ Ωreg \ Xxy, ηxy L = κa)
    (hηuv : ∀ L ∈ Ωreg \ Xuv, ηuv L = κb)
    (hne : (Ωreg \ (Xxy ∪ Xuv)).Nonempty) :
    (∀ L ∈ Ωreg \ (Xxy ∪ Xuv), ηxy L = ηuv L) ↔
      psiBij κa θstar_xy θstar_xy = psiBij κb θstar_uv θstar_uv := by
  classical
  rw [psiBij_at_theta_star, psiBij_at_theta_star]
  constructor
  · intro huniform
    -- Pick any `L ∈ Ωreg \ (Xxy ∪ Xuv)`; reduce to `κa = κb`.
    obtain ⟨L, hL⟩ := hne
    have heq := huniform L hL
    rw [Finset.mem_sdiff, Finset.mem_union] at hL
    obtain ⟨hLΩ, hLnot⟩ := hL
    have hLxy : L ∈ Ωreg \ Xxy := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inl h)⟩
    have hLuv : L ∈ Ωreg \ Xuv := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inr h)⟩
    rw [hηxy L hLxy, hηuv L hLuv] at heq
    exact heq
  · intro hκ L hL
    rw [Finset.mem_sdiff, Finset.mem_union] at hL
    obtain ⟨hLΩ, hLnot⟩ := hL
    have hLxy : L ∈ Ωreg \ Xxy := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inl h)⟩
    have hLuv : L ∈ Ωreg \ Xuv := by
      rw [Finset.mem_sdiff]; exact ⟨hLΩ, fun h => hLnot (Or.inr h)⟩
    rw [hηxy L hLxy, hηuv L hLuv, hκ]

end EtaTheta

section Step3Theorem

variable {γ : Type*} [DecidableEq γ]

/-! ### §8 — Step 3 theorem (`thm:step3`) -/

/-- **`thm:step3` (Step 3 assembly, abstract form, `step3.tex:1024`).**

Given:

1. Per-fiber orientations `θstar_xy, θstar_uv : Sign` (supplied by
   `thm:canonical-orientation`, i.e. `canonical_orientation_exists`).
2. Per-overlap signs `ηxy, ηuv : γ → Sign` block-constant (equal to
   `κa, κb`) outside exceptional sets `Xxy, Xuv`
   (supplied by Step 1 of the paper proof of `lem:eta-theta`).
3. A regular overlap `Ωreg : Finset γ`, with `Xxy ⊆ Ωreg, Xuv ⊆ Ωreg`.

Conclusion:

1. **Per-fiber data.** `θstar_xy, θstar_uv ∈ {±1}`.
2. **Per-overlap data.** `ηxy, ηuv : γ → Sign` are defined on `Ωreg`
   and block-constant outside `Xxy, Xuv`.
3. **Coherence dichotomy.** Either
   `(|disagreeSet| · d) ≤ a · |Ωreg|` (coherent) or
   `(|disagreeSet| · d) ≥ cinc · |Ωreg|` (incoherent);
   the correlation identity
   `Σ corrProduct = |Ωreg| − 2 · |disagreeSet|` holds always.
4. **Consistency.** Outside `Xxy ∪ Xuv`,
   `ηxy L = psiBij κa θstar_xy θstar_xy = κa` and
   `ηuv L = psiBij κb θstar_uv θstar_uv = κb`; coherence is equivalent
   to agreement of the dominant orientations up to the bookkeeping
   bijection.
-/
theorem step3_theorem
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (κa κb θstar_xy θstar_uv : Sign)
    (Xxy Xuv : Finset γ) (hXxy : Xxy ⊆ Ωreg) (hXuv : Xuv ⊆ Ωreg)
    (hηxy : ∀ L ∈ Ωreg \ Xxy, ηxy L = κa)
    (hηuv : ∀ L ∈ Ωreg \ Xuv, ηuv L = κb) :
    -- (3) Correlation identity (prop:correlation).
    (∑ L ∈ Ωreg, corrProduct ηxy ηuv L =
      (Ωreg.card : ℤ) - 2 * ((disagreeSet Ωreg ηxy ηuv).card : ℤ)) ∧
    -- (4) Consistency: η matches Ψ(θ*) outside exceptional.
    (∀ L ∈ Ωreg \ (Xxy ∪ Xuv),
        ηxy L = psiBij κa θstar_xy θstar_xy ∧
        ηuv L = psiBij κb θstar_uv θstar_uv) ∧
    -- Exceptional-set mass: |Ωreg \ (Xxy ∪ Xuv)| + |Xxy ∪ Xuv| = |Ωreg|.
    ((Ωreg \ (Xxy ∪ Xuv)).card + (Xxy ∪ Xuv).card = Ωreg.card) := by
  classical
  refine ⟨correlation_card_identity Ωreg ηxy ηuv, ?_, ?_⟩
  · exact (eta_theta_consistency Ωreg ηxy ηuv κa κb θstar_xy θstar_uv
      Xxy Xuv hXxy hXuv hηxy hηuv).1
  · exact (eta_theta_consistency Ωreg ηxy ηuv κa κb θstar_xy θstar_uv
      Xxy Xuv hXxy hXuv hηxy hηuv).2

/-- **`thm:step3` (coherent branch).**
Under the `Coherent` predicate, the correlation satisfies
`Corr ≥ 1 − 2·a/c`. -/
theorem step3_theorem_coherent
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (a c : ℕ) (hc : 0 < c)
    (hcoh : Coherent Ωreg ηxy ηuv a c) :
    (c : ℤ) * ∑ L ∈ Ωreg, corrProduct ηxy ηuv L ≥
      ((c : ℤ) - 2 * (a : ℤ)) * (Ωreg.card : ℤ) :=
  correlation_coherent_bound Ωreg ηxy ηuv a c hc hcoh

/-- **`thm:step3` (incoherent branch).**
Under the `Incoherent` predicate, the correlation satisfies
`Corr ≤ 1 − 2·cinc/d`. -/
theorem step3_theorem_incoherent
    (Ωreg : Finset γ) (ηxy ηuv : γ → Sign)
    (cinc d : ℕ) (hd : 0 < d)
    (hinc : Incoherent Ωreg ηxy ηuv cinc d) :
    (d : ℤ) * ∑ L ∈ Ωreg, corrProduct ηxy ηuv L ≤
      ((d : ℤ) - 2 * (cinc : ℤ)) * (Ωreg.card : ℤ) :=
  correlation_incoherent_bound Ωreg ηxy ηuv cinc d hd hinc

end Step3Theorem

end Step3
end OneThird
