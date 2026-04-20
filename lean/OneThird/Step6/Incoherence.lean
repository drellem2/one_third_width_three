/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 6 — Formal definition of incoherent active pair (G2)

Formalises the incoherence definition of `step6.tex`
(`step6.tex:966-1046`).

For each rich interface `α = (x, y) ∈ Rich⋆`, Step 2 produces an
orientation `σ_α ∈ {±1}` and an exceptional set `B_α`. For every
ordered pair `(α, β)` on the regular overlap
`Ω_{αβ} := (F_α ∩ F_β) ∖ (B_α ∪ B_β)`, Step 3 supplies local signs
`η_α(L), η_β(L) ∈ {±1}` (`Def:eta`) recording which of the two
oriented BK moves on the common overlap axis lies in the
positive-cone of the corresponding staircase.

The pair is **active** if the weighted overlap `w_{αβ}` exceeds the
active threshold `w₀`. It is **incoherent** (equivalently, **bad**)
if the disagreement fraction of the two local signs exceeds a
threshold `c_inc`:

  `Pr_{L ∈ Ω_{αβ}}[η_α(L) ≠ η_β(L)] ≥ c_inc`.

Equivalently (see `correlation_disagree_identity`), the correlation
`Corr(α, β) := E[η_α · η_β]` is at most `1 - 2·c_inc`.

## Content

* `Sign` — a local-sign value, i.e. `Bool` (with `false ↦ +1`,
  `true ↦ -1`).
* `disagreeSet` — the Finset of `L ∈ Ω_{αβ}` where the two signs
  disagree.
* `activePair`, `incoherentPair`, `badPair`, `coherentPair` — the
  four paper-level predicates in cleared-denominator form.
* `badPair_iff_active_incoherent` — `bad = active ∧ incoherent`.
* `activePair_partition` — every active pair is bad or coherent.
* `correlation_disagree_identity` — relates `Corr` and
  `Pr[η_α ≠ η_β]`: `Σ η_α · η_β = |Ω| - 2·|disagree|`.
* `badPair_quantitative_incoherence` — bad active pair has
  incoherence fraction `≥ c_inc` on its overlap.
-/

namespace OneThird
namespace Step6

open Finset
open scoped BigOperators

/-! ### Local signs and disagreement -/

/-- **Local sign** (`step6.tex:985`). A value in `{+1, -1}`, encoded
as `Bool` with `false ↦ +1`, `true ↦ -1`. -/
abbrev Sign := Bool

/-- The numerical value `±1 : ℤ` of a sign. -/
def Sign.toInt : Sign → ℤ
  | false => 1
  | true  => -1

/-- **Disagreement set** (`step6.tex:1004`).
Given a regular overlap `Ω : Finset LinExt` and two sign functions
`η_α, η_β : LinExt → Sign`, the `disagreeSet` is the subset of
`Ω` on which `η_α ≠ η_β`. -/
def disagreeSet {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) : Finset LinExt :=
  Ω.filter (fun L => η_α L ≠ η_β L)

/-- Cardinality of `disagreeSet`. -/
def disagreeCount {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) : ℕ :=
  (disagreeSet Ω η_α η_β).card

lemma disagreeSet_subset {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) :
    disagreeSet Ω η_α η_β ⊆ Ω :=
  Finset.filter_subset _ _

lemma disagreeCount_le {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) :
    disagreeCount Ω η_α η_β ≤ Ω.card :=
  Finset.card_le_card (disagreeSet_subset Ω η_α η_β)

/-- **Agreement set**, the complement of `disagreeSet` inside `Ω`. -/
def agreeSet {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) : Finset LinExt :=
  Ω.filter (fun L => η_α L = η_β L)

lemma agree_disagree_card {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) :
    (agreeSet Ω η_α η_β).card + disagreeCount Ω η_α η_β = Ω.card := by
  have := Finset.card_filter_add_card_filter_not
    (s := Ω) (p := fun L => η_α L = η_β L)
  simpa [agreeSet, disagreeSet, disagreeCount] using this

/-- **Correlation** of two sign functions on the overlap
(`step6.tex:1011`): `∑ η_α(L) · η_β(L) ∈ ℤ`. -/
def correlationSum {LinExt : Type*} (Ω : Finset LinExt)
    (η_α η_β : LinExt → Sign) : ℤ :=
  ∑ L ∈ Ω, (η_α L).toInt * (η_β L).toInt

/-- **Correlation–disagreement identity** (`step6.tex:1008-1013`).

`∑_{L ∈ Ω} η_α(L) · η_β(L) = |Ω| - 2 · disagreeCount`.

So `Corr(α, β) = 1 - 2 · Pr[η_α ≠ η_β]`. -/
theorem correlation_disagree_identity {LinExt : Type*}
    (Ω : Finset LinExt) (η_α η_β : LinExt → Sign) :
    correlationSum Ω η_α η_β =
      (Ω.card : ℤ) - 2 * (disagreeCount Ω η_α η_β : ℤ) := by
  classical
  unfold correlationSum
  -- Partition Ω by the predicate `η_α L = η_β L`.
  have hsplit :
      (∑ L ∈ Ω, (η_α L).toInt * (η_β L).toInt)
        = (∑ L ∈ Ω.filter (fun L => η_α L = η_β L),
              (η_α L).toInt * (η_β L).toInt)
          + (∑ L ∈ Ω.filter (fun L => ¬ η_α L = η_β L),
              (η_α L).toInt * (η_β L).toInt) := by
    rw [← Finset.sum_filter_add_sum_filter_not Ω (fun L => η_α L = η_β L)]
  -- Value on each part.
  have hagree :
      (∑ L ∈ Ω.filter (fun L => η_α L = η_β L),
          (η_α L).toInt * (η_β L).toInt) =
        ((Ω.filter (fun L => η_α L = η_β L)).card : ℤ) := by
    rw [show
          (∑ L ∈ Ω.filter (fun L => η_α L = η_β L),
              (η_α L).toInt * (η_β L).toInt) =
          (∑ _L ∈ Ω.filter (fun L => η_α L = η_β L), (1 : ℤ)) from
          Finset.sum_congr rfl (by
            intro L hL
            rw [Finset.mem_filter] at hL
            rw [hL.2]
            rcases η_β L <;> simp [Sign.toInt])]
    simp
  have hdisagree :
      (∑ L ∈ Ω.filter (fun L => ¬ η_α L = η_β L),
          (η_α L).toInt * (η_β L).toInt) =
        - ((Ω.filter (fun L => ¬ η_α L = η_β L)).card : ℤ) := by
    rw [show
          (∑ L ∈ Ω.filter (fun L => ¬ η_α L = η_β L),
              (η_α L).toInt * (η_β L).toInt) =
          (∑ _L ∈ Ω.filter (fun L => ¬ η_α L = η_β L), (-1 : ℤ)) from
          Finset.sum_congr rfl (by
            intro L hL
            rw [Finset.mem_filter] at hL
            obtain ⟨_, hne⟩ := hL
            rcases hαL : η_α L <;> rcases hβL : η_β L <;>
              simp_all [Sign.toInt])]
    simp
  -- Combine.
  rw [hsplit, hagree, hdisagree]
  have hac := agree_disagree_card Ω η_α η_β
  have hne :
      (Ω.filter (fun L => ¬ η_α L = η_β L))
        = disagreeSet Ω η_α η_β := by
    unfold disagreeSet; rfl
  have hag :
      (Ω.filter (fun L => η_α L = η_β L))
        = agreeSet Ω η_α η_β := by
    unfold agreeSet; rfl
  rw [hne, hag]
  have hacZ : ((agreeSet Ω η_α η_β).card : ℤ)
      + (disagreeCount Ω η_α η_β : ℤ) = (Ω.card : ℤ) := by
    exact_mod_cast hac
  have hdc : (disagreeCount Ω η_α η_β : ℤ) = ((disagreeSet Ω η_α η_β).card : ℤ) := by
    unfold disagreeCount
    rfl
  linarith [hacZ, hdc]

/-! ### Active / bad / coherent pair definitions
(`step6.tex:255-259`, `step6.tex:999-1046`) -/

/-- **Active pair** (`step6.tex:255-259`).
`(α, β)` is active when `w_{αβ}` exceeds the active threshold `w₀`. -/
def activePair {Pair : Type*} (w₀ : ℕ) (w : Pair → Pair → ℕ)
    (α β : Pair) : Prop :=
  w₀ ≤ w α β

/-- **Incoherent pair** (`def:incoherent-pair`, `step6.tex:999-1007`).
`(α, β)` is incoherent if the disagreement fraction on `Ω_{αβ}` is
at least `c_inc_n / c_inc_d`. -/
def incoherentPair {Pair LinExt : Type*} (c_inc_n c_inc_d : ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) : Prop :=
  c_inc_n * (Ω α β).card ≤
    c_inc_d * disagreeCount (Ω α β) (η α) (η β)

/-- **Bad pair** (`step6.tex:1001`): active **and** incoherent. -/
def badPair {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) : Prop :=
  activePair w₀ w α β ∧ incoherentPair c_inc_n c_inc_d Ω η α β

/-- **Coherent pair** (`step6.tex:1015`): active and NOT incoherent. -/
def coherentPair {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) : Prop :=
  activePair w₀ w α β ∧ ¬ incoherentPair c_inc_n c_inc_d Ω η α β

/-- **Bad = active ∧ incoherent.** -/
theorem badPair_iff_active_incoherent
    {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) :
    badPair w₀ c_inc_n c_inc_d w Ω η α β ↔
      activePair w₀ w α β ∧ incoherentPair c_inc_n c_inc_d Ω η α β :=
  Iff.rfl

/-- **Active partition** (`rem:well-defined-partition`,
`step6.tex:1032-1046`). Every active pair is bad or coherent. -/
theorem activePair_partition
    {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) (hact : activePair w₀ w α β) :
    badPair w₀ c_inc_n c_inc_d w Ω η α β ∨
      coherentPair w₀ c_inc_n c_inc_d w Ω η α β := by
  by_cases hinc : incoherentPair c_inc_n c_inc_d Ω η α β
  · exact Or.inl ⟨hact, hinc⟩
  · exact Or.inr ⟨hact, hinc⟩

/-- **Bad and coherent are disjoint.** -/
theorem badPair_coherentPair_disjoint
    {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    (α β : Pair) :
    ¬ (badPair w₀ c_inc_n c_inc_d w Ω η α β ∧
        coherentPair w₀ c_inc_n c_inc_d w Ω η α β) := by
  rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  exact h2 h1

/-- **Quantitative incoherence form** for Step 4 consumption
(`step6.tex:1042-1045`). -/
theorem badPair_quantitative_incoherence
    {Pair LinExt : Type*} (w₀ c_inc_n c_inc_d : ℕ)
    (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign)
    {α β : Pair}
    (hbad : badPair w₀ c_inc_n c_inc_d w Ω η α β) :
    c_inc_n * (Ω α β).card ≤
      c_inc_d * disagreeCount (Ω α β) (η α) (η β) :=
  hbad.2

/-! ### Bad active pairs as a `Finset` (for summation) -/

/-- **Bad active pair Finset.** -/
noncomputable def badActivePairs
    {Pair LinExt : Type*} [DecidableEq Pair]
    (richStar : Finset Pair)
    (w₀ c_inc_n c_inc_d : ℕ) (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign) : Finset (Pair × Pair) := by
  classical
  exact (richStar ×ˢ richStar).filter
    (fun p => w₀ ≤ w p.1 p.2 ∧
      c_inc_n * (Ω p.1 p.2).card ≤
        c_inc_d * disagreeCount (Ω p.1 p.2) (η p.1) (η p.2))

/-- **Coherent active pair Finset.** -/
noncomputable def coherentActivePairs
    {Pair LinExt : Type*} [DecidableEq Pair]
    (richStar : Finset Pair)
    (w₀ c_inc_n c_inc_d : ℕ) (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign) : Finset (Pair × Pair) := by
  classical
  exact (richStar ×ˢ richStar).filter
    (fun p => w₀ ≤ w p.1 p.2 ∧
      ¬ (c_inc_n * (Ω p.1 p.2).card ≤
          c_inc_d * disagreeCount (Ω p.1 p.2) (η p.1) (η p.2)))

lemma badActivePairs_subset
    {Pair LinExt : Type*} [DecidableEq Pair]
    (richStar : Finset Pair)
    (w₀ c_inc_n c_inc_d : ℕ) (w : Pair → Pair → ℕ)
    (Ω : Pair → Pair → Finset LinExt)
    (η : Pair → LinExt → Sign) :
    badActivePairs richStar w₀ c_inc_n c_inc_d w Ω η ⊆
      richStar ×ˢ richStar := by
  classical
  unfold badActivePairs
  exact Finset.filter_subset _ _

end Step6
end OneThird
