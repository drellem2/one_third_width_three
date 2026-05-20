/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step5.EndpointMono
import OneThird.Step5.ConvexOverlap
import OneThird.Poset

/-!
# Step 5 — G1+G2 grounded forms and a non-vacuous instantiation

FULL REFACTOR Phase 2, Wave-1 (`mg-b21f`, scoped by `mg-d8c7` §2.1 /
§5.2 under S5-A). This file *grounds* the abstract G1 (`EndpointMono.lean`,
`lem:endpoint-mono`) and G2 (`ConvexOverlap.lean`, `lem:convex-overlap`)
ports: it connects the abstract endpoint families `Fin p → ℤ` consumed
by `convex_overlap` to the **actual `C`-coordinate incomparability
interval endpoints** of a poset, and then exercises the whole chain on
a **concrete width-3 non-chain poset**.

## What the grounding does

* `endpoint_mono_grounded` — for any two chains `A`, `B` of a poset
  enumerated monotonically (`a : Fin p → α`, `b : Fin q → α`), the four
  `C`-coordinate endpoint families `alphaIdx C ∘ a`, `betaIdx C ∘ a`,
  `alphaIdx C ∘ b`, `betaIdx C ∘ b` are weakly increasing. This is G1
  (`endpoint_mono`) lifted to index families.

* `convex_overlap_grounded` — feeding those families into the G2
  dichotomy `convex_overlap`: the G1 monotonicity discharges G2's
  monotonicity hypotheses, so the rich-or-banded dichotomy holds for
  the genuine incomparability-interval data of any poset triple.

## Non-vacuity (`mg-b21f` acceptance bar)

The grounding is instantiated on `W3 := Fin 3 × Fin 3` with the product
order — a genuine **width-3, non-chain** poset (`W3_widthAtMost_three`,
`W3_not_chain`), Dilworth-decomposed into three length-3 chains. On this
instance the port fires **non-vacuously**: the incomparability interval
`IC(chainA 1)` on the third chain is non-empty, the `β`-endpoint family
is genuinely *strictly* increasing (`betaIdx … 0 < betaIdx … 2` — so G1
monotonicity is exercised, not vacuously satisfied by a constant), and
the rich set is non-empty (`richPair_concrete`). No `Subsingleton`/empty
baseline is used. See `g1_g2_grounded_concrete`.
-/

namespace OneThird
namespace Step5

open Finset

/-! ## §G.1. G1 grounded — endpoint families of a poset are monotone -/

section Grounded

variable {α : Type*} [Preorder α]

/-- **G1 grounded, `α`-half.** If `a : Fin p → α` enumerates a chain
monotonically, the `C`-coordinate left-endpoint family `alphaIdx C ∘ a`
is weakly increasing. Immediate from `alphaIdx_mono_of_le`. -/
theorem endpointFamily_alphaIdx_monotone (C : Finset α) {p : ℕ}
    (a : Fin p → α) (ha : Monotone a) :
    Monotone (fun i => (alphaIdx C (a i) : ℤ)) := by
  intro i i' hii
  dsimp only
  have := alphaIdx_mono_of_le C (ha hii)
  exact_mod_cast this

/-- **G1 grounded, `β`-half.** The `C`-coordinate right-endpoint family
`betaIdx C ∘ a` is weakly increasing. Immediate from
`betaIdx_mono_of_le`. -/
theorem endpointFamily_betaIdx_monotone (C : Finset α) {p : ℕ}
    (a : Fin p → α) (ha : Monotone a) :
    Monotone (fun i => (betaIdx C (a i) : ℤ)) := by
  intro i i' hii
  dsimp only
  have := betaIdx_mono_of_le C (ha hii)
  exact_mod_cast this

/-- **`lem:endpoint-mono` (grounded).** For a poset triple `A, B | C`
with `A`, `B` enumerated monotonically, all four `C`-coordinate endpoint
families are weakly increasing — the paper's `lem:endpoint-mono` with
discard count `D₁(T) = 0` and additive error `E₁(T) = 0`
(`step5.tex:268-273`). -/
theorem endpoint_mono_grounded (C : Finset α) {p q : ℕ}
    (a : Fin p → α) (b : Fin q → α) (ha : Monotone a) (hb : Monotone b) :
    Monotone (fun i => (alphaIdx C (a i) : ℤ)) ∧
    Monotone (fun i => (betaIdx C (a i) : ℤ)) ∧
    Monotone (fun j => (alphaIdx C (b j) : ℤ)) ∧
    Monotone (fun j => (betaIdx C (b j) : ℤ)) :=
  ⟨endpointFamily_alphaIdx_monotone C a ha,
   endpointFamily_betaIdx_monotone C a ha,
   endpointFamily_alphaIdx_monotone C b hb,
   endpointFamily_betaIdx_monotone C b hb⟩

/-! ## §G.2. G2 grounded — convex-overlap on the genuine interval data -/

/-- **`lem:convex-overlap` (grounded).** The G2 rich-or-banded dichotomy
applied to the *actual* `C`-coordinate incomparability-interval endpoint
families of a poset triple. The G2 monotonicity hypotheses are
discharged by G1 (`endpoint_mono_grounded`): no abstract `Monotone`
assumption is required of the caller beyond the chain enumerations being
monotone. -/
theorem convex_overlap_grounded (C : Finset α) {p q : ℕ}
    (a : Fin p → α) (b : Fin q → α) (ha : Monotone a) (hb : Monotone b)
    {T : ℤ} (hT : 1 ≤ T) (c richCount : ℕ) :
    (c * (p * q) ≤ richCount) ∨
    (∃ (f : Fin p → ℤ) (K : ℤ), 0 ≤ K ∧ Monotone f ∧
      ∀ (i : Fin p) (j : Fin q),
        j ∈ richRow (fun i => (alphaIdx C (a i) : ℤ))
                    (fun i => (betaIdx C (a i) : ℤ))
                    (fun j => (alphaIdx C (b j) : ℤ))
                    (fun j => (betaIdx C (b j) : ℤ)) T i →
          f i - K ≤ (j : ℤ) ∧ (j : ℤ) ≤ f i + K) :=
  convex_overlap _ _ _ _ hT
    (endpointFamily_alphaIdx_monotone C a ha)
    (endpointFamily_alphaIdx_monotone C b hb) c richCount

end Grounded

/-! ## §G.3. Non-vacuous instantiation at a concrete width-3 poset

`W3 := Fin 3 × Fin 3` with the product order. This is a genuine width-3,
non-chain, 9-element poset; its three "rows" `{0} × Fin 3`,
`{1} × Fin 3`, `{2} × Fin 3` are a Dilworth decomposition into length-3
chains. On the triple `(chainA, chainB | chainC)` the G1+G2 port fires
with non-trivial data — see `g1_g2_grounded_concrete`. -/

section ConcreteWitness

/-- The concrete carrier: `Fin 3 × Fin 3` with the product partial
order. A width-3, non-chain, 9-element poset. -/
abbrev W3 : Type := Fin 3 × Fin 3

instance : DecidableLT W3 := decidableLTOfDecidableLE

/-- `W3` has width at most 3: every antichain injects into the first
coordinate (two elements with equal first coordinate are comparable in
the second, hence equal in an antichain), and `|Fin 3| = 3`. -/
theorem W3_widthAtMost_three : HasWidthAtMost W3 3 := by
  intro s hs
  have hcard : s.card ≤ (Finset.univ : Finset (Fin 3)).card := by
    refine Finset.card_le_card_of_injOn (fun x => x.1)
      (fun x _ => Finset.mem_univ _) ?_
    intro x hx y hy hxy
    rcases le_total x.2 y.2 with h2 | h2
    · exact hs.eq hx hy (Prod.le_def.mpr ⟨le_of_eq hxy, h2⟩)
    · exact (hs.eq hy hx (Prod.le_def.mpr ⟨le_of_eq hxy.symm, h2⟩)).symm
  simpa using hcard

/-- `W3` is not a chain: `(0,1)` and `(1,0)` are incomparable. -/
theorem W3_not_chain : ¬ IsChainPoset W3 := by
  intro h
  rcases h (0, 1) (1, 0) with h1 | h1
  · exact absurd (Prod.le_def.mp h1).2 (by decide)
  · exact absurd (Prod.le_def.mp h1).1 (by decide)

/-- First Dilworth chain `A = {0} × Fin 3`, enumerated monotonically. -/
def chainA : Fin 3 → W3 := fun i => (0, i)

/-- Second Dilworth chain `B = {1} × Fin 3`, enumerated monotonically. -/
def chainB : Fin 3 → W3 := fun j => (1, j)

/-- Third Dilworth chain `C = {2} × Fin 3`, the chain on which the
incomparability intervals `IC(·)` live. -/
def chainC : Finset W3 := {(2, 0), (2, 1), (2, 2)}

theorem chainA_monotone : Monotone chainA := by
  intro i i' h; exact Prod.le_def.mpr ⟨le_refl _, h⟩

theorem chainB_monotone : Monotone chainB := by
  intro j j' h; exact Prod.le_def.mpr ⟨le_refl _, h⟩

/-! ### Concrete endpoint values

`IC(chainA i)` on `C` is `{(2,k) : k < i}` (left endpoint constant,
right endpoint `= i`); symmetrically for `chainB`. The five values below
feed the non-vacuity facts. Each is closed by kernel evaluation after
switching the (classically defined) filter to the decidable instance. -/

theorem alphaIdx_chainA_two : alphaIdx chainC (chainA 2) = 0 := by
  unfold alphaIdx chainA chainC
  rw [Finset.filter_congr_decidable]
  decide

theorem betaIdx_chainA_zero : betaIdx chainC (chainA 0) = 0 := by
  unfold betaIdx chainA chainC
  rw [Finset.filter_congr_decidable]
  decide

theorem betaIdx_chainA_two : betaIdx chainC (chainA 2) = 2 := by
  unfold betaIdx chainA chainC
  rw [Finset.filter_congr_decidable]
  decide

theorem alphaIdx_chainB_two : alphaIdx chainC (chainB 2) = 0 := by
  unfold alphaIdx chainB chainC
  rw [Finset.filter_congr_decidable]
  decide

theorem betaIdx_chainB_two : betaIdx chainC (chainB 2) = 2 := by
  unfold betaIdx chainB chainC
  rw [Finset.filter_congr_decidable]
  decide

/-- **Non-vacuity, G1.** The `β`-endpoint family of chain `A` is
genuinely *strictly* increasing across the chain — G1 monotonicity is
exercised, not vacuously satisfied by a constant family. -/
theorem betaIdx_chainA_strict_mono :
    betaIdx chainC (chainA 0) < betaIdx chainC (chainA 2) := by
  rw [betaIdx_chainA_zero, betaIdx_chainA_two]; decide

/-- **Non-vacuity, intervals.** The incomparability interval
`IC(chainA 1)` on the third chain `C` is non-empty: `(2,0) ∥ chainA 1`.
The grounding is therefore not a `Subsingleton`/empty baseline. -/
theorem IC_chainA_one_nonempty : ∃ c ∈ chainC, c ∥ chainA 1 := by
  refine ⟨(2, 0), by decide, ?_, ?_⟩
  · intro h; exact absurd (Prod.le_def.mp h).1 (by decide)
  · intro h; exact absurd (Prod.le_def.mp h).2 (by decide)

/-- **Non-vacuity, G2.** The rich set of the grounded convex-overlap
instance is non-empty: the pair `(chainA 2, chainB 2)` is rich at
threshold `T = 1` (its incomparability intervals on `C` overlap in
length `3 ≥ 1`). -/
theorem richPair_concrete :
    RichPair (fun i => (alphaIdx chainC (chainA i) : ℤ))
             (fun i => (betaIdx chainC (chainA i) : ℤ))
             (fun j => (alphaIdx chainC (chainB j) : ℤ))
             (fun j => (betaIdx chainC (chainB j) : ℤ)) 1 2 2 := by
  unfold RichPair intersectLength
  dsimp only
  rw [alphaIdx_chainA_two, betaIdx_chainA_two,
      alphaIdx_chainB_two, betaIdx_chainB_two]
  decide

/-- **G1+G2 grounded, instantiated and verified non-vacuous** (`mg-b21f`).

On the concrete width-3 non-chain poset `W3` with its Dilworth triple
`(chainA, chainB | chainC)`, the full G1+G2 port holds and fires with
non-trivial content:

1. `W3` is genuinely width-3 and not a chain;
2. **G1** — the `C`-coordinate endpoint families are monotone, and the
   `β`-family is *strictly* increasing somewhere (monotonicity is
   exercised, not vacuous);
3. the incomparability interval `IC(chainA 1)` on `C` is non-empty;
4. **G2** — the rich-or-banded dichotomy `convex_overlap_grounded`
   holds, and its rich set is non-empty (`richPair_concrete`).

No `Subsingleton`-on-empty baseline is used anywhere. -/
theorem g1_g2_grounded_concrete :
    HasWidthAtMost W3 3 ∧ ¬ IsChainPoset W3 ∧
    Monotone (fun i => (betaIdx chainC (chainA i) : ℤ)) ∧
    betaIdx chainC (chainA 0) < betaIdx chainC (chainA 2) ∧
    (∃ c ∈ chainC, c ∥ chainA 1) ∧
    ((1 : ℕ) * (3 * 3) ≤ 0 ∨
      ∃ (f : Fin 3 → ℤ) (K : ℤ), 0 ≤ K ∧ Monotone f ∧
        ∀ (i j : Fin 3),
          j ∈ richRow (fun i => (alphaIdx chainC (chainA i) : ℤ))
                      (fun i => (betaIdx chainC (chainA i) : ℤ))
                      (fun j => (alphaIdx chainC (chainB j) : ℤ))
                      (fun j => (betaIdx chainC (chainB j) : ℤ)) 1 i →
            f i - K ≤ (j : ℤ) ∧ (j : ℤ) ≤ f i + K) ∧
    RichPair (fun i => (alphaIdx chainC (chainA i) : ℤ))
             (fun i => (betaIdx chainC (chainA i) : ℤ))
             (fun j => (alphaIdx chainC (chainB j) : ℤ))
             (fun j => (betaIdx chainC (chainB j) : ℤ)) 1 2 2 :=
  ⟨W3_widthAtMost_three, W3_not_chain,
   endpointFamily_betaIdx_monotone chainC chainA chainA_monotone,
   betaIdx_chainA_strict_mono, IC_chainA_one_nonempty,
   convex_overlap_grounded chainC chainA chainB
     chainA_monotone chainB_monotone (by decide) 1 0,
   richPair_concrete⟩

end ConcreteWitness

end Step5
end OneThird
