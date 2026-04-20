/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import OneThird.Mathlib.LinearExtension.Fintype
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The Bubley–Karzanov (BK) graph on linear extensions

For a finite poset `α`, the **Bubley–Karzanov graph** `bkGraph α` is the
graph on `LinearExt α` with two extensions adjacent iff they differ by
a single adjacent transposition of an incomparable pair. This is the
balanced Kleitman / Karzanov graph that drives the conductance
arguments of Step 8 (`step8.tex` Theorem E) and the random-walk model
underlying the entire 1/3–2/3 program.

This file lives in the `OneThird/Mathlib/` tier — its results are
intentionally independent of the 1/3–2/3 conjecture and could be
extracted into mathlib as a standalone module on linear-extension
random walks.

## Main definitions

* `OneThird.BKAdj L L'` — the BK adjacency relation: `L` and `L'`
  differ by exactly one adjacent transposition of an incomparable
  pair.
* `OneThird.bkGraph α` — the BK graph as a `SimpleGraph (LinearExt α)`.
* `OneThird.LinearExt.swapAdj` — the linear extension obtained from
  `L` by swapping two adjacent elements at positions `k`, `k+1` when
  those elements are incomparable.

## Main results

* `OneThird.BKAdj.symm` — BK adjacency is symmetric.
* `OneThird.BKAdj.irrefl` — BK adjacency is irreflexive.
* `OneThird.BKAdj.ne` — BK-adjacent extensions are unequal.
* `OneThird.bkGraph_preconnected` — the BK graph is preconnected
  (Bubley–Karzanov 1991): any two linear extensions are joined by a
  walk of adjacent-incomparable swaps. The proof is by strong
  induction on the Kendall-tau style inversion count between `L`
  and `L'`: if they differ, the permutation `σ = L^{-1} ∘ L'` has
  an adjacent descent, whose elements must be incomparable and whose
  `swapAdj` strictly decreases the inversion count.

## References

* R. Bubley and M. Dyer, *Faster random generation of linear
  extensions*, Discrete Math. 201 (1999), 81–88.
* A. Karzanov and L. Khachiyan, *On the conductance of order Markov
  chains*, Order 8 (1991), 7–15.
-/

open SimpleGraph

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Bubley–Karzanov adjacency.** Two linear extensions `L`, `L'`
of a finite poset `α` are BK-adjacent iff they agree everywhere
except on an incomparable pair `(x, y)` whose positions differ by a
single adjacent transposition: `L` places `x` at position `k` and
`y` at `k+1`, while `L'` swaps them. -/
def BKAdj (L L' : LinearExt α) : Prop :=
  ∃ (x y : α) (k : Fin (Fintype.card α)) (hk : k.val + 1 < Fintype.card α),
    (x ∥ y) ∧
      L.pos x = k ∧
      L.pos y = ⟨k.val + 1, hk⟩ ∧
      L'.pos x = ⟨k.val + 1, hk⟩ ∧
      L'.pos y = k ∧
      ∀ z : α, z ≠ x → z ≠ y → L.pos z = L'.pos z

namespace BKAdj

/-- BK adjacency is symmetric: swap the roles of `x` and `y`. -/
theorem symm {L L' : LinearExt α} (h : BKAdj L L') : BKAdj L' L := by
  obtain ⟨x, y, k, hk, hxy, hLx, hLy, hL'x, hL'y, hrest⟩ := h
  refine ⟨y, x, k, hk, hxy.symm, hL'y, hL'x, hLy, hLx, ?_⟩
  intro z hzy hzx
  exact (hrest z hzx hzy).symm

/-- BK adjacency is irreflexive: an incomparable pair cannot occupy
both positions `k` and `k+1` simultaneously in a single extension. -/
theorem irrefl (L : LinearExt α) : ¬ BKAdj L L := by
  rintro ⟨x, y, k, hk, _, hLx, _, hL'x, _, _⟩
  -- From `L.pos x = k` and `L.pos x = ⟨k+1, hk⟩` we get `k.val = k.val + 1`.
  have hkk : (k : Fin (Fintype.card α)) = ⟨k.val + 1, hk⟩ :=
    hLx.symm.trans hL'x
  have : k.val = k.val + 1 := by simpa using congrArg Fin.val hkk
  omega

/-- BK-adjacent extensions are unequal. -/
theorem ne {L L' : LinearExt α} (h : BKAdj L L') : L ≠ L' := by
  rintro rfl
  exact BKAdj.irrefl L h

end BKAdj

/-- The **Bubley–Karzanov graph** of a finite poset `α`: vertices are
linear extensions of `α`, with an edge between `L` and `L'` whenever
they are obtained from one another by a single adjacent transposition
of an incomparable pair. -/
def bkGraph (α : Type*) [PartialOrder α] [Fintype α] [DecidableEq α] :
    SimpleGraph (LinearExt α) where
  Adj := BKAdj
  symm := fun _ _ => BKAdj.symm
  loopless := ⟨BKAdj.irrefl⟩

@[simp] lemma bkGraph_adj {L L' : LinearExt α} :
    (bkGraph α).Adj L L' ↔ BKAdj L L' := Iff.rfl

namespace LinearExt

/-- Swap the elements at adjacent positions `k` and `k + 1` in a
linear extension `L`. When the two elements in question are
incomparable, the result is again a linear extension. -/
def swapAdj (L : LinearExt α) (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩) :
    LinearExt α where
  toFun := L.toFun.trans (Equiv.swap k ⟨k.val + 1, hk⟩)
  monotone := by
    intro a b hab
    have hL : L.toFun a ≤ L.toFun b := L.monotone hab
    set k' : Fin (Fintype.card α) := ⟨k.val + 1, hk⟩ with hk'def
    have hk'val : k'.val = k.val + 1 := rfl
    show Equiv.swap k k' (L.toFun a) ≤ Equiv.swap k k' (L.toFun b)
    -- Rule out the "bad case" L.toFun a = k and L.toFun b = k' via
    -- incomparability.
    have hbad_imp : L.toFun a = k → L.toFun b = k' → False := by
      intro hak hbk'
      apply hincomp.1
      have ha : L.toFun.symm k = a := by
        apply L.toFun.injective
        rw [Equiv.apply_symm_apply, hak]
      have hb : L.toFun.symm k' = b := by
        apply L.toFun.injective
        rw [Equiv.apply_symm_apply, hbk']
      rw [ha, hb]; exact hab
    have hij_val : (L.toFun a).val ≤ (L.toFun b).val := hL
    rcases eq_or_ne (L.toFun a) k with hik | hik
    · rcases eq_or_ne (L.toFun b) k' with hjk' | hjk'
      · exact (hbad_imp hik hjk').elim
      · rw [hik, Equiv.swap_apply_left]
        rcases eq_or_ne (L.toFun b) k with hjk | hjk
        · rw [hjk, Equiv.swap_apply_left]
        · rw [Equiv.swap_apply_of_ne_of_ne hjk hjk']
          show k'.val ≤ (L.toFun b).val
          rw [hk'val]
          have hjk_val : (L.toFun b).val ≠ k.val := fun h => hjk (Fin.ext h)
          have hjk'_val : (L.toFun b).val ≠ k.val + 1 :=
            fun h => hjk' (Fin.ext h)
          have : k.val ≤ (L.toFun b).val := by
            have := hij_val
            rw [show (L.toFun a).val = k.val from congrArg Fin.val hik] at this
            exact this
          omega
    · rcases eq_or_ne (L.toFun a) k' with hik' | hik'
      · rw [hik', Equiv.swap_apply_right]
        rcases eq_or_ne (L.toFun b) k with hjk | hjk
        · exfalso
          have h1 : (L.toFun a).val = k.val + 1 := by
            rw [hik']
          have h2 : (L.toFun b).val = k.val := by rw [hjk]
          omega
        · rcases eq_or_ne (L.toFun b) k' with hjk' | hjk'
          · rw [hjk', Equiv.swap_apply_right]
          · rw [Equiv.swap_apply_of_ne_of_ne hjk hjk']
            show k.val ≤ (L.toFun b).val
            have hjk_val : (L.toFun b).val ≠ k.val := fun h => hjk (Fin.ext h)
            have hjk'_val : (L.toFun b).val ≠ k.val + 1 :=
              fun h => hjk' (Fin.ext h)
            have : k.val + 1 ≤ (L.toFun b).val := by
              have := hij_val
              rw [show (L.toFun a).val = k.val + 1 from
                (congrArg Fin.val hik').trans rfl] at this
              exact this
            omega
      · rw [Equiv.swap_apply_of_ne_of_ne hik hik']
        rcases eq_or_ne (L.toFun b) k with hjk | hjk
        · rw [hjk, Equiv.swap_apply_left]
          show (L.toFun a).val ≤ k'.val
          rw [hk'val]
          have hik_val : (L.toFun a).val ≠ k.val := fun h => hik (Fin.ext h)
          have hik'_val : (L.toFun a).val ≠ k.val + 1 :=
            fun h => hik' (Fin.ext h)
          have : (L.toFun a).val ≤ k.val := by
            have := hij_val
            rw [show (L.toFun b).val = k.val from congrArg Fin.val hjk] at this
            exact this
          omega
        · rcases eq_or_ne (L.toFun b) k' with hjk' | hjk'
          · rw [hjk', Equiv.swap_apply_right]
            show (L.toFun a).val ≤ k.val
            have hik_val : (L.toFun a).val ≠ k.val := fun h => hik (Fin.ext h)
            have hik'_val : (L.toFun a).val ≠ k.val + 1 :=
              fun h => hik' (Fin.ext h)
            have : (L.toFun a).val ≤ k.val + 1 := by
              have := hij_val
              rw [show (L.toFun b).val = k.val + 1 from
                (congrArg Fin.val hjk').trans rfl] at this
              exact this
            omega
          · rw [Equiv.swap_apply_of_ne_of_ne hjk hjk']
            exact hL

lemma pos_swapAdj_of_pos_eq (L : LinearExt α) (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    (x : α) (hx : L.pos x = k) :
    (L.swapAdj k hk hincomp).pos x = ⟨k.val + 1, hk⟩ := by
  show Equiv.swap k ⟨k.val + 1, hk⟩ (L.toFun x) = _
  rw [show L.toFun x = k from hx, Equiv.swap_apply_left]

lemma pos_swapAdj_of_pos_eq_succ (L : LinearExt α) (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    (y : α) (hy : L.pos y = ⟨k.val + 1, hk⟩) :
    (L.swapAdj k hk hincomp).pos y = k := by
  show Equiv.swap k ⟨k.val + 1, hk⟩ (L.toFun y) = _
  rw [show L.toFun y = ⟨k.val + 1, hk⟩ from hy, Equiv.swap_apply_right]

lemma pos_swapAdj_of_other (L : LinearExt α) (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩)
    {z : α} (hzk : L.pos z ≠ k) (hzk' : L.pos z ≠ ⟨k.val + 1, hk⟩) :
    (L.swapAdj k hk hincomp).pos z = L.pos z := by
  show Equiv.swap k ⟨k.val + 1, hk⟩ (L.toFun z) = _
  exact Equiv.swap_apply_of_ne_of_ne hzk hzk'

end LinearExt

/-- The `swapAdj` construction is BK-adjacent to the original extension. -/
lemma bkAdj_swapAdj (L : LinearExt α) (k : Fin (Fintype.card α))
    (hk : k.val + 1 < Fintype.card α)
    (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩) :
    BKAdj L (L.swapAdj k hk hincomp) := by
  refine ⟨L.toFun.symm k, L.toFun.symm ⟨k.val + 1, hk⟩, k, hk, hincomp, ?_,
    ?_, ?_, ?_, ?_⟩
  · show L.toFun (L.toFun.symm k) = k; simp
  · show L.toFun (L.toFun.symm ⟨k.val + 1, hk⟩) = ⟨k.val + 1, hk⟩; simp
  · apply L.pos_swapAdj_of_pos_eq; show L.toFun (L.toFun.symm k) = k; simp
  · apply L.pos_swapAdj_of_pos_eq_succ
    show L.toFun (L.toFun.symm ⟨k.val + 1, hk⟩) = ⟨k.val + 1, hk⟩; simp
  · intro z hzx hzy
    apply Eq.symm
    apply L.pos_swapAdj_of_other k hk hincomp
    · intro h
      apply hzx
      show z = L.toFun.symm k
      apply L.toFun.injective
      rw [Equiv.apply_symm_apply]; exact h
    · intro h
      apply hzy
      show z = L.toFun.symm ⟨k.val + 1, hk⟩
      apply L.toFun.injective
      rw [Equiv.apply_symm_apply]; exact h

/-- The Kendall-tau style **inversion count** between two linear
extensions: the number of ordered pairs `(a, b)` with `a` before `b`
in `L` but `b` before `a` in `L'`. -/
def invCount (L L' : LinearExt α) : ℕ :=
  ((Finset.univ : Finset (α × α)).filter
    (fun p => L.lt p.1 p.2 ∧ L'.lt p.2 p.1)).card

/-- Non-identity permutation of `Fin n` must have an adjacent descent. -/
private lemma exists_adj_descent_of_ne_refl {n : ℕ} (τ : Fin n ≃ Fin n)
    (hτ : τ ≠ Equiv.refl _) :
    ∃ (k : Fin n) (hk : k.val + 1 < n), τ ⟨k.val + 1, hk⟩ < τ k := by
  by_contra h
  push_neg at h
  -- `h : ∀ k hk, τ k ≤ τ ⟨k.val+1, hk⟩`
  apply hτ
  -- Show τ is monotone via induction on val difference, then strictly
  -- monotone via injectivity, then the identity via well-founded order.
  have hmono : Monotone τ := by
    intro i j hij
    -- Strong induction on `d = j.val - i.val`.
    suffices aux : ∀ d : ℕ, ∀ (j : Fin n), j.val = i.val + d → τ i ≤ τ j from
      aux (j.val - i.val) j (by have : i.val ≤ j.val := hij; omega)
    intro d
    induction d with
    | zero =>
      intro j hj
      have : i = j := Fin.ext hj.symm
      rw [this]
    | succ m ih =>
      intro j hj
      have hj_lt : i.val + m + 1 < n := by
        have : j.val < n := j.isLt
        omega
      have hj_prev_lt : i.val + m < n := by omega
      have hih : τ i ≤ τ ⟨i.val + m, hj_prev_lt⟩ := ih _ rfl
      have hstep : τ ⟨i.val + m, hj_prev_lt⟩ ≤ τ ⟨i.val + m + 1, hj_lt⟩ := by
        have := h ⟨i.val + m, hj_prev_lt⟩ hj_lt
        exact this
      have hj_eq : (⟨i.val + m + 1, hj_lt⟩ : Fin n) = j := Fin.ext (by
        show i.val + m + 1 = j.val
        omega)
      rw [hj_eq] at hstep
      exact hih.trans hstep
  have hstrict : StrictMono τ := hmono.strictMono_of_injective τ.injective
  apply Equiv.ext
  intro i
  exact le_antisymm hstrict.apply_le hstrict.le_apply

/-- If `L ≠ L'`, there is a swap of adjacent incomparable elements in
`L` that strictly decreases the inversion count toward `L'`. -/
private lemma exists_swapAdj_invCount_lt {L L' : LinearExt α} (hne : L ≠ L') :
    ∃ (k : Fin (Fintype.card α)) (hk : k.val + 1 < Fintype.card α)
      (hincomp : L.toFun.symm k ∥ L.toFun.symm ⟨k.val + 1, hk⟩),
      invCount (L.swapAdj k hk hincomp) L' < invCount L L' := by
  -- Build permutation `τ = L.toFun.symm.trans L'.toFun` on `Fin n`.
  set τ : Fin (Fintype.card α) ≃ Fin (Fintype.card α) :=
    L.toFun.symm.trans L'.toFun with hτdef
  have hτ : τ ≠ Equiv.refl _ := by
    intro h
    apply hne
    apply LinearExt.ext
    apply Equiv.ext
    intro a
    have : τ (L.toFun a) = L.toFun a := by rw [h]; rfl
    simp [hτdef] at this
    exact this.symm
  obtain ⟨k, hk, hdesc⟩ := exists_adj_descent_of_ne_refl τ hτ
  -- Let x, y = elements at positions k, k+1 in L.
  set x := L.toFun.symm k with hxdef
  set y := L.toFun.symm ⟨k.val + 1, hk⟩ with hydef
  have hLposx : L.pos x = k := by simp [LinearExt.pos, x]
  have hLposy : L.pos y = ⟨k.val + 1, hk⟩ := by simp [LinearExt.pos, y]
  have hL'posy_lt : L'.pos y < L'.pos x := by
    show τ ⟨k.val + 1, hk⟩ < τ k
    exact hdesc
  -- x ∥ y
  have hincomp : x ∥ y := by
    refine ⟨?_, ?_⟩
    · intro hxy
      have hmono' := L'.monotone hxy
      exact absurd hmono' (not_le.mpr hL'posy_lt)
    · intro hyx
      have hmono' : L.pos y ≤ L.pos x := L.monotone hyx
      rw [hLposy, hLposx] at hmono'
      have : k.val + 1 ≤ k.val := hmono'
      omega
  refine ⟨k, hk, hincomp, ?_⟩
  -- Now show invCount decreases.
  set L₁ := L.swapAdj k hk hincomp
  have hL₁x : L₁.pos x = ⟨k.val + 1, hk⟩ := by
    exact L.pos_swapAdj_of_pos_eq k hk hincomp x hLposx
  have hL₁y : L₁.pos y = k :=
    L.pos_swapAdj_of_pos_eq_succ k hk hincomp y hLposy
  have hL₁other : ∀ z : α, z ≠ x → z ≠ y → L₁.pos z = L.pos z := by
    intro z hzx hzy
    apply L.pos_swapAdj_of_other k hk hincomp
    · intro h
      apply hzx
      show z = L.toFun.symm k
      apply L.toFun.injective
      rw [Equiv.apply_symm_apply]
      exact h
    · intro h
      apply hzy
      show z = L.toFun.symm ⟨k.val + 1, hk⟩
      apply L.toFun.injective
      rw [Equiv.apply_symm_apply]
      exact h
  -- Show filter(L₁) ⊂ filter(L) as finsets of ordered pairs.
  unfold invCount
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · -- subset: every inversion of L₁ vs L' is also an inversion of L vs L'.
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_, hp.2.2⟩
    obtain ⟨_, hL₁lt, hL'lt⟩ := hp
    -- We need L.lt p.1 p.2.
    -- Case analyze based on whether p.1, p.2 ∈ {x, y}.
    by_cases hpx : p.1 = x
    · by_cases hpy : p.2 = y
      · -- p = (x, y): L₁.lt x y means L₁.pos x < L₁.pos y, but
        -- L₁.pos x = k+1, L₁.pos y = k, so contradiction.
        exfalso
        rw [hpx, hpy] at hL₁lt
        rw [LinearExt.lt, hL₁x, hL₁y] at hL₁lt
        have : k.val + 1 < k.val := hL₁lt
        omega
      · -- p = (x, z) with z ≠ y. L.pos z = L₁.pos z.
        rw [hpx] at hL₁lt ⊢
        -- p.2 ≠ x since L₁.lt x p.2 is strict.
        have hp2x : p.2 ≠ x := by
          intro hp2x
          rw [hp2x] at hL₁lt
          exact lt_irrefl _ hL₁lt
        have hzpos : L.pos p.2 = L₁.pos p.2 :=
          (hL₁other p.2 hp2x hpy).symm
        rw [LinearExt.lt, hL₁x] at hL₁lt
        rw [LinearExt.lt, hLposx]
        -- hL₁lt: k.val + 1 < L₁.pos p.2.val = L.pos p.2.val
        rw [← hzpos] at hL₁lt
        have : k.val + 1 < (L.pos p.2).val := hL₁lt
        show k.val < (L.pos p.2).val
        omega
    · by_cases hpy_x : p.1 = y
      · by_cases hpy_y : p.2 = y
        · exfalso
          rw [hpy_x, hpy_y] at hL₁lt
          exact (lt_irrefl _) hL₁lt
        · -- p = (y, z), z ≠ y (and z ≠ x since p.1 = y and we're in not hpx).
          rw [hpy_x] at hL₁lt ⊢
          have hzpos : L.pos p.2 = L₁.pos p.2 := by
            have hzx : p.2 ≠ x := by
              intro h; apply hpy_y
              -- But we don't have p.2 = y here; we have the negation case.
              -- Actually we have p.2 ≠ y (from not hpy_y).
              -- Need p.2 ≠ x — from hL'lt (p.2 ≠ p.1 = y since p.2 ≠ y,
              -- but that doesn't give us p.2 ≠ x directly).
              -- Actually here, we need p.2 ≠ x. Case: p = (y, x). Let's check.
              -- If p.2 = x: L'.lt x y. But we proved hL'posy_lt : L'.pos y < L'.pos x,
              -- so L'.lt x y is false. So this case is impossible.
              exfalso
              apply (not_lt.mpr (le_of_lt hL'posy_lt))
              rw [← hpy_x, ← h]
              exact hL'lt
            exact (hL₁other p.2 hzx hpy_y).symm
          rw [LinearExt.lt, hL₁y] at hL₁lt
          rw [LinearExt.lt, hLposy]
          rw [← hzpos] at hL₁lt
          have : k.val < (L.pos p.2).val := hL₁lt
          show k.val + 1 < (L.pos p.2).val
          -- need p.2 ≠ y (true) and p.2 ≠ x (handled above).
          -- L.pos p.2 ≠ k+1 (since p.2 ≠ y and pos_injective).
          have hne1 : (L.pos p.2).val ≠ k.val + 1 := by
            intro heq
            apply hpy_y
            apply L.pos_injective
            rw [hLposy]; exact Fin.ext heq
          omega
      · by_cases hpy2 : p.2 = x
        · -- p = (a, x), a ≠ x, a ≠ y. L₁.lt a x means L.pos a < k+1 = L₁.pos x.
          rw [hpy2] at hL₁lt ⊢
          have hzpos : L.pos p.1 = L₁.pos p.1 :=
            (hL₁other p.1 hpx hpy_x).symm
          rw [LinearExt.lt, hL₁x] at hL₁lt
          rw [LinearExt.lt, hLposx]
          rw [← hzpos] at hL₁lt
          have hne1 : (L.pos p.1).val ≠ k.val := by
            intro heq
            apply hpx
            apply L.pos_injective
            rw [hLposx]; exact Fin.ext heq
          have hne2 : (L.pos p.1).val ≠ k.val + 1 := by
            intro heq
            apply hpy_x
            apply L.pos_injective
            rw [hLposy]; exact Fin.ext heq
          have : (L.pos p.1).val < k.val + 1 := hL₁lt
          show (L.pos p.1).val < k.val
          omega
        · by_cases hpy3 : p.2 = y
          · -- p = (a, y), a ≠ x, a ≠ y.
            rw [hpy3] at hL₁lt ⊢
            have hzpos : L.pos p.1 = L₁.pos p.1 :=
              (hL₁other p.1 hpx hpy_x).symm
            rw [LinearExt.lt, hL₁y] at hL₁lt
            rw [LinearExt.lt, hLposy]
            rw [← hzpos] at hL₁lt
            have hne1 : (L.pos p.1).val ≠ k.val := by
              intro heq
              apply hpx
              apply L.pos_injective
              rw [hLposx]; exact Fin.ext heq
            have hne2 : (L.pos p.1).val ≠ k.val + 1 := by
              intro heq
              apply hpy_x
              apply L.pos_injective
              rw [hLposy]; exact Fin.ext heq
            have : (L.pos p.1).val < k.val := hL₁lt
            show (L.pos p.1).val < k.val + 1
            omega
          · -- p = (a, b), a, b ∉ {x, y}. L₁.pos = L.pos on both.
            have h1 : L.pos p.1 = L₁.pos p.1 :=
              (hL₁other p.1 hpx hpy_x).symm
            have h2 : L.pos p.2 = L₁.pos p.2 :=
              (hL₁other p.2 hpy2 hpy3).symm
            rw [LinearExt.lt, h1, h2]
            exact hL₁lt
  · -- not equal: pair (x, y) is in filter(L) but not filter(L₁).
    intro hsub
    have hxy_mem_L : (x, y) ∈ (Finset.univ : Finset (α × α)).filter
        (fun p => L.lt p.1 p.2 ∧ L'.lt p.2 p.1) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · show (L.pos x).val < (L.pos y).val
        rw [hLposx, hLposy]
        show k.val < k.val + 1
        omega
      · exact hL'posy_lt
    have hxy_mem_L₁ : (x, y) ∈ (Finset.univ : Finset (α × α)).filter
        (fun p => L₁.lt p.1 p.2 ∧ L'.lt p.2 p.1) := hsub hxy_mem_L
    rw [Finset.mem_filter] at hxy_mem_L₁
    have hlt : L₁.lt x y := hxy_mem_L₁.2.1
    rw [LinearExt.lt, hL₁x, hL₁y] at hlt
    have : k.val + 1 < k.val := hlt
    omega

/-- **Bubley–Karzanov connectivity.** The BK graph is preconnected:
any two linear extensions `L, L'` of `α` can be transformed into one
another by a sequence of adjacent-incomparable swaps.

The proof is by strong induction on the Kendall-tau style inversion
count `invCount L L'`: if `L = L'` the walk is trivial, otherwise the
permutation `τ = L^{-1} ∘ L'` has an adjacent descent, whose two
elements must be incomparable. Swapping them yields a BK-adjacent
extension with strictly fewer inversions, and the induction closes. -/
theorem bkGraph_preconnected (α : Type*) [PartialOrder α]
    [Fintype α] [DecidableEq α] : (bkGraph α).Preconnected := by
  intro L L'
  suffices h : ∀ (N : ℕ) (L : LinearExt α),
      invCount L L' ≤ N → (bkGraph α).Reachable L L' from
    h (invCount L L') L le_rfl
  intro N
  induction N with
  | zero =>
    intro L hN
    by_cases hLL' : L = L'
    · subst hLL'; exact SimpleGraph.Reachable.refl _
    · exfalso
      obtain ⟨k, hk, hincomp, hinvLt⟩ := exists_swapAdj_invCount_lt hLL'
      have : invCount (L.swapAdj k hk hincomp) L' < 0 := lt_of_lt_of_le hinvLt hN
      exact Nat.not_lt_zero _ this
  | succ n ih =>
    intro L hN
    by_cases hLL' : L = L'
    · subst hLL'; exact SimpleGraph.Reachable.refl _
    · obtain ⟨k, hk, hincomp, hinvLt⟩ := exists_swapAdj_invCount_lt hLL'
      have hadj : (bkGraph α).Adj L (L.swapAdj k hk hincomp) :=
        bkAdj_swapAdj L k hk hincomp
      have hN' : invCount (L.swapAdj k hk hincomp) L' ≤ n := by
        have := hinvLt
        omega
      exact hadj.reachable.trans (ih _ hN')

/-- The BK graph of any finite poset is connected: nonempty (there is
at least one linear extension by Szpilrajn) and preconnected
(Bubley–Karzanov). -/
theorem bkGraph_connected (α : Type*) [PartialOrder α]
    [Fintype α] [DecidableEq α] : (bkGraph α).Connected where
  preconnected := bkGraph_preconnected α
  nonempty := LinearExt.instNonempty

end OneThird
