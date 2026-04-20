/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import OneThird.Poset
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.Mathlib.BKGraph

/-!
# Linear extensions: balance and BK conductance quantities

Project-specific notions layered on top of the Mathlib-style basics in
`OneThird.Mathlib.LinearExtension.Fintype` and the BK graph in
`OneThird.Mathlib.BKGraph`:

* `IsBalanced`, `HasBalancedPair`, `IsGammaCounterexample`: the
  notions appearing in the main theorem and Step 8;
* `edgeBoundary`, `volume`, `Phi`: BK cut / conductance quantities.

The underlying type `LinearExt α` and the `Fintype` / counting /
`probLT` API live in `OneThird.Mathlib.LinearExtension.Fintype`. The
`BKAdj` adjacency relation (with proven symmetry / irreflexivity) and
the `bkGraph α : SimpleGraph (LinearExt α)` packaging live in
`OneThird.Mathlib.BKGraph`.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- A pair `(x, y)` is *balanced* if `1/3 ≤ Pr[x <_L y] ≤ 2/3`. -/
def IsBalanced (x y : α) : Prop :=
  (1 : ℚ) / 3 ≤ probLT x y ∧ probLT x y ≤ 2 / 3

/-- `P` *has a balanced pair* iff some incomparable pair is balanced.
The main theorem claims this for every non-chain width-3 poset. -/
def HasBalancedPair (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] : Prop :=
  ∃ x y : α, (x ∥ y) ∧ IsBalanced x y

/-- *`γ`-counterexample*: matching the paper definition at
`step8.tex:30-33`. Every incomparable pair has
`min(Pr[x<y], Pr[y<x]) < 1/3 - γ` (no pair is `γ`-close to balanced)
and the balance quantity
`β(P) := inf_{x∥y} min{Pr[x<y], Pr[y<x]}` satisfies `β(P) ≥ γ`.

Equivalently, for every incomparable pair `(x, y)`,
`p_{xy} ∈ [γ, 1/3 − γ) ∪ (2/3 + γ, 1 − γ]`. -/
def IsGammaCounterexample (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] (γ : ℚ) : Prop :=
  ∀ x y : α, (x ∥ y) →
    γ ≤ min (probLT x y) (probLT y x) ∧
      min (probLT x y) (probLT y x) < (1 : ℚ)/3 - γ

/-! ## Expansion / conductance quantities -/

/-- Edge boundary of a cut `S ⊆ LinearExt α` for the BK adjacency:
number of BK-adjacent ordered pairs `(L, L')` with `L ∈ S`, `L' ∉ S`. -/
noncomputable def edgeBoundary (S : Finset (LinearExt α)) : ℕ := by
  classical
  exact
    ((S ×ˢ (Finset.univ \ S)).filter
      (fun p : LinearExt α × LinearExt α => BKAdj p.1 p.2)).card

/-- Counting-measure volume from Step 8: `vol(S) = |S| (n − 1)`. -/
noncomputable def volume (S : Finset (LinearExt α)) : ℕ :=
  S.card * (Fintype.card α - 1)

/-- BK conductance `Φ(S) = |∂S| / min(vol S, vol Sᶜ)`. -/
noncomputable def Phi (S : Finset (LinearExt α)) : ℚ :=
  (edgeBoundary S : ℚ)
    / (min (volume S) (volume (Finset.univ \ S)) : ℚ)

/-! ## BK-Dirichlet foundation -/

/-- (private) **Swap-pair uniqueness** for the BK-graph edge
parametrization. If `(L, L')` is a BK edge whose swap acts on the
incomparable pair `(x₀, y₀)` at position `k` (i.e. the positions
of `x₀, y₀` flip between `k` and `k+1`, and every other element is
fixed), and `(x, y)` is an ordered pair with `L.lt x y` but
`¬ L'.lt x y`, then `(x, y) = (x₀, y₀)`. This is the key fact
behind the double-counting identity: each BK-adjacent ordered pair
belongs to exactly one `∂(pairCut x y)` — the one indexed by its
swap pair. -/
private lemma swap_pair_uniqueness
    {α : Type*} [PartialOrder α] [Fintype α]
    {L L' : LinearExt α} {x y x₀ y₀ : α} {k : ℕ}
    (hLxv : (L.pos x₀).val = k) (hLyv : (L.pos y₀).val = k + 1)
    (hL'xv : (L'.pos x₀).val = k + 1) (hL'yv : (L'.pos y₀).val = k)
    (hrestv : ∀ z : α, z ≠ x₀ → z ≠ y₀ → (L.pos z).val = (L'.pos z).val)
    (hLlt : (L.pos x).val < (L.pos y).val)
    (hnotL'lt : ¬ (L'.pos x).val < (L'.pos y).val) :
    x = x₀ ∧ y = y₀ := by
  classical
  by_cases hxx : x = x₀
  · by_cases hyy : y = y₀
    · exact ⟨hxx, hyy⟩
    · exfalso
      rw [hxx] at hLlt hnotL'lt
      rw [hLxv] at hLlt
      rw [hL'xv] at hnotL'lt
      by_cases hyx : y = x₀
      · rw [hyx, hLxv] at hLlt; omega
      · have hye : (L.pos y).val = (L'.pos y).val := hrestv y hyx hyy
        rw [hye] at hLlt
        have hval : (L'.pos y).val = k + 1 := by omega
        have hposy : (L.pos y).val = (L.pos y₀).val := by rw [hye, hval, hLyv]
        exact hyy (L.pos_injective (Fin.ext hposy))
  · exfalso
    by_cases hxy : x = y₀
    · rw [hxy] at hLlt hnotL'lt
      rw [hLyv] at hLlt
      rw [hL'yv] at hnotL'lt
      by_cases hyx : y = x₀
      · rw [hyx, hLxv] at hLlt; omega
      · by_cases hyy : y = y₀
        · rw [hyy, hLyv] at hLlt; omega
        · have hye : (L.pos y).val = (L'.pos y).val := hrestv y hyx hyy
          rw [hye] at hLlt; omega
    · have hxe : (L.pos x).val = (L'.pos x).val := hrestv x hxx hxy
      by_cases hyx : y = x₀
      · rw [hyx] at hLlt hnotL'lt
        rw [hLxv] at hLlt
        rw [hL'xv] at hnotL'lt
        rw [hxe] at hLlt
        omega
      · by_cases hyy : y = y₀
        · rw [hyy] at hLlt hnotL'lt
          rw [hLyv] at hLlt
          rw [hL'yv] at hnotL'lt
          rw [hxe] at hLlt
          have hval : (L'.pos x).val = k := by omega
          have hposx : (L.pos x).val = (L.pos x₀).val := by rw [hxe, hval, hLxv]
          exact hxx (L.pos_injective (Fin.ext hposx))
        · have hye : (L.pos y).val = (L'.pos y).val := hrestv y hyx hyy
          rw [hxe, hye] at hLlt
          exact hnotL'lt hLlt

open Classical in
/-- **Pair-cut edge-boundary total bound** (BK-Dirichlet foundation,
`step8.tex:207-229`). For a finite poset `α`, the total BK
edge-boundary summed over all ordered incomparable pairs `(x, y)`
satisfies

`∑_{x ∥ y} |∂_BK (pairCut x y)| ≤ (n - 1) · |𝓛(P)|`,

where `pairCut x y = {L : L.lt x y}` is the set of linear extensions
placing `x` before `y`.

The proof is by double counting via the `(σ, i) ↦ τ_i σ = L.swapAdj`
edge parametrization (`OneThird.Mathlib.BKGraph`). Each BK edge
`{L, L'}` comes from swapping some adjacent incomparable pair
`{σ(i), σ(i+1)}` at some position `i ∈ [n-1]`; the edge crosses
`pairCut x y` (in either direction) iff `{σ(i), σ(i+1)} = {x, y}`, so
summing over ordered pairs counts each edge exactly twice (once for
each ordering of the swapped pair). On the other hand, the number of
valid `(σ, i)` pairs is at most `(n - 1) · |𝓛(P)|` (one per extension
per position), and each BK edge corresponds to exactly two such
`(σ, i)` pairs. Combining, `2 · |E_BK| ≤ (n - 1) · |𝓛(P)|`.

Formally we inject the sigma finset of all valid triples
`((x, y), L, L')` into `LinearExt α × Fin n`, using
`swap_pair_uniqueness` for well-definedness and injectivity of
the map `((x, y), L, L') ↦ (L, L.pos x)`. -/
theorem edgeBoundary_pairCut_sum_le :
    (∑ p ∈ ((Finset.univ : Finset (α × α)).filter
              (fun p : α × α => p.1 ∥ p.2)),
        edgeBoundary ((Finset.univ : Finset (LinearExt α)).filter
            (fun L : LinearExt α => L.lt p.1 p.2))) ≤
      (Fintype.card α - 1) * numLinExt α := by
  set n := Fintype.card α with hn_def
  -- Sigma finset of all triples `(p, L, L')` satisfying the constraints.
  let T : Finset (Σ _ : α × α, LinearExt α × LinearExt α) :=
    (Finset.univ.filter (fun p : α × α => p.1 ∥ p.2)).sigma
      (fun p => (((Finset.univ : Finset (LinearExt α)).filter
                    (fun L : LinearExt α => L.lt p.1 p.2)) ×ˢ
                 (Finset.univ \ ((Finset.univ : Finset (LinearExt α)).filter
                    (fun L : LinearExt α => L.lt p.1 p.2)))).filter
                 (fun q : LinearExt α × LinearExt α => BKAdj q.1 q.2))
  -- LHS equals `T.card` by `Finset.card_sigma`.
  have hLHS :
      (∑ p ∈ ((Finset.univ : Finset (α × α)).filter
                (fun p : α × α => p.1 ∥ p.2)),
         edgeBoundary ((Finset.univ : Finset (LinearExt α)).filter
            (fun L : LinearExt α => L.lt p.1 p.2))) = T.card :=
    (Finset.card_sigma _ _).symm
  rw [hLHS]
  -- Target finset `U = LinearExt × {k : Fin n | k.val + 1 < n}`.
  let ValidPos : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun k => k.val + 1 < n)
  let U : Finset (LinearExt α × Fin n) :=
    (Finset.univ : Finset (LinearExt α)) ×ˢ ValidPos
  -- `|ValidPos| = n - 1`.
  have hValidPos_card : ValidPos.card = n - 1 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · -- n = 0: Fin n is empty so ValidPos is empty too.
      have hempty : ValidPos = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intros k _
        have := k.isLt; omega
      rw [hempty, Finset.card_empty]; omega
    · have hlast_mem :
          (⟨n - 1, Nat.pred_lt hn_pos.ne'⟩ : Fin n) ∈
            (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      have heq :
          ValidPos =
            (Finset.univ : Finset (Fin n)).erase ⟨n - 1, Nat.pred_lt hn_pos.ne'⟩ := by
        ext k
        simp only [ValidPos, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
          true_and, and_true]
        constructor
        · intro hlt heq
          have hv : k.val = n - 1 := by rw [heq]
          omega
        · intro hne
          have hkne : k.val ≠ n - 1 := fun hv => hne (Fin.ext hv)
          have hkL : k.val < n := k.isLt
          omega
      rw [heq, Finset.card_erase_of_mem hlast_mem, Finset.card_univ,
        Fintype.card_fin]
  -- `|U| = numLinExt α * (n - 1)`.
  have hU_card : U.card = numLinExt α * (n - 1) := by
    have h1 : U.card = (Finset.univ : Finset (LinearExt α)).card * ValidPos.card :=
      Finset.card_product _ _
    rw [h1, Finset.card_univ, hValidPos_card]
    rfl
  -- Injection `f : T → U` via `(p, L, L') ↦ (L, L.pos p.1)`.
  let f : (Σ _ : α × α, LinearExt α × LinearExt α) → LinearExt α × Fin n :=
    fun t => (t.2.1, t.2.1.pos t.1.1)
  have hf_bound : T.card ≤ U.card := by
    refine Finset.card_le_card_of_injOn f ?maps ?inj
    · -- Maps into U: need `(L.pos p.1).val + 1 < n`.
      rintro ⟨p, L, L'⟩ ht
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter,
        Finset.mem_univ, Finset.mem_product, Finset.mem_sdiff, true_and] at ht
      obtain ⟨_, ⟨hLlt, hnotL'⟩, hBK⟩ := ht
      obtain ⟨x₀, y₀, k, hk, _, hLx, hLy, hL'x, hL'y, hrest⟩ := hBK
      -- Convert to val-form.
      have hLxv : (L.pos x₀).val = k.val := congrArg Fin.val hLx
      have hLyv : (L.pos y₀).val = k.val + 1 := by rw [hLy]
      have hL'xv : (L'.pos x₀).val = k.val + 1 := by rw [hL'x]
      have hL'yv : (L'.pos y₀).val = k.val := congrArg Fin.val hL'y
      have hrestv : ∀ z : α, z ≠ x₀ → z ≠ y₀ → (L.pos z).val = (L'.pos z).val :=
        fun z h1 h2 => congrArg Fin.val (hrest z h1 h2)
      -- Apply swap_pair_uniqueness to get p.1 = x₀.
      have ⟨hpx, _⟩ := swap_pair_uniqueness (L := L) (L' := L') (x := p.1) (y := p.2)
        (k := k.val) hLxv hLyv hL'xv hL'yv hrestv
        (hLlt : (L.pos p.1).val < (L.pos p.2).val) hnotL'
      -- Map to U.
      show f ⟨p, L, L'⟩ ∈ U
      simp only [U, ValidPos, f, Finset.mem_product, Finset.mem_univ,
        Finset.mem_filter, true_and]
      rw [hpx, hLx]
      exact hk
    · -- Injectivity on T.
      rintro ⟨p, L, L'⟩ ht ⟨p', L₁, L₁'⟩ ht' hfeq
      simp only [f, Prod.mk.injEq] at hfeq
      obtain ⟨hLeq, hposeq⟩ := hfeq
      subst hLeq
      have hp1eq : p.1 = p'.1 := L.pos_injective hposeq
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter,
        Finset.mem_univ, Finset.mem_product, Finset.mem_sdiff, true_and] at ht ht'
      obtain ⟨_, ⟨hLlt, hnotL'⟩, hBK⟩ := ht
      obtain ⟨_, ⟨hLlt', hnotL₁'⟩, hBK'⟩ := ht'
      obtain ⟨x₀, y₀, k, hk, _, hLx, hLy, hL'x, hL'y, hrest⟩ := hBK
      obtain ⟨x₁, y₁, k', hk', _, hLx₁, hLy₁, hL'x₁, hL'y₁, hrest'⟩ := hBK'
      -- Val-form for first triple.
      have hLxv : (L.pos x₀).val = k.val := congrArg Fin.val hLx
      have hLyv : (L.pos y₀).val = k.val + 1 := by rw [hLy]
      have hL'xv : (L'.pos x₀).val = k.val + 1 := by rw [hL'x]
      have hL'yv : (L'.pos y₀).val = k.val := congrArg Fin.val hL'y
      have hrestv : ∀ z : α, z ≠ x₀ → z ≠ y₀ → (L.pos z).val = (L'.pos z).val :=
        fun z h1 h2 => congrArg Fin.val (hrest z h1 h2)
      -- Val-form for second triple.
      have hLxv₁ : (L.pos x₁).val = k'.val := congrArg Fin.val hLx₁
      have hLyv₁ : (L.pos y₁).val = k'.val + 1 := by rw [hLy₁]
      have hL'xv₁ : (L₁'.pos x₁).val = k'.val + 1 := by rw [hL'x₁]
      have hL'yv₁ : (L₁'.pos y₁).val = k'.val := congrArg Fin.val hL'y₁
      have hrestv' : ∀ z : α, z ≠ x₁ → z ≠ y₁ → (L.pos z).val = (L₁'.pos z).val :=
        fun z h1 h2 => congrArg Fin.val (hrest' z h1 h2)
      -- Apply swap_pair_uniqueness to each.
      have ⟨hp1, hp2⟩ := swap_pair_uniqueness (L := L) (L' := L') (x := p.1) (y := p.2)
        (k := k.val) hLxv hLyv hL'xv hL'yv hrestv
        (hLlt : (L.pos p.1).val < (L.pos p.2).val) hnotL'
      have ⟨hp'1, hp'2⟩ := swap_pair_uniqueness (L := L) (L' := L₁') (x := p'.1) (y := p'.2)
        (k := k'.val) hLxv₁ hLyv₁ hL'xv₁ hL'yv₁ hrestv'
        (hLlt' : (L.pos p'.1).val < (L.pos p'.2).val) hnotL₁'
      -- Derive x₀ = x₁, k = k', y₀ = y₁.
      have hx_eq : x₀ = x₁ := hp1.symm.trans (hp1eq.trans hp'1)
      have hkv_eq : k.val = k'.val := by
        have hpx : L.pos x₀ = L.pos x₁ := by rw [hx_eq]
        rw [hLx, hLx₁] at hpx
        exact congrArg Fin.val hpx
      have hk_eq : k = k' := Fin.ext hkv_eq
      have hy_eq : y₀ = y₁ := by
        have hv : (L.pos y₀).val = (L.pos y₁).val := by
          rw [hLyv, hLyv₁, hkv_eq]
        exact L.pos_injective (Fin.ext hv)
      have hp_eq : p = p' :=
        Prod.ext hp1eq (hp2.trans (hy_eq.trans hp'2.symm))
      -- Substitute to identify the two triples.
      subst hx_eq
      subst hy_eq
      subst hk_eq
      have hL'eq : L' = L₁' := by
        apply LinearExt.ext
        apply Equiv.ext
        intro z
        change L'.pos z = L₁'.pos z
        by_cases hzx : z = x₀
        · rw [hzx, hL'x, hL'x₁]
        · by_cases hzy : z = y₀
          · rw [hzy, hL'y, hL'y₁]
          · rw [← hrest z hzx hzy, hrest' z hzx hzy]
      subst hp_eq
      subst hL'eq
      rfl
  calc T.card ≤ U.card := hf_bound
    _ = numLinExt α * (n - 1) := hU_card
    _ = (n - 1) * numLinExt α := Nat.mul_comm _ _

end OneThird
