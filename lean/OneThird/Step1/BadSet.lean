/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import OneThird.RichPair
import OneThird.Step1.CommonChain
import OneThird.Step1.LocalCoords
import OneThird.Step1.BKMoves

/-!
# Step 1, part (iv): bad-set boundary-cardinality bounds

Faithful Lean port of the structural backbone of part (iv) of the
local interface theorem (`thm:interface`, `step1.tex:174-194`): the
quantitative control on the bad set `Bad_{x,y}` of a rich pair.

The paper's part (iv) asserts that `Bad_{x,y}` is "at most
one-dimensional": it decomposes into `K = O(1)` strips, each strip a
union of `O(n)` raw fibers, each raw fiber of size `≤ t(x,y) + 1`,
yielding `|Bad_{x,y}| = O(n · t)`. The proof rests on three
structural facts, all ported here in full:

* **Chain structure** (`commonNbhdFinset_comparable`): the common
  neighbours of `(x, y)` are pairwise comparable — `lem:CNchain-width3`
  lifted to the `Finset` API.
* **Order-convexity of the incomparability locus**
  (`incomp_of_between`): if an element `z` is incomparable to two
  common neighbours `c ≤ c''`, it is incomparable to every common
  neighbour between them. This is the paper's
  "`I(z)` is a contiguous interval" (`step1.tex:307-311`).
* **Per-fiber size bound** (`collinear_fiber_card_le`): a raw fiber
  whose coordinate image is confined to a single axis-parallel line
  (the defining property of a *bad* raw fiber) has at most
  `t(x,y) + 1` elements. This is `step1.tex:352-358`.

Together with the external-element count (`card_externalFinset`,
`|Z| = n - t - 2`, `step1.tex:301`) these are the load-bearing
ingredients of the `|Bad_{x,y}| = O(n · t)` bound.

## A faithfulness caveat surfaced by the port

The paper (`step1.tex:308-311`) claims `|I(z)| ≤ 2` for the
incomparability locus `I(z) := {k : z ∥ c_k}` of an *external*
element `z`, citing a width-`4` antichain. A literal reading does not
support the **length** bound: a width-`4` antichain inside
`{x, y, z} ∪ {c_{k_1}, c_{k_2}, c_{k_3}}` would require `z ∥ x` and
`z ∥ y` (the `c_k` are mutually comparable, so an antichain contains
at most one of them), i.e. `z ∈ commonNbhd x y` — but `z` is
*external*, hence comparable to `x` or to `y`. Width `3` therefore
yields only the **order-convexity** of `I(z)` (`incomp_of_between`
here), not `|I(z)| ≤ 2`. The convexity is what is ported; the
unproven length bound is documented and flagged for the Step 1
assembly ticket. See the module note below and the state document.

## Main definitions

* `OneThird.externalFinset x y` — the external elements `Z`, those
  outside `{x, y} ∪ C(x, y)`.

## Main results

* `OneThird.commonNbhdFinset_comparable` — common neighbours are
  pairwise comparable.
* `OneThird.incomp_of_between` — order-convexity of the
  incomparability locus.
* `OneThird.card_externalFinset` — `|Z| = n - t - 2`.
* `OneThird.collinear_fiber_card_le` — a coordinate-collinear,
  `(localCoord, σ)`-injective fiber has `≤ t + 1` elements.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## Chain structure of the common neighbours -/

/-- **Common neighbours are pairwise comparable** (`lem:CNchain-width3`,
`step1.tex:40`, in `Finset` form). In a width-`3` poset every two
common neighbours of an incomparable pair `(x, y)` are comparable. -/
theorem commonNbhdFinset_comparable (hP : HasWidthAtMost α 3) {x y : α}
    (hxy : x ∥ y) {a b : α} (ha : a ∈ commonNbhdFinset x y)
    (hb : b ∈ commonNbhdFinset x y) :
    a ≤ b ∨ b ≤ a := by
  by_cases hab : a = b
  · exact Or.inl (hab ▸ le_refl a)
  · have hchain := commonNbhd_isChain_of_width3 hP hxy
    have ha' : a ∈ commonNbhd x y := mem_commonNbhdFinset.mp ha
    have hb' : b ∈ commonNbhd x y := mem_commonNbhdFinset.mp hb
    exact hchain ha' hb' hab

/-! ## Order-convexity of the incomparability locus -/

/-- **Order-convexity of `I(z)`** (`step1.tex:307-311`). If `z` is
incomparable to `c` and to `c''`, it is incomparable to every `c'`
between them. The common-neighbour chain `C(x, y)` is totally
ordered (`commonNbhdFinset_comparable`), so this says the set of
common neighbours incomparable to a fixed `z` is a contiguous
sub-interval of the chain.

This is pure order theory — it needs neither width `3` nor that the
`c`'s are common neighbours, only the betweenness `c ≤ c' ≤ c''`. -/
theorem incomp_of_between {z c c' c'' : α} (h1 : c ≤ c') (h2 : c' ≤ c'')
    (hzc : z ∥ c) (hzc'' : z ∥ c'') : z ∥ c' :=
  ⟨fun hle => hzc''.1 (hle.trans h2), fun hle => hzc.2 (h1.trans hle)⟩

/-- The incomparability locus `I(z)` of `z` against the common
neighbours of `(x, y)`, as a `Finset`. -/
noncomputable def incompLocus (x y z : α) : Finset α := by
  classical
  exact (commonNbhdFinset x y).filter (fun c => z ∥ c)

lemma mem_incompLocus {x y z c : α} :
    c ∈ incompLocus x y z ↔ c ∈ commonNbhdFinset x y ∧ z ∥ c := by
  unfold incompLocus
  simp [Finset.mem_filter]

/-- The incomparability locus is order-convex inside the
common-neighbour chain: if `c` and `c''` lie in `I(z)` and `c'` is a
common neighbour between them, then `c' ∈ I(z)`. -/
theorem incompLocus_ordConvex {x y z : α} {c c' c'' : α}
    (hc : c ∈ incompLocus x y z) (hc'' : c'' ∈ incompLocus x y z)
    (hc' : c' ∈ commonNbhdFinset x y) (h1 : c ≤ c') (h2 : c' ≤ c'') :
    c' ∈ incompLocus x y z := by
  rw [mem_incompLocus] at hc hc'' ⊢
  exact ⟨hc', incomp_of_between h1 h2 hc.2 hc''.2⟩

/-! ## The external-element set -/

/-- The **external-element set** `Z := X ∖ ({x, y} ∪ C(x, y))`
(`step1.tex:301`): elements that are neither `x`, nor `y`, nor a
common neighbour. -/
noncomputable def externalFinset (x y : α) : Finset α :=
  Finset.univ \ insert x (insert y (commonNbhdFinset x y))

lemma mem_externalFinset {x y z : α} :
    z ∈ externalFinset x y ↔
      z ≠ x ∧ z ≠ y ∧ z ∉ commonNbhdFinset x y := by
  unfold externalFinset
  simp [Finset.mem_sdiff, Finset.mem_insert, not_or]

/-- **External-element count** (`step1.tex:301`): there are exactly
`n - t - 2` external elements, where `n = |α|` and `t = t(x, y)` is
the common-neighbour-chain length. -/
theorem card_externalFinset {x y : α} (hxy : x ∥ y) :
    (externalFinset x y).card
      = Fintype.card α - commonNbhdLength x y - 2 := by
  unfold externalFinset
  have hyC : y ∉ commonNbhdFinset x y := by
    rw [mem_commonNbhdFinset]
    exact fun h => Incomp.irrefl y h.2
  have hxC : x ∉ commonNbhdFinset x y := by
    rw [mem_commonNbhdFinset]
    exact fun h => Incomp.irrefl x h.1
  have hxyne : x ≠ y := fun h => hxy.1 (h ▸ le_refl x)
  have hx_ins : x ∉ insert y (commonNbhdFinset x y) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxyne, hxC⟩
  rw [Finset.card_univ_diff,
      Finset.card_insert_of_notMem hx_ins,
      Finset.card_insert_of_notMem hyC]
  unfold commonNbhdLength
  omega

/-! ## Per-fiber size bound for bad raw fibers -/

/-- **Bad-fiber size bound** (`step1.tex:352-358`). A raw fiber on
which the coordinate map is `(localCoord, σ)`-injective (condition
`G1`, automatic on every raw fiber), the sign marker is constant, and
the first coordinate is pinned to a single value `i₀` — i.e. the
fiber's `π`-image lies on one axis-parallel line, the defining
property of a *bad* raw fiber — has at most `t(x, y) + 1` elements.

This is the boundary-cardinality content of part (iv): every raw
fiber meeting `Bad_{x,y}` is "one-dimensional", so it carries at most
`t + 1` linear extensions. -/
theorem collinear_fiber_card_le {x y : α} {F : Finset (LinearExt α)}
    {i₀ : ℕ}
    (hinj : ∀ L₁ ∈ F, ∀ L₂ ∈ F,
        localCoord x y L₁ = localCoord x y L₂ →
        signMarker x y L₁ = signMarker x y L₂ → L₁ = L₂)
    (hsign : ∃ ε : Bool, ∀ L ∈ F, signMarker x y L = ε)
    (hline : ∀ L ∈ F, iCoord x y L = i₀) :
    F.card ≤ commonNbhdLength x y + 1 := by
  classical
  obtain ⟨ε, hε⟩ := hsign
  -- `jCoord` alone is injective on `F`: it determines `localCoord`.
  have hjinj : Set.InjOn (jCoord x y) (↑F : Set (LinearExt α)) := by
    intro L₁ hL₁ L₂ hL₂ hj
    apply hinj L₁ hL₁ L₂ hL₂
    · unfold localCoord
      rw [hline L₁ hL₁, hline L₂ hL₂, hj]
    · rw [hε L₁ hL₁, hε L₂ hL₂]
  -- the `jCoord`-image lands in `{0, …, t}`
  have himg : F.image (jCoord x y)
      ⊆ Finset.range (commonNbhdLength x y + 1) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨L, _, rfl⟩ := hp
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (jCoord_le_commonNbhdLength x y L)
  calc F.card = (F.image (jCoord x y)).card :=
        (Finset.card_image_of_injOn hjinj).symm
    _ ≤ (Finset.range (commonNbhdLength x y + 1)).card :=
        Finset.card_le_card himg
    _ = commonNbhdLength x y + 1 := Finset.card_range _

/-- The mirror of `collinear_fiber_card_le` for a fiber pinned to a
single *second*-coordinate value `j₀` (a vertical bad strip line). -/
theorem collinear_fiber_card_le' {x y : α} {F : Finset (LinearExt α)}
    {j₀ : ℕ}
    (hinj : ∀ L₁ ∈ F, ∀ L₂ ∈ F,
        localCoord x y L₁ = localCoord x y L₂ →
        signMarker x y L₁ = signMarker x y L₂ → L₁ = L₂)
    (hsign : ∃ ε : Bool, ∀ L ∈ F, signMarker x y L = ε)
    (hline : ∀ L ∈ F, jCoord x y L = j₀) :
    F.card ≤ commonNbhdLength x y + 1 := by
  classical
  obtain ⟨ε, hε⟩ := hsign
  have hiinj : Set.InjOn (iCoord x y) (↑F : Set (LinearExt α)) := by
    intro L₁ hL₁ L₂ hL₂ hi
    apply hinj L₁ hL₁ L₂ hL₂
    · unfold localCoord
      rw [hline L₁ hL₁, hline L₂ hL₂, hi]
    · rw [hε L₁ hL₁, hε L₂ hL₂]
  have himg : F.image (iCoord x y)
      ⊆ Finset.range (commonNbhdLength x y + 1) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨L, _, rfl⟩ := hp
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (iCoord_le_commonNbhdLength x y L)
  calc F.card = (F.image (iCoord x y)).card :=
        (Finset.card_image_of_injOn hiinj).symm
    _ ≤ (Finset.range (commonNbhdLength x y + 1)).card :=
        Finset.card_le_card himg
    _ = commonNbhdLength x y + 1 := Finset.card_range _

/-! ## Non-vacuity: the structural lemmas on a concrete instance

On the discrete `Fin 3` poset `Antichain3` (defined by the S1-A port
in `OneThird/Step1/GroundSet.lean`), the pair `(a0, a1)` is a genuine
rich pair: `commonNbhdFinset a0 a1 = {a2}` is a non-empty chain. This
certifies that `commonNbhdFinset_comparable` and the part-(iv)
structural API are not vacuous baselines. -/

/-- **Non-vacuity of the part-(iv) structural lemmas.** On the
concrete width-`3`, non-chain poset `Antichain3` the common-neighbour
finset of `(a0, a1)` is non-empty, and the chain lemma
`commonNbhdFinset_comparable` applies to its unique element. -/
theorem badSet_structure_nonvacuous :
    (Antichain3.a2 ∈ commonNbhdFinset Antichain3.a0 Antichain3.a1) ∧
    (Antichain3.a2 ≤ Antichain3.a2 ∨ Antichain3.a2 ≤ Antichain3.a2) := by
  have hmem : Antichain3.a2 ∈ commonNbhdFinset
      Antichain3.a0 Antichain3.a1 := by
    rw [Antichain3.commonNbhdFinset_a0_a1]
    exact Finset.mem_singleton.mpr rfl
  refine ⟨hmem, ?_⟩
  exact commonNbhdFinset_comparable Antichain3.hasWidthAtMost
    (Antichain3.incomp_iff_ne.mpr (by decide)) hmem hmem

end OneThird
