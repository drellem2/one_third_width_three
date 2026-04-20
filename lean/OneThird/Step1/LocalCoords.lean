/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import OneThird.Poset
import OneThird.LinearExtension
import OneThird.Mathlib.BKGraph
import Mathlib.Data.Finset.Image

/-!
# Step 1: Local coordinates and fiber structure

Core Step 1 definitions — the local coordinate map `π_{x,y}`, the sign
marker `σ(L)`, the external-ordering equivalence, and raw/good fibers —
together with the basic API used throughout the Step 1–2 arguments.

Corresponds to `def:local-coords`, `def:ext-equiv`, and `def:good-fiber`
of `step1.tex` §2. The main Step 1 interface theorem
(`thm:interface`) is stated in `OneThird/RichPair.lean`; its proof is
out of scope for this file (tracked separately as S1.c).

## Main definitions

* `signMarker x y L` — `true` iff `x <_L y`.
* `iCoord x y L`, `jCoord x y L`, `localCoord x y L` — the coordinates
  `i(L), j(L), π_{x,y}(L)`.
* `ExternalEquiv x y` — the external-ordering equivalence on linear
  extensions (proven to be reflexive, symmetric, transitive).
* `rawFiber x y L₀ ε` — the raw fiber at representative `L₀` and sign `ε`.
* `IsGoodFiber x y F` — the good-fiber predicate (G1 + G2 + G3).
* `goodFiberSet`, `badSet` — good and bad parts of `L(P)`.

## Main results

* `signMarker_eq_true_iff` — `signMarker x y L = true ↔ L.lt x y`.
* `iCoord_le_commonNbhdLength`, `jCoord_le_commonNbhdLength` — the
  coordinate-bound part (i) of `thm:interface`.
* `ExternalEquiv.refl`, `.symm`, `.trans`, `externalSetoid` — the
  external equivalence is indeed an equivalence relation.
* `rawFiber_biUnion_univ` — the raw fibers cover every linear
  extension: `⋃_{L₀} rawFiber x y L₀ (signMarker x y L₀) = univ`.
* `IsGoodFiber.card_le_sq` — a good raw fiber has at most
  `(t(x, y) + 1)^2` elements.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## Sign marker and local coordinates -/

/-- Sign marker `σ(L) ∈ {+, −}` of a linear extension relative to a
pair `(x, y)`: `true` iff `x` precedes `y` in `L`. -/
noncomputable def signMarker (x y : α) (L : LinearExt α) : Bool :=
  decide (L.lt x y)

lemma signMarker_eq_true_iff {x y : α} {L : LinearExt α} :
    signMarker x y L = true ↔ L.lt x y := by
  simp [signMarker]

lemma signMarker_eq_false_iff {x y : α} {L : LinearExt α} :
    signMarker x y L = false ↔ ¬ L.lt x y := by
  simp [signMarker]

/-- First local coordinate `i(L)`: number of common neighbors of
`(x, y)` that precede `x` in `L`. -/
noncomputable def iCoord (x y : α) (L : LinearExt α) : ℕ :=
  ((commonNbhdFinset x y).filter (fun z => L.lt z x)).card

/-- Second local coordinate `j(L)`: number of common neighbors of
`(x, y)` that precede `y` in `L`. -/
noncomputable def jCoord (x y : α) (L : LinearExt α) : ℕ :=
  ((commonNbhdFinset x y).filter (fun z => L.lt z y)).card

/-- Local coordinate map `π_{x,y}` of Def. `def:local-coords`. -/
noncomputable def localCoord (x y : α) (L : LinearExt α) : ℕ × ℕ :=
  (iCoord x y L, jCoord x y L)

/-- **Coordinate bound** (part (i) of `thm:interface`): the first local
coordinate is at most the common-neighbor-chain length `t(x, y)`. -/
lemma iCoord_le_commonNbhdLength (x y : α) (L : LinearExt α) :
    iCoord x y L ≤ commonNbhdLength x y := by
  unfold iCoord commonNbhdLength
  exact Finset.card_filter_le _ _

/-- **Coordinate bound** (part (i) of `thm:interface`): the second local
coordinate is at most the common-neighbor-chain length `t(x, y)`. -/
lemma jCoord_le_commonNbhdLength (x y : α) (L : LinearExt α) :
    jCoord x y L ≤ commonNbhdLength x y := by
  unfold jCoord commonNbhdLength
  exact Finset.card_filter_le _ _

lemma localCoord_fst_le (x y : α) (L : LinearExt α) :
    (localCoord x y L).1 ≤ commonNbhdLength x y :=
  iCoord_le_commonNbhdLength x y L

lemma localCoord_snd_le (x y : α) (L : LinearExt α) :
    (localCoord x y L).2 ≤ commonNbhdLength x y :=
  jCoord_le_commonNbhdLength x y L

/-! ## External-ordering equivalence -/

/-- External-ordering equivalence for a pair `(x, y)`: two linear
extensions agree on the relative order of every pair of elements
outside `{x, y} ∪ C(x, y)`, and on each external element's order
with every common neighbor. (See paragraph before
`def:good-fiber` in `step1.tex`.) -/
noncomputable def ExternalEquiv (x y : α) (L L' : LinearExt α) : Prop :=
  (∀ a b : α,
      a ∉ insert x (insert y (commonNbhdFinset x y)) →
      b ∉ insert x (insert y (commonNbhdFinset x y)) →
      (L.lt a b ↔ L'.lt a b)) ∧
  (∀ (a : α) (c : α), c ∈ commonNbhdFinset x y →
      a ∉ insert x (insert y (commonNbhdFinset x y)) →
      (L.lt a c ↔ L'.lt a c))

namespace ExternalEquiv

/-- External equivalence is reflexive. -/
@[refl] lemma refl (x y : α) (L : LinearExt α) : ExternalEquiv x y L L :=
  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

/-- External equivalence is symmetric. -/
@[symm] lemma symm {x y : α} {L L' : LinearExt α}
    (h : ExternalEquiv x y L L') : ExternalEquiv x y L' L :=
  ⟨fun a b ha hb => (h.1 a b ha hb).symm,
   fun a c hc ha => (h.2 a c hc ha).symm⟩

/-- External equivalence is transitive. -/
lemma trans {x y : α} {L L' L'' : LinearExt α}
    (h₁ : ExternalEquiv x y L L') (h₂ : ExternalEquiv x y L' L'') :
    ExternalEquiv x y L L'' :=
  ⟨fun a b ha hb => (h₁.1 a b ha hb).trans (h₂.1 a b ha hb),
   fun a c hc ha => (h₁.2 a c hc ha).trans (h₂.2 a c hc ha)⟩

end ExternalEquiv

/-- The `Equivalence` record for the external-ordering relation. -/
lemma externalEquivalence (x y : α) :
    Equivalence (ExternalEquiv (α := α) x y) :=
  ⟨ExternalEquiv.refl x y, ExternalEquiv.symm, ExternalEquiv.trans⟩

/-- The external-ordering equivalence as a `Setoid`. -/
noncomputable def externalSetoid (x y : α) : Setoid (LinearExt α) where
  r := ExternalEquiv x y
  iseqv := externalEquivalence x y

/-! ## Raw fibers -/

/-- Raw fiber of `(x, y)` at representative `L₀` and sign `ε`: all
linear extensions externally equivalent to `L₀` and having sign `ε`. -/
noncomputable def rawFiber (x y : α) (L₀ : LinearExt α) (ε : Bool) :
    Finset (LinearExt α) := by
  classical
  exact
    Finset.univ.filter
      (fun L => ExternalEquiv x y L L₀ ∧ signMarker x y L = ε)

lemma mem_rawFiber {x y : α} {L₀ L : LinearExt α} {ε : Bool} :
    L ∈ rawFiber x y L₀ ε ↔
      ExternalEquiv x y L L₀ ∧ signMarker x y L = ε := by
  classical
  unfold rawFiber
  simp

/-- Any linear extension is in its "own" raw fiber — the one anchored
at itself with its own sign. -/
lemma self_mem_rawFiber (x y : α) (L : LinearExt α) :
    L ∈ rawFiber x y L (signMarker x y L) := by
  classical
  rw [mem_rawFiber]
  exact ⟨ExternalEquiv.refl x y L, rfl⟩

/-- **Raw fiber partition** (covering half): the raw fibers at the
self-anchored sign cover every linear extension. This is the first
half of the partition statement of part (ii) of `thm:interface`;
disjointness of the good part modulo sign + external class is the
remaining half, handled at the level of good fibers. -/
lemma rawFiber_biUnion_univ (x y : α) :
    (Finset.univ : Finset (LinearExt α)).biUnion
      (fun L₀ => rawFiber x y L₀ (signMarker x y L₀)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro L
  rw [Finset.mem_biUnion]
  exact ⟨L, Finset.mem_univ _, self_mem_rawFiber x y L⟩

/-- Sign is constant on a raw fiber: `signMarker = ε` for every
element of `rawFiber x y L₀ ε`. -/
lemma signMarker_of_mem_rawFiber {x y : α} {L₀ L : LinearExt α} {ε : Bool}
    (hL : L ∈ rawFiber x y L₀ ε) : signMarker x y L = ε :=
  (mem_rawFiber.mp hL).2

/-! ## Good fibers -/

/-- A raw fiber is *good* (Def. `def:good-fiber`) if:

* (G1) the coordinate map (together with the sign) is injective;
* (G2) its coordinate image is order-convex in `ℕ²`;
* (G3) internal BK edges are exactly unit grid moves with preserved
  sign.
-/
noncomputable def IsGoodFiber (x y : α) (F : Finset (LinearExt α)) : Prop :=
  (∀ L₁ ∈ F, ∀ L₂ ∈ F,
      localCoord x y L₁ = localCoord x y L₂ →
      signMarker x y L₁ = signMarker x y L₂ →
      L₁ = L₂) ∧
  (∀ p ∈ F.image (localCoord x y), ∀ q ∈ F.image (localCoord x y),
      p.1 ≤ q.1 → p.2 ≤ q.2 →
      ∀ r : ℕ × ℕ,
        (p.1 ≤ r.1 ∧ r.1 ≤ q.1) →
        (p.2 ≤ r.2 ∧ r.2 ≤ q.2) →
        r ∈ F.image (localCoord x y)) ∧
  (∀ L₁ ∈ F, ∀ L₂ ∈ F,
      BKAdj L₁ L₂ ↔
        (signMarker x y L₁ = signMarker x y L₂ ∧
         ((iCoord x y L₁ = iCoord x y L₂ + 1 ∧
               jCoord x y L₁ = jCoord x y L₂) ∨
          (iCoord x y L₂ = iCoord x y L₁ + 1 ∧
               jCoord x y L₁ = jCoord x y L₂) ∨
          (jCoord x y L₁ = jCoord x y L₂ + 1 ∧
               iCoord x y L₁ = iCoord x y L₂) ∨
          (jCoord x y L₂ = jCoord x y L₁ + 1 ∧
               iCoord x y L₁ = iCoord x y L₂))))

namespace IsGoodFiber

variable {x y : α} {F : Finset (LinearExt α)}

omit [DecidableEq α] in
/-- G1 projection: good fibers are (localCoord, signMarker)-injective. -/
lemma injective (hF : IsGoodFiber x y F) :
    ∀ L₁ ∈ F, ∀ L₂ ∈ F,
      localCoord x y L₁ = localCoord x y L₂ →
      signMarker x y L₁ = signMarker x y L₂ →
      L₁ = L₂ := hF.1

end IsGoodFiber

omit [DecidableEq α] in
/-- **Good-fiber cardinality bound**: if `F` is a good fiber on which
the sign is constant (e.g. a raw good fiber), its cardinality is at
most `(t(x, y) + 1)^2`.

Reason: G1 gives injectivity of `(localCoord, signMarker)` on `F`;
combined with constant sign this means `localCoord` is injective on
`F`, and its image lies in `{0,…,t}^2`. -/
theorem IsGoodFiber.card_le_sq
    {x y : α} {F : Finset (LinearExt α)} {ε : Bool}
    (hF : IsGoodFiber x y F)
    (hsign : ∀ L ∈ F, signMarker x y L = ε) :
    F.card ≤ (commonNbhdLength x y + 1) ^ 2 := by
  classical
  set t := commonNbhdLength x y
  -- Box the image of `localCoord` inside `range (t+1) ×ˢ range (t+1)`.
  have himg_sub :
      F.image (localCoord x y)
        ⊆ (Finset.range (t + 1)) ×ˢ (Finset.range (t + 1)) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    rcases hp with ⟨L, _, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · exact Nat.lt_succ_of_le (localCoord_fst_le x y L)
    · exact Nat.lt_succ_of_le (localCoord_snd_le x y L)
  -- `localCoord` is injective on `F` using G1 plus constant sign.
  have hinj : Set.InjOn (localCoord x y) (↑F : Set (LinearExt α)) := by
    intro L₁ hL₁ L₂ hL₂ hpq
    have hsgn : signMarker x y L₁ = signMarker x y L₂ := by
      rw [hsign L₁ hL₁, hsign L₂ hL₂]
    exact hF.1 L₁ hL₁ L₂ hL₂ hpq hsgn
  -- `F.card = (F.image localCoord).card` by injectivity.
  have hcard_eq : F.card = (F.image (localCoord x y)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hprod_card :
      ((Finset.range (t + 1)) ×ˢ (Finset.range (t + 1))).card = (t + 1) ^ 2 := by
    rw [Finset.card_product, Finset.card_range, ← pow_two]
  calc F.card
      = (F.image (localCoord x y)).card := hcard_eq
    _ ≤ ((Finset.range (t + 1)) ×ˢ (Finset.range (t + 1))).card :=
        Finset.card_le_card himg_sub
    _ = (t + 1) ^ 2 := hprod_card

/-- Specialization of `IsGoodFiber.card_le_sq` to a good raw fiber:
the cardinality bound `(t(x,y) + 1)^2` holds because sign is
automatically constant on any raw fiber. -/
theorem IsGoodFiber.rawFiber_card_le
    {x y : α} {L₀ : LinearExt α} {ε : Bool}
    (hF : IsGoodFiber x y (rawFiber x y L₀ ε)) :
    (rawFiber x y L₀ ε).card ≤ (commonNbhdLength x y + 1) ^ 2 :=
  hF.card_le_sq (ε := ε) (fun _ hL => signMarker_of_mem_rawFiber hL)

/-! ## Good and bad sets -/

/-- Good fiber set `F_{x,y}`: the union of all good raw fibers. -/
noncomputable def goodFiberSet (x y : α) : Finset (LinearExt α) := by
  classical
  exact
    Finset.univ.filter
      (fun L => ∃ L₀, IsGoodFiber x y (rawFiber x y L₀ (signMarker x y L))
                      ∧ L ∈ rawFiber x y L₀ (signMarker x y L))

/-- Bad set `Bad_{x, y}` of a rich pair: complement of `goodFiberSet`. -/
noncomputable def badSet (x y : α) : Finset (LinearExt α) :=
  Finset.univ \ goodFiberSet x y

lemma goodFiberSet_union_badSet (x y : α) :
    goodFiberSet x y ∪ badSet x y = Finset.univ := by
  classical
  unfold badSet
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

lemma goodFiberSet_disjoint_badSet (x y : α) :
    Disjoint (goodFiberSet x y) (badSet x y) := by
  classical
  unfold badSet
  exact Finset.disjoint_sdiff

end OneThird
