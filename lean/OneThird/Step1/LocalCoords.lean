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
* `rawFiber x y L₀` — the raw fiber at representative `L₀`: the
  external-ordering class of `L₀`, spanning **both** signs
  (paper `def:good-fiber`).
* `IsGoodFiber x y F` — the good-fiber predicate (G1 + G2 + G3).
* `goodFiberSet`, `badSet` — good and bad parts of `L(P)`.

## Main results

* `signMarker_eq_true_iff` — `signMarker x y L = true ↔ L.lt x y`.
* `iCoord_le_commonNbhdLength`, `jCoord_le_commonNbhdLength` — the
  coordinate-bound part (i) of `thm:interface`.
* `ExternalEquiv.refl`, `.symm`, `.trans`, `externalSetoid` — the
  external equivalence is indeed an equivalence relation.
* `rawFiber_biUnion_univ` — the raw fibers cover every linear
  extension: `⋃_{L₀} rawFiber x y L₀ = univ`.
* `rawFiber_eq_of_externalEquiv` — raw fibers are external-equivalence
  classes.
* `mem_goodFiberSet` — membership in the good-fiber set.
* `IsGoodFiber.card_le_sq` — a constant-sign good fiber has at most
  `(t(x, y) + 1)^2` elements; `IsGoodFiber.card_le_two_sq` — a
  both-sign good raw fiber has at most `2·(t(x, y) + 1)^2`.

## S1-G2 re-port (mg-fc78)

The raw fiber and the G3 clause were re-ported to the genuine paper
`def:good-fiber` (`step1.tex:114-133`).  The previous S1-A port made
`rawFiber` a *single-sign* slice; combined with the genuine
rectangle-convexity clause G2 this made `goodFiberSet` provably empty
for every rich pair (S1-E, mg-c2d7).  The paper's raw fiber is the
external-ordering class over **both** signs; G3 carries the diagonal
sign-flip edge.  See `rawFiber`, `IsGoodFiber`, and
`OneThird/Step1/Interface.lean` §6.
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

/-- Raw fiber of `(x, y)` at representative `L₀` (paper Def.
`def:good-fiber`, `step1.tex:114-120`): the **external-ordering class**
of `L₀` — every linear extension externally equivalent to `L₀`.

A raw fiber `F_{x,y}(E)` spans **both signs**.  `step1.tex:121`
partitions `F_{x,y}(E)` *further* by the sign `σ`, but the raw fiber
itself, and its coordinate image `D_{x,y}(E) := π_{x,y}(F_{x,y}(E))`
(clause G2), range over both signs.  This is load-bearing: the
order-convexity clause G2 is rectangle-convexity in `ℤ²`
(`def:good-fiber` `cond:G2`), and a *single-sign* image lies in the
triangle `{(i,j) : i ≤ j}` (sign `+`) resp. `{(i,j) : j ≤ i}`
(sign `−`) — never rectangle-convex for `t ≥ 1`.  A raw fiber over both
signs has the full rectangle as its image (the sign-`+` triangle and
sign-`−` triangle glued along the diagonal), and that *is* order-convex
for a good external class.

(A single-sign `rawFiber` was the S1-A faithfulness defect diagnosed by
S1-E, work item mg-c2d7: it made `goodFiberSet` empty for every rich
pair.  See `OneThird/Step1/Interface.lean` §6.) -/
noncomputable def rawFiber (x y : α) (L₀ : LinearExt α) :
    Finset (LinearExt α) := by
  classical
  exact Finset.univ.filter (fun L => ExternalEquiv x y L L₀)

lemma mem_rawFiber {x y : α} {L₀ L : LinearExt α} :
    L ∈ rawFiber x y L₀ ↔ ExternalEquiv x y L L₀ := by
  classical
  unfold rawFiber
  simp

/-- Any linear extension is in its "own" raw fiber — the external
class anchored at itself. -/
lemma self_mem_rawFiber (x y : α) (L : LinearExt α) :
    L ∈ rawFiber x y L :=
  mem_rawFiber.mpr (ExternalEquiv.refl x y L)

/-- A raw fiber depends only on the external-ordering class of its
anchor: externally equivalent anchors give the **same** raw fiber.
This is the genuine — non-tautological — content behind part (ii)'s
"the raw fibers are equivalence classes". -/
lemma rawFiber_eq_of_externalEquiv {x y : α} {L L₀ : LinearExt α}
    (h : ExternalEquiv x y L L₀) : rawFiber x y L₀ = rawFiber x y L := by
  ext L'
  simp only [mem_rawFiber]
  exact ⟨fun he => he.trans h.symm, fun he => he.trans h⟩

/-- **Raw fiber partition** (covering half): the raw fibers cover every
linear extension. This is the first half of the partition statement of
part (ii) of `thm:interface`; disjointness of the good part modulo
external class is the remaining half, handled at the level of good
fibers. -/
lemma rawFiber_biUnion_univ (x y : α) :
    (Finset.univ : Finset (LinearExt α)).biUnion
      (fun L₀ => rawFiber x y L₀) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro L
  rw [Finset.mem_biUnion]
  exact ⟨L, Finset.mem_univ _, self_mem_rawFiber x y L⟩

/-! ## Good fibers -/

/-- A raw fiber is *good* (Def. `def:good-fiber`, `step1.tex:114-133`) if:

* **(G1)** the coordinate map together with the sign is injective —
  `(i, j, σ)` determines `L` (`cond:G1`);
* **(G2)** its coordinate image `D_{x,y}(E)` is **order-convex in `ℤ²`**
  (`cond:G2`): for image points `p ≤ q` (componentwise) the entire
  axis-aligned rectangle `[p, q]` lies in the image.  Because the raw
  fiber spans both signs (see `rawFiber`), the image is a genuine
  rectangle straddling the diagonal, and order-convexity is the honest
  discriminator of the good external classes;
* **(G3)** internal BK edges are exactly the **unit grid moves** with
  preserved sign **together with the diagonal sign-flip edge**
  (`cond:G3` + paper part (iii) case (b), `step1.tex:163-166`; the
  Output-interface line "BK edges inside each good raw fiber are exactly
  unit grid moves in `(i,j)`, plus at most one sign-flip edge at
  `i = j`").  Two members `L₁, L₂` are BK-adjacent iff either
  they share a sign and `π_{x,y}` differs by `±e₁` / `±e₂`, or they
  carry **opposite** sign with `π_{x,y}` unchanged and on the diagonal
  `i = j` (the `{x, y}`-swap of part (iii) case (b)).

The sign-flip disjunct of G3 is essential and was the omission, together
with the single-sign `rawFiber`, behind the S1-E faithfulness defect
(mg-c2d7): a both-sign raw fiber always carries sign-flip BK edges, so
the single-sign G3 was unsatisfiable on it. -/
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
        ((signMarker x y L₁ = signMarker x y L₂ ∧
          ((iCoord x y L₁ = iCoord x y L₂ + 1 ∧
                jCoord x y L₁ = jCoord x y L₂) ∨
           (iCoord x y L₂ = iCoord x y L₁ + 1 ∧
                jCoord x y L₁ = jCoord x y L₂) ∨
           (jCoord x y L₁ = jCoord x y L₂ + 1 ∧
                iCoord x y L₁ = iCoord x y L₂) ∨
           (jCoord x y L₂ = jCoord x y L₁ + 1 ∧
                iCoord x y L₁ = iCoord x y L₂))) ∨
         (signMarker x y L₁ = ! signMarker x y L₂ ∧
          iCoord x y L₁ = iCoord x y L₂ ∧
          jCoord x y L₁ = jCoord x y L₂ ∧
          iCoord x y L₁ = jCoord x y L₁)))

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

omit [DecidableEq α] in
/-- **Good raw-fiber cardinality bound (both signs)**: a good fiber `F`
has at most `2·(t(x, y) + 1)^2` elements.  G1 makes `(i, j, σ)`
determine `L`, and `(i, j, σ)` ranges over `{0,…,t}² × {+, −}`.  This is
the honest both-sign refinement of `card_le_sq` — a raw fiber spans
both signs, so the bound carries the factor `2`. -/
theorem IsGoodFiber.card_le_two_sq
    {x y : α} {F : Finset (LinearExt α)} (hF : IsGoodFiber x y F) :
    F.card ≤ 2 * (commonNbhdLength x y + 1) ^ 2 := by
  classical
  set t := commonNbhdLength x y with ht
  set Cod : Finset ((ℕ × ℕ) × Bool) :=
    ((Finset.range (t + 1)) ×ˢ (Finset.range (t + 1))) ×ˢ
      (Finset.univ : Finset Bool) with hCod
  have hinj : Set.InjOn (fun L => (localCoord x y L, signMarker x y L))
      (↑F : Set (LinearExt α)) := by
    intro L₁ hL₁ L₂ hL₂ h
    obtain ⟨hc, hs⟩ := Prod.mk.inj h
    exact hF.1 L₁ hL₁ L₂ hL₂ hc hs
  have himg_sub : F.image (fun L => (localCoord x y L, signMarker x y L))
      ⊆ Cod := by
    intro p hp
    simp only [Finset.mem_image] at hp
    rcases hp with ⟨L, _, rfl⟩
    simp only [hCod, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
      and_true]
    exact ⟨Nat.lt_succ_of_le (localCoord_fst_le x y L),
           Nat.lt_succ_of_le (localCoord_snd_le x y L)⟩
  have hcard : Cod.card = 2 * (t + 1) ^ 2 := by
    simp only [hCod, Finset.card_product, Finset.card_range, Finset.card_univ,
      Fintype.card_bool, pow_two]
    exact Nat.mul_comm _ 2
  calc F.card
      = (F.image (fun L => (localCoord x y L, signMarker x y L))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Cod.card := Finset.card_le_card himg_sub
    _ = 2 * (t + 1) ^ 2 := hcard

/-! ## Good and bad sets -/

/-- Good fiber set `F_{x,y}` (paper Def. `def:good-fiber`,
`step1.tex:128-132`): the union of all good raw fibers. -/
noncomputable def goodFiberSet (x y : α) : Finset (LinearExt α) := by
  classical
  exact
    Finset.univ.filter
      (fun L => ∃ L₀, IsGoodFiber x y (rawFiber x y L₀)
                      ∧ L ∈ rawFiber x y L₀)

/-- Membership characterisation of the good-fiber set: `L` is good iff
it lies in *some* good raw fiber. -/
lemma mem_goodFiberSet {x y : α} {L : LinearExt α} :
    L ∈ goodFiberSet x y ↔
      ∃ L₀, IsGoodFiber x y (rawFiber x y L₀) ∧ L ∈ rawFiber x y L₀ := by
  classical
  unfold goodFiberSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A linear extension whose own raw fiber is good lies in the
good-fiber set. -/
lemma mem_goodFiberSet_of_isGoodFiber {x y : α} {L : LinearExt α}
    (hF : IsGoodFiber x y (rawFiber x y L)) : L ∈ goodFiberSet x y :=
  mem_goodFiberSet.mpr ⟨L, hF, self_mem_rawFiber x y L⟩

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
