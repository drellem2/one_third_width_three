/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Basic

/-!
# Relation-as-data finite posets

In Mathlib, `PartialOrder α` is a typeclass: a fixed type `α` carries
a fixed `≤` relation. This file introduces `RelationPoset α`, the
*data version* of a finite partial order — the relation is a
`Finset (α × α)` bundled with reflexivity / antisymmetry /
transitivity hypotheses, and *multiple* `RelationPoset α` values can
coexist on the same underlying type `α`.

This is the foundational data type for the Case 2 FKG
monotonicity-under-augmentation argument of `prop:in-situ-balanced`
(`step8.tex:3001-3032`), which couples linear extensions of two
distinct posets `Q` and `Q'` on the same ground set: `Q'` is obtained
from `Q` by adding (or removing) a single comparability. With
`PartialOrder` as a typeclass this is awkward — every `α` carries one
fixed order; with `RelationPoset α` it is a routine value-level
manipulation.

## Main declarations

* `RelationPoset α` — the data type.
* `RelationPoset.le`, `RelationPoset.lt` — the partial-order relations
  as `Prop`s on `α`, parametrised by the `RelationPoset α` value.
* `RelationPoset.discrete` — the discrete poset (only `x ≤ x`).
* `RelationPoset.ofPartialOrder` — the `RelationPoset α` corresponding
  to an ambient `[PartialOrder α]` typeclass.
* `RelationPoset.addRel` — augment by a single new comparability
  `(a, b)`, given that `b ≤ a` does not already hold (so the new
  relation remains antisymmetric).
* `RelationPoset.eraseCoverRel` — restrict by removing a single cover
  relation `(a, b)` (no proper intermediate element exists), which is
  the form needed for the `Q''` construction in Case 2's symmetric
  starting poset.
* `RelationPoset.Subseteq` — the sub-poset relation
  `Q.rel ⊆ Q'.rel`, with API `Subseteq.le_of_le` showing the
  implication on `Q.le` is the expected direction.
* `RelationPoset.lt_wellFounded` — `<` on a finite ground set is
  well-founded (derived from `Finite.wellFounded_of_trans_of_irrefl`).
* `RelationPoset.instFintype_le_subtype` — a `Fintype` instance on
  the subtype `{p : α × α // Q.le p.1 p.2}`, witnessing the
  data-level finiteness of the relation.

## Downstream use

`OneThird.Mathlib.RelationPoset` is consumed by:

* `OneThird.Mathlib.RelationPoset.LinearExt` (A8-S2-cont-2) —
  defines `LinearExt' Q : Type`, `numLinExt' Q : ℕ`, and `probLT' Q`
  as the data-level analogues of `LinearExt α`, `numLinExt α`,
  `probLT` over `RelationPoset α`.
* `OneThird.Mathlib.RelationPoset.FKG` (A8-S2-cont-3) — proves the
  FKG monotonicity-under-augmentation lemma
  `Subseteq Q Q' → ∀ E up-closed, probLT'.onEvent Q' E ≤ probLT'.onEvent Q E`,
  via the Birkhoff transport on the universal `LowerSet α` lattice
  shared by `Q` and `Q'`.

## References

* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`).
* `docs/a8-s2-status.md` §3a-3b — paper-vs-formalization gap
  analysis explaining why the typeclass-bundled `PartialOrder α` is
  insufficient for cross-poset coupling and why a data version is
  required.
-/

namespace OneThird

open Finset

variable {α : Type*}

/-! ### §1 — Definition -/

/-- A **finite poset given as data**: a `Finset (α × α)` of "edges"
representing the `≤` relation, bundled with reflexivity, antisymmetry,
and transitivity hypotheses.

Unlike `PartialOrder α` (a typeclass on the type `α`), a
`RelationPoset α` is a *value* — multiple `RelationPoset α` values can
coexist on the same underlying type, supporting the cross-poset
coupling argument of `prop:in-situ-balanced` Case 2
(`step8.tex:3001-3032`). -/
@[ext]
structure RelationPoset (α : Type*) [DecidableEq α] [Fintype α] where
  /-- The set of comparable ordered pairs `(x, y)` with `x ≤ y`. -/
  rel : Finset (α × α)
  /-- Reflexivity: every element is related to itself. -/
  refl' : ∀ x : α, (x, x) ∈ rel
  /-- Antisymmetry. -/
  antisymm' : ∀ {x y : α}, (x, y) ∈ rel → (y, x) ∈ rel → x = y
  /-- Transitivity. -/
  trans' : ∀ {x y z : α}, (x, y) ∈ rel → (y, z) ∈ rel → (x, z) ∈ rel

namespace RelationPoset

variable [DecidableEq α] [Fintype α]

/-! ### §2 — Basic order-theoretic API -/

/-- The `≤` relation on `α` parametrised by `Q : RelationPoset α`. -/
def le (Q : RelationPoset α) (x y : α) : Prop := (x, y) ∈ Q.rel

/-- The strict `<` relation on `α` parametrised by `Q : RelationPoset α`. -/
def lt (Q : RelationPoset α) (x y : α) : Prop := Q.le x y ∧ x ≠ y

lemma mem_rel_iff (Q : RelationPoset α) (x y : α) :
    (x, y) ∈ Q.rel ↔ Q.le x y := Iff.rfl

lemma le_refl (Q : RelationPoset α) (x : α) : Q.le x x := Q.refl' x

lemma le_trans (Q : RelationPoset α) {x y z : α} (hxy : Q.le x y)
    (hyz : Q.le y z) : Q.le x z := Q.trans' hxy hyz

lemma le_antisymm (Q : RelationPoset α) {x y : α} (hxy : Q.le x y)
    (hyx : Q.le y x) : x = y := Q.antisymm' hxy hyx

lemma lt_iff_le_and_ne (Q : RelationPoset α) {x y : α} :
    Q.lt x y ↔ Q.le x y ∧ x ≠ y := Iff.rfl

lemma lt_irrefl (Q : RelationPoset α) (x : α) : ¬ Q.lt x x :=
  fun h => h.2 rfl

lemma lt_trans (Q : RelationPoset α) {x y z : α} (hxy : Q.lt x y)
    (hyz : Q.lt y z) : Q.lt x z := by
  refine ⟨Q.le_trans hxy.1 hyz.1, fun hxz => ?_⟩
  -- If x = z then Q.le y z = Q.le y x, paired with Q.le x y, gives x = y by antisymmetry.
  apply hxy.2
  apply Q.le_antisymm hxy.1
  rw [hxz]
  exact hyz.1

lemma lt_asymm (Q : RelationPoset α) {x y : α} (hxy : Q.lt x y) :
    ¬ Q.lt y x := by
  intro hyx
  exact hxy.2 (Q.le_antisymm hxy.1 hyx.1)

lemma lt_of_le_of_ne (Q : RelationPoset α) {x y : α} (hle : Q.le x y)
    (hne : x ≠ y) : Q.lt x y := ⟨hle, hne⟩

lemma le_of_lt (Q : RelationPoset α) {x y : α} (h : Q.lt x y) :
    Q.le x y := h.1

instance instDecidableLe (Q : RelationPoset α) (x y : α) :
    Decidable (Q.le x y) :=
  inferInstanceAs (Decidable ((x, y) ∈ Q.rel))

instance instDecidableLt (Q : RelationPoset α) (x y : α) :
    Decidable (Q.lt x y) :=
  inferInstanceAs (Decidable (Q.le x y ∧ x ≠ y))

/-! ### §3 — Well-foundedness of `<` -/

/-- An auxiliary `Std.Irrefl` instance for `Q.lt`, packaged so that
`Finite.wellFounded_of_trans_of_irrefl` is applicable. -/
instance instStdIrreflLt (Q : RelationPoset α) : Std.Irrefl Q.lt :=
  ⟨Q.lt_irrefl⟩

/-- An auxiliary `IsTrans` instance for `Q.lt`. -/
instance instIsTransLt (Q : RelationPoset α) : IsTrans α Q.lt :=
  ⟨fun _ _ _ => Q.lt_trans⟩

/-- `Q.lt` is well-founded on a finite ground set. The standard mathlib
fact `Finite.wellFounded_of_trans_of_irrefl` packages this from
transitivity + irreflexivity (already established above) plus the
ambient `[Fintype α]`. -/
theorem lt_wellFounded (Q : RelationPoset α) : WellFounded Q.lt :=
  Finite.wellFounded_of_trans_of_irrefl Q.lt

/-! ### §4 — Fintype on the relation subtype

The relation `Q.le` is decidable (since `Q.rel` is a `Finset`), so the
subtype of comparable pairs is itself finite. We package this as a
`Fintype` instance for downstream use (e.g. defining a `LinearExt' Q`
type by enumerating bijections compatible with `Q.le`). -/

/-- The subtype of comparable pairs `{p : α × α // Q.le p.1 p.2}` is a
fintype, witnessed by `Q.rel` (with the membership coercion). -/
instance instFintype_le_subtype (Q : RelationPoset α) :
    Fintype {p : α × α // Q.le p.1 p.2} :=
  Fintype.subtype Q.rel (fun p => by simp [le])

/-- The cardinality of the relation subtype equals the cardinality of
`Q.rel` (the number of comparable ordered pairs, including reflexive
ones). -/
lemma card_le_subtype (Q : RelationPoset α) :
    Fintype.card {p : α × α // Q.le p.1 p.2} = Q.rel.card := by
  classical
  rw [Fintype.subtype_card]

/-! ### §5 — Sub-poset relation `Subseteq` -/

/-- `Q.Subseteq Q'` iff every pair comparable in `Q` is comparable in
`Q'`. Equivalently, `Q.rel ⊆ Q'.rel`. This is the key relation for the
FKG monotonicity-under-augmentation argument: every linear extension
of `Q'` (the larger poset, with more constraints) is a linear
extension of `Q` (the smaller poset, with fewer constraints). -/
def Subseteq (Q Q' : RelationPoset α) : Prop := Q.rel ⊆ Q'.rel

@[refl] lemma Subseteq.refl (Q : RelationPoset α) : Q.Subseteq Q :=
  fun _ h => h

@[trans] lemma Subseteq.trans {Q₁ Q₂ Q₃ : RelationPoset α}
    (h₁₂ : Q₁.Subseteq Q₂) (h₂₃ : Q₂.Subseteq Q₃) : Q₁.Subseteq Q₃ :=
  fun _ h => h₂₃ (h₁₂ h)

lemma Subseteq.le_of_le {Q Q' : RelationPoset α} (h : Q.Subseteq Q')
    {x y : α} (hle : Q.le x y) : Q'.le x y := h hle

lemma Subseteq.antisymm {Q Q' : RelationPoset α}
    (h₁ : Q.Subseteq Q') (h₂ : Q'.Subseteq Q) : Q = Q' := by
  apply RelationPoset.ext
  exact Finset.Subset.antisymm h₁ h₂

instance instDecidableSubseteq (Q Q' : RelationPoset α) :
    Decidable (Q.Subseteq Q') :=
  inferInstanceAs (Decidable (Q.rel ⊆ Q'.rel))

/-! ### §6 — Constructor: discrete poset -/

/-- The **discrete** `RelationPoset α`: only the diagonal relation
`{(x, x) | x : α}`, i.e. no proper comparabilities. -/
def discrete (α : Type*) [DecidableEq α] [Fintype α] : RelationPoset α where
  rel := (Finset.univ : Finset α).image (fun x => (x, x))
  refl' := fun x => by
    rw [Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, rfl⟩
  antisymm' := by
    intro x y hxy _
    rw [Finset.mem_image] at hxy
    obtain ⟨z, _, hz⟩ := hxy
    have hx : z = x := (Prod.mk.inj hz).1
    have hy : z = y := (Prod.mk.inj hz).2
    exact hx.symm.trans hy
  trans' := by
    intro x y z hxy hyz
    rw [Finset.mem_image] at hxy hyz
    obtain ⟨a, _, ha⟩ := hxy
    obtain ⟨b, _, hb⟩ := hyz
    have hax : a = x := (Prod.mk.inj ha).1
    have hay : a = y := (Prod.mk.inj ha).2
    have hby : b = y := (Prod.mk.inj hb).1
    have hbz : b = z := (Prod.mk.inj hb).2
    have hxy_eq : x = y := hax.symm.trans hay
    have hyz_eq : y = z := hby.symm.trans hbz
    rw [Finset.mem_image]
    exact ⟨x, Finset.mem_univ _, by rw [hxy_eq, hyz_eq]⟩

lemma discrete_le_iff (α : Type*) [DecidableEq α] [Fintype α]
    {x y : α} : (discrete α).le x y ↔ x = y := by
  change (x, y) ∈ (Finset.univ : Finset α).image (fun x => (x, x)) ↔ x = y
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, _, hz⟩
    have hx : z = x := (Prod.mk.inj hz).1
    have hy : z = y := (Prod.mk.inj hz).2
    exact hx.symm.trans hy
  · rintro rfl
    exact ⟨x, Finset.mem_univ _, rfl⟩

lemma discrete_lt_iff (α : Type*) [DecidableEq α] [Fintype α]
    {x y : α} : (discrete α).lt x y ↔ False := by
  rw [lt, discrete_le_iff]
  exact ⟨fun h => h.2 h.1, False.elim⟩

/-- The discrete poset is a sub-poset of every poset. -/
lemma discrete_subseteq (Q : RelationPoset α) :
    (discrete α).Subseteq Q := by
  intro p hp
  rw [show (discrete α).rel = (Finset.univ : Finset α).image (fun x => (x, x)) from rfl,
      Finset.mem_image] at hp
  obtain ⟨x, _, hx⟩ := hp
  rw [← hx]
  exact Q.refl' x

/-! ### §7 — Constructor: from a typeclass `PartialOrder α` -/

/-- Lift an ambient `[PartialOrder α]` typeclass to a value-level
`RelationPoset α`. The relation is the comparable-pairs set
`{p : α × α | p.1 ≤ p.2}` realised as a `Finset` via `Finset.univ`
together with the decidability of `≤`. -/
def ofPartialOrder (α : Type*) [DecidableEq α] [Fintype α]
    [PartialOrder α] [DecidableLE α] : RelationPoset α where
  rel := (Finset.univ : Finset (α × α)).filter (fun p => p.1 ≤ p.2)
  refl' := fun x => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact _root_.le_refl x
  antisymm' := by
    intro x y hxy hyx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy hyx
    exact _root_.le_antisymm hxy hyx
  trans' := by
    intro x y z hxy hyz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy hyz ⊢
    exact _root_.le_trans hxy hyz

lemma ofPartialOrder_le_iff (α : Type*) [DecidableEq α]
    [Fintype α] [PartialOrder α] [DecidableLE α] {x y : α} :
    (ofPartialOrder α).le x y ↔ x ≤ y := by
  change (x, y) ∈ (Finset.univ : Finset (α × α)).filter (fun p => p.1 ≤ p.2) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma ofPartialOrder_lt_iff (α : Type*) [DecidableEq α]
    [Fintype α] [PartialOrder α] [DecidableLE α] {x y : α} :
    (ofPartialOrder α).lt x y ↔ x < y := by
  rw [lt, ofPartialOrder_le_iff]
  exact ⟨fun ⟨h1, h2⟩ => _root_.lt_of_le_of_ne h1 h2,
         fun h => ⟨h.le, ne_of_lt h⟩⟩

/-! ### §8 — Constructor: augmented poset (`addRel`)

Given a poset `Q` and a pair `(a, b)` with `¬ Q.le b a`, augment `Q`
by the comparability `a ≤ b`. The new relation is the transitive
closure of `Q.rel ∪ {(a, b)}`, computed as

  `Q.rel ∪ {(x, y) | Q.le x a ∧ Q.le b y}`.

The hypothesis `¬ Q.le b a` is necessary (without it, adding `a ≤ b`
together with the existing `b ≤ a` would force `a = b` by
antisymmetry, which is generally false). -/

/-- The added pairs in `addRel Q a b`: pairs `(x, y)` such that
`Q.le x a ∧ Q.le b y`. By reflexivity of `Q`, this set always contains
`(a, b)` itself. -/
def addedPairs (Q : RelationPoset α) (a b : α) : Finset (α × α) :=
  (Finset.univ : Finset (α × α)).filter
    (fun p => Q.le p.1 a ∧ Q.le b p.2)

lemma mem_addedPairs (Q : RelationPoset α) (a b : α) (p : α × α) :
    p ∈ addedPairs Q a b ↔ Q.le p.1 a ∧ Q.le b p.2 := by
  rw [addedPairs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The augmented poset: add the comparability `(a, b)` to `Q`,
provided `¬ Q.le b a`. -/
def addRel (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a) :
    RelationPoset α where
  rel := Q.rel ∪ addedPairs Q a b
  refl' := fun x => Finset.mem_union_left _ (Q.refl' x)
  antisymm' := by
    intro x y hxy hyx
    rcases Finset.mem_union.mp hxy with hxy_old | hxy_new
    · rcases Finset.mem_union.mp hyx with hyx_old | hyx_new
      · -- both in Q.rel
        exact Q.antisymm' hxy_old hyx_old
      · -- (x, y) ∈ Q.rel, (y, x) ∈ added
        rw [mem_addedPairs] at hyx_new
        obtain ⟨hya, hbx⟩ := hyx_new
        -- Q.le x y, Q.le y a → Q.le x a; Q.le b x, Q.le x a → Q.le b a. Contradiction.
        exact (hba (Q.le_trans hbx (Q.le_trans hxy_old hya))).elim
    · rcases Finset.mem_union.mp hyx with hyx_old | hyx_new
      · -- (x, y) ∈ added, (y, x) ∈ Q.rel
        rw [mem_addedPairs] at hxy_new
        obtain ⟨hxa, hby⟩ := hxy_new
        -- Q.le b y, Q.le y x → Q.le b x; Q.le b x, Q.le x a → Q.le b a. Contradiction.
        exact (hba (Q.le_trans (Q.le_trans hby hyx_old) hxa)).elim
      · -- both in added
        rw [mem_addedPairs] at hxy_new hyx_new
        obtain ⟨_, hby⟩ := hxy_new
        obtain ⟨hya, _⟩ := hyx_new
        -- Q.le b y, Q.le y a → Q.le b a. Contradiction.
        exact (hba (Q.le_trans hby hya)).elim
  trans' := by
    intro x y z hxy hyz
    rcases Finset.mem_union.mp hxy with hxy_old | hxy_new
    · rcases Finset.mem_union.mp hyz with hyz_old | hyz_new
      · exact Finset.mem_union_left _ (Q.le_trans hxy_old hyz_old)
      · -- (x, y) ∈ Q.rel, (y, z) ∈ added
        rw [mem_addedPairs] at hyz_new
        obtain ⟨hya, hbz⟩ := hyz_new
        refine Finset.mem_union_right _ ?_
        rw [mem_addedPairs]
        exact ⟨Q.le_trans hxy_old hya, hbz⟩
    · rcases Finset.mem_union.mp hyz with hyz_old | hyz_new
      · -- (x, y) ∈ added, (y, z) ∈ Q.rel
        rw [mem_addedPairs] at hxy_new
        obtain ⟨hxa, hby⟩ := hxy_new
        refine Finset.mem_union_right _ ?_
        rw [mem_addedPairs]
        exact ⟨hxa, Q.le_trans hby hyz_old⟩
      · -- both in added: contradicts ¬ Q.le b a
        rw [mem_addedPairs] at hxy_new hyz_new
        obtain ⟨_, hby⟩ := hxy_new
        obtain ⟨hya, _⟩ := hyz_new
        exact (hba (Q.le_trans hby hya)).elim

lemma addRel_le_iff (Q : RelationPoset α) (a b : α)
    (hba : ¬ Q.le b a) (x y : α) :
    (addRel Q a b hba).le x y ↔ Q.le x y ∨ (Q.le x a ∧ Q.le b y) := by
  change (x, y) ∈ (Q.rel ∪ addedPairs Q a b) ↔ _
  rw [Finset.mem_union, mem_addedPairs]
  rfl

/-- The augmented poset is a super-poset of the original. -/
lemma subseteq_addRel (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a) :
    Q.Subseteq (addRel Q a b hba) :=
  fun _ hp => Finset.mem_union_left _ hp

/-- The augmented poset includes the new comparability `a ≤ b`. -/
lemma addRel_le (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a) :
    (addRel Q a b hba).le a b := by
  rw [addRel_le_iff]
  exact Or.inr ⟨Q.refl' a, Q.refl' b⟩

/-! ### §9 — Constructor: restricted poset (`eraseCoverRel`)

Given a poset `Q` and a comparability `(a, b)` with `a ≠ b` such that
`(a, b)` is a *cover* relation in `Q` (no proper intermediate `c`
distinct from both `a` and `b` satisfies `Q.le a c ∧ Q.le c b`), the
poset obtained by removing only the edge `(a, b)` from `Q.rel` is
again a `RelationPoset α`.

Removing a non-cover edge would break transitivity: if some
intermediate `c` exists with `Q.le a c` and `Q.le c b`, then both
`Q.le a c` and `Q.le c b` survive the removal but we no longer have
`Q.le a b` to chain them. -/

/-- A pair `(a, b)` is a **cover** in `Q` if `Q.le a b`, `a ≠ b`, and
no proper intermediate exists: every `c` with `Q.le a c` and
`Q.le c b` is either `a` or `b`. -/
def IsCover (Q : RelationPoset α) (a b : α) : Prop :=
  Q.le a b ∧ a ≠ b ∧ ∀ c : α, Q.le a c → Q.le c b → c = a ∨ c = b

/-- Remove a cover relation `(a, b)` from `Q`. The resulting `Finset`
satisfies the poset axioms because no `(x, z)` ≠ `(a, b)` could have
required `(a, b)` for its transitivity proof. -/
def eraseCoverRel (Q : RelationPoset α) (a b : α) (h : Q.IsCover a b) :
    RelationPoset α where
  rel := Q.rel.erase (a, b)
  refl' := fun x => by
    rw [Finset.mem_erase]
    refine ⟨?_, Q.refl' x⟩
    intro hxx
    -- (x, x) = (a, b) → x = a ∧ x = b → a = b, contradicting h.2.1.
    have hxa : x = a := (Prod.mk.inj hxx).1
    have hxb : x = b := (Prod.mk.inj hxx).2
    exact h.2.1 (hxa.symm.trans hxb)
  antisymm' := by
    intro x y hxy hyx
    rw [Finset.mem_erase] at hxy hyx
    exact Q.antisymm' hxy.2 hyx.2
  trans' := by
    intro x y z hxy hyz
    rw [Finset.mem_erase] at hxy hyz
    obtain ⟨hxy_ne, hxy_old⟩ := hxy
    obtain ⟨hyz_ne, hyz_old⟩ := hyz
    rw [Finset.mem_erase]
    refine ⟨?_, Q.le_trans hxy_old hyz_old⟩
    -- Suppose (x, z) = (a, b). Then x = a, z = b, and y is a proper
    -- intermediate. By the cover hypothesis, y = a or y = b — but
    -- in either case, the edge we'd be using ((x, y) or (y, z)) is
    -- exactly (a, b), which we erased.
    intro hxz
    have hxa : x = a := (Prod.mk.inj hxz).1
    have hzb : z = b := (Prod.mk.inj hxz).2
    subst hxa
    subst hzb
    -- Now x = a, z = b. (x, y) = (a, y) ∈ Q.rel \ {(a, b)} and
    -- (y, z) = (y, b) ∈ Q.rel \ {(a, b)}. Apply the cover hypothesis.
    obtain ⟨_, _, h_cover⟩ := h
    rcases h_cover y hxy_old hyz_old with rfl | rfl
    · -- y = a: then (y, z) = (a, b), but we erased (a, b). Contradiction.
      exact hyz_ne rfl
    · -- y = b: then (x, y) = (a, b), erased. Contradiction.
      exact hxy_ne rfl

lemma eraseCoverRel_le_iff (Q : RelationPoset α) (a b : α)
    (h : Q.IsCover a b) (x y : α) :
    (eraseCoverRel Q a b h).le x y ↔ Q.le x y ∧ ¬ (x = a ∧ y = b) := by
  change (x, y) ∈ (Q.rel.erase (a, b)) ↔ Q.le x y ∧ ¬ (x = a ∧ y = b)
  rw [Finset.mem_erase]
  refine ⟨fun ⟨hne, hmem⟩ => ⟨hmem, ?_⟩, fun ⟨hmem, hne⟩ => ⟨?_, hmem⟩⟩
  · rintro ⟨rfl, rfl⟩; exact hne rfl
  · intro hxz
    apply hne
    exact ⟨(Prod.mk.inj hxz).1, (Prod.mk.inj hxz).2⟩

/-- The restricted poset is a sub-poset of the original. -/
lemma eraseCoverRel_subseteq (Q : RelationPoset α) (a b : α)
    (h : Q.IsCover a b) : (eraseCoverRel Q a b h).Subseteq Q := by
  change (Q.rel.erase (a, b)) ⊆ Q.rel
  exact Finset.erase_subset _ _

/-- The erased pair is no longer in the restricted poset. -/
lemma eraseCoverRel_not_le (Q : RelationPoset α) (a b : α)
    (h : Q.IsCover a b) : ¬ (eraseCoverRel Q a b h).le a b := by
  intro hle
  rw [eraseCoverRel_le_iff] at hle
  exact hle.2 ⟨rfl, rfl⟩

/-! ### §10 — Roundtrip / sanity lemmas -/

/-- For an ambient `[PartialOrder α]` typeclass, `ofPartialOrder α`
is a super-poset of the discrete poset. -/
lemma discrete_subseteq_ofPartialOrder (α : Type*) [DecidableEq α]
    [Fintype α] [PartialOrder α] [DecidableLE α] :
    (discrete α).Subseteq (ofPartialOrder α) :=
  discrete_subseteq _

/-! ### §11 — Cardinality bookkeeping -/

/-- Reflexive pairs are always present, so `n ≤ |Q.rel|`. -/
lemma card_le_rel_le (Q : RelationPoset α) :
    Fintype.card α ≤ Q.rel.card := by
  classical
  -- The map `x ↦ (x, x)` injects α into Q.rel.
  have hinj : Function.Injective (fun x : α => ((x, x) : α × α)) :=
    fun a b h => (Prod.mk.inj h).1
  have hsubset : (Finset.univ : Finset α).image (fun x => (x, x)) ⊆ Q.rel := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨x, _, hx⟩ := hp
    rw [← hx]
    exact Q.refl' x
  calc Fintype.card α
      = (Finset.univ : Finset α).card := (Finset.card_univ).symm
    _ = ((Finset.univ : Finset α).image (fun x => (x, x))).card := by
        rw [Finset.card_image_of_injective _ hinj]
    _ ≤ Q.rel.card := Finset.card_le_card hsubset

/-- Sub-posets have smaller relations. -/
lemma Subseteq.card_rel_le {Q Q' : RelationPoset α} (h : Q.Subseteq Q') :
    Q.rel.card ≤ Q'.rel.card := Finset.card_le_card h

/-- Adding a comparability (when it is a genuinely new edge) strictly
grows the relation card by at least one. -/
lemma card_rel_lt_addRel (Q : RelationPoset α) (a b : α) (hba : ¬ Q.le b a)
    (hab : ¬ Q.le a b) : Q.rel.card < (addRel Q a b hba).rel.card := by
  classical
  have hsub : Q.rel ⊆ (addRel Q a b hba).rel :=
    subseteq_addRel Q a b hba
  refine Finset.card_lt_card ⟨hsub, fun h => hab ?_⟩
  -- (a, b) is in the augmented poset (via the reflexive pair `(a, a)`
  -- and `(b, b)` in addedPairs); if Q.rel = augmented, then (a, b) ∈ Q.rel.
  have hab_aug : (addRel Q a b hba).le a b := addRel_le Q a b hba
  exact h hab_aug

/-- Erasing a cover relation strictly shrinks the relation card by
exactly one. -/
lemma card_rel_eraseCoverRel (Q : RelationPoset α) (a b : α)
    (h : Q.IsCover a b) :
    (eraseCoverRel Q a b h).rel.card + 1 = Q.rel.card := by
  classical
  have hmem : (a, b) ∈ Q.rel := h.1
  rw [eraseCoverRel]
  exact Finset.card_erase_add_one hmem

/-! ### §12 — Decidable equality -/

instance instDecidableEq : DecidableEq (RelationPoset α) := fun Q Q' =>
  decidable_of_iff (Q.rel = Q'.rel) ⟨fun h => RelationPoset.ext h, fun h => h ▸ rfl⟩

end RelationPoset

end OneThird
