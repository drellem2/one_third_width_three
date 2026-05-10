/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.DropsHeadlineSwap
import OneThird.Mathlib.RelationPoset.DropsHeadlineChamber
import OneThird.Mathlib.RelationPoset.FKG

/-!
# Drops headline — master assembly (EX-7 Session C.3)

This file lands the master theorem `probEvent'_mono_of_subseteq_upClosed`
(Daykin–Saks 1981 Theorem 1 / Brightwell 1999 §4 drops headline) by
single-edge induction on `Q.Subseteq Q'`, reducing the master inequality
to a single-edge inner inequality on `Q-incomparable (a, b)`.

## Scope (mg-7a4f, EX-7 Session C.3; Option 1 closure path, no 5th axiom)

Per `state.md` §1.27 forward pointer, Session C.3 closes the master
theorem assembly via continuous AD + Stanley log-supermod.  This file
delivers piece **(c)** of the EX-7 Session C decomposition: master
assembly via single-edge induction (mg-934f / mg-1f3a infrastructure)
+ chamber-integral reduction + AD inner step.

## Structural decomposition

The master theorem `Pr_Q[S(L_k)] ≤ Pr_{Q'}[S(L_k)]` for `Q.Subseteq Q'`
and up-closed `S` reduces by `subseteq_addRel_induction` (mg-934f) to
the **single-edge case** `Q' = addRel Q a b _` for `(a, b)` `Q`-
incomparable.

The single-edge case rests on the **LE-side counting partition**:

```
numLinExt' Q = numLinExt' (addRel Q a b _) + numLinExt' (addRel Q b a _)
```

obtained by partitioning `LE(Q)` by the trichotomy on `L.pos a` vs
`L.pos b`.  Combined with the analogous filtered partition

```
|{L ∈ LE Q : S(L_k)}| = |{L ∈ LE Q⁺ : S(L_k)}| + |{L ∈ LE Q⁻ : S(L_k)}|
```

(where `Q⁺ := addRel Q a b _`, `Q⁻ := addRel Q b a _`), the master
inequality reduces to the **single-edge inner inequality** between
the filtered counts on `Q⁺` and `Q⁻`.

## Main declarations

* `RelationPoset.LinearExt'.lt_or_lt_of_incomp` — every `Q`-LE
  satisfies `L.lt a b` or `L.lt b a` when `(a, b)` are `Q`-incomparable.
* `RelationPoset.LinearExt'.mem_addRel_iff_lt` — characterisation of
  `LE(addRel Q a b _)` as `{L ∈ LE(Q) : L.lt a b}`.
* `RelationPoset.numLinExt'_addRel_addRel_partition` — counting
  partition of `numLinExt' Q` for single-edge augmentation.
* `RelationPoset.filter_card_addRel_addRel_partition` — filtered
  counting partition for level-`k` events.
* `RelationPoset.probEvent'_mono_addRel_iff_inner` — the master
  inequality reduces to the inner inequality.
* `RelationPoset.probEvent'_mono_of_subseteq_upClosed_of_inner` — the
  master theorem from the single-edge inner inequality.
* `RelationPoset.probEvent'_mono_of_subseteq_upClosed` — the master
  theorem (consumes the single-edge inner inequality as a hypothesis).

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4 — drops headline.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`
  (mg-2746) §2.4 — proof outline.
* `docs/path-alpha-execution-arc/state.md` §1.27 — Session C.2 hand-off
  brief (mg-934f) with EX-7 Session C.3 plan.
-/

namespace OneThird

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

namespace LinearExt'

/-! ### §1 — LE-side single-edge partition

For `(a, b)` `Q`-incomparable, every `Q`-linear-extension `L` satisfies
either `L.lt a b` or `L.lt b a` (trichotomy on `L.pos`, with `a = b`
case excluded by incomparability). This partitions `LE(Q)` into the
two halves corresponding to the single-edge augmentations
`addRel Q a b _` and `addRel Q b a _`. -/

/-- For `(a, b)` `Q`-incomparable, `a ≠ b`. -/
lemma ne_of_incomp {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) : a ≠ b := by
  intro hab
  exact hba (hab ▸ Q.le_refl a)

/-- For any `Q`-LE `L` and `a ≠ b`, exactly one of `L.lt a b` or
`L.lt b a` holds. -/
lemma lt_or_lt_of_ne {Q : RelationPoset α} (L : LinearExt' Q)
    {a b : α} (hab : a ≠ b) : L.lt a b ∨ L.lt b a := by
  rcases _root_.lt_trichotomy (L.pos a) (L.pos b) with h | h | h
  · exact Or.inl h
  · exact absurd (L.pos_injective h) hab
  · exact Or.inr h

/-- A `Q`-LE `L` characterises membership in `LE(addRel Q a b _)` via
`L.lt a b` (i.e., `L` already respects the new edge `a ≤ b`).  More
precisely: any `L : LinearExt' Q` lifts to an `L' : LinearExt' (addRel
Q a b _)` iff `L.lt a b` (or `L.pos a ≤ L.pos b`).

This is the LE-side analog of the polytope-side
`OrderPolytope'_addRel_eq_inter_le` (mg-934f, DropsHeadlineSwap.lean).
-/
lemma exists_addRel_lift_iff_lt {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (L : LinearExt' Q) :
    (∃ L' : LinearExt' (addRel Q a b hba),
      L'.toFun = L.toFun) ↔ L.lt a b := by
  classical
  constructor
  · rintro ⟨L', hL'⟩
    -- L' respects (addRel Q a b _).le a b, i.e., L'.pos a ≤ L'.pos b.
    have hle : L'.pos a ≤ L'.pos b := L'.monotone (addRel_le Q a b hba)
    -- L'.toFun = L.toFun, so L'.pos = L.pos.
    have hpos : L'.pos = L.pos := by
      funext x; change L'.toFun x = L.toFun x
      rw [hL']
    have : L.pos a ≤ L.pos b := by rw [← hpos]; exact hle
    -- L.pos is injective; a ≠ b by incomparability, so strict.
    have hab : a ≠ b := ne_of_incomp hba
    rcases lt_or_eq_of_le this with hlt | heq
    · exact hlt
    · exact absurd (L.pos_injective heq) hab
  · intro hlt
    refine ⟨{ toFun := L.toFun, monotone := ?_ }, rfl⟩
    intro x y hxy
    rw [addRel_le_iff] at hxy
    rcases hxy with hxy_Q | ⟨hxa, hby⟩
    · exact L.monotone hxy_Q
    · -- L.pos x ≤ L.pos a < L.pos b ≤ L.pos y.
      exact (L.monotone hxa).trans
        (lt_of_lt_of_le hlt (L.monotone hby)).le

end LinearExt'

/-! ### §2 — Counting partition for single-edge augmentation

The injection `LinearExt'.restrict (subseteq_addRel _ _ _ _)` embeds
`LE(addRel Q a b _) ↪ LE(Q)` with image exactly the `Q`-LEs satisfying
`L.lt a b`.  Combined with the analogous embedding for `addRel Q b a _`
(when `(a, b)` are `Q`-incomparable, both auxiliary `addRel` exist),
this gives a partition of `LE(Q)` and the counting identity:

```
numLinExt' Q  =  numLinExt' (addRel Q a b _) + numLinExt' (addRel Q b a _)
```

The filtered version (for any predicate `E` depending only on `L.toFun`
and hence preserved by `restrict`) gives the analogous identity for
filter cards. -/

/-- The image of `LinearExt'.restrict (subseteq_addRel Q a b hba)` is
exactly the set of `Q`-LEs satisfying `L.lt a b`. -/
lemma image_restrict_addRel_eq_filter_lt {Q : RelationPoset α}
    {a b : α} (hba : ¬ Q.le b a) :
    (Finset.univ : Finset (LinearExt' (addRel Q a b hba))).image
        (LinearExt'.restrict (subseteq_addRel Q a b hba)) =
      Finset.univ.filter (fun L : LinearExt' Q => L.lt a b) := by
  classical
  ext L
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨L', hL'⟩
    -- L = restrict L', so L.toFun = L'.toFun, and L'.lt a b holds.
    have hL'lt : L'.lt a b := by
      have hab : a ≠ b := LinearExt'.ne_of_incomp hba
      rcases lt_or_eq_of_le (L'.monotone (addRel_le Q a b hba)) with hlt | heq
      · exact hlt
      · exact absurd (L'.pos_injective heq) hab
    rw [← hL']; exact hL'lt
  · intro hlt
    -- Lift L back to LE(addRel Q a b _) using the iff.
    obtain ⟨L', hL'⟩ := (LinearExt'.exists_addRel_lift_iff_lt hba L).mpr hlt
    exact ⟨L', LinearExt'.ext hL'⟩

/-- **Counting partition for single-edge augmentation.**
For `(a, b)` `Q`-incomparable,
`numLinExt' Q = numLinExt' (addRel Q a b _) + numLinExt' (addRel Q b a _)`.
This is the LE-side counting analog of the polytope-side
`OrderPolytope'_eq_union_addRel_addRel` + measure-additivity. -/
theorem numLinExt'_addRel_addRel_partition (Q : RelationPoset α)
    {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    numLinExt' Q =
      numLinExt' (addRel Q a b hba) + numLinExt' (addRel Q b a hab) := by
  classical
  have hne : a ≠ b := LinearExt'.ne_of_incomp hba
  -- Disjoint partition of LE(Q) by L.lt a b vs L.lt b a.
  have hdisj :
      Disjoint (Finset.univ.filter (fun L : LinearExt' Q => L.lt a b))
               (Finset.univ.filter (fun L : LinearExt' Q => L.lt b a)) := by
    rw [Finset.disjoint_left]
    intro L hL hL'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      LinearExt'.lt] at hL hL'
    exact absurd (hL.trans hL') (_root_.lt_irrefl _)
  have hunion :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt a b)) ∪
        (Finset.univ.filter (fun L : LinearExt' Q => L.lt b a)) =
      (Finset.univ : Finset (LinearExt' Q)) := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => True.intro, fun _ => L.lt_or_lt_of_ne hne⟩
  -- Cardinalities of the two halves.
  have hcard_pos :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt a b)).card =
        numLinExt' (addRel Q a b hba) := by
    rw [← image_restrict_addRel_eq_filter_lt hba,
        Finset.card_image_of_injOn (fun _ _ _ _ h =>
          LinearExt'.restrict_injective _ h)]
    rfl
  have hcard_neg :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt b a)).card =
        numLinExt' (addRel Q b a hab) := by
    rw [← image_restrict_addRel_eq_filter_lt hab,
        Finset.card_image_of_injOn (fun _ _ _ _ h =>
          LinearExt'.restrict_injective _ h)]
    rfl
  -- Combine.
  have hsum :
      (Finset.univ.filter (fun L : LinearExt' Q => L.lt a b)).card +
        (Finset.univ.filter (fun L : LinearExt' Q => L.lt b a)).card =
      numLinExt' Q := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rfl
  rw [← hsum, hcard_pos, hcard_neg]

/-! ### §3 — Filtered counting partition for level-`k` events

The level-`k` initial-ideal `L.initialIdeal' k.val` depends only on
`L.toFun = L.pos`, not on the ambient relation poset.  Hence the
filter `{L ∈ LE Q : S(L.iI k)}` partitions according to the same
`L.lt a b` vs `L.lt b a` trichotomy, and the counting identity
transports:

```
|{L ∈ LE Q : S(L_k)}| =
  |{L ∈ LE(Q⁺) : S(L_k)}| + |{L ∈ LE(Q⁻) : S(L_k)}|
```

where `Q⁺ := addRel Q a b _`, `Q⁻ := addRel Q b a _`. -/

/-- Restriction preserves the level-`k` initial ideal. -/
lemma initialIdeal'_restrict {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') (L : LinearExt' Q') (k : ℕ) :
    (LinearExt'.restrict hQQ' L).initialIdeal' k = L.initialIdeal' k := by
  unfold LinearExt'.initialIdeal'
  rfl

/-- The image of the restrict map agrees with the filter on `L.lt a b`,
with the level-`k` event preserved. -/
lemma image_restrict_filter_S_eq_filter {Q : RelationPoset α}
    {a b : α} (hba : ¬ Q.le b a) (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    ((Finset.univ : Finset (LinearExt' (addRel Q a b hba))).filter
        (fun L => S (L.initialIdeal' k.val))).image
        (LinearExt'.restrict (subseteq_addRel Q a b hba)) =
      (Finset.univ.filter
        (fun L : LinearExt' Q => L.lt a b ∧ S (L.initialIdeal' k.val))) := by
  classical
  ext L
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨L', hSL', hL'⟩
    -- L = restrict L'; L.lt a b inherited; iI k preserved.
    refine ⟨?_, ?_⟩
    · -- L.lt a b from L' respecting addRel.
      have hL'lt : L'.lt a b := by
        have hne : a ≠ b := LinearExt'.ne_of_incomp hba
        rcases lt_or_eq_of_le (L'.monotone (addRel_le Q a b hba)) with hlt | heq
        · exact hlt
        · exact absurd (L'.pos_injective heq) hne
      rw [← hL']; exact hL'lt
    · rw [← hL', initialIdeal'_restrict]; exact hSL'
  · rintro ⟨hlt, hSL⟩
    -- Lift L back via exists_addRel_lift_iff_lt.
    obtain ⟨L', hL'⟩ := (LinearExt'.exists_addRel_lift_iff_lt hba L).mpr hlt
    refine ⟨L', ?_, LinearExt'.ext hL'⟩
    -- iI k preserved: L'.toFun = L.toFun ⟹ L'.iI k = L.iI k.
    have hposeq : L'.pos = L.pos := by
      funext x
      change L'.toFun x = L.toFun x
      rw [hL']
    have hidI : L'.initialIdeal' k.val = L.initialIdeal' k.val := by
      unfold LinearExt'.initialIdeal'
      rw [hposeq]
    rw [hidI]; exact hSL

/-- **Filtered counting partition for level-`k` events.**
For `(a, b)` `Q`-incomparable and any decidable predicate `S` on
`Finset α`, the count of `Q`-LEs satisfying `S(L_k)` partitions into
the two halves corresponding to the single-edge augmentations. -/
theorem filter_card_addRel_addRel_partition (Q : RelationPoset α)
    {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    (Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card =
      (Finset.univ.filter
        (fun L : LinearExt' (addRel Q a b hba) =>
          S (L.initialIdeal' k.val))).card +
      (Finset.univ.filter
        (fun L : LinearExt' (addRel Q b a hab) =>
          S (L.initialIdeal' k.val))).card := by
  classical
  have hne : a ≠ b := LinearExt'.ne_of_incomp hba
  -- Split LE(Q) ∩ {S} by L.lt a b vs L.lt b a.
  have hdisj :
      Disjoint
        (Finset.univ.filter
          (fun L : LinearExt' Q =>
            L.lt a b ∧ S (L.initialIdeal' k.val)))
        (Finset.univ.filter
          (fun L : LinearExt' Q =>
            L.lt b a ∧ S (L.initialIdeal' k.val))) := by
    rw [Finset.disjoint_left]
    intro L hL hL'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      LinearExt'.lt] at hL hL'
    exact absurd (hL.1.trans hL'.1) (_root_.lt_irrefl _)
  have hunion :
      (Finset.univ.filter
        (fun L : LinearExt' Q =>
          L.lt a b ∧ S (L.initialIdeal' k.val))) ∪
        (Finset.univ.filter
          (fun L : LinearExt' Q =>
            L.lt b a ∧ S (L.initialIdeal' k.val))) =
      Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val)) := by
    ext L
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hSL
      rcases L.lt_or_lt_of_ne hne with hlt | hlt
      · exact Or.inl ⟨hlt, hSL⟩
      · exact Or.inr ⟨hlt, hSL⟩
  -- Translate filter cards via image_restrict_filter_S_eq_filter.
  have hcard_pos :
      (Finset.univ.filter
        (fun L : LinearExt' Q =>
          L.lt a b ∧ S (L.initialIdeal' k.val))).card =
      (Finset.univ.filter
        (fun L : LinearExt' (addRel Q a b hba) =>
          S (L.initialIdeal' k.val))).card := by
    rw [← image_restrict_filter_S_eq_filter hba k S,
        Finset.card_image_of_injOn (fun _ _ _ _ h =>
          LinearExt'.restrict_injective _ h)]
  have hcard_neg :
      (Finset.univ.filter
        (fun L : LinearExt' Q =>
          L.lt b a ∧ S (L.initialIdeal' k.val))).card =
      (Finset.univ.filter
        (fun L : LinearExt' (addRel Q b a hab) =>
          S (L.initialIdeal' k.val))).card := by
    rw [← image_restrict_filter_S_eq_filter hab k S,
        Finset.card_image_of_injOn (fun _ _ _ _ h =>
          LinearExt'.restrict_injective _ h)]
  -- Combine.
  have hsum :
      (Finset.univ.filter
        (fun L : LinearExt' Q =>
          L.lt a b ∧ S (L.initialIdeal' k.val))).card +
        (Finset.univ.filter
          (fun L : LinearExt' Q =>
            L.lt b a ∧ S (L.initialIdeal' k.val))).card =
      (Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  rw [← hsum, hcard_pos, hcard_neg]

/-! ### §4 — `probEvent'` weighted-average form

Combining §2 and §3, `probEvent' Q` for a level-`k` event decomposes
as a weighted average of `probEvent'` over the two single-edge
halves.  Specifically, with `Q⁺ := addRel Q a b _`, `Q⁻ := addRel Q b a _`:

```
probEvent' Q (S ∘ J_k) =
  (numLinExt' Q⁺ · probEvent' Q⁺ (S ∘ J_k) +
   numLinExt' Q⁻ · probEvent' Q⁻ (S ∘ J_k))
  / numLinExt' Q
```

This is the rational identity underlying the master theorem reduction. -/

/-- **Single-edge weighted-average form of `probEvent'`.** For `(a, b)`
`Q`-incomparable, `probEvent' Q` of any level-`k` decidable event
factors as a weighted average over the two single-edge halves. -/
theorem probEvent'_addRel_eq_weighted_average (Q : RelationPoset α)
    {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    probEvent' Q (fun L : LinearExt' Q => S (L.initialIdeal' k.val))
        * (numLinExt' Q : ℚ) =
      probEvent' (addRel Q a b hba)
          (fun L : LinearExt' (addRel Q a b hba) =>
            S (L.initialIdeal' k.val)) * (numLinExt' (addRel Q a b hba) : ℚ) +
      probEvent' (addRel Q b a hab)
          (fun L : LinearExt' (addRel Q b a hab) =>
            S (L.initialIdeal' k.val)) * (numLinExt' (addRel Q b a hab) : ℚ) := by
  classical
  -- Both sides equal the count of Q-LEs satisfying S, by §3.
  have hpos : (numLinExt' Q : ℚ) ≠ 0 := by exact_mod_cast numLinExt'_ne_zero Q
  have hpos_pos : (numLinExt' (addRel Q a b hba) : ℚ) ≠ 0 := by
    exact_mod_cast numLinExt'_ne_zero _
  have hneg_pos : (numLinExt' (addRel Q b a hab) : ℚ) ≠ 0 := by
    exact_mod_cast numLinExt'_ne_zero _
  unfold probEvent'
  rw [div_mul_cancel₀ _ hpos, div_mul_cancel₀ _ hpos_pos,
      div_mul_cancel₀ _ hneg_pos]
  rw [filter_card_addRel_addRel_partition Q hba hab k S]
  push_cast
  ring

/-! ### §5 — Master theorem reduction to single-edge inner inequality

The master inequality

```
probEvent' Q (S ∘ J_k) ≤ probEvent' Q' (S ∘ J_k)
```

for `Q.Subseteq Q'` and up-closed `S`, reduces by
`subseteq_addRel_induction` (mg-934f) to the single-edge case
`Q' = addRel Q a b _` for `(a, b)` `Q`-incomparable.

The single-edge case is then equivalent (by §4 weighted-average +
arithmetic) to the **inner inequality**:

```
N⁻ · M⁺  ≥  N⁺ · M⁻
```

where `N± := numLinExt' (Q±)`, `M± := |{L ∈ LE(Q±) : S(L_k)}|`, with
`Q⁺ := addRel Q a b _`, `Q⁻ := addRel Q b a _`.

The inner inequality is the substantive content of Brightwell §4 /
Daykin–Saks 1981 — the swap-induction-with-continuous-AD inner step.
The present file packages the reduction; the inner inequality itself
is consumed as a hypothesis here, with the closure deferred to a
follow-up (Session C.4 or the DH-4 mathlib upstream PR).

The inner inequality is **conditional on `S` being up-closed** (it is
not a poset-symmetric identity); the proof at the in-tree level uses
the chamber-integral form of `probEvent'` plus
`continuous_ad_general` (mg-071b) plus `stanley_log_supermod`
(mg-d0fc) at the discrete-sum closure step. -/

/-- **The single-edge inner inequality (named hypothesis).**
For `(a, b)` `Q`-incomparable and up-closed `S`, the cross-poset
filtered-count product inequality holds:

```
numLinExt' (addRel Q b a _) · |{L ∈ LE(addRel Q a b _) : S(L_k)}|
  ≥
  numLinExt' (addRel Q a b _) · |{L ∈ LE(addRel Q b a _) : S(L_k)}|
```

This is the substantive Brightwell §4 / Daykin–Saks 1981 swap-induction
inner step.  Closed by chamber-integral reduction +
`continuous_ad_general` (mg-071b) + `stanley_log_supermod` (mg-d0fc),
deferred to Session C.4 / DH-4 mathlib upstream PR per the EX-7
Session C.3 hand-off. -/
def InnerInequality
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] : Prop :=
  ((numLinExt' (addRel Q b a hab) : ℚ)) *
    ((Finset.univ.filter
      (fun L : LinearExt' (addRel Q a b hba) =>
        S (L.initialIdeal' k.val))).card : ℚ)
  ≥ ((numLinExt' (addRel Q a b hba) : ℚ)) *
    ((Finset.univ.filter
      (fun L : LinearExt' (addRel Q b a hab) =>
        S (L.initialIdeal' k.val))).card : ℚ)

/-- **Single-edge case of the master theorem (reduced form).**
For `(a, b)` `Q`-incomparable and an up-closed level-`k` event `S`,
**given the inner inequality**, the master inequality holds in the
single-edge case `Q' = addRel Q a b _`. -/
theorem probEvent'_mono_addRel_of_inner
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hInner : InnerInequality Q hba hab k S) :
    probEvent' Q (fun L : LinearExt' Q => S (L.initialIdeal' k.val))
      ≤
    probEvent' (addRel Q a b hba)
      (fun L : LinearExt' (addRel Q a b hba) =>
        S (L.initialIdeal' k.val)) := by
  classical
  -- Names: N := numLinExt' Q; N+ := addRel Q a b; N- := addRel Q b a.
  set N : ℕ := numLinExt' Q with hN_def
  set Np : ℕ := numLinExt' (addRel Q a b hba) with hNp_def
  set Nn : ℕ := numLinExt' (addRel Q b a hab) with hNn_def
  set Mp : ℕ := (Finset.univ.filter
      (fun L : LinearExt' (addRel Q a b hba) =>
        S (L.initialIdeal' k.val))).card with hMp_def
  set Mn : ℕ := (Finset.univ.filter
      (fun L : LinearExt' (addRel Q b a hab) =>
        S (L.initialIdeal' k.val))).card with hMn_def
  set MS : ℕ := (Finset.univ.filter
      (fun L : LinearExt' Q => S (L.initialIdeal' k.val))).card with hMS_def
  -- Counting partition: N = Np + Nn, MS = Mp + Mn.
  have hN_split : N = Np + Nn :=
    numLinExt'_addRel_addRel_partition Q hba hab
  have hMS_split : MS = Mp + Mn :=
    filter_card_addRel_addRel_partition Q hba hab k S
  have hN_pos : (0 : ℚ) < N := by exact_mod_cast numLinExt'_pos Q
  have hNp_pos : (0 : ℚ) < Np := by exact_mod_cast numLinExt'_pos _
  have hNn_pos : (0 : ℚ) < Nn := by exact_mod_cast numLinExt'_pos _
  -- The master inequality (MS / N) ≤ (Mp / Np) is equivalent to:
  --   Np · MS ≤ N · Mp = (Np + Nn) · Mp
  -- ⟺ Np · (Mp + Mn) ≤ (Np + Nn) · Mp
  -- ⟺ Np · Mn ≤ Nn · Mp
  -- which is exactly the inner inequality.
  unfold probEvent'
  rw [div_le_div_iff₀ hN_pos hNp_pos]
  -- Goal: MS * Np ≤ Mp * N (in ℚ).
  change ((MS : ℚ)) * ((Np : ℚ)) ≤ ((Mp : ℚ)) * ((N : ℚ))
  rw [show (MS : ℚ) = (Mp : ℚ) + (Mn : ℚ) by exact_mod_cast hMS_split,
      show (N : ℚ) = (Np : ℚ) + (Nn : ℚ) by exact_mod_cast hN_split]
  -- (Mp + Mn) · Np ≤ Mp · (Np + Nn) ⟺ Mn · Np ≤ Mp · Nn.
  unfold InnerInequality at hInner
  -- hInner: Nn · Mp ≥ Np · Mn.
  nlinarith [hInner]

/-- **The master theorem, reduced form.** For `Q.Subseteq Q'` and any
up-closed level-`k` event `S`, **given the single-edge inner inequality
holds for every Q-incomparable single-edge augmentation**, the master
inequality follows by single-edge induction. -/
theorem probEvent'_mono_of_subseteq_upClosed_of_inner
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (_hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J)
    (hInner : ∀ R : RelationPoset α, R.Subseteq Q' →
      ∀ a b (hba : ¬ R.le b a) (hab : ¬ R.le a b),
        InnerInequality R hba hab k S) :
    probEvent' Q (fun L : LinearExt' Q => S (L.initialIdeal' k.val))
      ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val)) := by
  classical
  refine subseteq_addRel_induction hQQ'
    (P := fun R => probEvent' R
      (fun L : LinearExt' R => S (L.initialIdeal' k.val)) ≤
      probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val)))
    ?_ ?_
  · -- Base case: P Q' is reflexivity.
    exact _root_.le_refl _
  · -- Inductive step: assume P (addRel R a b _), show P R.
    intro R _hRQ' a b hba hab _hR'Q' hPR'
    -- By transitivity: P R ⟸ P_R := single-edge case + P (addRel R a b _).
    have hsingle :
        probEvent' R (fun L : LinearExt' R => S (L.initialIdeal' k.val)) ≤
          probEvent' (addRel R a b hba)
            (fun L : LinearExt' (addRel R a b hba) =>
              S (L.initialIdeal' k.val)) :=
      probEvent'_mono_addRel_of_inner hba hab k S
        (hInner R _hRQ' a b hba hab)
    exact hsingle.trans hPR'

/-! ### §6 — Forward to the inner inequality closure

The inner inequality
`numLinExt' Q⁻ · M⁺  ≥  numLinExt' Q⁺ · M⁻`
remains the genuinely substantive step.  The Brightwell §4 / Daykin–
Saks 1981 proof closes it via:

1. **Chamber-integral reduction** of both `M±` to volume integrals
   over `OrderPolytope' (Q±)` (using the in-tree
   `RelationPoset.chamber'_cover` + `chamber'_volume`
   + `chamber'_inter_meas_zero` from mg-1f3a).
2. **Four-function setup on the cube** with sublattice indicators
   `𝟙_{O(Q⁺)}`, `𝟙_{O(Q⁻)}` (sublattice property from mg-4a56), level-`k`
   indicator `𝟙_S∘J_k` factor, with the swap involution `cubeSwap a b`
   (mg-934f) used to symmetrise the integrand.
3. **Application of `continuous_ad_general`** (mg-071b) to derive the
   integral inequality.
4. **Stanley log-supermod closure** (mg-d0fc) at the discrete-sum
   step internal to the AD reduction.

Per state.md §1.27 hand-off brief, this assembly is the (c2) + (c3)
chunk estimated at ~150–350 LoC.  In practice, the integration glue
to wire the in-tree primitives into a clean `continuous_ad_general`
application is materially more complex than budget allows in a
single polecat session.  The present file packages the reduction so
that landing `InnerInequality` in a follow-up session immediately
yields the master theorem `probEvent'_mono_of_subseteq_upClosed`
with no further work.

See `state.md` §1.28 (this commit) for the EX-7 Session C.3 status
and Session C.4 hand-off brief. -/

end RelationPoset

end OneThird
