/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.DropsHeadlineChamber
import OneThird.Mathlib.LinearExtension.OrderPolytope

/-!
# Drops headline — single-edge induction + swap involution (EX-7 Session C.2)

This file lands the structural induction lemma reducing `Q.Subseteq Q'`
to a chain of single-edge `addRel` augmentations, plus the cube-side
swap involution `cubeSwap a b` and the polytope-level chamber identity

```
OrderPolytope' Q  =  OrderPolytope' (addRel Q a b _)
                      ∪ OrderPolytope' (addRel Q b a _)
```

modulo the Lebesgue-null diagonal hyperplane `{f : f a = f b}`.

This is piece **(b)** of the EX-7 Session C decomposition (state.md
§1.26, mg-1f3a handoff brief); piece (a) is the chamber transport in
`DropsHeadlineChamber.lean` (Session C.1, mg-1f3a) and piece (c) is
the master theorem assembly via continuous AD + Stanley log-supermod
(Session C.3, forthcoming).

## Scope (mg-934f, Session C.2; Option 1 closure path, no 5th axiom)

Per state.md §1.26 forward pointer:

* **(b1)** structural induction lemma reducing `Q.Subseteq Q'` to a
  chain of single-edge `addRel` augmentations (~80–100 LoC) — §1
  `subseteq_addRel_induction`.
* **(b2)** cube-side swap involution `τ_{ab}` for `(a, b)` `Q`-
  incomparable, plus the chamber identity `O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))`
  modulo a Lebesgue-null hyperplane (~100–120 LoC) — §2 + §3.

The trust surface stays at four named axioms (`brightwell_sharp_centred`,
`case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
`cellMass_AD`); no new project axioms are introduced.

## Main declarations

* `RelationPoset.subseteq_addRel_induction` — the single-edge induction
  principle: to prove `P : RelationPoset α → Prop` at `Q` from
  `Q.Subseteq Q'` and `P Q'`, it suffices to handle a single-edge
  `addRel` step.
* `RelationPoset.cubeSwap` — the cube-side swap involution
  `(α → ℝ) ≃ᵐ (α → ℝ)` defined by `f ↦ f ∘ Equiv.swap a b`.
* `RelationPoset.cubeSwap_apply` — pointwise formula for the swap.
* `RelationPoset.cubeSwap_involutive` — `cubeSwap a b ∘ cubeSwap a b = id`.
* `RelationPoset.volume_measurePreserving_cubeSwap` — measure-preservation
  via `volume_measurePreserving_piCongrLeft`.
* `RelationPoset.OrderPolytope'_addRel_eq_inter_le` — for `(a, b)`
  Q-incomparable, `O(addRel Q a b _) = O(Q) ∩ {f : f a ≤ f b}`.
* `RelationPoset.OrderPolytope'_eq_union_addRel_addRel` — the chamber
  identity at the polytope level: `O(Q) = O(addRel Q a b _) ∪ O(addRel
  Q b a _)`.
* `RelationPoset.OrderPolytope'_inter_addRel_addRel_subset_diag` — the
  intersection of the two halves lies in the Lebesgue-null diagonal
  `{f : f a = f b}`.

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4.2 — single-edge induction + swap.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* `docs/path-alpha-execution-arc/ex7-drops-headline-scoping.md`
  (mg-2746) §2.4 — single-edge swap setup.
* `docs/path-alpha-execution-arc/state.md` §1.26 — Session C.2 handoff
  brief (mg-1f3a).
-/

namespace OneThird

open Finset MeasureTheory

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — Single-edge induction principle

Strong induction on `Q'.rel.card - Q.rel.card`: at each step, pick any
new pair `(a, b) ∈ Q'.rel \ Q.rel`. By antisymmetry of `Q'`, `(b, a)`
is not in `Q'.rel` either, so `¬ Q.le b a` (since `Q.rel ⊆ Q'.rel`).
This gives a well-defined intermediate poset `addRel Q a b _` strictly
between `Q` and `Q'`, decreasing the gap by ≥ 1. -/

/-- **Single-edge induction principle.** To prove a property
`P : RelationPoset α → Prop` at `Q` from a `Q.Subseteq Q'` hypothesis
where `P` holds at `Q'`, it suffices to show `P` propagates from
`addRel R a b _` to `R` for any `R`-incomparable pair `(a, b)` lying
inside `Q'`. -/
theorem subseteq_addRel_induction {Q Q' : RelationPoset α}
    (hQQ' : Q.Subseteq Q') (P : RelationPoset α → Prop)
    (hP_Q' : P Q')
    (hP_step : ∀ R : RelationPoset α, R.Subseteq Q' →
      ∀ a b (hba : ¬ R.le b a) (_ : ¬ R.le a b),
        (addRel R a b hba).Subseteq Q' → P (addRel R a b hba) → P R) :
    P Q := by
  classical
  -- Strong induction on the gap k := Q'.rel.card - R.rel.card.
  suffices h : ∀ (k : ℕ) (R : RelationPoset α) (_ : R.Subseteq Q'),
      Q'.rel.card - R.rel.card = k → P R from
    h _ _ hQQ' rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro R hRQ' hk
    by_cases hgap : Q'.rel.card - R.rel.card = 0
    · -- Equal-card case: R.rel ⊆ Q'.rel and same card → R = Q'.
      have hcard_le : R.rel.card ≤ Q'.rel.card := hRQ'.card_rel_le
      have hcard_eq : R.rel.card = Q'.rel.card := by omega
      have hreq : R.rel = Q'.rel :=
        Finset.eq_of_subset_of_card_le hRQ' hcard_eq.ge
      have hReq : R = Q' := RelationPoset.ext hreq
      rw [hReq]; exact hP_Q'
    · -- Strictly smaller case: pick `(a, b) ∈ Q'.rel \ R.rel`.
      have hpos : 0 < Q'.rel.card - R.rel.card := Nat.pos_of_ne_zero hgap
      have hsub_strict : R.rel ⊂ Q'.rel := by
        refine ⟨hRQ', fun hsup => ?_⟩
        have hcard_le2 : Q'.rel.card ≤ R.rel.card := Finset.card_le_card hsup
        have hcard_eq : R.rel.card = Q'.rel.card :=
          Nat.le_antisymm hRQ'.card_rel_le hcard_le2
        omega
      obtain ⟨p, hpQ', hpR⟩ : ∃ p, p ∈ Q'.rel ∧ p ∉ R.rel := by
        rcases Finset.exists_of_ssubset hsub_strict with ⟨p, hpQ', hpR⟩
        exact ⟨p, hpQ', hpR⟩
      -- Decompose p = (a, b); membership in `.rel` is the `.le` form by `mem_rel_iff`.
      obtain ⟨a, b⟩ := p
      have h_ab_Q' : Q'.le a b := hpQ'
      have h_ab_R : ¬ R.le a b := hpR
      have h_ba_R : ¬ R.le b a := by
        intro hle
        -- R.le b a → Q'.le b a, paired with Q'.le a b, gives a = b by antisymm,
        -- so (a, b) is reflexive, hence in R.rel — contradicting h_ab_R.
        have h_ba_Q' : Q'.le b a := hRQ'.le_of_le hle
        have hab : a = b := Q'.le_antisymm h_ab_Q' h_ba_Q'
        apply h_ab_R
        rw [hab]; exact R.le_refl b
      -- Build intermediate R' := addRel R a b _.
      set R' : RelationPoset α := addRel R a b h_ba_R with hR'_def
      have hR_R' : R.Subseteq R' := subseteq_addRel R a b h_ba_R
      -- R'.rel.card > R.rel.card (strict).
      have hcard_lt : R.rel.card < R'.rel.card :=
        card_rel_lt_addRel R a b h_ba_R h_ab_R
      -- R'.Subseteq Q': R'.rel = R.rel ∪ addedPairs R a b ⊆ Q'.rel.
      have hR'Q' : R'.Subseteq Q' := by
        intro q hq
        rcases Finset.mem_union.mp hq with hq_R | hq_added
        · exact hRQ' hq_R
        · -- (q.1, q.2) ∈ addedPairs R a b: R.le q.1 a ∧ R.le b q.2.
          rw [mem_addedPairs] at hq_added
          obtain ⟨hxa, hby⟩ := hq_added
          have hxa' : Q'.le q.1 a := hRQ'.le_of_le hxa
          have hby' : Q'.le b q.2 := hRQ'.le_of_le hby
          have hxy : Q'.le q.1 q.2 :=
            Q'.le_trans hxa' (Q'.le_trans h_ab_Q' hby')
          exact hxy
      -- Apply IH at gap < k.
      have hgap_R' : Q'.rel.card - R'.rel.card < k := by
        have h1 : R'.rel.card ≤ Q'.rel.card := hR'Q'.card_rel_le
        omega
      have hPR' : P R' := ih _ hgap_R' R' hR'Q' rfl
      -- Apply step.
      exact hP_step R hRQ' a b h_ba_R h_ab_R hR'Q' hPR'

/-! ### §2 — Cube swap `cubeSwap a b`

The cube-side swap involution `τ_{ab} : (α → ℝ) ≃ᵐ (α → ℝ)` defined by
post-composition with `Equiv.swap a b`: `τ_{ab}(f) x = f (swap a b x)`.

This is realised as `(MeasurableEquiv.piCongrLeft (fun _ => ℝ) (Equiv.swap a b)).symm`
following the `relabelEquiv` pattern of mg-10d9 / mg-497d. -/

/-- The **cube swap involution** at the value level: for `a, b : α`,
`cubeSwap a b : (α → ℝ) ≃ᵐ (α → ℝ)` is the measurable equivalence
`f ↦ f ∘ Equiv.swap a b`. -/
def cubeSwap (a b : α) : (α → ℝ) ≃ᵐ (α → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) (Equiv.swap a b)).symm

omit [Fintype α] in
@[simp] lemma cubeSwap_apply (a b : α) (f : α → ℝ) (x : α) :
    cubeSwap a b f x = f (Equiv.swap a b x) := by
  -- By `Equiv.piCongrLeft_symm_apply`.
  change ((MeasurableEquiv.piCongrLeft (fun _ : α => ℝ)
            (Equiv.swap a b)).symm : (α → ℝ) → _) f x
    = f (Equiv.swap a b x)
  rfl

omit [Fintype α] in
/-- The cube swap is **involutive**: applying twice gives the identity. -/
lemma cubeSwap_involutive (a b : α) :
    Function.Involutive (cubeSwap a b : (α → ℝ) → (α → ℝ)) := by
  intro f
  funext x
  simp [cubeSwap_apply, Equiv.swap_apply_self]

/-- The cube swap is **measure-preserving** under Lebesgue measure on
`α → ℝ`. Transports `volume_measurePreserving_piCongrLeft`. -/
lemma volume_measurePreserving_cubeSwap (a b : α) :
    MeasurePreserving (cubeSwap a b)
      (volume : Measure (α → ℝ)) (volume : Measure (α → ℝ)) :=
  (volume_measurePreserving_piCongrLeft (fun _ : α => ℝ) (Equiv.swap a b)).symm

/-! ### §3 — Polytope identities for single-edge augmentation

For `(a, b)` with `¬ Q.le b a` (the well-definedness hypothesis for
`addRel Q a b _`), the order polytope of `addRel Q a b _` is exactly
the slice of `OrderPolytope' Q` cut by `{f : f a ≤ f b}`.  Combined
with `le_total` on ℝ, this gives the chamber identity at the polytope
level. -/

/-- **Single-edge polytope cut.** For `(a, b)` with `¬ Q.le b a`,
`OrderPolytope' (addRel Q a b _) = OrderPolytope' Q ∩ {f : f a ≤ f b}`. -/
theorem OrderPolytope'_addRel_eq_inter_le {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) :
    OrderPolytope' (addRel Q a b hba) =
      OrderPolytope' Q ∩ { f : α → ℝ | f a ≤ f b } := by
  ext f
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_OrderPolytope']
  constructor
  · -- (⟹): f respects (addRel Q a b _).le, hence f respects Q.le and f a ≤ f b.
    rintro ⟨hcube, hmono⟩
    refine ⟨⟨hcube, fun x y hxy => ?_⟩, ?_⟩
    · -- Q.le x y → (addRel Q a b _).le x y by Subseteq.
      exact hmono x y ((subseteq_addRel Q a b hba).le_of_le hxy)
    · -- (a, b) ∈ (addRel Q a b _).rel by addRel_le.
      exact hmono a b (addRel_le Q a b hba)
  · -- (⟸): f respects Q.le and f a ≤ f b, hence f respects (addRel Q a b _).le.
    rintro ⟨⟨hcube, hQmono⟩, hab_le⟩
    refine ⟨hcube, fun x y hxy => ?_⟩
    -- (x, y) ∈ Q.rel ∪ addedPairs Q a b.
    rw [addRel_le_iff] at hxy
    rcases hxy with hxy_Q | ⟨hxa, hby⟩
    · exact hQmono x y hxy_Q
    · -- (x, y) ∈ addedPairs Q a b: f x ≤ f a ≤ f b ≤ f y.
      exact (hQmono x a hxa).trans (hab_le.trans (hQmono b y hby))

/-- **Single-edge polytope cover.** For `(a, b)` with `¬ Q.le b a` and
`¬ Q.le a b` (i.e., `(a, b)` is `Q`-incomparable), the order polytope
of `Q` is the union of the order polytopes of the two single-edge
augmentations `addRel Q a b _` and `addRel Q b a _`.

Proof: `O(addRel Q a b _) = O(Q) ∩ {f a ≤ f b}` and
`O(addRel Q b a _) = O(Q) ∩ {f b ≤ f a}` by §3 above; their union is
`O(Q) ∩ ({f a ≤ f b} ∪ {f b ≤ f a}) = O(Q)` by `le_total` on ℝ. -/
theorem OrderPolytope'_eq_union_addRel_addRel {Q : RelationPoset α}
    {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    OrderPolytope' Q =
      OrderPolytope' (addRel Q a b hba) ∪ OrderPolytope' (addRel Q b a hab) := by
  rw [OrderPolytope'_addRel_eq_inter_le hba,
      OrderPolytope'_addRel_eq_inter_le hab]
  ext f
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro hf
    rcases le_total (f a) (f b) with hle | hle
    · exact Or.inl ⟨hf, hle⟩
    · exact Or.inr ⟨hf, hle⟩
  · rintro (⟨hf, _⟩ | ⟨hf, _⟩) <;> exact hf

/-- **Single-edge polytope intersection lies in the diagonal hyperplane.**
For `(a, b)` `Q`-incomparable, the intersection of the two single-edge
augmentation polytopes is contained in `{f : f a = f b}`, the
Lebesgue-null diagonal hyperplane (`equalCoordSubmoduleAlpha a b`). -/
theorem OrderPolytope'_inter_addRel_addRel_subset_diag {Q : RelationPoset α}
    {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    OrderPolytope' (addRel Q a b hba) ∩ OrderPolytope' (addRel Q b a hab) ⊆
      (OneThird.LinearExt.OrderPolytope.equalCoordSubmoduleAlpha a b
        : Set (α → ℝ)) := by
  rw [OrderPolytope'_addRel_eq_inter_le hba,
      OrderPolytope'_addRel_eq_inter_le hab]
  rintro f ⟨⟨_, hab_le⟩, ⟨_, hba_le⟩⟩
  -- f a ≤ f b and f b ≤ f a → f a = f b.
  change f a = f b
  exact _root_.le_antisymm (a := f a) (b := f b) hab_le hba_le

/-- **Lebesgue-null intersection (volume corollary).** For `(a, b)`
`Q`-incomparable with `a ≠ b`, the intersection of the two
single-edge augmentation polytopes is Lebesgue-null. -/
theorem volume_OrderPolytope'_inter_addRel_addRel
    (Q : RelationPoset α) {a b : α} (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (hne : a ≠ b) :
    volume (OrderPolytope' (addRel Q a b hba) ∩
            OrderPolytope' (addRel Q b a hab)) = 0 := by
  letI : PartialOrder α := Q.asPartialOrder
  apply measure_mono_null
    (OrderPolytope'_inter_addRel_addRel_subset_diag hba hab)
  exact OneThird.LinearExt.OrderPolytope.volume_equalCoordSubmoduleAlpha hne

/-! ### §4 — Forward to EX-7 Session C.3

Session C.3 (master theorem `probEvent'_mono_of_subseteq_upClosed`)
consumes:

* **§1 `subseteq_addRel_induction`** — reduces the master theorem to
  the single-edge case `Q' = addRel Q a b _`, where `(a, b)` is
  `Q`-incomparable.
* **§2 `cubeSwap`** — the cube-side swap `f ↦ f ∘ swap a b`, used
  inside the inner-step continuous AD argument to relate integrals
  over `OrderPolytope' (addRel Q a b _)` to integrals over
  `OrderPolytope' (addRel Q b a _)`.
* **§3 polytope identities** — `OrderPolytope'_eq_union_addRel_addRel`
  + `volume_OrderPolytope'_inter_addRel_addRel` give the chamber
  identity `vol(O(Q)) = vol(O(addRel Q a b _)) + vol(O(addRel Q b a _))`
  modulo a Lebesgue-null hyperplane, the structural fact closing the
  level-`k` reduction in Brightwell §4.2.

Combined with `OneThird.ContinuousFKG.continuous_ad_general` (mg-071b)
and `OneThird.LinearExt.stanley_log_supermod` (mg-d0fc), Session C.3
will close `probEvent'_mono_of_subseteq_upClosed` without introducing
a 5th project axiom; the trust surface stays at the four named
axioms (`brightwell_sharp_centred`,
`case3Witness_hasBalancedPair_outOfScope`, `stanley_log_supermod`,
`cellMass_AD`). -/

end RelationPoset

end OneThird
