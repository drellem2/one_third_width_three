/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.DropsHeadlineMaster

/-!
# Inner inequality — chamber-integral / volume-form bridge (EX-7 Session C.4)

This file lands piece **(c4-1)** of the EX-7 Session C.4 plan from
`docs/path-alpha-execution-arc/state.md` §1.28: the chamber-integral
volume-form bridge for the single-edge inner inequality
`RelationPoset.InnerInequality` defined in
`DropsHeadlineMaster.lean` (mg-7a4f).

## Scope (mg-7b85, EX-7 Session C.4 piece (c4-1); Option α, no 5th axiom)

The master theorem `probEvent'_mono_of_subseteq_upClosed` was reduced
to the single-edge `InnerInequality`
```
numLinExt' Q⁻ · |{L ∈ LE Q⁺ : S(L_k)}|
  ≥ numLinExt' Q⁺ · |{L ∈ LE Q⁻ : S(L_k)}|
```
by mg-7a4f / Session C.3 (`DropsHeadlineMaster.lean` §5).

This file rewrites the four `(numLinExt'  ·, filter card  ·)` factors as
chamber-volume integrals over the cube `α → ℝ`:

* `numLinExt' Q±` becomes `n! · vol(O(Q±))` via mg-1f3a
  `orderPolytope'_volume`.
* `|{L ∈ LE Q± : S(L_k)}|` becomes `n! · vol(chamberSet' Q± S k)` via
  the chamber decomposition `chamber'_cover` + `chamber'_volume` +
  `chamber'_inter_meas_zero` of mg-1f3a, applied to the sub-finset
  `{L : S(L_k)}` rather than the full `Finset.univ`.

The volume form `volumeInnerInequality` then reads
```
vol(O(Q⁻)) · vol(chamberSet' Q⁺ S k) ≥ vol(O(Q⁺)) · vol(chamberSet' Q⁻ S k)
```
and the bridge `InnerInequality_iff_volumeInnerInequality` shows the
two are equivalent (both equivalent to the same `ℕ`-inequality after
clearing the `n!^2` denominators).

The genuinely substantive Brightwell §4 / Daykin–Saks 1981 swap-with-
conditional-AD step is left to a follow-up: it is now equivalent to
proving `volumeInnerInequality`, a chamber-volume comparison whose
shape is closer to a standard four-function continuous-AD application
than the original integer counts.  Per state.md §1.28, the shape of
the residual gap is characterised in §4 below.

## Main declarations

* `RelationPoset.chamberSet'` — for `Q : RelationPoset α`, decidable
  level-`k` event `S` on `Finset α`, the union of chambers `σ_L` over
  `L : LinearExt' Q` with `S(L.iI k)`, viewed as a subset of `α → ℝ`.
* `RelationPoset.chamberSet'_volume` — the volume of `chamberSet' Q S k`
  is `|{L : LE Q | S(L.iI k)}| / n!`.
* `RelationPoset.volumeInnerInequality` — the volume form of
  `InnerInequality`.
* `RelationPoset.InnerInequality_iff_volumeInnerInequality` — the
  bridge equivalence.

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4 — drops headline.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* `docs/path-alpha-execution-arc/state.md` §1.28 — Session C.4 hand-off
  brief (mg-7a4f) with `(c4-*)` split.
-/

namespace OneThird

open Finset MeasureTheory
open scoped ENNReal

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — `chamberSet'`: chambers of `Q` indexed by an event

For `S : Finset α → Prop` decidable, `chamberSet' Q S k` is the union
of chambers `σ_L` over `L ∈ LinearExt' Q` whose level-`k` initial ideal
satisfies `S`.  This is the cube subset whose volume — by the chamber
decomposition — equals `|{L : LE Q | S(L.iI k)}| / n!`. -/

/-- The union of chambers `σ_L` indexed by `L : LinearExt' Q` with
`S (L.initialIdeal' k)`.  Using a `Finset.univ.filter` indexing for
direct compatibility with `measure_biUnion_finset₀`. -/
def chamberSet' (Q : RelationPoset α) (S : Finset α → Prop) [DecidablePred S]
    (k : ℕ) : Set (α → ℝ) :=
  ⋃ L ∈ (Finset.univ.filter
    (fun L : LinearExt' Q => S (L.initialIdeal' k))), chamber' L

lemma mem_chamberSet' {Q : RelationPoset α} {S : Finset α → Prop}
    [DecidablePred S] {k : ℕ} {f : α → ℝ} :
    f ∈ chamberSet' Q S k ↔
      ∃ L : LinearExt' Q, S (L.initialIdeal' k) ∧ f ∈ chamber' L := by
  unfold chamberSet'
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop]

/-- `chamberSet'` is a subset of `OrderPolytope' Q`. -/
lemma chamberSet'_subset_orderPolytope' (Q : RelationPoset α)
    (S : Finset α → Prop) [DecidablePred S] (k : ℕ) :
    chamberSet' Q S k ⊆ OrderPolytope' Q := by
  intro f hf
  rw [mem_chamberSet'] at hf
  obtain ⟨L, _, hfL⟩ := hf
  exact chamber'_subset_orderPolytope' L hfL

/-- Each chamber in `chamberSet'` is Borel-measurable; the whole set is
measurable as a finite union. -/
lemma chamberSet'_measurableSet (Q : RelationPoset α)
    (S : Finset α → Prop) [DecidablePred S] (k : ℕ) :
    MeasurableSet (chamberSet' Q S k) := by
  classical
  unfold chamberSet'
  exact (Finset.univ.filter
      (fun L : LinearExt' Q => S (L.initialIdeal' k))).measurableSet_biUnion
    (fun L _ => measurableSet_chamber' L)

/-! ### §2 — Volume formula for `chamberSet'`

The volume of `chamberSet' Q S k` equals `|{L : LE Q | S(L.iI k)}| / n!`,
by the same chamber-decomposition argument that gives
`orderPolytope'_volume`: the family `{σ_L}_{L : S}` is pairwise
AE-disjoint (`chamber'_inter_meas_zero` for `L ≠ L'`), each chamber has
measurable indicator and volume `1/n!` (`chamber'_volume`), so the
union has volume `|{L : S}| · (1/n!)`. -/

/-- **Chamber-volume formula for `chamberSet'`.** -/
theorem chamberSet'_volume (Q : RelationPoset α)
    (S : Finset α → Prop) [DecidablePred S] (k : ℕ) :
    volume (chamberSet' Q S k) =
      ENNReal.ofReal
        (((Finset.univ.filter
            (fun L : LinearExt' Q => S (L.initialIdeal' k))).card : ℝ) /
          (Nat.factorial (Fintype.card α) : ℝ)) := by
  classical
  unfold chamberSet'
  -- AE-disjoint family of chambers indexed by the filter set.
  set T : Finset (LinearExt' Q) :=
    Finset.univ.filter (fun L : LinearExt' Q => S (L.initialIdeal' k)) with hT_def
  have hAE : Set.Pairwise (T : Set (LinearExt' Q))
      (fun L L' : LinearExt' Q =>
        AEDisjoint volume (chamber' L) (chamber' L')) :=
    fun L _ L' _ hLL' => chamber'_inter_meas_zero hLL'
  have hMble : ∀ L ∈ T, NullMeasurableSet (chamber' L) volume :=
    fun L _ => (measurableSet_chamber' L).nullMeasurableSet
  rw [measure_biUnion_finset₀ hAE hMble]
  simp only [chamber'_volume]
  rw [Finset.sum_const]
  -- card • ENNReal.ofReal (1/n!) = ENNReal.ofReal (card / n!).
  have hcard_nn : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  rw [nsmul_eq_mul]
  rw [show ((T.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (T.card : ℝ) from
      (ENNReal.ofReal_natCast _).symm]
  rw [← ENNReal.ofReal_mul hcard_nn]
  congr 1
  ring

/-- **Real-valued chamber-volume formula for `chamberSet'`.** -/
theorem chamberSet'_volume_toReal (Q : RelationPoset α)
    (S : Finset α → Prop) [DecidablePred S] (k : ℕ) :
    (volume (chamberSet' Q S k)).toReal =
      ((Finset.univ.filter
        (fun L : LinearExt' Q => S (L.initialIdeal' k))).card : ℝ) /
        (Nat.factorial (Fintype.card α) : ℝ) := by
  classical
  rw [chamberSet'_volume]
  rw [ENNReal.toReal_ofReal]
  -- numerator nonneg, denominator > 0.
  have h_n_pos : (0 : ℝ) < (Nat.factorial (Fintype.card α) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  positivity

/-- **Real-valued volume formula for `OrderPolytope' Q`.** -/
theorem orderPolytope'_volume_toReal (Q : RelationPoset α) :
    (volume (OrderPolytope' Q : Set (α → ℝ))).toReal =
      (numLinExt' Q : ℝ) / (Nat.factorial (Fintype.card α) : ℝ) := by
  rw [orderPolytope'_volume]
  rw [ENNReal.toReal_ofReal]
  have h_n_pos : (0 : ℝ) < (Nat.factorial (Fintype.card α) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  positivity

/-! ### §3 — Volume form of `InnerInequality`

The volume-form analogue of `InnerInequality` reads:
```
vol(O(Q⁻)) · vol(chamberSet' Q⁺ S k)
  ≥ vol(O(Q⁺)) · vol(chamberSet' Q⁻ S k)
```
working in `ℝ` (via `ENNReal.toReal`) — equivalently in `ℝ≥0∞`.
The bridge `InnerInequality_iff_volumeInnerInequality` proves the
two are equivalent: both reduce to the same integer inequality
`numLinExt' Q⁻ · M⁺ ≥ numLinExt' Q⁺ · M⁻` after clearing the `n!^2`
denominator. -/

/-- **The volume-form inner inequality.**  For `(a, b)` `Q`-incomparable
and any decidable level-`k` event `S` on `Finset α`, the cube-volume
inequality
```
vol(O(addRel Q b a _)) · vol(chamberSet' (addRel Q a b _) S k)
  ≥ vol(O(addRel Q a b _)) · vol(chamberSet' (addRel Q b a _) S k)
```
working in `ℝ` (via `ENNReal.toReal`).  Equivalent to `InnerInequality`
modulo the `n!^2` denominator (see
`InnerInequality_iff_volumeInnerInequality`). -/
def volumeInnerInequality
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] : Prop :=
  (volume (OrderPolytope' (addRel Q b a hab) : Set (α → ℝ))).toReal *
      (volume (chamberSet' (addRel Q a b hba) S k.val)).toReal
  ≥ (volume (OrderPolytope' (addRel Q a b hba) : Set (α → ℝ))).toReal *
      (volume (chamberSet' (addRel Q b a hab) S k.val)).toReal

/-- **Bridge: discrete `InnerInequality` ↔ volume-form
`volumeInnerInequality`.**  Both unfold to the same integer inequality
`numLinExt' Q⁻ · M⁺ ≥ numLinExt' Q⁺ · M⁻` after clearing `(n!)²`. -/
theorem InnerInequality_iff_volumeInnerInequality
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    InnerInequality Q hba hab k S ↔
      volumeInnerInequality Q hba hab k S := by
  classical
  unfold InnerInequality volumeInnerInequality
  -- Substitute the four toReal-volumes.
  rw [orderPolytope'_volume_toReal (addRel Q b a hab),
      orderPolytope'_volume_toReal (addRel Q a b hba),
      chamberSet'_volume_toReal (addRel Q a b hba) S k.val,
      chamberSet'_volume_toReal (addRel Q b a hab) S k.val]
  -- Both sides reduce to the same ℕ-inequality after multiplying by (n!)².
  set N : ℕ := Nat.factorial (Fintype.card α)
  set NpQ : ℕ := numLinExt' (addRel Q a b hba)
  set NnQ : ℕ := numLinExt' (addRel Q b a hab)
  set MpQ : ℕ := (Finset.univ.filter
    (fun L : LinearExt' (addRel Q a b hba) =>
      S (L.initialIdeal' k.val))).card
  set MnQ : ℕ := (Finset.univ.filter
    (fun L : LinearExt' (addRel Q b a hab) =>
      S (L.initialIdeal' k.val))).card
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hN_sq_pos : (0 : ℝ) < (N : ℝ) * (N : ℝ) := mul_pos hN_pos hN_pos
  -- Algebraic identity: products with a common (N*N) denominator factor.
  have hexp_p : ((NpQ : ℝ) / (N : ℝ)) * ((MnQ : ℝ) / (N : ℝ)) =
      ((NpQ : ℝ) * (MnQ : ℝ)) / ((N : ℝ) * (N : ℝ)) := by
    field_simp
  have hexp_n : ((NnQ : ℝ) / (N : ℝ)) * ((MpQ : ℝ) / (N : ℝ)) =
      ((NnQ : ℝ) * (MpQ : ℝ)) / ((N : ℝ) * (N : ℝ)) := by
    field_simp
  -- Translate the ℚ-inequality to an ℝ-inequality.
  rw [ge_iff_le, ge_iff_le]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- ℚ ⟹ ℝ.
    have hℝ : (NpQ : ℝ) * (MnQ : ℝ) ≤ (NnQ : ℝ) * (MpQ : ℝ) := by
      exact_mod_cast h
    rw [hexp_p, hexp_n]
    exact div_le_div_of_nonneg_right hℝ (_root_.le_of_lt hN_sq_pos)
  · -- ℝ ⟹ ℚ.
    rw [hexp_p, hexp_n] at h
    -- (NpQ*MnQ)/(N*N) ≤ (NnQ*MpQ)/(N*N) ⟹ NpQ*MnQ ≤ NnQ*MpQ.
    have hℝ : (NpQ : ℝ) * (MnQ : ℝ) ≤ (NnQ : ℝ) * (MpQ : ℝ) := by
      have hsq_ne : (N : ℝ) * (N : ℝ) ≠ 0 := ne_of_gt hN_sq_pos
      have := mul_le_mul_of_nonneg_right h (_root_.le_of_lt hN_sq_pos)
      rwa [div_mul_cancel₀ _ hsq_ne, div_mul_cancel₀ _ hsq_ne] at this
    exact_mod_cast hℝ

/-! ### §4 — Forward to the volume-form Brightwell §4 closure

The remaining substantive step is to prove `volumeInnerInequality`,
i.e., the cube-volume inequality
```
vol(O(Q⁻)) · vol(chamberSet' Q⁺ S k)
  ≥ vol(O(Q⁺)) · vol(chamberSet' Q⁻ S k).
```

This is the natural setting for the Brightwell §4 / Daykin–Saks 1981
swap-with-conditional-AD argument: both sides are integrals against
Lebesgue measure of products of indicator functions
(`𝟙_{O(Q±)}`, `𝟙_{chamberSet' Q± S k}`), and the chain
`vol(O(Q⁻)) · vol(chamberSet' Q⁺ S k)
  = ∫_{α → ℝ} 𝟙_{O(Q⁻)}(x) dx · ∫_{α → ℝ} 𝟙_{O(Q⁺)}(y) · 𝟙_{S}(L_y.iI k) dy`
makes the candidate four-function setup
```
f₁ := 𝟙_{O(Q⁻)},
f₂ := 𝟙_{O(Q⁺)} · 𝟙_S,
f₃ := 𝟙_{O(Q⁺)},
f₄ := 𝟙_{O(Q⁻)} · 𝟙_S,
```
a literal application of `OneThird.ContinuousFKG.continuous_ad_general`
(mg-071b, Monotone-free), modulo two technical obligations:

1. **The level-`k` indicator `𝟙_S∘L_·_k` is well-defined off a Lebesgue-
   null set** (the chamber boundaries).  This requires a measurable
   representative on the closed cube and a null-set-free a.e. equality
   to the chamber-defined version.  Standard but ~80–150 LoC of
   measure-theory glue.

2. **The pointwise four-function AD inequality on the cube fails for
   the natural `(f₁, f₂, f₃, f₄)`** (per mg-2746 §2.3 vertex-level
   counterexample, validated in mg-7a4f mid-session cube-vertex case
   analysis).  The genuine Brightwell §4 / Daykin–Saks 1981 closure
   uses a more delicate setup involving:
   * a chamber-by-chamber pairing argument that handles the `f` with
     `f a = f b` on a Lebesgue-null hyperplane separately;
   * a swap-with-conditional-AD argument restricted to the chamber
     where the swap τ_{ab} *does* preserve `Q.le` (i.e., the chambers
     `σ_L` for `L ∈ LinearExt' Q` where the swap of positions of `a`
     and `b` in `L` is still a `Q`-LE — these are exactly the LEs
     where `a, b` are adjacent in `L.pos`);
   * `stanley_log_supermod` (mg-d0fc) at the final discrete-sum
     closure step.

   This combined argument is estimated at ~500–1000+ LoC by mg-2746
   §7.2 / state.md §1.27 / state.md §1.28, beyond a single polecat
   budget.  This file packages the chamber-volume reduction so the
   follow-up polecat can focus directly on the residual
   `volumeInnerInequality` closure.

See `state.md` §1.29 (this commit) for the EX-7 Session C.4 (c4-1)
status and the residual Brightwell §4 chamber-AD gap. -/

end RelationPoset

end OneThird
