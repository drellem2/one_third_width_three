/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.LayeredReduction
import Mathlib.Order.Interval.Finset.Nat

/-!
# Step 8 — `LayeredDecomposition.compactify`: empty-band compactification

Builds the **band-compactification operator** on `LayeredDecomposition`
under sub-poset descent, fixing **Obstruction B** (empty bands at
sub-poset descent) of `mg-979e-block-and-report.md` §1.b.

## The bug this fixes

`LayeredDecomposition.restrict L S : LayeredDecomposition ↥S`
(`LayeredReduction.lean:203`) preserves the depth `K = L.K` and the
interaction width `w = L.w` but allows *empty bands*: an original
band index `k ∈ [1, L.K]` with no element of `S` in `L.bandSet k`
becomes an empty band of `L.restrict S`. Empty bands break two
downstream invariants:

1. `bounded_irreducible_balanced_inScope` (the K=3 InCase3Scope leaf)
   requires `1 ≤ bandSize L k` for every `k ∈ [1, K]`.
2. Reducible-cut search at sub-posets can find only "trivial" cuts
   (`D.Lower = ∅` or `D.Upper = ∅`) that produce zero progress on the
   strong-induction hypothesis.

The fix is **band-compactification**: at the moment of restriction,
build a new `LayeredDecomposition` on `↥S` whose depth `K'` counts
only the *non-empty* bands of `L.restrict S`, with band indices
densely renumbered.

## Architecture (`mg-979e` §3.a recommendation)

Given `L : LayeredDecomposition α` and `S : Finset α`, the
compactification `L.compactify S : LayeredDecomposition ↥S`:

* uses the same interaction width `w' := L.w` (no tightening);
* sets `K' := compactBand L S L.K`, the count of non-empty bands of
  `L.restrict S` in `[1, L.K]`;
* renumbers band indices: for `z : ↥S`,
  `(L.compactify S).band z := compactBand L S (L.band z.val)`,
  the *rank* of the original band `L.band z.val` among the non-empty
  band indices of `L.restrict S` lying in `[1, L.band z.val]`.

The constructor establishes `(L1)` (each band is an antichain of size
≤ 3) and `(L2)` (`forced_lt`, `cross_band_lt_upward`) directly from
the corresponding axioms of `L`. The structural correctness rests on
the strict monotonicity of `compactBand` at non-empty indices: rank
preserves the linear order of the underlying band indices, so each
new band coincides with the restriction of an original (non-empty)
band, and the (L2) constants `w` are preserved exactly.

## Preservation API

* `compactify_K_le : (L.compactify S).K ≤ L.K`
* `compactify_w_eq : (L.compactify S).w = L.w`
* `compactify_band_le_orig : (L.compactify S).band z ≤ L.band z.val`
* `compactify_K_le_of_K_le : depth-cap propagation`
* `compactify_card_le_of_card_le : cardinality-cap propagation`
* `compactify_band_injective_of_injective : Injective propagation`
* `compactify_band_eq_iff_band_eq : band relabelling structure`

These are the lemmas required to thread cap hypotheses (Candidate A''
of `mg-979e`: `LB.K ≤ 2 * LB.w + 2`, `Fintype.card β ≤ 6 * LB.w + 6`,
plus `Function.Injective LB.band`) through F3-style sub-poset descent.

## Computability

`NonEmptyOnS L S k` is decidable (existence over a `Finset`), so
`compactBand` and `compactify` are computable.

## References

* `mg-979e-block-and-report.md` §1.b — the empty-band obstruction
  this constructor closes.
* `mg-979e-block-and-report.md` §3.a — the polecat-recommended
  compactification architecture this implements.
* `lean/OneThird/Step8/LayeredReduction.lean` — base `LayeredDecomposition`
  structure plus the `restrict` operator we compactify on top of.
-/

namespace OneThird
namespace Step8
namespace LayeredDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — `NonEmptyOnS`: band non-emptiness on a sub-poset -/

/-- `NonEmptyOnS L S k`: the band index `k` contains at least one
element of `S`. Equivalent to `(L.restrict S).bandSize k ≥ 1`, but
phrased directly to avoid pulling in `bandSize` infrastructure
(`BoundedIrreducibleBalanced.lean`). -/
def NonEmptyOnS (L : LayeredDecomposition α) (S : Finset α) (k : ℕ) : Prop :=
  ∃ a ∈ S, L.band a = k

instance NonEmptyOnS.decidable (L : LayeredDecomposition α) (S : Finset α) (k : ℕ) :
    Decidable (NonEmptyOnS L S k) := by
  unfold NonEmptyOnS
  infer_instance

/-- The original band of any `z : ↥S` is non-empty on `S` (witnessed
by `z.val ∈ S` itself). -/
lemma nonEmptyOnS_band_val (L : LayeredDecomposition α) (S : Finset α) (z : ↥S) :
    NonEmptyOnS L S (L.band z.val) :=
  ⟨z.val, z.property, rfl⟩

/-! ### §2 — `compactBand`: the rank of a band index among non-empty bands -/

/-- The rank of `k` among the non-empty band indices of `L.restrict S`
lying in `[1, k]`. Concretely:
`compactBand L S k = #{ i ∈ [1, k] : NonEmptyOnS L S i }`.

The new depth is `K' := compactBand L S L.K`; the new band map sends
`z : ↥S` to `compactBand L S (L.band z.val)`. -/
def compactBand (L : LayeredDecomposition α) (S : Finset α) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun i => NonEmptyOnS L S i)).card

@[simp] lemma compactBand_zero (L : LayeredDecomposition α) (S : Finset α) :
    compactBand L S 0 = 0 := by
  unfold compactBand
  have h : (Finset.Icc 1 0 : Finset ℕ) = ∅ := by ext x; simp
  rw [h]
  rfl

/-- `compactBand` is monotone in its band-index argument. -/
lemma compactBand_mono (L : LayeredDecomposition α) (S : Finset α) {a b : ℕ}
    (hab : a ≤ b) : compactBand L S a ≤ compactBand L S b := by
  unfold compactBand
  apply Finset.card_le_card
  apply Finset.monotone_filter_left
  intro x hx
  simp only [Finset.mem_Icc] at hx ⊢
  exact ⟨hx.1, hx.2.trans hab⟩

/-- Strict monotonicity of `compactBand` at non-empty indices: if `a < b`
and `b` is a non-empty band index (and ≥ 1), then
`compactBand L S a < compactBand L S b`. -/
lemma compactBand_lt_of_lt_of_nonEmpty (L : LayeredDecomposition α) (S : Finset α)
    {a b : ℕ} (hab : a < b) (hb_pos : 1 ≤ b) (hb : NonEmptyOnS L S b) :
    compactBand L S a < compactBand L S b := by
  unfold compactBand
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · -- subset
    apply Finset.monotone_filter_left
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hab.le⟩
  · -- not equal: `b` is in the second filter but not the first
    intro hsub
    have hb_mem : b ∈ ((Finset.Icc 1 b).filter (fun i => NonEmptyOnS L S i)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb_pos, le_refl _⟩, hb⟩
    have hb_mem' : b ∈ ((Finset.Icc 1 a).filter (fun i => NonEmptyOnS L S i)) :=
      hsub hb_mem
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb_mem'
    omega

/-- The compactBand difference is bounded by the index difference: any
gap of `b - a` in band indices contributes at most `b - a` non-empty
bands, since each non-empty band contributes at most `1` to the rank. -/
lemma compactBand_diff_le (L : LayeredDecomposition α) (S : Finset α) {a b : ℕ}
    (hab : a ≤ b) :
    compactBand L S b ≤ compactBand L S a + (b - a) := by
  classical
  unfold compactBand
  -- Decompose `Icc 1 b = Icc 1 a ⊔ Ioc a b` (disjoint).
  have h_eq : (Finset.Icc 1 b) = (Finset.Icc 1 a) ∪ (Finset.Ioc a b) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · intro ⟨h1, h2⟩
      by_cases hxa : x ≤ a
      · exact Or.inl ⟨h1, hxa⟩
      · exact Or.inr ⟨not_le.mp hxa, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.trans hab⟩
      · exact ⟨by omega, h2⟩
  have h_disj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hy
    omega
  rw [h_eq, Finset.filter_union]
  rw [Finset.card_union_of_disjoint
      (h_disj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  have h_le : ((Finset.Ioc a b).filter (fun i => NonEmptyOnS L S i)).card ≤ b - a := by
    calc ((Finset.Ioc a b).filter (fun i => NonEmptyOnS L S i)).card
        ≤ (Finset.Ioc a b).card := Finset.card_filter_le _ _
      _ = b - a := Nat.card_Ioc _ _
  exact Nat.add_le_add_left h_le _

/-- A non-empty band index `k ≥ 1` gets compactBand value at least 1
(it itself participates in the count). -/
lemma one_le_compactBand_of_nonEmpty (L : LayeredDecomposition α) (S : Finset α)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk : NonEmptyOnS L S k) :
    1 ≤ compactBand L S k := by
  unfold compactBand
  apply Finset.card_pos.mpr
  refine ⟨k, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hk_pos, le_refl _⟩, hk⟩

/-- Equal compactBand values on `↥S` force equal original band values. -/
lemma compactBand_inj_on_S (L : LayeredDecomposition α) (S : Finset α)
    {z w : ↥S}
    (h : compactBand L S (L.band z.val) = compactBand L S (L.band w.val)) :
    L.band z.val = L.band w.val := by
  rcases lt_trichotomy (L.band z.val) (L.band w.val) with hlt | heq | hgt
  · exfalso
    have := compactBand_lt_of_lt_of_nonEmpty L S hlt
      (L.band_pos w.val) (nonEmptyOnS_band_val L S w)
    omega
  · exact heq
  · exfalso
    have := compactBand_lt_of_lt_of_nonEmpty L S hgt
      (L.band_pos z.val) (nonEmptyOnS_band_val L S z)
    omega

/-! ### §3 — `compactify`: the compactification constructor -/

/-- **Compactification of a layered decomposition under restriction**
(`mg-979e-block-and-report.md` §3.a).

Given `L : LayeredDecomposition α` and `S : Finset α`, builds
`L.compactify S : LayeredDecomposition ↥S` whose depth `K'` counts
only the non-empty bands of `L.restrict S`, with band indices densely
renumbered. The interaction width `w' = L.w` is preserved exactly.

Fixes Obstruction B from `mg-979e-block-and-report.md` §1.b: the
existing `L.restrict S : LayeredDecomposition ↥S` preserves
`K = L.K` but allows empty bands, breaking downstream invariants
(notably `bounded_irreducible_balanced_inScope`'s
`∀ k ∈ [1, K], 1 ≤ bandSize L k`). The compactification removes that
pathology without altering the underlying ground set. -/
def compactify (L : LayeredDecomposition α) (S : Finset α) :
    LayeredDecomposition ↥S where
  K := compactBand L S L.K
  w := L.w
  band z := compactBand L S (L.band z.val)
  band_pos z := by
    apply one_le_compactBand_of_nonEmpty
    · exact L.band_pos z.val
    · exact nonEmptyOnS_band_val L S z
  band_le z := compactBand_mono L S (L.band_le z.val)
  band_size k := by
    classical
    -- Either no z achieves this `k` (empty filter) or some z₀ does, in which
    -- case every w with the same compactBand has the same original band as z₀,
    -- and the new band-k is contained in `(L.restrict S).bandSet (L.band z₀.val)`.
    by_cases hexists :
        ∃ z : ↥S, compactBand L S (L.band z.val) = k
    · obtain ⟨z₀, hz₀⟩ := hexists
      have h_subset :
          (Finset.univ.filter
              (fun w : ↥S => compactBand L S (L.band w.val) = k)) ⊆
            (Finset.univ.filter
              (fun w : ↥S => L.band w.val = L.band z₀.val)) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        have h_eq : compactBand L S (L.band w.val) =
            compactBand L S (L.band z₀.val) := by
          rw [hw, hz₀]
        exact compactBand_inj_on_S L S h_eq
      -- Inject the subtype filter into the ambient filter via Subtype.val.
      have h_card_inj : (Finset.univ.filter
          (fun w : ↥S => L.band w.val = L.band z₀.val)).card ≤ 3 := by
        have hinj : Function.Injective (fun w : ↥S => w.val) :=
          Subtype.val_injective
        have hcard_img :
            ((Finset.univ.filter (fun w : ↥S => L.band w.val = L.band z₀.val)).image
              (fun w : ↥S => w.val)).card =
            (Finset.univ.filter (fun w : ↥S => L.band w.val = L.band z₀.val)).card :=
          Finset.card_image_of_injective _ hinj
        have hsub2 :
            (Finset.univ.filter (fun w : ↥S => L.band w.val = L.band z₀.val)).image
              (fun w : ↥S => w.val) ⊆
            (Finset.univ : Finset α).filter (fun a => L.band a = L.band z₀.val) := by
          intro a ha
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and] at ha
          obtain ⟨w, hw, rfl⟩ := ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hw
        calc (Finset.univ.filter (fun w : ↥S => L.band w.val = L.band z₀.val)).card
            = _ := hcard_img.symm
          _ ≤ _ := Finset.card_le_card hsub2
          _ ≤ 3 := L.band_size _
      exact (Finset.card_le_card h_subset).trans h_card_inj
    · push Not at hexists
      have h_empty :
          (Finset.univ.filter
              (fun w : ↥S => compactBand L S (L.band w.val) = k)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intros z _
        exact hexists z
      rw [h_empty]
      simp
  band_antichain k := by
    classical
    intro a ha b hb hne hle
    simp only [Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at ha hb
    -- Same compactBand value → same original band value.
    have h_eq : compactBand L S (L.band a.val) =
        compactBand L S (L.band b.val) := by
      rw [ha, hb]
    have h_band_eq : L.band a.val = L.band b.val := compactBand_inj_on_S L S h_eq
    have hne_α : a.val ≠ b.val := fun h => hne (Subtype.ext h)
    have hle_α : a.val ≤ b.val := hle
    apply L.band_antichain (L.band a.val)
      (show a.val ∈ ((((Finset.univ : Finset α).filter
          (fun x => L.band x = L.band a.val))) : Set α) by
        simp only [Finset.coe_filter, Finset.mem_univ,
          true_and, Set.mem_setOf_eq])
      (show b.val ∈ ((((Finset.univ : Finset α).filter
          (fun x => L.band x = L.band a.val))) : Set α) by
        simp only [Finset.coe_filter, Finset.mem_univ,
          true_and, Set.mem_setOf_eq]
        exact h_band_eq.symm)
      hne_α hle_α
  forced_lt z w h := by
    -- h : compactBand L S (L.band z.val) + L.w < compactBand L S (L.band w.val).
    -- Need: z.val < w.val (Subtype `<` is the ambient `<`).
    -- Step 1: from compactBand strictness, L.band z.val < L.band w.val.
    have h_lt : L.band z.val < L.band w.val := by
      by_contra h_ge
      push Not at h_ge
      have := compactBand_mono L S h_ge
      omega
    -- Step 2: from compactBand_diff_le, L.band z.val + L.w < L.band w.val.
    have h_diff : L.band z.val + L.w < L.band w.val := by
      have h_bd := compactBand_diff_le L S h_lt.le
      omega
    -- Step 3: apply L.forced_lt and lift back to Subtype.
    exact L.forced_lt z.val w.val h_diff
  cross_band_lt_upward z w h :=
    compactBand_mono L S (L.cross_band_lt_upward z.val w.val h)

/-! ### §4 — Preservation API lemmas -/

@[simp] lemma compactify_K (L : LayeredDecomposition α) (S : Finset α) :
    (L.compactify S).K = compactBand L S L.K := rfl

@[simp] lemma compactify_w (L : LayeredDecomposition α) (S : Finset α) :
    (L.compactify S).w = L.w := rfl

@[simp] lemma compactify_band_apply (L : LayeredDecomposition α) (S : Finset α)
    (z : ↥S) :
    (L.compactify S).band z = compactBand L S (L.band z.val) := rfl

/-- **Depth contracts under compactification**: `K' ≤ K`. -/
lemma compactify_K_le (L : LayeredDecomposition α) (S : Finset α) :
    (L.compactify S).K ≤ L.K := by
  change compactBand L S L.K ≤ L.K
  unfold compactBand
  calc ((Finset.Icc 1 L.K).filter (fun i => NonEmptyOnS L S i)).card
      ≤ (Finset.Icc 1 L.K).card := Finset.card_filter_le _ _
    _ = L.K + 1 - 1 := Nat.card_Icc _ _
    _ = L.K := by omega

/-- **Width is preserved exactly**: `w' = w`. The compactification does not
attempt to tighten the interaction width — tightening is sub-poset-specific
information that the constructor does not consume. -/
@[simp] lemma compactify_w_eq (L : LayeredDecomposition α) (S : Finset α) :
    (L.compactify S).w = L.w := rfl

/-- Width inequality form (often the convenient shape for compositional ports). -/
lemma compactify_w_le (L : LayeredDecomposition α) (S : Finset α) :
    (L.compactify S).w ≤ L.w := le_of_eq (compactify_w_eq L S)

/-- **Band-index domination**: each new band index is bounded by the
original band of the underlying `α`-element. -/
lemma compactify_band_le_orig (L : LayeredDecomposition α) (S : Finset α)
    (z : ↥S) :
    (L.compactify S).band z ≤ L.band z.val := by
  change compactBand L S (L.band z.val) ≤ L.band z.val
  unfold compactBand
  calc ((Finset.Icc 1 (L.band z.val)).filter
          (fun i => NonEmptyOnS L S i)).card
      ≤ (Finset.Icc 1 (L.band z.val)).card := Finset.card_filter_le _ _
    _ = L.band z.val + 1 - 1 := Nat.card_Icc _ _
    _ = L.band z.val := by omega

/-- **Depth-cap propagation**: if `L.K ≤ N`, then `(L.compactify S).K ≤ N`. -/
lemma compactify_K_le_of_K_le (L : LayeredDecomposition α) (S : Finset α)
    {N : ℕ} (hN : L.K ≤ N) : (L.compactify S).K ≤ N :=
  (compactify_K_le L S).trans hN

/-- **Cardinality-cap propagation**: if `Fintype.card α ≤ M`, then any
`Finset` `S ⊆ α` has `Fintype.card ↥S ≤ M`. Recorded as a building block
for threading the Candidate A'' size cap `|α| ≤ 6w + 6` of
`mg-979e-block-and-report.md` §1.a through `compactify`. -/
lemma compactify_card_le_of_card_le (S : Finset α) {M : ℕ}
    (hM : Fintype.card α ≤ M) : Fintype.card ↥S ≤ M :=
  (Fintype.card_subtype_le _).trans hM

/-- **Injectivity propagation**: if the original band map `L.band` is
injective on `α`, then the compactified band map is injective on `↥S`.

This makes the Candidate A''-style `Function.Injective LB.band` cap
(`mg-979e-block-and-report.md` §1.b) survive sub-poset descent through
`compactify`. -/
lemma compactify_band_injective_of_injective
    (L : LayeredDecomposition α) (S : Finset α)
    (hInj : Function.Injective L.band) :
    Function.Injective (L.compactify S).band := by
  intro z w h
  -- h : compactBand L S (L.band z.val) = compactBand L S (L.band w.val)
  --     (definitionally — `(L.compactify S).band` is `compactBand ∘ ...`)
  have h' : compactBand L S (L.band z.val) =
      compactBand L S (L.band w.val) := h
  exact Subtype.ext (hInj (compactBand_inj_on_S L S h'))

/-- **Band relabelling structure**: two elements of `↥S` lie in the same
new band iff they lie in the same original band. The compactification is
a *relabelling*, not a coarsening — equivalence classes of the new band
map coincide with non-empty original-band classes restricted to `S`. -/
lemma compactify_band_eq_iff_band_eq (L : LayeredDecomposition α) (S : Finset α)
    (z w : ↥S) :
    (L.compactify S).band z = (L.compactify S).band w ↔
      L.band z.val = L.band w.val := by
  constructor
  · intro h
    have h' : compactBand L S (L.band z.val) =
        compactBand L S (L.band w.val) := h
    exact compactBand_inj_on_S L S h'
  · intro h
    change compactBand L S (L.band z.val) = compactBand L S (L.band w.val)
    rw [h]

end LayeredDecomposition

end Step8
end OneThird
