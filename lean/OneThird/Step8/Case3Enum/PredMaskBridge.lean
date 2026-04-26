/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BoundedIrreducibleBalanced
import OneThird.Step8.Case3Enum.IrreducibleBridge

/-!
# Step 8 — A5-G3c: `enumPredAtMaskOf = predMaskOf` construction-equivalence
(`mg-1906`, partial; finished in `mg-1906-followup`)

## Goal

Prove the construction-equivalence used by F5a's bridge:

```
Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L) = predMaskOf L
```

This equivalence identifies the imperative pre-warshall + warshall
pipeline of `enumPredAtMaskOf` with the abstract `predMaskOf L` —
provided `L : LayeredDecomposition α` has the `cross_band_lt_upward`
field (added in `mg-53ce` / A5-G2 path 1), which makes
`predMaskOf L` upper-triangular bit-wise.

## Scope of this commit (`mg-1906`)

The original A5-G3c estimate (~200-300 LOC) anticipated unrolling the
two `for`-loops of `enumPredPreWarshallOf` and applying
`predMaskOf_warshall`. In tree, the construction-equivalence
*additionally* requires unrolling `enumPartition`'s four-deep nested
`for`-loops to characterize membership in `enumForcedUVOf` and
`enumFreeUVOf` as position predicates — that part was unanticipated
and adds ~150-300 more LOC.

Per pc-1906's mayor consult (2026-04-26), this commit ships the
foundational infrastructure that the followup builds on:

* §1 — `enumNOf (bandSizes L) = Fintype.card α`.
* §2 — Band-major positional consequences of `cross_band_lt_upward`:
  if bit `u` of `predMaskOf L [v]` is set, then `band (e.symm u) <
  band (e.symm v)` and so `u.val < v.val`. These will drive the
  upper-triangle case analysis in the followup, which uses them to
  identify `predMaskOf` bits with cross-band Fin pairs.
* §3 — `addEdgesList`: a recursive form of folding edge-additions
  over a list of pairs, with size, monotonicity, upper-bound, and
  lower-bound bit-set lemmas. Used to express the forced-edge first
  `for`-loop of `enumPredPreWarshallOf`.
* §4 — `maskedFreeBody`: the per-`k` body of the masked-free
  `for`-loop, with size, monotonicity, upper-bound, and lower-bound
  bit-set lemmas. Used to express the second `for`-loop of
  `enumPredPreWarshallOf`.

The remaining pieces are deferred to **`mg-1906-followup`**:

* §5 — Imperative→functional reduction of the two `for`-loops in
  `enumPredPreWarshallOf` to an explicit `addEdgesList` + `List.foldl`
  form. Pending: the body wrapper definitions need to match the
  `let mut pred := …; for … do pred := …` desugaring exactly, mirroring
  `BalancedLift.lean`'s `warshallOuterBody` pattern.
* §6 — Bit characterization of `enumPredPreWarshallOf` (combining §3,
  §4, and §5).
* §7 — Membership characterization of `enumForcedUVOf` /
  `enumFreeUVOf` as position predicates (requires `enumPartition`
  four-loop unrolling — natural seam between the original ~250 LOC
  estimate and the additional ~250 LOC needed).
* §8 — The final equality theorem, by combining §6 with the
  membership characterization plus `predMaskOf_warshall`.

## References

* `docs/a5-g2-status.md` — the A5-G2 diagnosis and resolution.
* `dfaf737` (mg-53ce / A5-G2 path 1) — `cross_band_lt_upward` field.
* `BalancedLift.lean §4` — `getD_set!_eq` `set!`/`getD` helper
  (template; mirrored as `getD_set!_eq_aux` below).
-/

namespace OneThird.Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### §1 — `enumNOf (bandSizes L) = Fintype.card α` -/

/-- The total ground set size for a layered decomposition's band-size
list, computed by `enumNOf`, equals `Fintype.card α`. -/
lemma enumNOf_bandSizes_eq_card (L : LayeredDecomposition α) :
    Case3Enum.enumNOf (bandSizes L) = Fintype.card α := by
  unfold Case3Enum.enumNOf
  rw [show (bandSizes L).length = L.K from bandSizes_length L,
    offsetsOf_bandSizes_getD L L.K (le_refl _), bandOffset_K]

/-! ### §2 — Band-major positional consequences of upper-triangularity -/

/-- Two distinct elements in the same band are incomparable
(`band_antichain`). -/
private lemma not_lt_of_band_eq (L : LayeredDecomposition α) {x y : α}
    (hne : x ≠ y) (heq : L.band x = L.band y) : ¬ (x < y) := by
  classical
  intro hlt
  have hA := L.band_antichain (L.band y)
  have hx_mem :
      x ∈ ((((Finset.univ : Finset α).filter
              (fun a => L.band a = L.band y)) : Set α)) := by
    simp [heq]
  have hy_mem :
      y ∈ ((((Finset.univ : Finset α).filter
              (fun a => L.band a = L.band y)) : Set α)) := by
    simp
  exact hA hx_mem hy_mem hne hlt.le

/-- If bit `u` of `predMaskOf L [v]` is set, then `band (e.symm u) <
band (e.symm v)`, where `e = bandMajorEquiv L`. Uses
`cross_band_lt_upward` (gives `≤`) plus `band_antichain` (excludes
strict relations within the same band). -/
lemma bandMajorEquiv_band_lt_of_predMask_bit
    (L : LayeredDecomposition α) (u v : Fin (Fintype.card α))
    (h : Nat.testBit ((predMaskOf L).getD v.val 0) u.val = true) :
    L.band ((bandMajorEquiv L).symm u) < L.band ((bandMajorEquiv L).symm v) := by
  classical
  rw [← testBit'_eq_testBit] at h
  have hlt : (bandMajorEquiv L).symm u < (bandMajorEquiv L).symm v :=
    (testBit'_predMaskOf L u v).mp h
  have hle :
      L.band ((bandMajorEquiv L).symm u) ≤ L.band ((bandMajorEquiv L).symm v) :=
    L.cross_band_lt_upward _ _ hlt
  rcases lt_or_eq_of_le hle with hLt | hEq
  · exact hLt
  · exact absurd hlt (not_lt_of_band_eq L (ne_of_lt hlt) hEq)

/-- If bit `u` of `predMaskOf L [v]` is set, then `u.val < v.val`
(upper-triangularity in band-major order). -/
lemma bandMajor_pos_lt_of_predMask_bit
    (L : LayeredDecomposition α) (u v : Fin (Fintype.card α))
    (h : Nat.testBit ((predMaskOf L).getD v.val 0) u.val = true) :
    u.val < v.val := by
  classical
  have hband := bandMajorEquiv_band_lt_of_predMask_bit L u v h
  have hpos_v : 1 ≤ L.band ((bandMajorEquiv L).symm v) := L.band_pos _
  have hcalc1 :
      (bandMajorEquiv L ((bandMajorEquiv L).symm u)).val < bandOffset L
        (L.band ((bandMajorEquiv L).symm u)) :=
    bandMajorEquiv_apply_val_lt L _
  have hu_eq : (bandMajorEquiv L ((bandMajorEquiv L).symm u)).val = u.val := by
    rw [Equiv.apply_symm_apply]
  rw [hu_eq] at hcalc1
  have hcalc2 :
      bandOffset L (L.band ((bandMajorEquiv L).symm u)) ≤
        bandOffset L (L.band ((bandMajorEquiv L).symm v) - 1) := by
    apply bandOffset_mono; omega
  have hcalc3 :
      bandOffset L (L.band ((bandMajorEquiv L).symm v) - 1) ≤
        (bandMajorEquiv L ((bandMajorEquiv L).symm v)).val :=
    bandOffset_le_bandMajorEquiv_apply_val L _
  have hv_eq : (bandMajorEquiv L ((bandMajorEquiv L).symm v)).val = v.val := by
    rw [Equiv.apply_symm_apply]
  rw [hv_eq] at hcalc3
  omega

end OneThird.Step8

/-! ### §3 — Edge-addition primitives for the forced-edge `for`-loop -/

namespace OneThird.Step8.Case3Enum

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- Auxiliary `set!`/`getD` characterization (mirror of
`BalancedLift.getD_set!_eq`): `(out.set! v w).getD v' 0` equals `w`
when `v' = v` and `v` is in-bounds, otherwise `out.getD v' 0`. -/
private lemma getD_set!_eq_aux (out : Array Nat) (v : Nat) (w : Nat) (v' : Nat) :
    (out.set! v w).getD v' 0 =
      if v' = v ∧ v < out.size then w else out.getD v' 0 := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hv' : v' = v
  · subst hv'
    by_cases hvsize : v' < out.size
    · simp only [Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt hvsize, Option.getD_some,
        and_self, hvsize, ↓reduceIte]
    · rw [Array.setIfInBounds_eq_of_size_le (Nat.not_lt.mp hvsize)]
      simp [hvsize]
  · have hne : v' ≠ v := hv'
    have hne' : v ≠ v' := fun h => hne h.symm
    simp only [Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hne']
    rw [if_neg]
    intro ⟨h1, _⟩; exact hne h1

/-- Effect on `pred[j]`'s bit `i` of OR-ing `bit u` into `pred[v]`,
when `v < pred.size`. -/
lemma testBit_setOrBit (pred : Array Nat) (u v : Nat)
    (hv : v < pred.size) (i j : Nat) :
    Nat.testBit ((pred.set! v (pred.getD v 0 ||| bit u)).getD j 0) i =
      (Nat.testBit (pred.getD j 0) i ||
        (decide (j = v) && decide (i = u))) := by
  rw [getD_set!_eq_aux]
  by_cases hjv : j = v
  · subst hjv
    rw [if_pos ⟨rfl, hv⟩, Nat.testBit_or,
      show bit u = 2 ^ u from by simp [bit, Nat.one_shiftLeft]]
    rw [Nat.testBit_two_pow]
    rcases Decidable.eq_or_ne u i with rfl | hne
    · simp
    · have h1 : decide (u = i) = false := decide_eq_false hne
      have h2 : decide (i = u) = false := decide_eq_false (fun h => hne h.symm)
      simp [h1, h2]
  · rw [if_neg]
    · simp [hjv]
    · intro ⟨h, _⟩; exact hjv h

/-- `set!` is a no-op on `getD` when the target index is out-of-bounds. -/
lemma getD_set!_of_size_le (pred : Array Nat) (v x : Nat)
    (hv : pred.size ≤ v) (j : Nat) :
    (pred.set! v x).getD j 0 = pred.getD j 0 := by
  rw [getD_set!_eq_aux]
  rw [if_neg]
  intro ⟨_, hlt⟩; exact absurd hlt (Nat.not_lt.mpr hv)

/-- Edge-fold: starting from `pred`, fold `(u, v) ↦ set! v (pred[v] ||| bit u)`
over a list of pairs. -/
def addEdgesList (pairs : List (Nat × Nat)) (pred : Array Nat) :
    Array Nat :=
  pairs.foldl (fun pred uv =>
    pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)) pred

@[simp] lemma addEdgesList_nil (pred : Array Nat) :
    addEdgesList [] pred = pred := rfl

@[simp] lemma addEdgesList_cons (uv : Nat × Nat)
    (rest : List (Nat × Nat)) (pred : Array Nat) :
    addEdgesList (uv :: rest) pred =
      addEdgesList rest
        (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)) := rfl

lemma addEdgesList_size (pairs : List (Nat × Nat)) (pred : Array Nat) :
    (addEdgesList pairs pred).size = pred.size := by
  induction pairs generalizing pred with
  | nil => rfl
  | cons uv rest ih =>
    rw [addEdgesList_cons, ih]; simp

/-- Bit-monotonicity of `addEdgesList`. -/
lemma addEdgesList_bit_mono {pairs : List (Nat × Nat)} {pred : Array Nat}
    {i j : Nat} (h : Nat.testBit (pred.getD j 0) i = true) :
    Nat.testBit ((addEdgesList pairs pred).getD j 0) i = true := by
  induction pairs generalizing pred with
  | nil => rw [addEdgesList_nil]; exact h
  | cons uv rest ih =>
    rw [addEdgesList_cons]
    apply ih
    by_cases hv : uv.2 < pred.size
    · rw [testBit_setOrBit pred uv.1 uv.2 hv i j]; rw [h]; rfl
    · rw [getD_set!_of_size_le pred uv.2 _ (Nat.le_of_not_lt hv) j]
      exact h

/-- **Upper bound**: a bit set in the result of `addEdgesList` is
either set in the seed or comes from an edge in `pairs` (with the
required bound `j < pred.size`). -/
lemma testBit_addEdgesList_imp (pairs : List (Nat × Nat))
    (pred : Array Nat) (i j : Nat)
    (h : Nat.testBit ((addEdgesList pairs pred).getD j 0) i = true) :
    Nat.testBit (pred.getD j 0) i = true ∨
      (j < pred.size ∧ (i, j) ∈ pairs) := by
  induction pairs generalizing pred with
  | nil =>
    rw [addEdgesList_nil] at h; exact Or.inl h
  | cons uv rest ih =>
    rw [addEdgesList_cons] at h
    rcases ih (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)) h with hb | ⟨hjs, hin⟩
    · by_cases hv : uv.2 < pred.size
      · rw [testBit_setOrBit pred uv.1 uv.2 hv i j] at hb
        rcases Bool.or_eq_true_iff.mp hb with hb1 | hb2
        · exact Or.inl hb1
        · rw [Bool.and_eq_true] at hb2
          have hj_eq : j = uv.2 := of_decide_eq_true hb2.1
          have hi_eq : i = uv.1 := of_decide_eq_true hb2.2
          subst hj_eq; subst hi_eq
          exact Or.inr ⟨hv, List.mem_cons_self⟩
      · rw [getD_set!_of_size_le pred uv.2 _ (Nat.le_of_not_lt hv) j] at hb
        exact Or.inl hb
    · have hsize : (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)).size = pred.size := by simp
      rw [hsize] at hjs
      exact Or.inr ⟨hjs, List.mem_cons_of_mem _ hin⟩

/-- **Lower bound**: if a pair `(i, j)` is in `pairs` and `j < n`
(where the seed has size `n`), then bit `i` of position `j` in the
result is set. -/
lemma testBit_addEdgesList_of_mem (pairs : List (Nat × Nat))
    (pred : Array Nat) (i j : Nat) (hjs : j < pred.size)
    (hin : (i, j) ∈ pairs) :
    Nat.testBit ((addEdgesList pairs pred).getD j 0) i = true := by
  induction pairs generalizing pred with
  | nil => exact absurd hin List.not_mem_nil
  | cons uv rest ih =>
    rw [addEdgesList_cons]
    rcases List.mem_cons.mp hin with heq_uv | hmem
    · -- (i, j) = uv
      have hi_eq : i = uv.1 := congrArg Prod.fst heq_uv
      have hj_eq : j = uv.2 := congrArg Prod.snd heq_uv
      have hv : uv.2 < pred.size := hj_eq ▸ hjs
      apply addEdgesList_bit_mono
      rw [testBit_setOrBit pred uv.1 uv.2 hv i j]
      simp [hj_eq, hi_eq]
    · have hjs2 : j < (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)).size := by
        simpa using hjs
      exact ih (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)) hjs2 hmem

/-! ### §4 — Per-`k` body of the masked-free `for`-loop -/

/-- The per-`k` body of the masked-free for-loop: if bit `k` of the
mask is set, OR `bit (freeUV[k].1)` into `pred[freeUV[k].2]`;
otherwise leave `pred` unchanged. -/
def maskedFreeBody (mask : Nat) (freeUV : Array (Nat × Nat))
    (k : Nat) (pred : Array Nat) : Array Nat :=
  if testBit' mask k then
    pred.set! (freeUV.getD k (0, 0)).2
      (pred.getD (freeUV.getD k (0, 0)).2 0 ||| bit (freeUV.getD k (0, 0)).1)
  else pred

lemma maskedFreeBody_size (mask : Nat) (freeUV : Array (Nat × Nat))
    (k : Nat) (pred : Array Nat) :
    (maskedFreeBody mask freeUV k pred).size = pred.size := by
  unfold maskedFreeBody; split_ifs <;> simp

lemma foldl_maskedFreeBody_size (mask : Nat) (freeUV : Array (Nat × Nat))
    (l : List Nat) (pred : Array Nat) :
    (l.foldl (fun pred k => maskedFreeBody mask freeUV k pred) pred).size =
      pred.size := by
  induction l generalizing pred with
  | nil => rfl
  | cons k rest ih => rw [List.foldl_cons, ih, maskedFreeBody_size]

/-- Bit-monotonicity of the masked-free fold. -/
lemma maskedFreeBody_foldl_bit_mono (mask : Nat) (freeUV : Array (Nat × Nat))
    {l : List Nat} {pred : Array Nat} {i j : Nat}
    (h : Nat.testBit (pred.getD j 0) i = true) :
    Nat.testBit
        ((l.foldl (fun pred k => maskedFreeBody mask freeUV k pred) pred).getD
          j 0) i = true := by
  induction l generalizing pred with
  | nil => rw [List.foldl_nil]; exact h
  | cons k rest ih =>
    rw [List.foldl_cons]
    apply ih
    by_cases hbit : testBit' mask k
    · have hbody :
          maskedFreeBody mask freeUV k pred =
            pred.set! (freeUV.getD k (0, 0)).2
              (pred.getD (freeUV.getD k (0, 0)).2 0 |||
                bit (freeUV.getD k (0, 0)).1) := by
        unfold maskedFreeBody; rw [if_pos hbit]
      rw [hbody]
      by_cases hv : (freeUV.getD k (0, 0)).2 < pred.size
      · rw [testBit_setOrBit pred (freeUV.getD k (0, 0)).1 _ hv i j]
        rw [h]; rfl
      · rw [getD_set!_of_size_le pred (freeUV.getD k (0, 0)).2 _
          (Nat.le_of_not_lt hv) j]
        exact h
    · have hbody : maskedFreeBody mask freeUV k pred = pred := by
        unfold maskedFreeBody; rw [if_neg hbit]
      rw [hbody]; exact h

/-- **Upper bound**: a bit set in the result of `maskedFreeBody` foldl
is either set in the seed, or comes from a `k ∈ l` with `mask`'s
bit `k` set and `freeUV[k] = (i, j)`. -/
lemma testBit_foldl_maskedFreeBody_imp (mask : Nat)
    (freeUV : Array (Nat × Nat)) (l : List Nat) (pred : Array Nat) (i j : Nat)
    (h : Nat.testBit
        ((l.foldl (fun pred k => maskedFreeBody mask freeUV k pred) pred).getD
          j 0) i = true) :
    Nat.testBit (pred.getD j 0) i = true ∨
      (j < pred.size ∧ ∃ k ∈ l, testBit' mask k = true ∧
        freeUV.getD k (0, 0) = (i, j)) := by
  induction l generalizing pred with
  | nil => rw [List.foldl_nil] at h; exact Or.inl h
  | cons k rest ih =>
    rw [List.foldl_cons] at h
    rcases ih (maskedFreeBody mask freeUV k pred) h with hb |
        ⟨hjs, k', hk'_mem, hbit', heq'⟩
    · by_cases hbit : testBit' mask k
      · have hbody :
            maskedFreeBody mask freeUV k pred =
              pred.set! (freeUV.getD k (0, 0)).2
                (pred.getD (freeUV.getD k (0, 0)).2 0 |||
                  bit (freeUV.getD k (0, 0)).1) := by
          unfold maskedFreeBody; rw [if_pos hbit]
        rw [hbody] at hb
        by_cases hv : (freeUV.getD k (0, 0)).2 < pred.size
        · rw [testBit_setOrBit pred (freeUV.getD k (0, 0)).1 _ hv i j] at hb
          rcases Bool.or_eq_true_iff.mp hb with hb1 | hb2
          · exact Or.inl hb1
          · rw [Bool.and_eq_true] at hb2
            have hj_eq : j = (freeUV.getD k (0, 0)).2 := of_decide_eq_true hb2.1
            have hi_eq : i = (freeUV.getD k (0, 0)).1 := of_decide_eq_true hb2.2
            refine Or.inr ⟨by rw [hj_eq]; exact hv, k, ?_, hbit, ?_⟩
            · exact List.mem_cons_self
            · ext
              · exact hi_eq.symm
              · exact hj_eq.symm
        · rw [getD_set!_of_size_le pred (freeUV.getD k (0, 0)).2 _
            (Nat.le_of_not_lt hv) j] at hb
          exact Or.inl hb
      · have hbody : maskedFreeBody mask freeUV k pred = pred := by
          unfold maskedFreeBody; rw [if_neg hbit]
        rw [hbody] at hb
        exact Or.inl hb
    · have hsize : (maskedFreeBody mask freeUV k pred).size = pred.size :=
        maskedFreeBody_size _ _ _ _
      rw [hsize] at hjs
      exact Or.inr ⟨hjs, k', List.mem_cons_of_mem _ hk'_mem, hbit', heq'⟩

/-- **Lower bound**: if some `k ∈ l` has the mask bit set and
`freeUV[k] = (i, j)` and `j < pred.size`, then the bit at `(i, j)`
is set in the result. -/
lemma testBit_foldl_maskedFreeBody_of_mem (mask : Nat)
    (freeUV : Array (Nat × Nat)) (l : List Nat) (pred : Array Nat) (i j : Nat)
    (hjs : j < pred.size)
    (h : ∃ k ∈ l, testBit' mask k = true ∧
      freeUV.getD k (0, 0) = (i, j)) :
    Nat.testBit
        ((l.foldl (fun pred k => maskedFreeBody mask freeUV k pred) pred).getD
          j 0) i = true := by
  obtain ⟨k, hk_mem, hbit, heq⟩ := h
  induction l generalizing pred with
  | nil => exact absurd hk_mem List.not_mem_nil
  | cons k' rest ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hk_mem with rfl | hmem
    · have hbody :
          maskedFreeBody mask freeUV k pred =
            pred.set! (freeUV.getD k (0, 0)).2
              (pred.getD (freeUV.getD k (0, 0)).2 0 |||
                bit (freeUV.getD k (0, 0)).1) := by
        unfold maskedFreeBody; rw [if_pos hbit]
      rw [hbody]
      have hj_eq : (freeUV.getD k (0, 0)).2 = j := by rw [heq]
      have hi_eq : (freeUV.getD k (0, 0)).1 = i := by rw [heq]
      have hv : (freeUV.getD k (0, 0)).2 < pred.size := by rw [hj_eq]; exact hjs
      apply maskedFreeBody_foldl_bit_mono
      rw [testBit_setOrBit pred (freeUV.getD k (0, 0)).1 _ hv i j]
      rw [hj_eq, hi_eq]; simp
    · have hsize : (maskedFreeBody mask freeUV k' pred).size = pred.size :=
        maskedFreeBody_size _ _ _ _
      have hjs2 : j < (maskedFreeBody mask freeUV k' pred).size := by
        rw [hsize]; exact hjs
      exact ih (maskedFreeBody mask freeUV k' pred) hjs2 hmem

end OneThird.Step8.Case3Enum
