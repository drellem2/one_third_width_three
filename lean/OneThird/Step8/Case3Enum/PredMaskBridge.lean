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

/-! ### §5 — Imperative→functional reduction of `enumPredPreWarshallOf`

The two `for`-loops of `enumPredPreWarshallOf` reduce, in `Id`, to an
explicit `addEdgesList` (forced-edge phase) + `List.foldl` of
`maskedFreeBody` (masked-free phase). Mirrors the pattern of
`BalancedLift.warshall_imperative_eq`. -/

/-- `forIn` over the forced-edge body reduces to `addEdgesList`. -/
private lemma forIn_forced_eq_addEdgesList (forcedUV : List (Nat × Nat))
    (pred : Array Nat) :
    (forIn (m := Id) forcedUV pred (fun uv pred =>
      (do pure PUnit.unit
          pure (ForInStep.yield
            (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1))) : Id _))) =
      addEdgesList forcedUV pred := by
  induction forcedUV generalizing pred with
  | nil => rfl
  | cons uv rest ih =>
    rw [List.forIn_cons]
    show (forIn (m := Id) rest
        (pred.set! uv.2 (pred.getD uv.2 0 ||| bit uv.1)) _ : Id _) = _
    rw [ih, addEdgesList_cons]

/-- A reformulation of `maskedFreeBody` using the `dite` form of
`Array.getD`, matching the do-elaboration of the for-loop. -/
private lemma maskedFreeBody_dite_eq (mask : Nat)
    (freeUV : Array (Nat × Nat)) (k : Nat) (pred : Array Nat) :
    (if testBit' mask k then
      pred.set!
        (if h : k < freeUV.size then freeUV.getInternal k h else (0, 0)).2
        (pred.getD
          (if h : k < freeUV.size then freeUV.getInternal k h else (0, 0)).2 0 |||
          bit
            (if h : k < freeUV.size then freeUV.getInternal k h else (0, 0)).1)
      else pred) = maskedFreeBody mask freeUV k pred := by
  unfold maskedFreeBody
  rfl

/-- `forIn` over the masked-free body reduces to `foldl maskedFreeBody`. -/
private lemma forIn_free_eq_foldl_maskedFreeBody (mask : Nat)
    (freeUV : Array (Nat × Nat)) (l : List Nat) (pred : Array Nat) :
    (forIn (m := Id) l pred (fun k pred =>
      (if testBit' mask k then
        (do pure PUnit.unit
            pure (ForInStep.yield
              (pred.set!
                (if h : k < freeUV.size then freeUV.getInternal k h
                  else (0, 0)).2
                (pred.getD
                    (if h : k < freeUV.size then freeUV.getInternal k h
                      else (0, 0)).2 0 |||
                  bit (if h : k < freeUV.size then freeUV.getInternal k h
                    else (0, 0)).1))) : Id _)
      else
        (do pure PUnit.unit
            pure (ForInStep.yield pred) : Id _)))) =
      l.foldl (fun pred k => maskedFreeBody mask freeUV k pred) pred := by
  induction l generalizing pred with
  | nil => rfl
  | cons k rest ih =>
    rw [List.forIn_cons, List.foldl_cons, ← maskedFreeBody_dite_eq mask freeUV k pred]
    by_cases hbit : testBit' mask k
    · simp only [hbit, ↓reduceIte]
      show (forIn (m := Id) rest _ _ : Id _) = _
      exact ih _
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
      show (forIn (m := Id) rest _ _ : Id _) = _
      exact ih _

/-- **Imperative→functional reduction of `enumPredPreWarshallOf`.**

The imperative two-`for`-loop construction equals the explicit
functional form: starting from `Array.replicate (enumNOf bs) 0`,
apply `addEdgesList forcedUV.toList`, then `foldl maskedFreeBody`
over `[0, nfree)`. -/
lemma enumPredPreWarshallOf_eq (w : Nat) (bs : List Nat) (mask : Nat) :
    enumPredPreWarshallOf w bs mask =
      (List.range' 0 (enumFreeUVOf w bs).size).foldl
        (fun pred k => maskedFreeBody mask (enumFreeUVOf w bs) k pred)
        (addEdgesList (enumForcedUVOf w bs).toList
          (Array.replicate (enumNOf bs) 0)) := by
  unfold enumPredPreWarshallOf
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← Array.forIn_toList]
  rw [forIn_forced_eq_addEdgesList]
  exact forIn_free_eq_foldl_maskedFreeBody mask (enumFreeUVOf w bs) _ _

/-! ### §6 — Bit characterization of `enumPredPreWarshallOf` -/

/-- The all-zeros replicate has every `getD` equal to `0`. -/
private lemma getD_replicate_zero (n j : Nat) :
    (Array.replicate n (0 : Nat)).getD j 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?]
  by_cases hj : j < (Array.replicate n (0 : Nat)).size
  · rw [Array.getElem?_eq_getElem hj]; simp
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hj)]; rfl

/-- **Upper bound**: a bit set in `enumPredPreWarshallOf` is either
in the forced-edge list or comes from a masked free-edge slot. -/
lemma testBit_enumPredPreWarshallOf_imp (w : Nat) (bs : List Nat)
    (mask : Nat) (i j : Nat)
    (h : Nat.testBit ((enumPredPreWarshallOf w bs mask).getD j 0) i = true) :
    j < enumNOf bs ∧
      ((i, j) ∈ (enumForcedUVOf w bs).toList ∨
        ∃ k, k < (enumFreeUVOf w bs).size ∧
          testBit' mask k = true ∧
          (enumFreeUVOf w bs).getD k (0, 0) = (i, j)) := by
  rw [enumPredPreWarshallOf_eq] at h
  set seed : Array Nat := addEdgesList (enumForcedUVOf w bs).toList
    (Array.replicate (enumNOf bs) 0) with hseed_def
  have hseed_size : seed.size = enumNOf bs := by
    rw [hseed_def, addEdgesList_size, Array.size_replicate]
  -- Combine §4 upper bound with §3 upper bound.
  rcases testBit_foldl_maskedFreeBody_imp mask (enumFreeUVOf w bs)
      (List.range' 0 (enumFreeUVOf w bs).size) seed i j h with hb_seed |
      ⟨hjs2, k', hk'_mem, hbit', heq'⟩
  · -- Bit was already set in the seed.
    rcases testBit_addEdgesList_imp (enumForcedUVOf w bs).toList
        (Array.replicate (enumNOf bs) 0) i j hb_seed with hb_zero | ⟨hjs0, hin⟩
    · -- Bit is set in the all-zero replicate — impossible.
      exfalso
      rw [getD_replicate_zero, Nat.zero_testBit] at hb_zero
      exact Bool.false_ne_true hb_zero
    · refine ⟨?_, Or.inl hin⟩
      rw [Array.size_replicate] at hjs0; exact hjs0
  · -- Bit comes from a masked free-edge slot.
    have hjs_n : j < enumNOf bs := by rw [hseed_size] at hjs2; exact hjs2
    refine ⟨hjs_n, Or.inr ⟨k', ?_, hbit', heq'⟩⟩
    rw [List.mem_range'_1] at hk'_mem; omega

/-- **Lower bound (forced)**: forced-edge pairs always set the bit. -/
lemma testBit_enumPredPreWarshallOf_of_forced (w : Nat) (bs : List Nat)
    (mask : Nat) {i j : Nat}
    (hin : (i, j) ∈ (enumForcedUVOf w bs).toList)
    (hjs : j < enumNOf bs) :
    Nat.testBit ((enumPredPreWarshallOf w bs mask).getD j 0) i = true := by
  rw [enumPredPreWarshallOf_eq]
  apply maskedFreeBody_foldl_bit_mono
  apply testBit_addEdgesList_of_mem
  · rw [Array.size_replicate]; exact hjs
  · exact hin

/-- **Lower bound (free)**: a masked free-edge slot also sets the
bit. -/
lemma testBit_enumPredPreWarshallOf_of_free (w : Nat) (bs : List Nat)
    (mask : Nat) {i j : Nat}
    (h : ∃ k, k < (enumFreeUVOf w bs).size ∧
      testBit' mask k = true ∧
      (enumFreeUVOf w bs).getD k (0, 0) = (i, j))
    (hjs : j < enumNOf bs) :
    Nat.testBit ((enumPredPreWarshallOf w bs mask).getD j 0) i = true := by
  rw [enumPredPreWarshallOf_eq]
  obtain ⟨k, hk_lt, hbit, heq⟩ := h
  set seed : Array Nat := addEdgesList (enumForcedUVOf w bs).toList
    (Array.replicate (enumNOf bs) 0) with hseed_def
  have hseed_size : seed.size = enumNOf bs := by
    rw [hseed_def, addEdgesList_size, Array.size_replicate]
  apply testBit_foldl_maskedFreeBody_of_mem
  · rw [hseed_size]; exact hjs
  · refine ⟨k, ?_, hbit, heq⟩
    rw [List.mem_range'_1]; omega

/-! ### §7 — Membership characterization of `enumForcedUVOf` / `enumFreeUVOf`

Unrolls `enumPartition`'s four-deep nested `for`-loops to characterize
membership in `enumForcedUVOf` / `enumFreeUVOf` as position
predicates: a pair `(a, b)` is in the forced (resp. free) array iff
there exist band indices `i < j < bs.length` with `j - i > w`
(resp. `≤ w`), `a` lies in band-`i+1`'s range, and `b` lies in
band-`j+1`'s range. -/

/-- Membership predicate for the forced output: there exist band
indices `i, j` with `i < j < K = bs.length`, `j - i > w`, and
`(a, b)` falls in the band-`i+1` × band-`j+1` rectangle. -/
def IsForcedPair (w : Nat) (bs : List Nat) (a b : Nat) : Prop :=
  ∃ i j, i < j ∧ j < bs.length ∧ j - i > w ∧
    (offsetsOf bs).getD i 0 ≤ a ∧ a < (offsetsOf bs).getD (i + 1) 0 ∧
    (offsetsOf bs).getD j 0 ≤ b ∧ b < (offsetsOf bs).getD (j + 1) 0

/-- Membership predicate for the free output: as above with
`j - i ≤ w` instead. -/
def IsFreePair (w : Nat) (bs : List Nat) (a b : Nat) : Prop :=
  ∃ i j, i < j ∧ j < bs.length ∧ j - i ≤ w ∧
    (offsetsOf bs).getD i 0 ≤ a ∧ a < (offsetsOf bs).getD (i + 1) 0 ∧
    (offsetsOf bs).getD j 0 ≤ b ∧ b < (offsetsOf bs).getD (j + 1) 0

/-- "Push the rectangle `[offI, offI1) × [offJ, offJ1)` of pairs into
the array, in `(a, b)` lexicographic order." -/
private def pushRect (offI offI1 offJ offJ1 : Nat) (out : Array (Nat × Nat)) :
    Array (Nat × Nat) :=
  (List.range' offI (offI1 - offI)).foldl (fun out a =>
    (List.range' offJ (offJ1 - offJ)).foldl (fun out b => out.push (a, b)) out) out

/-- Membership in the foldl of `push (a, b)` over `b ∈ l`. -/
private lemma mem_foldl_push_b (a : Nat) (l : List Nat)
    (out : Array (Nat × Nat)) (c d : Nat) :
    (c, d) ∈ (l.foldl (fun out b => out.push (a, b)) out).toList ↔
      (c, d) ∈ out.toList ∨ (c = a ∧ d ∈ l) := by
  induction l generalizing out with
  | nil => simp
  | cons b rest ih =>
    rw [List.foldl_cons, ih, Array.toList_push, List.mem_append, List.mem_singleton,
      Prod.mk.injEq, List.mem_cons]
    tauto

/-- Auxiliary helper: membership in the result of foldl over the
outer a-list, with each step doing an inner b-push-loop. -/
private lemma mem_pushRect_aux (innerL : List Nat)
    (out : Array (Nat × Nat)) (c d : Nat) :
    ∀ (l : List Nat),
      (c, d) ∈ (l.foldl (fun out a =>
        innerL.foldl (fun out b => out.push (a, b)) out) out).toList ↔
        (c, d) ∈ out.toList ∨ (c ∈ l ∧ d ∈ innerL) := by
  intro l
  induction l generalizing out with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih, mem_foldl_push_b]
    constructor
    · rintro ((h | ⟨hc, hd⟩) | ⟨hc, hd⟩)
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons.mpr (Or.inl hc), hd⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ hc, hd⟩
    · rintro (h | ⟨hc, hd⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inl (Or.inr ⟨rfl, hd⟩)
        · exact Or.inr ⟨hc', hd⟩

/-- The result of `pushRect` has size equal to `out.size + (offI1 - offI) * (offJ1 - offJ)`. -/
private lemma pushRect_size (offI offI1 offJ offJ1 : Nat)
    (out : Array (Nat × Nat)) :
    (pushRect offI offI1 offJ offJ1 out).size =
      out.size + (offI1 - offI) * (offJ1 - offJ) := by
  unfold pushRect
  generalize (offI1 - offI) = m
  generalize (offJ1 - offJ) = n
  -- Show the foldl preserves size accumulation by induction on the outer list.
  suffices h :
      ∀ (l : List Nat) (out : Array (Nat × Nat)),
        (l.foldl (fun out a =>
          (List.range' offJ n).foldl (fun out b => out.push (a, b)) out) out).size =
            out.size + l.length * n by
    rw [h]
    rw [List.length_range']
  intro l out
  induction l generalizing out with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldl_cons, ih]
    have h_inner :
        ((List.range' offJ n).foldl (fun out b => out.push (a, b)) out).size =
          out.size + n := by
      have : ∀ (l : List Nat) (out : Array (Nat × Nat)),
          (l.foldl (fun out b => out.push (a, b)) out).size = out.size + l.length := by
        intro l out
        induction l generalizing out with
        | nil => simp
        | cons b rest ih =>
          rw [List.foldl_cons, ih, Array.size_push, List.length_cons]
          omega
      rw [this, List.length_range']
    rw [h_inner, List.length_cons]
    ring

/-- Membership in `pushRect`'s output. -/
private lemma mem_pushRect (offI offI1 offJ offJ1 : Nat)
    (out : Array (Nat × Nat)) (c d : Nat) :
    (c, d) ∈ (pushRect offI offI1 offJ offJ1 out).toList ↔
      (c, d) ∈ out.toList ∨
        (offI ≤ c ∧ c < offI1 ∧ offJ ≤ d ∧ d < offJ1) := by
  unfold pushRect
  rw [mem_pushRect_aux]
  simp only [List.mem_range'_1]
  -- Goal: (c, d) ∈ out.toList ∨ (offI ≤ c ∧ c < offI + (offI1 - offI)) ∧
  --       (offJ ≤ d ∧ d < offJ + (offJ1 - offJ))
  -- ↔  (c, d) ∈ out.toList ∨ offI ≤ c ∧ c < offI1 ∧ offJ ≤ d ∧ d < offJ1
  refine or_congr Iff.rfl ?_
  by_cases hI : offI1 ≤ offI
  · -- offI1 ≤ offI, so the LHS forces c < offI which clashes with offI ≤ c.
    have h_emp : offI1 - offI = 0 := by omega
    rw [h_emp, Nat.add_zero]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; omega
    · rintro ⟨h1, h2, _⟩; omega
  · push_neg at hI
    by_cases hJ : offJ1 ≤ offJ
    · have h_emp : offJ1 - offJ = 0 := by omega
      rw [h_emp, Nat.add_zero]
      constructor
      · rintro ⟨_, h1, h2⟩; omega
      · rintro ⟨_, _, _, h⟩; omega
    · push_neg at hJ
      have hI_eq : offI + (offI1 - offI) = offI1 := by omega
      have hJ_eq : offJ + (offJ1 - offJ) = offJ1 := by omega
      rw [hI_eq, hJ_eq]
      tauto

/-- Inner two for-loops of `enumPartition` (over `a ∈ [offI, offI1)`,
`b ∈ [offJ, offJ1)`), in the `cond = true` case, push the rectangle
to `state.2`. -/
private lemma forIn_inner_two_loops_true (offI offI1 offJ offJ1 : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat))
    (h_cond : True = True) :
    (forIn (m := Id) (List.range' offI (offI1 - offI)) state (fun a state =>
      (do pure PUnit.unit
          let r ← (forIn (m := Id) (List.range' offJ (offJ1 - offJ)) state
            (fun b state =>
              (do pure PUnit.unit
                  pure (ForInStep.yield (state.1, state.2.push (a, b))) : Id _)))
          pure (ForInStep.yield r) : Id _))) =
      (state.1, pushRect offI offI1 offJ offJ1 state.2) := by
  clear h_cond
  unfold pushRect
  -- Inner b-loop: pushes (a, b) to state.2 for b ∈ inner_list.
  have h_inner : ∀ (l : List Nat) (st : Array (Nat × Nat) × Array (Nat × Nat))
      (a : Nat),
      (forIn (m := Id) l st (fun b state =>
        (do pure PUnit.unit
            pure (ForInStep.yield (state.1, state.2.push (a, b))) : Id _))) =
        (st.1, l.foldl (fun out b => out.push (a, b)) st.2) := by
    intro l st a
    induction l generalizing st with
    | nil => rfl
    | cons b rest ih =>
      rw [List.forIn_cons]
      show (forIn (m := Id) rest (st.1, st.2.push (a, b)) _ : Id _) = _
      rw [ih, List.foldl_cons]
  -- Outer a-loop.
  induction (List.range' offI (offI1 - offI)) generalizing state with
  | nil => rfl
  | cons a rest ih =>
    rw [List.forIn_cons]
    show (forIn (m := Id) rest _ _ : Id _) = _
    rw [h_inner]
    -- After inner: st.1 unchanged, st.2 now has rectangle pushes.
    rw [ih]
    rw [List.foldl_cons]

/-- Inner two for-loops, `cond = false` case, push to `state.1`. -/
private lemma forIn_inner_two_loops_false (offI offI1 offJ offJ1 : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat)) :
    (forIn (m := Id) (List.range' offI (offI1 - offI)) state (fun a state =>
      (do pure PUnit.unit
          let r ← (forIn (m := Id) (List.range' offJ (offJ1 - offJ)) state
            (fun b state =>
              (do pure PUnit.unit
                  pure (ForInStep.yield (state.1.push (a, b), state.2)) : Id _)))
          pure (ForInStep.yield r) : Id _))) =
      (pushRect offI offI1 offJ offJ1 state.1, state.2) := by
  unfold pushRect
  have h_inner : ∀ (l : List Nat) (st : Array (Nat × Nat) × Array (Nat × Nat))
      (a : Nat),
      (forIn (m := Id) l st (fun b state =>
        (do pure PUnit.unit
            pure (ForInStep.yield (state.1.push (a, b), state.2)) : Id _))) =
        (l.foldl (fun out b => out.push (a, b)) st.1, st.2) := by
    intro l st a
    induction l generalizing st with
    | nil => rfl
    | cons b rest ih =>
      rw [List.forIn_cons]
      show (forIn (m := Id) rest (st.1.push (a, b), st.2) _ : Id _) = _
      rw [ih, List.foldl_cons]
  induction (List.range' offI (offI1 - offI)) generalizing state with
  | nil => rfl
  | cons a rest ih =>
    rw [List.forIn_cons]
    show (forIn (m := Id) rest _ _ : Id _) = _
    rw [h_inner]
    rw [ih]
    rw [List.foldl_cons]

/-- The body of one (i, j) iteration: applies `pushRect` to `state.2`
if `j - i > w`, otherwise to `state.1`. -/
private def jLoopBody (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat)) :
    Array (Nat × Nat) × Array (Nat × Nat) :=
  let offI := offsets.getD i 0
  let offI1 := offsets.getD (i + 1) 0
  let offJ := offsets.getD j 0
  let offJ1 := offsets.getD (j + 1) 0
  if j - i > w then
    (state.1, pushRect offI offI1 offJ offJ1 state.2)
  else
    (pushRect offI offI1 offJ offJ1 state.1, state.2)

/-- The j-loop body's effect on freeUV. -/
private lemma jLoopBody_fst (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat)) :
    (jLoopBody w offsets i j state).1 =
      if j - i > w then state.1 else
        pushRect (offsets.getD i 0) (offsets.getD (i+1) 0)
                 (offsets.getD j 0) (offsets.getD (j+1) 0) state.1 := by
  unfold jLoopBody
  split_ifs <;> rfl

/-- The j-loop body's effect on forcedUV. -/
private lemma jLoopBody_snd (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat)) :
    (jLoopBody w offsets i j state).2 =
      if j - i > w then
        pushRect (offsets.getD i 0) (offsets.getD (i+1) 0)
                 (offsets.getD j 0) (offsets.getD (j+1) 0) state.2
      else state.2 := by
  unfold jLoopBody
  split_ifs <;> rfl

/-- Membership monotonicity in `pushRect`. -/
private lemma mem_pushRect_mono (offI offI1 offJ offJ1 : Nat)
    (out : Array (Nat × Nat)) (cd : Nat × Nat) :
    cd ∈ out.toList → cd ∈ (pushRect offI offI1 offJ offJ1 out).toList := by
  obtain ⟨c, d⟩ := cd
  intro h; rw [mem_pushRect]; exact Or.inl h

/-- Membership monotonicity in `jLoopBody`. -/
private lemma mem_jLoopBody_mono (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : Array (Nat × Nat) × Array (Nat × Nat)) (cd : Nat × Nat) :
    (cd ∈ state.1.toList → cd ∈ (jLoopBody w offsets i j state).1.toList) ∧
    (cd ∈ state.2.toList → cd ∈ (jLoopBody w offsets i j state).2.toList) := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [jLoopBody_fst]
    split_ifs
    · exact h
    · exact mem_pushRect_mono _ _ _ _ _ _ h
  · intro h
    rw [jLoopBody_snd]
    split_ifs
    · exact mem_pushRect_mono _ _ _ _ _ _ h
    · exact h

/-- Membership monotonicity in foldl of `jLoopBody`. -/
private lemma mem_foldl_jLoopBody_mono (w : Nat) (offsets : Array Nat) (i : Nat)
    (l : List Nat) (state : Array (Nat × Nat) × Array (Nat × Nat))
    (cd : Nat × Nat) :
    (cd ∈ state.1.toList →
      cd ∈ (l.foldl (fun st j => jLoopBody w offsets i j st) state).1.toList) ∧
    (cd ∈ state.2.toList →
      cd ∈ (l.foldl (fun st j => jLoopBody w offsets i j st) state).2.toList) := by
  induction l generalizing state with
  | nil => exact ⟨id, id⟩
  | cons j rest ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (jLoopBody w offsets i j state)
    obtain ⟨k1, k2⟩ := mem_jLoopBody_mono w offsets i j state cd
    exact ⟨fun h => h1 (k1 h), fun h => h2 (k2 h)⟩

/-! #### §7b — MProd-shaped variants for `enumPartition`'s two-`mut`
do-block elaboration.

The do-block of `enumPartition` (`Case3Enum.lean §5`) has two `let mut`
variables (`freeUV` and `forcedUV`) which Lean's do-elaborator combines
into a single `MProd` state. The Prod-shaped helpers above
(`forIn_inner_two_loops_*`, `jLoopBody`) don't directly compose with
the elaborated do-block. The MProd-shaped variants below mirror the
Prod versions and let us reduce `enumPartition`'s do-block to an
explicit nested `foldl` form. -/

/-- MProd-shape `jLoopBody`: the body of one `(i, j)` iteration on a
joint `MProd Array Array` state. The field convention follows
`enumPartition`'s do-elaboration: `state.fst = forcedUV` (pushed when
`j - i > w`), `state.snd = freeUV` (pushed otherwise). -/
private def jLoopBodyM (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat))) :
    MProd (Array (Nat × Nat)) (Array (Nat × Nat)) :=
  let offI := offsets.getD i 0
  let offI1 := offsets.getD (i + 1) 0
  let offJ := offsets.getD j 0
  let offJ1 := offsets.getD (j + 1) 0
  if j - i > w then
    ⟨pushRect offI offI1 offJ offJ1 state.fst, state.snd⟩
  else
    ⟨state.fst, pushRect offI offI1 offJ offJ1 state.snd⟩

private lemma jLoopBodyM_fst (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat))) :
    (jLoopBodyM w offsets i j state).fst =
      if j - i > w then
        pushRect (offsets.getD i 0) (offsets.getD (i+1) 0)
                 (offsets.getD j 0) (offsets.getD (j+1) 0) state.fst
      else state.fst := by
  unfold jLoopBodyM; split_ifs <;> rfl

private lemma jLoopBodyM_snd (w : Nat) (offsets : Array Nat) (i j : Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat))) :
    (jLoopBodyM w offsets i j state).snd =
      if j - i > w then state.snd else
        pushRect (offsets.getD i 0) (offsets.getD (i+1) 0)
                 (offsets.getD j 0) (offsets.getD (j+1) 0) state.snd := by
  unfold jLoopBodyM; split_ifs <;> rfl

/-- MProd inner b-loop with `if cond` inside the body. State given
as explicit `(fA, fB)` arrays to avoid eta issues. -/
private lemma forIn_inner_b_loop_M_cond (w : Nat) (a i j : Nat)
    (l : List Nat) (fA fB : Array (Nat × Nat)) :
    (forIn (m := Id) l (⟨fA, fB⟩ :
        MProd (Array (Nat × Nat)) (Array (Nat × Nat))) (fun b r =>
      if j - i > w then
        (do pure PUnit.unit
            pure (ForInStep.yield (⟨r.fst.push (a, b), r.snd⟩ :
              MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)
      else
        (do pure PUnit.unit
            pure (ForInStep.yield (⟨r.fst, r.snd.push (a, b)⟩ :
              MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _))) =
      (if j - i > w then
        ⟨l.foldl (fun out b => out.push (a, b)) fA, fB⟩
      else
        ⟨fA, l.foldl (fun out b => out.push (a, b)) fB⟩) := by
  induction l generalizing fA fB with
  | nil =>
    by_cases hc : j - i > w
    · simp only [hc, ↓reduceIte, List.foldl_nil]; rfl
    · simp only [hc, ↓reduceIte, List.foldl_nil]; rfl
  | cons b rest ih =>
    rw [List.forIn_cons]
    by_cases hc : j - i > w
    · simp only [hc, ↓reduceIte]
      show (forIn (m := Id) rest
          (⟨fA.push (a, b), fB⟩ :
            MProd (Array (Nat × Nat)) (Array (Nat × Nat))) _ : Id _) = _
      have := ih (fA := fA.push (a, b)) (fB := fB)
      simp only [hc, ↓reduceIte] at this
      rw [this, List.foldl_cons]
    · simp only [hc, ↓reduceIte]
      show (forIn (m := Id) rest
          (⟨fA, fB.push (a, b)⟩ :
            MProd (Array (Nat × Nat)) (Array (Nat × Nat))) _ : Id _) = _
      have := ih (fA := fA) (fB := fB.push (a, b))
      simp only [hc, ↓reduceIte] at this
      rw [this, List.foldl_cons]

/-- MProd inner two for-loops with cond inside the inner-most body.
State given as explicit `(fA, fB)` arrays. The lemma is stated for an
arbitrary outer-loop list `aL` so that induction abstracts it
uniformly across LHS and RHS. -/
private lemma forIn_inner_two_loops_M_cond_aux
    (w : Nat) (offsets : Array Nat) (i j : Nat) (aL : List Nat) :
    ∀ (fA fB : Array (Nat × Nat)),
    (forIn (m := Id) aL
        (⟨fA, fB⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
        (fun a r =>
      (do
          let r ← (forIn (m := Id) (List.range' (offsets.getD j 0)
              ((offsets.getD (j + 1) 0) - (offsets.getD j 0)))
              (⟨r.fst, r.snd⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
            (fun b r =>
              if j - i > w then
                (do pure PUnit.unit
                    pure (ForInStep.yield (⟨r.fst.push (a, b), r.snd⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)
              else
                (do pure PUnit.unit
                    pure (ForInStep.yield (⟨r.fst, r.snd.push (a, b)⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)))
          pure PUnit.unit
          pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
            MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _))) =
      (if j - i > w then
        ⟨aL.foldl (fun out a =>
          (List.range' (offsets.getD j 0)
            ((offsets.getD (j + 1) 0) - (offsets.getD j 0))).foldl
            (fun out b => out.push (a, b)) out) fA, fB⟩
      else
        ⟨fA, aL.foldl (fun out a =>
          (List.range' (offsets.getD j 0)
            ((offsets.getD (j + 1) 0) - (offsets.getD j 0))).foldl
            (fun out b => out.push (a, b)) out) fB⟩) := by
  induction aL with
  | nil =>
    intros fA fB
    by_cases hc : j - i > w
    · simp only [hc, ↓reduceIte, List.foldl_nil]; rfl
    · simp only [hc, ↓reduceIte, List.foldl_nil]; rfl
  | cons a rest ih =>
    intros fA fB
    rw [List.forIn_cons]
    show (forIn (m := Id) rest _ _ : Id _) = _
    rw [forIn_inner_b_loop_M_cond w a i j _ fA fB]
    by_cases hc : j - i > w
    · simp only [hc, ↓reduceIte]
      have := ih ((List.range' (offsets.getD j 0)
          ((offsets.getD (j + 1) 0) - (offsets.getD j 0))).foldl
          (fun out b => out.push (a, b)) fA) fB
      simp only [hc, ↓reduceIte] at this
      rw [this, List.foldl_cons]
    · simp only [hc, ↓reduceIte]
      have := ih fA ((List.range' (offsets.getD j 0)
          ((offsets.getD (j + 1) 0) - (offsets.getD j 0))).foldl
          (fun out b => out.push (a, b)) fB)
      simp only [hc, ↓reduceIte] at this
      rw [this, List.foldl_cons]

/-- MProd inner two for-loops, specialized to the outer a-list of
`enumPartition`. -/
private lemma forIn_inner_two_loops_M_cond
    (w : Nat) (offsets : Array Nat) (i j : Nat)
    (fA fB : Array (Nat × Nat)) :
    (forIn (m := Id) (List.range' (offsets.getD i 0)
        ((offsets.getD (i + 1) 0) - (offsets.getD i 0)))
        (⟨fA, fB⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
        (fun a r =>
      (do
          let r ← (forIn (m := Id) (List.range' (offsets.getD j 0)
              ((offsets.getD (j + 1) 0) - (offsets.getD j 0)))
              (⟨r.fst, r.snd⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
            (fun b r =>
              if j - i > w then
                (do pure PUnit.unit
                    pure (ForInStep.yield (⟨r.fst.push (a, b), r.snd⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)
              else
                (do pure PUnit.unit
                    pure (ForInStep.yield (⟨r.fst, r.snd.push (a, b)⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)))
          pure PUnit.unit
          pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
            MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _))) =
      jLoopBodyM w offsets i j ⟨fA, fB⟩ := by
  unfold jLoopBodyM pushRect
  exact forIn_inner_two_loops_M_cond_aux w offsets i j _ fA fB

/-- The outer j-loop of `enumPartition` (over `j ∈ [i+1, K)`) reduces
to a `foldl` of `jLoopBodyM`. -/
private lemma forIn_jLoop_M (w : Nat) (offsets : Array Nat) (i K : Nat)
    (fA fB : Array (Nat × Nat)) :
    (forIn (m := Id) (List.range' (i + 1) (K - (i + 1)))
        (⟨fA, fB⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
        (fun j r =>
      (do
        let r ← (forIn (m := Id) (List.range' (offsets.getD i 0)
            ((offsets.getD (i + 1) 0) - (offsets.getD i 0)))
            (⟨r.fst, r.snd⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
          (fun a r =>
            (do
                let r ← (forIn (m := Id) (List.range' (offsets.getD j 0)
                    ((offsets.getD (j + 1) 0) - (offsets.getD j 0)))
                    (⟨r.fst, r.snd⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
                  (fun b r =>
                    if j - i > w then
                      (do pure PUnit.unit
                          pure (ForInStep.yield (⟨r.fst.push (a, b), r.snd⟩ :
                            MProd (Array (Nat × Nat))
                                  (Array (Nat × Nat)))) : Id _)
                    else
                      (do pure PUnit.unit
                          pure (ForInStep.yield (⟨r.fst, r.snd.push (a, b)⟩ :
                            MProd (Array (Nat × Nat))
                                  (Array (Nat × Nat)))) : Id _)))
                pure PUnit.unit
                pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
                  MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)))
        pure PUnit.unit
        pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
          MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _))) =
      (List.range' (i + 1) (K - (i + 1))).foldl
        (fun st j => jLoopBodyM w offsets i j st) ⟨fA, fB⟩ := by
  induction (List.range' (i + 1) (K - (i + 1))) generalizing fA fB with
  | nil => rfl
  | cons j rest ih =>
    rw [List.forIn_cons, List.foldl_cons]
    -- The body for `j` evaluates the inner two for-loops to jLoopBodyM.
    rw [forIn_inner_two_loops_M_cond w offsets i j fA fB]
    -- The new state is jLoopBodyM ⟨fA, fB⟩
    show (forIn rest _ _ : Id _) = _
    -- The new state is the MProd value (jLoopBodyM ...). Apply ih with its
    -- fst/snd projections.
    let next := jLoopBodyM w offsets i j ⟨fA, fB⟩
    exact ih (fA := next.fst) (fB := next.snd)

/-- The outer i-loop of `enumPartition` reduces to a nested `foldl`
of `jLoopBodyM`. State given as explicit `(fA, fB)` arrays. -/
private lemma forIn_iLoop_M (w : Nat) (offsets : Array Nat) (K : Nat)
    (fA fB : Array (Nat × Nat)) :
    (forIn (m := Id) (List.range' 0 K)
        (⟨fA, fB⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
        (fun i r =>
      (do
          let r ← (forIn (m := Id) (List.range' (i + 1) (K - (i + 1)))
              (⟨r.fst, r.snd⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
            (fun j r =>
              (do
                let r ← (forIn (m := Id) (List.range' (offsets.getD i 0)
                    ((offsets.getD (i + 1) 0) - (offsets.getD i 0)))
                    (⟨r.fst, r.snd⟩ :
                      MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
                  (fun a r =>
                    (do
                        let r ← (forIn (m := Id) (List.range' (offsets.getD j 0)
                            ((offsets.getD (j + 1) 0) - (offsets.getD j 0)))
                            (⟨r.fst, r.snd⟩ :
                              MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
                          (fun b r =>
                            if j - i > w then
                              (do pure PUnit.unit
                                  pure (ForInStep.yield
                                    (⟨r.fst.push (a, b), r.snd⟩ :
                                      MProd (Array (Nat × Nat))
                                            (Array (Nat × Nat)))) : Id _)
                            else
                              (do pure PUnit.unit
                                  pure (ForInStep.yield
                                    (⟨r.fst, r.snd.push (a, b)⟩ :
                                      MProd (Array (Nat × Nat))
                                            (Array (Nat × Nat)))) : Id _)))
                        pure PUnit.unit
                        pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
                          MProd (Array (Nat × Nat))
                                (Array (Nat × Nat)))) : Id _)))
                pure PUnit.unit
                pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
                  MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _)))
          pure PUnit.unit
          pure (ForInStep.yield (⟨r.fst, r.snd⟩ :
            MProd (Array (Nat × Nat)) (Array (Nat × Nat)))) : Id _))) =
      (List.range' 0 K).foldl
        (fun st i =>
          (List.range' (i + 1) (K - (i + 1))).foldl
            (fun st j => jLoopBodyM w offsets i j st) st)
        ⟨fA, fB⟩ := by
  induction (List.range' 0 K) generalizing fA fB with
  | nil => rfl
  | cons i rest ih =>
    rw [List.forIn_cons, List.foldl_cons]
    -- The body for `i` evaluates the j-loop forIn.
    rw [forIn_jLoop_M w offsets i K fA fB]
    -- The new state is foldl over jLoopBodyM applied to ⟨fA, fB⟩.
    show (forIn rest _ _ : Id _) = _
    let next := (List.range' (i + 1) (K - (i + 1))).foldl
        (fun st j => jLoopBodyM w offsets i j st) ⟨fA, fB⟩
    exact ih (fA := next.fst) (fB := next.snd)

/-- **Imperative→functional reduction of `enumPartition`** (§7).

The four-deep nested `for`-loops of `enumPartition w bs` reduce, in
`Id`, to a clean nested `foldl` over `(i, j)` pairs of `jLoopBodyM`,
applied to the initial state `⟨#[], #[]⟩`. The MProd convention:
`fst = forcedUV` (pushed when `j - i > w`), `snd = freeUV`. The
result swaps to `(freeUV, forcedUV)` as `enumPartition` returns. -/
lemma enumPartition_eq (w : Nat) (bs : List Nat) :
    enumPartition w bs =
      let st :=
        (List.range' 0 bs.length).foldl
          (fun st i =>
            (List.range' (i + 1) (bs.length - (i + 1))).foldl
              (fun st j => jLoopBodyM w (offsetsOf bs) i j st) st)
          (⟨#[], #[]⟩ : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
      (st.snd, st.fst) := by
  unfold enumPartition
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  show ((forIn (m := Id) _ _ _ : Id _) >>= _) = _
  rw [forIn_iLoop_M w (offsetsOf bs) bs.length #[] #[]]
  rfl

/-! #### §7c — Membership characterizations of `enumFreeUVOf` /
`enumForcedUVOf`. -/

private lemma mem_jLoopBodyM_fst_iff (w : Nat) (offsets : Array Nat)
    (i j : Nat) (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ (jLoopBodyM w offsets i j state).fst.toList ↔
      cd ∈ state.fst.toList ∨
        (j - i > w ∧
         (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
         (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  unfold jLoopBodyM
  by_cases hc : j - i > w
  · simp only [hc, ↓reduceIte, true_and]
    obtain ⟨c, d⟩ := cd
    rw [mem_pushRect]
  · simp only [hc, ↓reduceIte, false_and, or_false]

private lemma mem_jLoopBodyM_snd_iff (w : Nat) (offsets : Array Nat)
    (i j : Nat) (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ (jLoopBodyM w offsets i j state).snd.toList ↔
      cd ∈ state.snd.toList ∨
        (¬ j - i > w ∧
         (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
         (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  unfold jLoopBodyM
  by_cases hc : j - i > w
  · simp only [hc, ↓reduceIte, not_true_eq_false, false_and, or_false]
  · simp only [hc, ↓reduceIte, not_false_eq_true, true_and]
    obtain ⟨c, d⟩ := cd
    rw [mem_pushRect]

private lemma mem_foldl_jLoopBodyM_fst_iff (w : Nat) (offsets : Array Nat)
    (i : Nat) (l : List Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ ((l.foldl (fun st j => jLoopBodyM w offsets i j st) state).fst.toList) ↔
      cd ∈ state.fst.toList ∨
        (∃ j ∈ l, j - i > w ∧
          (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
          (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  induction l generalizing state with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, mem_jLoopBodyM_fst_iff]
    constructor
    · rintro ((h1 | h2) | ⟨j', hj'_mem, hcond⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_self, h2⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj'_mem, hcond⟩
    · rintro (h | ⟨j', hj'_mem, hcond⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hj'_mem with rfl | hmem
        · exact Or.inl (Or.inr hcond)
        · exact Or.inr ⟨j', hmem, hcond⟩

private lemma mem_foldl_jLoopBodyM_snd_iff (w : Nat) (offsets : Array Nat)
    (i : Nat) (l : List Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ ((l.foldl (fun st j => jLoopBodyM w offsets i j st) state).snd.toList) ↔
      cd ∈ state.snd.toList ∨
        (∃ j ∈ l, ¬ j - i > w ∧
          (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
          (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  induction l generalizing state with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, mem_jLoopBodyM_snd_iff]
    constructor
    · rintro ((h1 | h2) | ⟨j', hj'_mem, hcond⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_self, h2⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj'_mem, hcond⟩
    · rintro (h | ⟨j', hj'_mem, hcond⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hj'_mem with rfl | hmem
        · exact Or.inl (Or.inr hcond)
        · exact Or.inr ⟨j', hmem, hcond⟩

/-- Membership in the fst of the nested foldl over (i, j). -/
private lemma mem_foldl_foldl_jLoopBodyM_fst_iff
    (w : Nat) (offsets : Array Nat) (K : Nat) (l : List Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ ((l.foldl
        (fun st i =>
          (List.range' (i + 1) (K - (i + 1))).foldl
            (fun st j => jLoopBodyM w offsets i j st) st) state).fst.toList) ↔
      cd ∈ state.fst.toList ∨
        (∃ i ∈ l, ∃ j ∈ List.range' (i + 1) (K - (i + 1)),
          j - i > w ∧
          (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
          (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  induction l generalizing state with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih, mem_foldl_jLoopBodyM_fst_iff]
    constructor
    · rintro ((h1 | ⟨j, hj_mem, hcond⟩) | ⟨i', hi'_mem, hexists⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨i, List.mem_cons_self, j, hj_mem, hcond⟩
      · exact Or.inr ⟨i', List.mem_cons_of_mem _ hi'_mem, hexists⟩
    · rintro (h | ⟨i', hi'_mem, j, hj_mem, hcond⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hi'_mem with rfl | hmem
        · exact Or.inl (Or.inr ⟨j, hj_mem, hcond⟩)
        · exact Or.inr ⟨i', hmem, j, hj_mem, hcond⟩

/-- Membership in the snd of the nested foldl over (i, j). -/
private lemma mem_foldl_foldl_jLoopBodyM_snd_iff
    (w : Nat) (offsets : Array Nat) (K : Nat) (l : List Nat)
    (state : MProd (Array (Nat × Nat)) (Array (Nat × Nat)))
    (cd : Nat × Nat) :
    cd ∈ ((l.foldl
        (fun st i =>
          (List.range' (i + 1) (K - (i + 1))).foldl
            (fun st j => jLoopBodyM w offsets i j st) st) state).snd.toList) ↔
      cd ∈ state.snd.toList ∨
        (∃ i ∈ l, ∃ j ∈ List.range' (i + 1) (K - (i + 1)),
          ¬ j - i > w ∧
          (offsets.getD i 0) ≤ cd.1 ∧ cd.1 < (offsets.getD (i+1) 0) ∧
          (offsets.getD j 0) ≤ cd.2 ∧ cd.2 < (offsets.getD (j+1) 0)) := by
  induction l generalizing state with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih, mem_foldl_jLoopBodyM_snd_iff]
    constructor
    · rintro ((h1 | ⟨j, hj_mem, hcond⟩) | ⟨i', hi'_mem, hexists⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨i, List.mem_cons_self, j, hj_mem, hcond⟩
      · exact Or.inr ⟨i', List.mem_cons_of_mem _ hi'_mem, hexists⟩
    · rintro (h | ⟨i', hi'_mem, j, hj_mem, hcond⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hi'_mem with rfl | hmem
        · exact Or.inl (Or.inr ⟨j, hj_mem, hcond⟩)
        · exact Or.inr ⟨i', hmem, j, hj_mem, hcond⟩

/-- **Membership in `enumForcedUVOf`** (§7). A pair `(a, b)` is in
the forced output iff there exist band indices `i < j < bs.length`
with `j - i > w`, `a` in band-`i+1`'s range, `b` in band-`j+1`'s
range. -/
lemma mem_enumForcedUVOf_iff (w : Nat) (bs : List Nat) (a b : Nat) :
    (a, b) ∈ (enumForcedUVOf w bs).toList ↔ IsForcedPair w bs a b := by
  unfold enumForcedUVOf
  rw [enumPartition_eq]
  show (a, b) ∈ _ ↔ _
  rw [mem_foldl_foldl_jLoopBodyM_fst_iff]
  unfold IsForcedPair
  constructor
  · rintro (h | ⟨i, hi_mem, j, hj_mem, hcond, ha1, ha2, hb1, hb2⟩)
    · exact absurd h (List.not_mem_nil)
    · refine ⟨i, j, ?_, ?_, hcond, ha1, ha2, hb1, hb2⟩
      · rw [List.mem_range'_1] at hj_mem; exact hj_mem.1
      · rw [List.mem_range'_1] at hj_mem; omega
  · rintro ⟨i, j, hij, hjK, hcond, ha1, ha2, hb1, hb2⟩
    refine Or.inr ⟨i, ?_, j, ?_, hcond, ha1, ha2, hb1, hb2⟩
    · rw [List.mem_range'_1]; exact ⟨Nat.zero_le _, by omega⟩
    · rw [List.mem_range'_1]; exact ⟨hij, by omega⟩

/-- **Membership in `enumFreeUVOf`** (§7). A pair `(a, b)` is in the
free output iff there exist band indices `i < j < bs.length` with
`j - i ≤ w` and the band-rectangle constraints. -/
lemma mem_enumFreeUVOf_iff (w : Nat) (bs : List Nat) (a b : Nat) :
    (a, b) ∈ (enumFreeUVOf w bs).toList ↔ IsFreePair w bs a b := by
  unfold enumFreeUVOf
  rw [enumPartition_eq]
  show (a, b) ∈ _ ↔ _
  rw [mem_foldl_foldl_jLoopBodyM_snd_iff]
  unfold IsFreePair
  constructor
  · rintro (h | ⟨i, hi_mem, j, hj_mem, hcond, ha1, ha2, hb1, hb2⟩)
    · exact absurd h (List.not_mem_nil)
    · refine ⟨i, j, ?_, ?_, ?_, ha1, ha2, hb1, hb2⟩
      · rw [List.mem_range'_1] at hj_mem; exact hj_mem.1
      · rw [List.mem_range'_1] at hj_mem; omega
      · omega
  · rintro ⟨i, j, hij, hjK, hcond, ha1, ha2, hb1, hb2⟩
    refine Or.inr ⟨i, ?_, j, ?_, ?_, ha1, ha2, hb1, hb2⟩
    · rw [List.mem_range'_1]; exact ⟨Nat.zero_le _, by omega⟩
    · rw [List.mem_range'_1]; exact ⟨hij, by omega⟩
    · omega

end OneThird.Step8.Case3Enum

/-! ### §8 — Construction-equivalence: `enumPredAtMaskOf = predMaskOf`

The headline construction-equivalence required by F5a's bridge. The
proof combines:

* §6 — bit characterization of `enumPredPreWarshallOf`.
* §7 — membership characterization of `enumForcedUVOf`/`enumFreeUVOf`.
* `LayeredDecomposition`'s `forced_lt` and `cross_band_lt_upward`
  fields, the band-major positional formula
  `bandMajorEquiv_val_lt_bandOffset_iff`, and the bit characterization
  of `predMaskOf` (`testBit_predMaskOf`).
* §1 — `enumNOf (bandSizes L) = Fintype.card α`.
* `predMaskOf_warshall` — Warshall is a no-op on `predMaskOf L`.
* `closureCanonical_predMaskOf` infrastructure (`maskOfRec`'s
  bit-by-bit characterization). -/

namespace OneThird.Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- `(a, b) ∈ A.toList` iff there exists an in-bounds index `k` with
`A.getD k (0, 0) = (a, b)`. -/
private lemma mem_toList_iff_exists_getD (A : Array (Nat × Nat)) (a b : Nat) :
    (a, b) ∈ A.toList ↔ ∃ k, k < A.size ∧ A.getD k (0, 0) = (a, b) := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨k, hkLt, hkEq⟩
    refine ⟨k, hkLt, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkLt, Option.getD_some]
    exact hkEq
  · rintro ⟨k, hkLt, hkEq⟩
    refine ⟨k, hkLt, ?_⟩
    have : A[k] = A.getD k (0, 0) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hkLt]; rfl
    rw [this, hkEq]

/-- For a `LayeredDecomposition L` with `cross_band_lt_upward`, the
bit-set predicate of `enumPredPreWarshallOf` at mask `maskOf L`
matches the bit-set predicate of `predMaskOf L`.

The forward direction uses `forced_lt` (for forced pairs) and the
`maskOfRec` bit characterization (for free pairs). The backward
direction uses §2's `bandMajor_pos_lt_of_predMask_bit` to extract
band indices, then case splits on `j - i` vs `L.w`. -/
lemma testBit_enumPredPreWarshallOf_iff_testBit_predMaskOf
    (L : LayeredDecomposition α) (u v : Nat) :
    Nat.testBit ((Case3Enum.enumPredPreWarshallOf L.w (bandSizes L)
        (maskOf L)).getD v 0) u = true ↔
      Nat.testBit ((predMaskOf L).getD v 0) u = true := by
  classical
  constructor
  · -- (⇒) bit set in enumPredPreWarshallOf ⟹ bit set in predMaskOf
    intro h
    obtain ⟨hv_lt, hbits⟩ :=
      Case3Enum.testBit_enumPredPreWarshallOf_imp _ _ _ _ _ h
    rcases hbits with hForced | ⟨k, hk_lt, hbit_mask, hfreeUV_eq⟩
    · -- Forced case: by `mem_enumForcedUVOf_iff`, get IsForcedPair, then forced_lt.
      rw [Case3Enum.mem_enumForcedUVOf_iff] at hForced
      obtain ⟨i, j, hij, hjK, hgap, ha1, ha2, hb1, hb2⟩ := hForced
      have hKlen : (bandSizes L).length = L.K := bandSizes_length L
      -- Identify (offsetsOf bs).getD k 0 with bandOffset L k.
      rw [offsetsOf_bandSizes_getD L i (by omega)] at ha1
      rw [offsetsOf_bandSizes_getD L (i+1) (by omega)] at ha2
      rw [offsetsOf_bandSizes_getD L j (by omega)] at hb1
      rw [offsetsOf_bandSizes_getD L (j+1) (by omega)] at hb2
      -- u, v are in the right band ranges; band of symm u = i+1, band of symm v = j+1.
      have hu_lt_card : u < Fintype.card α := by
        have hcard := bandOffset_K L
        have hmono : bandOffset L (i + 1) ≤ bandOffset L L.K :=
          bandOffset_mono L (by omega)
        rw [hcard] at hmono; omega
      have hv_lt_card : v < Fintype.card α := by
        have hcard := bandOffset_K L
        have hmono : bandOffset L (j + 1) ≤ bandOffset L L.K :=
          bandOffset_mono L (by omega)
        rw [hcard] at hmono; omega
      -- band of symm u = i+1
      have hu_eq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩)).val
          = u := by rw [Equiv.apply_symm_apply]
      have hv_eq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩)).val
          = v := by rw [Equiv.apply_symm_apply]
      have hbandU : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) = i + 1 := by
        have h1 : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) ≤ i + 1 := by
          rw [← bandMajorEquiv_val_lt_bandOffset_iff, hu_eq]
          exact ha2
        have h2 : ¬ L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) ≤ i := by
          rw [← bandMajorEquiv_val_lt_bandOffset_iff, hu_eq]
          omega
        omega
      have hbandV : L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) = j + 1 := by
        have h1 : L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) ≤ j + 1 := by
          rw [← bandMajorEquiv_val_lt_bandOffset_iff, hv_eq]
          exact hb2
        have h2 : ¬ L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) ≤ j := by
          rw [← bandMajorEquiv_val_lt_bandOffset_iff, hv_eq]
          omega
        omega
      -- Apply forced_lt: band(symm u) + L.w < band(symm v) → symm u < symm v.
      have hlt :
          (bandMajorEquiv L).symm ⟨u, hu_lt_card⟩ <
            (bandMajorEquiv L).symm ⟨v, hv_lt_card⟩ := by
        apply L.forced_lt
        rw [hbandU, hbandV]; omega
      -- bit u of (predMaskOf L)[v] is set.
      exact (testBit_predMaskOf L ⟨u, hu_lt_card⟩ ⟨v, hv_lt_card⟩).mpr hlt
    · -- Free case: bit u of predMaskOf[v] follows from maskOfRec characterization.
      have hfreeUVOf_size : (freeUVOf L).size =
          (Case3Enum.enumFreeUVOf L.w (bandSizes L)).size := by
        unfold freeUVOf; rfl
      have hfreeUVOf_getD : (freeUVOf L).getD k (0, 0) =
          (Case3Enum.enumFreeUVOf L.w (bandSizes L)).getD k (0, 0) := by
        unfold freeUVOf; rfl
      have hk_freeUVOf : k < (freeUVOf L).size := by rw [hfreeUVOf_size]; exact hk_lt
      have hbit_predMask :
          Nat.testBit ((predMaskOf L).getD ((freeUVOf L).getD k (0, 0)).2 0)
            ((freeUVOf L).getD k (0, 0)).1 = true := by
        unfold maskOf at hbit_mask
        rw [testBit'_eq_testBit, testBit_maskOfRec_lt _ _ _ _ hk_freeUVOf] at hbit_mask
        exact hbit_mask
      rw [hfreeUVOf_getD, hfreeUV_eq] at hbit_predMask
      exact hbit_predMask
  · -- (⇐) bit set in predMaskOf ⟹ bit set in enumPredPreWarshallOf
    intro h
    -- Extract bound and band info from the predMaskOf bit.
    have hbound := testBit'_predMaskOf_bound L v u
        (by rw [testBit'_eq_testBit]; exact h)
    obtain ⟨hv_lt_card, hu_lt_card⟩ := hbound
    -- band(symm u) < band(symm v)
    have hband_lt : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) <
        L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) :=
      bandMajorEquiv_band_lt_of_predMask_bit L
        ⟨u, hu_lt_card⟩ ⟨v, hv_lt_card⟩ h
    -- Set i = band(symm u) - 1, j = band(symm v) - 1.
    set i : Nat := L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) - 1 with hi_def
    set j : Nat := L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) - 1 with hj_def
    have hbandU_pos : 1 ≤ L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) :=
      L.band_pos _
    have hbandV_pos : 1 ≤ L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) :=
      L.band_pos _
    have hbandU_le : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) ≤ L.K :=
      L.band_le _
    have hbandV_le : L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) ≤ L.K :=
      L.band_le _
    have hij : i < j := by omega
    have hjK : j < L.K := by omega
    -- u and v are in band rectangles.
    have hu_ge : bandOffset L i ≤ u := by
      have := bandOffset_le_bandMajorEquiv_apply_val L ((bandMajorEquiv L).symm
        ⟨u, hu_lt_card⟩)
      have heq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩)).val = u := by
        rw [Equiv.apply_symm_apply]
      rw [heq] at this
      have hii : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) - 1 = i := rfl
      omega
    have hu_lt : u < bandOffset L (i + 1) := by
      have := bandMajorEquiv_apply_val_lt L ((bandMajorEquiv L).symm
        ⟨u, hu_lt_card⟩)
      have heq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩)).val = u := by
        rw [Equiv.apply_symm_apply]
      rw [heq] at this
      have hisucc : L.band ((bandMajorEquiv L).symm ⟨u, hu_lt_card⟩) = i + 1 := by omega
      rw [hisucc] at this
      exact this
    have hv_ge : bandOffset L j ≤ v := by
      have := bandOffset_le_bandMajorEquiv_apply_val L ((bandMajorEquiv L).symm
        ⟨v, hv_lt_card⟩)
      have heq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩)).val = v := by
        rw [Equiv.apply_symm_apply]
      rw [heq] at this
      have hjj : L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) - 1 = j := rfl
      omega
    have hv_lt : v < bandOffset L (j + 1) := by
      have := bandMajorEquiv_apply_val_lt L ((bandMajorEquiv L).symm
        ⟨v, hv_lt_card⟩)
      have heq : (bandMajorEquiv L ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩)).val = v := by
        rw [Equiv.apply_symm_apply]
      rw [heq] at this
      have hjsucc : L.band ((bandMajorEquiv L).symm ⟨v, hv_lt_card⟩) = j + 1 := by omega
      rw [hjsucc] at this
      exact this
    -- Translate bandOffset to (offsetsOf (bandSizes L)).
    have hoff_i : (Case3Enum.offsetsOf (bandSizes L)).getD i 0 = bandOffset L i :=
      offsetsOf_bandSizes_getD L i (by omega)
    have hoff_isucc :
        (Case3Enum.offsetsOf (bandSizes L)).getD (i + 1) 0 = bandOffset L (i + 1) :=
      offsetsOf_bandSizes_getD L (i + 1) (by omega)
    have hoff_j : (Case3Enum.offsetsOf (bandSizes L)).getD j 0 = bandOffset L j :=
      offsetsOf_bandSizes_getD L j (by omega)
    have hoff_jsucc :
        (Case3Enum.offsetsOf (bandSizes L)).getD (j + 1) 0 = bandOffset L (j + 1) :=
      offsetsOf_bandSizes_getD L (j + 1) (by omega)
    have hjK' : j < (bandSizes L).length := by rw [bandSizes_length]; omega
    -- v < enumNOf (bandSizes L) follows from v < Fintype.card α + §1.
    have hv_enumNOf : v < Case3Enum.enumNOf (bandSizes L) := by
      rw [enumNOf_bandSizes_eq_card]; exact hv_lt_card
    -- Two cases on j - i vs L.w.
    by_cases hgap : j - i > L.w
    · -- Forced case: apply testBit_enumPredPreWarshallOf_of_forced.
      apply Case3Enum.testBit_enumPredPreWarshallOf_of_forced _ _ _ _ hv_enumNOf
      rw [Case3Enum.mem_enumForcedUVOf_iff]
      refine ⟨i, j, hij, hjK', hgap, ?_, ?_, ?_, ?_⟩
      · rw [hoff_i]; exact hu_ge
      · rw [hoff_isucc]; exact hu_lt
      · rw [hoff_j]; exact hv_ge
      · rw [hoff_jsucc]; exact hv_lt
    · -- Free case: apply testBit_enumPredPreWarshallOf_of_free.
      have hgap' : j - i ≤ L.w := Nat.not_lt.mp hgap
      have hmem_free : (u, v) ∈ (Case3Enum.enumFreeUVOf L.w (bandSizes L)).toList := by
        rw [Case3Enum.mem_enumFreeUVOf_iff]
        refine ⟨i, j, hij, hjK', hgap', ?_, ?_, ?_, ?_⟩
        · rw [hoff_i]; exact hu_ge
        · rw [hoff_isucc]; exact hu_lt
        · rw [hoff_j]; exact hv_ge
        · rw [hoff_jsucc]; exact hv_lt
      -- Extract position k.
      obtain ⟨k, hk_lt, hk_eq⟩ :=
        (mem_toList_iff_exists_getD _ u v).mp hmem_free
      apply Case3Enum.testBit_enumPredPreWarshallOf_of_free _ _ _ _ hv_enumNOf
      refine ⟨k, hk_lt, ?_, hk_eq⟩
      -- bit k of maskOf L is set: by maskOfRec characterization with freeUV[k] = (u, v).
      have hk_freeUVOf : k < (freeUVOf L).size := by unfold freeUVOf; exact hk_lt
      have hbit_pred :
          Nat.testBit ((predMaskOf L).getD ((freeUVOf L).getD k (0, 0)).2 0)
            ((freeUVOf L).getD k (0, 0)).1 = true := by
        have : (freeUVOf L).getD k (0, 0) = (u, v) := by
          unfold freeUVOf; exact hk_eq
        rw [this]; exact h
      unfold maskOf
      rw [testBit'_eq_testBit, testBit_maskOfRec_lt _ _ _ _ hk_freeUVOf]
      exact hbit_pred

/-- **§8 — `enumPredAtMaskOf = predMaskOf` construction-equivalence**
(A5-G3c, `mg-9568`).

The headline equality used by F5a's bridge: the imperative
post-warshall predecessor mask construction `enumPredAtMaskOf` at
`mask = maskOf L` equals the abstract `predMaskOf L`.

The proof reduces the `enumPredAtMaskOf` definition through:
1. `enumPredPreWarshallOf L.w (bandSizes L) (maskOf L) = predMaskOf L`
   — by `Array.ext` + bit-by-bit equality
   (`testBit_enumPredPreWarshallOf_iff_testBit_predMaskOf`).
2. `enumNOf (bandSizes L) = Fintype.card α` (`enumNOf_bandSizes_eq_card`).
3. `warshall (predMaskOf L) (Fintype.card α) = predMaskOf L`
   (`predMaskOf_warshall`). -/
theorem enumPredAtMaskOf_eq_predMaskOf (L : LayeredDecomposition α) :
    Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L) = predMaskOf L := by
  classical
  -- First, show enumPredPreWarshallOf w bs (maskOf L) = predMaskOf L.
  have hpre_eq :
      Case3Enum.enumPredPreWarshallOf L.w (bandSizes L) (maskOf L) =
        predMaskOf L := by
    apply Array.ext
    · -- Sizes equal: both equal Fintype.card α.
      rw [Case3Enum.enumPredPreWarshallOf_eq,
          Case3Enum.foldl_maskedFreeBody_size, Case3Enum.addEdgesList_size,
          Array.size_replicate, enumNOf_bandSizes_eq_card, size_predMaskOf]
    · -- Per-entry equality: both sides are Nat, so use Nat.eq_of_testBit_eq.
      intro v hv1 _hv2
      apply Nat.eq_of_testBit_eq
      intro u
      -- Reduce getElem to getD via the in-bounds witness, then apply the
      -- bit-equivalence lemma.
      have hLHS : (Case3Enum.enumPredPreWarshallOf L.w (bandSizes L)
          (maskOf L))[v] = (Case3Enum.enumPredPreWarshallOf L.w (bandSizes L)
          (maskOf L)).getD v 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hv1]; rfl
      have hRHS : (predMaskOf L)[v] = (predMaskOf L).getD v 0 := by
        have hv2_size : v < (predMaskOf L).size := by
          rw [size_predMaskOf]
          have : (Case3Enum.enumPredPreWarshallOf L.w (bandSizes L)
              (maskOf L)).size = Case3Enum.enumNOf (bandSizes L) := by
            rw [Case3Enum.enumPredPreWarshallOf_eq,
                Case3Enum.foldl_maskedFreeBody_size,
                Case3Enum.addEdgesList_size, Array.size_replicate]
          rw [this, enumNOf_bandSizes_eq_card] at hv1
          exact hv1
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hv2_size]; rfl
      rw [hLHS, hRHS]
      -- Two booleans are equal iff (true ↔ true).
      rcases hcase_lhs : Nat.testBit ((Case3Enum.enumPredPreWarshallOf L.w
          (bandSizes L) (maskOf L)).getD v 0) u with _ | _
      · rcases hcase_rhs : Nat.testBit ((predMaskOf L).getD v 0) u with _ | _
        · rfl
        · exfalso
          exact Bool.false_ne_true (hcase_lhs.symm.trans
            ((testBit_enumPredPreWarshallOf_iff_testBit_predMaskOf L u v).mpr
              hcase_rhs))
      · rcases hcase_rhs : Nat.testBit ((predMaskOf L).getD v 0) u with _ | _
        · exfalso
          exact Bool.false_ne_true (hcase_rhs.symm.trans
            ((testBit_enumPredPreWarshallOf_iff_testBit_predMaskOf L u v).mp
              hcase_lhs))
        · rfl
  -- Now combine.
  unfold Case3Enum.enumPredAtMaskOf
  rw [hpre_eq, enumNOf_bandSizes_eq_card, predMaskOf_warshall]

end OneThird.Step8
