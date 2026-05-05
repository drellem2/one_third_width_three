/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BoundedIrreducibleBalancedInScope
import OneThird.Step8.Case3Enum.AllBalancedBridge

/-!
# Step 8 — Option-C K=2 substantive closure (`mg-01ec`)

The **Option-C K=2 substantive closure**: for every layered width-3
poset `β` with `LB.K = 2`, `2 ≤ Fintype.card β`, and `¬
LayerOrdinalReducible LB 1` (i.e. `LB` is layer-ordinal-sum
irreducible at the only valid cut index), `β` admits a balanced
pair (`HasBalancedPair β`).

The closure is the **substantive new content** of the Option-C
execution arc per `mg-fefe`'s AMBER verdict: it discharges the
`K = 2` portion of `Step8.Case3Witness.{u}` by direct enumeration
over the 40-class layered-irreducible width-3 K=2 catalog of
`mg-e112` §A, **bypassing the provably-false `Case2FKGSubClaim`**
per `docs/path-c-cleanup-roadmap.md` §6b.

## Architecture

The original ticket architecture (`mg-01ec` §"Architecture") split
the discharge into

```
if F1-inactive then
  -- 8 F1-inactive classes via N-poset-core extraction
  n_poset_core_balanced_pair LB
else
  -- 32 F1-active classes via Bool certificate
  case_2_strict_bool_certificate LB
```

The **realised architecture is unified**: the F5a Bool certificate
infrastructure (`Case3Enum.enumPosetsFor`,
`Case3Enum.hasBalancedPair`) handles **all 40 classes uniformly**.
The F1-active/F1-inactive distinction is mathematically clean (per
`mg-fefe` Deliverable A) but architecturally redundant — every
F1-inactive K=2 irreducible width-3 poset of size `≤ 6`
admits a balanced pair via the same enumeration as the F1-active
classes (the slow-path linear-extension DP discovers the
N-poset-induced balanced pair without an explicit
N-core extraction). Deliberate PM decision: avoid duplicating the
Deliverable A structural argument inside Lean when the certificate
already covers the case.

The 8 reducible classes (per the catalog) are excluded by the
`hIrred : ¬ LayerOrdinalReducible LB 1` hypothesis.

## Bool certificate

The K=2 specialisation of `Case3Enum.allBalanced` enumerates over
`bandSizesGen 2 6` (the 9 band-size tuples `[m, n] ∈ {1,2,3}^2`
with `m + n ≤ 6`); the Bool decision-procedure
`Case3Enum.enumPosetsFor 1 [m, n]` returns `true` iff every layered
K=2 irreducible width-3 poset on `[m, n]` admits a balanced pair.

For K=2 with `w ≥ 1`, `(L2-forced)` is vacuous (since `band x +
w < band y` requires `band y > band x + w ≥ 2`, but `band y ≤ K
= 2`), so the partition phase of `enumPosetsFor` always classifies
all cross-pairs as **free** at any `w ≥ 1` — a single certificate
slice at `w = 1` covers every layered decomposition with `K = 2`
and `L.w ≥ 1`. The `L.w = 0` regime is vacuous: combined with
`K = 2` it forces every `(band 1, band 2)` cross-pair to be `<`
in `LB`, which is `LayerOrdinalReducible LB 1`, contradicting
`hIrred`.

## Reference

* `mg-01ec` — this work item (ticket: Option-C execution arc K=2
  substantive closure).
* `mg-fefe` — the validation arc whose AMBER verdict gated this
  execution arc.
* `mg-fefe` Deliverable A
  (`docs/option-c-validation-arc-1/f1-inactive-n-core-proof.md`)
  — F1-inactive ⇒ N-poset-core uniform paper-level proof
  (referenced for completeness; not consumed by the Lean proof).
* `mg-fefe` Deliverable B
  (`docs/option-c-validation-arc-1/signature-design.md`)
  — Candidate A signature analysis (preserves
  `Case3Witness.{u}` universal scope).
* `mg-e112` §A
  (`docs/proof-approaches-catalog-1/obstruction-enumeration.md`)
  — 40-class catalog (32 F1-active + 8 F1-inactive irreducible;
  8 reducibles excluded by `hIrred`).
* `mg-e112` §C
  (`docs/proof-approaches-catalog-1/in-tree-primitive-inventory.md`)
  — primitive inventory; `case3_certificate` Bool kit pattern at
  `lean/OneThird/Step8/Case3Enum/Certificate.lean` reused here.
* `docs/path-c-cleanup-roadmap.md` §6b — the K=2 finite enumerator
  alternative this implements.
* `docs/option-c-execution-arc/k2-closure-status.md` — verification
  status (LoC delta, axiom inventory, class coverage table).
-/

namespace OneThird
namespace Step8
namespace OptionC

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open Step8.Case3Enum (enumPosetsFor bandSizesGen)

/-! ### §1 — K=2 Bool certificate -/

set_option linter.style.nativeDecide false in
/-- **K=2 Bool certificate** (analogue of `case3_certificate`,
`mg-e112` §C; this ticket: `mg-01ec`).

For every band-size tuple `bs ∈ bandSizesGen 2 6`, every layered
width-3 irreducible K=2 poset on `bs` with an adjacent
incomparable cross-pair admits a balanced pair.

Verified by `native_decide` over the 9 band-size tuples
`[m, n]` with `m, n ∈ {1, 2, 3}` and `m + n ≤ 6`. The interaction
width `w` is fixed at `1`: for K=2, the only band-pair gap is `1`,
so any `w ≥ 1` makes `(L2-forced)` vacuous and the enumeration is
`w`-independent at `w ≥ 1`. The `w = 0` regime is structurally
excluded by `hIrred` in the Prop-level closure (see §3).

Per the F5a-ℓ pattern: the only axiom this contributes to
downstream `#print axioms` is `Lean.ofReduceBool` from
`native_decide` itself — no new project axioms. -/
theorem case2_certificate :
    ∀ bs ∈ bandSizesGen 2 6, enumPosetsFor 1 bs = true := by
  native_decide

/-! ### §2 — Per-`bandSizes` certificate consumption

Specialise `case2_certificate` to a concrete `bandSizes L` for any
`L : LayeredDecomposition β` with `L.K = 2` and bands non-empty,
producing the F5a-style `enumPosetsFor 1 (bandSizes L) = true`
fact consumed by the in-scope bridge of §3. -/

variable {β : Type*} [PartialOrder β] [Fintype β] [DecidableEq β]

/-- For a K=2 layered decomposition with bands non-empty and
`Fintype.card β ≤ 6`, the F5a Bool fact at `w = 1` holds for
`bandSizes L`. -/
lemma enumPosetsFor_bandSizes_eq_true_of_K2
    (L : LayeredDecomposition β) (hK2 : L.K = 2)
    (hCardLe : Fintype.card β ≤ 6)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → 1 ≤ bandSize L k) :
    enumPosetsFor 1 (bandSizes L) = true := by
  have hMem : bandSizes L ∈ bandSizesGen 2 6 := by
    have h := bandSizes_mem_bandSizesGen L 6 hCardLe hNonempty
    rwa [hK2] at h
  exact case2_certificate (bandSizes L) hMem

/-! ### §3 — K=2 width-1 sister decomposition

For any `L : LayeredDecomposition β` with `L.K = 2`, the band map
already satisfies `(L2-forced)` for every `w' ≥ 0`: at K=2, the
hypothesis `band x + w' < band y` is satisfiable only for `w' = 0`
(forced regime), and for `w' ≥ 1` it is vacuous. We construct the
**w=1 sister** decomposition `normalizeWAtK2 L hK2`, sharing every
field with `L` except `w := 1`.

The sister is needed because `freeUVOf L`, `maskOf L`, and the
F5a bridge artifacts depend on `L.w` (via `enumFreeUVOf L.w
(bandSizes L)`); the certificate is at `w = 1`, so we lift the
closure through the sister whose `w` matches the certificate. -/

/-- The `w = 1` sister of a K=2 layered decomposition. Same
band map, same `K`, same partial order on `β`; only the recorded
interaction width changes to `1`. The (L2-forced) axiom is
vacuously satisfied at `w = 1` for K=2 since `band x + 1 < band y`
requires `band y ≥ 3 > 2 = K`. -/
def normalizeWAtK2 (L : LayeredDecomposition β) (hK2 : L.K = 2) :
    LayeredDecomposition β where
  K := L.K
  w := 1
  band := L.band
  band_pos := L.band_pos
  band_le := L.band_le
  band_size := L.band_size
  band_antichain := L.band_antichain
  forced_lt := by
    intro x y h
    -- `band x + 1 < band y` is impossible at K = 2.
    exfalso
    have h1 := L.band_pos x
    have h2 := L.band_le y
    rw [hK2] at h2
    omega
  cross_band_lt_upward := L.cross_band_lt_upward

@[simp] lemma normalizeWAtK2_K (L : LayeredDecomposition β)
    (hK2 : L.K = 2) :
    (normalizeWAtK2 L hK2).K = L.K := rfl

@[simp] lemma normalizeWAtK2_w (L : LayeredDecomposition β)
    (hK2 : L.K = 2) :
    (normalizeWAtK2 L hK2).w = 1 := rfl

@[simp] lemma normalizeWAtK2_band (L : LayeredDecomposition β)
    (hK2 : L.K = 2) :
    (normalizeWAtK2 L hK2).band = L.band := rfl

@[simp] lemma normalizeWAtK2_bandSet (L : LayeredDecomposition β)
    (hK2 : L.K = 2) (k : ℕ) :
    (normalizeWAtK2 L hK2).bandSet k = L.bandSet k := rfl

@[simp] lemma bandSize_normalizeWAtK2 (L : LayeredDecomposition β)
    (hK2 : L.K = 2) (k : ℕ) :
    bandSize (normalizeWAtK2 L hK2) k = bandSize L k := rfl

@[simp] lemma bandSizes_normalizeWAtK2 (L : LayeredDecomposition β)
    (hK2 : L.K = 2) :
    bandSizes (normalizeWAtK2 L hK2) = bandSizes L := rfl

/-- The sister inherits layer-ordinal-irreducibility from `L`
(both share the same band map and the same partial order on `β`,
so `LayerOrdinalReducible` agrees on the two). -/
lemma normalizeWAtK2_layerOrdinalIrreducible
    {γ : Type*} [PartialOrder γ] [Fintype γ]
    (L : LayeredDecomposition γ) (hK2 : L.K = 2)
    (hIrr : LayerOrdinalIrreducible L) :
    LayerOrdinalIrreducible (normalizeWAtK2 L hK2) := by
  classical
  intro k hk1 hk_lt
  -- `(normalizeWAtK2 L hK2).K = L.K` and band map is shared, so
  -- `LayerOrdinalReducible` on the sister is `LayerOrdinalReducible L`.
  exact hIrr k hk1 hk_lt

/-! ### §4 — K=2 in-scope Prop bridge (sister applied)

Mirrors the body of `Step8.bounded_irreducible_balanced_inScope`
(`BoundedIrreducibleBalancedInScope.lean`) for the K=2 sister
decomposition with `w = 1`. The proof is structurally identical
except that `hK : 2 ≤ L.K` is derived directly from `hK2 : L.K = 2`
rather than extracted from `InCase3Scope`. -/

/-- **K=2 in-scope Bool→Prop bridge** (this ticket: `mg-01ec`).

For a layered decomposition `L` with `L.K = 2`, `L.w = 1`, layered-
ordinal-sum irreducible, with all bands non-empty and the F5a Bool
fact `enumPosetsFor 1 (bandSizes L) = true`, `α` admits a balanced
pair.

The proof reuses every K-agnostic helper from
`BoundedIrreducibleBalancedInScope.lean`:

* `enumPredAtMaskOf_eq_predMaskOf L` (G3c, `mg-9568`) — the
  construction-equivalence between F5a's per-mask pred and `L`'s
  band-major pred.
* `irreducible_predMaskOf_offsetsOf_eq_true L hIrr` (B1', `mg-a08f`)
  — irreducibility ⇒ Bool `irreducible` gate.
* `hasAdjacentIncomp_predMaskOf_eq_true L hK hIrr hNonempty …`
  (B2, `mg-e9d6`) — irreducibility ⇒ Bool `hasAdjacentIncomp`
  gate. **Only this step uses `2 ≤ L.K`**, derived here from
  `hK2 : L.K = 2`.
* `Case3Enum.findSymmetricPair_isSome_imp_symmetric` — fast-path
  Bool→Prop lift.
* `Case3Enum.enumPosetsFor_iter_balanced` (G1', `mg-b487`) — inner
  per-mask iteration theorem.
* `Case3Enum.hasBalancedPair_of_hasBalancedPair` and
  `hasBalancedPair_of_predOrder_orderIso` — the final lift to
  `HasBalancedPair α`.
-/
theorem option_c_K2_closure_inScope_at_w1
    {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : LayeredDecomposition α)
    (hK2 : L.K = 2)
    (hIrr : LayerOrdinalIrreducible L)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → 1 ≤ bandSize L k)
    (h_certificate : enumPosetsFor L.w (bandSizes L) = true) :
    HasBalancedPair α := by
  classical
  -- Construction-equivalence (G3c).
  have h_construction_eq :
      Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L) =
        predMaskOf L := enumPredAtMaskOf_eq_predMaskOf L
  have h_freeUV_eq :
      Case3Enum.enumFreeUVOf L.w (bandSizes L) = freeUVOf L := rfl
  -- Bool ↔ Prop bridge inputs (validity, bit-bound, size).
  have hValid : Case3Enum.ValidPredMask (predMaskOf L) (Fintype.card α) :=
    (predMaskOf_isValid L).toValidPredMask
  have h_bnd : Case3Enum.predBitsBoundedBy (predMaskOf L)
      (Fintype.card α) := predBitsBoundedBy_predMaskOf L
  have h_size : (predMaskOf L).size = Fintype.card α := size_predMaskOf L
  -- Fast-path symmetric-pair lift (G3a).
  have h_sym_lift :
      (Case3Enum.findSymmetricPair (predMaskOf L)
            (Fintype.card α)).isSome = true →
        ∃ x y : Fin (Fintype.card α),
          Case3Enum.Symmetric (predMaskOf L) (Fintype.card α) x y :=
    fun h =>
      Case3Enum.findSymmetricPair_isSome_imp_symmetric
        (predMaskOf L) (Fintype.card α) h
  -- Bool-level `hasBalancedPair` at L's band-major encoding.
  have h_bal :
      Case3Enum.hasBalancedPair (predMaskOf L) (Fintype.card α) = true := by
    unfold Case3Enum.hasBalancedPair
    cases hsymopt :
        Case3Enum.findSymmetricPair (predMaskOf L) (Fintype.card α) with
    | some _ => rfl
    | none =>
      -- Slow path: discharge via the iteration theorem at `mask = maskOf L`.
      have hN_eq : Case3Enum.enumNOf (bandSizes L) = Fintype.card α :=
        enumNOf_bandSizes_eq_card L
      -- Loop-range membership.
      have hmask :
          maskOf L < 1 <<< Case3Enum.enumNfreeOf L.w (bandSizes L) := by
        change maskOf L <
          1 <<< (Case3Enum.enumFreeUVOf L.w (bandSizes L)).size
        rw [h_freeUV_eq, Nat.one_shiftLeft]
        exact maskOf_lt_two_pow_size L
      -- Closure-canonical gate.
      have hcanon :
          Case3Enum.closureCanonical
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (maskOf L)
              (Case3Enum.enumFreeUVOf L.w (bandSizes L)) = true := by
        rw [h_construction_eq, h_freeUV_eq]
        exact closureCanonical_predMaskOf L
      -- No symmetric pair gate.
      have hsym_gate :
          (Case3Enum.findSymmetricPair
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.enumNOf (bandSizes L))).isSome = false := by
        rw [h_construction_eq, hN_eq, hsymopt]; rfl
      -- Irreducibility gate (B1').
      have hirr_gate :
          Case3Enum.irreducible
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.offsetsOf (bandSizes L)) = true := by
        rw [h_construction_eq]
        exact irreducible_predMaskOf_offsetsOf_eq_true L hIrr
      -- Adjacent-incomparable gate (B2). The **only** K-specific step.
      have hadj_gate :
          Case3Enum.hasAdjacentIncomp
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.offsetsOf (bandSizes L)) = true := by
        rw [h_construction_eq]
        have hK : 2 ≤ L.K := by rw [hK2]
        have hNonemptyBand :
            ∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty := by
          intro k hk1 hk2
          have hcard : 0 < (L.bandSet k).card := hNonempty k hk1 hk2
          exact Finset.card_pos.mp hcard
        refine hasAdjacentIncomp_predMaskOf_eq_true L hK hIrr
          hNonemptyBand (Case3Enum.offsetsOf (bandSizes L)) ?_ ?_ ?_
        · rw [offsetsOf_bandSizes_size L]
        · intro x
          have hb_le : L.band x - 1 ≤ L.K := by
            have := L.band_le x; omega
          rw [offsetsOf_bandSizes_getD L _ hb_le]
          exact bandOffset_le_bandMajorEquiv_apply_val L x
        · intro x
          rw [offsetsOf_bandSizes_getD L _ (L.band_le x)]
          exact bandMajorEquiv_apply_val_lt L x
      -- Apply the inner iteration theorem (G1').
      have h_slow_at_iter :
          Case3Enum.hasBalancedPairSlow
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.enumNOf (bandSizes L)) = true :=
        Case3Enum.enumPosetsFor_iter_balanced L.w (bandSizes L)
          h_certificate (maskOf L) hmask hcanon hsym_gate hirr_gate hadj_gate
      rw [h_construction_eq, hN_eq] at h_slow_at_iter
      exact h_slow_at_iter
  -- Lift the Bool fact to `HasBalancedPair (Fin n) [predOrder]`.
  have hBalFin :
      @HasBalancedPair (Fin (Fintype.card α))
        (Case3Enum.predOrder (predMaskOf L) hValid) _ _ :=
    Case3Enum.hasBalancedPair_of_hasBalancedPair hValid h_bnd h_size
      h_sym_lift h_bal
  -- Transport via `bandMajorOrderIso_predOrder L` (G3b).
  exact hasBalancedPair_of_predOrder_orderIso hValid
    (bandMajorOrderIso_predOrder L) hBalFin

/-! ### §5 — K=2 width transparency

For a K=2 layered decomposition `L` with `L.w ≥ 1`, the `w = 1`
sister `normalizeWAtK2 L hK2` has the **same partial order** on
`β` (band map and forced/upward axioms are shared; only `L.w`
changes). Hence `HasBalancedPair β` for the sister implies the
same for `L`. -/

/-- Both bands of a K=2 layered-ordinal-irreducible decomposition
are non-empty. (If band 1 (resp. band 2) were empty, `(L2-forced)`-
free reducibility at `k = 1` would hold vacuously, contradicting
irreducibility.) -/
lemma bands_nonempty_of_K2_irreducible
    {γ : Type*} [PartialOrder γ] [Fintype γ]
    (L : LayeredDecomposition γ) (hK2 : L.K = 2)
    (hIrred : ¬ LayerOrdinalReducible L 1) :
    ∀ k : ℕ, 1 ≤ k → k ≤ L.K → 1 ≤ bandSize L k := by
  classical
  intro k hk1 hkK
  rw [hK2] at hkK
  -- `k ∈ {1, 2}`.
  by_contra hcontra
  push Not at hcontra
  have hzero : bandSize L k = 0 := by omega
  -- bandSize = 0 ⇒ bandSet k is empty.
  have hempty : L.bandSet k = ∅ := by
    rw [Finset.card_eq_zero.mp hzero]
  apply hIrred
  -- LayerOrdinalReducible L 1: ∀ u v, band u ≤ 1 → 1 < band v → u < v.
  intro u v hu hv
  -- We split on whether band u or band v lies in the empty band, deriving
  -- a vacuous-hypothesis contradiction in each case.
  interval_cases k
  · -- k = 1: band 1 is empty. But hu : band u ≤ 1 and band_pos gives band u = 1.
    -- So u ∈ bandSet 1 = ∅, contradiction.
    have hu1 : L.band u = 1 := le_antisymm hu (L.band_pos u)
    have hu_mem : u ∈ L.bandSet 1 := by
      rw [LayeredDecomposition.mem_bandSet]; exact hu1
    rw [hempty] at hu_mem
    exact absurd hu_mem (Finset.notMem_empty u)
  · -- k = 2: band 2 is empty. hv : 1 < band v and band_le gives band v ≤ K = 2,
    -- so band v = 2; then v ∈ bandSet 2 = ∅, contradiction.
    have hv_le : L.band v ≤ 2 := by rw [← hK2]; exact L.band_le v
    have hv2 : L.band v = 2 := by omega
    have hv_mem : v ∈ L.bandSet 2 := by
      rw [LayeredDecomposition.mem_bandSet]; exact hv2
    rw [hempty] at hv_mem
    exact absurd hv_mem (Finset.notMem_empty v)

/-- For a K=2 layered decomposition, `Fintype.card γ ≤ 6` (since
each band has ≤ 3 elements by `(L1)` and `K = 2`). -/
lemma card_le_six_of_K2
    {γ : Type*} [PartialOrder γ] [Fintype γ]
    (L : LayeredDecomposition γ) (hK2 : L.K = 2) :
    Fintype.card γ ≤ 6 := by
  classical
  have hsum : (Finset.range L.K).sum (fun i => bandSize L (i + 1)) =
      Fintype.card γ := sum_bandSize_eq_card L
  rw [hK2] at hsum
  rw [← hsum]
  -- range 2 = {0, 1}; sum bandSize ≤ 3 + 3 = 6.
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  change bandSize L (0 + 1) + bandSize L (0 + 1 + 1) ≤ 6
  have h1 : bandSize L (0 + 1) ≤ 3 := bandSize_le_three L (0 + 1)
  have h2 : bandSize L (0 + 1 + 1) ≤ 3 := bandSize_le_three L (0 + 1 + 1)
  omega

/-! ### §6 — Main theorem: `option_c_K2_closure` -/

/-- **`option_c_K2_closure`** (substantive deliverable of `mg-01ec`).

The Option-C K=2 substantive closure: for every layered width-3
poset `β` with `LB.K = 2`, `2 ≤ Fintype.card β`, and `LB`
layer-ordinal-sum irreducible (i.e. `¬ LayerOrdinalReducible LB
1`, which is equivalent to `LayerOrdinalIrreducible LB` at K=2),
`β` admits a balanced pair.

**Proof (architecture).**

1. **`LB.w = 0`** is structurally excluded: K=2 with `w = 0` makes
   `(L2-forced)` operative on every cross-pair `(band 1, band 2)`,
   which is exactly `LayerOrdinalReducible LB 1`, contradicting
   `hIrred`.

2. **`LB.w ≥ 1`** is dispatched via the **w=1 sister**
   `LB' := normalizeWAtK2 LB hK2` (same partial order; only the
   recorded interaction width changes). The sister's `bandSizes`
   is `bandSizes LB`, and the F5a K=2 Bool certificate
   (`case2_certificate`, §1) supplies `enumPosetsFor 1 (bandSizes
   LB) = true` via `enumPosetsFor_bandSizes_eq_true_of_K2`. The
   in-scope bridge `option_c_K2_closure_inScope_at_w1` (§4) then
   yields `HasBalancedPair β`.

The hypotheses `hP : HasWidthAtMost β 3` and `hNonChain : ¬
IsChainPoset β` are not strictly required by the proof body
(width-3 follows from `LB`'s `(L1)` band-size ≤ 3 axiom + K=2,
giving `|β| ≤ 6`; non-chain is recovered from the K=2 +
irreducibility regime via the existence of the adjacent
incomparable cross-pair witnessed by `exists_adjacent_not_lt_of_irreducible`).
They are kept in the signature for downstream consumer alignment
with the Candidate A signature of `mg-fefe` Deliverable B.

**Class coverage** (40-class K=2 width-3 layered-irreducible
catalog of `mg-e112` §A):

* 32 F1-active classes — covered by the Bool certificate.
* 8 F1-inactive classes (3-element antichains, 4-element
  N-poset, and the |α|∈{5,6} antichain-extension classes
  `K2-N5-{2,3}` and `K2-N6-{...}`) — also covered by the same
  Bool certificate (the slow-path linear-extension DP in
  `Case3Enum.hasBalancedPair` discovers a balanced pair without
  an explicit N-poset-core extraction).
* 8 reducible classes — excluded by `hIrred`.

See `docs/option-c-execution-arc/k2-closure-status.md` for
LoC delta, axiom inventory, and the per-class coverage table.

**Axiom audit.** `#print axioms option_c_K2_closure` reports
`[propext, Classical.choice, Quot.sound, Lean.ofReduceBool]` —
the existing `Lean.ofReduceBool` from `native_decide` (consumed
by `case2_certificate`'s decision procedure) plus the standard
mathlib trio. **No new project axioms.** -/
theorem option_c_K2_closure
    (LB : Step8.LayeredDecomposition β)
    (_hP : HasWidthAtMost β 3) (_hNonChain : ¬ IsChainPoset β)
    (hK2 : LB.K = 2) (_hCard : 2 ≤ Fintype.card β)
    (hIrred : ¬ Step8.LayerOrdinalReducible LB 1) :
    HasBalancedPair β := by
  classical
  -- §6.1 — Convert `hIrred` to `LayerOrdinalIrreducible LB`.
  have hIrr : Step8.LayerOrdinalIrreducible LB := by
    intro k hk1 hkK
    rw [hK2] at hkK
    have hkeq : k = 1 := by omega
    subst hkeq
    exact hIrred
  -- §6.2 — Case on `LB.w`.
  by_cases hw0 : LB.w = 0
  · -- §6.3 — `LB.w = 0` ⇒ contradiction with `hIrred`.
    exfalso
    apply hIrred
    intro u v hu hv
    apply LB.forced_lt
    rw [hw0]; omega
  · -- §6.4 — `LB.w ≥ 1`: dispatch via the w=1 sister.
    have hw1_le : 1 ≤ LB.w := Nat.pos_of_ne_zero hw0
    -- Build the w=1 sister.
    let LB' := normalizeWAtK2 LB hK2
    have hLB'_K2 : LB'.K = 2 := hK2
    have hLB'_w1 : LB'.w = 1 := rfl
    have hLB'_irr : Step8.LayerOrdinalIrreducible LB' :=
      normalizeWAtK2_layerOrdinalIrreducible LB hK2 hIrr
    -- Band-non-emptiness on LB transports to LB'.
    have hNonemptyLB := bands_nonempty_of_K2_irreducible LB hK2 hIrred
    have hNonempty' : ∀ k : ℕ, 1 ≤ k → k ≤ LB'.K → 1 ≤ bandSize LB' k := by
      intro k hk1 hkK
      rw [bandSize_normalizeWAtK2]
      exact hNonemptyLB k hk1 hkK
    -- Card-bound on LB transports to LB' (same band map and `K`).
    have hCardLe : Fintype.card β ≤ 6 := card_le_six_of_K2 LB hK2
    -- Certificate at w=1 specialised to LB' = LB on the band-side.
    have h_cert : enumPosetsFor LB'.w (bandSizes LB') = true := by
      rw [hLB'_w1, bandSizes_normalizeWAtK2]
      exact enumPosetsFor_bandSizes_eq_true_of_K2 LB hK2 hCardLe hNonemptyLB
    -- Apply the in-scope bridge to the sister. Both `hLB'_w1` and
    -- `hw1_le` are recorded for clarity but unused in the bridge body.
    have _ : LB'.w = 1 := hLB'_w1
    have _ : 1 ≤ LB.w := hw1_le
    exact option_c_K2_closure_inScope_at_w1 LB' hLB'_K2
      hLB'_irr hNonempty' h_cert

end OptionC
end Step8
end OneThird
