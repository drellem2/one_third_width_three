/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.BoundedIrreducibleBalanced
import OneThird.Step8.Case3Enum.IrreducibleBridge
import OneThird.Step8.Case3Enum.AdjIncompBridge
import OneThird.Step8.Case3Enum.BalancedLift
import OneThird.Step8.Case3Enum.EnumPosetsForBridge
import OneThird.Step8.Case3Enum.SymmetricLift
import OneThird.Step8.Case3Enum.PredMaskBridge

/-!
# Step 8 — A5-G3d: certificate-driven discharge of
`bounded_irreducible_balanced_inScope` (`mg-d783`, refactored
`mg-651f`)

Composes:

* G1' (`mg-b487`, merged) — `enumPosetsFor_iter_balanced`: the per-mask
  iteration theorem reducing the `enumPosetsFor w bs = true` Bool fact
  to a slow-path conclusion at any iteration mask satisfying the four
  Bool gates (`closureCanonical`, no symmetric pair, `irreducible`,
  `hasAdjacentIncomp`).
* G3a (`mg-609a`, merged) + G3a-followup (`mg-792a` /
  `successorMasks_testBit`, merged) — `findSymmetricPair_isSome_imp_symmetric`:
  Bool→Prop lift for the fast-path symmetric witness extraction, with
  the `successorMasks` bit-correctness obligation now discharged in-tree.
* G3b (`mg-59cf`, merged) — `hasBalancedPair_of_predOrder_orderIso`:
  the explicit-instance `OrderIso`-transport variant lifting a
  `Fin n`-side balanced pair through `bandMajorOrderIso_predOrder L`.
* G3c (`mg-9568`, merged) — `enumPredAtMaskOf_eq_predMaskOf`: the
  construction-equivalence is now provable in-tree from
  `cross_band_lt_upward` (mg-53ce / A5-G2 path 1) plus the bit
  characterizations of `enumPredPreWarshallOf` and `predMaskOf`. The
  free-UV alignment is `rfl` (`freeUVOf L` is *defined* as
  `Case3Enum.enumFreeUVOf L.w (bandSizes L)`).
* B1' (`mg-a08f`) — `irreducible_predMaskOf_offsetsOf_eq_true`:
  `LayerOrdinalIrreducible` ⇒ `Case3Enum.irreducible (predMaskOf L)
  (offsetsOf (bandSizes L)) = true`.
* B2 (`mg-e9d6`) — `hasAdjacentIncomp_predMaskOf_eq_true`:
  irreducibility ⇒ `Case3Enum.hasAdjacentIncomp (predMaskOf L) offsets
  = true` for the band-major offsets of `L`.
* B3 (`mg-0f0e`) — band-major positional alignment between the
  `bandMajorEquiv L` and `Case3Enum.offsetsOf (bandSizes L)`.

Plus the in-tree `closureCanonical_predMaskOf` and `predMaskOf_warshall`
witnesses to discharge the remaining gates.

The signature now carries only the two genuinely external obligations:

1. `hNonempty` — every band of `L` is non-empty (excludes the trivial
   case where `bandSizesGen` would not enumerate `L`'s tuple, and
   underwrites the `hasAdjacentIncomp` bridge).
2. `h_certificate` — `Case3Enum.enumPosetsFor L.w (bandSizes L) = true`,
   the F5a Bool fact specialised to `L`'s band-size list. Caller derives
   from `case3_certificate` together with `bandSizes_mem_bandSizesGen`
   and an `allBalanced` unrolling.

The previously-carried `h_construction_eq`, `h_freeUV_eq`, and `h_succ`
hypotheses (the G3c-followup and G3a-followup obligations of `mg-d783`)
are now discharged inline by `enumPredAtMaskOf_eq_predMaskOf` and
`findSymmetricPair_isSome_imp_symmetric`.

## Reference

`step8.tex` §`sec:g4-balanced-pair`, Proposition `prop:in-situ-balanced`
(`step8.tex:2965-2970`); F5a `case3_certificate`
(`OneThird.Step8.Case3Enum.case3_certificate`); `docs/a5-glue-status.md`
§§3-4.
-/

namespace OneThird
namespace Step8

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- **`bounded_irreducible_balanced_inScope`** (A5-G3d, `mg-d783`;
A5-G2 path 1 wiring closeout, `mg-651f`).

Certificate-driven discharge of the `InCase3Scope`-restricted form of
`prop:in-situ-balanced` (Case 3 of `step8.tex:2965-2970`). For any
layered width-3 poset `α` with a `LayeredDecomposition L` whose
parameter tuple `(L.w, Fintype.card α, L.K)` lies in F5a's certified
scope (`InCase3Scope`), `α` admits a balanced pair.

The proof composes G1'-G3a-G3b-G3c with the B1'-B2-B3 bridges and the
in-tree `closureCanonical_predMaskOf` / `predMaskOf_warshall` witnesses.
The construction-equivalence (`enumPredAtMaskOf_eq_predMaskOf`) and the
`successorMasks` bit-correctness (`successorMasks_testBit`) are now
discharged in-tree, leaving only the two genuinely external obligations:
band non-emptiness and the F5a Bool certificate fact for `L`'s
band-size list. -/
theorem bounded_irreducible_balanced_inScope
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hScope : InCase3Scope L.w (Fintype.card α) L.K)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → 1 ≤ bandSize L k)
    (h_certificate :
      Case3Enum.enumPosetsFor L.w (bandSizes L) = true) :
    HasBalancedPair α := by
  classical
  -- Construction-equivalence (G3c, `mg-9568`) and the `rfl`-form of
  -- `enumFreeUVOf = freeUVOf` (the latter is definitionally true; the
  -- former follows from `cross_band_lt_upward` / A5-G2 path 1).
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
  -- G3a + G3a-followup discharge: lift `findSymmetricPair = some _` to a
  -- `Symmetric` witness via `successorMasks_testBit`.
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
    -- Fast-path / slow-path dispatch.
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
      -- Closure-canonical gate (in-tree witness, rewritten via
      -- `h_construction_eq` and `h_freeUV_eq`).
      have hcanon :
          Case3Enum.closureCanonical
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (maskOf L)
              (Case3Enum.enumFreeUVOf L.w (bandSizes L)) = true := by
        rw [h_construction_eq, h_freeUV_eq]
        exact closureCanonical_predMaskOf L
      -- No symmetric pair gate (we are inside the `none` branch).
      have hsym_gate :
          (Case3Enum.findSymmetricPair
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.enumNOf (bandSizes L))).isSome = false := by
        rw [h_construction_eq, hN_eq, hsymopt]; rfl
      -- Irreducibility gate via B1'.
      have hirr_gate :
          Case3Enum.irreducible
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.offsetsOf (bandSizes L)) = true := by
        rw [h_construction_eq]
        exact irreducible_predMaskOf_offsetsOf_eq_true L hIrr
      -- Adjacent-incomparable gate via B2 + band-major positional
      -- alignment.
      have hadj_gate :
          Case3Enum.hasAdjacentIncomp
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.offsetsOf (bandSizes L)) = true := by
        rw [h_construction_eq]
        have hK : 2 ≤ L.K := by
          obtain ⟨hK3, _, _, _, _⟩ := hScope
          omega
        have hNonemptyBand :
            ∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty := by
          intro k hk1 hk2
          have hcard : 0 < (L.bandSet k).card := hNonempty k hk1 hk2
          exact Finset.card_pos.mp hcard
        refine hasAdjacentIncomp_predMaskOf_eq_true L hK hIrr
          hNonemptyBand (Case3Enum.offsetsOf (bandSizes L)) ?_ ?_ ?_
        · -- Size: `L.K + 1 ≤ (offsetsOf (bandSizes L)).size`.
          rw [offsetsOf_bandSizes_size L]
        · -- Lower-positional: `offsets[L.band x - 1] ≤ pos x`.
          intro x
          have hb_le : L.band x - 1 ≤ L.K := by
            have := L.band_le x; omega
          rw [offsetsOf_bandSizes_getD L _ hb_le]
          exact bandOffset_le_bandMajorEquiv_apply_val L x
        · -- Upper-positional: `pos x < offsets[L.band x]`.
          intro x
          rw [offsetsOf_bandSizes_getD L _ (L.band_le x)]
          exact bandMajorEquiv_apply_val_lt L x
      -- Apply the iteration theorem (G1') and rewrite back to predMaskOf.
      have h_slow_at_iter :
          Case3Enum.hasBalancedPairSlow
              (Case3Enum.enumPredAtMaskOf L.w (bandSizes L) (maskOf L))
              (Case3Enum.enumNOf (bandSizes L)) = true :=
        Case3Enum.enumPosetsFor_iter_balanced L.w (bandSizes L)
          h_certificate (maskOf L) hmask hcanon hsym_gate hirr_gate hadj_gate
      rw [h_construction_eq, hN_eq] at h_slow_at_iter
      -- The `cases hsymopt` already substituted `none` into the match;
      -- the arm reduces to `hasBalancedPairSlow`.
      exact h_slow_at_iter
  -- Lift the Bool fact to `HasBalancedPair (Fin n) [predOrder]`.
  have hBalFin :
      @HasBalancedPair (Fin (Fintype.card α))
        (Case3Enum.predOrder (predMaskOf L) hValid) _ _ :=
    Case3Enum.hasBalancedPair_of_hasBalancedPair hValid h_bnd h_size
      h_sym_lift h_bal
  -- Transport via `bandMajorOrderIso_predOrder L` (G3b explicit-instance
  -- variant).
  exact hasBalancedPair_of_predOrder_orderIso hValid
    (bandMajorOrderIso_predOrder L) hBalFin

end Step8
end OneThird
