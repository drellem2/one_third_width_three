/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — Case-3 cap-5 singletons-only enumeration (`mg-4d7b`)

Extends the F5a `case3_certificate` family (covering K = 3 across
w ∈ {1, 2, 3, 4} at full sizeLimit, plus the K = 4 w = 1 sliver)
to the *cap-5 singletons-only sub-scope* of
`Step8.Case3Witness.{u}`:

Under all five caps of `Case3Witness.{u}`:

* Cap 1 (`Function.Injective LB.band`) + Cap 4 (nonempty bands)
  force band sizes singletons: `bandSizes = List.replicate K 1`.
* Cap 2 (`LB.K ≤ 2 * LB.w + 2`) + Cap 5 (`LB.w ≤ 4`) bound
  `K ≤ 10`.

So the universal Case3Witness antecedent restricts to:

  ∀ β with 2 ≤ |β| ≤ 10, ∀ LB : LayeredDecomposition β satisfying
  caps 1+4 (bands singletons, K = |β|), cap 2 (K ≤ 2w+2), cap 5
  (w ≤ 4), and ¬IsChainPoset β, width ≤ 3, …

The Bool-level enumeration `enumPosetsFor w (List.replicate K 1)`
ranges precisely over the (K, w)-indexed cap-5 sub-scope (one
`bandSizes` tuple per K).

## Tractability tiers

This file ports the per-`(K, w)` `native_decide` certificates for
**K = 4 w ∈ {2, 3, 4}, K ∈ {5, 6, 7, 8}, all w ∈ {0..4}**
(filtered to satisfy `K ≤ 2w + 2`). These are small (`nfree ≤ 22`,
`2^nfree ≤ 4.2M`) and within the standard `native_decide` budget.

The remaining cells:

* K = 9 w = 4 (`nfree = 26`, `2^26 = 67M`) — fits in budget but
  ~30s native_decide; split into `Cap5SingletonsK9.lean` for parallel
  Lake builds.
* K = 10 w = 4 (`nfree = 30`, `2^30 = 1.07G`) — exceeds native_decide
  budget; certified externally via `enum_cap5_K10.py` (parallel
  Python).  Per-cell pass-status recorded in
  `lean/scripts/enum_cap5_K10_certificate.json`.  Lean-side import
  is parked under `mg-4d7b-followup-K10-decide` (sealed-list
  `decide` precedent: `K4W1.lean`'s 50-element pre-filtered list).

K = 2, 3 cases:

* K = 2 is included as §0 below (small Bool-level evaluation; the
  Prop-level discharge in `OptionC.Case3WitnessProof` does a
  reducibility case-split with `option_c_K2_closure`).
* K = 3 is already covered for all w ∈ {1..4} by the existing
  `case3_balanced_w{1..4}` certificates (their `bandSizesGen 3
  sizeLimit` ranges include `[1, 1, 1]`).

## References

* `mg-4d7b` (this file): cap-5 enumeration polecat (Daniel directive
  2026-05-17T20:55Z).
* `mg-d5a0`: cap-5 signature refactor; named cap 5 `LB.w ≤ 4`.
* `mg-e2e9`: architecture analysis exposing the missing cap.
* `lean/scripts/enum_cap5.py`: external enumerator (this session).
* `lean/scripts/enum_cap5_K2to8_certificate.json`: per-cell
  pass-status certificate ported here.
* `docs/state-Case3Witness-cap5-enumeration.md`: cumulative state.
-/

-- `native_decide` trust: each theorem ports one (K, w) slice of the
-- cap-5 enumeration certificate verified by `lean/scripts/enum_cap5.py`.
set_option linter.style.nativeDecide false

namespace OneThird
namespace Step8
namespace Case3Enum

/-! ### §0 — K = 2 cells

K = 2 w ∈ {0, 1}: with bands singletons (cap 1+4), the K = 2 layered
config has the unique cross-pair `(M_1, M_2) = ({elt 0}, {elt 1})`.

* `w = 0`: the cross-pair is *forced* `<` by (L2-forced); the
  resulting poset is a 2-chain, so the `irreducible` filter rejects
  the only candidate config (every cut is *reducible* since the
  cross is `<`).  Bool result `true` is *vacuously* over the empty
  filtered set.
* `w = 1`: the cross-pair is *free* (band gap = 1 ≤ w); the
  unique closure-canonical config is the 2-element antichain (mask
  = 0).  This is irreducible (cross-pair incomparable), has an
  adjacent incomparable cross-pair, and `Pr[0 <_L 1] = 1/2 ∈
  [1/3, 2/3]` by the symmetric-pair fast path.

(The Prop-level Case3Witness discharge of K = 2 goes through
`OptionC.Case3WitnessProof`'s K = 2 case-split:
`LayerOrdinalReducible` ⇒ chain (contradicts `¬IsChainPoset β`);
`LayerOrdinalIrreducible` ⇒ `option_c_K2_closure`.) -/

theorem case3_balanced_singletons_K2_w0 :
    enumPosetsFor 0 [1, 1] = true := by native_decide

theorem case3_balanced_singletons_K2_w1 :
    enumPosetsFor 1 [1, 1] = true := by native_decide

/-! ### §1 — K = 4 cells (w ∈ {2, 3, 4})

K = 4 w = 1 is already discharged by `case3_balanced_K4_w1`
(`mg-9a4a` Window C; `K4W1.lean`). The w ∈ {2, 3, 4} slices below
extend coverage to the full K = 4 row of the cap-5 table. -/

/-- `enumPosetsFor 2 [1,1,1,1] = true`: every K = 4, w = 2,
singleton-bands layered width-3 irreducible poset on 4 elements with
an adjacent incomparable cross-pair admits a balanced pair. -/
theorem case3_balanced_singletons_K4_w2 :
    enumPosetsFor 2 [1, 1, 1, 1] = true := by native_decide

/-- `enumPosetsFor 3 [1,1,1,1] = true`: K = 4, w = 3 slice. -/
theorem case3_balanced_singletons_K4_w3 :
    enumPosetsFor 3 [1, 1, 1, 1] = true := by native_decide

/-- `enumPosetsFor 4 [1,1,1,1] = true`: K = 4, w = 4 slice. -/
theorem case3_balanced_singletons_K4_w4 :
    enumPosetsFor 4 [1, 1, 1, 1] = true := by native_decide

/-! ### §2 — K = 5 cells (w ∈ {2, 3, 4}, `K ≤ 2w + 2` ⇒ w ≥ 2) -/

theorem case3_balanced_singletons_K5_w2 :
    enumPosetsFor 2 [1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K5_w3 :
    enumPosetsFor 3 [1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K5_w4 :
    enumPosetsFor 4 [1, 1, 1, 1, 1] = true := by native_decide

/-! ### §3 — K = 6 cells (w ∈ {2, 3, 4}) -/

theorem case3_balanced_singletons_K6_w2 :
    enumPosetsFor 2 [1, 1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K6_w3 :
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K6_w4 :
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1] = true := by native_decide

/-! ### §4 — K = 7 cells (w ∈ {3, 4}) -/

theorem case3_balanced_singletons_K7_w3 :
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K7_w4 :
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1, 1] = true := by native_decide

/-! ### §5 — K = 8 cells (w ∈ {3, 4})

K = 8 w = 4 has `nfree = 22` (~4.2M closure-canonical candidates);
allow extra `native_decide` budget for this cell. -/

theorem case3_balanced_singletons_K8_w3 :
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1, 1, 1] = true := by native_decide

theorem case3_balanced_singletons_K8_w4 :
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1, 1, 1] = true := by native_decide

/-! ### §6 — Cap-5 singletons combined certificate

Combined `And` of all (K, w) cells covered in this file, suitable
for downstream consumers needing the full singletons-only sub-scope
as a single hypothesis. K = 3 and K = 4 w = 1 cells are pulled
from `case3_certificate`; K = 9 lives in `Cap5SingletonsK9.lean`
(separate file for parallel Lake builds); K = 10 is certified
externally via `enum_cap5_K10.py` (no in-tree Lean theorem to avoid
introducing a new axiom — sealed-list `decide` import parked
under follow-up).

NB: This is **not** the full Case3Witness proof — that requires a
Bool↔Prop bridge analogous to `allBalanced_imp_enumPosetsFor`
(`AllBalancedBridge.lean`) re-targeted at the singletons sub-scope.
This combined certificate is the *enumeration substrate* for that
proof. -/
theorem case3_balanced_singletons_K4_to_K8 :
    enumPosetsFor 2 [1, 1, 1, 1] = true ∧
    enumPosetsFor 3 [1, 1, 1, 1] = true ∧
    enumPosetsFor 4 [1, 1, 1, 1] = true ∧
    enumPosetsFor 2 [1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 3 [1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 4 [1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 2 [1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 3 [1, 1, 1, 1, 1, 1, 1, 1] = true ∧
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1, 1, 1] = true :=
  ⟨case3_balanced_singletons_K4_w2,
   case3_balanced_singletons_K4_w3,
   case3_balanced_singletons_K4_w4,
   case3_balanced_singletons_K5_w2,
   case3_balanced_singletons_K5_w3,
   case3_balanced_singletons_K5_w4,
   case3_balanced_singletons_K6_w2,
   case3_balanced_singletons_K6_w3,
   case3_balanced_singletons_K6_w4,
   case3_balanced_singletons_K7_w3,
   case3_balanced_singletons_K7_w4,
   case3_balanced_singletons_K8_w3,
   case3_balanced_singletons_K8_w4⟩

end Case3Enum
end Step8
end OneThird
