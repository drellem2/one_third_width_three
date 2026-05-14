/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum.W1
import OneThird.Step8.Case3Enum.W2
import OneThird.Step8.Case3Enum.W3
import OneThird.Step8.Case3Enum.W4
import OneThird.Step8.Case3Enum.K4W1

/-!
# Step 8 — Case-3 residual enumeration: combined certificate

Packages the per-`w` Bool-level certificates into the single
conjunction `case3_certificate`. No additional `native_decide`
evaluation happens here — this is just `And`-introduction.

## Scope (`mg-9a4a` Window C narrowing, small size-limit variant)

Matches `lean/scripts/enum_case3_certificate.json` together with the
Window C small-size extension of
`docs/compatibility-geometry-pathP3-scoping.md`:

| K | w | size cap | configs              | source                       |
|---|---|----------|----------------------|------------------------------|
| 3 | 1 | 9 (full) | 344243               | `case3_balanced_w1`          |
| 3 | 2 | 7        | 102784               | `case3_balanced_w2`          |
| 3 | 3 | 7        | 102784               | `case3_balanced_w3`          |
| 3 | 4 | 7        | 102784               | `case3_balanced_w4`          |
| 4 | 1 | 8        | 50 tuples            | `case3_balanced_K4_w1`       |

The K=4 w=1 small-size slice is the `mg-9a4a` Window C extension
narrowing the residual axiom's parameter range (`InCase3Scope`
widening). See `docs/compatibility-geometry-pathP3-scoping.md` for
the full scoping verdict and the larger-`c` slices that remain
axiomatic.

**Small size-limit variant.** The full Window C target of the
scoping doc (`K = 4, w = 1, c ≤ 12` and the K=3 c-sliver at
`c ∈ {8, 9}`) includes band-tuples at `nfree ≥ 18` whose
`2^nfree` native-decide evaluations do not fit the local build
window. The residual axiom continues to apply on those tuples; only
the small-cardinality K=4-w=1 slice (50 band-tuples at `c ≤ 8`) is
discharged here, alongside the unchanged K=3 four-`w` certificates.

Full-depth (`K ≥ 5`) and high-`w` band-tuple configurations with
`nfree > 27` remain out of reach of `native_decide` — those stay
under the residual axiom (`case3Witness_hasBalancedPair_outOfScope`)
post-narrowing.

## Downstream use

The consumer `Step8.bounded_irreducible_balanced_inScope` (on an
abstract `LayeredDecomposition α`) extracts the appropriate slice via
`allBalanced_imp_enumPosetsFor` (resp.
`allBalancedAtK_imp_enumPosetsFor` for the K=4 entry) together with
the band-major Fin-n encoding. -/

namespace OneThird
namespace Step8
namespace Case3Enum

/-- **Case-3 residual enumeration certificate** — Lean-native port
of `enum_case3_certificate.json` together with the `mg-9a4a` Window
C small-size extension (`K = 4, w = 1, c ≤ 8`).

For every `(K, w, sizeLimit)` in the certified scope, every layered
width-3 poset satisfying (L1)-(L4), layer-ordinal-sum irreducible,
with the given depth and interaction width, and an adjacent
incomparable cross-pair, admits a balanced pair. -/
theorem case3_certificate :
    allBalanced 1 9 = true ∧
    allBalanced 2 7 = true ∧
    allBalanced 3 7 = true ∧
    allBalanced 4 7 = true ∧
    allBalancedAtK 4 1 8 = true :=
  ⟨case3_balanced_w1, case3_balanced_w2, case3_balanced_w3,
   case3_balanced_w4, case3_balanced_K4_w1⟩

end Case3Enum
end Step8
end OneThird
