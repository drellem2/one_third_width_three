/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum.W1
import OneThird.Step8.Case3Enum.W2
import OneThird.Step8.Case3Enum.W3
import OneThird.Step8.Case3Enum.W4

/-!
# Step 8 — Case-3 residual enumeration: combined certificate

Packages the four per-`w` Bool-level certificates
(`case3_balanced_w1 … case3_balanced_w4`) into the single
conjunction `case3_certificate`.  No additional `native_decide`
evaluation happens here — this is just `And`-introduction.

## Scope

Matches `lean/scripts/enum_case3_certificate.json` exactly:

| w | K | size cap | configs | Python elapsed |
|---|---|----------|---------|----------------|
| 1 | 3 | 9 (full) | 344243  | ~13s           |
| 2 | 3 | 7        | 102784  | ~4s            |
| 3 | 3 | 7        | 102784  | ~4s            |
| 4 | 3 | 7        | 102784  | ~4s            |

Full-depth (`K = 2w + 2`) and full-size (`|Q| = 3(3w + 1)`)
enumerations are out of reach for `native_decide` at `v4.29.1` —
the Python script estimates hours of single-threaded compute for
those, and native compilation plus evaluation on that scale
exceeds the 10-minute lake-build target.  The scope covered here
exactly matches the check-in evidence of `mg-307c`.

## Downstream use

The consumer `Step8.bounded_irreducible_balanced` (on an abstract
`LayeredDecomposition α`) needs a separate encoding argument to
transport this Bool-level certificate to a statement on arbitrary
width-3 layered posets.  That encoding — choose an element
labelling within each band, prove probability invariance under
relabelling — is a follow-up F5a-ℓ item and lives outside this
certificate module.
-/

namespace OneThird
namespace Step8
namespace Case3Enum

/-- **Case-3 residual enumeration certificate** — Lean-native
port of `enum_case3_certificate.json`.  For every `(w, size_limit)`
in the certified Python scope, every layered width-3 poset
satisfying (L1)-(L4), layer-ordinal-sum irreducible, with depth
`K = 3`, interaction width `w ∈ {1, 2, 3, 4}`, and an adjacent
incomparable cross-pair, admits a balanced pair. -/
theorem case3_certificate :
    allBalanced 1 9 = true ∧
    allBalanced 2 7 = true ∧
    allBalanced 3 7 = true ∧
    allBalanced 4 7 = true :=
  ⟨case3_balanced_w1, case3_balanced_w2, case3_balanced_w3, case3_balanced_w4⟩

end Case3Enum
end Step8
end OneThird
