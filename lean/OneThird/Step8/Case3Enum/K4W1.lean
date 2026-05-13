/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — Case-3 residual enumeration: `K = 4, w = 1` native-decide slice (`mg-9a4a`)

Window C of `docs/compatibility-geometry-pathP3-scoping.md` (small
size-limit variant): extend the F5a `case3_certificate` from `K = 3`
to the K=4-w=1 small-cardinality slice `|Q| ≤ 8`. The full Window C
target `|Q| ≤ 12 = 6·w + 6` includes 31 K=4-w=1 band-tuples at
`nfree ≥ 18` that are intractable in the local native-decide budget;
those remain axiomatic. The 50 K=4-w=1 band-tuples with `c ≤ 8` are
covered here.

This file is split from `OneThird.Step8.Case3Enum.Certificate` so
that lake builds the four per-`w` and the K=4 w=1 native-decide
evaluations in parallel.
-/

-- `native_decide` trust: this theorem ports the `K = 4, w = 1, c ≤ 8`
-- extension slice of the enumeration certificate.
set_option linter.style.nativeDecide false

namespace OneThird
namespace Step8
namespace Case3Enum

/-- `allBalancedAtK 4 1 8 = true` (`mg-9a4a`, Window C small-size):
every `K = 4`, `w = 1`, layered width-3 irreducible poset on `≤ 8`
elements with an adjacent incomparable cross-pair admits a balanced
pair. Discharges the small-cardinality (`c ≤ 8`) slice of the
`K = 4, w = 1` parameter range; the higher-`c` slices remain
axiomatic. See `docs/compatibility-geometry-pathP3-scoping.md` §5.1
and the file header above for the narrowing accounting. -/
theorem case3_balanced_K4_w1 : allBalancedAtK 4 1 8 = true := by
  native_decide

end Case3Enum
end Step8
end OneThird
