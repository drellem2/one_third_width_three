/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — Case-3 residual enumeration: `w = 1` native-decide slice

Covers `~344243` configurations (see `lean/scripts/README.md`).
The effective size cap for `K = 3` with bands in `{1, 2, 3}` is
`|Q| ≤ 9` — equivalent to the Python script's nominal
`max_total = 12`.

This file is split out from `OneThird.Step8.Case3Enum` so that the
four per-`w` `native_decide` evaluations compile in parallel.
-/

-- `native_decide` trust: this theorem ports one slice of the
-- enumeration certificate verified by `lean/scripts/enum_case3.py`.
set_option linter.style.nativeDecide false

namespace OneThird
namespace Step8
namespace Case3Enum

/-- `allBalanced 1 9 = true`: every `w = 1`, `K = 3`, layered
width-3 irreducible poset on `≤ 9` elements with an adjacent
incomparable cross-pair admits a balanced pair.  Verifies the
`w = 1` slice (`344243` configurations) of
`enum_case3_certificate.json`. -/
theorem case3_balanced_w1 : allBalanced 1 9 = true := by
  native_decide

end Case3Enum
end Step8
end OneThird
