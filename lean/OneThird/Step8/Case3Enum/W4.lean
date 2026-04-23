/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — Case-3 residual enumeration: `w = 4` native-decide slice

Covers `~102784` configurations (`|Q| ≤ 7` slice of
`lean/scripts/enum_case3_certificate.json`).
-/

-- `native_decide` trust: this theorem ports one slice of the
-- enumeration certificate verified by `lean/scripts/enum_case3.py`.
set_option linter.style.nativeDecide false

namespace OneThird
namespace Step8
namespace Case3Enum

/-- `allBalanced 4 7 = true`: the `|Q| ≤ 7` slice of the `w = 4`
residual (`102784` configurations). -/
theorem case3_balanced_w4 : allBalanced 4 7 = true := by
  native_decide

end Case3Enum
end Step8
end OneThird
