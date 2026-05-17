/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.Case3Enum

/-!
# Step 8 — Case-3 cap-5 singletons K = 9 cell (`mg-4d7b`)

The K = 9 w = 4 cell of the cap-5 enumeration: `nfree = 26`
(2^26 = 67M closure-canonical mask candidates). This is at the
top of the `native_decide` budget but tractable on commodity
hardware (~30s wall-clock per Python reference enumeration; faster
under `native_decide`'s compiled evaluator).

Split into a dedicated file so that Lake builds the K = 9 evaluation
in parallel with the smaller cells in `Cap5Singletons.lean`. K = 10
(`nfree = 30`, 2^30 ≈ 1.07G masks) is *not* in scope for
`native_decide` — that cell is certified externally via
`enum_cap5_K10.py` and recorded in
`enum_cap5_K10_certificate.json`; no in-tree Lean theorem to avoid
introducing a new project axiom.

This file is intentionally *not* imported from `OneThird.lean`
(see comment in `OneThird.lean` near the `Case3Enum.K4W1` import):
the per-file `native_decide` budget for K = 9 w = 4 (2^26 ≈ 67M
masks, ~12 min Python single-thread, faster under native compile)
is at the top of the standard build budget. The file builds on
demand via `lake build OneThird.Step8.Case3Enum.Cap5SingletonsK9`.

External verification: see `lean/scripts/enum_cap5.py --K-min 9
--K-max 9` and the corresponding entry of
`lean/scripts/enum_cap5_K9_certificate.json`.
-/

set_option linter.style.nativeDecide false

namespace OneThird
namespace Step8
namespace Case3Enum

/-- `enumPosetsFor 4 [1,1,1,1,1,1,1,1,1] = true`: every K = 9, w = 4,
singleton-bands layered width-3 irreducible poset on 9 elements with
an adjacent incomparable cross-pair admits a balanced pair.

This is the K = 9 cell of the cap-5 singletons-only sub-scope
enumeration; under all five `Case3Witness` caps + cap 1 + cap 4
(injective + nonempty bands), this is the only K = 9 cell in scope
(`K ≤ 2w + 2` with `w ≤ 4` forces `w = 4` at `K = 9`). -/
theorem case3_balanced_singletons_K9_w4 :
    enumPosetsFor 4 [1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by native_decide

end Case3Enum
end Step8
end OneThird
