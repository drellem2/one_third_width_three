# State — S7-F-D — Session 1: the exceptional-set balanced-pair lift, `exc_perturb` wired

**Ticket:** mg-876f (OneThird-S7-F-D — S7-F bridge: extend the
chain-removal subtype lift to exceptional-set deletion, wire
`exc_perturb`).
**Type:** Lean deliverable.
**Parent:** FULL REFACTOR Phase 2, Piece 3 (the S7-F bridge);
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 sub-arc
`mg-S7-F-D`.
**Depends:** mg-bcc9 (S7-F-C — the `LayeredDecomposition` on
`X ∖ X^exc`).
**Predecessors read:** `docs/PROOF-STRUCTURE-ONBOARDING.md`;
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3;
`docs/state-S7F-C-Session1.md`; `docs/state-MA-Sig-Session1.md`
§4.2 §F + §4.3; `step8.tex:2009-2089`;
`lean/OneThird/Step8/ExcPerturb.lean`;
`lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1042-1239`.

---

## §0. Verdict — **GREEN-with-a-block-report**

Paper item (iii) of `lem:layered-from-step7` (`step8.tex:2080-2089`) —
the *perturbation lift* — is **ported**, in its **honest** shape. The
deliverable is `lean/OneThird/Step8/ExcBalancedLift.lean` (NEW,
sorry-free, **no new `axiom`**, builds clean, imported into
`OneThird.lean`; full `OneThird` build green):

* `IsApproxBalanced` / `HasApproxBalancedPair` — the
  `ε`-approximate-balance notion (the paper's "`HasBalancedPair` with
  `o(1)` error"); `hasApproxBalancedPair_zero_iff` proves
  `HasApproxBalancedPair α 0 ↔ HasBalancedPair α` — the `ε = 0`
  collapse to the exact notion, so the extension genuinely
  *generalises* `OrdinalDecomp.hasBalancedPair_lift`;
* `hasApproxBalancedPair_lift_exc` — **the lift.** A balanced pair on
  `{a // a ∉ S}` lifts to an `ε`-approximately balanced pair of `α`,
  `ε = 2|S|/(|α|−|S|+1)` (the `exc_perturb` / F6b bound). The
  exceptional-set-deletion analogue of the ordinal-sum
  `OrdinalDecomp.hasBalancedPair_lift`;
* `not_isGammaCounterexample_of_exc_balanced` (alias `excPerturbLift`)
  — the headline-ready corollary: if `ε ≤ γ`, an exceptional-set
  balanced pair **refutes** `IsGammaCounterexample α γ`;
* `hasApproxBalancedPair_lift_exc_compl` /
  `not_isGammaCounterexample_of_exc_balanced_compl` — the `↥(Tᶜ)`
  carrier variants (the bridge S7-F-C emits its `LayeredDecomposition`
  on `↥((Xexc D)ᶜ)`), plus the `complNotMemOrderIso` carrier iso and
  the `restrictNotMemOrderIso` wiring helper for S7-F-Z;
* the lift is **discharged non-vacuously on the genuine S7-F bridge
  object** (`§6` of the file): the 3×3 grid minus
  `Xexc gridChainLiftData = {(0,0)}` (`grid_Xexc`).
  `gridMinusCorner_hasBalancedPair` discharges
  `HasBalancedPair (X ∖ X^exc)` via the coordinate-swap automorphism,
  and `grid_hasApproxBalancedPair` runs the lift end to end →
  `HasApproxBalancedPair (Fin 3 × Fin 3) (2/9)` with `ε = 2/9 < 1/3`,
  a genuine non-degenerate window.

**THE BLOCK-REPORT (§2).** The pinned bridge contract
`docs/state-MA-Sig-Session1.md §4.2 §F` transcribes paper item (iii)
as a free-standing theorem `excPerturbLift : … → HasBalancedPair α`
(exact conclusion). **That is ill-posed — a false proposition for
every `|X^exc| ≥ 1`.** Exceptional-set deletion perturbs every
marginal `probLT` by `ε > 0`, so a pair balanced on `X ∖ X^exc`
(`probLT ∈ [1/3, 2/3]`) only lands in the *widened* window
`[1/3 − ε, 2/3 + ε]` on `X` — it is **not** `HasBalancedPair X`. The
ticket body itself names the honest target ("transfer … **with `o(1)`
error**"), so this is **not** a scope expansion: this session delivers
the honest shapes (`HasApproxBalancedPair` / `¬ IsGammaCounterexample`)
and block-reports that §4.2 §F must be re-pinned. The fix is small and
local — see §2.

**`#print axioms`.** `hasApproxBalancedPair_zero_iff` (the `ε = 0`
sanity check, no `exc_perturb`): only `propext`, `Classical.choice`,
`Quot.sound`. `hasApproxBalancedPair_lift_exc`,
`not_isGammaCounterexample_of_exc_balanced`, `excPerturbLift`, the
`_compl` variants, the grid certificates: those three **plus**
`LinearExt.brightwell_sharp_centred` — **inherited from `exc_perturb`
/ `one_elem_perturb`** (F6b already depends on it; verified
`#print axioms exc_perturb`). No `sorryAx`, **no new project axiom**.
`AXIOMS.md` unchanged.

---

## §1. What "extend the chain-removal subtype lift" means here

The ticket: extend `OrdinalDecomp.hasBalancedPair_lift`
(`Subtype.lean:1152`, scoped at ordinal-sum decompositions) to the
"delete `O_T(1)` exceptional elements" variant, and wire `exc_perturb`.

The two lifts, side by side:

| | ordinal-sum lift (`hasBalancedPair_lift`) | exceptional-set lift (`hasApproxBalancedPair_lift_exc`) |
|---|---|---|
| sub-poset | `↥D.Mid` (a piece of an ordinal cut) | `{a // a ∉ S}` (delete `S`) |
| marginal transfer | **exact** — `probLT_restrict_eq` (marginal invariance, `cor:ordinal-marginal`) | **approximate** — `exc_perturb`, error `2\|S\|/(\|α\|−\|S\|+1)` |
| conclusion | `HasBalancedPair α` | `HasApproxBalancedPair α ε` |
| `step8.tex` | item (ii) lever / `lem:ordinal-factorisation` | item (iii), `2080-2089` |

The structural skeleton is **identical** to `hasBalancedPair_lift`:
carry the *same* pair `(x, y)`; incomparability transfers verbatim
(the `Subtype` order is the restricted ambient order — the exact same
two-line argument as `hasBalancedPair_lift`'s incomparability half).
The *only* difference is the marginal step: `hasBalancedPair_lift`
rewrites with the exact `probLT_restrict_eq`; the exceptional-set lift
sandwiches with the `exc_perturb` inequality. Hence the conclusion is
`HasApproxBalancedPair`, and `hasApproxBalancedPair_zero_iff` proves
that at `ε = 0` (`S = ∅`) the two coincide — the extension is a
genuine generalisation, not a different theorem.

**Non-triviality is genuine.** The lift transfers real content: the
hypothesis `HasBalancedPair {a // a ∉ S}` is a true, non-vacuous
proposition on the grid witness (`gridMinusCorner_hasBalancedPair`),
the cardinality side condition `|S| + 2 ≤ |α|` is *derived* (not
assumed) from the existence of the incomparable pair, and the output
`HasApproxBalancedPair (Fin 3 × Fin 3) (2/9)` is a non-degenerate
window (`2/9 < 1/3`). The same pair genuinely crosses the boundary.

---

## §2. THE BLOCK-REPORT — `MA-Sig §4.2 §F` `excPerturbLift` is ill-posed

`docs/state-MA-Sig-Session1.md §4.2 §F` pins:

```lean
theorem excPerturbLift
    (γ : ℚ) (hγ_pos : 0 < γ)
    (Xexc : Finset α)
    (hXexc_small : 2 * (Xexc.card : ℚ)
        / (Fintype.card α - Xexc.card + 1 : ℚ) < γ / 2)
    (hBP_sub : HasBalancedPair {a : α // a ∉ Xexc}) :
    HasBalancedPair α              -- ← ILL-POSED
```

**Why it is a false proposition (for every `|Xexc| ≥ 1`).**
`HasBalancedPair {a // a ∉ Xexc}` exhibits an incomparable pair
`(x, y)` with `probLT x y ∈ [1/3, 2/3]` *computed inside the
subtype*. `exc_perturb` (`ExcPerturb.lean:351`) gives, and gives only,

```
  |probLT x.val y.val − probLT x y|  ≤  ε,   ε = 2k/(n−k+1) > 0.
```

So the lifted ambient marginal lands in `[1/3 − ε, 2/3 + ε]` — a
*strictly wider* window. There is no mechanism forcing it back into
`[1/3, 2/3]`: deleting an element genuinely moves marginals (delete an
element forced below `x` and `probLT x y` shifts). `HasBalancedPair α`
demands the **exact** `[1/3, 2/3]`. Hence the pinned `excPerturbLift`
is not provable — it is a false statement, not a vacuous one.

This is the **same error class as pitfall #6** (the mg-0bd1 8th
vacuity): a signature that type-checks but pins a false proposition.
`MA-Sig §4.4`'s satisfiability check (B) was run for the *bridge*
`lem_layered_from_step7` (§10/§11) but **not** for §4.2 §F
`excPerturbLift` — §F was tagged "UNCHANGED" and waved through. Check
(B) applied to §F would have caught it: the conclusion `HasBalancedPair
α` is not derivable from `HasBalancedPair {subtype}` + an
`ε`-perturbation with `ε > 0`.

**The fix is small and local — already applied in this session.**
The honest content is two theorems, both delivered:

1. `hasApproxBalancedPair_lift_exc` — the genuine lift, conclusion
   `HasApproxBalancedPair α ε` (the paper's "with `o(1)` error",
   verbatim).
2. `not_isGammaCounterexample_of_exc_balanced` / `excPerturbLift`
   (re-pinned) — conclusion `¬ IsGammaCounterexample α γ`.

The headline body `MA-Sig §4.3` adapts **trivially**: §10/§11 already
have `hCex : IsGammaCounterexample α γ` in scope, so

```lean
    -- §10–§11 (re-pinned):
    exact excPerturbLift γ Xexc hXexc_pert hBP_sub hCex
```

replaces "`have hBP := excPerturbLift …; exact hNoBP hBP`". The
contradiction target swaps from `hNoBP` to `hCex` — both are in scope
in the §4.3 body; the `n ≥ n₀(γ, T)` realisability step (§5) already
forces `ε < γ`, exactly the `excPerturbLift` side condition. Two
further deltas from the §F pin, both honest simplifications:

* `hγ_pos : 0 < γ` is **dropped** — positivity of `γ` is not used (the
  contradiction is the `<` vs `≥` clash on `min(p, 1−p)`; it holds for
  any `γ`).
* the side condition is `ε ≤ γ` (the genuinely-needed threshold), not
  `ε < γ/2`. The headline's `n₀` gives `ε < γ` comfortably, so this is
  a relaxation, not a tightening.

**Recommended action for whoever owns `MA-Sig`:** re-pin §4.2 §F to
the `not_isGammaCounterexample`/`HasApproxBalancedPair` shape above,
and re-pin §4.3 §10–§11 to contradict `hCex`. No other piece is
affected — §F is a leaf of the contract.

---

## §3. File walk-through — `Step8/ExcBalancedLift.lean`

* **§1 — `IsApproxBalanced` / `HasApproxBalancedPair`.** The
  `ε`-approximate-balance notion. `hasApproxBalancedPair_zero_iff`
  (`ε = 0` ↔ exact), `.mono` (window widens with `ε`),
  `HasBalancedPair.toApprox`.
* **§2 — transport + swap witness.** `hasBalancedPair_orderIso`
  (transport `HasBalancedPair` along an order iso, via
  `probLT_orderIso`); `probLT_eq_half_of_swap` /
  `incomp_isBalanced_of_swap` / `hasBalancedPair_of_swap` — a swap
  automorphism between `x ≠ y` forces `probLT = 1/2`, hence `x ∥ y`
  and `IsBalanced x y`. (General theory; consumed by the §6 witness.)
* **§3 — the lift.** `card_compl_subtype`
  (`|X ∖ S| = |X| − |S|`); `card_le_of_hasBalancedPair_compl`
  (the side condition `|S| + 2 ≤ |α|` *derived* from the incomparable
  pair, not assumed); `hasApproxBalancedPair_lift_exc` — the main
  theorem.
* **§4 — the `γ`-counterexample refutation.**
  `not_isGammaCounterexample_of_exc_balanced` — both one-sided
  ambient marginals are pinned `≥ 1/3 − γ` (the forward direction via
  `exc_perturb` on `(x, y)`; the reverse via `exc_perturb` on
  `(y, x)` + `probLT_add_probLT_of_ne` on the subtype), which
  overshoots the `γ`-counterexample ceiling. `excPerturbLift` is the
  `MA-Sig`-contract-named alias.
* **§5 — the `Xᶜ` carrier variant.** `complNotMemOrderIso`
  (`↥(Tᶜ) ≃o {a // a ∉ T}`); `hasApproxBalancedPair_lift_exc_compl`,
  `not_isGammaCounterexample_of_exc_balanced_compl`;
  `restrictNotMemOrderIso` (restrict a set-fixing order automorphism
  to the deletion subtype — wiring helper for S7-F-Z and the §6
  witness).
* **§6 — non-vacuous instantiation.** `gridSwap` (the coordinate-swap
  automorphism of `Fin 3 × Fin 3`); `GridMinusCorner` (the subtype
  `Grid ∖ {(0,0)}` — exactly `Xexc gridChainLiftData` by `grid_Xexc`);
  `gridCornerSwap` (the swap restricted to it);
  `gridMinusCorner_hasBalancedPair`; `grid_exc_eps` (`ε = 2/9`);
  `grid_hasApproxBalancedPair`; `grid_not_isGammaCounterexample`.

---

## §4. Mathlib gap check (ticket note: "note a possible mathlib gap")

The ticket flagged a *possible mathlib gap* in the subtype-lift
extension, to be block-reported if materially larger than expected.
**Verdict: no mathlib gap.** Everything needed was already in tree:

* `LinearExt.exc_perturb` (F6b) — the `probLT`-level perturbation
  bound, the substantive content of the lift.
* `LinearExt.probLT_orderIso` — `probLT` transport along an order iso
  (already in `ExcPerturb.lean`).
* `probLT_add_probLT_of_ne` — the two one-sided marginals sum to one.
* Standard Mathlib (`Fintype.card_subtype_compl`,
  `Fintype.one_lt_card_iff`, `OrderIso`, `abs_le`, `le_min`).

The "extension" is a thin combinator: it composes `exc_perturb` (the
real work, already done by F6b) with the same incomparability-transfer
argument `OrdinalDecomp.hasBalancedPair_lift` already uses. The genuine
*finding* of this session is not a mathlib gap — it is the §2
block-report (the §F contract shape was wrong, not the mathlib
substrate).

---

## §5. Build / axioms

* `lake build OneThird.Step8.ExcBalancedLift` — clean (only the
  pre-existing `push_neg` deprecation from `ExceptionalSet.lean`).
* `lake build OneThird` — green; the new file is imported into
  `OneThird.lean` after `BridgeLayered`.
* `#print axioms` — see §0. `hasApproxBalancedPair_zero_iff`: standard
  three only. The lift/refutation theorems: standard three +
  `brightwell_sharp_centred`, inherited from `exc_perturb` (F6b
  already carries it — not introduced here). No `sorry`, no new
  project axiom; `AXIOMS.md` unchanged.

---

## §6. Hand-off to S7-F-Z (integration)

`mg-S7-F-Z` wires A–D into `lem_layered_from_step7`. For item (iii):

* the bridge's `LayeredDecomposition` is on `↥((Xexc D)ᶜ)`
  (`BridgeLayered.lean`); Piece 6 (`lem_layered_balanced_full`)
  consumes it and emits `HasBalancedPair ↥((Xexc D)ᶜ)`. Feed that
  directly to **`not_isGammaCounterexample_of_exc_balanced_compl`**
  (the `↥(Tᶜ)` variant) with `T := Xexc D` — no carrier-shuffling
  needed.
* the `ε ≤ γ` side condition is the `MA-Sig §4.3 §5` `n ≥ n₀(γ, T)`
  output (`exc_perturb_bound_of_n_zero`); `C_exc T = O_T(1)` and
  `n₀` is chosen so `2 C_exc T/(n − C_exc T + 1) < γ`.
* **S7-F-Z must also re-pin `MA-Sig §4.2 §F` + §4.3 §10–§11** per §2
  above before the headline body can close — that is the one
  remaining contract edit, and it is mechanical.
