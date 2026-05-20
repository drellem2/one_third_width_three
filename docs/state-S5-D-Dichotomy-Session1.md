# OneThird-S5-D Session 1 state report — Rich-or-Collapse dichotomy grounded

**Ticket:** mg-d4bb (FULL REFACTOR Phase 2, Wave-1; Piece-1 Steps-1-6
cascade port; scoped by mg-d8c7 §2.1 / §5.2 under S5-D; depends on
mg-faf8).
**Verdict:** **GREEN — substantively landed.** The Step 5
Rich-or-Collapse dichotomy (`thm:step5`, `step5.tex:74`) is ported in
*grounded* form: the per-triple dichotomies are discharged from genuine
poset incomparability-interval geometry (no opaque `dich_*` inputs),
and the whole three-triple assembly is instantiated **non-vacuously**
on a concrete width-3 non-chain poset. Full `lake build` clean.

---

## §0. TL;DR

* **The dichotomy port (`thm:step5`, `step5.tex:74`).** `Dichotomy.lean`
  already carried the *abstract* dichotomy: `thm_step5` takes the three
  per-triple dichotomies `dich_AB/AC/BC` and the G4/G5 closures as
  **opaque hypotheses** and case-splits. That is faithful to the paper
  assembly but does not connect to any poset — it is the typed-routing
  surface the FULL REFACTOR is replacing with groundings.
* **This session grounds it.** New file `Step5/DichotomyGrounded.lean`
  discharges the three per-triple dichotomy hypotheses from the
  **genuine `alphaIdx`/`betaIdx` incomparability-interval geometry** of
  a poset, reusing the G1+G2 grounding `convex_overlap_grounded` landed
  by mg-b21f (S5-A). The result `dichotomy_grounded` is the
  Rich-or-Collapse dichotomy with **no opaque hypotheses**.
* **Non-vacuity bar met.** `dichotomy_grounded_concrete` instantiates
  the full three-triple assembly on `W3 := Fin 3 × Fin 3` (product
  order) — the genuine width-3 non-chain 9-element poset of mg-b21f.
  The rich row is genuinely non-empty
  (`(2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2`, from the genuine
  rich pair `(chainA 2, chainB 2)`), the `β`-endpoint family genuinely
  *strictly* increases, `p = q = r = 3`. No `Subsingleton`/empty
  baseline anywhere.
* **No new axioms, no `sorry`, no headline-path change.** All additions
  are pure interval geometry + a concrete instance; the abstract
  `Dichotomy.lean` and all downstream modules are unaffected (the new
  file is an import-only leaf).

## §1. Inventory delta

```
DichotomyGrounded.lean   new, 264 LoC   (grounded dichotomy + concrete instance)
OneThird.lean            +1 import line
```

`EndpointMono.lean`, `ConvexOverlap.lean`, `Dichotomy.lean`,
`G1G2Grounded.lean`, `FiberMass.lean`, `Layering.lean`,
`SecondMoment.lean` — all unchanged.

## §2. What the grounding does

| Symbol | Role (`step5.tex`) |
|---|---|
| `gRichRow Z x y T` | rich-row family of a genuine triple `(X,Y\|Z)`: `richRow` wired to the actual `alphaIdx`/`betaIdx` interval endpoints |
| `mem_gRichRow` | membership characterisation of `gRichRow` via `RichPair` |
| `prop_single_triple_grounded` | `prop:single-triple` (`step5.tex:106`) on genuine geometry; G2 monotonicity discharged by G1 |
| `dichotomy_grounded` | `thm:step5` Steps 2-3 (`step5.tex:212-246`): some triple many-rich ∨ all three banded — **no opaque hypotheses** |
| `thm_step5_grounded` | full `thm:step5` (`step5.tex:74`): G4 fiber-mass closure upgrades many-rich to (R); three banded outcomes are (C) |
| `dichotomy_grounded_concrete` | the non-vacuous `W3` instantiation (mg-d4bb acceptance bar) |

`dichotomy_grounded` is the substantive deliverable: it is the genuine
geometric content of `thm:step5`'s case split, with the three
per-triple dichotomies *discharged* from `convex_overlap_grounded`
rather than *assumed* as in the abstract `thm_step5`. `thm_step5_grounded`
adds the faithful G4/G5 packaging — G4 (`lem:fiber-mass`, `FiberMass.lean`)
is consumed as the separately-ticketed closure exactly as the paper
proof invokes it at `step5.tex:233`; G5 (collapse) is the genuine
"all three triples banded" conjunction.

## §3. Non-vacuous instantiation (`mg-d4bb` acceptance bar)

`W3 := Fin 3 × Fin 3` (product order), the genuine width-3 non-chain
9-element poset of mg-b21f, Dilworth-decomposed into three length-3
chains `chainA`, `chainB`, `chainCenum` with reference finsets
`chainAref`, `chainBref`, `chainC`. `dichotomy_grounded_concrete`
bundles, all proved (not assumed):

1. `HasWidthAtMost W3 3` and `¬ IsChainPoset W3`;
2. the `β`-endpoint family of `chainA` on `C` is genuinely *strictly*
   increasing (`betaIdx … 0 = 0 < 2 = betaIdx … 2`) — the interval
   geometry varies, it is not constant;
3. the rich row of the triple `(A,B|C)` is genuinely non-empty:
   `(2 : Fin 3) ∈ gRichRow chainC chainA chainB 1 2`, derived from the
   genuine rich pair `(chainA 2, chainB 2)` (their `C`-incomparability
   intervals overlap in length `3 ≥ 1`);
4. the full `dichotomy_grounded` Rich-or-Collapse dichotomy holds on
   the three genuine ordered triples.

No `Subsingleton`-on-empty baseline; `p = q = r = 3`; the rich set is
genuinely populated. The acceptance bar is met.

## §4. No gap-discovery

Default-skeptical re-read of `step5.tex:74-246` (`thm:step5` +
`prop:single-triple` + their proofs) against the Lean port surfaced
**no ill-posed target** and **no missing mathlib dependency**. The
paper's `thm:step5` proof is a clean three-triple case split over the
per-triple dichotomy; the only inputs are G1-G5, all of which are
in tree (G1+G2 grounded by mg-b21f; G3/G4/G5 abstract forms in
`FiberMass.lean` / `Layering.lean`). The dichotomy assembly itself
carries no hidden width-3 essentialism beyond what G1/G2 already
respect.

One scope note (not blocking, consistent with mg-b21f §3): the
abstract `Step5Collapse` of `Dichotomy.lean` — `∃ fAC fBC K, ∀ i j,
|fAC i − fBC j| ≤ 2K+1` — is satisfiable for *any* `fAC, fBC` on
finite index types (bounded range ⇒ `K` exists), so it is a weak
packaging. `dichotomy_grounded` / `thm_step5_grounded` therefore emit
the **genuine, non-trivial collapse output** — the conjunction of
three `SingleTripleBanded` facts (every rich row inside a width-`K`
band around a nondecreasing envelope) — rather than the weak
`Step5Collapse`. The G5 packaging of the three bands into the paper's
`|h(x) − h(y)|` height bounds (`lem:global-layering`,
`global_layering_structural` in `Layering.lean`) is the separate
S5 G5 ticket.

## §5. Build

`lake build OneThird.Step5.DichotomyGrounded` clean (4 modules
rebuilt: `ConvexOverlap`, `G1G2Grounded`, `Dichotomy`,
`DichotomyGrounded`; mathlib cache reused). `lake build OneThird`
(full tree) clean — the new file is an import-only leaf, no
downstream module consumes it, nothing else recompiles beyond the
added import. No new warnings, no `sorry`, no new axioms.
