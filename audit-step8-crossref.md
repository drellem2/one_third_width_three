# Audit: Paper ↔ Lean cross-reference, Step 8 (mg-6f46 / Q3)

Date: 2026-04-23.

Performed under mg-6f46 (Q3). Walked every file in
`lean/OneThird/Step8/` and the headline `lean/OneThird/MainTheorem.lean`
against `step8.tex`, looking for drift in signatures, stale line
references, missing Lean counterparts, and residual `sorry` / `axiom`
tokens.

**Verdict: mismatch.** Several gaps found; see §"Findings" and
§"Follow-ups" below.

## Scope of audit

Files walked (all of `lean/OneThird/Step8/`, plus headline):

| File | LoC |
|------|-----|
| `BipartiteEnum.lean` | 313 |
| `FrozenPair.lean` | 518 |
| `G2Constants.lean` | 264 |
| `LayeredBalanced.lean` | 847 |
| `LayeredReduction.lean` | 458 |
| `LayerOrdinal.lean` | 415 |
| `MainAssembly.lean` | 486 |
| `SmallN.lean` | 249 |
| `TheoremE.lean` | 221 |
| `Window.lean` | 281 |
| `MainTheorem.lean` | 95 |

Paper labels enumerated from `step8.tex` (29 `\label{...}` declarations
of types `thm:`, `prop:`, `lem:`, `cor:`, `def:`).

## Findings

### 1. Residual `sorry` token on main (BLOCKER)

The task brief asserts F5 (mg-3fd8) and F7 (mg-f1b7) both landed and
that the Lean side should be "sorry-free (modulo the
brightwell_sharp_centred axiom)." **This is not the case on main.**

`lean/OneThird/Step8/LayeredBalanced.lean:728` contains a live
`(by sorry)`:

```lean
exact D.hasBalancedPair_lift
  (lem_layered_balanced_subtype L (by sorry) h2 D hxy_inc
    ⟨Finset.mem_univ x, Finset.mem_univ y⟩)
```

inside the `K ≥ 2` branch of `lem_layered_balanced` (lines 653-729).
The `by sorry` discharges `hw_zero : L.w = 0`, which the
`layeredFromBridges` ground-set witness (with
`w = Fintype.card α + Lwidth3.bandwidth`) never satisfies.

`git log --all` confirms:

* F5 (`mg-3fd8`, commit `ddff2d2`) — on `polecat-pc-3fd8` only, **not
  merged into main**. Would have introduced `Case3Witness.{u}` and
  rewritten `lem_layered_balanced_subtype` without `hw_zero`.
* F7 (`mg-f1b7`, commit `9603b45`) — on `polecat-pc-f1b7` only, **not
  merged into main**. Would have tightened `layeredFromBridges`.
* Both work items are tagged `archived` in the `mg` tracker without
  having reached `main`, consistent with the already-filed bug
  `mg-06f2` ("polecats archive tickets without code merging").

**Impact.** The entire main-chain (`width3_one_third_two_thirds`
→ `Step8.width3_one_third_two_thirds_assembled` → `mainAssembly` →
`mainTheoremInputsOf` → `lem_layered_balanced layeredFromBridges`) is
not sorry-free.

### 2. Declared axioms: none present (clean)

A scan of `lean/OneThird/` for `axiom` declarations returned **zero
hits** (grep for `^\s*axiom\s`). Every occurrence of the string
"axiom" is in docstrings/comments only.

Notably, the task brief's allow-listed `brightwell_sharp_centred`
axiom is **not present** in the codebase. Mentions of "Brightwell"
appear only as bibliographic citations inside
`Mathlib/LinearExtension/FKG.lean` and `FiberSize.lean`. The sharp
centred-sum bound (`eq:sharp-centred`) was formalised paper-side in
`mg-391c` (commit `c6d76d6`); no Lean-side axiom followed.

### 3. Stale `step8.tex:NNNN` line references (widespread)

Many Lean docstrings reference specific `step8.tex:NNNN` line numbers
that no longer point at the cited content. The paper has been
re-paginated (notably via `mg-ba4cf8f`, the `hyp:arith` restriction of
`thm:main-step8`, and multiple paper-side expansions in §G4). The
`\label{...}` labels themselves still match; only line numbers drift.

Representative mismatches (Lean docstring ref → actual paper line):

| Lean file | Claimed ref | Actual |
|-----------|-------------|--------|
| `Window.lean` docstring | `step8.tex:1571-1765` (§sec:g4-balanced-pair) | 2335-3237 |
| `Window.lean` | `step8.tex:1606-1607` (window size bound) | 2538 |
| `Window.lean` ofBandPair | `step8.tex:1576-1582` | 2524-2539 |
| `LayeredReduction.lean` docstring | `step8.tex:1325-1530` (§sec:layered-reduction) | 1873-2334 |
| `LayeredReduction.lean` lem_cut | `step8.tex:1371` | 2164 |
| `LayeredReduction.lean` lem_layered_reduction | `step8.tex:1397` | 2190 |
| `LayeredReduction.lean` K₀ | `step8.tex:1412` | 2205 |
| `LayeredReduction.lean` def:layered | `step8.tex:1335` | 1883 |
| `LayeredBalanced.lean` windowLocalization | `step8.tex:1573-1608` | 2521-2569 |
| `LayeredBalanced.lean` lem:chained-lift | `step8.tex:2091-2187` | need re-map |
| `LayerOrdinal.lean` | `step8.tex:1619-1621` | need re-map |
| `MainAssembly.lean` | `step8.tex:488-849` (§sec:main-thm) | 502-945 |

The labels (`lem:cut`, `lem:layered-reduction`, `def:layered`,
`lem:window-localization`, etc.) are all still in the paper — it is
only the line numbers that have drifted.

### 4. Signature mismatch: `thm:main-step8` / `width3_one_third_two_thirds`

Paper (`step8.tex:525-528`, landed `mg-0015`/`ba4cf8f`):

> **Theorem (Width-3 1/3-2/3, conditional on Steps 1-7 and on
> Hypothesis~\ref{hyp:arith}).** Assume Hypothesis~\ref{hyp:arith}.
> Then every finite width-3 poset that is not a total order has a
> balanced pair.

Lean (`lean/OneThird/MainTheorem.lean:38-41`):

```lean
theorem width3_one_third_two_thirds
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α) :
    HasBalancedPair α := ...
```

No arithmetic-richness hypothesis is threaded. On main this is
masked by the G4-branch `(by sorry)` (§1 above). Once F5-style
closure lands, either (a) `hyp:arith` needs threading as an
additional hypothesis, (b) a `Case3Witness` / arithmetic-condition
input replaces it, or (c) the paper wording relaxes.

### 5. Paper labels without explicit Lean labelling

Several paper lemmas correspond to Lean constructs that exist but do
not cite the paper label. This is cosmetic for the proof but hurts
traceability.

| Paper label | Lean counterpart | Status |
|-------------|------------------|--------|
| `lem:ordinal-factorisation` | `OrdinalDecomp.probLT_restrict_eq` | Lean'd but unlabeled |
| `cor:ordinal-marginal` | same as above (used inline) | Lean'd but unlabeled |
| `def:ordinal-decomp` | `OrdinalDecomp` struct | Lean'd but unlabeled |
| `def:ordinal-chain` | `OrdinalChainLift` struct | Lean'd but unlabeled |
| `lem:reducible-witness` | `OrdinalDecompOfReducible` | Lean'd but unlabeled |
| `cor:reducibility-transfer` | (none found) | not Lean'd |

### 6. Paper labels with no Lean counterpart (paper-only)

| Paper label | Lean status | Notes |
|-------------|-------------|-------|
| `lem:layered-from-step7` | paper-only (A5, landed `mg-a356`) | F7 was the corresponding Lean ticket, still on branch |
| `lem:exc-perturb` | paper-only | F6 / F6-prereq pipeline |
| `lem:one-elem-perturb` | paper-only | F6-prereq (landed paper-side `mg-17ef`) |
| `lem:enum` | partially — `bipartite_balanced_enum` for depth-2 only; depth-≥3 enumeration (F5a) not Lean'd on main | F5a bool-certificate prereq (`mg-fd88`) on branch only |
| `prop:in-situ-balanced` | mentioned in `LayerOrdinal.lean` docstring only | proof is paper-side strong induction (`step8.tex:2752+`) |

### 7. `lem_layered_reduction` is a thin wrapper

`lean/OneThird/Step8/LayeredReduction.lean:431` —

```lean
theorem lem_layered_reduction (L : LayeredDecomposition α)
    (balanced strictSubCex : Prop)
    (W : ReductionWitness L balanced strictSubCex) :
    LayeredReductionConclusion balanced strictSubCex :=
  W.conclusion
```

The theorem body literally returns the disjunction supplied by the
caller. The combinatorial content of `lem:layered-reduction`
(`step8.tex:2190-2334`, Steps 1-6 of the proof) is not proved in
Lean — it is assumed as `W.conclusion`. This is documented in the
docstring ("The combinatorial cut + perturbation argument is left to
the downstream window-localization gluing in `LayeredBalanced.lean`")
and not a bug per se, but anyone auditing the chain should know the
combinatorial theorem is not formalised yet.

## Summary table

| Category | Count | Severity |
|----------|-------|----------|
| Live `sorry` tokens in Step 8 | 1 | blocker |
| `axiom` declarations (any) | 0 | ok |
| Stale `step8.tex:N` refs in docstrings | ~25+ | cosmetic |
| Signature drift (paper ↔ Lean) | 1 (`thm:main-step8`) | tracked by §1 |
| Unlabeled Lean counterparts of paper lemmas | 6 | cosmetic |
| Paper-only labels (no Lean) | 5 | scope-known |
| Thin-wrapper theorems | 1 (`lem_layered_reduction`) | scope-known |

## Follow-ups spawned

Alignment tickets filed via `mg new` for each class of drift that
needs work — see §"Follow-ups" in the work-item tracker. Mayor mailed
about the F5/F7-never-landed situation (already tracked under
`mg-06f2`).

The audit itself is self-contained and does not gate F8 directly; F8
(whatever succeeds this) inherits the live sorry as its blocker.
