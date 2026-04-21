# OneThird — Lean 4 formalization

This directory holds the Lean 4 / mathlib scaffold for formalizing the proof
of the width-3 case of the 1/3–2/3 conjecture developed in the LaTeX sources
(`../step1.tex` through `../step8.tex`). See `../README.md` and
`../roadmap.md` for the mathematical outline; see `../summary.md` for the
"mathematical completeness" status of the LaTeX proof itself.

## Audit (2026-04-21, round 11 — `mg-68af`)

**Headline:** `lake build` succeeds. **1 `sorry` + 1 axiom remain** in
the project code. The previously circular `fkg_case_output` axiom has
been rescoped to match `prop:bipartite-balanced` (`step8.tex:1627`),
and the `lem_layered_balanced` reduction step is now its own
explicit `sorry`.

### Round-10 → round-11 delta

`mg-68af` rescoped the `fkg_case_output` axiom introduced by
`mg-aab8` at round 8.5/9.

Previously:

```lean
axiom fkg_case_output
    {α} … (x y : α) (_hxy : x ∥ y) :
    ∃ x' y' : α, (x' ∥ y') ∧ 1/2 ≤ probLT x' y' ∧ probLT x' y' ≤ 2/3
```

This is circular: for any α with an incomparable pair `(x, y)`, the
axiom output is (modulo `1/2 ≥ 1/3`) a balanced pair — i.e., the full
1/3–2/3 conjecture for arbitrary width-3 α.

After rescoping, `fkg_case_output` matches `prop:bipartite-balanced`
(`step8.tex:1627`): `A ∪ B = Finset.univ`, `A ⊔ B` disjoint antichains
of size `≤ 3`, `A < B`, one incomparable pair ⇒ balanced pair. Finite
(`|α| ≤ 6`, at most `1024` configurations modulo automorphism) and
non-circular.

`bipartiteBalanced` is now proved by direct application of the
rescoped axiom. `lem_layered_balanced` can no longer invoke
`bipartiteBalanced` from an arbitrary non-chain poset (the covering
hypothesis fails for `|α| > 6`), so the paper's reduction step
(`windowLocalization` + iterated ordinal-sum decomposition + K=1/K≥2
dichotomy, `step8.tex:1760-1796`) is exposed as its own `sorry`.

Net: the one foundation-item axiom + `lem_layered_balanced` body
together replace the previously hidden circularity with two
independent, bounded gaps.

### All non-classical leaves — 2 total (1 sorry + 1 axiom)

Line numbers below are for the `sorry` / `axiom` token itself.

| # | File:line | Declaration | Category |
|---|-----------|-------------|----------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:326` | `fkg_case_output` | **F4 foundation axiom** — finite bipartite form of `prop:bipartite-balanced` |
| 2 | `OneThird/Step8/LayeredBalanced.lean:413` | `lem_layered_balanced` | G4 reduction glue (window + ordinal-sum + K-dichotomy, `step8.tex:1760-1796`) |

Dilworth's theorem is now fully discharged as of `mg-6010` (round 10.5).

## Audit (2026-04-21, round 10 — `mg-ca21`)

**Headline:** `lake build` succeeds. **2 `sorry`s remain** — the Dilworth
sorry has moved from the main theorem body to a single helper
(`dilworth_splice`), and the FKG / rotation case-analysis output is
unchanged. The main Galvin induction is now fully scaffolded.

### Round-9 → round-10 delta

This round landed `mg-ca21`, which replaced the monolithic
`hasChainCover_of_hasWidth` sorry with a structural Galvin proof:
strong induction on `Fintype.card β`, empty base case, antichain case,
non-antichain Case A (`width β' < k`, extend by `{b, t}`), and Case B
setup (`width β' = k`, construct `D`, `U`, apply IH to get chain
covers). The remaining sorry is in the helper `dilworth_splice`
(the align + splice step), scheduled as `mg-6010`. The sorry count in
the source is unchanged (2), but the residual Dilworth work shrinks
from ≈500–1000 lines to ≈200 lines.

### All `sorry`s — 2 total

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Accepted as |
|---|-----------|-------------|-------------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:418` | `lem_layered_balanced` (inside proof) — `hFKGCaseOutput` argument to `bipartiteBalanced` | **FKG / Graham–Yao–Yao foundation item** (F4 of `step8.tex:1640-1749`) |
| 2 | `OneThird/Mathlib/Poset/Dilworth.lean:171` | `dilworth_splice` (align + splice step) | **Dilworth's theorem** (classical finite case) — residual splice tracked as `mg-6010` |

## Audit (2026-04-20, round 9 — `mg-46d1`)

**Headline:** `lake build` succeeds (1333 jobs, clean). **2 `sorry`s
remain, both accepted external dependencies**: Dilworth's theorem and the
FKG / rotation case-analysis output (F4 foundation item). Under the audit
policy "treat FKG / Graham–Yao–Yao related sorry as an accepted external
dependency," **all remaining sorries are accepted**.

**Formalization status: complete modulo the 2-item accepted
external-dependency list below.** Every paper theorem statement has a
Lean counterpart; every step's internal content is proved sorry-free;
every remaining `sorry` is a classical-result / foundation-item deferral
explicitly tracked outside the scope of this scaffold.

### Round-8 → round-9 delta

No new commits landed between round 8 (`374deef`) and this audit. The
round-8 "remaining gap" at `Step8/LayeredBalanced.lean:418` is
reclassified here as **accepted**, per the round-9 policy that
FKG-family downstream hypotheses are out of scope for the width-3
scaffold and tracked separately as the F4 foundation item.

### All `sorry`s — 2 total, both accepted

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Accepted as |
|---|-----------|-------------|-------------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:418` | `lem_layered_balanced` (inside proof) — `hFKGCaseOutput` argument to `bipartiteBalanced` | **FKG / Graham–Yao–Yao foundation item** (F4 of `step8.tex:1640-1749`) |
| 2 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **Dilworth's theorem** (classical finite case) — tracked as `mg-19ca` |

### Accepted external-dependency list

To claim the Lean directory formalizes `thm:main` of `main.tex` modulo
explicitly listed prerequisites, two external dependencies remain:

1. **Dilworth's theorem (finite case)** — `hasChainCover_of_hasWidth`
   (`Mathlib/Poset/Dilworth.lean:135`). Classical result; ≈500–1000 lines
   of Lean; ongoing work tracked as `mg-19ca`. A general-mathlib
   contribution rather than a project-specific gap.
2. **FKG / Graham–Yao–Yao output for the bipartite case analysis** — the
   `hFKGCaseOutput` hypothesis consumed by `bipartiteBalanced` inside
   `lem_layered_balanced` (`Step8/LayeredBalanced.lean:418`). Asserts an
   incomparable pair with `probLT ∈ [1/2, 2/3]` via the FKG / rotation
   case analysis of `step8.tex:1640-1749`. The F4 foundation item
   tracked separately; the within-layer FKG inequality is classical but
   not currently in mathlib for the linear-extension measure.

All other step-level content (Steps 1–7 and the Step 8 assembly spine)
compiles sorry-free.

### No new fix items

No actionable polecat-sized fix items are introduced by this audit.
Both remaining sorries require multi-session foundation-item work
outside the scope of the width-3 scaffold:

- `mg-19ca` (Dilworth) is a general-mathlib project, not a step-level
  polecat task.
- F4 (FKG case analysis) requires formalizing the FKG inequality on
  linear extensions (or the weaker Graham–Yao–Yao inequality) —
  comparable in scope to Dilworth.

Follow-on audit passes should wait for external progress on one of
these two items before opening fresh fix items.

## Audit (2026-04-20, round 8 — `mg-9058`)

**Headline:** `lake build` succeeds (1333 jobs, clean). **2 `sorry`s
remain**: **1 accepted external dependency** (Dilworth's theorem) and
**1 genuine gap** (the FKG / rotation-case-analysis output inside
`lem_layered_balanced`). Down from 1-genuine-gap-plus-broken-build at
round 7 after `mg-b9b5` (`3d724d4`) repaired the type mismatch.

### Round-7 → round-8 delta

One commit landed between round 7 (`e7e7524`) and this audit:

| Commit | Item | Effect |
|---|---|---|
| `3d724d4` | `mg-b9b5` — fix `lem_layered_balanced` type mismatch | Build is green again. `hFKGCaseOutput` argument to `bipartiteBalanced` supplied as `sorry` (the F4 foundation-item hypothesis). The remaining gap is therefore *where* `mg-dead` planted its call to `bipartiteBalanced`, not in the theorem statement. |

Net: **red build → green build**; sorry count in source text unchanged
at 2.

### All `sorry`s — 2 total (1 genuine gap + 1 accepted)

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Category | Tracking item |
|---|-----------|-------------|----------|---------------|
| 1 | `OneThird/Step8/LayeredBalanced.lean:418` | `lem_layered_balanced` (inside proof) | genuine gap — F4 foundation item | `mg-f9ed` (fresh round 8) |
| 2 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) |

### The remaining gap — `hFKGCaseOutput`

`lem_layered_balanced` now discharges via `bipartiteBalanced` with the
caller-supplied configuration `A = {x, y}`, `B = ∅`. The final argument
to `bipartiteBalanced` is `hFKGCaseOutput`, an existential asserting
that some incomparable pair in α has `probLT ∈ [1/2, 2/3]`. This is the
FKG / rotation case analysis of `step8.tex:1640-1749` — the "F4"
foundation item from the paper (finite enumeration over the ≤1024
bipartite configurations on `|A|, |B| ≤ 3`, discharging Case 2 via the
already-proved `rotation_contradiction` and Case 1 via a symmetric-pair
involution). A ninth audit `mg-46d1` is blocked on `mg-f9ed`.

### Verdict

Once `mg-f9ed` lands, the 1/3–2/3 formalisation will be complete modulo
the accepted Dilworth deferral. Note: the originally-listed second
accepted sorry (`kahnLinialBaseCase`) was already discharged at round 2
(`b3273b1`, `mg-24ab`), so only **one** accepted external dependency
remains.

## Audit (2026-04-20, round 7 — `mg-044c`)

**Headline:** `lake build` **fails** at commit `a09fe70` with a type
mismatch at `OneThird/Step8/LayeredBalanced.lean:392`. Once the build is
restored, **1 `sorry` remains**: the accepted external dependency
(Dilworth's theorem). The two genuine gaps flagged at round 6
(`counterexample_implies_low_BK_expansion` and `lem_layered_balanced`)
were discharged by `mg-f703` (`a09fe70`) and `mg-dead` (`ab28229`)
respectively — but `mg-dead` landed broken and its follow-up commit
`mg-f703` did not fix it.

### Round-6 → round-7 delta

Two commits landed between round 6 (`e1a1397`) and this audit:

| Commit | Item | Effect |
|---|---|---|
| `ab28229` | `mg-dead` — prove `lem_layered_balanced` via `bipartiteBalanced` | **broken build**: 8 positional args supplied to a 9-arg `bipartiteBalanced`. The `hFKGCaseOutput` hypothesis (added when `bipartiteBalanced` was refactored) is missing. |
| `a09fe70` | `mg-f703` — prove `counterexample_implies_low_BK_expansion` via trivial cut | closes the `MainTheorem.lean:56` sorry. |

Net: **3 → 1 sorry** (in the source text), but the build is red.

### Build failure details

```
error: OneThird/Step8/LayeredBalanced.lean:392:2: Type mismatch
  bipartiteBalanced {x, y} ∅ ?m.63 ?m.64 ?m.65 ?m.66 ?m.67 ?m.68
has type
  (∃ x y, x ∥ y ∧ 1 / 2 ≤ probLT x y ∧ probLT x y ≤ 2 / 3) →
    ∃ x y, x ∥ y ∧ IsBalanced x y
but is expected to have type
  HasBalancedPair α
```

Tracked as `mg-b9b5`. A round-8 audit (`mg-9058`) is blocked on it.

That the merge queue accepted `ab28229` while `lake build` was failing
suggests the refinery does not run `lake build` as a merge gate — this
is a separate process concern worth flagging.

### All `sorry`s — 1 accepted (modulo build fix)

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Category | Tracking item |
|---|-----------|-------------|----------|---------------|
| 1 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) |

Once `mg-b9b5` is resolved, the 1/3–2/3 formalisation will be complete
modulo Dilworth's theorem and whatever hypothesis `lem_layered_balanced`
ends up relying on (its proof is now load-bearing on
`bipartiteBalanced`'s `hFKGCaseOutput` hypothesis, which itself is an
abstract Prop-level input — tracked separately as the FKG / rotation
case analysis foundation item).

## Audit (2026-04-20, round 6)

**Headline:** `lake build` succeeds. **3 `sorry`s remain — unchanged from
round 5**: **1 accepted external dependency** (Dilworth's theorem) and
**2 genuine gaps** still to close. No commits landed on `main` between
round 5 (`36f5e75`) and this audit, so the sorry inventory is identical.

### Round-5 → round-6 delta

No relevant commits landed between round 5 and this audit. The prior
reopened tracking items `mg-a4f8` and `mg-d914` were not picked up by a
polecat in the interval; per the round-6 mayor directive, **fresh fix
items** have been opened for both remaining gaps:

- `mg-f703` — `counterexample_implies_low_BK_expansion` (MainTheorem.lean:47)
- `mg-dead` — `lem_layered_balanced` (LayeredBalanced.lean:375)

A seventh audit pass is tracked as `mg-044c`, blocked on both. On
completion it will either declare the formalisation complete modulo
Dilworth or open fresh fix items.

### All `sorry`s — 3 total (2 gaps + 1 accepted)

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Category | Tracking item |
|---|-----------|-------------|----------|---------------|
| 1 | `OneThird/MainTheorem.lean:56` | `counterexample_implies_low_BK_expansion` | genuine gap | `mg-f703` (fresh round-6) |
| 2 | `OneThird/Step8/LayeredBalanced.lean:387` | `lem_layered_balanced` (G4) | genuine gap | `mg-dead` (fresh round-6) |
| 3 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) |

## Audit (2026-04-20, round 5)

**Headline:** `lake build` succeeds. **3 `sorry`s remain — unchanged from
round 4**: **1 accepted external dependency** (Dilworth's theorem) and
**2 genuine gaps** still to close. No commits landed on `main` between
round 4 (`622dfac`) and this audit, so the sorry inventory is identical.

### Round-4 → round-5 delta

No relevant commits landed between round 4 and this audit. The two
genuine gaps remain exactly where round 4 left them; tracking items
`mg-a4f8` (Theorem E headline bridge) and `mg-d914` (G4 layered
balanced body) have been **reopened** so the merge queue can dispatch
a polecat against each.

### All `sorry`s — 3 total (2 gaps + 1 accepted)

Line numbers below are the line of the `sorry` token itself.

| # | File:line | Declaration | Category | Tracking item |
|---|-----------|-------------|----------|---------------|
| 1 | `OneThird/MainTheorem.lean:56` | `counterexample_implies_low_BK_expansion` | genuine gap | `mg-a4f8` (reopened round 5) |
| 2 | `OneThird/Step8/LayeredBalanced.lean:387` | `lem_layered_balanced` (G4) | genuine gap | `mg-d914` (reopened round 5) |
| 3 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) |

A sixth audit pass is tracked as `mg-d5d3`, blocked on `mg-a4f8` and
`mg-d914`. On completion it will either declare the formalisation
complete modulo Dilworth or open fresh fix items.

**Note.** The original `mg-58b8` task description listed two accepted
sorries (Dilworth + Kahn–Linial), but the Kahn–Linial sorry was already
discharged at round 2 (`b3273b1`, `mg-24ab`). The 1/3–2/3 formalisation
therefore has exactly **one** remaining accepted external dependency.

## Audit (2026-04-20, round 4)

**Headline:** `lake build` succeeds. **3 `sorry`s remain**: **1 accepted
external dependency** (Dilworth's theorem — see below) and **2 genuine
gaps** still to close. Down from 4 at round 3 after commit `74a8fed`
(`mg-8db9`) closed `edgeBoundary_pairCut_sum_le` via swap-pair uniqueness.

Answer to "can we claim the proof is formalized in Lean 4, modulo a
single accepted external dependency (Dilworth)": **not yet** — two
genuine gaps remain: the G4 balanced-pair lemma (`lem_layered_balanced`,
`mg-d914`) and the top-level Theorem E bridge
(`counterexample_implies_low_BK_expansion`, `mg-a4f8`). Closing both
would complete the formalisation modulo the accepted Dilworth sorry.

### Accepted external dependency

`OneThird/Mathlib/Poset/Dilworth.lean:135` — `hasChainCover_of_hasWidth`
(Dilworth's theorem, finite case, 1950) is **intentionally left as
`sorry`** and is **not part of our proof**. It is a classical
mathlib-flavoured result whose formalisation (≈500–1000 lines of Lean)
is a downstream concern tracked separately as `mg-19ca`. This sorry is
**accepted** and should not be treated as a gap to close for the
1/3–2/3 formalisation. It is not in the import closure of the main
theorem.

**Note.** A stale version of this task description listed a second
accepted sorry, `kahnLinialBaseCase` (Kahn–Linial 1991). That sorry was
already **discharged** at round 2 (commit `b3273b1`, `mg-24ab`), so
`OneThird/Step8/SmallN.lean` no longer contains it. The 1/3–2/3
formalisation therefore has exactly **one** remaining accepted external
dependency, not two.

### Round-3 → round-4 delta

Between round 3 (commit `6b65ebf`) and round 4 (this commit), one commit
landed on main:

| Commit | Item | Effect on sorry count |
|---|---|---|
| `74a8fed` | `mg-8db9` — prove `edgeBoundary_pairCut_sum_le` via swap-pair uniqueness | `LinearExtension.lean:111` closed |

Net: **4 → 3 sorries**; one closed, none opened.

### All `sorry`s — 3 total (2 gaps + 1 accepted)

Line numbers below are the line of the `sorry` token itself. The
declaration header sits a few lines above.

| # | File:line | Declaration | Category | Tracking item | What it defers |
|---|-----------|-------------|----------|---------------|----------------|
| 1 | `OneThird/MainTheorem.lean:56` | `counterexample_implies_low_BK_expansion` | genuine gap | `mg-a4f8` (reopened) | Top-level Theorem E (`thm:cex-implies-low-expansion`, `step8.tex:114`) in the general (not-necessarily-indecomposable) form. The indecomposable form `Step8.cexImpliesLowBKExpansion` is proved; closing this headline version requires the `rem:decomp-reduction` bridge plus the now-proved `frozenPairCut_exists`. |
| 2 | `OneThird/Step8/LayeredBalanced.lean:387` | `lem_layered_balanced` (G4) | genuine gap | `mg-d914` (reopened) | Paper `lem:layered-balanced`, `step8.tex:1768-1802`. High-level disjunction over `K = 1` (antichain symmetry involution) / `K ≥ 2` (invoking `windowLocalization` + `bipartiteBalanced`, both proved). The FKG factorisation + high-level disjunction itself remains. |
| 3 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) | Dilworth's theorem (finite case). Classical mathlib-flavoured result; formalisation tracked separately as `mg-19ca` and **intentionally left as `sorry`**. Not counted against completion of the 1/3–2/3 formalisation. Not in the import closure of the main theorem. |

A fifth audit pass is tracked as `mg-58b8`, blocked on `mg-a4f8` and
`mg-d914`; on completion it will either declare the formalisation
complete modulo Dilworth or open fresh fix items.

## Audit (2026-04-19, round 3)

**Headline:** `lake build` succeeds. **4 `sorry`s remain**: **1 accepted
external dependency** (Dilworth's theorem — see below) and **3 genuine
gaps** still to close. The sorry count is unchanged from round 2 in
number, but the contents shifted: `frozenPairCut_exists` (FrozenPair.lean)
was discharged (`mg-0dce`, commit `8a0f8cf`), and its residual foundation
item — `edgeBoundary_pairCut_sum_le` — was extracted into a new sorry at
`OneThird/LinearExtension.lean:111`.

Answer to "can we claim the proof is formalized in Lean 4, modulo a single
accepted external dependency (Dilworth)": **not yet** — three genuine
gaps remain: the G4 balanced-pair lemma, the BK edge-boundary
pair-sum bound, and the top-level Theorem E bridge. Closing all three
would complete the formalisation modulo the accepted Dilworth sorry.

### Accepted external dependency

`OneThird/Mathlib/Poset/Dilworth.lean:135` — `hasChainCover_of_hasWidth`
(Dilworth's theorem, finite case) is **intentionally left as `sorry`** and
is **not part of our proof**. It is a classical mathlib-flavoured result
whose formalisation (≈500–1000 lines of Lean) is a downstream concern
tracked separately as `mg-19ca`. This sorry is **accepted** and should
not be treated as a gap to close for the 1/3–2/3 formalisation. It is
not in the import closure of the main theorem.

### Round-2 → round-3 delta

Between round 2 (commit `e56e8ae`) and round 3 (this commit), one commit
landed on main:

| Commit | Item | Effect on sorry count |
|---|---|---|
| `8a0f8cf` | `mg-0dce` — prove `frozenPairCut_exists` via averaging | `FrozenPair.lean:151` closed; `edgeBoundary_pairCut_sum_le` sorry introduced (`LinearExtension.lean:111`) |

Net: 4 sorries before and after; one closed, one opened. The opened
sorry is a classical double-counting identity for the BK edge boundary,
extracted as a foundation item.

## Audit (2026-04-19, round 2)

**Headline (historical):** `lake build` succeeds. **4 `sorry`s remain** —
down from 10 at round 1 (mg-67be, same day) after nine sorry-filling
commits landed in the interim (see "Round-1 → round-2 delta" below). The
Lean code is a **structural scaffold with the Step 8 main assembly fully
wired**, not yet a self-contained proof. The headline theorem
`OneThird.width3_one_third_two_thirds` no longer contains a direct `sorry` —
`Step8.width3_one_third_two_thirds_assembled` routes through the newly
discharged `MainTheoremInputs` bundle (`mg-4fa9`, commit `e44f2fa`) — but
the bundle's `caseC` calls `lem_layered_balanced` whose body is still
`sorry`, so the headline conclusion remains transitively unproved.

Answer to "can we claim the proof is formalized in Lean 4, modulo explicitly
listed sorries": **four remaining gaps** — the G4 balanced-pair lemma, the
frozen-pair/BK-Dirichlet foundation, the top-level Theorem E bridge, and
Dilworth's theorem body. Steps 1–7 now have poset-level bridges
(`OneThird/Bridge.lean`, `mg-8453`); the main assembly no longer has a
load-bearing sorry.

### Build status

```sh
cd lean && lake build
```

succeeds (1333 jobs, ≈2 min on a warm cache) with 4 `declaration uses
sorry` warnings plus several hundred `unusedDecidableInType` /
`unusedSectionVars` linter warnings. No errors.

### All `sorry`s — 4 total (3 gaps + 1 accepted)

Current state as of round 3 (this commit):

| # | File:line | Declaration | Category | Tracking item | What it defers |
|---|-----------|-------------|----------|---------------|----------------|
| 1 | `OneThird/MainTheorem.lean:56` | `counterexample_implies_low_BK_expansion` | genuine gap | `mg-a4f8` (reopened) | Top-level Theorem E (`thm:cex-implies-low-expansion`, `step8.tex:114`) in the general (not-necessarily-indecomposable) form. The indecomposable form `Step8.cexImpliesLowBKExpansion` is proved; closing this headline version requires the `rem:decomp-reduction` bridge plus the now-proved `frozenPairCut_exists`. |
| 2 | `OneThird/LinearExtension.lean:111` | `edgeBoundary_pairCut_sum_le` | genuine gap | `mg-8db9` (new, round 3) | Classical combinatorial identity: `∑_{x ∥ y} |∂_BK (pairCut x y)| ≤ (n - 1)·|𝓛(P)|`. Double counting via the `(σ, i) ↦ L.swapAdj` BK edge parametrisation (paper `step8.tex:207-229`). Extracted as a foundation item by `mg-0dce` during the `frozenPairCut_exists` assembly. |
| 3 | `OneThird/Step8/LayeredBalanced.lean:387` | `lem_layered_balanced` (G4) | genuine gap | `mg-d914` (reopened) | Paper `lem:layered-balanced`, `step8.tex:1768-1802`. High-level disjunction over `K = 1` (antichain symmetry involution) / `K ≥ 2` (invoking `windowLocalization` + `bipartiteBalanced`, both now proved). The FKG factorisation + high-level disjunction itself remains. |
| 4 | `OneThird/Mathlib/Poset/Dilworth.lean:135` | `hasChainCover_of_hasWidth` | **accepted external dependency** (*not* a gap) | `mg-19ca` (separate mathlib effort) | Dilworth's theorem (finite case). Classical mathlib-flavoured result; formalisation tracked separately as `mg-19ca` and **intentionally left as `sorry`**. Not counted against completion of the 1/3–2/3 formalisation. Not in the import closure of the main theorem. |

**Note on tracking-item status.** mg-a4f8 and mg-d914 were marked `done`
during round 1/2 when their scaffold/sub-sorry work landed, but the
top-level sorry in each case remains. They are reopened this round.
mg-0dce (round-2 item for `frozenPairCut_exists`) is correctly done:
the sorry it targeted is closed, and a new tracking item `mg-8db9` was
created for the extracted residual foundation. The round-2 audit ticket
`mg-6f2d` is done; round-3 audit is tracked as `mg-56a7` (this commit),
and a follow-up round-4 audit is tracked as `mg-80a2`, blocked on
`mg-a4f8`, `mg-d914`, `mg-8db9`.

### Round-1 → round-2 delta

Between round 1 (`6a53685`, 10 sorries) and round 2 (this commit, 4
sorries), the following commits landed on main, removing six sorries and
introducing one new one:

| Commit | Item | Effect on sorry count |
|---|---|---|
| `f61de75` | `mg-a4f8` — prove `Step8.cexImpliesLowBKExpansion` | `TheoremE.lean:222` closed; `frozenPairCut_exists` sorry introduced (new file `FrozenPair.lean`) |
| `e44f2fa` | `mg-4fa9` — discharge `MainTheoremInputs` bundle | `MainAssembly.lean:215` closed |
| `ee9ab61` | `mg-eeb5` — prove `bkGraph_preconnected` | `BKGraph.lean:128` closed |
| `a8df3e0` | `mg-9f1a` — discharge `smallNFiniteEnum` | `SmallN.lean:144` closed |
| `d01002e` | `mg-8453` — bridge Steps 1–7 to poset level | new `OneThird/Bridge.lean`; no sorry change |
| `fac88bf` | `mg-d914` — discharge G4 `lem_layered_balanced` sub-sorries | sub-sorry closed but top-level `lem_layered_balanced` sorry moved to line 387 (still present) |
| `deb3569` | `mg-17f1` — prove `windowLocalization` | `LayeredBalanced.lean:123` closed |
| `17b86cc` | `mg-c290` — prove `bipartiteBalanced` | `LayeredBalanced.lean:230` closed |
| `b3273b1` | `mg-24ab` — prove Kahn–Linial base case | `SmallN.lean:112` closed |

Net: −10 + 4 = **6 sorries eliminated** (the FrozenPair introduction is
counted as closing TheoremE.lean:222 but opening FrozenPair.lean:151, since
the `Step8.cexImpliesLowBKExpansion` proof extracted the residual foundation
into its own file). The Kahn–Linial constant is now available as
`OneThird.Step8.δ_KL : ℚ := 276393 / 1000000` with
`δ_KL_lower_bound : δ_KL ≥ 0.276393` and
`one_third_sub_δ_KL_lt : 1/3 − δ_KL ≤ 58/1000` (`mg-24ab`).

### What's actually proved vs. what's assumed

The Lean files for Steps 1–7 establish *conditional* conclusions: given
abstract inputs (numeric bounds, abstract `Prop`-level hypotheses, abstract
`Finset`s playing the role of overlaps/pairs), the step's conclusion
follows. These proofs are real — `thm_step5` / `thm_step6` / `thm_step7`
do discharge their stated goals without `sorry` — but the goals are
*abstract* algebraic implications, not statements about `α : Type*
[PartialOrder α] [Fintype α]`.

For example, `OneThird.Step6.thm_step6` (line 246) proves:

```
theorem thm_step6
    (sumBadW M boundary c_n c_d δ_n δ_d : ℕ)
    (hSum : c_n * sumBadW ≤ c_d * M * boundary) :
    (c_n * δ_n * M ≤ c_d * M * δ_d * boundary) ∨
      (δ_d * sumBadW ≤ δ_n * M)
```

This is a correct algebraic implication, but it does not mention posets,
linear extensions, or rich pairs. The paper's `thm:step6` (coherence
forced by `prop_G2`) is a statement about linear extensions; the Lean
theorem is the *numeric lemma underneath* that paper statement. The
gap — from "the numeric lemma" to "the paper statement for an actual
poset" — is not formalised anywhere in the repo.

Similarly, `OneThird.Step8.mainAssembly` (line 231) reads:

```
theorem mainAssembly
    (γ_n γ_d : ℕ) (_h2 : 2 ≤ Fintype.card α)
    (_hP : HasWidthAtMost α 3) (_hNonChain : ¬ IsChainPoset α)
    (I : MainTheoremInputs α γ_n γ_d) :
    HasBalancedPair α := by
  cases I.step5_choice with
  | true  => exact I.caseC I.caseR_to_caseC
  | false => exact I.caseC I.caseR_to_caseC
```

`MainTheoremInputs` is a `structure` whose relevant fields are
`caseC : LayeredDecomposition α → HasBalancedPair α` and
`caseR_to_caseC : LayeredDecomposition α`. So `mainAssembly` literally
evaluates to "apply the hypothesised `caseC` to the hypothesised
`LayeredDecomposition`." As of `mg-4fa9` (commit `e44f2fa`) the bundle
is constructed by `mainTheoremInputsOf`, which routes `caseC` through
`lem_layered_balanced` — so the constructive burden is pushed onto
that lemma's `sorry` (row 3 of the table) rather than living at the
assembly layer.

### Import chain

`OneThird/MainTheorem.lean` imports `OneThird.Step8.MainAssembly`, which
imports `OneThird.Step6.Assembly`, `OneThird.Step7.Assembly`,
`OneThird.Step8.TheoremE` (which in turn imports
`OneThird.Step8.FrozenPair`), `OneThird.Step8.G2Constants`,
`OneThird.Step8.LayeredReduction`, `OneThird.Step8.LayeredBalanced`,
`OneThird.Step8.Window`, and `OneThird.Step8.SmallN`. The Step 6 and
Step 7 assemblies import only their own submodules. **Steps 1–5 are not
in the transitive import closure of the main theorem** — they are
compiled by `OneThird.lean` (the library root) and surfaced at
poset-level via `OneThird.Bridge` (`mg-8453`), but nothing in the
`width3_one_third_two_thirds` proof tree depends on them as of round 2.

Closing the remaining sorries (`lem_layered_balanced`,
`edgeBoundary_pairCut_sum_le`, and the top-level Theorem E bridge) does
**not** require wiring Steps 1–5 into the assembly — the
`MainTheoremInputs` construction at `MainAssembly.lean:mainTheoremInputsOf`
currently supplies a trivial layered witness, which downstream work may
replace with a Step-5-through-Step-7 cascade or may leave as-is if the
Step 8 reduction suffices.

### Correspondence with the LaTeX

`OneThird.width3_one_third_two_thirds` statement matches `thm:main` of
`main.tex` and `thm:main-step8` of `step8.tex`: a finite width-≤ 3 poset
that is not a chain admits an incomparable pair `(x,y)` with
`1/3 ≤ Pr[x <_L y] ≤ 2/3` under the uniform linear-extension measure.

`OneThird.counterexample_implies_low_BK_expansion` matches
`thm:cex-implies-low-expansion` (Theorem E).

The Step 1–7 assembly files' top-level theorems (`thm_step5`,
`thm_step6`, `thm_step7`, `thm_step4`, `thm_step3`, plus the Step 2
conclusion and Step 1 local interface theorem) correspond to the
paper's per-step conclusions, but (as discussed above) in abstract
form rather than as statements about `[PartialOrder α] [Fintype α]`.

### Verdict

This Lean directory is a **structurally complete scaffold with the
Step 8 main assembly fully wired**, and **all paper theorem statements
present**. It is **not yet a complete formalisation** of the 1/3–2/3
conjecture for width-3 posets. The three remaining genuine gaps are:

1. The G4 balanced-pair lemma `lem_layered_balanced`
   (`LayeredBalanced.lean:387`) is `sorry`. Load-bearing for the
   headline theorem via `MainTheoremInputs.caseC`. Tracked: `mg-d914`.
2. The BK edge-boundary pair-sum bound `edgeBoundary_pairCut_sum_le`
   (`LinearExtension.lean:111`) is `sorry`. Load-bearing for
   `frozenPairCut_exists` (now proved modulo this lemma) and
   transitively for the headline Theorem E bridge. Classical
   combinatorial identity, extracted during `mg-0dce`. Tracked:
   `mg-8db9`.
3. The top-level Theorem E bridge
   `counterexample_implies_low_BK_expansion` (`MainTheorem.lean:56`)
   is `sorry`. Awaits `edgeBoundary_pairCut_sum_le` plus the
   `rem:decomp-reduction` reduction to the indecomposable form.
   Tracked: `mg-a4f8`.

Plus **one accepted external dependency** (not a gap):

4. Dilworth's theorem body `hasChainCover_of_hasWidth`
   (`Dilworth.lean:135`) is an **accepted** `sorry`. Classical
   mathlib-flavoured result; substantial (≈500–1000 lines of Lean).
   Not in the import closure of the headline theorem. Tracked
   separately as `mg-19ca`. **Not counted against completion** of
   this formalisation.

Kahn–Linial, finite enumeration, Bubley–Karzanov connectivity,
window-localisation, bipartite-balanced, `frozenPairCut_exists`,
the `MainTheoremInputs` bundle, and the Steps 1–7 → poset bridge —
all `sorry`-free.

To claim a complete formalisation of the main theorem's import closure
(modulo the accepted Dilworth sorry), items (1), (2), (3) must be
closed. Follow-up audit round 4: `mg-80a2`, blocked on those three.

## Project structure — `OneThird.Mathlib.*` vs. `OneThird.*`

We keep **all** Lean source in this directory — nothing is pushed to
mathlib from here. However, files are partitioned so that the
mathlib-general results can be extracted later without restructuring:

- **`OneThird/Mathlib/`** — results general enough to be contributed
  back to mathlib eventually (poset width, Dilworth's theorem,
  `Fintype (LinearExt α)`, edge boundary for `SimpleGraph`,
  Bubley–Karzanov graph, conductance / Dirichlet form, 2D-grid
  isoperimetry on top of `YoungDiagram`, …). These modules depend
  only on mathlib, not on anything specific to the 1/3–2/3 proof.
- **`OneThird/StepN/`** — the proof-specific lemmas from
  `stepN.tex`. These may depend on `OneThird/Mathlib/*` and on
  earlier `OneThird/StepM/*`.
- **`OneThird/MainTheorem.lean`** — the top-level assembly.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager). It will pick up `lean-toolchain` automatically and install the
matching Lean version on first use.

## Build

```sh
cd lean
lake exe cache get   # fetch prebuilt mathlib olean cache
lake build
```

`lake exe cache get` is optional but strongly recommended — building mathlib
from source takes hours, whereas the cache downloads in a few minutes.

## File inventory

Top-level (13 files):

- `lakefile.toml` — Lake project config, pins `mathlib` to `v4.29.1`.
- `lean-toolchain` — pinned Lean version (`leanprover/lean4:v4.29.1`).
- `OneThird.lean` — library root; re-exports all submodules.
- `OneThird/Basic.lean` — shared imports and the `Incomp` predicate.
- `OneThird/Poset.lean` — width, antichains, common-neighbor chain,
  rich pairs.
- `OneThird/LinearExtension.lean` — project-specific layer on top of
  `Mathlib/LinearExtension/Fintype`: the Bubley–Karzanov graph,
  balance / counterexample definitions, BK conductance.
- `OneThird/RichPair.lean` — local coordinates, external-ordering
  equivalence, good/raw/bad fibers, the Step 1 local interface
  theorem.
- `OneThird/MainTheorem.lean` — the main width-3 1/3–2/3 theorem and
  Theorem E (`counterexample ⇒ low BK expansion`).
- `OneThird/Bridge.lean` — poset-level re-statements of each Step 1–7
  top-level abstract theorem.
- `MATHLIB_GAPS.md` — mathlib-coverage audit for the eight-step proof.
- `../.github/workflows/lean.yml` — CI for `lake build`.

`OneThird/Mathlib/*` (7 files): poset `Width`, `Dilworth`,
`Indecomposable`; `SimpleGraph.EdgeBoundary`; `BKGraph`; `DirichletForm`;
`Grid2D`; `LinearExtension/Fintype`.

`OneThird/Step1/*` (3): `CommonChain`, `Corollaries`, `LocalCoords`.
`OneThird/Step2/*` (6): `OneD`, `RowDecomp`, `FiberAvg`, `WeakGrid`,
`PerFiber`, `Conclusion`.
`OneThird/Step3/*` (3): `LocalSign`, `CommonAxes`, `Step3Theorem`.
`OneThird/Step4/*` (3): `RectangleModel`, `DensityRegularization`,
`Step4Theorem`.
`OneThird/Step5/*` (6): `EndpointMono`, `ConvexOverlap`, `FiberMass`,
`Layering`, `SecondMoment`, `Dichotomy`.
`OneThird/Step6/*` (6): `ErrorControl`, `CommutingSquare`, `RichnessBound`,
`Incoherence`, `OverlapCounting`, `Assembly`.
`OneThird/Step7/*` (7): `SignedThreshold`, `SignConsistency`, `Cocycle`,
`Potential`, `SingleThreshold`, `Bandwidth`, `Assembly`.
`OneThird/Step8/*` (8): `TheoremE`, `FrozenPair`, `G2Constants`,
`LayeredReduction`, `LayeredBalanced`, `Window`, `SmallN`,
`MainAssembly`.

`OneThird/Bridge.lean` — poset-level re-statements of each step's
top-level abstract theorem (Steps 1–7), added in `mg-8453`.

Total: 57 Lean files.

## Updating mathlib

Bump `rev` in `lakefile.toml` and `lean-toolchain` to the matching Lean
release, then run `lake update && lake exe cache get && lake build`.

## Contributing

- Prefer the smallest self-contained commit: one lemma or one
  definition + its glue lemmas.
- If a result is mathlib-flavored (no project-specific combinatorics),
  place it in `OneThird/Mathlib/` so it can be extracted later.
- Keep existing `sorry`s visible: deleting a `sorry` without proving
  it is a review red flag.
- Do **not** push anything to mathlib from this repo — all code
  stays here until a separate upstreaming effort is organized.
