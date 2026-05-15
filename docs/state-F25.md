# State F25 — the Hypothesis A constants audit (BK/Cheeger execution of milestone 1 part (iii)) — cumulative state

**Ticket:** mg-c6f2. **Branch:** `polecat-mg-c6f2`. **Parent:** mg-a30d (F24).
**Type:** paper-and-pencil; no HPC; no Lean; no new axioms.
**Status:** single-session, delivered.
**Verdict:** **RED-hypothesis-A-false-small-γ-tail** (precisely located).

---

## Session 1 — 2026-05-15 (sole session, complete)

### Inputs read

- **`docs/compatibility-geometry-F24-route-fork-comparison.md`** (full) — F25 scoping in §4; the `∃T` collapse argument in §1.3; the constants inventory and dependency map in §1.2/§1.3.
- **`/Users/daniel/research/one_third_width_three/step8.tex`** (full, 3237 lines) — Hyp A statement (`hyp:arith` line 505); constants discussion (`rem:final-constants-audit` lines 1751–1870); G2 (`prop:G2`); G3 (`lem:layered-reduction` lines 2190–2311 — the load-bearing line `K_0 := max(2w+2, 2w/γ+4)` is line 2205); G4 (`lem:layered-balanced`); the cascade discharge `rem:G2-order`.
- **`/Users/daniel/research/one_third_width_three/step5.tex`** (partial, 1184 lines, key sections read) — `prop:single-triple` (lines 106–195); `lem:convex-overlap` (G2, lines 357–459) with `c ∈ (0, 1)` "absolute"; `cor:second-moment` (lines 1107+) — `T_0` implicit, `c_5(T) = (c_5^⋆)²/16`.
- **`/Users/daniel/research/one_third_width_three/step4.tex`** (partial, 1361 lines) — `lem:rect-stable` (lines 427–541): **`c_4 = c_0 = c_1/4 = 1/8`, `C_4 = C_0 = C'/4 = 12/4 = 3`** (pinned numerically); `prop:G2-step4` block-transfer with `ε' = √(4ε/ρ)`; `lem:many-nonconst` (lines 728–) with `c_1 = 1/2`.
- **`/Users/daniel/research/one_third_width_three/step6.tex`** (partial, 1293 lines) — `lem:sum-step4` (lines 266+): `c_1 = c δ_0/(4M)`; `lem:overlap-counting` (lines 347+): `M = 2 M_0 + 1` with `M_0 = O(1)`. **Line 469 explicitly disclaims numerical pinning of `M`.**
- **`/Users/daniel/research/one_third_width_three/step7.tex`** (partial, 1630 lines) — `prop:71/72/73` (lines 1112–1271). **`C_7` is `step8`'s aggregate of `step7`'s `o(1)`-rates; not defined inside `step7`.**
- **`/Users/daniel/research/one_third_width_three/step1.tex`** (partial, 732 lines) — `thm:interface` (line 144+): fiber-density `|F_α| ≳ c_0^{(1)} t² · |L(P)|/(|A||B||C|)`, bad-set thickness `|B_α| ≤ C·t·|L(P)|/(|A||B||C|)` — both with unpinned absolute constants.

### Findings, ordered

#### F25.1 — Subtask 1: the `∃T` collapse to `T = T_0` (F24 §4 step 1)

The T-monotonicities `c_5^⋆ ≍ T^{−O(1)}` (decreasing) and `w(T)` non-decreasing are **asserted** in `step8.tex` `rem:final-constants-audit` but **not formally re-derived** as stand-alone lemmas in `step5/7`. Both are structurally intuitive (larger T shrinks the T-fat support `A', B'` and increases the bandwidth `K_bw`); F25 inherits them as sealed F24 inputs and confirms the collapse `T = T_0`. The Hypothesis A `∃T` quantifier reduces to the single γ-inequality
```
   γ² · c_5(T_0) · c_6 · δ_0(γ) ≥ 8     [or equiv c_5^⋆(T_0, γ)² ≥ 128/(γ² c_6 δ_0)].
```
**`T_0` is absolute but numerically unpinned** in `step5.tex` `cor:second-moment` (it's the implicit threshold making `|B_α|/|F_α| = O(1/T) ≤ 1/2`, which requires upstream constants `C` and `c_0^{(1)}` from `step1.tex` that are not numerically given).

#### F25.2 — Subtask 2: explicit γ-dependences (F24 §4 step 2)

| quantity | γ-dependence | source |
|---|---|---|
| `K_0(γ, w)` | **`max(2w+2, 2w/γ + 4)`** — explicit `1/γ`-blowup | `step8.tex` `lem:layered-reduction` line 2205 |
| `δ_0(γ)` | `δ_0 = min(1/(4 C_7), 1/(2 w K_0))` ∼ `γ/(4w²)` for `γ < w²/C_7` | derived |
| `c_5^⋆(T_0, γ)` | upper bound `c_5^⋆ ≤ c < 1` (G2 absolute); **no positive lower bound extracted from `step5.tex`** | `step5.tex` `prop:single-triple` |
| `c_5(T_0)` | `= (c_5^⋆/4)² = (c_5^⋆)²/16 ≤ c²/16 < 1/16` | `step5.tex` `cor:second-moment` |
| `c_6, C_7, w(T_0)` | absolute (γ-independent); **not numerically pinned** | `step6/7/8` |

**Crux 2 (γ-dependence of `K_0`)** — F24's "second crux" — is **explicitly written into `step8`'s G3 proof** and has the form `K_0 = 2w/γ + 4` for `γ < 1`. The `1/γ` factor is *structural*: it comes from `|W|/|X| ≲ γ` necessary for window-removal in the perturbation bound `2|W|/(|X|−|W|+1)` to preserve γ-counter\-example property. Removing it requires not constants-tightening but a structurally new deep-layering reduction.

**Crux 1 (γ-dependence of `c_5^⋆`)** — F24's "first crux" — turns out *worse than the audit can determine*: `step5.tex` extracts no positive lower bound on `c_5^⋆`'s γ-dependence at all (only `c_5^⋆ ≤ c < 1` universal upper bound). The crux question — "does `c_5^⋆(T_0, γ)` stay bounded below as γ → 0?" — has no answer in the existing text.

#### F25.3 — Subtask 3: evaluate Hyp A on `γ ∈ (0, 0.057)` (F24 §4 step 3)

In the small-γ regime (`γ < γ_⋆ = w²/C_7`), Hyp A reduces algebraically to
```
   (c_5^⋆)² · γ³  ≥  512 w² / c_6.                          (★★★)
```
The LHS is bounded above by `c² γ³` (since `c_5^⋆ ≤ c < 1`), which → 0 cubically as γ → 0; the RHS is a fixed positive constant. **Therefore Hyp A is violated for every `γ < γ_crit := (512 w² / ((c_5^⋆)² c_6))^{1/3} > 0`.**

For plausible numerical realisations of the unpinned constants:
- pessimistic estimate: `γ_crit ≈ 936` (with `c_5^⋆ = 1/4`, `c_6 = 10⁻³`, `w² = 100`).
- optimistic estimate: `γ_crit ≈ 27` (with `c_5^⋆ = 1/2`, `c_6 = 1/10`, `w = 1`).

**Both `≫ 0.057` (the upper end of the Hyp-A window).** To get `γ_crit ≤ 0.057` would require `(c_5^⋆)² c_6 / w² ≥ 2.77 · 10⁶`, which is structurally impossible (`c_5^⋆ ≤ c < 1`, `c_6 = c_4/(4M) < 1/8`, `w ≥ 1`).

**Result:** Hyp A fails on at least a `(0, γ_crit)` tail with `γ_crit > 0`; for plausible numbers, **fails on the entire Hyp-A window `(0, 0.057)`**.

#### F25.4 — Subtask 4: `ε / n_0` cascade cross-check (F24 §4 step 4)

The cascade `γ → T_0 → δ_0 → ε → n` is **structurally realisable** *whenever Hyp A holds*: `ε = δ_0/(2K(T_0)) > 0` well-defined; `n_0(γ, T_0) = Θ(C_exc(T_0)/γ)` polynomial in `1/γ`; `lem:small-n` covers `n ≤ n_0`. The cascade is *not* the bottleneck. The bottleneck is Hyp A itself failing on the small-γ tail (F25.3), leaving `n > n_0(γ, T_0)` uncovered (the "large-n tail" that `step8.tex`'s scope note flags).

#### F25.5 — The verdict: RED, not AMBER

F24 §4 chartered AMBER as "a single un-optimised lemma whose constant can be sharpened" and RED as "genuinely false in the small-γ tail; barrier constant named." The audit's finding meets the RED criterion: the barrier is the *order* of `K_0`'s γ-dependence (`1/γ`), not the size of an absolute constant. Constants-tightening cannot fix a `γ → 0` cubic decay against a fixed positive constant.

#### F25.6 — Constants pinned vs. unpinned

| pinned | unpinned (left as absolute placeholders) |
|---|---|
| `c_4 = 1/8` | `T_0` |
| `C_4 = 3` | `c_5^⋆(T_0, γ)` lower bound |
| `C_4/c_4 = 24` | `c_6` (via `M_mult`) |
| `K_0(γ, w) = max(2w+2, 2w/γ + 4)` | `C_7` |
| `δ_0(γ) ∼ γ/(4w²)` for small γ | `w(T_0)` |
| `c_5(T_0) ≤ (c²)/16 < 1/16` | `C_2(T)` (poly in T) |

### Operational consequence for milestone 1

**The in-tree BK/Cheeger spine `main.tex` + Steps 1–8 as written does NOT unconditionally prove width-3 1/3–2/3.** The small-γ, large-n tail `γ ∈ (0, γ_crit)` and `n > n_0(γ, T_0)` is uncovered. The "uncovered tail" is exactly the regime `step8.tex`'s own scope note (Theorem `thm:main-step8` scope discussion + `rem:n-dependence-g1`) flags. Milestone 1 part (iii) is NOT closed by Route B as scoped.

**Both F24 routes now have located gaps:**
- Route A — `n`-uniform `(CM-rel)` proof, F23-evidence-disfavoured.
- Route B — `K_0(γ, w)`-driven small-γ-tail failure of Hyp A, *structural* to layered-reduction approach.

Re-ranking is a PM decision, not an F25 finding.

### Deliverables

- `docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md` (~13k words) — the audit, with full constants inventory, derivation, three subtasks, verdict.
- `docs/state-F25.md` (this file).

### Trust surface

**Unchanged.** Paper-and-pencil only. No Lean changes, no new axioms, no HPC, no computation. The F10 cohomological core (parts i–ii, unconditional via F17+F18), the F19–F23 chamber-Morse arc (parked), and the Lean `width3_one_third_two_thirds` 4-axiom artifact are all untouched.

### What F25 does not establish / what F26 would have to be

F25 does not propose a specific F26. The audit's RED finding implies F26 (if commissioned) would not be a constants-tightening exercise. Plausible F26 attack surfaces, all of them *structural-research-grade*:

- **Re-prove G3 (`lem:layered-reduction`) with a γ-independent (or weakly γ-dependent) `K_0`** — requires deep-layering balanced-pair extraction without window-removal.
- **Generalise G4 (`lem:layered-balanced`) to deep layerings** — the shallow-`K` argument averages on a bounded interaction window; extending this to `K = ω(1/γ)` requires a different argument.
- **Replace the layered-reduction approach entirely** for case (C) of Step 5 — a direct BK-expansion / Cheeger argument on layered structures, bypassing G3/G4.

None of these is a constants audit. All are structural-mathematical research questions.

### Open questions / open scope items

- `γ_crit` numerical value — depends on numerical pinning of `c_5^⋆, c_6, w(T_0)`. F25 does not pin these (they are not pinned in the existing text).
- The first-crux question — "does `c_5^⋆(T_0, γ)` admit a positive lower bound in γ?" — remains unanswered in the existing text and is not the F25 bottleneck (the K_0 cubic decay already forces RED regardless).
- The `T_0` value question — `T_0` depends on `step1.tex`'s `C` and `c_0^{(1)}` which are not numerically given. Pinning these is a *separate* F26-class audit of `step1.tex`'s interface theorem.

### Protocol log

- 2026-05-15 — claimed mg-c6f2; registered `pogo schedule` mail-check on `*/10 * * * *`; read F24 + step1/4/5/6/7/8; wrote audit + state; ready to commit.

---

*Single-session F25; ledger frozen at session 1 close. If F26 is commissioned, fork a new state document — F25 is the audit, not the continuation.*
