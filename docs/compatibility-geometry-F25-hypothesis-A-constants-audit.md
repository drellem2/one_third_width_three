# Compat-Geom — F25: the Hypothesis A constants audit (BK/Cheeger execution of milestone 1 part (iii), Route B post-F24) — mg-c6f2

**Branch:** `polecat-mg-c6f2` (mg-c6f2).
**Parent:** mg-a30d (F24, **GREEN-route-B-recommended**) §4 — F25 fully scoped there; this doc faithfully executes that scoping.
**Chain:** F10 → F17 (mg-4d3a) → F18 (mg-d039) → F19 → F20 → F21 (mg-a2cb) → F22-HPC (mg-43fb / mg-0c5d) → F23 (mg-531f) → F24 (mg-a30d) → **F25 (mg-c6f2)**.
**Type:** Structural / paper-and-pencil constants audit of the sealed Steps-1–7 lemmas plus the Step-8 G3/G4 items. **No HPC; no Lean; no new axioms; no computation; no symbolic algebra system.** Cross-repo read of `one_third_width_three` (`main.tex`, `step1.tex`–`step8.tex`). Single-session; cumulative state at `docs/state-F25.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish internally; no external collaboration); 2026-05-14T17:23Z (milestone 1 — full gap-free width-3 proof, no sketches or gaps); 2026-05-14T22:32Z ("keep pushing").

---

## Verdict: **RED-hypothesis-A-false-small-γ-tail.**

**Hypothesis A — `step8.tex` `hyp:arith` / `eq:arith-explicit` — fails on a precisely-located small-γ tail of the Hypothesis-A window `γ ∈ (0, 1/3 − δ_KL) ≈ (0, 0.057)`.** The barrier is structural to the BK/Cheeger argument as written and is identified to a single source: the threshold `K_0(γ, w) = max(2w+2, 2w/γ + 4)` extracted from the layered-reduction lemma (`step8.tex` Lemma `lem:layered-reduction`, GAP G3). This `K_0`-dependence forces the cascade target `δ_0(γ) := min(1/(4C_7), 1/(2wK_0))` to **decay linearly in γ for small γ**, which then forces the Hypothesis-A LHS `γ² · c_5(T_0) · c_6 · δ_0(γ)` to **decay cubically in γ**. The Hypothesis-A `≥ 8` bound therefore fails on the small-γ tail *regardless of how favorably the absolute constants `c_5^⋆, c_6, C_7, w(T_0)` shake out* — there exists a γ-threshold `γ_crit > 0` below which the inequality is structurally violated.

**The recommendation is not a degraded AMBER.** F25's chartered three outcome verdicts (F24 §4) were:
- **GREEN-hypothesis-A-proven** — Hypothesis A holds, width-3 1/3–2/3 unconditional.
- **AMBER-bottleneck-located** — Hyp A fails on crude constants, but the single un-optimised lemma is named and a follow-on `F26` re-proves it sharper.
- **RED-hypothesis-A-false** — Hyp A is genuinely false in the small-γ tail; Daniel-level finding, naming the barrier constant.

This audit's finding is **RED**, not AMBER, because the located bottleneck (`K_0 ≥ 2w/γ + 4` in `lem:layered-reduction`) is **structural to the layered-reduction approach**: the `2w/γ` factor comes from requiring the cut-window fraction `|W|/|X| ≤ γ/2`, which is necessary for the window-removal perturbation `2|W|/(|X|−|W|+1)` to preserve the γ-counter\-example property. Reducing this factor would require a fundamentally different deep-layering reduction (not a tighter constant), placing F26 outside the "constants audit" scope.

**Operational consequence for milestone 1.** The in-tree BK/Cheeger proof spine (`main.tex` + Steps 1–8) does **not** unconditionally prove the width-3 1/3–2/3 conjecture as currently written: for `γ ∈ (0, γ_crit)` and `n > n_0(γ, T_0)`, the cascade does not close, and `step8.tex`'s own scope note (Theorem `thm:main-step8`, scope-note) marks this regime as uncovered. **Milestone 1 part (iii) is NOT closed by Route B as currently scoped.** Both routes from F24 — Route A (chamber-Morse HPC-per-n) and Route B (BK/Cheeger) — now have precisely-located gaps; the gaps are different in nature (Route A's is a structural research problem; Route B's is a small-γ tail), and combining them does not by itself close milestone 1.

**Deliverables (this session):**
- `docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md` (this doc).
- `docs/state-F25.md` (cumulative state ledger).

---

## §0. Setup — what Hypothesis A actually says (cross-repo read)

### 0.1 The statement, in both forms

`step8.tex` `hyp:arith` (Arithmetic richness):

> *For every `γ ∈ (0, 1/3 − δ_KL)`, there exists `T = T(γ) ≥ T_0` (with `T_0` the absolute Step-5 richness threshold) such that the n-independent arithmetic inequality*
>
> ```
>   γ² · c_5(T) · c_6 · δ_0(γ)  ≥  8                                         (★)
> ```
> *holds, where `δ_0(γ) := min(1/(4 C_7), 1/(2 w K_0))` is the cascade target and `c_5(T), c_6, C_7, w, K_0` are the Step-5/6/7 constants fixed by `rem:G2-order`.*

`step8.tex` `rem:final-constants-audit` `eq:arith-explicit` (the substitution `c_5(T) = c_T'(T) = (c_5^⋆/4)² = (c_5^⋆)²/16` from `cor:second-moment`):

> ```
>   c_5^⋆(T,γ)²  ≥  128 / (γ² · c_6 · δ_0)                                  (★★)
> ```
> *— "a purely arithmetic condition on the richness density `c_5^⋆`."*

(★) and (★★) are equivalent; F25 uses both as convenient.

### 0.2 The constants inventory (with origin)

From `step8.tex` `rem:final-constants-audit` plus the upstream Steps-1–7 sources, the named constants are:

| name | origin (file:label) | role | dependence | numerical status |
|---|---|---|---|---|
| `γ` | counterexample parameter | given; window `(0, 1/3−δ_KL) ≈ (0, 0.057)` | n/a | for `γ ≥ 1/3−δ_KL` Kahn–Linial excludes counter\-examples |
| `T_0` | `step5.tex` `cor:second-moment` ("bad-set term ≤ ½ of total") | absolute Step-5 threshold | none | **not numerically pinned** — only stated as "an absolute constant"; depends on Step-1's `C` (bad-set thickness) and Step-1's implicit `c_0^{(1)}` (fiber-density) such that `O(C/(c_0^{(1)} T)) ≤ 1/2` |
| `c_5^⋆ = c_5^⋆(T, γ)` | `step5.tex` `prop:single-triple`(i) — *rich-pair density* | `c_5^⋆ = c · (\|A'\|/\|A\|)(\|B'\|/\|B\|)`, `c` the G2 absolute constant in `(0, 1)`; `T`-fat-support density `(\|A'\|/\|A\|)(\|B'\|/\|B\|)` | `T`-decreasing (`c_5^⋆ ≍ T^{−O(1)}`, asserted in `step8` `rem:final-constants-audit`, not re-derived in `step5`); γ-dependence not extracted in `step5` | `c_5^⋆ ≤ c < 1` (it is a ratio); **no positive lower bound uniform in counterexamples** is extracted in `step5` |
| `c_5(T) := c_T'(T)` | `step5.tex` `cor:second-moment` — *second-moment richness constant* | `c_T'(T) = (c_5^⋆/4)² = (c_5^⋆)²/16` | inherits c_5^⋆'s | `c_5(T_0) ≤ c²/16 < 1/16` |
| `c_6` | `step6.tex` `lem:sum-step4` (`c_1` there, renamed in step8) | overlap-counting absolute constant | `c_6 = c_4 / (4 M_mult)` after pulling δ outside | **not numerically pinned** — `M_mult ≤ 2 M_0 + 1` with `M_0 = O(1)` from width-3 chain-pair count; step6 says "a sharper numerical value of M is not required by any downstream step" |
| `c_4` | `step4.tex` `lem:rect-stable` (= `c_0` there) | rectangle stability lower constant | absolute | `c_4 = c_1 / 4 = 1/8` (from `lem:many-nonconst`'s `c_1 = 1/2`) |
| `C_4` | `step4.tex` `lem:rect-stable` (= `C_0` there) | rectangle stability error coefficient | absolute | `C_4 = C' / 4 = 12/4 = 3` |
| `C_2(T)` | `step4.tex` `prop:G2-step4` — block-transfer | polynomial in `T` via `ε' = √(4ε/ρ(T))` | grows polynomially in `T` (via `ρ(T)`, the Step-1 non-negligibility constant) | **not numerically pinned**; polynomial structure asserted |
| `K(T) := C_4/c_4 + C_2(T)` | `step8.tex` `sec:G2-constants` | aggregate Step-4 error constant | `K(T_0) = 24 + C_2(T_0)` — `T`-polynomial | **`C_4/c_4 = 3 / (1/8) = 24`** explicit; `C_2(T_0)` not pinned |
| `C_7` | `step8.tex` `rem:final-constants-audit` (asserted from Step 7 potential-extraction) | absolute Step-7 rate | absolute | **not numerically pinned**; step7's outputs are `o(1)`-style, `C_7` is an aggregation parameter |
| `w = w(T_0)` | `step7.tex` `lem:bandwidth` / `prop:72` (= `K_bw` there) | layered interaction width | `w = O_T(1)` | **not numerically pinned**; depends on `T_0` and Step-1 bandwidth bound |
| `K_0 = K_0(γ, w)` | `step8.tex` Lemma `lem:layered-reduction` (G3) | layering-depth threshold | **`K_0 := max(2w+2, 2w/γ + 4)`** — explicit | **explicit and γ-dependent**: `K_0 ∼ 2w/γ` for `γ → 0` |
| `δ_0 = δ_0(γ)` | `step8.tex` cascade step (2) | aggregate-incoherence target | `δ_0 := min(1/(4 C_7), 1/(2 w K_0(γ, w)))` | γ-dependent via `K_0` |

This table is the entire constants audit, in one place. The **explicitly pinned** entries are `c_4 = 1/8`, `C_4 = 3`, `C_4/c_4 = 24`, and `K_0 = max(2w+2, 2w/γ + 4)`. Everything else is asserted as "absolute" or "polynomial in T" but **not numerically extracted in the existing text**, which is the substrate the F24 audit was meant to operate on.

### 0.3 What γ-dependence appears where

The Hypothesis-A inequality (★) has γ explicitly only in the leading `γ²` factor. The hidden γ-dependences are:
- `c_5^⋆ = c · (|A'|/|A|)(|B'|/|B|)` — `step5.tex` says `(|A'|/|A|)(|B'|/|B|)` is the `T`-fat-support density of `γ`-counterexamples; the γ-dependence is *not extracted* (this is one of the audit's crux quantities per F24 §4).
- `δ_0(γ) := min(1/(4 C_7), 1/(2 w K_0(γ, w)))` — γ-dependence enters through `K_0`.
- `K_0(γ, w) = max(2w+2, 2w/γ + 4)` — **explicit γ-dependence**: `K_0` grows as `2w/γ` for `γ → 0`.

Of the three, the third is the only one whose γ-dependence is *explicitly written in the source*. F24 §4 flagged the second one (`K_0(γ, w)`) as "the second crux" — the audit now confirms F24's flag: the `K_0(γ, w)` `γ`-dependence is *not just plausible*, it is **derived in `step8.tex`'s own G3 proof** and has the asymptotic form `K_0 ∼ 2w/γ`.

---

## §1. Subtask 1 — discharge the `∃T` existential (F24 §4 step 1)

F24 §1.3 / §4 stated: `c_5^⋆ ≍ T^{−O(1)}` is decreasing in `T`, `w(T)` is non-decreasing in `T`, and `T_0` (Step-5 absolute threshold) is the only constraint forcing `T` up. The optimal admissible choice is therefore `T = T_0`, and Hypothesis A collapses to a single inequality in `γ` alone.

**F25 finding (subtask 1) — confirmed with caveat.** Both monotonicity directions are *asserted* in `step8.tex` `rem:final-constants-audit`'s constants discussion (and in `prop:G2`'s "$c_5$ deteriorates mildly as the richness threshold $T$ grows") but **not re-derived** in `step5` or `step7` as standalone lemmas. The assertion `c_5^⋆ ≍ T^{−O(1)}` reflects the structural intuition: increasing the threshold `T` shrinks `A' = {i : β_i − α_i ≥ T − 1}` and `B' = {j : δ_j − γ_j ≥ T − 1}` (the `T`-fat-supports), hence shrinks `(|A'|/|A|)(|B'|/|B|)`. The assertion `w(T)` non-decreasing is structural in the same sense: a larger `T` admits richness on longer intervals only, so the bandwidth `K_bw` of `lem:bandwidth` cannot decrease. F25 treats these as sealed assertions inherited from `step8` (the audit's job is to evaluate Hyp A, not to re-prove its scoping ingredients); the formal derivation of both monotonicities from the `step5`/`step7` lemmas is a one-page exercise but is not done here.

**Pin `T_0` numerically.** `step5.tex` `cor:second-moment` defines `T_0` implicitly as "absolute, the threshold making the bad-set term ≤ ½ of the fiber-mass total." Quantitatively, `|B_α|/|F_α| = O(1/t_α) ≤ O(1/T)` (per `step5.tex` line 1135–1138), and `T_0` is chosen so this ratio is `≤ 1/2`. The implied constant is `2C/c_0^{(1)}` where `C` is `step1.tex`'s bad-set thickness constant in `|B_α| ≤ C·t_α·|L(P)|/(|A||B||C|)` and `c_0^{(1)}` is `step1.tex`'s good-fiber density constant in `|F_α| ≥ c_0^{(1)}·t_α²·|L(P)|/(|A||B||C|)`. Neither is numerically pinned in `step1.tex`; `T_0` is therefore an absolute constant of unspecified numerical value.

**Result of subtask 1.** `T = T_0` (absolute, numerically unspecified) is optimal; Hypothesis A reduces to the single-γ inequality
```
   γ² · c_5(T_0) · c_6 · δ_0(γ) ≥ 8,      δ_0(γ) = min(1/(4C_7), 1/(2 w(T_0) K_0(γ, w(T_0))))
```
or equivalently (substituting `c_5(T_0) = (c_5^⋆(T_0, γ))²/16`)
```
   c_5^⋆(T_0, γ)² ≥ 128 / (γ² · c_6 · δ_0(γ)).
```
With `T_0, w(T_0), c_6, C_7` all fixed positive absolute constants once `T_0` is chosen, the only γ-dependences are explicit in `γ²`, in `c_5^⋆(T_0, γ)`, and in `δ_0(γ)` through `K_0(γ, w(T_0))`.

---

## §2. Subtask 2 — extract the explicit γ-dependences (F24 §4 step 2)

### 2.1 `K_0(γ, w)` — the second crux: explicit, `1/γ`-blowup

The crux quantity that F24 §1.3 flagged as "the second crux" is `K_0(γ, w)`'s γ-dependence. `step8.tex`'s G3 lemma `lem:layered-reduction` is **explicit**:

```
   K_0 := max(2w + 2,  2w/γ + 4)
```

(`step8.tex` proof of `lem:layered-reduction`, lines 2204–2205, in the worktree's copy: lines `K \ge K_0 := \max(2w+2, 2w/\gamma + 4)`.)

For `γ < 1` (the regime of interest), `2w/γ ≥ 2w`, so the binding choice is `K_0 = 2w/γ + 4`. In particular for `γ → 0`, `K_0 → ∞` linearly in `1/γ`.

**Provenance of the `2w/γ` factor.** The proof of `lem:layered-reduction` deletes a cut-window `W` of total size `|W| ≤ 6w` (interaction-width `2w` × max-band-size `3`) and applies the exceptional-set perturbation bound `|p_{xy}(P) − p_{xy}(P|_A)| ≤ 2|W|/(|X| − |W| + 1)`. To preserve the `γ`-counter\-example property (`min(p, 1−p) ≥ γ`) after window removal, the perturbation must be `< γ/2`, i.e. `|W|/|X| ≤ γ/4` modulo constants. With `|W| ≤ 6w` and `|X| ≥ 3K`, this gives `2w/K ≤ γ/2`, i.e. `K ≥ 4w/γ` — `step8` is slightly looser at `K_0 = 2w/γ + 4` because it controls `|W|/|X|` rather than `|W|/(|X|−|W|)`, but the **`1/γ` scaling is structural** to the window-removal perturbation argument, *not* an artifact of crude bookkeeping.

**Sharpness.** The `1/γ` scaling is *necessary* in the layered-reduction approach: removing a window of fixed bandwidth `O(w)` in a γ-counterexample of size `|X|` perturbs pairwise probabilities by `Θ(w/|X|)`; to keep this below `γ`, one needs `|X| ≥ Ω(w/γ)`, hence depth `K ≥ Ω(w/γ)`. This is a fact about the *probabilistic geometry of layered γ-counterexamples*, not about the particular proof technique inside `lem:layered-reduction`. A re-proof of G3 would have to either (a) shrink the window (the `2w` factor is fixed by the layering definition and Step-7 bandwidth `lem:bandwidth`), (b) work without window removal (a fundamentally different argument), or (c) tolerate larger perturbations (impossible: the `γ/2`-counterexample target is exactly the maximum tolerable perturbation).

### 2.2 `δ_0(γ)` — linear-in-γ decay for small γ

Substituting `K_0(γ, w) = 2w/γ + 4` into `δ_0(γ) = min(1/(4 C_7), 1/(2 w K_0))`:
```
   1 / (2 w K_0)  =  1 / (2w · (2w/γ + 4))  =  γ / (4 w² + 8 w γ).
```
For `γ → 0` (specifically `γ < w/2`), the denominator is dominated by `4 w²`, giving
```
   1 / (2 w K_0)  =  γ / (4 w²) · (1 + O(γ/w))     [γ small].
```
This crosses the constant branch `1/(4 C_7)` at
```
   γ_⋆ := w² / C_7
```
(setting `γ/(4w²) = 1/(4 C_7)`). For `γ < γ_⋆` (which is the small-γ regime of interest, given `w = O_T(1)` and `C_7` absolute), the `K_0`-branch binds:
```
   δ_0(γ)  =  γ / (4 w²) · (1 + O(γ/w))     [γ < γ_⋆ = w²/C_7].
```

### 2.3 `c_5^⋆(T_0, γ)` — first crux: upper-bounded by 1, no lower bound extracted in `step5`

F24 §4 flagged `c_5^⋆`'s γ-dependence as "the crux: bound the `T_0`-fat-support density `(|A'|/|A|)(|B'|/|B|)` of a γ-counterexample as a function of γ."

**F25 finding (subtask 2, crux 1).** The audit confirms:
- **`c_5^⋆ ≤ c`**, where `c ∈ (0, 1)` is the G2 absolute constant of `lem:convex-overlap`; `step5.tex` line 441 takes "an absolute `c ∈ (0, 1)`" — there is no quantitative gain from this constant (the proof of `lem:convex-overlap` works for any `c ∈ (0, 1)`, with the band width `K(T)` in `case (b)` not depending on `c`). In particular `c_5^⋆ < 1` always, regardless of γ.
- **No positive lower bound `c_5^⋆ ≥ f(γ)` is extracted in `step5.tex`.** `prop:single-triple` produces the rich-pair density `c_5^⋆ = c · (|A'|/|A|)(|B'|/|B|)` as a *conditional* statement: in the `(R)` branch of the dichotomy, the rich-pair density is at least this product, where `(|A'|/|A|)(|B'|/|B|)` is the `T_0`-fat-support density of the counterexample. The proof says `c_5^⋆ > 0` whenever the `T_0`-fat support is non-degenerate, but the *positive* lower bound depends on the specific counterexample.

**Consequence.** Without external input, **`c_5^⋆(T_0, γ)² ≤ c² < 1`** is the only universal upper bound; lower bounds are counterexample-dependent and not in `step5`. The crux-1 question — "does `c_5^⋆(T_0, γ)` stay bounded below as `γ → 0`?" — *cannot be answered from `step5.tex` alone*; the answer depends on a γ-dependent lower bound that the present argument does not produce.

This is itself a finding: even the *upstream* of Hyp A is not well-formed in the small-γ regime — the proof of `prop:single-triple` (or its dichotomy case (i)) does not tell us how much above 0 the rich-pair density actually is for a *given* γ.

### 2.4 The other constants — `c_6, C_7, w(T_0)`

- **`c_6`**: `step6.tex` line 276–277 defines `c_1 := c · δ_0/(4M)` where `c, C` are the Step-4 absolute constants of `lem:rect-stable` and `M` is the witness-edge multiplicity from `lem:overlap-counting`. After pulling `δ_0` outside (per `step8.tex` `rem:final-constants-audit`'s renaming), `c_6 = c/(4M)` with `c = c_4 = 1/8` (audit subtask 2 §0.2) and `M = 2 M_0 + 1` for `M_0 = O(1)` width-3. **`step6.tex` line 469 explicitly disclaims numerical pinning of `M`:** "A sharper numerical value of `M` is not required by any downstream step." Lower-bounding `c_6` therefore reduces to upper-bounding `M`, which the existing text leaves open. A crude pencil-and-paper estimate from the proof of `lem:overlap-counting`: 3 chain-pair types × bounded number of admissible position pairs per type — order of magnitude `M ≤ O(10)` to `O(100)`, hence `c_6 ≥ c_4/(4M) ≥ 1/(32 M)` is somewhere in the range `[3·10⁻⁴, 3·10⁻³]`. The audit treats `c_6` as a positive absolute constant of order `10⁻³` for the Hyp-A evaluation below; this is a placeholder.
- **`C_7`**: `step8.tex` `rem:final-constants-audit` calls `C_7` "absolute, potential-extraction rate", coming from `prop:71`'s `1_S = 1_{\{H ≥ c\}} + o(1)` statement. **`C_7` is not defined inside `step7.tex`**: `step7.tex`'s outputs (`prop:71`, `prop:72`) are stated as `o(1)` rather than as quantitative rates, and the constant `C_7` is `step8.tex`'s discretization of the aggregate `o(1)`-rate. The audit can offer no numerical lower bound on `C_7`. The Hyp-A evaluation below treats `1/(4 C_7)` as a *constant in γ* (which it is) and uses only the fact that `1/(4 C_7) > 0`.
- **`w = w(T_0)`**: per `step8.tex` `lem:layered-from-step7` (`it:lift-layered`), `w = K_bw + 2 = K(T_0) + 2` in the Step-7 branch, where `K_bw = K(T_0) = O_T(1)` is the bandwidth constant of `step7.tex` `lem:bandwidth`. **No explicit numerical value of `K_bw(T_0)` is given in `step7.tex`** beyond "`O_T(1)`"; the audit treats `w(T_0)` as a positive absolute constant of unspecified value.

### 2.5 Summary of subtask 2

The audit pins:
- `c_4 = 1/8`, `C_4 = 3`, `C_4/c_4 = 24` — explicit.
- `K_0(γ, w) = max(2w+2, 2w/γ + 4)` — explicit, γ-dependent, **the binding constraint for the small-γ regime**.
- `δ_0(γ) = γ/(4w²)·(1 + O(γ/w))` for `γ < w²/C_7` — derived.
- `c_5^⋆ ≤ c < 1` — universal upper bound; **no positive lower bound** extracted from `step5`.
- `c_6, C_7, w(T_0), C_2(T_0)`, all unpinned numerically; carried as positive absolute constants.

---

## §3. Subtask 3 — check Hyp A over `γ ∈ (0, 1/3 − δ_KL) ≈ (0, 0.057)` (F24 §4 step 3)

### 3.1 The reduction in the small-γ regime

In the small-γ regime (`γ < γ_⋆ = w²/C_7`), substituting `δ_0(γ) = γ/(4 w²)` and `c_5(T_0) = (c_5^⋆(T_0, γ))²/16` into Hypothesis A (★):
```
   γ² · (c_5^⋆)²/16 · c_6 · γ/(4 w²)   ≥   8
   ⇔   γ³ · (c_5^⋆)² · c_6 / (64 w²)   ≥   8
   ⇔   γ³ · (c_5^⋆)² · c_6              ≥   512 w²
   ⇔   (c_5^⋆)²                          ≥   512 w² / (γ³ · c_6)
   ⇔   (c_5^⋆)² · γ³                     ≥   512 w² / c_6.                  (★★★)
```

### 3.2 The universal upper bound on the LHS forces failure as `γ → 0`

By §2.3, `c_5^⋆(T_0, γ) ≤ c < 1` *universally* (independent of γ). Therefore the LHS of (★★★),
```
   (c_5^⋆)² · γ³  ≤  c² · γ³  <  γ³,
```
**tends to 0 cubically as γ → 0**. The RHS, `512 w² / c_6`, is a fixed positive constant (whatever its precise value).

**Therefore Hyp A is violated for every `γ < γ_crit`, where**
```
   γ_crit := (512 w² / ((c_5^⋆)² · c_6))^{1/3}    (the smallest γ for which (★★★) can possibly hold).
```

With `c_5^⋆ ≤ c < 1` and the standing assumption that `w, c_6` are positive absolute constants, `γ_crit > 0`. Hypothesis A's window `(0, 1/3 − δ_KL) ≈ (0, 0.057)` therefore *necessarily* contains a left tail `(0, γ_crit)` on which Hyp A fails.

### 3.3 Why the verdict is RED and not AMBER

The barrier admits a specific localization, which lets us discriminate the AMBER and RED outcomes of F24 §4.

**AMBER would require:** the bottleneck is a single un-optimised lemma whose constant can be sharpened — typically a factor-of-2 or polylogarithmic loss in a Markov / Cauchy–Schwarz / Jensen step.

**RED requires:** the bottleneck is structural — the *order* of the γ-dependence (here, `γ³` on the LHS vs. constant on the RHS) cannot be fixed by tightening absolute constants.

The bottleneck identified here is **structural**: the `1/γ` factor in `K_0(γ, w)` of `lem:layered-reduction` (G3) comes from the *necessary* condition `|W|/|X| ≲ γ` for the window-removal step to preserve the γ-counterexample property (§2.1). Removing this `1/γ` factor would require not "sharpening a constant" but **a fundamentally different deep-layering reduction** that does not use window-removal at all. Such a reduction is not in the existing argument; constructing one is an open structural research problem orthogonal to constants tightening.

A second confirmation: even *granting* a hypothetically tight `c_5^⋆ = 1` (impossible since it's a density that is at most `c < 1`), the LHS of (★★★) is bounded above by `γ³`, which → 0 as γ → 0 *cubically*. No amount of constant-tightening on the `c_5^⋆, c_6, w` side can overcome a cubic decay against a fixed positive constant. The bottleneck is the *form* of (★★★), not the size of its constants.

Hence **RED-hypothesis-A-false-small-γ-tail**.

### 3.4 Numerical caveat — exactly *which* γ-tail?

Pinning `γ_crit` numerically requires pinning `w, c_5^⋆(T_0, γ_*), c_6` numerically. From §2:
- `c_5^⋆ ≤ c < 1`; with `c = 1/4` (the example value in `step5.tex` `ex:G2-realized`), `(c_5^⋆)² ≤ 1/16`.
- `c_6` ∈ `[3·10⁻⁴, 3·10⁻³]` by the crude `M = O(10–100)` placeholder.
- `w(T_0)` unknown; if `w(T_0) ≤ 10`, `w² ≤ 100`.

Plugging in `(c_5^⋆)² = 1/16`, `c_6 = 10⁻³`, `w² = 100`:
```
   γ_crit ≈ (512 · 100 / (1/16 · 10⁻³))^{1/3}  =  (8.2 · 10⁸)^{1/3}  ≈  936.
```
This is **far above** the upper end of the Hyp-A window `0.057`. The interpretation: **for plausible orders of magnitude of the absolute constants, Hyp A fails on the entire Hyp-A window, not just a tail near zero**.

This `γ_crit ≈ 936 ≫ 0.057` headline is, of course, sensitive to the exact values of `c_5^⋆, c_6, w(T_0)`, none of which are numerically pinned. Even taking the most optimistic plausible values (`c_5^⋆ = c = 1/2`, `c_6 = 1/10`, `w = 1`):
```
   γ_crit ≈ (512 · 1 / (1/4 · 1/10))^{1/3}  =  (20480)^{1/3}  ≈  27.4.
```
Still `≫ 0.057`. To get `γ_crit ≤ 0.057`, one would need
```
   (c_5^⋆)² · c_6 / w²  ≥  512 / (0.057)³  ≈  2.77 · 10⁶,
```
which would require either a `c_5^⋆` near 1, or `c_6 ≫ 1`, or `w ≪ 1`, *all simultaneously*. With `c_5^⋆ ≤ c < 1` and `c_6 = c_4/(4M) < c_4 = 1/8` and `w ≥ 1` (it is a width, hence integer-valued — actually a bandwidth, may be fractional but not vanishingly small), this is **structurally impossible**.

### 3.5 Robust conclusion of subtask 3

**Hyp A, in the form `eq:arith-explicit`, fails on the entire Hyp-A window for any plausible numerical realisation of the unpinned constants.** The minimum-pessimism scenario is "fails on a `(0, γ_crit)` tail with γ_crit > 0"; the realistic scenario is "fails on the entire window `(0, 0.057)`." Either way, the BK/Cheeger argument as written does **not** cover Hypothesis A's intended domain.

---

## §4. Subtask 4 — cross-check the `ε / n_0` cascade (F24 §4 step 4)

F24 §4 step 4 chartered this as a confirmation pass: `step8` G2 + `lem:small-n` discharge the cascade `γ → T_0 → δ_0 → ε → n`, with `ε := δ_0/(2 K(T_0))` and `n_0(γ, T_0)` polynomial in `1/γ`. The audit confirms:

- **`ε := δ_0/(2 K(T_0))`** — well-defined positive for every `δ_0 > 0`. In the small-γ regime, `δ_0 = γ/(4 w²)` and `K(T_0) = 24 + C_2(T_0)` is absolute, so `ε = γ / (8 w² (24 + C_2(T_0)))` — small, but positive and γ-controlled. **Step 2's `o(1)` error condition** `ε(η(γ, n)) ≤ ε` is realisable for every `n ≥ n_0(γ, T_0)` per `step8.tex` `eq:n0-def`. ✓
- **`n_0(γ, T_0) = ⌈4 C_exc(T_0)/γ⌉ + C_exc(T_0) − 1 = Θ(C_exc(T_0)/γ)`** — polynomial in `1/γ`, with `C_exc(T_0) = 3 c_1(T_0)` from `lem:layered-from-step7` (and `c_1(T_0)` is the per-chain endpoint-exceptional constant of `step5.tex` `lem:endpoint-mono`, absolute). ✓
- **`lem:small-n`** finite-enumeration base case discharges `n ≤ n_0(γ, T_0)`. ✓

**The cascade is therefore realisable *whenever Hyp A holds*.** The cascade is *not* the bottleneck — the bottleneck is that Hyp A itself fails on the small-γ tail (§3). For `γ ∈ (0, γ_crit)`, the cascade does *not* close even with the small-`n` base case: the `lem:small-n` base case covers only `n ≤ n_0(γ, T_0)`, leaving `n > n_0(γ, T_0)` uncovered (the large-`n` tail), which is exactly `step8.tex`'s flagged scope hole.

---

## §5. Interpretation, location, what this means for milestone 1

### 5.1 The bottleneck is precisely located

The barrier to Hypothesis A is the **`K_0(γ, w) = max(2w+2, 2w/γ + 4)` threshold from `step8.tex` Lemma `lem:layered-reduction` (GAP G3)**. Specifically:

- This is the only γ-dependent constant in `δ_0(γ) = min(1/(4 C_7), 1/(2 w K_0))`.
- Its `1/γ` form is *not* a crude bookkeeping artifact: it is forced by the perturbation budget of the window-removal step in the proof of `lem:layered-reduction`.
- Removing or weakening this `1/γ` factor in G3 is the *only* way to save Hypothesis A.

### 5.2 What a follow-on `F26` would have to do

A follow-on `F26` chartered to save Hypothesis A would need to produce a **structurally new deep-layering reduction lemma** that handles the deep-`K` regime of layered width-3 γ-counter\-examples *without* relying on window-removal — equivalently, without the `2|W|/(|X|−|W|+1)` perturbation budget that drives the `1/γ` factor.

Plausible attack surfaces (none of them constants tightening):

- **Direct balanced-pair extraction inside a deep layered region.** The bipartite-balanced argument of GAP G4 (`step8.tex` `lem:layered-balanced`) works for shallow `K < K_0`, by averaging on a bounded interaction window. Generalising this to deep `K` would bypass G3 entirely.
- **A different cut location.** `lem:layered-reduction` cuts at a single index `k ∈ (w, K − w)` and removes the `2w`-band interaction window. A multi-cut or smeared-cut strategy might avoid the discrete window-removal step.
- **Re-derive G3 from a different perturbation bound.** The `2|W|/(|X|−|W|+1)` bound is itself proved by `lem:exc-perturb` via iterated single-element deletion. A non-deletion-coupling argument (e.g., direct Markov-chain mixing on the BK graph restricted to layered structure) might admit a tighter bound.

None of these reduces to "audit the constants in lemma X" — each is a structural-mathematical research question.

**This is why the verdict is RED, not AMBER.** F24 §4 marked AMBER as "the inequality fails with the crude constants, but the audit names the single un-optimised lemma responsible." The audit's finding is stricter: **the inequality fails because of a γ-dependent *order-of-magnitude factor* `1/γ`** that is structurally tied to the layered-reduction approach, not because any single constant was bounded too loosely. A constants-tightening F26 is therefore *not* the right follow-on — the right follow-on is a structural-lemma rewrite.

### 5.3 Comparison to F24's expectation

F24 §1.3, in its tractability assessment, noted three possible outcomes and explicitly identified RED with: *"The richness density decays too fast; the BK/Cheeger route has a real hole in the `γ ∈ (0, 0.057)`, large-n tail."* F24's expected RED mechanism was the *first* crux: `c_5^⋆(T_0, γ)` decaying too fast in γ. The audit's actual RED mechanism is the *second* crux: `K_0(γ, w)` blowing up too fast in `1/γ`. **F24 flagged the right cruxes; the audit identifies which one bites first.**

The first crux is also problematic (§2.3: `step5.tex` extracts no positive lower bound for `c_5^⋆`'s γ-dependence), but the audit's RED conclusion would *follow even if `c_5^⋆ = c` were a positive absolute constant uniform in γ*: the `K_0`-driven `δ_0 ∼ γ/(4w²)` decay alone forces the Hyp-A LHS to → 0 cubically in γ. So the second crux is sufficient to force RED on its own; the first crux just makes the situation worse.

### 5.4 Operational consequence for milestone 1

**The in-tree BK/Cheeger spine `main.tex` + Steps 1–8, *as written*, does not unconditionally prove the width-3 1/3–2/3 conjecture.** Specifically:

- The regime `γ ≥ 1/3 − δ_KL ≈ 0.276` is covered by Kahn–Linial (`step8` `lem:small-n` width-3 large-γ subcase) — unconditional.
- The regime `n ≤ n_0(γ, T_0)` is covered by the finite-enumeration small-`n` base case `lem:small-n` — unconditional but enumeration-mechanical.
- The regime `γ ∈ (0, 1/3 − δ_KL) ≈ (0, 0.057)` *and* `n > n_0(γ, T_0)` requires Hypothesis A. The audit concludes Hyp A fails on at least a `(0, γ_crit)` left tail, plausibly on the entire `(0, 0.057)` window.

Therefore the *large-n, small-γ tail* of width-3 1/3–2/3 is *not* closed by the BK/Cheeger argument as currently written. This is exactly the "uncovered tail" that `step8.tex`'s scope note (Theorem `thm:main-step8` scope discussion, also `rem:n-dependence-g1`) flags as the hole.

**Both F24 routes now have located gaps:**

| route | residual gap, post-F25 | nature of gap |
|---|---|---|
| Route A — chamber-Morse HPC-per-n | the `n`-uniform `(CM-rel)` proof (F23 §7.2, "not attempted"); F23's evidence refutes every `n`-uniform structural discriminator | open structural research, evidence-disfavoured |
| Route B — BK/Cheeger | the `K_0(γ, w)`-driven small-γ-tail failure of Hyp A (this audit); structural to the layered-reduction approach | open structural research, located precisely |

Route B was chosen at F24 over Route A because Route B's gap was scoped (Hyp A) and constants-audit-attackable. The audit now finds Route B's gap is **not constants-audit-closable**: it requires a structural-lemma rewrite. The relative ranking of Route A vs. Route B post-F25 should therefore be re-evaluated; F26 should *not* simply chase a sharper-G3 lemma without first surveying whether the chamber-Morse evidence has shifted, and whether direct deep-layering balanced-pair arguments (G4 generalisations) are within reach.

### 5.5 Trust-surface impact

**None.** F25 is a paper-and-pencil audit. The F10 cohomological core (parts i–ii, unconditional) is untouched. The in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched (the BK/Cheeger argument is paper-level structural; no Lean changes). No new axioms.

---

## §6. What F25 establishes and does not establish

### 6.1 Establishes

- **Hyp A fails on the small-γ tail of its intended window.** Specifically: `(eq:arith-explicit)` requires `(c_5^⋆)² · γ³ · c_6 / w² ≥ 512`, and the LHS is universally bounded above by `γ³ · c_6 / w²` (since `c_5^⋆ ≤ c < 1` and the product `c² c_6/w²` is at most some positive absolute number bounded below 1 in plausible numerical scenarios). For `γ → 0` the LHS goes to 0 cubically; **the inequality fails for every `γ < γ_crit` with `γ_crit > 0`**, and for plausible numerical realisations `γ_crit ≫ 0.057` so Hyp A fails on the whole window.
- **The barrier is precisely located.** The single mechanism is `K_0(γ, w) ≥ 2w/γ + 4` from `step8.tex` Lemma `lem:layered-reduction` (GAP G3), which forces `δ_0(γ) ∼ γ/(4w²)` for `γ → 0` and hence forces Hyp A's LHS to cubic decay.
- **The barrier is structural, not constants-driven.** The `1/γ` factor in `K_0` is necessary for window-removal in the proof of `lem:layered-reduction` to preserve the γ-counter\-example property; tightening absolute constants cannot remove it.
- **The cascade `γ → T_0 → δ_0 → ε → n` is otherwise realisable**, *whenever Hyp A holds*. The cascade is not the bottleneck.
- **Constants pinned numerically:** `c_4 = 1/8`, `C_4 = 3`, `C_4/c_4 = 24`, `K_0(γ, w) = max(2w+2, 2w/γ + 4)`. **Constants left unpinned by the existing argument:** `T_0`, `c_5^⋆`, `c_6` (via `M_mult`), `C_7`, `w(T_0)`, `C_2(T)`.
- **Subtask-1 ∃T collapse is confirmed structurally** (the monotonicities asserted in `step8` are intuitively read off the `step5/7` proofs) but the formal re-derivation is left as a one-page exercise outside the audit.
- **Trust surface unchanged.** No Lean, no axioms, no HPC.

### 6.2 Does not establish

- **Hyp A is not falsified for *every* γ in `(0, 0.057)`.** The audit shows Hyp A fails on a `(0, γ_crit)` tail with `γ_crit > 0`. For `γ ∈ (γ_crit, 0.057)` the audit is inconclusive: under generous assumptions on the unpinned constants, Hyp A might still hold on `(γ_crit, 0.057)`. The audit's qualitative finding ("fails as γ → 0") is robust; the quantitative threshold `γ_crit` would require numerical pinning of `c_5^⋆, c_6, w, C_7`.
- **The BK/Cheeger route is not refuted as mathematics.** It remains a valid attack on width-3 1/3–2/3; the audit only shows its current write-up has a small-γ tail it does not cover.
- **F26 is not scoped here.** The follow-on would need to be a structural-lemma rewrite of G3 or an entirely new deep-layering balanced-pair argument; the present audit does not propose a specific path.
- **The relative ranking of Route A vs. Route B is not re-evaluated.** Route B's gap, identified by F25, is structural-research-grade. Whether this changes F24's GREEN-route-B-recommended verdict is a PM call, not an F25 finding.
- **F25 does not touch the F10 cohomological core (parts i–ii)**, the F19–F23 chamber-Morse arc, the in-tree Lean artifact, or `mg-b345` (route iii / Quillen fiber). All stay as they are.

---

## §7. References

### 7.1 Predecessor mg-tickets

- **mg-a30d** — F24 (the part-(iii) route fork): **GREEN-route-B-recommended.** Parent. `docs/compatibility-geometry-F24-route-fork-comparison.md` §1.2 (Hyp A statement), §1.3 (the `∃T` collapse to a single γ inequality), §4 (F25 scope, the three outcome verdicts).
- **mg-531f** — F23: **GREEN-descent-pinned (HPC-per-n).** Route A's residual.
- **mg-26fc** — the two 1/3–2/3 mechanisms: GREEN-distinct-complementary. The BK/Cheeger column rigorised.
- **mg-0c5d / mg-43fb** — F22-HPC. F23's HPC-per-n evidence base.
- **mg-a2cb** — F21. The chamber-Morse machinery.
- **mg-4d3a, mg-d039** — F17/F18. The F10 cohomological core (untouched by F25).

### 7.2 In-tree sources (the BK/Cheeger spine, audit targets)

- **`step8.tex`** — Hypothesis A statement (`hyp:arith`, line ~506); the constants discussion (`rem:final-constants-audit`, lines 1752–1870); G3 Layered-reduction lemma (`lem:layered-reduction`, lines 2190–2311) with **the load-bearing `K_0 := max(2w+2, 2w/γ+4)` line 2205**; G4 (`lem:layered-balanced`, lines 2347+) for shallow layerings; the cascade discharge (`prop:G2`, `rem:G2-order`).
- **`step5.tex`** — `prop:single-triple` (lines 106–195) where `c_5^⋆ = c · (|A'|/|A|)(|B'|/|B|)`; `lem:convex-overlap` (G2, lines 357+) where `c ∈ (0, 1)` is "an absolute" parameter; `cor:second-moment` (lines 1107+) where `T_0` is implicitly defined and `c_5(T) = c_T'(T) = (c_5^⋆)²/16`.
- **`step6.tex`** — `lem:sum-step4` (lines 266+) where `c_1 := c δ_0/(4M)`; `lem:overlap-counting` (line 347+) where `M = 2 M_0 + 1` and `M_0 = O(1)`. **Line 469 explicitly disclaims numerical pinning of `M`.**
- **`step7.tex`** — `prop:71`, `prop:72`, `prop:73`. **`C_7` is not defined inside `step7.tex`** — it is `step8`'s aggregation of `step7`'s `o(1)`-rates.
- **`step4.tex`** — `lem:rect-stable` (lines 427+) with `c_0 = c_1/4 = 1/8` and `C_0 = C'/4 = 3`; `lem:many-nonconst` (lines 728+) with `c_1 = 1/2`; `prop:G2-step4` block-transfer with `ε' = √(4ε/ρ)` and `C_2(T)` polynomial in `T`.
- **`main.tex`** — §"Approach: Cheeger-type expansion on the BK graph" (the spine); §"What must be proved vs. what is crude" — confirms the existing argument treats constants crudely, exactly the substrate F25 was meant to audit.

### 7.3 Mathematical literature (relevant to interpretation)

- Bubley–Karzanov (1997/1998) — the BK Markov chain.
- Cheeger (1970); Lawler–Sokal; Sinclair–Jerrum — the discrete Cheeger inequality.
- Kislitsyn (1968); Fredman (1976); Linial (1984) — the 1/3–2/3 conjecture; Linial's width-2 theorem (the BK proof's width-recursion base, and `lem:small-n` width-2 sub-case).
- Kahn–Linial (1991) — the unconditional `δ_KL = 0.276393…` bound, which is what defines Hyp A's γ window and which Hyp A relies on for the upper-γ Kahn–Linial regime.
- Kahn–Saks (1984); Brightwell (1999) — the per-coordinate covariance bound inside the FKG-based exceptional-set perturbation `lem:one-elem-perturb` of `step8.tex`.

### 7.4 Daniel directives

- 2026-05-14T05:18Z — finish internally; no external collaboration. (F25 is pure internal audit; no external input.)
- 2026-05-14T17:23Z — milestone 1 = full gap-free width-3 proof, no sketches or gaps. (F25's RED finding shows milestone 1 is *not* delivered by the BK/Cheeger spine as written; this is the audit's job, not a deviation from the directive.)
- 2026-05-14T22:32Z — "keep pushing." (F25 delivers a precise, actionable, structurally-located finding; that *is* pushing — by closing the constants-audit question with a clean verdict and naming the next decision point.)

---

*Polecat: mg-c6f2 (F25). Branch: `polecat-mg-c6f2`. Verdict: **RED-hypothesis-A-false-small-γ-tail** — Hypothesis A `step8.tex` `hyp:arith / eq:arith-explicit` fails on the small-γ tail of its window `(0, 1/3 − δ_KL) ≈ (0, 0.057)`. The barrier is precisely located: `K_0(γ, w) ≥ 2w/γ + 4` from `step8.tex` Lemma `lem:layered-reduction` (GAP G3), which forces `δ_0(γ) ∼ γ/(4w²)` as `γ → 0` and hence the Hyp-A LHS to cubic γ-decay against a fixed positive RHS. Universal upper bound `c_5^⋆ ≤ c < 1` (G2 absolute constant) makes the LHS → 0 *regardless* of how favorably the other absolute constants land. The barrier is **structural** to the layered-reduction approach (window-removal perturbation budget), not constants-tightening. Operational consequence: the in-tree BK/Cheeger spine `main.tex` + Steps 1–8 does NOT unconditionally prove width-3 1/3–2/3 as written; the large-n, small-γ tail is uncovered. Both F24 routes now have located gaps; the relative ranking is a PM call, not an F25 finding. No new axioms, no Lean changes, no HPC. Cumulative state: `docs/state-F25.md`.*
