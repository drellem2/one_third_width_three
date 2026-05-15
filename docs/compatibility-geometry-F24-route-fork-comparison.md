# Compat-Geom — F24: the part-(iii) route fork — scope-and-compare HPC-per-n chamber-Morse vs. the BK/Cheeger pivot, recommend, scope F25 (mg-a30d)

**Branch:** `polecat-cat-mg-a30d` (mg-a30d).
**Parent:** mg-531f (F23, **GREEN-descent-pinned HPC-per-n**) §8 — F23 surfaced this fork as a PM/Daniel decision; F24 resolves it with a head-to-head comparison.
**Chain:** F10 → F17 (mg-4d3a) → F18 (mg-d039) → F19 → F20 → F21 (mg-a2cb) → F22-HPC (mg-43fb / mg-0c5d) → F23 (mg-531f) → **F24 (mg-a30d)**.
**Type:** Structural scoping + head-to-head comparison. **Paper-and-pencil; no new axioms; no Lean; no computation; no HPC.** Multi-session-able; cumulative `docs/state-F24.md`. LaTeX-style Markdown, F-series house style.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T17:23Z (milestone 1 — full gap-free width-3 proof, no sketches or gaps); 2026-05-14T22:32Z ("keep pushing").

---

## Verdict: **GREEN-route-B-recommended.**

**Route B — pivot F10 part (iii) to the BK/Cheeger-expansion mechanism — is the decisively more tractable path to milestone 1.** The recommendation is not close; it is forced by three findings, each established below.

1. **Route B has a single, precisely-stated, finite residual gap.** The in-tree width-3 paper (`main.tex` + Steps 1–8) is gap-free *except* for **Hypothesis A** (`step8.tex` `hyp:arith`). Steps 1–7 are unconditional; the Step-8 items G1–G5 are all discharged inside `step8.tex`. Hypothesis A is **one `n`-independent arithmetic inequality** in named constants — `step8.tex` itself calls it "a purely arithmetic condition on the richness density" and "the sole external numerical input the present argument requires." It is **not** a deep new conjecture; it is a **constants audit** of an already-written proof (§1).

2. **Route A has no comparable single gap — it is Tier-3 HPC *plus* an endgame F23 has already shown is evidence-disfavored.** Route A materialises `M^chamber_n` at `n = 5,6,7` (each Tier-3 HPC — `Δ_5` already `> 2·10⁷` cells) to pin `c*_6, c*_7`, *then* must prove an `n`-uniform `(CM-rel)` seeded by the 5-datapoint record. But **F23 already ran the `n`-uniform-pattern probe on the 3-datapoint record `c*_3, c*_4, c*_5` and refuted *every* structural discriminator as `n`-uniform** (F23 §4–§5). The "datapoints seed an `n`-uniform proof" bet has already partially failed; two more HPC datapoints do not change the structural verdict. Route A is **HPC + an unscoped, evidence-disfavored research problem with no identified attack** (§2).

3. **Route B's gap is paper-and-pencil polecat-attackable; Route A's is not.** Resolving Hypothesis A is a bounded, well-defined audit of the sealed Steps-1–7 constants — no HPC, no Lean, no new axioms. Even its *worst case* (the inequality turns out false or hard) is a **better-delineated, more informative** outcome than Route A's treadmill: it names the exact bottleneck lemma. Route A's worst case is "another Tier-3 datapoint, still no pattern" (§3).

**PM lean — CONFIRMED, and strengthened.** pm-onethird leaned Route B; F24 confirms it on evidence and sharpens the reason. The lean was "Route A risks a treadmill; Route B is a genuinely different attack." F24's sharper reason: **Route B's gap is the *actual in-tree width-3 paper's sole remaining hypothesis*, and resolving it *is* milestone 1 part (iii) — directly, with no further machinery.** Route A, even fully executed (`c*_6, c*_7` pinned), is *not* milestone 1: it still owes the `n`-uniform `(CM-rel)` proof, which F23's evidence says is not there to be found.

This is **not** AMBER-route-B-blocked: Hypothesis A is not "a hard open problem with no clean attack" — the attack (the constants audit) is clear, bounded, and scoped here as F25 (§4). The uncertainty is about the audit's *outcome*, not the *tractability of the investigation*.

**Deliverables (this session):**
- `docs/compatibility-geometry-F24-route-fork-comparison.md` (this doc).
- `docs/state-F24.md` (cumulative state ledger).

---

## §0. The fork, precisely

### 0.1 Where milestone 1 stands after F23

Milestone 1 (Daniel 2026-05-14T17:23Z) is **the full gap-free width-3 1/3–2/3 proof — no sketches, no gaps**. The status of its three components:

- **F10 parts (i)–(ii) — the cohomological core — UNCONDITIONAL.** `Hyp(n)` for all `n`, `(H-Cox)+(sgn)`, the existence/uniqueness/non-vanishing pairing of `ω_bal^{(n)}`. F17 proved `(UCC.1)`, F18 proved `(UCC.2)`; `(UCC)` is complete (roadmap headline). Not at issue here.
- **F10 part (iii) — the numerical width-3 conclusion — the open piece.** "Every width-3 partial order `P` admits incomparable `x,y` with `Pr_P[x<y] ∈ [1/3,2/3]`" (F10 §6.7(iii); the actual 1/3–2/3 statement). This is what F19→F23 pursued through "the canonical chamber-Morse critical cell `c*_n`" and the inductive rule generating the `c*_n` tower.
- **The Lean `width3_one_third_two_thirds` artifact** — separate 4-axiom trust surface, the *finite/structural* width-3 result; untouched by the F-series, not at issue here.

So milestone 1 reduces to **closing F10 part (iii) gap-free at general `n`**.

### 0.2 What F23 established — the chamber-Morse route is HPC-per-n

F23's verdict, **GREEN-descent-pinned (HPC-per-n)**:

- The canonical `S_{n+1}`-equivariant rule selecting `c*_{n+1}` **exists** — Rule B = "descent-reachable AND chamber-Morse critical" + `min-|L|-profile` tie-break. `c*_n` **is** a well-defined canonical object; the meta-question resolved positively, no re-founding needed.
- **BUT the rule is HPC-per-n, not closed-form / `n`-uniform.** Applying Rule B at level `n+1` needs the level-`(n+1)` chamber-Morse matching `M^chamber_{n+1}` — Tier-3 HPC from `n = 5`. The cofiber-Morse induction (Prop F21.1) is correct but **does not self-close into a closed-form recursion.**
- **No closed-form structural rule survives.** F23 §4–§5: *every* structural (non-criticality) discriminator of the 4 candidate orbits — top-poset OSA signature, new-element locus, size-2-block position — is **refuted as an `n`-uniform rule** by the recorded `c*_3, c*_5`. The only `n`-uniform selector is chamber-Morse criticality itself, which is the *definition* of `c*_n` and is HPC-per-n.

F23 §8 surfaced two documented continuations as a PM/Daniel decision. F24 is the evidence that resolves the fork.

### 0.3 The two routes

> **Route A — HPC-per-n chamber-Morse grind.** Materialise `M^chamber_n` at `n = 5,6,7` as Tier-3 HPC, apply Rule B to pin the genuine `c*_6, c*_7`, then pursue the `n`-uniform proof of `(CM-rel)` seeded by the 5-datapoint record `c*_3..c*_7`. (Route 2 of `state-F22-HPC` §5.)

> **Route B — pivot part (iii) to the BK/Cheeger-expansion mechanism.** Obtain the numerical width-3 conclusion via the in-tree paper's Bubley–Karzanov-graph / Cheeger-expansion proof spine (`main.tex` + Steps 1–8), which does **not** use the canonical chamber-Morse critical cell at all — it sidesteps the entire F19–F23 wall. Its open gap is Hypothesis A. (mg-26fc mechanism (a).)

The fork is **not** "which mechanism is correct" — mg-26fc already established (GREEN-distinct-complementary) that the two are distinct-but-resonant mechanisms, *both* valid attacks on width-3 1/3–2/3. The fork is **which residual gap do you attack to reach milestone 1**: the HPC-per-n chamber-Morse machinery (Route A), or Hypothesis A (Route B).

---

## §1. Route B scoped — the BK/Cheeger-expansion mechanism

### 1.1 The dictionary: F10 part (iii) ⟷ what the BK/Cheeger route proves, conditional on what

**What the BK/Cheeger route proves.** `step8.tex` Theorem `thm:main-step8` (= `main.tex` Theorem `thm:conclusion-main`):

> *Assume Hypothesis A. Then every finite width-3 poset that is not a total order has a balanced pair: incomparable `x,y` with `1/3 ≤ Pr[x<y] ≤ 2/3`.*

This is **exactly the 1/3–2/3 conjecture for width 3** — i.e. exactly F10 part (iii)'s conclusion.

| | F10 part (iii) (the ICOP / chamber-Morse route) | The BK/Cheeger route (`main.tex` + Steps 1–8) |
|---|---|---|
| **Conclusion** | width-3 `P` ⟹ ∃ incomparable `x,y` with `Pr_P[x<y] ∈ [3/11,8/11]` | width-3 `P` non-chain ⟹ ∃ incomparable `x,y` with `Pr_P[x<y] ∈ [1/3,2/3]` |
| **Strength** | sharper — the BFT interval `[3/11,8/11] ⊂ [1/3,2/3]` | exactly the 1/3–2/3 statement `[1/3,2/3]` |
| **Mechanism** | non-vanishing sign-isotypic cohomological pairing `⟨ω_bal^{(n)}, c*_n⟩ ≠ 0` along the canonical critical chain; ICOP | Cheeger-type expansion dichotomy on the Bubley–Karzanov graph `G_BK(P)`; a counterexample forces a structurally-impossible low-conductance cut |
| **Residual gap (post-F23)** | the HPC-per-n chamber-Morse machinery generating the `c*_n` tower (= Route A) — *plus* `(ICOP-step)` and the width-3 bridge | **Hypothesis A** (`hyp:arith`) — and nothing else |
| **`n`-induction?** | yes — cofiber LES `Δ_n ↪ Δ_{n+1}`; this is the spine the F19–F23 wall sits on | **no** — Theorem E holds uniformly for all `n`; the only recursion is on *width*, capped by Linial's width-2 theorem (mg-26fc §3.4) |

**The load-bearing dictionary fact.** For milestone 1, the target is the **`[1/3,2/3]`** statement — that *is* the 1/3–2/3 conjecture. The `[3/11,8/11]` sharpening that F10 part (iii) carries is a *bonus* of the ICOP machinery, not a milestone-1 requirement. **The BK/Cheeger route delivers exactly the milestone-1 target, conditional on Hypothesis A alone.** It does not need F10 parts (i)–(ii), the canonical chamber-Morse cell, the `c*_n` tower, `(ICOP-step)`, or the width-3 bridge — it is a *self-contained, parallel proof* of width-3 1/3–2/3 whose only residual hypothesis is Hypothesis A.

"Pivot part (iii) to the BK/Cheeger mechanism" therefore means precisely: **for the milestone-1 deliverable "gap-free width-3 1/3–2/3," obtain the numerical conclusion from `main.tex` + Steps 1–8 (gap = Hypothesis A) instead of from F10 §6.7(iii) (gap = the HPC-per-n chamber-Morse machinery).** The F10 cohomological core retains its independent value as the general-`n` / methodology-paper result; it is not discarded — it is simply not the load-bearing path to milestone 1.

### 1.2 Hypothesis A, stated precisely

From `step8.tex` `hyp:arith` (Arithmetic richness):

> *For every `γ ∈ (0, 1/3 − δ_KL)`, there exists `T = T(γ) ≥ T_0` (with `T_0` the absolute Step-5 richness threshold) such that the `n`-independent arithmetic inequality*
> ```
>   γ² · c_5(T) · c_6 · δ_0(γ)  ≥  8
> ```
> *holds, where `δ_0(γ) := min(1/(4·C_7), 1/(2·w·K_0))` is the cascade target and `c_5(T), c_6, C_7, w, K_0` are the Step-5/6/7 constants.*

`step8.tex` `rem:final-constants-audit` gives the equivalent **explicit form** (eq:arith-explicit), substituting `c_5(T) = c_T'(T) = (c_5^⋆/4)² = (c_5^⋆)²/16`:

> ```
>   c_5^⋆(T,γ)²  ≥  128 / (γ² · c_6 · δ_0)
> ```
> *— "a purely arithmetic condition on the richness density `c_5^⋆` produced by Proposition `single-triple`."*

The named ingredients, with their origin and dependence (from `step8.tex` `rem:final-constants-audit` + the Steps-1–7 sources):

| constant | origin | dependence | notes |
|---|---|---|---|
| `γ` | the counterexample parameter | given; window `(0, 1/3−δ_KL)`, `δ_KL = 0.276393…`, so `γ ∈ (0, ≈0.057)` | for `γ ≥ 1/3−δ_KL` Kahn–Linial excludes counterexamples outright |
| `c_5^⋆(T,γ)` | Step 5, `prop:single-triple`(i) — the richness density | `c_5^⋆ = c·(\|A'\|/\|A\|)(\|B'\|/\|B\|)`, `c` absolute (convex-overlap); `≍ T^{−O(1)}`; the `T`-fat-support fraction `(\|A'\|/\|A\|)(\|B'\|/\|B\|)` is the `γ`-dependent piece | **the crux quantity** — see §1.3 |
| `c_6` | Step 6, `lem:overlap-counting` (= `c_1` there) | **absolute** — independent of `T,γ,ε,δ` | overlap-counting multiplicity factor |
| `C_7` | Step 7, potential-extraction | **absolute** | |
| `w = w(T)` | Step 7(ii) / Step 5 — interaction width | grows with `T` ("set by Step 5's richness threshold") | |
| `K_0 = K_0(γ,w)` | `step8.tex` `lem:layered-reduction` (G3) — deep-regime layering depth threshold | depends on `γ` and `w` | `γ`-dependence is the second crux — see §1.3 |
| `c_4, C_4` | Step 4, `lem:rect-stable` (`c_4 = c_1/4`, `C_4 = C'/4`) | **absolute** | enter only via `K(T)`, which enters `δ` not `δ_0` |
| `C_2(T)` | Step 4 block-transfer | polynomial in `T` | enters `K(T)`, not the form-(iii) inequality |
| `T_0` | Step 5 `cor:second-moment` — bad-set/good-bulk split threshold | **absolute** | |

### 1.3 Hypothesis A tractability — it is a constants audit, and it is polecat-attackable

**Hypothesis A is not a deep abstract conjecture.** `step8.tex` is explicit and self-aware about its status:

- "an `n`-independent arithmetic inequality" — **not** a statement about all `n`; a *single* inequality on constants;
- "it is not derived from Steps 1–7 ... and constitutes the sole external numerical input the present argument requires";
- "its verification is deferred to an external constants audit of `c_5^⋆, c_6, C_7, w, K_0`";
- `rem:final-constants-audit` ¶"No circular or impossible constraint": every constant is either (a) an absolute positive constant from a sealed upstream lemma, (b) a polynomial in `T` with `T = T(γ)`, or (c) a parameter chosen with strictly-decreasing dependence — the dependency chain `γ → T → δ_0 → ε → n` is acyclic.

So resolving Hypothesis A is a **bounded, well-defined audit of an already-written, gap-free-modulo-this proof**: read the proofs of the Steps-1–7 lemmas that produce `c_5^⋆, w(T), K_0(γ,w)` and the absolute constants, extract explicit (or explicit-enough — power-law / closed-form) bounds, and check the inequality. **No HPC, no Lean, no new axioms, no computation** — paper-and-pencil, exactly the polecat-attackable regime.

**A scoping observation that makes Route B even more tractable — the `∃T` collapses.** Hypothesis A is quantified `∃ T = T(γ)`, which looks like a search. But `step8.tex`'s own constants discussion shows `T`'s effect is **monotone-unfavourable on both sides** of (eq:arith-explicit):

- `c_5^⋆ ≍ T^{−O(1)}` — increasing `T` *shrinks* the LHS `c_5^⋆²`;
- `w = w(T)` grows with `T` — increasing `T` *shrinks* `δ_0` (via the `1/(2wK_0)` branch), *enlarging* the RHS `128/(γ²c_6δ_0)`.

The only constraint forcing `T` *up* is `T ≥ T_0` (`T_0` **absolute**, the `cor:second-moment` split threshold; `prop:single-triple`'s dichotomy itself holds for any `T ≥ 1`). So the optimal admissible choice is **`T = T_0`**, and Hypothesis A collapses to a **single inequality in `γ` alone**:
```
   c_5^⋆(T_0,γ)²  ≥  128 / (γ² · c_6 · δ_0(γ)).
```
(F25's first task is to confirm the two monotonicity directions rigorously from the Steps-5/7 proofs — `step8.tex` states both, but the audit should pin them — after which the existential is discharged.)

**The genuine mathematical content / the risk.** With `T = T_0` fixed, the question is a single asymptotic-as-`γ→0` check. As `γ → 0`:
- RHS `128/(γ²c_6δ_0)` **blows up** — `γ² → 0`, and if `K_0(γ,w) → ∞` as `γ → 0` then `δ_0 → 0` too, compounding the blow-up;
- LHS `c_5^⋆(T_0,γ)²` — governed by the `T_0`-fat-support density of a `γ`-counterexample; its `γ`-behaviour is *not* read off `step8.tex` and must be extracted from Step 5.

So the crux of Hypothesis A is a **clean, finite-flavoured quantitative question**: *does the richness density `c_5^⋆(T_0,γ)` stay bounded below — or decay slowly enough — as `γ → 0` to beat the `1/γ²` blow-up and the `K_0(γ)` factor in `δ_0`?* Three honest outcomes, **all of them better-delineated than anything Route A offers**:

1. **The crude constants already satisfy it.** Hypothesis A is proven, width-3 1/3–2/3 becomes unconditional, **milestone 1 part (iii) is done.** Plausible: `main.tex` §"What must be proved vs. what is crude" says the constants were "treated crudely; we do not attempt to optimize them" — there may be ample slack, or none; the audit decides.
2. **The crude constants fail, but the bottleneck is one un-optimised lemma.** The audit *names* the lemma (e.g. "Step 5's `c_5^⋆` first-moment bound loses a factor `γ`"), and a follow-on re-proves it with a sharper constant. Still bounded, still paper-and-pencil.
3. **The inequality is genuinely false for small `γ`.** The richness density decays too fast; the BK/Cheeger route has a real hole in the `γ ∈ (0,0.057)`, large-`n` tail. This is a **Daniel-level finding** — but it is a *precisely-located* one (`step8.tex` itself flags exactly this scope boundary), naming which constant is the barrier, not an open-ended "the route stalled."

The decisive point for tractability: in **every** outcome, F25 produces a precise, actionable verdict on a bounded investigation. That is the opposite of a treadmill.

---

## §2. Route A re-scoped — the HPC-per-n chamber-Morse grind

### 2.1 The cost

Route A materialises `M^chamber_n` (or `M^cofiber_n` + the descent) at `n = 5, 6, 7` to apply F23's Rule B and pin the genuine `c*_6, c*_7`:

- **`n = 5`:** `|PPF_5| = 4110`; `Δ_5` has `> 2·10⁷` cells at dimension 3. The chamber-Morse matching on the full `Δ_5` is **Tier-3 HPC-class** (F23 §6 Finding 6.1; F20 §1.3; F21 §5.3).
- **`n = 6`:** `Δ_6` has `1.29·10⁵` vertices (`state-F22-HPC` §5, continuation route 2). Strictly larger; Tier-3 HPC.
- **`n = 7`:** larger still.

So Route A's *first* deliverable — the datapoints — is a multi-session Tier-3 HPC programme. That cost is real but is **not the load-bearing objection.** The load-bearing objection is what the datapoints are *for*.

### 2.2 The load-bearing question — do 5 datapoints seed an `n`-uniform proof? F23's evidence says no

Route A's milestone-1 endgame is **not** the datapoints `c*_6, c*_7`; it is *"pursue the `n`-uniform proof of `(CM-rel)` seeded by the 5-datapoint record `c*_3..c*_7`."* Pinning `c*_6, c*_7` is necessary but **nowhere near sufficient** for milestone 1 — milestone 1 demands the proof *for all `n`*.

And here is the decisive finding: **F23 already ran exactly this `n`-uniform-pattern probe — on the 3-datapoint record `c*_3, c*_4, c*_5` — and it failed.** F23 §5, the `n`-uniformity probe:

| `c*_n` | new-element-`(n−1)` locus | top-poset OSA | pure-LOW set | pure-HIGH set |
|---|---|:---:|:---:|:---:|
| `c*_3` | `[HIGH, HIGH]` | `OSA(1,2)` | `{0}` | `{2}` |
| `c*_4` | `[LOW, LOW, LOW]` | `OSA(2,1,1)` | `{1,3}` | `{2}` |
| `c*_5` | `[absent, HIGH, MIXED, MIXED]` | `OSA(2,2,1)` | `{0,2}` | `{1}` |

> F23 Finding 4.1 / §5: *"There is **no `n`-uniform structural pattern**: not the new-element locus, not the top-poset OSA signature, not the pure-LOW / pure-HIGH element sets ... The **only** `n`-uniform selector is chamber-Morse criticality itself — Rule B — which is the *definition* of `c*_n`."*

Every structural discriminator that *separates* the candidate orbits at the `n = 3→4` testbed (top-poset OSA, new-element locus) is **refuted as an `n`-uniform rule** by `c*_3, c*_5`. The bet underlying Route A — "more datapoints reveal the `n`-uniform pattern" — is therefore **already partially falsified**. Going from 3 datapoints to 5 does not resurrect a pattern that 3 datapoints actively *refuted*; there is no structural reason to expect the 4th and 5th datapoints to exhibit a uniformity the first 3 explicitly lack. (This is exactly the "extrapolate a closed form from `n ≤ 5`" trap F21 Finding 2.1 warns of, and F23 §4 confirmed concretely.)

### 2.3 Route A is HPC + an unscoped, evidence-disfavoured endgame — not a path to milestone 1

Stack the pieces:

- **The `n`-uniform `(CM-rel)` proof has no identified attack.** F23 §7.2 explicitly: *"The `n`-uniform proof of `(CM-rel)` ... is not attempted."* It is not scoped — not by F23, not by `state-F22-HPC` §5. And F23's *positive* finding is that the only `n`-uniform selector is chamber-Morse criticality itself, which is HPC-per-n by definition. So the endgame is an open structural research problem *whose available evidence points against the existence of the very thing it needs.*
- **Three structural models have now narrowed-without-closing.** `state-F22-HPC` §6 / F23 §8: the ι-tower (F19→F20, broken), the `M_rel^eq`-survivor (F21→F22-HPC, broken), and the descent (F22-HPC S2→F23, narrows to 4 orbits but the selector is HPC-per-n chamber-Morse criticality). Route A is a bet on a *fourth* structural model emerging from 2 more HPC datapoints — against a 3-for-3 track record of structural models not self-closing.
- **Even fully executed, Route A ≠ milestone 1.** `c*_6, c*_7` pinned is *progress on the `c*_n` tower*, not *the gap-free width-3 proof*. The treadmill is real and `state-F22-HPC` §5 named it: route 2 is "accept HPC-per-n" — i.e. accept that there is no closed-form recursion and grind datapoints. You can always pin one more `c*_n`; you never reach "all `n`."

Route A's residual value is **not** zero — the genuine `c*_6, c*_7`, if ever produced, are useful cross-checks for the F10 cohomological core and methodology-paper anchor data (extending the `n ≤ 6` ICOP record). But that is *decoration on the general-`n` cohomological result*, not the critical path to milestone 1.

---

## §3. Head-to-head comparison + recommendation

### 3.1 The comparison

| dimension | **Route A — HPC-per-n chamber-Morse** | **Route B — BK/Cheeger pivot** |
|---|---|---|
| **residual gap** | the HPC-per-n machinery generating `c*_n` + an *unscoped* `n`-uniform `(CM-rel)` proof | **one** named arithmetic inequality — Hypothesis A |
| **gap precisely stated?** | the datapoint cost is; the `n`-uniform endgame is **not** (F23 §7.2: "not attempted") | **yes** — `step8.tex` `hyp:arith` / `eq:arith-explicit`, fully explicit |
| **attack class** | Tier-3 HPC (`Δ_5 > 2·10⁷` cells; `Δ_6` `1.29·10⁵` vertices; `Δ_7` larger) + open structural research | **paper-and-pencil constants audit** — no HPC, no Lean, no axioms |
| **polecat-attackable?** | the HPC datapoints, yes (multi-session Tier-3); the endgame, **no identified attack** | **yes** — a bounded audit of 5 step-files' sealed lemmas |
| **evidence on feasibility** | F23 **refuted** every `n`-uniform structural discriminator on the 3-datapoint record; the core bet is partially falsified | `step8.tex` proves Steps 1–7 unconditional + G1–G5 discharged; Hypothesis A is the *sole* residual, by the paper's own audit |
| **reaches milestone 1 if it succeeds?** | **no** — `c*_6,c*_7` pinned is not "all `n`, no gaps"; still owes the `n`-uniform proof | **yes** — Hypothesis A closed ⟹ `thm:main-step8` unconditional ⟹ width-3 1/3–2/3 proven, gap-free, all `n` |
| **worst case** | another Tier-3 datapoint, still no pattern — a treadmill (`state-F22-HPC` §5 route 2's own framing) | a *named* bottleneck lemma, or a *precisely-located* Daniel-level finding — bounded and informative either way |
| **relation to the F19–F23 wall** | doubles down on it — needs exactly the HPC chamber-Morse machinery F23 showed does not self-close | **sidesteps it entirely** — does not use `c*_n`, the `c*_n` tower, or the cofiber LES induction |

### 3.2 Recommendation — Route B, decisively

**Recommend Route B.** It is the more tractable path to milestone 1 on every axis that matters, and the margin is not close:

1. **Single finite gap vs. HPC + an unscoped endgame.** Route B's entire residual is one arithmetic inequality that the in-tree paper itself isolates and calls "the sole external numerical input." Route A's residual is Tier-3 HPC *and* an `n`-uniform proof that F23 declined to attempt and whose prerequisite (an `n`-uniform structural rule) F23's evidence says does not exist.
2. **Route B's success *is* milestone 1; Route A's success is not.** Closing Hypothesis A makes `thm:main-step8` unconditional — that *is* the gap-free width-3 1/3–2/3 proof, directly. Closing Route A's datapoint phase leaves milestone 1 still owing its hardest, unscoped piece.
3. **Route B is paper-and-pencil polecat work; Route A is not.** The F24 constraints (no HPC, no Lean, no axioms) describe Route B's *execution*, not just its scoping. Route A's execution is the opposite.
4. **Route B's worst case dominates Route A's worst case.** If Hypothesis A is hard or false, F25 says *which constant* and *why* — a located, actionable result. If Route A stalls, you have one more expensive datapoint and the same structural verdict F23 already delivered.

### 3.3 PM lean — confirmed and strengthened

pm-onethird leaned Route B; the lean is **confirmed on evidence**. F24 strengthens the *reason*:

- The PM's reason was "Route A risks a treadmill; Route B is a genuinely different attack." Both true.
- F24's sharper reason: **Route B's gap is the actual in-tree width-3 paper's *sole remaining hypothesis*, it is a constants audit (not a deep conjecture), and resolving it *is* milestone 1 part (iii) with no further machinery — whereas Route A, even fully executed, still owes the `n`-uniform `(CM-rel)` proof that F23's own evidence disfavours.** The fork is not "treadmill vs. different attack" — it is "an unscoped HPC research programme that doesn't reach the goal even if it succeeds" vs. "a bounded paper-and-pencil audit that *is* the goal."

The PM's lean did not need correcting. F24's job was to confirm-or-correct on evidence; the evidence confirms.

---

## §4. F25 — the execution ticket scoped

> **F25 — The Hypothesis A constants audit (the BK/Cheeger execution of milestone 1 part (iii)).**

**Parent:** mg-a30d (F24, GREEN-route-B-recommended).
**Type:** Structural / paper-and-pencil constants audit. **No HPC; no Lean; no new axioms; no computation.** Cross-repo read: `one_third_width_three` `step1.tex`, `step4.tex`, `step5.tex`, `step6.tex`, `step7.tex`, `step8.tex` (the sealed Steps-1–7 lemma proofs + the `step8.tex` constants discussion). Multi-session-able; cumulative `docs/state-F25.md`. Suggest high priority, ~300k cap.

**Goal.** Resolve, or precisely delineate, **Hypothesis A** (`step8.tex` `hyp:arith` / `eq:arith-explicit`):
```
   for every γ ∈ (0, 1/3 − δ_KL):   c_5^⋆(T,γ)²  ≥  128 / (γ² · c_6 · δ_0(γ))   for some admissible T = T(γ).
```

**Scoped subtasks** (in order):

1. **Discharge the `∃T` existential.** Confirm — from the Step-5 (`prop:single-triple`, `cor:second-moment`) and Step-7 (`w(T)`) proofs — the two monotonicity directions `step8.tex` asserts: `c_5^⋆ ≍ T^{−O(1)}` (decreasing) and `w(T)` non-decreasing. If both hold, `T = T_0` (absolute) is optimal and Hypothesis A collapses to a single inequality in `γ`. Pin `T_0` numerically from `cor:second-moment`.

2. **Extract explicit bounds for each named constant.**
   - `c_5^⋆(T_0,γ)` — Step 5 `prop:single-triple`(i): `c_5^⋆ = c·(|A'|/|A|)(|B'|/|B|)`, `c` absolute (convex-overlap). **The crux:** bound the `T_0`-fat-support density `(|A'|/|A|)(|B'|/|B|)` of a `γ`-counterexample as a function of `γ` — this is where the `γ`-dependence of the LHS lives.
   - `K_0(γ,w)` — `step8.tex` `lem:layered-reduction` (G3): the deep-regime layering-depth threshold. **The second crux:** its `γ`-dependence governs whether `δ_0 → 0` as `γ → 0`.
   - `w = w(T_0)` — Step 7(ii) / Step 5 interaction width — a fixed number once `T_0` is fixed.
   - `c_6` (Step 6 `lem:overlap-counting`), `C_7` (Step 7 potential-extraction), `c_4, C_4` (Step 4 `lem:rect-stable`) — **absolute**: extract numerical lower/upper bounds.
   - `C_2(T_0), K(T_0)` — Step 4 block-transfer — needed only for the `ε`-budget cross-check, not the form-(iii) inequality.

3. **Check satisfiability over `γ ∈ (0, 1/3 − δ_KL) ≈ (0, 0.057)`.** With `T = T_0` and the extracted bounds, evaluate the single-`γ` inequality. Three outcomes, each a clean verdict:
   - **GREEN-hypothesis-A-proven** — the (crude or audited) constants satisfy the inequality on the whole window ⟹ width-3 1/3–2/3 is **unconditional**, milestone 1 part (iii) **done**.
   - **AMBER-bottleneck-located** — the inequality fails with the crude constants, but the audit names the single un-optimised lemma responsible; scope a follow-on F26 to re-prove it with a sharper constant.
   - **RED-hypothesis-A-false** — the inequality is genuinely false in the small-`γ` tail (richness density decays too fast); surface as a precisely-located Daniel-level finding, naming the barrier constant.

4. **Cross-check the `ε`/`n_0` interplay.** Confirm the cascade `γ → T_0 → δ_0 → ε → n` is realisable (`ε := δ_0/(2K(T_0))`; `n_0(γ,T_0)` polynomial in `1/γ`) — `step8.tex` discharges this (G2, `lem:small-n`), so this is a confirmation pass, not new work.

**Deliverables.** `docs/compatibility-geometry-F25-hypothesis-A-constants-audit.md` + `docs/state-F25.md`.

**Scope boundary.** F25 is the BK/Cheeger route's execution. The F19–F23 chamber-Morse arc and Route A stay parked. The F10 cohomological core (parts i–ii, unconditional) is untouched. The Lean `width3_one_third_two_thirds` 4-axiom trust surface is untouched (the BK/Cheeger proof is paper-level structural; no Lean changes).

---

## §5. What F24 establishes and does not establish

### 5.1 Establishes

- **The route fork is resolved on evidence: GREEN-route-B-recommended.** Route B (the BK/Cheeger pivot) is the decisively more tractable path to milestone 1 part (iii). The recommendation is forced, not a default — §3.
- **Route B scoped (§1).** What it proves (= the milestone-1 target, the `[1/3,2/3]` statement), conditional on what (Hypothesis A *alone* — Steps 1–7 unconditional, G1–G5 discharged in `step8.tex`). The F10-part-(iii) ⟷ BK/Cheeger dictionary is built (§1.1). Hypothesis A is stated precisely in both forms (§1.2) and assessed **attackable**: it is a paper-and-pencil constants audit, not a deep conjecture; the `∃T` existential collapses to `T = T_0` (§1.3).
- **Route A re-scoped (§2).** Its cost is multi-session Tier-3 HPC (`Δ_5 > 2·10⁷` cells onward); its endgame — the `n`-uniform `(CM-rel)` proof — is **unscoped and evidence-disfavoured**: F23 already refuted every `n`-uniform structural discriminator on the 3-datapoint record, so 2 more HPC datapoints do not seed the proof. Route A, even fully executed, does **not** reach milestone 1.
- **The PM lean (Route B) is confirmed and its reason sharpened** (§3.3).
- **F25 scoped precisely** (§4) — the Hypothesis A constants audit, with ordered subtasks and three named outcome verdicts.
- **Trust-surface impact: none.** Paper-and-pencil scoping; no new axioms, no Lean changes, no computation, no HPC. The in-tree Lean artifact is untouched.

### 5.2 Does not establish

- **Hypothesis A is not resolved.** F24 assesses its *tractability* (a constants audit, polecat-attackable) — not its *truth*. Whether the inequality holds is F25's job; the three outcomes (GREEN / AMBER / RED) are all live until the audit runs.
- **The monotonicity-in-`T` collapse is asserted from `step8.tex`'s own constants discussion, not re-derived.** F25 subtask 1 confirms it from the Steps-5/7 proofs.
- **Route A is not refuted as mathematics.** The chamber-Morse route is a valid attack (mg-26fc: distinct-but-resonant) and its datapoints retain cross-check value for the F10 cohomological core. F24 finds Route A is the *less tractable path to milestone 1* — not that it is wrong.
- **F24 does not touch the F10 cohomological core, the F19–F23 arc, or `mg-b345` (route iii / Quillen fiber).** All stay as they are; route (iii)/mg-b345 stays parked.

---

## §6. References

### 6.1 Predecessor and sibling mg-tickets

- **mg-531f** — F23 (the canonical descent rule): **GREEN-descent-pinned (HPC-per-n).** **Parent.** `docs/compatibility-geometry-F23-canonical-descent-rule.md`: Verdict + §6 Finding 6.1 (HPC-per-n is decisive), §4–§5 (every structural discriminator refuted as `n`-uniform — the core evidence against Route A), §8 (the two documented continuations — the fork F24 resolves). `docs/state-F23.md`.
- **mg-26fc** — the two 1/3–2/3 mechanisms: **GREEN-distinct-complementary.** `docs/compatibility-geometry-structural-analogy-scoping.md`: §1 (the BK/Cheeger column rigorised — `main.tex` + `step8.tex` is mechanism (a)), §1.5(c) (Theorem E as the in-tree concretisation), §3 (the F10 ⟷ BK/Cheeger dictionary toolkit), §4.1.3 (distinct open gaps: Hypothesis A vs. (FG-Cofiber)). The starting point for F24 Goal 1.
- **mg-0c5d** — F22-HPC Session 2: **RED-tripwire.** `docs/state-F22-HPC.md` §5 (the descent wall; the three continuation routes — Route A = route 2 "accept HPC-per-n"; finding 6 — the 4-orbit under-specification).
- **mg-43fb** — F22-HPC Session 1: **GREEN-partial.** `docs/state-F22-HPC.md` §1–§2.
- **mg-a2cb** — F21 (the genuine non-ι-lift chamber-Morse cell): **GREEN-needs-hpc-anchor.** Proposition F21.1 (the cofiber-Morse induction); Finding 2.1 (no closed form forced by `n ≤ 5`); §5.3 (the chamber-Morse greedy is HPC for `n ≥ 5`).
- **mg-c3fa** — F20: **GREEN-partial.** §1.3 (the chamber-Morse greedy is HPC-class for `n ≥ 5`).
- **mg-4d3a** — F17 (`(UCC.1)`); **mg-d039** — F18 (`(UCC.2)`): together make the F10 cohomological core unconditional.
- **mg-8216** — F10: **GREEN-conditional.** `docs/general-n-proof-synthesis.md` §6.7(iii) (part (iii), the numerical width-3 conclusion — what Route B delivers via a different mechanism); §5.4 ((ICOP-step)); §7.3 (the width-3 reduction bridge).

### 6.2 In-tree (the BK/Cheeger 1/3–2/3 spine — Route B)

- `main.tex` — §"Approach: Cheeger-type expansion on the BK graph" (the eight-step program); §"Main result" (Theorem `thm:main`, conditional on Hypothesis A); §"What must be proved vs. what is crude" (the constants "treated crudely; we do not attempt to optimize them" — directly relevant to F25's audit slack).
- `step8.tex` — `thm:cex-implies-low-expansion` (Theorem E, **discharged in full** in `step8.tex` §`sec:G1`); `hyp:arith` (**Hypothesis A** — the sole residual gap); `thm:main-step8` + scope note; `rem:n-dependence-g1` (the `n`-independent arithmetic reduction); `prop:G2` + `rem:G2-order` (the parameter cascade); `rem:final-constants-audit` (`eq:arith-explicit` — the explicit form; the full constants inventory with origins and dependences); G1–G5 (all discharged inside `step8.tex`); `lem:small-n` / `rem:small-n` (the small-`n` base case — discharged).
- `step5.tex` — `prop:single-triple` (the richness dichotomy; `c_5^⋆ = c·(|A'|/|A|)(|B'|/|B|)`); `cor:second-moment` (`c_5(T) = c_T'(T) = (c_5^⋆/4)²`; `T_0` absolute).
- `step4.tex`, `step6.tex`, `step7.tex` — the sources of `c_4, C_4, C_2(T)` / `c_6` / `C_7, w(T), K_0` respectively — F25's audit targets.

### 6.3 Mathematical literature

- R. Bubley, M. Karzanov, *Path coupling / faster random generation of linear extensions* (1997/1998) — the BK Markov chain; spectral gap controls mixing.
- J. Cheeger (1970); Lawler–Sokal, Sinclair–Jerrum — the discrete Cheeger inequality for reversible chains (the Dirichlet/conductance comparison `lem:dirichlet-conductance`).
- S. Kislitsyn (1968); M. Fredman (1976); N. Linial, *The information-theoretic bound is good for merging*, SIAM J. Comput. 13 (1984) — the 1/3–2/3 conjecture; Linial's width-2 theorem (the BK proof's width-recursion base, and `lem:small-n`).
- J. Kahn, N. Linial, *Balancing extensions via Brunn–Minkowski*, Combinatorica 11 (1991) — the unconditional `δ_KL = 0.276393…` bound (excludes counterexamples for `γ ≥ 1/3 − δ_KL`; defines Hypothesis A's `γ` window).
- J. Kahn, M. Saks (1984); G. Brightwell, S. Felsner, W. Trotter (1995) — the `[3/11,8/11]` interval (the sharper conclusion F10 part (iii) carries; not a milestone-1 requirement).

### 6.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. (F24 is pure internal scoping; Route B's execution stays internal.)
- 2026-05-14T17:23Z — milestone 1 = the full gap-free width-3 proof, no sketches or gaps. (F24's recommendation is chosen *because* Route B reaches exactly this — closing Hypothesis A makes `thm:main-step8` unconditional, gap-free, all `n` — whereas Route A does not.)
- 2026-05-14T22:32Z — "keep pushing." (F24 resolves the F23-surfaced fork decisively and scopes the execution ticket, rather than escalating the decision.)

---

*Polecat: mg-a30d (F24). Branch: `polecat-cat-mg-a30d`. Verdict: **GREEN-route-B-recommended** — pivot F10 part (iii) to the BK/Cheeger-expansion mechanism (`main.tex` + Steps 1–8). Route B's entire residual gap is **Hypothesis A** (`step8.tex` `hyp:arith`) — one `n`-independent arithmetic inequality the in-tree paper itself isolates as "the sole external numerical input"; it is a paper-and-pencil constants audit, not a deep conjecture, and the `∃T` existential collapses to `T = T_0`. Route A (HPC-per-n chamber-Morse grind) is Tier-3 HPC plus an unscoped `n`-uniform `(CM-rel)` proof that F23's own evidence disfavours (every structural discriminator refuted as `n`-uniform on the 3-datapoint record) — and, even fully executed, does not reach milestone 1. PM lean (Route B) confirmed and its reason sharpened. F25 scoped: the Hypothesis A constants audit. No new axioms; no Lean changes; no computation; no HPC. Cumulative state: `docs/state-F24.md`.*
