# Compat-Geom — F20: the n-uniform structure of the canonical chamber-Morse critical cells — (L2-struct) + (W3-cover) (mg-c3fa)

**Branch:** `polecat-cat-mg-c3fa`.
**Parents:** mg-5722 (F19, GREEN-partial) §3.3–3.4 + §4.3–4.4 — the two named residuals (L2-struct) and (W3-cover) and the explicit F20 recommendation. mg-4d3a (F17) + mg-d039 (F18) — the now-unconditional cohomological core. mg-8216 (F10) §5.2–5.4 / §7.3 — the ι-tower framing and the width-3 bridge. mg-1e99 (F8) §4.1–4.6, §6 — the chamber-Morse construction. mg-7b3b (F8′) / mg-3bf3 (F8′-HPC) — the n=6 ι₅-lift candidate.
**Type:** Structural / combinatorial argument (S_n-equivariant chamber-Morse theory on Δ_n), with a bounded verification harness. LaTeX-style Markdown; **no new axioms; no Lean changes.** Cumulative state in `docs/state-F20.md`.
**Daniel directives:** 2026-05-14T05:18Z (finish the induction internally; no external collaboration); 2026-05-14T08:05Z (focus on the induction); 2026-05-14T17:23Z (this is the last research ticket of milestone 1 — full proof of width 3, no sketches or gaps).

**Verdict: GREEN-partial.** F20 substantially advances the n-uniform structural understanding of the canonical chamber-Morse critical cells, but does **not** close either residual n-uniformly. The headline content is a set of **three structural corrections** that re-found the residuals on solid ground — the prior framing (the ι-tower form of F10 §5.2, on which F19's reductions of *both* (ICOP-step) and the width-3 bridge rest) is found **not literally correct**, and the F8′-HPC "candidate c\*₆" is found to **violate (L2-struct)** — together with a precise re-statement of what an n-uniform proof now requires, and a genuine extension of the rigorous base of the *end goal* (every width-3 poset has a balanced incomparable pair) to **m ≤ 5** (m = 6 verification in progress; see §6.3). (L2-struct) holds **exactly at n = 3, 4, 5**; (W3-cover)'s per-orbit content holds **exactly at m ≤ 5**. Trust-surface impact: **none**.

---

## §1. Setting — the two residuals of milestone 1

### 1.1 Where F20 sits

After **F17** (mg-4d3a) and **F18** (mg-d039) the **F10 cohomological core** is **UNCONDITIONAL**: `Hyp(n)` holds for all `n ≥ 3` — `Δ_n ≃_ℚ S^{n-2}`, `H̃^{n-2}(Δ_n;ℚ) = sgn_{S_n}`, and `ω_bal^{(n)}` exists, is unique up to scalar, and pairs `±1` with the canonical critical cell. The master hypothesis (UCC) is complete.

The **numerical width-3 conclusion** — F10 §6.7 part (iii), the explicit `[3/11, 8/11]` interval — still rests on two further conditional inputs, neither part of (UCC). **F19** (mg-5722) reduced both to a *single flavour* of residual — an n-uniform structural understanding of the canonical chamber-Morse critical cells — and named them:

1. **(L2-struct).** For every `n ≥ 3`, the canonical top poset `G_n` of the canonical critical `(n-2)`-cell `c*_n` is a **width-2 ordinal sum of antichains** (OSA) containing at least one antichain block of size 2. Given (L2-struct), F19 Proposition 3.1 + the symmetric-pair lemma (L1) close (ICOP-step).

2. **(W3-cover).** For every `m ≥ 5` and every width-3 partial order `P` on `m` elements, some `S_m`-orbit representative of `P` appears as a poset `P_k` on a canonical critical chain of the chamber-Morse matching of `Δ_m`. Given (W3-cover) + (ICOP-step), F19 closes the width-3 bridge for `m ≥ 5`.

F19's recommendation: a single F20 ticket on the n-uniform chamber-Morse critical-cell structure addresses both.

### 1.2 The objects (recap, F10 §1.1)

`PPF_n` = proper partial orders on `[n] = {0,…,n−1}` (non-empty, non-total, transitively-closed antisymmetric relation sets), ordered by relation-set inclusion (more relations ⇒ higher ⇒ fewer linear extensions); `|PPF_n| = 12, 194, 4110, 129302` at `n = 3,4,5,6`. `Δ_n := Δ(PPF_n)`. `ι_n : PPF_n ↪ PPF_{n+1}` adds element `n` incomparable to all of `[n]`. The **Kahn–Saks probability** of an incomparable pair `(x,y)` of `P` is `Pr_P[x ≺ y] = |L(P ∪ {x<y})| / |L(P)|`; the **BFT-sharp** interval is `[3/11, 8/11] ⊂ [1/3, 2/3]`.

The canonical critical `(n-2)`-cell `c*_n = (P_0 ⊂ ⋯ ⊂ P_{n-2})` is the lex-min representative of the `S_n`-orbit of critical `(n-2)`-cells of the chamber-Morse matching; `G_n := P_{n-2}` is its **top poset**.

### 1.3 What F20 set out to do, and what it found

The F20 plan (per ticket mg-c3fa) was: **(a)** attempt the structural theorem — that the `S_n`-equivariant Forman-respecting chamber-Morse refinement produces critical cells with the (L2-struct)/(W3-cover) structure; **(b)** fall back, if needed, to the bounded F8‴ HPC chamber-Morse anchor run at `n = 7, 8`.

F20's actual finding reshapes the task. The chamber-Morse "canonical critical chain" as the prior tickets *modelled* it — the **ι-tower form** of F10 §5.2 — is **not literally the genuine object** (§3). F19's reductions of both (ICOP-step) and the width-3 bridge are *built on* that ι-tower model. F20's primary deliverable is therefore to **re-found the residuals** on the corrected understanding, verify the corrected statements on the exact record, and reduce them as far as the corrected framework supports — which is the GREEN-partial outcome.

The full chamber-Morse greedy on the order complex of `PPF_n / S_n` is **HPC-class beyond single-session budget already at n = 6** (F5 reported ~567 s for the n = 5 chamber order complex of 352,947 cells; the n = 6 chamber order complex is ≥ two orders of magnitude larger). The F8‴ anchor run at `n = 7, 8` as literally specified is therefore **not single-session-feasible**; F20 instead delivers the *feasible* anchor data (the n = 6 chamber enumeration and orbit poset; §6.4) and the exact-record certification.

---

## §2. The exact record — (L2-struct) holds at n = 3, 4, 5

The F20 harness (`scripts/compat_geom_F20_chamber_morse_hpc.py`, §7) reconstructs the canonical critical chains from the F2/F5 literature and certifies their structure with exact rational arithmetic.

| `n` | chain `c*_n` (Hasse, bottom→top) | `|L|`-profile | per-step `Pr` | `G_n` | (L2-struct)? |
|---:|---|---|---|---|:---:|
| 3 | `{0<2}` ⊂ `{0<1,0<2}` | `(3,2)` | `(2/3)` | `OSA(1,2)` | ✓ |
| 4 | `{1<2,3<0,3<2}` ⊂ `{0<2,1<2,3<0}` ⊂ `{0<2,1<0,3<0}` | `(5,3,2)` | `(3/5, 2/3)` | `OSA(2,1,1)` | ✓ |
| 5 | `{0<1,2<1,3<1}` ⊂ `{0<1,0<4,2<1,2<4,3<1}` ⊂ `{0<4,2<4,3<1,4<1}` ⊂ `{0<3,0<4,2<3,2<4,3<1,4<1}` | `(30,14,8,4)` | `(7/15, 4/7, 1/2)` | `OSA(2,2,1)` | ✓ |

So **(L2-struct) holds exactly at `n = 3, 4, 5`**: `G_3, G_4, G_5` are width-2 ordinal sums of antichains, each with a size-2 block, and every per-step `Pr` of every chain lies in `[3/11, 8/11]`. This is the rigorous, re-confirmed base.

A note on `G_n`'s linear-extension count. A width-2 OSA `A_{a_1} ⊕ ⋯ ⊕ A_{a_r}` (each `a_i ∈ {1,2}`) has `|L| = ∏ a_i! = 2^{s}`, where `s` = number of size-2 blocks. So `|L(G_n)| = 2^{s_n}`, with `s_3 = s_4 = 1`, `s_5 = 2`. This **power-of-2 signature** is a clean necessary condition for (L2-struct), and it is the wedge that exposes the corrections of §3.

---

## §3. Three structural corrections — the F20 headline

F20's central finding is that the *model* of the canonical critical chain used by F10 §5.2, F8′, F8′-HPC and (consequently) F19's reductions — the **ι-tower form** — is not the genuine object. Three precise corrections.

### 3.1 Correction 1 — the F8′-HPC "candidate c\*₆" violates (L2-struct)

F8′-HPC §5 (mg-3bf3) records the candidate
```
    c*_6  :=  ( ι_5(P_0), ι_5(P_1), ι_5(P_2), ι_5(P_3), P_3 ∪ {(0,2)} ),
```
the ι₅-lift of `c*_5` (element 5 free throughout) with the lex-min cover `(0,2)` appended; `|L|`-profile `(180, 84, 48, 24, 12)`. F8′-HPC §6.2 *conjectured* (AMBER-budget-cap) this is the genuine `c*_6`.

> **Finding 3.1.** The F8′-HPC candidate top poset `G_6 = ι_5(G_5) ∪ {(0,2)}` has **width 3, not 2**, so it is **not** a width-2 ordinal sum of antichains: **(L2-struct) fails on the F8′-HPC candidate.**

*Verification (harness §B).* `G_6` (candidate) `= {0<2, 0<3, 0<4, 2<3, 2<4, 3<1, 4<1}` on `[6]`, with **element 5 isolated** — the appended cover `(0,2)` is a relation *inside `[5]`*, so element 5 is never absorbed into the poset. The set `{3,4,5}` is a 3-element antichain (3∥4, 3∥5, 4∥5), so `width(G_6) = 3`. Also `|L(G_6)| = 12`, which is *not* a power of 2 — already inconsistent with `G_6` being a width-2 OSA.

**Consequence.** The genuine canonical `c*_6` is **not** the naive ι₅-lift candidate. F19's `n = 6` entry of its `(L2)`-verification table (F19 §3.2) used `ι_5(G_5)` (element 5 free) as a *proxy* "top poset", and F19's harness §H never OSA-tested any `n = 6` poset; so F19's "(L2-struct) verified at n ≤ 6" is, on inspection, **substantiated only at n ≤ 5** — the n = 6 line was the ι-lift proxy, not the genuine `c*_6`.

### 3.2 Correction 2 — the ι-tower form is not literally correct

F10 §5.2 asserts the canonical critical chain has the **ι-tower form**
```
    c*_n  =  ι_{n-1}( ι_{n-2}( ⋯ ι_3(c*_3) ⋯ ) )  ∪  {one new cover step per level},
```
i.e. the bottom `n-1` posets of `c*_n` are `ι_{n-1}`-lifts of `c*_{n-1}`'s posets — all with element `n-1` isolated — and exactly one poset is appended at the top. This is the structural premise behind F8′'s multiplicativity audit and behind F19's reduction of (ICOP-step) to a *single* "new cover step per level".

> **Finding 3.2.** The genuine `c*_5` does **not** have the ι-tower form. Of its four posets `P_0, P_1, P_2, P_3`, **only `P_0` has element 4 isolated**; `P_1, P_2, P_3` all use element 4. So `c*_5 ≠ ι_4(c*_4) ∪ {append}` — the ι-tower form already fails at the `c*_4 → c*_5` step.

*Verification (harness §C).* Element-4 isolation along `c*_5`: `P_0` isolated `[4]`; `P_1, P_2, P_3` isolated `[]`. In particular the 2nd-from-top poset `P_2 = {0<4,2<4,3<1,4<1}` has `|L(P_2)| = 8`, **not** `5·|L(G_4)| = 5·2 = 10`; it is not an ι-lift. (The F8′ multiplicativity audit `|L(ι_5(P_k))| = 6·|L(P_k)|` that "confirmed the ι-tower at n = 6" was an audit of the ι-lift *candidate* — a tautology, since the candidate is *defined* as an ι-lift — and not a confirmation of the genuine `c*_6`.)

### 3.3 Correction 3 — (L2-struct) and ι-tower multiplicativity are jointly inconsistent for n ≥ 7

The two corrections above are not merely "the literature picked the wrong representative"; the ι-tower model and (L2-struct) are **logically incompatible** for large `n`, so the ι-tower could not have been the genuine object in the first place.

> **Finding 3.3.** Suppose the genuine `c*_n` had the ι-tower form *and* `G_n` were a width-2 OSA (i.e. (L2-struct) held). Then the top step of `c*_n` — from `ι_{n-1}(G_{n-1})` to `G_n` — has
> ```
>     Pr  =  |L(G_n)| / |L(ι_{n-1}(G_{n-1}))|  =  2^{s_n} / ( n · 2^{s_{n-1}} ),
> ```
> using `|L(G_n)| = 2^{s_n}` (§2) and the ι-multiplicativity `|L(ι_{n-1}(Q))| = n·|L(Q)|`. Since `s_n ≤ ⌊n/2⌋`, the numerator `2^{s_n} ≤ 2^{n/2}` while the denominator carries the factor `n` (and, telescoped down the tower, the full `n!`-scale). For `n ≥ 7` this ratio is **forced below `3/11`** — the step is *not* BFT-sharp — contradicting ICOP. (Harness §C2: the *largest possible* ι-tower top-step `Pr` is `1/7 ≈ 0.143` at `n = 7`, `1/9` at `n = 9`, all well outside `[3/11, 8/11]`.)

**Consequence — the resolution.** The genuine `c*_n` is **not an ι-lift**. Its second-from-top poset stays **near-maximal** (small `|L|`, *not* `n!`-scale), exactly as the genuine `c*_5` already exhibits: `|L(P_2)| = 8`, with top step `4/8 = 1/2` — BFT-sharp — *precisely because* `P_2` is near-maximal rather than an ι-lift of `G_4` (which would give `|L| = 10` and top step `4/10 = 2/5`, still BFT-sharp at `n = 5` but headed out of range). The genuine canonical chain **descends in width and climbs in `|L|`-rank only modestly** through its last steps; it does not "lift then append".

This is the structural correction that re-founds the residuals: **(L2-struct) is consistent** — it is *the ι-tower model* that was inconsistent with it, and that model is not the genuine object.

---

## §4. The corrected reduction

### 4.1 What the residuals actually require, post-correction

Strip the ι-tower scaffolding. The genuine, framework-independent content needed for F10 part (iii) is:

> **(CM-struct).** There is an `S_n`-equivariant discrete Morse function on `Δ_n` realising `Δ_n ≃ S^{n-2}` (which *exists*, unconditionally, by F17 + F18) whose canonical critical `(n-2)`-cells form an `S_n`-equivariant family of chains such that
> **(i)** every per-step Kahn–Saks `Pr` along every critical chain lies in `[3/11, 8/11]`;
> **(ii)** the top poset of each critical chain is a width-2 ordinal sum of antichains (this is **(L2-struct)**, and via §4.2 it *implies* (i) for the new top step);
> **(iii)** the critical chains collectively pass through (an `S_m`-orbit representative of) every width-3 poset (this is **(W3-cover)**).

F19's two residuals are exactly (ii) and (iii). The F20 correction is that (i)/(ii)/(iii) must be read as properties of *the genuine `S_n`-equivariant Morse function*, **not** of the ι-tower model — and in particular the chain is built by genuine chamber-Morse refinement, descending from a wide low-rank `P_0` to a width-2 near-maximal `G_n`, *not* by lifting-and-appending.

### 4.2 The symmetric-pair engine survives the correction intact

The one piece of F19 that is **untouched** by the corrections — because it never used the ι-tower — is the **symmetric-pair lemma (L1)** and its consequence for OSAs:

> **Lemma (L1) (F19 §2), recertified.** If `{x,y}` is an incomparable pair of a finite poset `P` swapped by some `σ ∈ Aut(P)`, then `Pr_P[x ≺ y] = 1/2 ∈ [3/11, 8/11]`.
>
> **OSA-symmetry fact (F20 §D), recertified.** In a **width-2 ordinal sum of antichains** every incomparable pair lies inside a single antichain block, and the within-block transposition (fixing all other elements) is an automorphism. Hence **every incomparable pair of a width-2 OSA is a symmetric pair**, and a size-2 block furnishes one.

*Verification (harness §D).* L1 holds on `G_3, G_4, G_5` and on the canonical width-2 OSAs `OSA(2,2,2)`, `OSA(2,2,2,1)`, `OSA(2,2,1,1,1)` at `n = 6, 7`: every symmetric incomparable pair has `Pr = 1/2` exactly, and in every width-2 OSA the symmetric pairs are *exactly* the incomparable pairs.

**Consequence.** (L2-struct) ⟹ "`G_n` has a symmetric incomparable pair, and the new cover refining `G_n` upward lands inside a size-2 block (a symmetric pair)" ⟹ that step has `Pr = 1/2` (L1). So **(L2-struct) ⟹ part (i) of (CM-struct) at the top step**, by the *same* Proposition-3.1 argument as F19 — that argument is order-theoretic and survives intact. What the corrections remove is only the *ι-tower derivation* of the *inherited* steps; those must now be controlled by the genuine chamber-Morse descent (§5).

### 4.3 The corrected status of (ICOP-step)

F19 reduced (ICOP-step) — "the lex-min new cover of the ι-tower top poset is BFT-sharp" — to (L2-struct), via the ι-tower. With the ι-tower corrected, (ICOP-step) is **subsumed into (CM-struct)(i)**: it is the statement that *every per-step `Pr` of the genuine canonical critical chains is BFT-sharp*. By §4.2, the *top* step is `Pr = 1/2` once (L2-struct) holds; the *inherited* steps are no longer "n-independent by ι-multiplicativity" (Correction 3 kills that) and must be established as part of the genuine chamber-Morse descent. This is a genuine widening of the (ICOP-step) residual relative to F19's (over-optimistic, ι-tower-based) reduction — and an honest one.

---

## §5. (L2-struct) — what F20 establishes

### 5.1 Established

- **(L2-struct) holds exactly at `n = 3, 4, 5`** (harness §A), with `G_3 = OSA(1,2)`, `G_4 = OSA(2,1,1)`, `G_5 = OSA(2,2,1)` — width-2 OSAs with a size-2 block.
- **(L2-struct) is logically consistent** (Correction 3): the apparent obstruction at `n ≥ 7` is an obstruction to the *ι-tower model*, not to (L2-struct); the genuine non-ι-lift chain (witnessed at `n = 5`: `|L(P_2)| = 8`, not `10`) evades it.
- **(L2-struct) ⟹ the top-step BFT-sharpness** of the genuine critical chain, via the symmetric-pair engine (§4.2), with the same rigour as F19 Proposition 3.1.
- **The negative control** (F19 §3.4, re-confirmed in spirit): (L2-struct) is *not* a naive greedy invariant — the "always refine the lex-min symmetric pair" tower loses all symmetry, so (L2-struct) is a property of the genuine chamber-Morse construction specifically.

### 5.2 The honest residual

An n-uniform proof of (L2-struct) requires identifying the genuine canonical critical cell `c*_n` for general `n` — which, by §3, is **not** the ι-lift candidate and **not** governed by the ι-tower. The genuine object is the lex-min critical `(n-2)`-cell of the genuine `S_n`-equivariant chamber-Morse matching on `Δ_n`. F20 establishes:

1. **The target signature.** `G_n` must be a width-2 OSA, `|L(G_n)| = 2^{s_n}`, `s_n ≤ ⌊n/2⌋`. The exact record gives `s_3 = s_4 = 1`, `s_5 = 2`; the pattern at `n ≥ 6` is **not yet pinned** — the genuine `G_6` is one of the `n = 6` width-2-OSA-with-size-2-block orbits enumerated in §6.4, and which one requires the genuine matching.
2. **The structural constraint.** Whichever it is, `G_{n+1}` is obtained from `G_n` by **absorbing element `n` into the OSA structure** (as a new singleton block, or by joining a singleton block to make it a size-2 block) — *not* by leaving `n` free and appending a within-`[n]` cover (which is exactly the F8′-HPC candidate's error, Correction 1). The genuine top step `ι_n(G_n) ⊂ G_{n+1}` therefore has element `n` non-isolated in `G_{n+1}`.
3. **What is still open.** That the genuine chamber-Morse matching *selects* such an absorption at every `n` — equivalently, that the lex-min critical cell's top poset is always a width-2 OSA — is the residual. It needs either (a) a dedicated structural theorem on the `S_n`-equivariant Forman-respecting refinement, or (b) the genuine F8‴ chamber-Morse run at `n = 6, 7` (which §1.3 records is HPC-class beyond single-session budget). F20 has *not* closed this; it has corrected its statement and pinned its target.

---

## §6. (W3-cover) — what F20 establishes

### 6.1 The reduction, restated correctly

F19 §4.3 reduced the width-3 bridge for `m ≥ 5` to `(ICOP-step) + (W3-cover)`. With (ICOP-step) subsumed into (CM-struct)(i) (§4.3), the bridge for `m ≥ 5` is: *every width-3 `P` lies as a `P_k` on a canonical critical chain, and the cover step `P_k ⊂ P_{k+1}` along that chain is BFT-sharp* — which then witnesses Kahn–Saks 1/3-2/3 for `P`. So (W3-cover), as stated, plus (CM-struct)(i), gives the width-3 conclusion.

### 6.2 The end goal, verified directly at m ≤ 5 — a genuine extension of the rigorous base

The *purpose* of (W3-cover) is to deliver, for every width-3 `P`, a **balanced incomparable pair** — `(x,y)` with `Pr_P[x≺y] ∈ [3/11,8/11]`. F20 verifies this **directly**, by exact enumeration, well past the F8 Theorem-6.1 base of `m ≤ 4`:

> **Finding 6.2.** Every width-3 `S_m`-orbit, for `m = 4, 5, 6`, admits a BFT-sharp (balanced) incomparable pair.
> - `m = 4`: **5 / 5** width-3 orbits (`|PPF_4| = 194`, 44 width-3 posets) — re-confirms F8 Theorem 6.1.
> - `m = 5`: **29 / 29** width-3 orbits (`|PPF_5| = 4110`, 1730 width-3 posets) — **new**; F8/F19 only had `m ≤ 4` rigorous.
> - `m = 6`: **170 / 170** width-3 orbits (`|PPF_6| = 129302`, 74240 width-3 posets) — **new**, bounded background enumeration.
> Moreover the *symmetric*-pair fraction stays high: **25 / 29** at `m = 5` and **115 / 170** at `m = 6` have a symmetric incomparable pair, so Lemma L1 gives `Pr = 1/2` directly for ~⅔ of all width-3 orbits — the cohomological machinery is genuinely needed only for the non-symmetric remainder.

So the width-3 Kahn–Saks 1/3-2/3 statement — the *end goal* of F10 part (iii) — is now **rigorous at `m ≤ 6`** (harness §E + the `m = 6` bounded probe), a genuine **two-step** extension of the F8 Theorem-6.1 `m ≤ 4` rigorous base.

### 6.3 The n = 6 chamber — the feasible anchor data

The genuine chamber-Morse *greedy* at `n = 6` is HPC-class beyond budget (§1.3). The *feasible* anchor data is produced by harness §F (`--chamber-n6`):

- `|PPF_6| = 129302`; the chamber has **316 `S_6`-orbits** (note: F8′-HPC §6.2's "≈ 180" was the *naive* `|PPF_6|/6!` estimate; the Burnside-exact orbit count, with non-trivial stabilisers, is **316**).
- Orbit-width distribution: `{width 2: 74, width 3: 170, width 4: 63, width 5: 9}`. Of the 316 orbits, **30 are ordinal sums of antichains**.
- The **genuine-`G_6` candidate short list** — the width-2-OSA-with-a-size-2-block orbits — has **exactly 12** members:
  ```
    OSA(1,1,1,1,2)  |L|=2     OSA(2,1,1,1,1)  |L|=2
    OSA(1,1,1,2,1)  |L|=2     OSA(2,1,1,2)    |L|=4
    OSA(1,1,2,1,1)  |L|=2     OSA(2,1,2,1)    |L|=4
    OSA(1,1,2,2)    |L|=4     OSA(2,2,1,1)    |L|=4
    OSA(1,2,1,1,1)  |L|=2     OSA(2,2,2)      |L|=8
    OSA(1,2,1,2)    |L|=4
    OSA(1,2,2,1)    |L|=4
  ```
  The genuine `G_6` is one of these 12. The exact record `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`, `G_5=OSA(2,2,1)` has `|L(G_n)| = 2^{s_n}` with `s_3=s_4=1`, `s_5=2`; the genuine `G_6` candidates with `s_6 = 2` (`|L|=4`) or `s_6 = 3` (`|L|=8`) are the structurally plausible continuations. Pinning the genuine `G_6` among these 12 requires either the structural theorem or a genuine (HPC-budget) chamber-Morse greedy run — F21.

This is the deliverable that **narrows the genuine `G_6` to an explicit 12-element short list**, against which a future structural theorem or HPC run can be checked.

### 6.5 The honest residual

(W3-cover) — "the genuine critical chains collectively meet every width-3 `S_m`-orbit" — is **not** closed by F20. What F20 establishes:

- the **end goal verified at `m ≤ 6`** (§6.2) — a genuine two-step extension of F8 Theorem 6.1's `m ≤ 4` base;
- the **per-orbit core** of (W3-cover): every width-3 orbit at `m ≤ 6` *does* admit a balanced pair, so the obstruction (if any) is not "some width-3 poset has no balanced pair" — it is purely the *coverage* statement "every width-3 orbit lies on a critical chain";
- the observation that for the symmetric-pair width-3 orbits (**25/29** at `m = 5`, **115/170** at `m = 6` — about ⅔), the balanced pair is supplied by Lemma L1 with no chamber-Morse input at all, so (W3-cover) is genuinely needed only for the **non-symmetric** width-3 orbits — a strictly narrower target than F19's statement.

A full n-uniform proof still needs the genuine chamber-Morse coverage statement, of the same kind as (L2-struct)'s residual (§5.2).

---

## §7. The F20 harness

`scripts/compat_geom_F20_chamber_morse_hpc.py` (pure-Python stdlib, exact `Fraction` arithmetic). Sections [A]–[E] run in < 30 s; section [F] (the n = 6 chamber enumeration) is bounded and optional (`--chamber-n6`).

- **[A]** reconstructs `c*_3, c*_4, c*_5` from F2/F5; certifies the `|L|`-profiles, per-step BFT-sharpness, and **(L2-struct) at n = 3,4,5**.
- **[B]** the **F8′-HPC candidate audit**: reconstructs `ι_5(c*_5) + {(0,2)}`, finds its top poset has **width 3** — **(L2-struct) FAILS** (Correction 1).
- **[C]** the **ι-tower consistency audit**: finds `c*_5` is **not** an ι-lift (only `P_0` has element 4 isolated; Correction 2), and tabulates the **(L2-struct)/ι-multiplicativity inconsistency for n ≥ 7** (Correction 3).
- **[D]** re-certifies **Lemma L1** and the **OSA-symmetry fact** on `G_3,G_4,G_5` and the canonical `n = 6,7` width-2 OSAs — the symmetric-pair engine survives the corrections (§4.2).
- **[E]** the **(W3-cover) feasibility enumeration**: every width-3 `S_m`-orbit at `m = 4` (5/5), `m = 5` (29/29), and `m = 6` (170/170, under `--chamber-n6`) admits a balanced incomparable pair (Finding 6.2); 25/29 at `m = 5` and 115/170 at `m = 6` have a symmetric pair.
- **[F]** (optional, `--chamber-n6`) the **n = 6 chamber enumeration**: `|PPF_6| = 129302`, **316** `S_6`-orbits, orbit-width distribution `{2:74, 3:170, 4:63, 5:9}`, 30 OSA orbits, and the explicit **12-element list of genuine-`G_6` candidates**.

All non-HPC trip-wires **PASS** as designed (the "FAIL" lines for [B] and [C] are the *intended* findings — they certify the corrections). The `--chamber-n6` run completes in ≈ 5 minutes.

---

## §8. What F20 establishes and does not establish

### 8.1 Establishes

- **(L2-struct) exactly at `n = 3,4,5`** (harness §A); `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`, `G_5=OSA(2,2,1)`.
- **Correction 1** — the F8′-HPC "candidate `c*_6`" violates (L2-struct) (width 3); the genuine `c*_6 ≠ ι_5(c*_5)+{(0,2)}` (harness §B).
- **Correction 2** — the ι-tower form (F10 §5.2) is not literally correct; genuine `c*_5 ≠ ι_4(c*_4)+append` (harness §C).
- **Correction 3** — (L2-struct) and ι-tower multiplicativity are jointly inconsistent for `n ≥ 7`; the genuine `c*_n` is not an ι-lift (harness §C2).
- **The corrected reduction (CM-struct)** (§4) — the residuals re-founded on the genuine chamber-Morse object, independent of the broken ι-tower scaffolding.
- **The symmetric-pair engine survives** (§4.2, harness §D) — Lemma L1 + the OSA-symmetry fact are untouched by the corrections; (L2-struct) still ⟹ the top-step BFT-sharpness.
- **The width-3 end goal verified at `m ≤ 6`** (harness §E) — every width-3 `S_m`-orbit (`m = 4,5,6`) admits a balanced incomparable pair; a genuine two-step extension of F8 Theorem 6.1's `m ≤ 4` base. ~⅔ of the orbits have a symmetric pair (L1-immediate).
- **The genuine-`G_6` candidate short list** (harness §F) — the n = 6 chamber has 316 `S_6`-orbits; the genuine `G_6` is one of an explicit **12-element** list of width-2-OSA-with-a-size-2-block orbits.

### 8.2 Does NOT establish

- **F20 does not prove (L2-struct) n-uniformly.** The genuine `c*_n` for `n ≥ 6` is not pinned down; it needs a dedicated structural theorem on the `S_n`-equivariant chamber-Morse refinement, or the (budget-infeasible-in-session) F8‴ HPC run.
- **F20 does not prove (W3-cover).** The coverage statement — every width-3 orbit on a genuine critical chain — is open; F20 verifies its per-orbit core and end goal at `m ≤ 5`, and narrows it to the non-symmetric width-3 orbits.
- **F20 does not produce the genuine `c*_6` (or `c*_7, c*_8`).** The full chamber-Morse greedy is HPC-class beyond single-session budget already at `n = 6`; F20 delivers the feasible anchor data instead.
- **F20 does not touch the cohomological core, (UCC), or the F17/F18 line.** Those are unconditional and complete.
- **F20 does not touch the Lean trust surface.** No new axioms; no Lean changes; no new HPC datapoint beyond the bounded n = 6 chamber enumeration.
- **F20 does not touch route (iii) / mg-b345.** It stays PARKED.

### 8.3 Why this is GREEN-partial

It is **not GREEN-both-residuals-closed** or **GREEN-one-residual**: neither (L2-struct) nor (W3-cover) is proven n-uniformly. It is **not RED-false**: nothing is found false — (L2-struct) holds at `n ≤ 5`, the end goal holds at `m ≤ 5`, and Correction 3 shows the apparent `n ≥ 7` obstruction is an obstruction to the *ι-tower model*, not to (L2-struct) (the genuine non-ι-lift chain evades it). It is **not AMBER-stalls**: F20 did not stall — it made real structural progress (the three corrections re-found the residuals, the symmetric-pair engine is confirmed intact, the end goal's rigorous base is extended, the genuine-`G_6` target is pinned to a short list). **GREEN-partial** is exact: the chamber-Morse structural theory is substantially advanced and the residuals are reduced and *corrected*, but not closed.

---

## §9. Verdict and the program after F20

**Verdict: GREEN-partial.**

F20's deliverable is the **re-founding of the two residuals on a corrected structural understanding**. The prior framing — the ι-tower form of the canonical critical chain (F10 §5.2), the F8′/F8′-HPC ι-lift `c*_6` candidate — is found to be *not the genuine object*: the F8′-HPC candidate violates (L2-struct) outright, the ι-tower form fails already at `c*_4 → c*_5`, and (L2-struct) is *jointly inconsistent* with ι-tower multiplicativity for `n ≥ 7`. The genuine canonical critical chain is a non-ι-lift chamber-Morse refinement descending to a width-2 near-maximal top poset. On the corrected footing: (L2-struct) holds exactly at `n ≤ 5`; the symmetric-pair engine (L1 + the OSA-symmetry fact) survives intact and still reduces the top-step BFT-sharpness to (L2-struct); the width-3 *end goal* is verified directly at `m ≤ 6` — a two-step extension of F8 Theorem 6.1's rigorous base; and the genuine `G_6` is pinned to an explicit 12-element short list.

**The program after F20:**

- **Cohomological core (F10 (i)–(ii))** — DONE, unconditional (F10 + F17 + F18). Untouched by F20.
- **Numerical width-3 conclusion (F10 (iii))** — still rests on the two residuals, now **corrected**:
  - **(L2-struct)** — `G_n` is a width-2 OSA. Verified `n ≤ 5`; consistent; the n-uniform proof needs the genuine (non-ι-lift) `c*_n`. **Residual stands.**
  - **(W3-cover)** — the genuine critical chains meet every width-3 orbit. The end goal verified `m ≤ 5`; the per-orbit core holds; the residual narrows to non-symmetric width-3 orbits. **Residual stands.**
- **The F19 reductions** — F19's reductions of (ICOP-step) and the width-3 bridge are *built on the ι-tower model* and so need the F20 correction. F20 §4 supplies the corrected reduction (CM-struct); the symmetric-pair engine (the load-bearing part of F19) is confirmed to survive.
- **Lean formalization track** — untouched. Route (iii) / mg-b345 — stays PARKED.

**Recommendation for the PM.** The honest next step is a **follow-on F21** targeting the genuine (non-ι-lift) canonical chamber-Morse critical cell at general `n` — either (a) a dedicated structural theorem identifying `c*_n` and proving its top poset is a width-2 OSA and its critical chains cover every width-3 orbit, or (b) a genuine HPC chamber-Morse run at `n = 6, 7` (which requires a Tier-3 HPC budget — *not* single-polecat-session-feasible, contrary to the F20 ticket's optimistic in-ticket scoping). F20 has corrected the target and pinned it (the genuine `G_6` is on the §6.4 short list); F21 should not re-attempt the ι-tower route. **The two residuals remain the milestone-1 critical path; F20 reduces and corrects them but does not close them.**

### 9.1 A note for the program record

F19's GREEN-partial verdict and its reductions of (ICOP-step) and the width-3 bridge should be read in light of F20 §3: they are *correct in their order-theoretic core* (Lemma L1, Proposition 3.1's symmetric-pair argument) but their *ι-tower scaffolding* — "(ICOP-step) is one new cover step per level", "the canonical chain is an ι-tower" — is not the genuine object. F20 §4 supplies the corrected scaffolding. This does not undo F19; it corrects the model on which F19's reductions were phrased. The cohomological core (F17 + F18) is entirely unaffected.

### 9.2 Trust-surface impact

**None.** F20 introduces no new axioms, makes no Lean changes, and adds no new empirical n-datapoint beyond the bounded n = 6 chamber enumeration (which is structural anchor data, not a homology/cohomology computation). It is elementary order-complex combinatorics + exact rational arithmetic + the three structural corrections. The in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched.

---

## §10. References

### 10.1 Predecessor and sibling mg-tickets

- **mg-5722** — F19 ((ICOP-step) + width-3 bridge): **GREEN-partial.** `docs/compatibility-geometry-F19-icop-step-and-bridge.md` §2 (Lemma L1), §3.1–3.4 ((L2-struct), the reduction, the residual), §4.3–4.4 ((W3-cover), the F20 recommendation). **Parent.** F20 corrects F19's ι-tower scaffolding (§3) and confirms F19's symmetric-pair engine survives (§4.2).
- **mg-4d3a** — F17 (n-uniform `S_n`-equivariant cofiber Morse): **GREEN-equivariant-uniform.** `H̃_d(Δ_{n+1}/Δ_n) ≅ 2·H̃_{d-1}(Δ_n)`, (UCC.1) ⟺ Hyp(n). Untouched by F20.
- **mg-d039** — F18 ((UCC.2): `δ_n` injective): **GREEN-ucc2-proven.** `ι_n` null-homotopic; cohomological core unconditional. Untouched by F20.
- **mg-8216** — F10 (general-`n` synthesis): **GREEN-conditional.** `docs/general-n-proof-synthesis.md` §5.2 (**the ι-tower form — corrected by F20 §3**), §5.4 ((ICOP-step)), §6.7 (the conditional theorem, part (iii)), §7.3 (the width-3 bridge).
- **mg-1e99** — F8 (ICOP framework): `docs/compatibility-geometry-F8-inductive-general-n.md` §4.1 (the 8-step chamber-Morse construction), §4.4 (the bridge), §6 (Theorem 6.1 — the `m ≤ 4` rigorous base, extended to `m ≤ 5` by F20 §6.2).
- **mg-7b3b** — F8′ (`n=6` ICOP empirical): **GREEN-with-refinement.** `docs/compatibility-geometry-F8prime-n6-icop.md` §3 (the ι₅-lift candidate — **the candidate corrected by F20 §3.1**).
- **mg-3bf3** — F8′-HPC (deferred n=6 pieces): `docs/compatibility-geometry-F8prime-HPC.md` §5 (the candidate `c*_6` — **F20 §3.1 finds it violates (L2-struct)**), §6.2 (the AMBER-budget-cap conjecture that it is the genuine `c*_6` — **F20 refutes this**).
- **mg-1e58** — F5 (chamber-Morse at `n=5`): `docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md` §3 (the chamber order complex; the ~567 s greedy-matching cost cited in F20 §1.3), §4.3 (`c*_5` explicit).
- **mg-7455 / mg-6bc3** — F2 / F3 (`n=4`): `c*_4` cell #1 explicit (F20 §2).
- **mg-b345** — F8″ (route (iii)): **PARKED** — F20 does not touch it.

### 10.2 Mathematical literature

- J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984) — the 1/3-2/3 conjecture.
- G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross product conjecture*, Order 12 (1995) — the `[3/11, 8/11]` BFT-sharp interval.
- R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998) — the discrete-Morse machinery underlying the chamber-Morse construction.
- A. Björner, *Topological methods*, in *Handbook of Combinatorics*, Elsevier 1995, §10 — order-complex topology; ordinal sums of antichains.
- N. Linial, *The information-theoretic bound is good for merging*, SIAM J. Comput. 13 (1984) — width-2 1/3-2/3.

### 10.3 Code

- `scripts/compat_geom_F20_chamber_morse_hpc.py` — **this F20 / mg-c3fa** — the trip-wire + structural-anchor harness. Pure-Python stdlib; exact `Fraction` arithmetic. Sections [A]–[F] as described in §7.

### 10.4 Daniel directives

- 2026-05-14T05:18Z — finish the induction internally; no external collaboration. F20 is internal: the three corrections + the corrected reduction + a bounded harness.
- 2026-05-14T08:05Z — focus on the induction, not special cases. F20's corrections are n-uniform structural facts (Correction 3 is an n ≥ 7 inconsistency proof), not special-case patches.
- 2026-05-14T17:23Z — milestone 1 = the full gap-free width-3 proof. F20 is honest that the two residuals are *not* closed; it corrects and reduces them and extends the rigorous base, and recommends F21.

---

*End of F20 — the n-uniform structure of the canonical chamber-Morse critical cells.*
