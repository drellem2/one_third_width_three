# OneThird — AP-0 Family A (hook-length / skew-shape) viability probe

*Phase-0 viability probe of the leading algebraic-program candidate, **Family A**
(hook-length / skew-shape posets / Naruse formula). Work item **mg-98a6**.*

*Inputs: [`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md)
@ 67dc3df §5 (and §1, §3A, §4, §8); canonical
[`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md)
@ 6e28060.*

*Reproducible script:
[`scripts/onethird_ap0_familyA_skew_probe.py`](../scripts/onethird_ap0_familyA_skew_probe.py)
(pure Python / stdlib; runs in seconds). Re-run with
`python3 scripts/onethird_ap0_familyA_skew_probe.py [--gradient] [--montecarlo]`.*

---

## 0. Vision alignment & non-goals

This ticket realises **vision-parts 3 and 4** (roadmap §0, anti-drift §4): a
parameter-space exploration of one shortlisted family, plus a bounded
counterexample-search-machinery test at small `n`. Vision-parts 1–2 are realised
by the family choice (skew shapes → width-3 posets) and the closed-form-`Q`
claim (Naruse).

Non-goals honoured (roadmap §8): **no** Cheeger / cut-and-window re-litigation
(§8.1); **no** counterexample claim from AP-0 alone (§8.2); **no** Lean, LaTeX,
or `main.tex` (§8.3); **width-3 only** (§8.5 / §8 width restriction); **Monte-Carlo
is never the source of truth** (§8.5) — it appears only as a spot-check.

## 1. Object, poset, and the constant `Q`

A skew Young diagram `λ/μ` has cells `(i,j)` with `μ_i < j ≤ λ_i`, ordered by the
product order `(i,j) ≤ (i',j') ⇔ i≤i' ∧ j≤j'`. Linear extensions of this poset
are exactly the **standard Young tableaux** of shape `λ/μ`. An antichain holds at
most one cell per row, so **3-row shapes have width ≤ 3** — the regime of the
width-3 1/3–2/3 program. We engineer the conjugate so width is *exactly* 3.

The balance constant is
`Q(P) = max over incomparable pairs (x,y) of min(Pr[x<y], Pr[y<x])`
under the uniform distribution on linear extensions. The 1/3–2/3 conjecture
asserts `Q(P) ≥ 1/3` for every non-chain finite poset; small `Q` lives at
**near-chain** posets (every incomparable pair strongly biased).

## 2. Methods and the acceptance gate

Three independent counting engines are implemented and cross-checked:

| ID | Method | Role |
|----|--------|------|
| **M1** | Brute-force enumeration of every linear extension | ground truth for `e` and every `Pr[x<y]` |
| **M2** | Order-ideal dynamic program (counts linear extensions of `P` and of every "force `x<y`" augmented poset) | independent kernel + `Q` path |
| **M3** | **Naruse** hook-length formula (sum over excited diagrams) | closed-form `e`; the engine an AP-1 sweep would run |
| M4 | Monte-Carlo (exact-count-weighted uniform topological sort) | **spot-check only, never truth** (§8.5) |

**Acceptance gate (roadmap §5.3a):** `Q` is reported only when **M1 and M2 agree
exactly**, and `e` is additionally confirmed by **M3**. In this probe **every
shape passed all cross-checks** — `e` agrees across Naruse = DP = brute-force,
`Q` agrees across brute-force = DP, the bounded-sweep DP minimum matches the
fully-verified witness, and the Monte-Carlo spot-checks land within sampling
error (e.g. `0.3862` vs exact `27/70 = 0.385714`). The DP path is thereby
validated, so the sweep numbers it produces are trustworthy.

## 3. Sanity results (roadmap §5.1)

The three required straight (2-row) shapes; all are width-2 controls confirming
the pipeline and the symmetric/extremal base cases. `e` by Naruse = DP = brute.

| Shape `λ` | `n` | `e` | incomparable pairs | `Q` | note |
|-----------|-----|-----|--------------------|-----|------|
| `(2,1)`   | 3   | 2   | 1 (symmetric)      | **1/2** | lone pair `(1,2)∥(2,1)` is symmetric ⇒ `Pr=1/2` |
| `(2,2)`   | 4   | 2   | 1 (symmetric)      | **1/2** | symmetric base case |
| `(3,1)`   | 4   | 3   | 2                  | **1/3** | hits the conjecture bound exactly: `Pr=2/3,1/3` |

`λ=(3,1)` lands **exactly on `Q = 1/3`** — the classical tight case — a good
landmark that the kernel is correct. Closed-form-applicability = `1/1`, `1/1`,
`2/2` (straight shapes: every forced pair stays a skew shape).

## 4. Real probe — near-chain 3-row skew shapes, `n ∈ [7,9]`

### 4a. One explicitly engineered near-chain ribbon (`n=7`)

`λ=(5,3,2)`, `μ=(2,1,0)` — a thin staircase ribbon winding through 3 rows
(rows overlap one column each), width exactly 3, `e=155`. **`Q = 74/155 ≈
0.4774`** (worst pair `(1,5)∥(3,2)`). Two-method agreement holds.

### 4b. Bounded sweep over **all** width-3 3-row skew shapes at each `n`

Rather than rely on a single hand-picked shape, we sweep **every** width-3 3-row
skew shape at each `n` (translation-normalised `μ_3=0`, all three rows non-empty,
`λ_1 ≤ 12`). The reported minimum `Q` is **verified stable** for `λ_1 ∈
{9,12,15}` — the bound is not hiding lower values. (No silent caps; the full
unbounded sweep is AP-1's job, §6.)

| `n` | shapes scanned | width-3 | **min `Q`** | min-`Q` witness `λ/μ` | dist to 1/3 |
|-----|----------------|---------|-------------|------------------------|-------------|
| 7   | 671            | 655     | **2/5 = 0.4000**   | `(4,3,3)/(3,0,0)` | +0.0667 |
| 8   | 810            | 796     | **27/70 = 0.38571**| `(4,4,2)/(2,0,0)` | +0.0524 |
| 9   | 929            | 917     | **2/5 = 0.4000**   | `(6,3,3)/(3,0,0)` | +0.0667 |

**Overall sweep minimum (n ∈ [7,9]) = `27/70 ≈ 0.3857`.** Each witness was
re-verified by the full M1/M2/M3 gate (e.g. the `n=8` witness has `e=140`,
worst pair `(1,4)∥(3,1)` at `27/70`).

**Surprising structural finding (honest):** the small-`Q` minimisers are *not*
the thin near-chain ribbons one might expect, but **stacked near-equal-row**
shapes — e.g. `(4,3,3)/(3,0,0)` is two full 3-cell rows plus a single top cell,
`(6,3,3)/(3,0,0)` is three offset 3-cell rows. The thin engineered ribbon (§4a)
gives a *higher* `Q` (0.477) than these.

### 4c. Local gradient (roadmap §5.3b)

Every single-cell deformation (grow a `λ` row, or grow `μ`) of each min-`Q`
witness **raises or holds `Q`** — the witnesses are local minima within the
family at these `n`. (For the higher-`Q` engineered ribbon, `grow μ row 2`
lowers `Q` from 0.477 → 0.422, pointing toward the stacked-row minimisers.) No
local deformation in the probe drives `Q` below 0.3857.

## 5. Closed-form-applicability fraction (mayor W1 watch-item)

For each incomparable pair, the kernel numerator `#{ext : x<y} = e(P + (x<y))` is
a closed-form Naruse count **iff** the augmented poset stays a skew shape, else it
falls through to the width-3 DP (roadmap §3A). We measure this by attempting to
realise each augmented poset as a skew-shape cell-poset (backtracking coordinate
embedding), **self-validated** by requiring `Naruse(realised shape) = DP count`
— so any pair counted as closed-form-applicable is verified, not asserted.

| Shape | closed-form-applicable pairs | fraction |
|-------|------------------------------|----------|
| sanity `(2,1)`, `(2,2)`, `(3,1)` | 1/1, 1/1, 2/2 | **1.000** |
| engineered ribbon `(5,3,2)/(2,1,0)` (n=7) | 1/14 | **0.071** |
| min-`Q` witness `(4,3,3)/(3,0,0)` (n=7) | 2/9 | **0.222** |
| min-`Q` witness `(4,4,2)/(2,0,0)` (n=8) | 0/14 | **0.000** |
| min-`Q` witness `(6,3,3)/(3,0,0)` (n=9) | 2/21 | **0.095** |

**Budget signal for AP-1.** The *count* `e` is **always** closed-form (Naruse).
But the **kernel-pair numerators are overwhelmingly DP-driven**: across the
width-3 `n∈[7,9]` shapes only **0–22%** of forced pairs stay skew shapes (mostly
near 0–10%). So a `Q`-sweep over Family A is **closed-form for `e`, DP-bound for
the kernel**. AP-1 should budget the kernel as `O(n⁴)`-DP-per-pair, not as a
free closed-form evaluation. (The clean closed-form pairs concentrate at the
geometric extremes — e.g. forcing the top-right vs bottom-left cell — where the
augmented poset is again a genuine skew diagram.)

## 6. Binary AP-0 verdict (roadmap §5 decision rule)

The decision rule has two branches:
- **descends toward 1/3** (some shape within striking distance, or a descending
  trend) → file **AP-1** (analytic parameter sweep over Family A skew shapes);
- **floors structurally above 1/3** (e.g. `Q=1/2` pinned by symmetry across
  reachable shapes) → pivot, file **AP-3** (Family B asymmetric gadgets).

**Observed.**
- Family A is **NOT symmetry-floored.** Width-3 skew shapes readily achieve
  `Q < 1/2` (down to `27/70 ≈ 0.386`); the `Q=1/2` symmetry pin is broken on the
  vast majority of shapes. **⇒ the AP-3 pivot branch does NOT apply.**
- But **no shape in the bounded `n∈[7,9]` probe reached striking distance of
  1/3** (closest gap `+0.0524`, just above the pre-declared `0.05` bar), and the
  per-`n` minimum is **flat/non-monotone** (0.400, 0.386, 0.400) — no clear
  descent yet. The minimisers are local minima under single-cell deformation.

A point-probe at `n∈[7,9]` **cannot** settle `inf Q` as `n→∞` — that is exactly
the analytic question AP-1 exists to answer (roadmap §6: the closed-form `e`
permits an analytic `inf Q` along a parameter ray that the per-instance DP
cannot reach).

### Verdict: **GREEN — pipeline de-risked; Family A is a LIVE candidate, not floored.**

> Family A clears Phase-0: the algebra→`Q` pipeline runs end-to-end, two
> independent methods agree exactly on every shape, and a reusable tested kernel
> `shape → (e, {Pr[x<y]}, Q)` exists. The family is **not** pinned at `Q=1/2`
> (rules out the AP-3 symmetry-pivot), reaches into the **low 0.39s** at small
> `n`, but shows **no confirmed monotone descent to 1/3** in this range.

### Recommended next ticket: **AP-1** (analytic parameter-sweep over Family A).

The sweep should (i) push the bounded grid to larger `n` and unbounded `λ_1`,
(ii) use Naruse closed-form for `e` but **budget the kernel as DP-per-pair** (§5
finding), and (iii) attempt the analytic `inf Q` along the stacked-near-equal-row
ray that minimised `Q` here, to decide whether `Q` continues toward 1/3 or
plateaus above it. **No counterexample is claimed or expected** (§8.2): the
likely outcome is a bounded null (`inf Q ≥ 1/3` over Family A), which is itself
valuable sharpness data. Should any AP-1 instance show `Q ≤ 1/3`, §8.2 mandates
brute-force re-verification **and** independent reimplementation before any claim
— AP-0 already runs three agreeing methods, but the bar is independent code.

---

## Appendix — reproduction

```
python3 scripts/onethird_ap0_familyA_skew_probe.py              # sanity + real probe + verdict
python3 scripts/onethird_ap0_familyA_skew_probe.py --gradient   # + local-gradient deformation probe
python3 scripts/onethird_ap0_familyA_skew_probe.py --montecarlo # + MC spot-check (sanity only)
```

The script asserts every cross-check inline (Naruse = DP = brute for `e`;
brute = DP for `Q`; sweep DP = verified witness), so a clean exit *is* the
two-method-agreement gate passing.
