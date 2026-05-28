# OneThird — AP-1a Family A small-k snapshot (k = 1, 2, 3)

*First descent-vs-plateau snapshot along the data-earned Family A ray. Work item
**mg-746f**, repackaged from AP-1 (AP-1a + AP-1b split per the mayor's 500k-wedge
guard).*

*Inputs: [`OneThird-AP-0-FamilyA-Viability-Probe.md`](OneThird-AP-0-FamilyA-Viability-Probe.md)
(AP-0 verdict + structural finding, mg-98a6);
[`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md)
§§5, 6, 8; canonical
[`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md)
(vision-parts 3 + 4).*

*Reproducible script:
[`scripts/onethird_ap1a_familyA_smallk_snapshot.py`](../scripts/onethird_ap1a_familyA_smallk_snapshot.py)
— reuses the AP-0 engine verbatim. Pure Python / stdlib; full run ≈ 4 min
(`--quick` for a fast smoke run). Re-run with
`python3 scripts/onethird_ap1a_familyA_smallk_snapshot.py`.*

---

## 0. Vision alignment & non-goals

This ticket realises **vision-part 3** (parameter-space exploration along the
data-earned ray, at small `k`) and delivers the first **vision-part 4** signal
(descent-vs-plateau snapshot). It consumes the AP-0 GREEN verdict's carry-forwards
verbatim and stays strictly inside the AP-1a bounded snapshot.

Non-goals honoured (roadmap §8): **no** Cheeger / cut-and-window re-litigation
(§8.1); **no** counterexample claim (§8.2 — and none arises: every `Q` is well
above `1/3`); **no** Lean, LaTeX, or `main.tex` (§8.3); **width-3 only**; **Monte-Carlo
is never the source of truth** (§8.5). Out of scope (deferred to AP-1b): `k > 3`,
adjacent rays, asymptotic fit, and the `lim_{k→∞} Q` estimate.

## 1. The ray and the methods

AP-0's structural finding: the small-`Q` minimisers of width-3 3-row skew shapes
are **not** thin near-chain ribbons (that hypothesis was empirically falsified)
but **stacked near-equal-row** shapes. The carried-forward "main ray" generalises
the AP-0 `n=7` argmin `(4,3,3)/(3,0,0)` as

> `λ = (3k+1, 3k, 3k)`,  `μ = (3k, 0, 0)`,  `n = |λ/μ| = 6k+1`.

Geometrically: a **single top cell** at `(row 1, column 3k+1)` stacked above
**two full rows of length `3k`** (rows 2 and 3, columns `1..3k`). The three
requested shapes:

| `k` | `λ/μ` | `n` |
|-----|-------|-----|
| 1 | `(4,3,3)/(3,0,0)`  | 7  |
| 2 | `(7,6,6)/(6,0,0)`  | 13 |
| 3 | `(10,9,9)/(9,0,0)` | 19 |

`Q(P) = max` over incomparable pairs `(x,y)` of `min(Pr[x<y], Pr[y<x])` under the
uniform distribution on linear extensions; the conjecture asserts `Q ≥ 1/3`.

**Two-method gate (roadmap §5.3a).** `Q` is reported only when **M1 brute-force
enumeration == M2 order-ideal DP**, with the count `e` additionally cross-checked
by **M3 Naruse** (excited-diagram hook-length formula). Brute force is feasible at
**all three** `k` here (`e ≤ 92378`), so the full M1/M2/M3 gate runs at every `k`.
The script asserts every cross-check inline, so a clean run *is* the gate passing.

## 2. Q(k) on the ray — the headline numbers

All three pass the full gate (`brute == DP`, `e == Naruse`):

| `k` | `λ/μ` | `n` | `e` | **`Q(k)`** | `≈` | dist to `1/3` | worst (argmax-min) pair(s) |
|-----|-------|-----|-----|-----------|-----|---------------|----------------------------|
| 1 | `(4,3,3)/(3,0,0)`  | 7  | 35    | **`2/5`**       | 0.400000 | +0.0667 | `(1,4)∥(2,3)`, `(1,4)∥(3,1)`, `(2,2)∥(3,1)`, `(2,3)∥(3,2)` |
| 2 | `(7,6,6)/(6,0,0)`  | 13 | 1716  | **`31/66`**     | 0.469697 | +0.1364 | `(2,4)∥(3,2)`, `(2,5)∥(3,3)` |
| 3 | `(10,9,9)/(9,0,0)` | 19 | 92378 | **`1673/3553`** | 0.470870 | +0.1376 | `(1,10)∥(2,6)`, `(1,10)∥(3,4)` |

(`e = 35, 1716, 92378` follow the clean closed form `e = C(6k+1, 3k)` =
`C(7,3), C(13,6), C(19,9)`; the count is always closed-form by Naruse.)

## 3. Closed-form-applicability fraction (mayor W1 watch-item)

For each forced pair, the kernel numerator `#{ext : x<y} = e(P+(x<y))` is a
closed-form Naruse count **iff** the augmented poset stays a genuine skew shape;
otherwise it falls through to the width-3 DP. Measured by attempting a
backtracking skew-shape realisation, **self-validated** by requiring
`Naruse(realised) = DP count`.

| `k` | closed-form pairs | total pairs | fraction |
|-----|-------------------|-------------|----------|
| 1 | 2 | 9  | **`2/9` ≈ 0.222** |
| 2 | 2 | 27 | **`2/27` ≈ 0.074** |
| 3 | 2 | 54 | **`2/54` ≈ 0.037** |

**Finding — the closed-form count is a constant `2`, not a constant fraction.**
Exactly two pairs stay skew at every `k` (the geometric extremes: the top cell
forced against the two opposite corner cells of the double row). As `k` grows the
total pair count grows `~3k(3k±1)` while the closed-form count stays pinned at 2,
so the fraction **decays to 0** (`0.222 → 0.074 → 0.037`). This sharpens the AP-0
budget signal: along this ray the `Q`-kernel is **essentially fully DP-bound** —
AP-1b must budget the kernel as `O(n⁴)`-DP-per-pair (the count `e` is the only
free closed-form quantity). Consistent with AP-0's measured 0–22% band.

## 4. Stability check — is the ray the minimiser? (No.)

A bounded sweep over **all** width-3 3-row skew shapes at each `n`
(translation-normalised `μ_3 = 0`, all rows non-empty, `λ_1 ≤ 12`), comparing the
global sweep minimum against the ray `Q`:

| `k` | `n` | width-3 shapes | sweep min `Q` | sweep argmin | ray `Q` | ray is argmin? |
|-----|-----|----------------|---------------|--------------|---------|----------------|
| 1 | 7  | 655  | `2/5` ≈ 0.4000     | `(4,3,3)/(3,0,0)` **+ 143 ties** | `2/5` ≈ 0.4000 | **yes** (1 of 144) |
| 2 | 13 | 1060 | `3/7` ≈ 0.4286     | `(5,5,4)/(1,0,0)` (unique) | `31/66` ≈ 0.4697 | **no** |
| 3 | 19 | 626  | `943/2074` ≈ 0.4547 | `(12,7,4)/(3,1,0)`, `(12,11,9)/(8,5,0)` | `1673/3553` ≈ 0.4709 | **no** |

**The ray is the sweep argmin only at `k=1`** — and there it is one of **144 tied**
shapes (`Q=2/5` is a heavily-degenerate floor at `n=7`, not a distinguished
witness). At `k=2` and `k=3` a strictly-lower-`Q` width-3 shape exists **off the
ray**: `(5,5,4)/(1,0,0)` at `n=13` beats the ray by `3/7` vs `31/66`, and the
`n=19` sweep min `943/2074` beats the ray's `1673/3553`.

So the answer to the ticket's stability question — *"confirm the sweep argmin is
stable, no hidden lower-Q nearby"* — is **negative**: the argmin is **not** stable
along this ray, and there **is** a hidden lower-`Q` shape at every `k > 1`. The
`(3k+1,3k,3k)/(3k,0,0)` ray tracks an AP-0 `n=7` tie, not a persistent minimiser.

**Sweep caveat (honest).** At `n=7` and `n=19` an argmin sits at `λ_1 = 12` (the
cap), so the true unbounded sweep minimum may be **lower** still — i.e. the
`0.4286 / 0.4547` figures are upper bounds on the real per-`n` minimum. Pushing
`λ_1` is an AP-1b job (§6). It does not affect the ray verdict, which only gets
*more* decisively "not the minimiser" if the off-ray minima drop further.

## 5. Descent-vs-plateau snapshot — the verdict

```
Q(1) = 2/5       ≈ 0.400000     dist to 1/3 = +0.067
Q(2) = 31/66     ≈ 0.469697     dist to 1/3 = +0.136
Q(3) = 1673/3553 ≈ 0.470870     dist to 1/3 = +0.138
step deltas:        +0.069697,    +0.001173
```

**Shape of the small-k sequence: RISES then PLATEAUS — non-monotone, and moving
*away* from `1/3`.** The big jump `k=1→2` (+0.070) is followed by a near-flat
`k=2→3` step (+0.0012); the sequence is settling near **`Q ≈ 0.47`**, i.e.
toward the symmetric `1/2` end, not toward `1/3`. The distance to `1/3` **grows**
(+0.067 → +0.138). Three points cannot prove asymptotics — we only name the
small-`k` shape — but on this ray the descent the ray was meant to probe **does
not happen**.

Cross-check against the **per-`n` sweep minimum** (the best any width-3 3-row
shape achieves), which tells the same story from the other side: `0.4000`
(`n=7`) → `0.4286` (`n=13`) → `0.4547` (`n=19`) also **rises** with `n` over this
range. The lowest `Q` seen anywhere in Family A small-`n` probing remains AP-0's
**`27/70 ≈ 0.386` at `n=8`**; nothing in AP-1a goes below it.

## 6. GUARD and recommended next ticket

**GUARD (roadmap §8.2, anti-Cheeger).** No `Q ≤ 1/3` is observed anywhere: the
ray minimum is `2/5 = 0.400`, the off-ray sweep minima are `0.4286 / 0.4547`, and
the all-time Family A record is `0.386` (AP-0, `n=8`) — all comfortably above
`1/3`. **The independent-reimplementation trigger does not fire.** (If it ever
did, three-engine agreement here would NOT satisfy §8.2: a separate codebase plus
brute force would be mandatory before any claim.)

### Verdict: **GREEN — snapshot delivered; the specified ray is a PLATEAU (falsified as a descent ray).**

> AP-1a clears its bounded scope: `Q(1)=2/5`, `Q(2)=31/66`, `Q(3)=1673/3553`
> computed under the full two-method gate at every `k`; the closed-form fraction
> measured (`2/9, 2/27, 2/54` — a constant-2, fraction→0 decay); the stability
> check run. The data-earned `(3k+1,3k,3k)/(3k,0,0)` ray **rises then plateaus
> near `Q ≈ 0.47`** and is the sweep minimiser **only at `k=1`** (where it is one
> of 144 ties). This is a clean, honest **null on the ray**: extending the AP-0
> `n=7` argmin via `k` does *not* trace a descent toward `1/3`.

### Recommended next ticket: **AP-1b — re-derive the minimising ray; do NOT extend this one.**

The descent-vs-plateau rule said: *AP-1b if descent or non-monotone-with-room;
STOP-and-report if `Q ≤ 1/3`.* We are in the **non-monotone-with-room** branch
(no `Q ≤ 1/3`), but with a sharp redirection from the data:

1. **Abandon the `(3k+1,3k,3k)/(3k,0,0)` ray as a descent probe** — it plateaus
   above `1/3` (this ticket's main finding). Extending it to `k > 3` is wasted
   compute.
2. **Re-derive the minimising ray from the off-ray argmins.** The actual small-`n`
   minimisers are *not* on this ray: `n=8 → (4,4,2)/(2,0,0)` (AP-0 record 0.386),
   `n=13 → (5,5,4)/(1,0,0)` (0.4286). These look like a **small-`μ`, near-equal-`λ`
   family** (`μ` ≈ a single small overhang, not a full first row) — a different
   parametrisation than the ticket's `μ=(3k,0,0)`. AP-1b should fit the ray
   through these minimisers and sweep *that*.
3. **Raise `λ_1` beyond 12.** The `n=7` and `n=19` sweep argmins sit at the
   `λ_1 = 12` cap, so the true per-`n` minimum is an *upper bound*; AP-1b's
   unbounded sweep (roadmap §6) may pull it lower.
4. Only on the correctly-derived ray does the asymptotic `inf_k Q` question
   (roadmap §6) become meaningful; pursue the analytic fit there, with the
   kernel budgeted as DP-per-pair (§3).

**No counterexample is claimed or expected** (§8.2). The honest reading of AP-1a:
Family A remains a LIVE, not-floored candidate (it reaches `Q < 1/2` freely), but
the *specific ray AP-0 handed forward* is the wrong one — it ascends. The value
delivered is exactly this falsification plus the corrected direction for AP-1b.

---

## Appendix — reproduction

```
python3 scripts/onethird_ap1a_familyA_smallk_snapshot.py           # full gate + stability sweep + verdict (~4 min)
python3 scripts/onethird_ap1a_familyA_smallk_snapshot.py --quick   # skip k=3 brute + n=13/n=19 sweeps (fast smoke)
```

The script reuses the AP-0 engine
(`scripts/onethird_ap0_familyA_skew_probe.py`) verbatim — `skew_cells`,
`build_poset`, `count_linear_extensions_dp`, `naruse_count`, `Q_via_dp`,
`probe_shape`, `sweep_min_Q` — and asserts every cross-check inline (Naruse = DP =
brute for `e`; brute = DP for `Q`; sweep DP = verified witness), so a clean exit
*is* the two-method-agreement gate passing.
