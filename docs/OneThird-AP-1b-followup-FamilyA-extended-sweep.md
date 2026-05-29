# OneThird — AP-1b′ Family A extended sweep (raise λ₁ cap, generalise the corrected minimiser)

*Follow-up to AP-1a (mg-746f), which falsified the `(3k+1,3k,3k)/(3k,0,0)` ray as
a descent ray and handed forward three corrected minimum candidates plus a
**hypothesis** for the real minimiser family. Work item **mg-106e**.*

*Inputs: [`OneThird-AP-1a-FamilyA-SmallK-Snapshot.md`](OneThird-AP-1a-FamilyA-SmallK-Snapshot.md)
(AP-1a verdict + stability sweep + cap caveat);
[`OneThird-AP-0-FamilyA-Viability-Probe.md`](OneThird-AP-0-FamilyA-Viability-Probe.md)
(AP-0 verdict + structural finding);
[`OneThird-Algebraic-Program-Roadmap.md`](OneThird-Algebraic-Program-Roadmap.md)
§§5, 6, 8; canonical
[`OneThird-Algebraic-Program-Vision.md`](OneThird-Algebraic-Program-Vision.md)
(vision-parts 3 + 4).*

*Reproducible script:
[`scripts/onethird_ap1b_followup_familyA_extended_sweep.py`](../scripts/onethird_ap1b_followup_familyA_extended_sweep.py)
— reuses the AP-0 engine verbatim (`skew_cells`, `build_poset`, `poset_width`,
`count_linear_extensions_dp`, `augment_relation`, `naruse_count`,
`try_realise_as_skew_shape`, `Q_via_dp`, `probe_shape`). Pure Python / stdlib +
`multiprocessing`. Full run ≈ 15–20 min on a 10-core laptop; `--quick` ≈ 5 min.
Re-run with `python3 scripts/onethird_ap1b_followup_familyA_extended_sweep.py`.*

---

## 0. Vision alignment & non-goals

This ticket realises **vision-part 3** (sweep along the data-corrected shape
direction) and gives a refined **vision-part 4** signal (descent-vs-plateau on
the *correct* family). It consumes the AP-1a + AP-0 carry-forwards verbatim.

Non-goals honoured (roadmap §8): **no** Cheeger / cut-and-window re-litigation;
**no** counterexample claim (and none arises — every `Q` stays well above `1/3`);
**no** Lean, LaTeX, or `main.tex`; **width-3 only**; **Monte-Carlo never the
source of truth**. The honest framing is unchanged from AP-1a: we are mapping
the family more honestly, **not** claiming a known descent.

**Two-method gate (roadmap §5.3a).** `Q` is reported only under the validated
two-method gate. For every headline witness with `e ≤ 200 000` the **full
M1==M2 brute-force gate** runs (`probe_shape` asserts `brute == DP` and
`e == Naruse` inline). For witnesses with `e > 200 000` (the n=19 minimiser has
`e ≈ 5.09M`) brute force is infeasible, so the gate is **DP == Naruse on `e`**
plus the **validated DP for `Q`** — the identical fallback AP-1a used for its
`k=3` point. A clean run *is* the gate passing.

---

## 1. Extended-cap argmins — raising λ₁ (SCOPE 1)

AP-1a swept all width-3 3-row skew shapes at each `n` under `λ₁ ≤ 12`, and
flagged that the `n=19` argmin sat **at** that cap — an upper-bound estimate
only. We re-ran each per-`n` sweep at caps `λ₁ ∈ {12, 18, 24}`.

| `n` | cap 12 | cap 18 | cap 24 | corrected argmin | cap-stable? |
|-----|--------|--------|--------|------------------|-------------|
| 7  | `2/5` ≈ 0.4000 `(4,3,3)/(3,0,0)` | `2/5` | `2/5` | `(4,3,3)/(3,0,0)` (one of 144+ ties) | **yes** |
| 8  | `27/70` ≈ 0.38571 `(4,4,2)/(2,0,0)` | `27/70` | `27/70` | `(4,4,2)/(2,0,0)` (unique) | **yes** |
| 13 | `3/7` ≈ 0.42857 `(5,5,4)/(1,0,0)` | `3/7` | `3/7` | `(5,5,4)/(1,0,0)` (unique) | **yes** |
| 19 | `943/2074` ≈ 0.45468 `(12,7,4)/(3,1,0)` **[AT CAP]** | `2307921/5088542` ≈ **0.45355** `(13,8,8)/(5,5,0)` | `2307921/5088542` ≈ **0.45355** `(13,8,8)/(5,5,0)` | **yes (at cap ≥ 18)** |

**The n=19 cap-12 estimate was a cap artifact.** Raising `λ₁` from 12 → 18
drops the n=19 minimum from `943/2074 ≈ 0.45468` to `2307921/5088542 ≈ 0.45355`,
and the new argmin `(13,8,8)/(5,5,0)` is **interior** (`λ₁ = 13 < 18`), not at
the cap. Cap 18 → 24 is **stable** (same value, same argmin; cap-24 verified at
14 267 width-3 shapes). So `(12,7,4)/(3,1,0)` is **replaced** by the corrected,
cap-stable n=19 minimiser `(13,8,8)/(5,5,0)`, `Q ≈ 0.45355`.

(For n=7 the "AT CAP" flag is spurious: `Q` stays pinned at `2/5` across all
caps — the high-`λ₁` shapes only add more *ties* at the degenerate `2/5` floor,
they never lower it. The same holds at n=8/13: the cap-12 values were already
the true minima.)

**Why λ₁ cannot simply be "unbounded."** A long thin row 1 floated far to the
right (`μ₁` large) above small rows 2–3 keeps `n` fixed while `λ₁ → ∞`, so the
shape count diverges with the cap. We therefore raise the cap to the requested
`λ₁ ≤ 24` and verify **value-stability** (the minimum stops moving), which it
does by cap 18 at every `n` here.

**Verification gate on the corrected witnesses** (script §1):

| `n` | witness | `e` | `Q` | self-dual? | gate |
|-----|---------|-----|-----|-----------|------|
| 7  | `(4,3,3)/(3,0,0)`  | 35      | `2/5` | no  | M1==M2 brute; `e`==Naruse |
| 8  | `(4,4,2)/(2,0,0)`  | 140     | `27/70` | **yes** | M1==M2 brute; `e`==Naruse |
| 13 | `(5,5,4)/(1,0,0)`  | 6006    | `3/7` | **yes** | M1==M2 brute; `e`==Naruse |
| 19 | `(13,8,8)/(5,5,0)` | 5088542 | `2307921/5088542` | **yes** | DP==Naruse(`e`); `Q` by validated DP |

---

## 2. The generalising rule (SCOPE 2)

### 2a. AP-1a's hypothesis — FALSIFIED

AP-1a's carried-forward hypothesis was: *"shapes where μ is small (first row
1–3, second row 0 or 1), λ rows close in size (within 1 for the top two, one
smaller third row)."* Testing it on the corrected argmins:

| `n` | corrected argmin | fits hypothesis? |
|-----|------------------|------------------|
| 8  | `(4,4,2)/(2,0,0)`  | **yes** (`μ₁=2`, `μ₂=0`, `λ₁=λ₂`, `λ₃<λ₂`) |
| 13 | `(5,5,4)/(1,0,0)`  | **yes** (`μ₁=1`, `μ₂=0`, `λ₁=λ₂`, `λ₃<λ₂`) |
| 19 | `(13,8,8)/(5,5,0)` | **NO** (`μ₁=5∉{1,2,3}`, `μ₂=5∉{0,1}`, `λ` top-two differ by 5) |

The hypothesis fit the two *small* candidates but is **decisively falsified by
the cap-raised n=19 minimiser** — exactly the candidate whose AP-1a form
`(12,7,4)/(3,1,0)` was a cap artifact. The hypothesis was reading off a small-`n`
accident, not the structural rule.

### 2b. The actual rule — CENTRAL SYMMETRY (self-dual shapes)

Every cap-stable per-`n` minimiser — including the falsifying n=19 shape — is a
**centrally-symmetric (self-dual) skew shape**: invariant under the 180°
rotation `(i,j) ↦ (4−i, C+1−j)` of its 3-row bounding box (`C = λ₁`). That
rotation **reverses** the product order, so the cell-poset `P` satisfies
`P ≅ Pᵒᵖ` — it is **self-dual**. For a 3-row skew shape, central symmetry is
exactly the three identities

> `μ₃ = 0`,  `λ₃ = λ₁ − μ₁`,  `μ₂ = λ₁ − λ₂`,

a clean **3-parameter family** in `(C=λ₁, λ₂, μ₁)`, with
`n = 2(λ₁ − μ₁) + (2λ₂ − λ₁)`. Check:

| witness | `λ₃ = λ₁−μ₁` | `μ₂ = λ₁−λ₂` | `μ₃` | self-dual |
|---------|-------------|-------------|------|-----------|
| `(4,4,2)/(2,0,0)`  | `2 = 4−2`  | `0 = 4−4`  | 0 | ✔ |
| `(5,5,4)/(1,0,0)`  | `4 = 5−1`  | `0 = 5−5`  | 0 | ✔ |
| `(13,8,8)/(5,5,0)` | `8 = 13−5` | `5 = 13−8` | 0 | ✔ |

**AP-1a's hypothesis is precisely the `μ₂ = 0` (i.e. `λ₁ = λ₂`), small-`μ₁`
sub-slice of this family.** The n=8 and n=13 minimisers happen to live in that
sub-slice; the n=19 minimiser is self-dual but with `λ₁ > λ₂` (`μ₂ = 5 ≠ 0`),
which is why it broke the hypothesis. Central symmetry is the rule; the
hypothesis was a special case.

### 2c. Does the self-dual family carry the global minimum?

We compared the **global** min (all width-3 3-row skew shapes) against the
**self-dual** min at each `n ∈ [7,15]` (cap 18):

| `n` | global min | self-dual min | match? |
|-----|-----------|---------------|--------|
| 7  | `2/5` ≈ 0.4000 | `12/29` ≈ 0.4138 | no (global = degenerate ribbon) |
| 8  | `27/70` ≈ 0.3857 | `27/70` | **yes** |
| 9  | `2/5` ≈ 0.4000 | `103/248` ≈ 0.4153 | no (global = degenerate ribbon) |
| 10 | `125/309` ≈ 0.4045 | `125/309` | **yes** |
| 11 | `47/110` ≈ 0.4273 | `27/61` ≈ 0.4426 | no (global = degenerate ribbon) |
| 12 | `14/33` ≈ 0.4242 | `14/33` | **yes** |
| 13 | `3/7` ≈ 0.4286 | `3/7` | **yes** |
| 14 | `16726/39559` ≈ 0.4228 | `16726/39559` | **yes** |
| 15 | `3/7` ≈ 0.4286 | `3/7` | **yes** |

The self-dual family **is** the global minimiser wherever the global minimum is
not a *degenerate near-chain ribbon*. The non-matching cases are the odd-`n`
`2/5`-type ribbon floors (heavily-tied, translation-orbit degenerate — the same
`2/5` AP-1a noted at n=7 with 144 ties), and crucially **they all sit ABOVE the
n=8 self-dual record `27/70 ≈ 0.386`**. So the self-dual family carries the
genuine low-`Q` content; the unconstrained global min only "wins" at odd `n` by
landing on a shallow degenerate ribbon that is not competitive with the n=8
record.

---

## 3. Self-dual family Q-sweep (SCOPE 3)

Minimum `Q` over self-dual width-3 3-row skew shapes at each `n`, cap 24
(cap-stable — verified identical at cap 16):

| `n` | min `Q` (self-dual) | `≈` | argmin `λ/μ` |
|-----|--------------------|-----|--------------|
| 7  | `12/29`               | 0.413793 | `(5,5,1)/(4,0,0)` |
| **8** | **`27/70`**         | **0.385714** | **`(4,4,2)/(2,0,0)`** |
| 9  | `103/248`             | 0.415323 | `(5,4,3)/(2,1,0)` |
| 10 | `125/309`             | 0.404531 | `(6,4,4)/(2,2,0)` |
| 11 | `27/61`               | 0.442623 | `(7,6,3)/(4,1,0)` |
| 12 | `14/33`               | 0.424242 | `(8,8,2)/(6,0,0)` |
| 13 | `3/7`                 | 0.428571 | `(5,5,4)/(1,0,0)` |
| 14 | `16726/39559`         | 0.422811 | `(10,6,6)/(4,4,0)` |
| 15 | `3/7`                 | 0.428571 | `(5,5,5)/(0,0,0)` |
| 16 | `679/1480`            | 0.458784 | `(8,6,6)/(2,2,0)` |
| 17 | `443/1015`            | 0.436453 | `(11,11,3)/(8,0,0)` |
| 18 | `203/442`             | 0.459276 | `(6,6,6)/(0,0,0)` |
| 19 | `2307921/5088542`     | 0.453553 | `(13,8,8)/(5,5,0)` |
| 20 | `1289070/2863813`     | 0.450124 | `(16,9,9)/(7,7,0)` |
| 21 | `4652/10203`          | 0.455944 | `(15,15,3)/(12,0,0)` |
| 22 | `2335/5168`           | 0.451819 | `(14,14,4)/(10,0,0)` |
| 23 | `35501036/75624161`   | 0.469440 | `(15,10,9)/(6,5,0)` |
| 24 | `44875/96577`         | 0.464655 | `(8,8,8)/(0,0,0)` |

The family-wide minimum is **`27/70 ≈ 0.385714` at n=8** — the same all-time
Family A record AP-0 found. Nothing in the extended range goes below it.

---

## 4. Descent-vs-plateau call (SCOPE 4)

```
self-dual family min Q vs n:
  n= 7  0.4138
  n= 8  0.3857   <-- family-wide minimum (= AP-0/AP-1a record 27/70)
  n= 9  0.4153
  n=10  0.4045
  n=11  0.4426
  n=12  0.4242
  n=13  0.4286
  n=14  0.4228
  n=15  0.4286
  n=16  0.4588
  n=17  0.4365
  n=18  0.4593
  n=19  0.4536
  n=20  0.4501
  n=21  0.4559
  n=22  0.4518
  n=23  0.4694
  n=24  0.4647
```

**CALL: PLATEAU / RISE — away from `1/3`, not toward it.** The self-dual
minimum is non-monotone (a mild parity wiggle) but its envelope **rises** from
the n=8 record `0.386` into a `~0.42–0.47` band and stays there; the last-five-`n`
mean is `≈ 0.456`. The genuine minimum sits at **small `n` (n=8)**, and growing
`n` moves the family minimum *up*, increasing the distance to `1/3`. This is the
same verdict AP-1a reached on the (wrong) ray — now confirmed on the *correct*
self-dual family — and is consistent with a family-restricted null
`inf_n Q(self-dual) > 1/3`, with the infimum apparently attained at small `n`.

This is a **clean, honest plateau** on the data-corrected shape direction: the
corrected rule does **not** trace a descent toward `1/3`. Family A reaches its
closest approach to `1/3` at `n=8` (`27/70 ≈ 0.386`) and recedes from there.

---

## 5. Closed-form-applicability fraction evolution (SCOPE 5)

For each forced pair the kernel numerator `#{ext : x<y} = e(P+(x<y))` is a
closed-form Naruse count **iff** the augmented poset stays a genuine skew shape;
otherwise it falls through to the width-3 DP. Measured (DP-only, so it works at
any `e`), self-validated by `Naruse(realised) == DP count`, along the self-dual
minimisers:

| `n` | self-dual minimiser | closed-form fraction |
|-----|--------------------|----------------------|
| 7  | `(5,5,1)/(4,0,0)`  | `1/9` ≈ 0.111 |
| 8  | `(4,4,2)/(2,0,0)`  | `0/14` = **0** |
| 10 | `(6,4,4)/(2,2,0)`  | `2/23` ≈ 0.087 |
| 12 | `(8,8,2)/(6,0,0)`  | `0/30` = **0** |
| 13 | `(5,5,4)/(1,0,0)`  | `0/30` = **0** |
| 14 | `(10,6,6)/(4,4,0)` | `0/51` = **0** |
| 15 | `(5,5,5)/(0,0,0)`  | `0/30` = **0** |
| 16 | `(8,6,6)/(2,2,0)`  | `1/27` ≈ 0.037 |
| 19 | `(13,8,8)/(5,5,0)` | `0/94` = **0** |

**Finding — the closed-form fraction is essentially `0` along the rule, sharper
than AP-1a's constant-`2` ray.** The centrally-symmetric "block" minimisers
almost never stay skew under a forced relation (the geometric extremes that kept
AP-1a's ray at a constant 2 closed-form pairs are absent here). The `Q`-kernel
along the corrected minimiser family is therefore **fully DP-bound**: budget it
as **`O(n⁴)`-DP-per-pair**, with only the count `e` itself closed-form (Naruse).
This confirms and strengthens the AP-0/AP-1a budget signal.

---

## 6. GUARD and recommended next ticket

**GUARD (roadmap §8.2, anti-Cheeger).** No `Q ≤ 1/3` is observed anywhere: the
family-wide minimum is `27/70 ≈ 0.386` (n=8), the per-`n` self-dual minima rise
to `~0.45`, and the all-time Family A record `27/70 ≈ 0.386` stands. **The
independent-reimplementation trigger does not fire.** (Were it ever to fire, the
AP-0/AP-1a/AP-1b′ three-engine agreement would NOT satisfy §8.2: a separate
codebase plus brute force would be mandatory before any claim.)

### Verdict: **GREEN — extended sweep delivered; the data-corrected rule is CENTRAL SYMMETRY, and it is a PLATEAU (no descent to 1/3).**

> AP-1b′ clears its scope. (1) The λ₁ cap is raised to 24 and the per-`n`
> argmins re-measured under the validated gate; the AP-1a n=19 estimate
> `(12,7,4)/(3,1,0)` is corrected to the cap-stable interior minimiser
> `(13,8,8)/(5,5,0)`, `Q ≈ 0.45355`. (2) AP-1a's small-`μ`/close-`λ` hypothesis
> is **falsified** by that corrected minimiser; the actual generalising rule is
> **central symmetry (self-dual skew shapes)**, a 3-parameter family of which
> AP-1a's hypothesis is the `μ₂=0` sub-slice. (3) The self-dual family `Q`-sweep
> over `n ∈ [7,24]` shows the minimum **rising** from the n=8 record `27/70`
> into a `~0.42–0.47` band. (4) **Descent-vs-plateau: PLATEAU/RISE — away from
> `1/3`.** (5) The closed-form fraction is **≈ 0** along the rule (fully
> DP-bound). No `Q ≤ 1/3`; no counterexample claimed or expected.

### Recommended next ticket: **AP-2 — asymptotic `inf_n Q` on the self-dual family + a width-3 *non-skew* probe.**

The corrected rule (central symmetry) plus the rising plateau is now solid
enough to ask the genuine asymptotic question on the *right* family:

1. **Analytic / fitted `inf_n Q` on the self-dual 3-parameter family** (roadmap
   §6.4). The minimum appears to be attained at small `n` (`n=8`) with the
   envelope rising; an analytic argument that `Q(self-dual) ≥ 27/70` (or at
   least `> 1/3`) for all `n` would convert the plateau into a
   **family-restricted sharpness result** — the program's intended deliverable
   (roadmap §8.2: the expected outcome is a bounded null, which is valuable).
   Budget the kernel as `O(n⁴)`-DP-per-pair (§5); only `e` is closed-form.
2. **Stop sweeping wider 3-row *skew* shapes for a lower record** — the n=8
   `27/70` floor has survived AP-0 (`n∈[7,9]`), AP-1a (the ray), and now AP-1b′
   (cap-raised global + self-dual family to `n=24`). It is a robust local record
   for 3-row skew shapes.
3. **Probe width-3 *non-skew* posets** (roadmap §3 Family B / §6 escalation) to
   ask whether the `27/70` skew-shape floor is a skew-shape artifact or a genuine
   width-3 obstruction — a useful cross-family sharpness datum, still under the
   width-3 restriction.

**No counterexample is claimed or expected** (§8.2). The honest reading: Family A
remains a LIVE, not-floored candidate (it reaches `Q < 1/2` freely and dips to
`0.386`), but along the **correct** (self-dual) shape direction the constant
**plateaus above `1/3`** with its infimum at small `n`. The value delivered is
the cap-corrected argmins, the corrected generalising rule, and a clean plateau
call on the right family.

---

## Appendix — reproduction

```
python3 scripts/onethird_ap1b_followup_familyA_extended_sweep.py           # full: caps 12/18/24, self-dual sweep n in [7,24] (~15-20 min)
python3 scripts/onethird_ap1b_followup_familyA_extended_sweep.py --quick   # caps 12/18, self-dual sweep n in [7,20] (~5 min)
```

The script reuses the AP-0 engine
(`scripts/onethird_ap0_familyA_skew_probe.py`) verbatim and asserts every
cross-check inline (Naruse == DP for `e`; brute == DP for `Q` where
`e ≤ 200 000`; sweep DP == verified witness; self-validated closed-form hits), so
a clean exit *is* the two-method-agreement gate passing. The `--quick` run caps
the n=19 global sweep at `λ₁ ≤ 18` (the cap-24 confirmation is the ~9-min long
pole) and the self-dual sweep at `n ≤ 20`; both reach the same verdict.
