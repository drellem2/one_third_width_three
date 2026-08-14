# mg-c99c — running the repaired instrument wider: the realised-face gate at `n = 8`, and the 146 re-read over `Z/2`

*Filed 2026-08-14. Closes the two remainders `mg-0f24` named in its `unverified` list and
deliberately did not fold in. Both were "run the repaired instrument wider" rather than
mathematical closure, which is why they were filed together and separately from `mg-dd84`.*

**Related:** `mg-0f24` (the repair), `mg-9cd1` (the audit that found D3 and D7), `mg-72e4` (the
instrument), `mg-bcd7` (the `n = 7` `c = 1` class), `mg-dd84` (the min-margin closure — landed on
`main` while this was in flight; not this ticket's work, but see §2.3 and §4).

---

## 0. Result

| | remainder | verdict |
|---|---|---|
| **R1** | the realised-face gate is unmeasured at `n = 8`; the old ambient gate declines 6 classes / 1 792 labelled there | **MEASURED, COMPLETE at `n = 8` — and the `n ≤ 7` pattern does NOT repeat.** The realised gate declines **3** of the 6 (392 labelled) and admits **3** (1 400 labelled). See §1 |
| **R2** | D3's `≥ 6 of 163` cannot become `= 6` until the 146 are re-read over `Z/2` | **CLOSED — `= 6 of 163 over Z/2`.** No 2-torsion in degree 3 or 4 anywhere in the 146. See §2 |

Neither remainder made a published figure wrong, and neither does now: R1 concerns an `n` nobody
has published, and R2 replaces a correctly-stated inequality with a correctly-stated equality
that keeps its field label.

**Nothing about what any control checks was changed.** Both scripts here are *additional*
instruments; `compat_geom_mg72e4_height1_anchor.py` and `audit_mg0f24_cap_gap.py` are untouched.
`mg-0f24`'s per-class verdicts at `n ≤ 7` are replayed from its committed JSON and reproduce
**identically** (control K5, §1.3).

**Host discipline.** Both scripts are single-process, single-core, `stdlib`-only. `pogo host load`
was consulted before each heavy run and read `PROCEED` both times (fleet 2.7 and 0.6 of 10 cores).
`$POGO_WORKER_CORES` is 3; neither script parallelises, so nothing was sized to `os.cpu_count()`
and the 3-core budget was never approached. Wall clock for the committed runs: R2 `2 m 33 s`,
R1 `≈ 25 m` (see §1.2 — the box was contended).

---

## 1. R1 — the realised-face gate at `n = 8`

`mg-0f24` replaced the over-cap gate's **ambient-simplex** test `binom(#atoms, d + 3)` with a
count of `Γ(P)`'s **realised** faces. Measured consequence at `n ≤ 7`: the old gate wrongly
excluded exactly one class (`n = 7`, `c = 1`, 42 labelled), the new gate excludes none. At
`n = 8` only the ambient side was computed — the old gate declines **6 classes / 1 792 labelled**
— and `mg-0f24` said plainly that what the new gate says there was **not measured**, because
*"counting realised faces for 556 classes at `n = 8` is a job, not a clause"*.

The narrow question was: **are those 6 declines real, or the same artifact one `n` higher?** At
`n ≤ 7` the answer was "artifact, every time", but that is one data point about a gate, not a law.

### 1.1 The answer — **the `n ≤ 7` pattern does not repeat. Half the declines at `n = 8` are real**

| | classes | labelled |
|---|---|---|
| declined by the **old ambient** gate at `n = 8` | 6 | 1 792 |
| of those, **still declined** by the realised gate (needed-degree column) | **3** | **392** |
| of those, **admitted** by the realised gate — wrongly excluded | **3** | **1 400** |
| **newly** excluded by the realised gate, needed-degree column | **0** | 0 |
| **newly** excluded by the realised gate, near-miss column | **0** | 0 |

Per class, with `d = n − c − 1` the needed degree and `cap = 3 000 000` faces:

| `c` | labelled | `#atoms` | `d` | ambient `binom(m, d+3)` | realised, through `d+1` | needed column | near-miss column |
|---|---|---|---|---|---|---|---|
| 1 | 56 | 42 | 6 | 445 891 810 | **> 3 000 000** (aborted) | **declined — real** | declined |
| 2 | 168 | 37 | 5 | 38 608 020 | **> 3 000 000** (aborted) | **declined — real** | declined |
| 2 | 168 | 37 | 5 | 38 608 020 | **> 3 000 000** (aborted) | **declined — real** | declined |
| 2 | 840 | 30 | 5 | 5 852 925 | `≤ 2 804 011` (bound) | **ADMITTED** | declined |
| 3 | 280 | 34 | 4 | 5 379 616 | `≤ 1 676 115` (bound) | **ADMITTED** | declined |
| 3 | 280 | 34 | 4 | 5 379 616 | `≤ 1 676 115` (bound) | **ADMITTED** | declined |

**So the answer to the narrow question is: three of the six were the same artifact one `n`
higher, and three are genuinely over cap.** At `n ≤ 7` the answer had been "artifact, every
time" — one class, one data point. Assuming that repeated would have been wrong for exactly half
the population at the next `n`. The repair is still a repair (it recovers 1 400 of 1 792 labelled
vertices the old gate would have thrown away, `78 %`), but it is not the case that the ambient
gate's declines are *always* spurious.

Two smaller readings, both new:

- **On the near-miss column (`β̃_{d+1}`, one dimension more) the realised gate declines all six.**
  That is the `mg-0f24` `n = 7` `c = 1` pattern holding at `n = 8`: a class can resolve the census
  question and still be over cap on the extra degree. The three "admitted" classes are admitted
  *for the needed degree*, which is what the census asks.
- **The realised gate excludes nothing the ambient gate admitted**, on either column, at any
  `n ≤ 8`. That was not guaranteed — the two tests are not nested (§1.2) — and it is now measured
  rather than assumed.

### 1.2 How 556 classes became a handful of enumerations — and why this is complete, not partial

For any simplicial complex on `m` vertices the number of faces of dimension `≤ dmax` is at most

    UB(m, dmax) = Σ_{k=1}^{dmax+1} binom(m, k)

because every face is a non-empty subset of size `≤ dmax + 1`. Where `UB ≤ cap` the realised gate
**provably** admits the class and no enumeration is needed. This is exact combinatorics, not a
heuristic or a sample.

`UB` and the old ambient test are **different objects**, and the difference is the whole reason
the two gates can disagree in both directions. The old test was `binom(m, d + 3)` — the size of
*one* layer, the one just **above** the skeleton in question. `UB` sums **every** layer up to and
including the skeleton. Neither dominates the other, so the realised gate can admit classes the
ambient gate declined *and* decline classes it admitted.

At `n = 8` this settles **203 of the 206** gated classes on the needed-degree column and **199 of
206** on the near-miss column outright; only **3** and **7** had to be enumerated against the cap.
Every one of the 206 has a verdict on both columns — nothing was sampled, truncated or skipped,
so this is a **complete** answer at `n = 8` and not a bounded partial. (The other **350** of the
**556** iso classes have `d = n − c − 1 < 0`, i.e. `c ≥ n`; they are outside the gate entirely and
are in neither denominator. `206 + 350 = 556`. The census itself — 556 classes / 6 285 806
labelled — is re-derived here and asserted against `mg-0f24`'s record, so the split is measured
rather than quoted.)

Where the enumeration did run and hit the abort, the realised count is reported as a **lower
bound** (`> 3 000 000`), which is all the gate needs: the class is over cap either way.

**Cost.** In the committed run: `1 374.8 s` for the `n = 8` sweep and `124.1 s` of per-`n` time
at `n ≤ 7`, one process, one core. An earlier identical run on a quieter host took `502.7 s` and
`52.8 s` — the difference is host contention (the process held `≈ 50 %` of one core for the
second run), not a change in the work. Roughly `87 s` of the `n = 8` figure is generating the
556 iso classes. **Both runs produce the same verdicts**; only the timings differ.
`mg-0f24`'s estimate that this was "a job, not a clause" was right about the shape of the work
and the bound is what made the job small.

### 1.3 The controls, and that they can fail

The counter is `mg-0f24`'s own `gamma_face_profile`, **imported rather than re-typed**, so there
is one counter in the corpus and not two.

| | what it pins | result |
|---|---|---|
| **K1** | the counter against the instrument's own `gamma_faces()` builder, per dimension, on every class at `n ≤ 5` | 31 classes / **191 dimension buckets**, all equal — the same 191 `mg-0f24` reported |
| **K2** | **MUTATION.** A counter with the `is_total` rejection dropped (so it counts a strictly larger complex) must be caught by K1's comparison | **caught** |
| **K3** | the NEW ingredient — the bound `UB` must never fall below an actual realised count. Pinned by enumeration on every gated class at `n ≤ 6` on both columns, *and* against every non-aborted count `mg-0f24` already recorded at `n ≤ 7` | **419 comparisons, 0 violations** |
| **K4** | **MUTATION.** A bound one term short must be caught by K3 | **caught** |
| **K5** | `mg-0f24`'s `n ≤ 7` per-class verdicts, replayed from its committed JSON and compared as multisets so row order cannot flatter the comparison | **identical at every `n`** |

The `mg-c99c` work item records that `mg-0f24`'s cap-gap face counter *"was demonstrated to go RED
against a deliberately broken counter"*. **That demonstration is not in the repository** — nothing
in `scripts/` or `docs/` contains it, so it cannot be re-run and K1 on its own is an assertion
nobody can show fails. **K2 commits it**, and K4 does the same for the ingredient this ticket adds.
That is the defect this corpus keeps catching, arriving one level up: a control whose
can-it-fail evidence lives only in a report.

The `n = 7` `c = 1` disagreement `mg-0f24` asserted (ambient excludes, realised admits the needed
degree, realised excludes the near-miss column) is re-asserted here, so a later edit that raises
the ambient cap instead of replacing the test goes RED rather than quietly reporting "0 wrongly
excluded".

**Script:** [`scripts/audit_mgc99c_n8_realised_gate.py`](../scripts/audit_mgc99c_n8_realised_gate.py)
**Data:** [`data/onethird-mgc99c-n8-realised-gate.json`](../data/onethird-mgc99c-n8-realised-gate.json)

---

## 2. R2 — the 146 re-read over `Z/2`, and D3's `≥ 6` becomes `= 6`

`mg-0f24` corrected D3 to *"`≥ 6` of 163 classes carry homology in degree 4"* and was careful to
write `≥` rather than `=`. The reason was a **torsion blind spot**, not a gap in the census:

- the **146** classes with a full homotopy type were read over the instrument's two primes near
  `10⁶` (`1 000 003`, `999 983`),
- the **17** without one were read over `Z/2` by `mg-9cd1`,
- so **2-torsion in degree 4 among the 146 would be invisible to both readings**.

### 2.1 The measurement

All 146 re-read over `Z/2` in degree 4, alongside the same degree over both instrument primes:

| | classes | labelled | `β̃₄ ≠ 0` over `Z/2` | `Z/2` disagrees with the primes |
|---|---|---|---|---|
| within the atom cap (**R2's population**) | 146 | 225 540 | 2 | **0** |
| outside it (`mg-9cd1`'s 17, re-derived) | 17 | 2 352 | 4 | 0 |
| **all** | **163** | **227 892** | **6** | **0** |

`β̃₄` over `Z/2` **equals** `β̃₄` over both instrument primes on **every one of the 163**. By
universal coefficients `dim_{F₂} H̃₄ = rank₄ + t₄(2) + t₃(2)`, so the agreement forces
`t₄(2) = t₃(2) = 0` — both, since they are non-negative and sum to zero. There is no hidden
seventh class, and no 2-torsion in degree 3 or 4 anywhere in the population.

**So D3's first column becomes `= 6 of 163 over Z/2`.** Landed at `mg-72e4` §4.2's table row and
§4.3's paragraph, replacing the `≥ 6` and the "nobody has done this" sentence.

### 2.2 Two things that came out of doing it rather than reasoning about it

**The 17 did not need to be quoted.** Their degree-4 skeletons turn out to sit **inside the
instrument's own `ELIM_CAP`** — the largest eliminated in this run is `495 147` faces against the
600 000 budget. They were excluded from the census by the gate on the **full** homotopy type
(`#atoms ≤ 20`), not by any degree-4 cost. So all 163 were read in one run, and `mg-9cd1`'s four
— the two stars and `K_{2,5}`/`K_{5,2}` — are **independently re-derived** rather than cited. The
`6` is now a figure one script produces over all 163.

**The field column moved, and `β̃_Q` did not.** Reading the 17 over the instrument's primes as
well (also new, also inside the cap) means `K_{2,5}`/`K_{5,2}` are no longer `Z/2`-only. That
changes the label and **nothing else**: `mg-72e4` §3's caveat is untouched, a mod-`p` ONE bounds `β̃_Q ≤ 1`
in every field, so those classes still have **no rational value**. This is deliberately not
folded into the count — Q-acyclicity is exactly the gap R2 is about, and it is not closed by
widening a claim.

### 2.3 An unplanned cross-check with `mg-dd84`

`mg-dd84` landed on `main` the same night, on a different branch, and closed the `n = 7`
min-margin denominator by showing the three `c ≤ 2` classes (`c = 1`, 42 labelled; two `c = 2`,
105 each — 252 labelled) carry **no homology in any degree**. Those three are among the 17 read
here, and this run independently reads all three as `β̃₄ = 0` over `Z/2` **and** over both
instrument primes. Different route, different purpose, neither measurement aware of the other.
It is a coincidence of scheduling rather than a designed control, and it is recorded as such —
but it is the only place in this ticket where a figure is confirmed by an instrument nobody here
wrote.

### 2.4 What `= 6` is not

It is a count **over `Z/2`**, in degree 4, over all 163 — the field label stays on the figure.
Two blind spots remain and **neither is the one R2 closed**:

1. **Odd torsion at a prime nobody read.** The three fields here are `Z/2` and the two primes near
   `10⁶`. A class could carry `q`-torsion at some other `q`, invisible to all three.
2. **Torsion *at* the instrument primes.** "No 2-torsion" is read against those primes standing in
   for the free rank. Torsion at `1 000 003` or `999 983` itself would be invisible to the
   comparison. The two primes agreeing on all 163 is **evidence** for this, not a proof.

Stated here rather than folded into the figure, because a `≥` that has been discharged should not
be silently re-purposed to carry a different uncertainty.

### 2.5 The controls, and that they can fail

The measurement is a comparison between two readings of the same complex. A `Z/2` reader that
silently reduced to the same answer as the primes would report "no disagreement" on all 146 and
**look exactly like a closure**. So:

| | what it pins | result |
|---|---|---|
| **Z1** | a 6-vertex triangulated **`RP²`**, whose entire content is that mod 2 sees homology the instrument's primes do not. **Both halves required**: `Z/2` must read `β̃ = (0, 0, 1, 1)` and the primes must read all zero | `Z/2` **(0,0,1,1)**, primes **(0,0,0,0)** — the reader can see 2-torsion. Precondition checked: every edge in exactly 2 triangles, 6/15/10, `χ = 1` |
| **Z2** | the parameterised reader against the instrument's own `reduced_betti_range`, on the primes it supports — boundaries of simplices, the empty complex, and every `Γ(P)` at `n ≤ 5` | **72 comparisons**, all equal |
| **Z3** | **MUTATION.** A `Z/2` reader that never actually left the primes must make Z1 go RED | **caught** |
| **reproduction** | the published populations and figures, re-derived rather than quoted: 163 / 227 892; 146 / 225 540; 17 / 2 352; 2 non-zero over the primes within cap and that they are `K_{3,4}`/`K_{4,3}`; 4 non-zero over `Z/2` outside it and that they are the two stars and `K_{2,5}`/`K_{5,2}` | **8 population/count checks + 2 class-identity checks, all pass** |

Z1 is the load-bearing one. Without it, "the `Z/2` reading agrees with the primes on all 146" is
a sentence a broken instrument produces just as readily as a working one.

**Script:** [`scripts/audit_mgc99c_z2_reread.py`](../scripts/audit_mgc99c_z2_reread.py)
**Data:** [`data/onethird-mgc99c-z2-reread.json`](../data/onethird-mgc99c-z2-reread.json)

---

## 3. This remedy is an artifact of the same kind as the defects it closes

Both remainders exist because a measurement was narrower than the sentence written about it. That
is exactly the failure mode two new scripts can commit, so the enumeration was done rather than
assumed:

| how this work could exhibit the defect it closes | checked by |
|---|---|
| the `Z/2` reader silently reduces to the primes, so "no disagreement on 146" is unfalsifiable | **Z1** (`RP²`, both halves) + **Z3** (mutation proves Z1 can fire) |
| the face counter counts a different complex than `Γ(P)` | **K1** (191 dimension buckets vs the builder) + **K2** (mutation) |
| the new `UB` bound is unsound, so "provably admitted" is a guess | **K3** (419 comparisons vs actual enumeration) + **K4** (mutation) |
| figures are **quoted** from earlier tickets rather than derived, so a rot goes unnoticed | both scripts re-derive their populations and go RED on mismatch: 163 / 227 892 / 146 / 225 540 / 17 / 2 352 / `K_{3,4}`,`K_{4,3}` / `mg-9cd1`'s four; and 556 / 6 285 806 / 6 declines / 1 792 labelled at `n = 8`. (A first draft of the `n = 8` script hard-coded the `556` in one sentence of its own summary; caught by this enumeration and replaced with the measured count.) |
| the widening silently moves an already-published verdict | **K5** replays every `mg-0f24` `n ≤ 7` row — identical |
| `ALL_PASS` over a population that never included the question | `R1_measured` / `R2_measured` are recorded in the JSON, and a run truncated below `n = 8` (or at another `n`/cap) says so in place of a verdict |
| the conclusion is stated wider than what was measured | `= 6` keeps its field label and §2.3 names the two blind spots that remain; R1 is labelled a reading of a **gate**, with no `β̃_d` claimed at `n = 8` |

**Not added to `.github/workflows/script-controls.yml`.** That workflow's stated admission rule is
*fast (order-seconds), self-contained, self-verifying*. These are `2 m 36 s` and `≈ 9 m 30 s`;
`audit_mg0f24_cap_gap.py` is out for the same reason. Adding them would trade a real budget for
the appearance of coverage. They are self-verifying (`ALL_PASS`, non-zero exit on failure) and
re-runnable by hand.

## 4. What this ticket did not do

- **`mg-dd84`'s min-margin closure** — untouched, and it did not need this work: `mg-dd84`
  landed on `main` while this branch was in flight and closed the 3 `c ≤ 2` classes (252 labelled)
  itself, taking the `n = 7` margin population to 163 of 163. This branch rebased onto it and
  resolved one conflicting table cell in `mg-72e4` §4.2 by taking `mg-dd84`'s margin and
  population columns and this ticket's homology-count column. §2.3 records where the two
  measurements happen to agree.
- **`n = 8` homology.** R1 measures a **gate**, not Betti numbers. Nothing here says what
  `β̃_d(Γ(P))` is at `n = 8` for any class, and the `n = 8` row of `mg-72e4` §4.2 does not exist
  and is not created.
- **Any change to what a control checks.** Both instruments are additive. The one existing
  verdict set that could have moved — `mg-0f24`'s `n ≤ 7` — is replayed and is identical.
