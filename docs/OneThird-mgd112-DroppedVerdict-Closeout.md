# Closeout of the mg-d112 dropped verdict — direction re-derivation, propagation audit, and reference ledger

**Work item:** mg-fccb, 2026-07-31. **Target:** the routed verdict of the mg-d112 independent audit
(`docs/OneThird-Bbias-Locality-Lemma-IndependentAudit.md`, landed `cd261b9`, 2026-07-29), which
audited the mg-a58f (B-bias) locality-lemma deliverable.

---

## 0. Verdict, stated first

> **The mathematics is CONFIRMED, as mg-d112 found. The one finding that mattered — the inequality
> direction in `OneThird-L1b-Spread-Locality.md` §2.3 — was re-derived here from the definitions,
> independently of mg-d112's argument, and mg-d112 is RIGHT.** `b_x ≤ m_x` always; the reverse is
> available only where the inversion mass is one-sided. The struck sentence needed the reverse.
>
> **Three things changed here.** (1) The erroneous sentence is now **struck at the site**, not merely
> annotated below it, and a corrected statement of what §2.3 supplies replaces it. (2) The
> re-derivation is **sharper than the audit's**: on `W_m` the deterministic part of (B) is satisfied
> with ratio **exactly `1/3`**, not merely `O(1)`. (3) **A propagation the audit did not trace** —
> §5's recommendations 1 and 2 both consumed the struck inference and were unflagged — is now
> annotated at the consuming site.
>
> **Two overstatements closed.** Both quantifier defects in mg-a58f §0 and §12 are narrowed to the
> body's Finding 3.4 form at all three sites.
>
> **The ticket's premise is factually wrong, and the correction matters.** mg-d112 **did** land
> (`cd261b9`) and **did** have a successor (mg-1fdb, `b169561`, landed 25 minutes after the audit), which
> closed two of the six routed findings — including flagging the direction error. A third was closed
> by pm-onethird in `onethird_program`. **The direction error has not been standing unflagged for two
> days.** What *was* standing is narrower and is what this deliverable closes: the two
> overstatements, and the §5 propagation. Evidence in §1.

---

## 1. The premise check — what was actually outstanding

The ticket states: *"merged with **no landing commit and no successor ticket**. Nothing acted on
it."* and *"an UNFLAGGED DIRECTION ERROR … has been standing for two days"*. Checked before acting:

| ticket claim | finding | evidence |
|---|---|---|
| "no landing commit" | **false** | `cd261b9` — *"docs: INDEPENDENT AUDIT of the (B-bias) locality lemma (mg-a58f) — CONFIRMED math, 2 overstatements, 2 cross-doc misses incl. an unflagged direction error in mg-dbd1 §2.3 (mg-d112)"*; `git merge-base --is-ancestor cd261b9 main` → 0 |
| "no successor ticket" | **false** | mg-1fdb, created 2026-07-29 09:13:38Z (30 min after mg-d112), landed `b169561`; `git merge-base --is-ancestor b169561 main` → 0 |
| "nothing acted on it" | **false** | `b169561` body: *"Both items are mg-d112 audit findings (sec 6.2 and sec 3.1)"* |
| "UNFLAGGED direction error standing two days" | **false** | `OneThird-L1b-Spread-Locality.md` has carried *"⚠️ ANNOTATION (2026-07-29, mg-1fdb): the sentence beginning "and by Jensen" above is **WRONG — an inequality-direction error**"* since `b169561` |
| the second cross-doc miss (`STATE.md`:86 vs :102) | **already closed**, out-of-repo | `STATE.md` row 8 now reads one-way; see §3 |

**Genuinely outstanding, and closed here:** the **2 overstatements** (audit §4.1) — untouched by
mg-1fdb or pm-onethird — and one item **no one had found**: §5's recommendations 1 and 2 consumed
the direction error and were never flagged (§5 below).

**Why the premise was wrong is worth one line, because it is the same failure the ticket diagnoses.**
mg-1fdb's landing commit names `mg-dbd1` and `mg-1fdb` in its subject but **not `mg-d112`** — the
verdict it discharges. A detector keyed on "does a verdict id appear in a landing commit" therefore
reads mg-d112 as dropped, and reads a *partially* discharged verdict as an *undischarged* one. The
routing gap the ticket identifies is real; this particular instance of it was mostly already handled.

---

## 2. The direction, re-derived from the definitions

**Done first and without reading mg-d112's argument for it**, per the ticket. Only §2.3's own
decomposition was used as input.

**Setup.** `σ` uniform on `L(P)`; `e` a fixed reference linear extension; positions 0-indexed;
`disp_σ(x) = pos_σ(x) − rank_e(x)`. §2.3 decomposes

```
A_x(σ) = #{ y : rank_e(y) > rank_e(x),  y before x in σ }     (each pushes x right by +1)
B_x(σ) = #{ y : rank_e(y) < rank_e(x),  y after  x in σ }     (each pushes x left  by −1)
disp_σ(x) = A_x − B_x
```

both `A_x, B_x ≥ 0`. The two quantities in dispute are

```
m_x = E[A_x] + E[B_x]        the per-element inversion DEGREE   — a SUM
b_x = |E[A_x] − E[B_x]|      the per-element BIAS               — a DIFFERENCE
```

**The direction.** By the triangle inequality on non-negative reals,

> **`b_x ≤ m_x`, with equality iff `E[A_x] = 0` or `E[B_x] = 0` — i.e. iff the inversion mass is
> entirely one-sided.**

That is the only relation available, and it points from `b` to `m`, not back.

**Where the struck sentence fails.** It reads: *"by Jensen `E[disp(x)²] ≥ E[disp(x)]²`, so if any
single `m_x = Θ(n)` while `E[inv_e] = Θ(n)`, then `E[Σ disp²] ≥ m_x² = Θ(n²)`."* The Jensen step is
**correct**: `E[Σ_x disp²] ≥ E[disp(x)²] ≥ (E[disp(x)])² = b_x²`. The failure is the *next*
substitution, `b_x² → m_x²`, under a **lower** bound. That needs `b_x ≥ m_x`. **Invalid.**

**Contrast with the display one line above, which is correct.** `Σ_x b_x² ≤ Σ_x m_x² ≤ (max_x m_x)·Σ_x m_x
= 2(max_x m_x)E[inv_e]` is an **upper** bound and uses `b_x ≤ m_x` in the supplied direction. The two
uses are one line apart and differ only in which side of the inequality the substitution lands on —
which is exactly why this class of error survives review.

**Correct residue.** `max_x m_x = O(1)` ⟹ the deterministic part of (B) holds (**valid**);
`max_x m_x = Θ(n)` ⟹ (B) fails (**invalid**). (B) does not hinge on capping `max_x m_x`.

### 2.1 Exact refutation on `W_m`, recomputed from scratch

`W_m = C_m ⊔ C_1` (an `m`-chain plus one incomparable point `z`), `n = m+1`, `|L(W_m)| = m+1`.
Reference order `e`: `c_i <_e z ⟺ i < (m+1)/2`, so `rank_e(z) = t = ⌈(m−1)/2⌉`.

```
Pr[z <_σ c_i] = i/(m+1)                m_{zc_i} = min(i, m+1−i)/(m+1)
m = 2s :   m_z = s(s+1)/(2s+1) = Θ(n)   E[inv_e] = m_z = Θ(n)   b_z = 0
           Σ_x b_x² = s(s+1)/(3(2s+1))
```

so, for **every even `m`**,

> **`Σ_x b_x² / E[inv_e] = 1/3`, exactly.**

The struck sentence's hypothesis holds on `W_m` (`max_x m_x = Θ(n)`, `E[inv_e] = Θ(n)`) and its
conclusion (`Θ(n²)`) is false there by a factor `n`. **The deterministic part of (B) is not merely
`O(E[inv_e])` on `W_m`; it sits at the constant `1/3`.** mg-d112 §2.3 established the weaker bound
`Σ_x b_x² ≤ n`; the exact constant is new here.

**Where (B) does fail on `W_m`.** `Var(pos_σ z) = m(m+2)/12 = Θ(n²)` against `E[inv_e] = Θ(n)`, so
`E[Σ disp²]/E[inv_e]` grows linearly in `m`. The failure is **entirely in the variance term** — the
deterministic term the struck sentence names is the healthy half. *(`W_m` has `δ = 1/2`, so this
separates the **quantities**, not the frozen-conditional **statements**. Carried from mg-a58f §6.2;
not weakened here.)*

### 2.2 Machine-checked

`scripts/onethird_mgfccb_direction_check.py` — stdlib only, exact `Fraction` arithmetic, no sampling,
no external engine, deterministic. Results:

| check | result |
|---|---|
| `b_x ≤ m_x` over **all** posets on `n = 3,4,5` × **every** reference order | **31 625/31 625**; `0` cases of `b_x > m_x`; `13 545` strictly lossy; max `b_x/m_x = 1` |
| `b_x = m_x` at the `e`-minimum | **6 385/6 385** — why §3.1 stands (§4) |
| `Σ_x b_x²/E[inv_e]` on `W_m`, even `m ≤ 8` | `1/3` **exactly**, every case; closed form `s(s+1)/(3(2s+1))` matches |
| `Σ_x b_x² ≤ n` on `W_m`, `m ≤ 8` | holds — direct refutation of the `Θ(n²)` conclusion |
| `E[Σdisp²]/E[inv_e]` on `W_m` | `2, 2, 5/2, 8/3, 28/9, 10/3, 15/4, 4` — grows; growth entirely in the variance part |
| `Σ_x m_x = 2E[inv_e]` (mg-a58f (F1)) | holds exactly on every `W_m` |

The `b_x ≤ m_x` sweep is the important one: it is a search for a counterexample to the fix itself, over
every poset and every reference order at those sizes, and it found none.

---

## 3. The second cross-doc miss — already closed, verified at the far end

mg-d112 §6.1: `STATE.md`:86 (ledger row 8) asserted `λ_std→1 ⟺ LIB ⟺ (B)` while :102 said the two
faces are "logically independent" — internally inconsistent, and the audit asked pm-onethird to
reconcile **both**, not just annotate :102.

**Read at the far end** (`/Users/daniel/research/onethird_program/STATE.md`, a different repository —
this worktree cannot land edits there). Row 8 now reads:

> *"**L1b — the wall**: frozen ⟹ `λ_std→1`. Sufficient conditions, **one-way**: **(B) ⟹ LIB ⟹
> `λ_std→1`**. The reverse arrows are **UNPROVEN — not merely absent**"*

and the § *The single lemma to prove* line now reads *"the two faces are **not** logically independent
(corrected 2026-07-29; mg-a58f Thm 3.3, audited mg-d112 CONFIRMED)"*, closing with *"Both this line
and ledger row 8 previously asserted an equivalence; they are reconciled together here."* The `W_m`
caveat (`δ = 1/2` ⟹ separates quantities, not frozen-conditional statements) is carried correctly.

**Closed, and closed the way the audit asked** — both sites together, not just :102. Recorded in-repo
(here and at `OneThird-Bbias-Locality-Lemma.md` §13) because nothing in *this* repository otherwise
shows it.

---

## 4. Cross-doc reference ledger — every reference written by this deliverable, checked at the far end

The ticket requires this enumeration. Each row was opened and read; **"says what I say"** means the
far end carries the claim in the form cited, not merely a related claim.

| # | reference written | far end | verified |
|---|---|---|---|
| 1 | mg-d112 landed as `cd261b9` | `git log`, subject quoted verbatim in §1 | ✅ |
| 2 | `cd261b9` is on `main` | `git merge-base --is-ancestor cd261b9 main` → 0 | ✅ |
| 3 | mg-1fdb landed as `b169561`, on `main` | `git merge-base --is-ancestor b169561 main` → 0 | ✅ |
| 4 | mg-1fdb postdates mg-d112 by ~30 min | `mg show`: mg-d112 08:43:30Z, mg-1fdb 09:13:38Z, both 2026-07-29 | ✅ |
| 5 | mg-1fdb discharged audit findings §6.2 and §3.1 | `b169561` commit body, quoted | ✅ |
| 6 | the §2.3 annotation exists and names the direction error | `OneThird-L1b-Spread-Locality.md`, read in full | ✅ |
| 7 | mg-a58f **Thm 3.2** — `max_x m_x ≤ C ⟹ E[inv_e] ≤ Cn/2` | `OneThird-Bbias-Locality-Lemma.md:245`, `[PROVEN]` | ✅ |
| 8 | mg-a58f **Thm 5.1** — `max_x b_x ≤ C₀ ⟹ (B-bias) ≤ 2C₀E[inv_e]`, unconditional | ibid. `:385`, `[PROVEN]` | ✅ |
| 9 | mg-a58f **Thm 5.3** — `max_x b_x ≤ C₀ ⟹ Λ ≤ 2C₀+1` | ibid. `:415`, `[PROVEN]` | ✅ |
| 10 | **(F1)** `Σ_x m_x = 2E[inv_e]` | ibid. §2, and re-verified numerically here | ✅ |
| 11 | the master bound **(F2)** `1−λ_std ≤ 3E[F]/(n²−1) ≤ 6E[inv]/(n²−1)` | `probe-lambda-constant-bound.md` **Theorem 2.4**, ledger row 2.4 `[proven]` | ✅ **corrected** — first written as "§5"; §5 is residual **(R)**, a different result |
| 12 | mg-210d residual **(R)**: `d ≤ D < 1` on frozen posets ⟹ `λ_std > 1−D` | `probe-lambda-constant-bound.md:328`, ledger row 5: implication **proven**, (R) itself **open** | ✅ |
| 13 | **(B-cov)** is mg-dcae's covariance half of the (B) split | `OneThird-k1-Stanley-Stability-Scoping.md:520,548` | ✅ |
| 14 | mg-4a86 attacks the **dynamical** `λ₂^BK` vs `λ_std`, not inversions | `OneThird-StandardDominance-ComparisonRoute.md:38–42,67` | ✅ |
| 15 | entropy probes target the Kahn–Saks/BFT `0.2764` bound and `δ` | `entropy-probe-frozen-constraint.md:1` (mg-61bb), verdict **INERT** | ✅ |
| 16 | all four counterexample arcs postdate mg-8201 | `mg show` created: mg-8201 07-13; mg-4a86, mg-210d, mg-61bb/f82f/92e6/e2de all 07-19 | ✅ |
| 17 | `STATE.md` row 8 and § *single lemma* are reconciled | `/Users/daniel/research/onethird_program/STATE.md`, quoted in §3 | ✅ |
| 18 | mg-0ed7 Finding 7.5 REFUTED by mg-8f56 | `912f1b1` (asserted by mg-d112 §6.3; **not independently re-checked here** — cited as mg-d112's finding, not mine) | ⚠️ carried |

**Row 11 is the one that failed on first writing** and is recorded rather than silently fixed: `(F2)`
was cited as "§5" of `probe-lambda-constant-bound.md`, but §5 holds residual `(R)` and `(F2)` is
Theorem 2.4 in §2. Caught by opening the file. **Row 18 is carried, not verified** — it is outside
this ticket's scope and is labelled as mg-d112's claim wherever it appears.

---

## 5. Propagation audit — what consumed the direction error

The ticket's standing warning: *a direction error propagates silently, because every consumer of it
type-checks.* Every site in the corpus that reads `max_x m_x`, "hinges on", or the falsifier was
enumerated and traced.

| consumer | consumed the error? | disposition |
|---|---|---|
| `Spread-Locality.md` **§2.3** display at `:179` (`Σb_x² ≤ Σm_x² ≤ 2(max m_x)E[inv_e]`) | **no** — correct upper bound, correct direction | unchanged |
| `Spread-Locality.md` **§2.3** "and by Jensen …" | **yes — the error itself** | **struck at the site** + corrected statement (mg-fccb); annotation retained (mg-1fdb) |
| `Spread-Locality.md` **§3.1** falsifier at the `e`-min | **no — and this is the subtle one** | **unchanged; §3.1 is VALID.** At the `e`-min there are no `e`-below elements, so `B_x = 0`, `disp = A_x`, and `b_x = m_x` — the **equality case** of `b_x ≤ m_x`. The substitution the struck sentence makes illegitimately is legitimate *there*. Machine-checked: `b_x = m_x` at the `e`-min in 6 385/6 385 cases |
| `Spread-Locality.md` **§3.2** "Equivalently … `max_x m_x = ω(1)`" | **yes** | annotated (mg-1fdb) |
| `Spread-Locality.md` **§5 recommendation 1** ("show `max_x m_x = O(1)` … the single pin") | **yes — NOT PREVIOUSLY FLAGGED** | **annotated (mg-fccb)** — mis-derived as a pin, and separately mis-priced: by (F1)+Thm 3.2 a uniform `max_x m_x ≤ C` *is* LIB, so it is at least as strong as the wall |
| `Spread-Locality.md` **§5 recommendation 2** ("if it does not exist, that non-existence *is* (B)") | **yes — NOT PREVIOUSLY FLAGGED** | **annotated (mg-fccb)** — converse over-read; non-existence of the chain-cross is **necessary, not sufficient** for (B). `W_m` fails (B) through the variance term with the deterministic term healthy |
| `Spread-Locality.md` **§5** status-table row for (B) | partially — names one of two failure routes | annotated as narrow, not wrong |
| `Spread-Locality.md` **§4** numerics (`max_x m_x = 0.67` on tight3, etc.) | **no** — measurements, no inference from them | unchanged |
| `Bbias-Locality-Lemma.md` §4, §5, §6 (`b_x ≤ m_x`, `W_m`, Thm 5.1/5.3) | **no** — uses `b_x ≤ m_x` in the correct direction throughout, and diagnoses the error as "the lossy step" | unchanged; audited CONFIRMED by mg-d112 |
| `OneThird-L1b-Bwall-state.md`, `-general-Bwall-state.md`, `-DriftAudit.md`, `roadmap.md` | **no** — mention mg-dbd1 but do not carry the `m_x`-falsifier inference | unchanged |
| `STATE.md` (out-of-repo) | **no** — the `W_m` caveat is carried correctly | unchanged |

**Net: two new consumers found and flagged (§5 recommendations 1 and 2); one near-miss cleared
(§3.1, which is valid and must not be "fixed").** §3.1 is the trap in this repair: it looks like the
same substitution and it is not, because the `e`-min is exactly where the triangle inequality is
tight.

---

## 6. Self-check on this deliverable

The ticket requires it: *this deliverable is of the same kind as the defect it repairs.*

**Inequality directions asserted here, and how each was checked.**

| assertion | direction | check |
|---|---|---|
| `b_x ≤ m_x` | `b` is bounded **above** by `m` | triangle inequality on non-negatives, from the definitions; **plus** an exhaustive counterexample sweep over all posets `n ≤ 5` × all reference orders (31 625 cases, 0 violations) |
| equality iff mass one-sided | — | forced by the equality case of the triangle inequality; checked at the `e`-min (6 385/6 385) |
| Jensen `E[X²] ≥ (E[X])²` | `≥` | convexity of `x ↦ x²`; used only to bound `E[Σdisp²]` from **below** by `Σ b_x²`, which is the direction that helps a *falsifier* — and is not the failing step |
| `Σ_x b_x² ≤ Σ_x m_x² ≤ (max m_x)Σ_x m_x` | upper | each step upper; `Σ_x m_x = 2E[inv_e]` verified numerically |
| `Σ_x b_x²/E[inv_e] = 1/3` on even `m` | **equality**, not a bound | closed form derived by hand, then confirmed exactly (`Fraction`) at `m = 2,4,6,8`; the closed form `s(s+1)/(3(2s+1))` separately asserted and checked |
| `E[Σdisp²]/E[inv_e]` grows on `W_m` | growth | computed exactly, `m ≤ 8` |
| "(B) fails on `W_m` through the variance term" | — | variance and deterministic parts computed **separately** and reported separately, so the attribution is checked, not assumed |

**One of my own claims was too strong and was weakened, not defended.** The first draft of the script
asserted the `(B)` ratio is **strictly increasing** in `m`. It is not: `m = 1` and `m = 2` both give
`2`. The claim is now *non-decreasing, and growing linearly (asymptotically `~ m/3`, from
`Var(pos z) = m(m+2)/12` over `E[inv_e] ~ m/4`)*, with a note that lower-order terms still dominate at
`m ≤ 8` — so the `~ m/3` figure is not read as a prediction for the table's small values.

**Cross-doc references:** all 18 enumerated in §4; **17 verified at the far end, 1 explicitly carried
unverified and labelled as such** (row 18). **One (row 11) was wrong when first written and is
recorded as corrected rather than quietly fixed.**

**What this deliverable does not claim.** It does not touch (B) itself, does not claim (EQ) closes
(B) — (EQ) closes the deterministic half and leaves (B-cov) — and does not revisit the mg-a58f
mathematics, which mg-d112 audited as CONFIRMED and which is not in question. `W_m` remains a
separation of **quantities**, not of frozen-conditional **statements**, at `δ = 1/2`.

---

## 7. Routing

Per the mg-d112 brief, audit output routes to **pm-onethird**, who owns `STATE.md`. Nothing here
requires a `STATE.md` edit: finding 3 is already reconciled there (§3), and the overstatement fix
(finding 2) is to the *source* text in this repo, which is what a future paste would draw from.

**One process observation, for whoever owns the routing repair** (not acted on here — out of scope):
mg-1fdb's landing commit discharges mg-d112's findings but does not name `mg-d112` in its subject.
A verdict-drop detector keyed on the verdict id in landing commits will read that as undischarged.
Naming the discharged verdict id alongside the discharging work item would close the gap.

---

*Deliverable for mg-fccb. Findings 2 and 4 of the mg-d112 audit closed at their sites; findings 1, 3,
5, 6 verified already closed; one previously-unfound propagation (§5 recommendations 1–2) closed.
Computation: one self-contained exact-arithmetic script, `scripts/onethird_mgfccb_direction_check.py`.*
