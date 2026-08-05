# INDEPENDENT AUDIT of the mg-fccb direction-error repair (mg-8a71)

**Target:** commit `1b00147` — *"close the mg-d112 verdict — strike the §2.3 direction error at the
site, find its two unflagged §5 consumers, narrow 2 overstatements (mg-fccb)"*, touching
`docs/OneThird-L1b-Spread-Locality.md`, `docs/OneThird-Bbias-Locality-Lemma.md`,
`docs/OneThird-mgd112-DroppedVerdict-Closeout.md`, `scripts/onethird_mgfccb_direction_check.py`,
`.github/workflows/script-controls.yml`.

**Auditor:** mg-8a71, pre-filed in the same action as its parent. I did not author the repair.

---

## 0. Verdict, stated first

**GREEN on the mathematics. AMBER on the remediation.**

| axis | verdict |
|---|---|
| **The direction** `b_x ≤ m_x` | **CONFIRMED, independently re-derived and machine-confirmed on a population 6.90× larger in triples than the repair's — 11.06× in posets.** The repair is right; mg-d112 was right; the struck sentence was wrong. |
| **The equality case pinning §3.1 as VALID** | **CONFIRMED.** §3.1 must not be "corrected". Verified 43 842/43 842. |
| **`W_m` closed forms (incl. the new exact `1/3`)** | **CONFIRMED**, all four, by hand *and* by exhaustive enumeration of `L(W_m)`. |
| **Consumer trace** | **INCOMPLETE AS REMEDIATION, complete as enumeration** — see **F1**. Two consumers the repair itself identified as carrying a *false* claim were left asserting it in live body text. |
| **Cross-doc claims the repair writes** | **CONFIRMED** on every row I re-opened (11 of 18 directly, plus the out-of-repo `STATE.md` quotes verbatim). |
| **Did the repair disturb the confirmed locality-lemma mathematics?** | **NO.** No mathematical statement was altered; the narrowing restored §0/§12 to the *body's* already-narrow Finding 3.4. |
| **The repair's own control** | **Sound conclusion, misnamed population** — see **F2**. |

Five findings: **F1** (medium), **F2** (medium), **F3**, **F4**, **F5** (low). None overturns the
repair. **F1 and F2 are defects in the repair that no prior reader flagged.**

---

## 1. The direction, re-derived — and one disclosure

### 1.1 Disclosure of contamination, made before the derivation

The brief says: *re-derive without reading the repair's reasoning*. I must record that I read
`1b00147`'s **commit message** — which restates the derivation in two lines — while running `git log`
to locate the target, **before** opening the document. Claiming a pure blind re-derivation would be
false.

What makes the re-derivation independent in the sense that matters: I derived the inequality, **its
equality case**, and **all four `W_m` closed forms** from the definitions in §0/§2.3 alone; and I
checked three things the commit message and the repair do not mention at all — the **e-maximum**
equality case (**F3**), and the two identities **(F1) `Σ_x m_x = 2E[inv_e]`** and
**(★) `E[Σdisp²] = 2E[inv_e] + Cross`** that the corrected §2.3 statement rests on and that the
repair did not re-verify. A contaminated reader who only nods along produces none of those.

### 1.2 The derivation, from §0/§2.3's definitions

`e` is a fixed reference linear extension; `pos_σ(x)` is the 0-indexed position of `x` in a uniform
`σ ∈ L(P)`; `disp_σ(x) = pos_σ(x) − rank_e(x)`.

`pos_σ(x) = #{y : y ≺_σ x}` and `rank_e(x) = #{y : y <_e x}`, so

```
disp_σ(x) = Σ_{y≠x} ( 1[y ≺_σ x] − 1[y <_e x] ).
```

Split the sum by the sign of `rank_e(y) − rank_e(x)`:

* `y` **`e`-below** `x`: the term is `1[y ≺_σ x] − 1 = −1[x ≺_σ y]`, and `x ≺_σ y` with `y <_e x` is
  exactly the event that `{x,y}` is `e`-inverted. Contribution `−B_x`.
* `y` **`e`-above** `x`: the term is `1[y ≺_σ x] − 0`, and `y ≺_σ x` with `x <_e y` is exactly the
  event that `{x,y}` is `e`-inverted. Contribution `+A_x`.

So **`disp_σ(x) = A_x − B_x` with `A_x, B_x ≥ 0`** — §2.3's own decomposition, re-derived. Hence

```
m_x = E[A_x] + E[B_x]      a SUM      of two non-negative reals
b_x = |E[A_x] − E[B_x]|    a DIFFERENCE of the same two
```

and therefore

> **`b_x ≤ m_x`, with equality iff `min(E[A_x], E[B_x]) = 0`** — i.e. iff `x`'s inversion mass is
> entirely one-sided. **The reverse `b_x ≥ m_x` is available nowhere else.**

**Where the struck sentence breaks, precisely.** It ran
`E[Σ disp²] ≥ Σ_x E[disp(x)]² = Σ_x b_x² ≥ m_x² = Θ(n²)`. The **first** step (Jensen) is
**correct** and I confirmed it (0 violations in 218 166 cases). The **second** step, the substitution
`b_x² → m_x²` under a *lower* bound, needs `b_x ≥ m_x`. It is the one invalid move, and it is invisible
because both quantities are non-negative reals attached to the same element: the sentence type-checks.

**Conclusion: the repair's direction is right, and so was mg-d112's.** My derivation was built from
the definitions and agrees.

### 1.3 The equality case, and why §3.1 survives — CONFIRMED, and extended

At the `e`-**minimum** there are no `e`-below elements, so `B_x ≡ 0`, `b_x = m_x`, and the
substitution the struck sentence makes illegitimately is *legitimate there*. §3.1 is therefore
**VALID and must not be "corrected"** — the repair calls this the trap and is right.

**Extension the repair does not state (F3).** The equality case is symmetric: at the `e`-**maximum**
there are no `e`-above elements, so `A_x ≡ 0` and `b_x = m_x` there too. Machine-confirmed:
**43 842/43 842 at the e-min *and* 43 842/43 842 at the e-max**, over every (labeled poset,
reference order) pair on `n ≤ 5`. So §3.1's falsifier has a second, unnamed instantiation — an
`e`-maximal element that leads a frozen chain a constant fraction of the time. Not an error; an
omission that leaves a usable falsifier site off the record.

### 1.4 `W_m` — every closed form re-derived and recomputed

`W_m = C_m ⊔ C_1`, `z` the free point, `e` placing `z` at `e`-rank `s = m/2` (which is the only `e`
making `b_z = 0`, since `E[pos_σ z] = m/2`). By hand: `Pr[z ≺_σ c_i] = i/(m+1)`,
`m_{zc_i} = min(i, m+1−i)/(m+1)`, and — the step the repair does not spell out —
`b_{c_i} = min(i, m+1−i)/(m+1) = m_{zc_i}` as well, which is what makes `Σ_x b_x²` a sum of squares
of the *same* numbers and produces the `1/3`:

```
m_z = E[inv_e] = s(s+1)/(2s+1)            Σ_x b_x² = 2Σ_{k≤s} k² /(2s+1)² = s(s+1)/(3(2s+1))
Σ_x b_x² / E[inv_e] = 1/3   exactly       Var(pos_σ z) = ((m+1)²−1)/12 = m(m+2)/12
```

All four **match the repair exactly**, and my instrument recomputes them from `L(W_m)` itself (not
from the closed form) at `m = 2,4,6,8,10`: **0 mismatches**. The `(B)` ratio `E[Σdisp²]/E[inv_e]`
comes out `2, 8/3, 10/3, 4, 14/3` — increments of `2/3` per `Δm = 2`, i.e. `~ m/3 + 4/3`, confirming
the repair's `~ m/3` **and** its own caveat that lower-order terms dominate at small `m`. **The
repair's "sharper than the audit" claim — the deterministic part of (B) is satisfied on `W_m` with
ratio exactly `1/3`, not merely `O(1)` — is CONFIRMED.**

---

## 2. Propagation — my own consumer trace, built before reading the repair's

A direction error propagates silently because every consumer type-checks. So I enumerated consumers
**semantically**, not by following the repair's list: every site in `docs/` that reads `max_x m_x`,
"hinges on", "Equivalently", or the §3.1 falsifier.

| consumer | consumes the error? | state after `1b00147` | my verdict |
|---|---|---|---|
| `Spread-Locality` §2.3 display `Σb² ≤ Σm² ≤ 2(max m)E[inv]` | no — upper bound, correct direction | unchanged | ✅ correct to leave |
| `Spread-Locality` §2.3 *"and by Jensen …"* | **yes — the error** | **struck in the body** + corrected statement | ✅ correctly repaired |
| `Spread-Locality` §3.1 falsifier at the `e`-min | **no** — equality case | unchanged | ✅ correctly left alone (the trap) |
| `Spread-Locality` §3.2 *"Equivalently: can `max_x m_x = ω(1)` …"* | **yes** | **still asserted in live body text**; annotated below | ⚠️ **F1** |
| `Spread-Locality` §5 rec 1 (*"the single pin"*) | **yes** | annotated (mg-fccb) | ✅ — not false, only mis-priced; annotation is the right instrument |
| `Spread-Locality` §5 rec 2 (*"that non-existence **is** (B)"*) | **yes** | **still asserted in live body text**; annotated below | ⚠️ **F1** |
| `Spread-Locality` §5 status-table row for (B) | partially | annotated as narrow | ✅ |
| `Spread-Locality` §4 numerics | no — measurements | unchanged | ✅ |
| `Bbias-Locality-Lemma` §4/§5/§6 | no — uses `b_x ≤ m_x` correctly, diagnoses the lossy step | unchanged | ✅ re-checked lines 209, 245, 348–351, 385, 415, 457–460 |
| `L1b-Bwall-state`, `-general-Bwall-state`, `-DriftAudit`, `-CoreLemma-forDaniel`, `k1-Stanley-Stability-Scoping`, `roadmap` | no | unchanged | ✅ grepped for the falsifier inference; none carries it |
| `STATE.md` (out-of-repo) | no — carries the `δ = 1/2` caveat correctly | unchanged | ✅ read at the far end |

**The enumeration agrees with the repair's, site for site.** The disagreement is about *disposition*,
and it is F1.

### F1 — MEDIUM: two consumers still assert the refuted inference in live body text

The repair's own stated reason for striking §2.3 rather than annotating it:

> *"mg-1fdb had annotated it below, **leaving the wrong claim in the body**"*

That standard is applied at §2.3 and **not** applied at the two other sites where the claim is
**false** rather than merely mis-priced:

* **§3.2** — *"Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with `E[inv_e] = O(n)` …?"* The
  repair's own annotation says this is *"a strictly stronger question than the first, not an
  equivalent one"*. The word **Equivalently** is still there, unstruck, in a display quote.
* **§5 recommendation 2** — *"If it does not exist, that non-existence **is** (B)."* The repair's own
  annotation says this is a **converse over-read**: non-existence is *necessary, not sufficient*. The
  sentence is still there, unstruck.

A reader who reads the body and skips the annotations — which is exactly the reader the strike at
§2.3 was for — still reads two false claims. This is not a mathematical error in the repair; it is an
inconsistently applied remediation standard, at the two sites the repair itself proved false.

**Recommendation:** strike both sentences at the site, in the §2.3 style (retained struck, correction
stated immediately), and re-baseline the control in §6.2 to zero.

---

## 3. Cross-doc claims the repair itself writes

The parent exists partly because a cross-doc miss went unflagged, so every reference the repair adds
was re-opened at the far end. The repair enumerates 18 in `Closeout` §4; I re-checked **11 directly**
(the ones where a wrong far end would change a conclusion) plus the two out-of-repo `STATE.md`
quotations.

| repair's claim | what I found at the far end | verdict |
|---|---|---|
| `(F2)` master bound is **Theorem 2.4**, §2, `[proven]` — *"first written as §5; corrected"* | `probe-lambda-constant-bound.md:148` **"Theorem 2.4 (master bound). [proven]"**, inside `## 2` (line 104) | ✅ and the self-reported correction is real |
| mg-210d residual **(R)** gives only `λ_std > 1−D`, and is not known to imply LIB | `probe-lambda-constant-bound.md:328–331`, ledger row 5: implication **proven**, (R) **open** | ✅ |
| **(B-cov)** is mg-dcae's covariance half | `OneThird-k1-Stanley-Stability-Scoping.md:520` (the (B-cov) display), `:548` | ✅ |
| mg-a58f **Thm 3.2 / 5.1 / 5.3** at `:245 / :385 / :415`, all `[PROVEN]` | all three present at those exact lines with those exact statements | ✅ |
| audit returned **45/47 CONFIRMED, 2 PLAUSIBLE, 0 BROKEN** | `OneThird-Bbias-Locality-Lemma-IndependentAudit.md:114`, verbatim | ✅ |
| mg-d112 landed `cd261b9`; mg-1fdb landed `b169561`; both on `main` | `git merge-base --is-ancestor` → **0** for both; subjects match | ✅ |
| mg-1fdb postdates mg-d112 by ~30 min | `mg show`: 08:43:30Z vs 09:13:38Z, same day | ✅ (30 m 08 s) |
| mg-4a86 attacks the **dynamical** `λ₂^BK`, not inversions | `OneThird-StandardDominance-ComparisonRoute.md:38–42` — *"`λ₂^BK` is a **dynamical** functional … `λ_std` is a **static** functional"* | ✅ |
| entropy probes target Kahn–Saks/BFT `0.2764` and `δ` | `entropy-probe-frozen-constraint.md:1` title is exactly that question; verdict INERT | ✅ |
| **all four arcs postdate mg-8201** (so the "false universal" really was false) | mg-8201 = `6a4abec`, **2026-07-13**; all four arc docs first appear **2026-07-19** | ✅ |
| `STATE.md` row 8 and the *single lemma* line are reconciled | both quoted strings present **verbatim** at `/Users/daniel/research/onethird_program/STATE.md:86` and `:102`, including *"Both this line and ledger row 8 previously asserted an equivalence; they are reconciled together here."* and the `δ = 1/2` caveat | ✅ |

**No cross-doc claim written by the repair failed at the far end.** Row 18 (mg-0ed7 §7.5 refuted by
mg-8f56) is carried by the repair as *explicitly unverified and attributed to mg-d112*; I did not
verify it either, and record that identically rather than launder it.

---

## 4. Did the repair disturb the confirmed mathematics?

**No.** The standing risk when a deliverable is told it overstated is over-correction. Checked:

* The diff to `OneThird-Bbias-Locality-Lemma.md` is **four hunks**: §0's abstract, the §12 attempt-index
  row, the §12 narrative line, and a new §13. **Not one line of §§1–11 — the theorems, proofs,
  identities, and `W_m` computations that mg-d112 audited as CONFIRMED — was touched.**
* The narrowing is a **restoration, not a weakening**: the body's Finding 3.4 *already* read
  *"the weakest of the three sufficient conditions … Both objects the program has attacked since
  mg-8201"* **before** the repair (verified at `1b00147^:docs/OneThird-Bbias-Locality-Lemma.md:313`).
  The overstatement lived only in the abstract and the paste-ready row, which had dropped the body's
  qualifiers. The repair moved §0/§12 **to** the body, not the body anywhere.
* No theorem lost a hypothesis; no `PROVEN` label was downgraded; `(EQ)`, Thm 3.2, Thm 3.3 and the
  strength ladder read identically before and after.

---

## 5. Findings F2–F5

### F2 — MEDIUM: the repair's control names a population that is not the one it sweeps

`scripts/onethird_mgfccb_direction_check.py:141` declares

```python
def all_posets(n):
    """All posets on n labelled elements (small n only), as Poset objects."""
    pairs = list(combinations(range(n), 2))          # <-- (a, b) with a < b, ONLY
```

Every generated relation is a subset of `{(a,b) : a < b}`, so the generator yields **only posets
having the identity permutation as a linear extension** — not all labeled posets. Measured:

| n | repair's `all_posets(n)` | labeled posets on `[n]` (A001035) |
|---|---|---|
| 3 | **7** | 19 |
| 4 | **40** | 219 |
| 5 | **357** | 4231 |
| total | **404** posets → 6 385 `(P, e)` pairs → **31 625** triples | **4 469** posets → **43 842** pairs → **218 166** triples |

The doc annotation and the **CI step comment** both say *"sweeps **ALL posets** on n = 3,4,5 against
EVERY reference linear extension (31 625 element/order pairs)"*. **31 625 is 14.5% of that
population.**

**The conclusion is nevertheless unaffected, and I verified this two ways rather than assuming it.**
(i) *Argument:* given any labeled `P` and reference order `e`, relabel by `e`-rank; the image has the
identity as a linear extension, hence lies in the swept family, `e` maps to one of its swept reference
orders, and `b_x`/`m_x` are invariant under simultaneous relabeling — so the swept family is a
**complete set of representatives up to isomorphism of `(P, e)` pairs** and no counterexample can
escape. (ii) *Measurement:* my instrument sweeps the genuinely-all-labeled population — **218 166
(poset, reference-order, element) triples, 0 violations of `b_x ≤ m_x`**, 76 116 strictly lossy,
142 050 equalities.

So: **sound result, misstated population.** Two live consequences: a CI comment asserting coverage it
does not have, and a mis-documented helper that would **silently** under-sweep by 11.06× in posets if reused for
any *label-dependent* property — where the isomorphism argument that rescues it here does not apply.
**Recommendation:** rename to `posets_with_identity_extension` and restate the counts as
"complete up to isomorphism of `(P, e)`", which is both true and the stronger claim.

### F3 — LOW: the `e`-maximum is an equality site too, and goes unnamed

See §1.3. `b_x = m_x` at the `e`-max in **43 842/43 842**. The repair pins only the `e`-min
(6 385/6 385 in its own population). §3.1's falsifier mechanism therefore has a symmetric second
instantiation nobody has written down.

### F4 — LOW: §0's restored quantifier is not the body's

`Closeout` §13 says the quantifiers were restored *"to the body's Finding 3.4 form"*. §12's row and
narrative match the body. **§0 does not**: the body says *"Both objects **the program** has attacked
since mg-8201"*; §0 now says *"both objects **the (A)+(B) route** has attacked since mg-8201"*. §0 is
**narrower** than the body, so it overstates nothing and no correction is required — but the three
sites are not identical, and §13's claim that they are is slightly off.

### F5 — LOW: the strike is wider than the error

The struck sentence ends *"(and the analogous variance tails)"*, which is **true** — the variance
tails are exactly where (B) actually fails on `W_m`, as the repair itself establishes. Striking the
whole sentence removes that true clause along with the false inference. The replacement text and the
§5 annotation both carry the variance half via `(B-cov)`, so **no content is lost**; recorded only so
the strike is not later read as retracting the variance claim.

*(Also noted, not a finding: the CI comment advertises `~8 s`; measured **14.5 s** on this host.)*

---

## 6. Instruments, populations, and predicted-vs-actual exit codes

I built my own instruments rather than re-running the repair's. **Predictions were written down
before execution and are reproduced unedited, misses included.**

### 6.1 `scripts/onethird_mg8a71_audit_instrument.py` — the numeric instrument

Exact `Fraction` arithmetic, stdlib only, no sampling, **25 s** (linear extensions are grown from minimal elements, not filtered out of `n!`). **Population, named:** every labeled
poset on `n = 3, 4, 5` (**19 + 219 + 4 231 = 4 469**, matching A001035), crossed with **every** linear
extension as reference order (**43 842** pairs, **218 166** element-triples), plus `W_m` for
`m = 2,4,6,8,10` enumerated from `L(W_m)`.

| check | predicted | actual |
|---|---|---|
| `W_m` closed forms (4 of them, incl. ratio `1/3`) | 0 mismatches | **0** ✅ |
| `b_x ≤ m_x` | 0 violations | **0** / 218 166 ✅ |
| `b_x = m_x` at the `e`-**min** | all | **43 842/43 842** ✅ |
| `b_x = m_x` at the `e`-**max** | all (`A_x = 0`, the mirror) | **43 842/43 842** ✅ |
| **(F1)** `Σ_x m_x = 2E[inv_e]` | 0 violations | **0** ✅ |
| **(★)** `E[Σdisp²] = 2E[inv_e] + Cross` | 0 violations | **0** ✅ (and *exactly*, where §4 of the target doc reports only `1e−9`) |
| Jensen `E[disp²] ≥ E[disp]²` | 0 violations | **0** ✅ |
| valid half `Σb² ≤ (max m)·2E[inv]` | 0 violations | **0** ✅ |
| struck inference as a finite statement | fails on a nonzero, large fraction | **3 102 / 43 692** pairs ✅ |
| **exit code** | **0** | **0** ✅ |

**Zero missed predictions.** The `e`-max prediction is the one that was not a restatement of the
repair, and it held.

The smallest witness to the struck inference's failure the sweep finds is **`n = 3`**: `P = {1 < 2}`,
`e = (1, 0, 2)`, where `max_x m_x = 2/3` but `Σ_x b_x² = 2/9 < 4/9`. The defect does not need `W_m`;
it fails on three elements.

### 6.2 `scripts/onethird_mg8a71_live_claim_control.py` — the new control, demonstrated against a defective commit

The numeric control **cannot see the defect it was written for**: the defect was never a false number,
it was a false sentence in live body text. So the new control is document-level. It classifies every
line of `OneThird-L1b-Spread-Locality.md` as live or *marked* (inside a `~~`-struck / `ANNOTATION` /
`RE-DERIVATION` blockquote — the corpus's convention for retaining a refuted claim as a record),
groups live text into paragraphs, and applies four signatures of the refuted `m_x`-falsifier
inference. **Population: one file, all 464 lines, 42 live paragraphs — not a sample.**

**Demonstrated against a commit where the defect is still present**, as the brief requires:

| run | predicted | actual |
|---|---|---|
| `1b00147^` (pre-repair; §2.3 error live in the body) | exit **1**, §2.3 flagged NEW | **exit 1** — `S1-jensen-falsifier` **and** `S2-hinges-on-degree` both NEW at §2.3 ✅ |
| `HEAD` (post-repair) | exit **0**, exactly the 2 baseline sites | **exit 0** — `S3` at §3.2, `S4` at §5, no new sites ✅ |

The baseline is **not** a way of tolerating the two sites: it is **F1, made executable**. When F1 is
fixed the control fails with *"baseline site disappeared"*, forcing a re-baseline to zero — a control
that notices being repaired, not just being broken.

### 6.3 Other commands, predicted and run

| command | predicted | actual |
|---|---|---|
| `python3 scripts/onethird_mgfccb_direction_check.py` (the repair's) | exit 0 | **0** ✅ |
| `git merge-base --is-ancestor cd261b9 main` | 0 | **0** ✅ |
| `git merge-base --is-ancestor b169561 main` | 0 | **0** ✅ |

---

## 7. Floor, not scope: what I audited that nothing asked for

The brief names the direction, the consumers, the cross-doc claims, and the over-correction risk. Two
things I chose that no list names:

1. **The identities under the corrected statement.** The repair verifies the *inequality* and leaves
   the *identities* alone. But the corrected §2.3 sentence — *"`max_x m_x = O(1)` ⟹
   `Σ_x E[disp(x)]² = O(E[inv_e])`"* — depends on **(F1) `Σ_x m_x = 2E[inv_e]`**, and (F1) is exactly
   the kind of "one line, immediate" identity that gets asserted and never re-checked. If (F1) were
   false, the repair would have replaced a wrong sentence with another wrong sentence, and the
   direction check would not notice. I re-verified (F1) and **(★)** exactly on 43 842 pairs. Both
   hold. *(The target doc's §4 reports (★) verified only to `1e−9` on `n ≤ 5`; this upgrades it to
   exact rational equality on a larger population.)*
2. **The population behind the repair's own headline number.** "31 625/31 625, zero violations" is a
   bare total. Naming the population is what turned it into **F2** — a claim of exhaustiveness over
   a set 11.06× larger in posets than the one actually swept. The number is right; the sentence
   around it is not.

I also checked the `e`-max equality case (**F3**) and re-read the target doc's §§1–4 for any *other*
inequality whose direction is load-bearing; §1.1's band bound `(2/3)k ≤ d_k ≤ (2/3)k + (n−1)/3` and
§1.2's descent to `‖r‖² ≥ (n−1)³/1152` both use their bounds in the direction they need (the **upper**
band bound to force `r_k < 0` on the bottom eighth, the **lower** on the top quarter), and are
untouched by this repair.

---

## 8. Routing

* **To pm-onethird:** F1 (strike the two remaining live sites in `Spread-Locality` §3.2 and §5 rec 2)
  and F2 (rename/re-document `all_posets`, restate the CI comment's population). Neither changes a
  proven statement.
* **Not routed:** F3, F4, F5 — recorded here, no action required.
  *(pm-onethird routed them anyway, under mg-069f, and all three were actionable. See §9.)*
* **Confirmed and closed:** the direction, the `W_m` forms, the §3.1 trap, the cross-doc ledger, and
  the untouched locality-lemma mathematics.

---

---

## 9. Disposition (added 2026-07-31, mg-069f)

All five findings closed. Full record and enumeration of what was re-checked:
`docs/OneThird-mg8a71-VerdictRepairs-Closeout.md`.

| # | finding | disposition |
|---|---|---|
| **F1** | two consumers still assert the refuted inference in live body text | **CLOSED** — §3.2's *"Equivalently"* display and §5 rec 2's converse both **struck at the site**, retained struck, corrected text stated immediately. The live-claim control's baseline is now **empty**; it failed with *"baseline site disappeared"* first, exactly as designed. |
| **F2** | the control names a population it does not sweep | **CLOSED** — counts independently re-derived (404 → 6 385 → 31 625; 4 469 → 43 842 → 218 166; A001035 confirmed), every misstatement corrected (2 doc sites, 1 CI comment, the script header), `all_posets` renamed `posets_with_identity_extension`, `all_labelled_posets` added, and `poset_family(n, label_dependent=…)` now forces each call site to state which family it needs. Both scripts assert their population counts. |
| **F3** | the `e`-maximum is an equality site too, and goes unnamed | **CLOSED** — named in §3.1 as the falsifier's mirror instantiation (an `e`-max element *leading* a frozen chain), and pinned by a new check in `onethird_mgfccb_direction_check.py` (6 385/6 385 at each end). Also measured: at every **interior** `e`-rank the equality is *not* forced (both equalities and strict losses occur), which is the fact §3.2's failure actually rests on. |
| **F4** | §0's restored quantifier is narrower than the body's; §13 says they are identical | **CLOSED, and slightly wider than reported** — corrected in `OneThird-Bbias-Locality-Lemma.md` §13. F4 states *"§12's row and narrative match the body"*; re-read at the far end, **the §12 row does not** (it carries the same *"(A)+(B) route"* as §0) and the §12 narrative drops the clause entirely. Text left narrow; only the description of the fix was wrong. |
| **F5** | the strike is wider than the error — it removed a true *variance tails* clause | **CLOSED** — the clause is **restored as live text** in §2.3 with the two-term decomposition and the `W_m` numbers that make it true, and the strike is explicitly recorded as not retracting it. |

*Also fixed, from the parenthetical at the end of §5:* the CI comment advertised `~8 s` for the
mg-fccb check; measured here at **14.5 s**, matching this audit and not the comment. Corrected.

---

*Deliverable for mg-8a71. Independent audit, pre-filed in the same action as its parent (mg-fccb).
Computation: `scripts/onethird_mg8a71_audit_instrument.py` (25 s, exact) and
`scripts/onethird_mg8a71_live_claim_control.py` (instant, demonstrated failing on `1b00147^`).*
