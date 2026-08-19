# Closeout of the mg-8a71 audit verdict (mg-069f)

**Target:** the five findings of `docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md` (mg-8a71,
landed `2697c07`), which audited the mg-fccb §2.3 direction repair (`1b00147`) as **GREEN on the
mathematics, AMBER on the remediation**.

**Verdict of this deliverable: all five closed.** F1, F2, F5 required text or code changes; F3
required naming a mechanism the corpus had measured but not written down; F4 required correcting a
description and turned out to be **wider than reported**. Nothing here touches the mathematics —
which mg-8a71 confirmed and this deliverable did not re-open beyond the checks enumerated in §5.

---

## 0. The one-line summary of what was wrong, and what this changes

The audited repair **stated a remediation standard** — *"an annotation leaves the wrong claim in the
body"* — struck one site by it, and left the same standard unapplied at two sites **it had itself
proved false**. Both are now struck at the site. Separately, its control **named a population 11.06×
larger than the one it swept** (4 469 posets named, 404 swept — *poset* grain; the figure here read
`6.9×`, the pair/triple ratio, until mg-1d03 corrected it per mg-0242 finding G3); the population is
now stated correctly at every site, the helper is
renamed to what it returns, and both scripts **assert their own population counts** so the gap cannot
reopen silently.

| finding | severity | disposition |
|---|---|---|
| **F1** — §3.2's *"Equivalently"* and §5 rec 2's converse still asserted in live body text | MEDIUM | **CLOSED** — struck at the site, corrections stated immediately; control re-baselined to zero |
| **F2** — the control names 4 469 labelled posets and sweeps 404 | MEDIUM | **CLOSED** — counts re-derived independently, 4 sites corrected, helper renamed, `poset_family(n, label_dependent=…)` added, counts asserted |
| **F3** — the `e`-maximum is an equality site too, unnamed | LOW | **CLOSED** — named in §3.1 as the mirror falsifier; pinned by a new check; the e-max assertion is now a failure condition, not just a printed number |
| **F4** — §0's restored quantifier is narrower than the body's; §13 claims identity | LOW | **CLOSED and widened** — F4 says *"§12's row and narrative match the body"*; re-read at the far end, **neither does** |
| **F5** — the strike removed a **true** *variance tails* clause | LOW | **CLOSED** — clause restored as live text, with the decomposition and the `W_m` numbers that make it true |

---

## 1. F1 — the two live sites, struck at the site

Both sentences were **proved false by the deliverable that left them standing**, and both lived in
body text with only an annotation below. Struck by mg-fccb's own stated rule, retained struck so the
corpus keeps the record, with the correct statement immediately after.

**§3.2** — struck: *"Equivalently: can `max_x m_x = ω(1)` (indeed `Θ(n)`) with `E[inv_e] = O(n)`,
δ < 1/3, width 3?"* The replacement states what the second display actually is: a **strictly stronger**
question, strictly stronger in the *unhelpful* direction — `W_m` answers it **yes** while (B)'s
deterministic part holds there at ratio exactly `1/3`, so a positive answer refutes nothing. The
element-level question that does the job is the **bias** one, `max_x b_x = ω(1)`, i.e. the negation of
mg-a58f's **(EQ)** — and even that governs only the deterministic half.

**§5 recommendation 2** — struck: *"If it does not exist, that non-existence **is** (B)."* The
replacement states the correct direction: non-existence is **necessary but not sufficient**. §3.1
proves *cross ⟹ (B) false*; the converse does not follow, because the cross falsifies the
**deterministic** term alone and `E[Σ_x disp²]` has two. On `W_m` the deterministic term is healthy
and **(B) fails anyway, through the variance term** — the configuration a non-existence argument
cannot see. Closing the hunt would leave **(B-cov)** open.

Recommendation 2 also picked up F3's mirror case, since the hunt has two shapes, not one.

### 1.1 The control noticed being repaired, which is what it was for

mg-8a71 built `scripts/onethird_mg8a71_live_claim_control.py` with F1's two sites as a **named
baseline** and made a baseline site *disappearing* a failure. That is what happened: the first run
after the strikes failed with *"baseline site disappeared (re-baseline this control)"* at both sites.
Baseline is now **empty** and the control is a plain assertion — the refuted inference is asserted in
live body text **nowhere** in that document.

**Two tightenings were needed, and each closed a real hole:**

1. **Inline `~~struck~~` spans now count as marked.** §5 rec 2 is one sentence of a numbered-list
   item; striking it required sentence-granularity marking, which the control did not understand.
2. **A blockquote that merely *declares* `STRUCK` is no longer exempt on the strength of its label.**
   Found by mutation: deleting the `~~` markup from the §3.2 fix while keeping the "STRUCK" heading
   left the claim rendering as live text, and the control **passed**. Strike-marked blocks are now
   checked with inline strikes removed, so the label has to be backed by the markup. Only
   `ANNOTATION` / `RE-DERIVATION` blocks stay exempt — commentary about a refuted claim has to quote
   it.

---

## 2. F2 — the population named vs. the population swept

**Counts re-derived from scratch before accepting the finding** (not taken from the audit):

| n | posets with identity as a linear extension | labelled posets on `[n]` (A001035) |
|---|---|---|
| 3 | 7 | 19 |
| 4 | 40 | 219 |
| 5 | 357 | 4231 |
| **total** | **404** → 6 385 pairs → **31 625** triples | **4 469** → 43 842 pairs → **218 166** triples |

Every figure matches mg-8a71's. **31 625 is 14.5% of the population that was named.**

**The verdict is unaffected and the corrected statement is the stronger one.** `b_x` and `m_x` are
invariant under simultaneous relabelling of `(P, e)`, and relabelling any pair by `e`-rank lands it in
the identity-extension family — so the 404 are a **complete set of representatives of `(P, e)` pairs
up to isomorphism**, and the sweep is exhaustive for a label-independent property. Confirmed against
an enumeration, not left as an argument: the all-labelled sweep is **0 violations in 218 166 triples**.

**Corrected at every site the wrong population appeared:** `OneThird-L1b-Spread-Locality.md` §2.3's
machine-checked note, `OneThird-mgd112-DroppedVerdict-Closeout.md` §2.2 and §6, the CI step comment,
and the script's own header.

**The helper — the part that would have bitten later.** `all_posets()` is renamed
**`posets_with_identity_extension()`**, documented with the table above and with when the isomorphism
argument does *not* apply. `all_labelled_posets()` is added (the S_n-orbit of that family; verified to
return 19/219/4231), and both are reached through:

```python
poset_family(n, *, label_dependent)
```

so a call site cannot pick a family without stating which case it is in. This is the actual danger
mg-8a71 named: for a **label-dependent** property the old helper would have under-swept **11.06× in
silence** — *poset* grain, 404 of 4 469; **6.90×** if the property is counted per element triple —
and nothing at the call site said so.

**Both scripts now assert their population counts** (404 / 6 385 / 31 625 and 4 469 / 43 842 /
218 166, the latter checked per-`n` against A001035). A generator drifting off its stated family now
fails instead of quietly sweeping less.

---

## 3. F3 — the `e`-maximum, and what makes the two ends special

The equality `b_x = m_x` holds iff `min(E[A_x], E[B_x]) = 0` — the inversion mass is **one-sided**.
That is forced at the `e`-min (`B_x = 0`) and, by mirror symmetry, at the `e`-max (`A_x ≡ 0`). §3.1
now names both: **an `e`-maximal element that *leads* an entire incomparable frozen chain a constant
fraction of the time refutes (B) exactly as an `e`-minimal element that trails one does.**

Measured at both ends: **6 385/6 385** each in the identity-extension family, **43 842/43 842** each
over the full labelled population.

**One thing checked that the audit did not, and that §3.2's failure actually rests on.** Equality is
*forced* only at the two ends, but it is not *rare* elsewhere — it occurs at interior positions
whenever the mass happens to be one-sided. At **every** interior `e`-rank the sweep finds both
equalities and strict losses (at `n = 3`, `e`-rank 1: **11 of 20** pairs equal, 9 strict). So the
correct statement is *forced at the ends, incidental in the middle* — the naive "equality only at the
ends" would be false, and the reason §3.2's generalisation to `max_x` fails is the absence of a
**guarantee**, not the absence of equality.

The e-max result was already **measured and printed** by the audit instrument but was **not** a
failure condition. It is now, since §3.1's body text rests on it.

---

## 4. F4 — confirmed, and wider than reported

§13's row 2 said the quantifiers were restored *"to the body's Finding 3.4 form"* at all three sites.
Read at the far end:

| site | phrasing | vs the body |
|---|---|---|
| body §3.4 | *"the weakest of the three sufficient conditions **the program has** … both objects **the program** has attacked since mg-8201"* | — |
| §0 | *"… both objects **the (A)+(B) route** has attacked since mg-8201"* | narrower |
| §12 attempt-index row | identical to §0 — *"the (A)+(B) route"* | narrower |
| §12 narrative | *"the weakest of the three … we hold **on this route**"*; the *"both objects … since mg-8201"* clause is **absent** | narrower still |

F4 states that *"§12's row and narrative match the body"*. **The §12 row does not** — it carries the
same *"(A)+(B) route"* as §0 — and the narrative dropped the clause rather than matching it. So the
finding holds at **three** sites, not one; only the description of the fix was ever wrong.

**Text left as is.** Every site is at most as strong as what §3.4 proves, which is the direction that
matters. Editing proven-safe text a third time to chase verbal uniformity is the **over-correction**
risk this audit family exists to name — the same risk that produced F5.

---

## 5. F5 — restoring what the strike over-reached

The struck §2.3 sentence ended *"(and the analogous variance tails)"*. That clause is **true**, and it
is where (B) actually fails. Restored as live text in §2.3, with what makes it true:

```
E[Σ_x disp²]  =  Σ_x Var(disp_σ(x))  +  Σ_x b_x²
```

On `W_m`, `Var(pos_σ z) = m(m+2)/12 = Θ(n²)` against `E[inv_e] = Θ(n)`, while the second sum sits at
ratio exactly `1/3`. So the variance half survives the strike intact and is the live residual — §2.2's
`Cross`, mg-dcae's **(B-cov)**. Only the *degree* half died. Recorded explicitly so the strike is not
later read as retracting the variance claim.

---

## 6. What I checked, enumerated

Per the verdict's instruction to enumerate. **Predictions were written before running.**

### 6.1 Populations — every one my controls NAME

| control | population NAMED | population SWEPT | agree? |
|---|---|---|---|
| `onethird_mgfccb_direction_check.py` | 404 posets / 6 385 pairs / 31 625 triples | **404 / 6 385 / 31 625**, asserted in-script | ✅ (was *"ALL posets"*, **11.06× too large at POSET grain** — this is F2) |
| `onethird_mg8a71_audit_instrument.py` | 4 469 posets / 43 842 pairs / 218 166 triples | **4 469 / 43 842 / 218 166**, asserted in-script and per-`n` against A001035 | ✅ correct as written; now enforced |
| `onethird_mg8a71_live_claim_control.py` | *"one file, all of it"* | **539/539 lines**, each in exactly one of {paragraph, quote, heading, exempt-annotation, blank}, asserted to sum | ⚠️ **headings were silently dropped** while the docstring claimed "all of it" — my own instance of the F2 defect, found by applying F2's test to myself. Fixed: headings are scanned, and coverage is now proven rather than asserted. |

> **CORRECTION ANNOTATION (2026-08-05, mg-1d03 — mg-0242 finding G3).** Two figures in the table
> above were wrong, and this is the table whose entire purpose is to report NAMED vs SWEPT. Recorded
> here rather than silently overwritten, because what the figures were is the finding:
>
> * row 3 read ~~*"537/537 lines"*~~. The control sweeps **539**. *(Population: every line of
>   `docs/OneThird-L1b-Spread-Locality.md`. Grain: one newline-split element — `wc -l` reports 538
>   newlines, so 539 elements.)*
> * row 1 read ~~*"6.9× too large"*~~. F2's gap is **11.06×** at the grain row 1 is about.
>   *(Population: labelled posets on `n = 3,4,5` versus those with the identity as a linear
>   extension. Grain: POSETS — 4 469/404 = 11.06×. 6.9× is a real number from an adjacent grain:
>   43 842/6 385 = 6.87× over PAIRS, 218 166/31 625 = 6.90× over TRIPLES, which is why it read as
>   plausible.)*
>
> **Every other figure in this table is now machine-checked** by calling the generator, not by
> reading the row: `scripts/onethird_mg0242_population_census.py` part (5b) parses rows 1–2 out of
> this markdown and compares all six integers against enumerated counts. A table that got its own
> row wrong had not earned trust on its neighbours. Both figures were held by that script's
> `BASELINE`; correcting them fired its re-baseline gate, and the baseline is now **empty**.

### 6.2 Exit codes — predicted before running, all five hit

| run | predicted | actual |
|---|---|---|
| live-claim control at HEAD (both sites struck) | 0 | **0** ✅ |
| live-claim control on `1b00147^` (pre-repair, §2.3 live) | 1 | **1** ✅ (S1 + S2 at §2.3) |
| live-claim control on `1b00147` (mg-fccb HEAD, F1's two sites) | 1 | **1** ✅ (S3 at §3.2, S4 at §5) |
| **mutant:** delete §3.2's `~~` markup, keep the "STRUCK" label | 1 | **0 ✗ → fixed → 1** ✅ |
| **mutant:** delete §5 rec 2's `~~` markup | 1 | **1** ✅ |
| `onethird_mgfccb_direction_check.py` | 0 | **0** ✅ (14.5 s) |
| `onethird_mg8a71_audit_instrument.py` | 0 | **0** ✅ (24 s) |

**One missed prediction, recorded rather than quietly fixed.** The `~~`-deletion mutant on §3.2 was
predicted to fail the control and **passed**. That is the finding in §1.1's item 2: a block could
*declare* itself struck without the claim being struck. Predicting it and being wrong is what
surfaced it; had I not run the mutant, the F1 fix would have shipped with a control that could not
tell it from a cosmetic edit.

### 6.3 Re-derived rather than accepted from the audit

* **All F2 counts**, independently: 7/40/357 → 404 → 6 385 → 31 625, and 19/219/4231 → 4 469 →
  43 842 → 218 166, the latter matched against A001035.
* **The `e`-max equality** at both population sizes, and the interior-position measurement (§3) that
  the audit did not take.
* **F4's far end**, verbatim at all four sites — which is how F4 turned out to be wider than reported.
* `all_labelled_posets()` returns exactly 19/219/4231, so the new generator is the population it
  claims and not a superset with duplicates.

### 6.4 Not re-checked, and named as such

* The **mathematics** — `b_x ≤ m_x`, the four `W_m` closed forms, (F1), (★), the §3.1 trap. mg-8a71
  re-derived these by hand and machine-confirmed them on 218 166 triples; both controls still run in
  CI and still pass. **Not independently re-derived here.**
* mg-8a71's **cross-doc ledger** (11 of 18 rows re-opened by the auditor). Only F4's rows were
  re-read here.
* The audit's `~8 s` → measured **14.5 s** discrepancy for the mg-fccb check: **reproduced** (14.5 s
  on this host) and the CI comment corrected.

---

## 7. Files touched

| file | why |
|---|---|
| `docs/OneThird-L1b-Spread-Locality.md` | F1 (§3.2, §5 rec 2 struck), F3 (§3.1 mirror falsifier), F5 (§2.3 variance clause restored), F2 (§2.3 population note) |
| `docs/OneThird-mgd112-DroppedVerdict-Closeout.md` | F2 (§2.2 table + correction note, §6 self-check row), F3 (equality row) |
| `docs/OneThird-Bbias-Locality-Lemma.md` | F4 (§13 row 2 + correction block) |
| `docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md` | §9 disposition of all five findings |
| `scripts/onethird_mgfccb_direction_check.py` | F2 (rename, `poset_family`, `all_labelled_posets`, asserted counts), F3 (e-max check) |
| `scripts/onethird_mg8a71_live_claim_control.py` | F1 (baseline → empty), inline-strike handling, label-vs-markup tightening, coverage proof |
| `scripts/onethird_mg8a71_audit_instrument.py` | asserted population counts; e-max made a failure condition |
| `.github/workflows/script-controls.yml` | F2 population comment, `~8 s` → 14.5 s, baseline-now-empty comment, exit-code table |

---

## 8. What this deliverable did not do

* It did **not** re-open the mathematics; §6.4 names exactly what was taken on the audit's authority.
* It did **not** re-widen the F4 quantifiers to the body's phrasing. Three narrower-than-proven
  statements are a correct record; the fix was to the sentence describing them.
* It did **not** add a control for the *general* proposition "no refuted claim survives in body text
  anywhere in the corpus". The live-claim control is one file, by design, and says so.

* It did **not** touch **§5 recommendation 1**, and there is a live disagreement there worth naming
  rather than absorbing. The verdict routed two sites; mg-8a71's consumer table adjudicated rec 1 as
  *"not false, only mis-priced; annotation is the right instrument"*. But mg-fccb's own annotation
  lists **two** defects in rec 1, and the first is not a pricing one: *"Since `max_x m_x = Θ(n)` does
  not falsify (B), `max_x m_x` is not the quantity (B) hinges on, and **rec 1 is not a pin**."* By
  that reasoning the live sentence *"This is the single pin"* is **false**, not merely expensive — and
  the F1 standard (strike what you have proved false) would reach it. **Not acted on**: the verdict
  named two sites and the audit dispositioned this one explicitly, and reversing an adjudication is
  not this deliverable's call. **Flagged for pm-onethird** as the one place where applying F1's rule
  strictly would go further than the verdict asked. It is also the reason the live-claim control's
  signature set does not include *"single pin"* — adding it would encode a disposition that has not
  been made.

---

*Deliverable for mg-069f, closing the mg-8a71 verdict. Computation: the three CI controls named above,
all stdlib-only and exact; no new script. One prediction missed (§6.2) and recorded.*
