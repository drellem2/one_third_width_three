# mg-0242 G3 + G4 — repair (mg-1d03)

**Scope.** mg-0242 findings **G3** (two named-vs-counted gaps the mg-069f repair *introduced*) and
**G4** (five remediation instruments in use, one named as the standard). mg-cd04 closed G1 and G2 and
stated explicitly that *"G3 and G4 are NOT addressed here and remain open"*. They were never ticketed
until mg-1d03.

**A pre-filed independent audit (mg-5854) is BLOCKED on this item.** Every count below therefore
names its **POPULATION** and the **GRAIN** of the value, so that a reader who did not do the work can
falsify it by re-running one command.

---

## 0. PREDICTIONS — written before any new measurement was taken

Recorded first, in their own commit, and **not revised afterwards**. A refuted prediction is a result.

Observed before this section was written (so *not* predictions, and listed here to keep the line
honest): the two G3 figures as reported by mg-069f's audit and reproduced by the existing census run
(`537` named / `539` swept; `6.9x` named / `11.06x` computed); the four `6.9x` sites in
`scripts/onethird_mgfccb_direction_check.py`; the ledger's own instrument column in
`scripts/onethird_mg0242_struck_vs_refuted.py`.

| # | prediction | population / grain | outcome |
|---|---|---|---|
| P1 | The **other two rows** of closeout §6.1 — the rows this repair is *not* fixing — are **correct** when the figure is obtained by calling the helper rather than reading the table. **0 gaps among the 6 figures.** | population: the 6 numerals in rows 1–2 of §6.1 of `docs/OneThird-mg8a71-VerdictRepairs-Closeout.md`; grain: one integer per (generator × {posets, pairs, triples}) | **✅ HIT on the claim, MISSED on the population.** 0 gaps — but the population is **12** figures, not 6: each row states the triple **twice**, once in the NAMED cell and once in the SWEPT cell. I counted the rows and not the cells. Recorded, not corrected. |
| P2 | The **other four rows** of the `posets_with_identity_extension` docstring table are **correct** when counted. **0 gaps among the 6 per-`n` figures.** | population: the per-`n` rows `3/4/5` of the docstring table in `scripts/onethird_mgfccb_direction_check.py`; grain: one integer per (n × {this family, A001035}) | **✅ HIT.** 0 gaps among the 6 per-`n` figures (7/40/357 and 19/219/4231); the 2 totals-row integers are also checked and also correct. |
| P3 | With both G3 numbers corrected and the census `BASELINE` **left untouched**, the census **exits 1** with two `BASELINE GAP CLOSED` lines — the re-baseline gate firing, not a regression. | population: one process exit code | **❌ REFUTED, and the refutation is a finding.** Exit 1 ✅ but **one** `BASELINE GAP CLOSED` line, not two. See §2. |
| P4 | With both entries then removed from `BASELINE`, the census **exits 0** and both comparisons pass as ordinary `OK` checks. | population: one process exit code | **✅ HIT.** Exit 0, `baseline: 0 known gap(s) tolerated; 0 seen`. |
| P5 | The ledger in `onethird_mg0242_struck_vs_refuted.py` prints *"the repair used three, and named only one"* immediately above a tally that lists **five** distinct instrument keys — a named-vs-counted error **inside the line that reports the count**, the same class as G3. | population: part (A)'s `BY INSTRUMENT` block; grain: distinct instrument keys | **✅ HIT.** The line read *"BY INSTRUMENT (the repair used three, and named only one)"* directly above a tally printing **five** keys. |
| P6 | The live-claim control's PASS readout contains **0** occurrences of the word *instrument* — i.e. a green run says nothing about which of the five remediations it can see. | population: the `main()` report block of `scripts/onethird_mg8a71_live_claim_control.py`; grain: word occurrences | **✅ HIT.** `grep -c instrument` over the whole file: **0**. |
| P7 | **Deletion-without-declaration is invisible to every control in CI.** A mutant that deletes a refuted claim outright — no `~~`, no annotation, no *"is struck"* — leaves the live-claim control at exit **0** *and* the declared-strike control at exit **0**. | population: 2 process exit codes over the mutated corpus | **✅ HIT.** live-claim exit **0**, declared-strike **0** hits. |
| P8 | **Deletion-declared-as-a-strike is visible to exactly one control.** The same deletion, with the *"is struck with it"* declaration restored and no markup, leaves the live-claim control at exit **0** and trips the declared-strike control (≥1 unbaselined hit). | population: 2 process exit codes over the mutated corpus | **❌ REFUTED on the first half.** Declared-strike trips (**1** hit) ✅, but live-claim exits **1**, not 0. See §3.3. |
| P9 | **Rewrite-in-place and rewrite+annotation are indistinguishable from strike-at-site to both controls.** Both mutants exit **0** on both controls. | population: 4 process exit codes over the mutated corpus | **✅ HIT.** All four exit codes 0; the three instruments fall in one indistinguishable group. |
| P10 | After all repairs, all five controls in `script-controls.yml` that touch this arc exit **0**: census, struck-vs-refuted, live-claim, declared-strike, direction check. | population: 5 process exit codes at HEAD | **✅ HIT.** census 0, struck-vs-refuted 0, live-claim 0, declared-strike 0, direction check 0 (plus audit instrument 0, identity re-run 0). |
| P11 | Sweeping `docs/`, `scripts/` and `.github/` for the literal `6.9x`/`6.9×` in a **poset-grain** claim finds **more than the one baselined site** — the "corrected at every site" claim will again be one or more sites short. | population: all `*.md`, `*.py`, `*.yml` under `docs/`, `scripts/`, `.github/`; grain: one site = one line asserting the ratio of a poset count | **✅ HIT, and by a wide margin.** **9** poset-grain sites, not 1. See §2.2. |
| P12 | The five instruments partition the ledger exactly: 4 + 2 + 2 + 1 + 1 = **10 = REFUTED**, with no ledger entry carrying a sixth instrument. | population: the 10 ledger entries of part (A); grain: one instrument key per entry | **✅ HIT.** 4 + 2 + 2 + 1 + 1 = 10 = REFUTED; computed, and a sixth instrument now fails the run. |

**Score: 10 hits, 1 partial, 2 refuted halves (P3, P8).** Both refutations produced changes to the
work; neither was revised to agree with the result.

---

## 1. Verdict

| finding | verdict |
|---|---|
| **G3** — closeout §6.1 names 537 lines where the control sweeps 539 | **CLOSED at the site**, and the whole table is now machine-checked, not just the row that was wrong |
| **G3** — direction-check docstring labels the 404 → 4 469 POSET row *"6.9× larger"* | **CLOSED at the site**, at **9** sites rather than 1, each now stating its **grain** |
| **G4** — five remediation instruments, one named as the standard | **CLOSED**: all five named with a rank and an acceptability rule; the detectability matrix is **measured**, not asserted; and both controls now say what their green does *not* mean at the point they report it |

Both G3 gaps were held by `scripts/onethird_mg0242_population_census.py`'s `BASELINE`. Correcting
them fired its re-baseline gate; the keys are removed and the baseline is now **empty**.

---

## 2. G3 — the two figures, and the seven more nobody had counted

### 2.1 `537` → `539`

**Population:** every line of `docs/OneThird-L1b-Spread-Locality.md`. **Grain:** one newline-split
element. `wc -l` reports 538 newlines ⇒ **539** elements, and the control's own bucket census sums to
539 (`heading 17 + blank 73 + paragraph 282 + quote 79 + exempt_annotation 88`).

Corrected in closeout §6.1 row 3, with a **correction annotation** recording what the cell read.

**Then the neighbours.** The ticket's instruction was *"check the other rows of that table by calling
the helper rather than reading the figure — a table that got its own row wrong has not earned trust
on its neighbours."* Census **part (5b)** now parses §6.1 rows 1–2 out of the markdown and compares
every integer against a count obtained by calling the generator:

```
[OK  ] §6.1 NAMED cell, onethird_mg8a71_audit_instrument.py  [4469, 43842, 218166]
[OK  ] §6.1 SWEPT cell, onethird_mg8a71_audit_instrument.py  [4469, 43842, 218166]
[OK  ] §6.1 NAMED cell, onethird_mgfccb_direction_check.py      [404, 6385, 31625]
[OK  ] §6.1 SWEPT cell, onethird_mgfccb_direction_check.py      [404, 6385, 31625]
figures parsed from §6.1 rows 1-2: 12
```

**P1 partly missed.** I predicted 6 figures; there are **12**, because each row names its triple
twice — once as NAMED and once as SWEPT. That is the table's whole design and I still counted rows
instead of cells. Left as filed.

Two parsing hazards were real and are handled at the site, not worked around: the corpus separates
thousands with U+202F (`6 385` is one number), and row 2 cites **A001035**, whose digits are an OEIS
id and not a population. `cell_numbers()` drops a digit run glued to a letter rather than counting it
as `1035`. Section anchoring is on `### 6.1` rather than first-match, because §6.2 and §7 carry rows
keyed by the same script names.

### 2.2 `6.9×` → `11.06×`, at nine sites, each with its grain named

**The ratio is grain-dependent, and that is the entire mechanism of the defect:**

| grain | ratio |
|---|---|
| **POSETS** | 4 469 / 404 = **11.06×** |
| PAIRS `(poset, reference-order)` | 43 842 / 6 385 = 6.87× |
| TRIPLES `(poset, order, element)` | 218 166 / 31 625 = 6.90× |

`6.9×` is a **real number from an adjacent grain**, which is exactly why it read as plausible on a
poset row for three commits.

**P11 hit, and by a wide margin.** mg-069f's audit found the one docstring row. A sweep of `docs/`,
`scripts/` and `.github/` for the literal finds **9 poset-grain sites**, all corrected, each now
naming its grain:

| site | was |
|---|---|
| `scripts/onethird_mgfccb_direction_check.py` docstring table, totals row | `(6.9x larger)` |
| `…direction_check.py` module docstring, *"named a population 6.9x larger"* | poset counts, 4 469 vs 404 |
| `…direction_check.py` `posets_with_identity_extension`, *"under-sweep by 6.9x"* | grain unstated |
| `…direction_check.py` `poset_family`, *"the 6.9x gap between the two families"* | families are poset sets |
| `scripts/onethird_mg0242_population_census.py` module docstring | *"NAMED 4 469 posets and SWEPT 404 — a 6.9x gap"* |
| `docs/OneThird-mg8a71-VerdictRepairs-Closeout.md` §0 | *"named a population 6.9× larger than the one it swept"* |
| `…Closeout.md` §4 | *"would have under-swept 6.9× in silence"* |
| `…Closeout.md` **§6.1 row 1** | *"(was ALL posets, 6.9× too large)"* — **in the same table as the 537** |
| `docs/OneThird-mgd112-DroppedVerdict-Closeout.md` §5 | *"under-swept 6.9× in silence"* |
| `.github/workflows/script-controls.yml` | *"This is 6.9x the family the step above sweeps"* |

**Three sites were deliberately NOT touched, and this is the F4 model case applied.**
`docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md` (mg-8a71's own filed report) carries the
figure at lines 19, 250 and 358. That document is **the record of a filed finding**, not live
instrument or closeout text; mg-cd04 set the precedent explicitly (*"It did not rewrite mg-0242's
findings"*), and two of the three are defensible at pair/triple grain anyway. Rewriting another
audit's filed text to agree with a later repair is the over-correction this arc exists to avoid.
Likewise untouched: every quotation of the defect inside
`docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md`, which is what an audit document is
for.

Also untouched, and for the same reason: `docs/OneThird-mg0242-G1G2-Repair.md` §5 and
`docs/OneThird-mg9a19-…-IndependentAudit.md` §5 both say the G3 gap is *"untouched and still
baselined"*. **True when written, and correctly scoped to their own commit.** Re-editing a dated
record to track a later repair is how a corpus loses the ability to say when it knew something.

### 2.3 The check that could not recognise its own repair — P3's refutation

**Predicted:** the census, run with its `BASELINE` intact against the corrected documents, exits 1
with **two** `BASELINE GAP CLOSED` lines. **Actual: exit 1, but one line.**

The 537→539 gate fired. The ratio gate did **not**. The old check computed
`round(4469/404, 1)` = `11.1` and compared it to the docstring literal, so:

* writing the correct figure **`11.06x`** ⇒ `11.06 ≠ 11.1` ⇒ still reported as an open gap;
* the **only** string it would have accepted as the repair was **`11.1x`** — a figure *less* precise
  than the finding it closes, and one that appears nowhere in mg-069f's audit, which says `11.06×`.

So the control that held G3b **could not recognise a correct repair of G3b**. It is now compared at
**two decimal places** — not a style preference: 2 dp is the precision at which the figure's *grain*
is recoverable from the figure itself, and coarsening is what let a triple-grain number pass as a
poset-grain one in the first place.

---

## 3. G4 — five instruments, one standard, and what the green actually means

### 3.1 All five, named

Counted over the 10-entry ledger (**population:** the ledger of `part (A)`; **grain:** one instrument
per entry; the five partition it exactly, 4 + 2 + 2 + 1 + 1 = 10 — **P12**):

| # | instrument | uses | rank | keeps a record? |
|---|---|---|---|---|
| 1 | **strike-at-site** | 4 | **PREFERRED** | yes — the wrong text stays, visibly wrong, inside `~~` |
| 2 | **rewrite + annotation** | 2 | acceptable | yes — an ANNOTATION block quotes what was there |
| 3 | **rewrite-in-place** | 2 | acceptable *only* under §3.2's condition | **no** |
| 4 | **deletion declared as a strike** | 1 | **NOT ACCEPTABLE** — the defect, not an instrument | claims one, makes none |
| 5 | **none (flagged and routed)** | 1 | acceptable *only* when routed | the claim stays live and is flagged |

### 3.2 Which is preferred, and when each is acceptable

**Strike-at-site is the standard.** Use it whenever the false text is a **sentence or clause a reader
could still act on**: the reader sees what was believed and that it is no longer believed, at the one
place they would look for it. It is the only instrument where the record and the site are the same
object, so it cannot drift apart from what it documents.

**Rewrite + annotation is acceptable when correct text must stand in the same position.** A table
cell, a population clause, a figure inside an otherwise-true sentence — striking these and writing
the replacement beside them makes the table or sentence unreadable, and the annotation carries the
record instead. *This repair used it on both G3 figures*, which is the honest test of the rule.

**Rewrite-in-place is acceptable only when the false text is not itself a finding** — a *description*
that was wrong, where an audit or closeout elsewhere already holds the record. It is **not**
acceptable for a claim this arc proved false, because then the corpus's only record of the refutation
is the refutation, and the thing refuted is gone. When in doubt, escalate to instrument 2. **Both
existing uses (C6, C10) satisfy this**: each rewrote a *description* of a population, and mg-8a71's
F2/F4 findings hold the record. **G4 is a finding about a missing standard, not about five mistakes,
and I did not re-open them.**

**Deletion declared as a strike is never acceptable** — a block that says text `is struck` and
carries no markup asserts a record it did not make. That is finding G1 (C9), closed by mg-cd04.

> *(Inline code, not a quotation, and that is the point: the first draft of this paragraph wrote the
> phrase as a quoted sentence and **the mg-cd04 declared-strike control failed this document** — a
> declaration verb plus a quoted span in one sentence with no `~~` in the block. The control was
> right; a paragraph defining the defect is not licensed to commit it. Fixed at the site rather than
> baselined, because a control that grows a tolerance every time it is right is not a control. This
> is the ninth instance of the arc's pattern and the second in this ticket: the defect appeared
> inside the remedy.)*

**None is acceptable only when the disposition is not the worker's to make** — an adjudication
between two prior findings, as with C5. Acceptable only if **flagged, routed to a named owner, and
recorded in a control baseline**, so *"not acted on"* cannot decay into *"forgotten"*.

### 3.3 Which the controls can detect — measured, not asserted

New **part (E)** of `onethird_mg0242_struck_vs_refuted.py` remediates one refuted sentence five ways
in a copy of the controlled document and runs both corpus controls over each copy.

| instrument | live-claim control | declared-strike control | verdict |
|---|---|---|---|
| strike-at-site | exit 0 | 0 hits | **INDISTINGUISHABLE** from ↓ |
| rewrite + annotation | exit 0 | 0 hits | **INDISTINGUISHABLE** from ↑↓ |
| rewrite-in-place | exit 0 | 0 hits | **INDISTINGUISHABLE** from ↑ |
| deletion declared as a strike | exit 1 | **1 hit** | separable |
| none | **exit 1** | 0 hits | separable |

**Three of the five are one thing to every control in CI.** So:

> **A green live-claim run means NO UN-REMEDIATED CLAIM. It does not — and structurally cannot —
> mean NO UNRECORDED REMEDIATION.** The instrument column of part (A) is the only record that tells
> them apart, and it is maintained by hand.

**This is now printed at the point each control reports**, per the ticket, in a
`WHAT THIS GREEN DOES NOT SAY` paragraph in the PASS block of both
`onethird_mg8a71_live_claim_control.py` and `onethird_mgcd04_declared_strike_control.py`.

**P8 refuted on its first half, and the correction sharpens the finding.** I predicted the
deletion-declared-as-a-strike mutant would leave the live-claim control at exit 0. It exits **1**.
mg-069f's tightening (a STRIKE-declaring block is checked with inline strikes removed) catches it —
**inside the controlled file**. C9 escaped not because the rule was absent but because it was written
*one document over from where the control looks*. The instrument is caught in-file by the live-claim
control and corpus-wide by mg-cd04's; it is the **only** one of the five any control can name.

### 3.4 The standard is now enforced, not just written down

* `INSTRUMENTS` in `onethird_mg0242_struck_vs_refuted.py` is the standard, as data.
* Part (A) **fails** if a ledger entry uses an instrument the standard does not name — a sixth
  instrument appearing is finding G4 again, and it now stops the run instead of being narrated.
* Part (A)'s tally line read *"the repair used three, and named only one"* above a tally printing
  **five** — **a named-vs-counted error inside the line whose job is to report the count** (P5). It
  is **computed** now.
* Part (E) **fails** if the blind spot ever silently disappears. Gaining discrimination is good and
  must be *recorded*, not absorbed.

---

## 4. What I did not do

* **Did not mandate strike-at-site everywhere.** The ticket is explicit that G4 is a missing
  standard, not five mistakes; C6/C10's rewrites and C7/C8's annotations were checked against §3.2's
  rule and all four pass it.
* **Did not re-open C5.** It remains the ledger's one live entry — flagged, routed, baselined.
* **Did not rewrite any filed audit's finding text** (§2.2), and did not touch the mg-cd04 or mg-9a19
  repair records that describe G3 as open, which was true when they were written.
* **Did not widen the live-claim control's signature population.** mg-0242 measured that at ~94%
  false positive; that decision stands.
* **Did not revise a prediction to agree with its result.** P1, P3 and P8 are recorded as filed.

## 5. How to falsify this

```
python3 scripts/onethird_mg0242_population_census.py        # exit 0; baseline EMPTY
python3 scripts/onethird_mg0242_struck_vs_refuted.py        # exit 0; parts (A) and (E)
python3 scripts/onethird_mg8a71_live_claim_control.py       # exit 0; read the PASS tail
python3 scripts/onethird_mgcd04_declared_strike_control.py  # exit 0; read the PASS tail
python3 scripts/onethird_mgfccb_direction_check.py          # exit 0
```

To see the re-baseline gate of §2.3 fire, run the census from `HEAD~` against this tree's docs.
