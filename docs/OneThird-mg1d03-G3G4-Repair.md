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
| P1 | The **other two rows** of closeout §6.1 — the rows this repair is *not* fixing — are **correct** when the figure is obtained by calling the helper rather than reading the table. **0 gaps among the 6 figures.** | population: the 6 numerals in rows 1–2 of §6.1 of `docs/OneThird-mg8a71-VerdictRepairs-Closeout.md`; grain: one integer per (generator × {posets, pairs, triples}) | **CONFIRMED.** 0 gaps in 6 figures — 404 / 6 385 / 31 625 and 4 469 / 43 842 / 218 166, each NAMED once and SWEPT once, every one re-obtained by calling the generator. Asserted on every push now, not believed. |
| P2 | The **other four rows** of the `posets_with_identity_extension` docstring table are **correct** when counted. **0 gaps among the 6 per-`n` figures.** | population: the per-`n` rows `3/4/5` of the docstring table in `scripts/onethird_mgfccb_direction_check.py`; grain: one integer per (n × {this family, A001035}) | **CONFIRMED.** 0 gaps in the 6 per-`n` figures (7/19, 40/219, 357/4231). The prediction's prose says *"other four rows"* where its own population line says rows 3/4/5 — 3 rows, 6 figures; the population line is the one that was measured. The totals row's two integers (404, 4 469) are also correct: only its ratio LABEL was wrong. |
| P3 | With both G3 numbers corrected and the census `BASELINE` **left untouched**, the census **exits 1** with two `BASELINE GAP CLOSED` lines — the re-baseline gate firing, not a regression. | population: one process exit code | **CONFIRMED.** Exit **1**, two `BASELINE GAP CLOSED` lines and nothing else. Transcript in §2. |
| P4 | With both entries then removed from `BASELINE`, the census **exits 0** and both comparisons pass as ordinary `OK` checks. | population: one process exit code | **CONFIRMED.** Exit **0**; both now print as ordinary `[OK  ]` checks. |
| P5 | The ledger in `onethird_mg0242_struck_vs_refuted.py` prints *"the repair used three, and named only one"* immediately above a tally that lists **five** distinct instrument keys — a named-vs-counted error **inside the line that reports the count**, the same class as G3. | population: part (A)'s `BY INSTRUMENT` block; grain: distinct instrument keys | **CONFIRMED.** *"the repair used three"* printed directly above five distinct keys. Named 3, counted 5. |
| P6 | The live-claim control's PASS readout contains **0** occurrences of the word *instrument* — i.e. a green run says nothing about which of the five remediations it can see. | population: the `main()` report block of `scripts/onethird_mg8a71_live_claim_control.py`; grain: word occurrences | **CONFIRMED.** 0 occurrences in 28 lines of output. It is 3 now, and §5 is the sentence they are in. |
| P7 | **Deletion-without-declaration is invisible to every control in CI.** A mutant that deletes a refuted claim outright — no `~~`, no annotation, no *"is struck"* — leaves the live-claim control at exit **0** *and* the declared-strike control at exit **0**. | population: 2 process exit codes over the mutated corpus | **CONFIRMED.** Mutant I4: live-claim **0**, declared-strike **0**. An undeclared deletion is invisible to both. |
| P8 | **Deletion-declared-as-a-strike is visible to exactly one control.** The same deletion, with the *"is struck with it"* declaration restored and no markup, leaves the live-claim control at exit **0** and trips the declared-strike control (≥1 unbaselined hit). | population: 2 process exit codes over the mutated corpus | **CONFIRMED as filed, and REFUTED in its unrestricted reading.** I5a (the declaration quotes a short form, as the real C9 site does): live-claim **0**, declared-strike **1** — as predicted. I5b (the declaration quotes the refuted sentence *verbatim*): live-claim **1**. The quotation is itself read as a live assertion. Scored on I5a because that is the shape C9 actually has; the choice was made after seeing both, and I5b is a finding — see §4.3. |
| P9 | **Rewrite-in-place and rewrite+annotation are indistinguishable from strike-at-site to both controls.** Both mutants exit **0** on both controls. | population: 4 process exit codes over the mutated corpus | **CONFIRMED.** I2 and I3: **0, 0** and **0, 0**. Neither control can tell either from strike-at-site. |
| P10 | After all repairs, all five controls in `script-controls.yml` that touch this arc exit **0**: census, struck-vs-refuted, live-claim, declared-strike, direction check. | population: 5 process exit codes at HEAD | **CONFIRMED.** All five exit 0, and so do the two controls this repair adds and the two nearest neighbours (mg-9a19, mg-0242 identity re-run). 9 of 9. |
| P11 | Sweeping `docs/`, `scripts/` and `.github/` for the literal `6.9x`/`6.9×` in a **poset-grain** claim finds **more than the one baselined site** — the "corrected at every site" claim will again be one or more sites short. | population: all `*.md`, `*.py`, `*.yml` under `docs/`, `scripts/`, `.github/`; grain: one site = one line asserting the ratio of a poset count | **CONFIRMED, and by 15 sites rather than one.** 16 ratio sites failed the grain rule at `b3bcad9`; exactly 1 of them was the baselined figure. *"Corrected at every site"* was 15 sites short. |
| P12 | The five instruments partition the ledger exactly: 4 + 2 + 2 + 1 + 1 = **10 = REFUTED**, with no ledger entry carrying a sixth instrument. | population: the 10 ledger entries of part (A); grain: one instrument key per entry | **CONFIRMED.** 4 + 2 + 2 + 1 + 1 = 10 = `REFUTED`, five distinct keys, no sixth. Asserted in code now: the standard's instrument set is checked against the ledger's column on every push. |

---

*(Sections 1 onward were written after the measurements; §0 was committed first, in its own
commit, and has not been edited since except to fill the outcome column.)*

---

## 1. G3 — the two figures, corrected at the site

**Every count below names its POPULATION and its GRAIN, and every one is obtained by CALLING a
helper or running a control.** The pre-filed audit **mg-5854** is instructed to check each row by
calling rather than reading; `scripts/onethird_mg1d03_table_row_audit.py` is that check, written so
the auditor can re-run it in one command instead of reproducing it.

| what | NAMED (before) | COUNTED | now |
|---|---|---|---|
| closeout §6.1 row 3, the live-claim control's own file | `537/537 lines` | **539** | `539/539` |
| closeout §6.1 row 3, bucket names | `exempt-annotation` | the scanner's key is `exempt_annotation` | corrected |
| direction-check docstring, totals row | `(6.9x larger)` | 4 469/404 = **11.0619** | `(11.06x larger, posets)` |

**Why `6.9x` read as plausible, stated once because it is the whole lesson of G3.** It is a real
number about these two families — it is the ratio of **pairs** (43 842/6 385 = 6.8664) and of
**triples** (218 166/31 625 = 6.8985). It was written on the **poset** row. A wrong number is caught
by arithmetic; a right number on the wrong **grain** is caught only by someone who asks *of what?*,
which is why it survived an audit, a repair and a closeout.

**The bucket-name correction was not in the ticket.** `{paragraph, quote, heading, exempt-annotation,
blank}` is a NAMED set and the scanner's keys are the COUNTED set; they differed by a hyphen. Found
by comparing the two mechanically rather than reading them, and now asserted.

## 2. The neighbours — checked by calling the helper, per mg-0242's instruction

> *"a table that got its own row wrong has not earned trust on its neighbours."*

**Closeout §6.1, rows 1 and 2.** Population: the 6 numerals across those two rows. Grain: one integer
per (generator × {posets, pairs, triples}), each appearing once as NAMED and once as SWEPT. Every one
re-obtained by enumerating: **0 gaps in 6 figures** (P1). The parser also refuses to pass if §6.1 stops
holding exactly the three rows it knows, so a fourth row cannot be added unchecked.

**The docstring table, rows `3/4/5`.** Population: 3 rows × 2 columns. Grain: one poset count per
(n × family). Counted: 7/19, 40/219, 357/4231 — **0 gaps in 6 figures** (P2).

**The re-baseline gate fired, exactly as it was built to (P3 → P4).** With both figures corrected and
`BASELINE` deliberately untouched, the census exited **1**:

```
baseline: 2 known gap(s) tolerated; 0 seen
  [GONE] closeout §6.1: live-claim control lines named vs swept
  [GONE] direction_check docstring: poset-row ratio named vs computed
RESULT: FAIL — 2 unbaselined NAMED-vs-COUNTED gap(s):
  - BASELINE GAP CLOSED — re-baseline this control: closeout §6.1: ...
  - BASELINE GAP CLOSED — re-baseline this control: direction_check docstring: ...
```

Only then was the baseline emptied, and the census exits **0**. The gate is the reason this repair
could not land silently, and the sequence is recorded here because a closed gap that leaves no trace
is a gap that can reopen unnoticed.

**One check was tightened while passing through it.** The census compared the docstring's ratio at
**one** decimal place (`6.9` vs `11.1`). At that precision the gap was visible but the *grain* was
not, and G3 was a grain error. It now compares at two decimal places **and requires the label to name
its grain**.

## 3. `6.9x` at every site — 15 sites beyond the one that was baselined (P11)

mg-069f's closeout says the population was *"corrected at every site"*. It was not, and neither is a
sweep for a literal enough — the same literal is **right** in some sentences and **wrong** in others,
because the two families differ by a different factor at each grain.

**The rule this repair adopts, and now enforces corpus-wide:** *a ratio between these two populations
is an assertion only if the GRAIN is named beside it, and it must be right at the grain nearest to
it.* Population: every `*.md`, `*.py`, `*.yml` under `docs/`, `scripts/`, `.github/`. Grain: one site
= one ratio literal.

| class | at `b3bcad9` (before) | at HEAD |
|---|---|---|
| **assertions failing the rule** | **16** — 1 baselined, **15 not** | **0** |
| assertions passing | 15 | 31 |
| quotations (backticks or a quoted span — never failed on) | 8 | 9 |
| named-vs-counted reports (the line carries BOTH figures) | 26 | 29 |

The two never-failed classes are **listed line by line** on every run. An exemption that does not
report its own reach is the defect this corpus has now found in itself four times (mg-9a19 H1,
mg-9d7b M4/M8), and this control was not going to be the fifth.

**`--demonstrate` makes the green a measurement**, per house convention: today's rules are copied into
a `git archive` of an older tree and run there.

```
python3 scripts/onethird_mg1d03_table_row_audit.py --demonstrate b3bcad9
  -> exit 1 there, 18 gaps: the two G3 figures plus 16 ratio sites.
```

**One correction was DECLINED, and the decline is the point.** `docs/OneThird-mgfccb-DirectionRepair-
IndependentAudit.md`'s headline *"machine-confirmed on a population 6.9× larger"* is **true at the
triple grain** — that audit's population was 218 166 triples against 31 625. It was not rewritten to
`11.06×`; its grain was named (`6.90× larger in triples — 11.06× in posets`). mg-8a71 finding F4 is
the model case here: *found wider than reported, then correctly DECLINED to re-widen proven-safe
text.* Blanket-replacing the literal would have introduced a new wrong figure in the name of fixing
one.

## 4. G4 — five instruments, one standard

mg-0242: *"Name all five, say which is preferred and when each is acceptable, and state which the
control can detect."* The answer lives in
`scripts/onethird_mg1d03_remediation_instruments.py`, executable rather than prose, and the count of
five is **counted from the ledger**, not asserted: population = the 10 ledger entries of
`onethird_mg0242_struck_vs_refuted.py` part (A), grain = one instrument key per entry. **4 + 2 + 2 +
1 + 1 = 10, five distinct keys, no sixth** (P12).

### 4.1 The standard, and when each of the other four is acceptable

**STANDARD: strike-at-site.** Not because the other four are wrong — mg-0242 says explicitly that G4
is *a finding about a missing standard, not about five mistakes*, and all four other uses in the
ledger were checked at the site and are right. It is the standard because it is the only instrument
that leaves the refuted claim **where it was said, marked false**: a reader arriving with the old
claim finds it and sees it refuted, a consumer citing it can still locate it, and — the load-bearing
reason — it is the only one that leaves a **mechanical trace**, so it is the only one a control can
confirm was used.

| instrument | uses | acceptable when |
|---|---|---|
| **strike-at-site** | 4 | **The standard.** Any claim that was asserted and is now known false, whenever the sentence can stay on the page. |
| rewrite-in-place | 2 | The defect is a **misstatement of an otherwise sound fact** — a wrong population name, a wrong figure, a wrong grain. There is no refuted inference to preserve. **Not** acceptable for a refuted inference: the reader who remembers it finds nothing. |
| rewrite + annotation | 2 | Preferred over a bare rewrite whenever the claim was **consumed elsewhere** or cited as evidence — the annotation is what lets a consumer notice. Required when the rewrite changes a number another document quotes. |
| deletion declared as a strike | 1 | Only when the sentence has **no true residue** and the deletion is **declared at the site**. An *undeclared* deletion is invisible to every control in CI (§4.2) and is the one instrument this standard forbids outright. |
| none — flagged and routed | 1 | Only when the disposition is **contested or belongs to another owner** (C5: mg-069f declined to reverse mg-8a71's adjudication and routed it to pm-onethird). Requires a `KNOWN_LIVE` entry naming the routee; an unflagged "none" is just an unremediated claim. |

**This repair used three of the five and says which where.** Strike-at-site: none needed. Rewrite +
annotation: closeout §6.1 (§1 above) — the figures are quoted by other documents, so the annotation
is mandatory under the rule just written. Rewrite-in-place: the 15 ratio sites, all of them
misstatements of a sound fact. Annotation-only: the two documents that record the G3 gap as *"still
baselined"* — time-indexed records, true when written, now carrying one line saying mg-1d03 closed
them.

### 4.2 Which of the five a control can actually see — MEASURED, not asserted

The "detectable" column is the one a document cannot be trusted on, so it is measured by mutation.
One refuted claim (ledger **C3**, §3.2's *"Equivalently"*) is remediated each way in a scratch copy of
the corpus, and both controls run over each mutant. Population: **7 mutants × 2 controls = 14 process
exit codes**. Grain: one exit code.

| mutant | live-claim | declared-strike |
|---|---|---|
| I1 strike-at-site (HEAD) | 0 | 0 |
| I2 rewrite-in-place | 0 | 0 |
| I3 rewrite + annotation | 0 | 0 |
| I4 **deletion, UNDECLARED** | **0** | **0** |
| I5a deletion, declared (quotes a short form) | 0 | **1** |
| I5b deletion, declared (quotes the sentence verbatim) | **1** | **1** |
| I6 **the claim RESTORED LIVE** (positive control) | **1** | 0 |

**Of the five instruments, CI distinguishes exactly one boundary: a strike DECLARED but not MADE.**
Strike-at-site, rewrite-in-place, rewrite + annotation and an undeclared deletion are **pairwise
indistinguishable** to both controls (P7, P9).

**I6 is why the six zeros mean anything.** A mutant matrix with no positive control measures nothing:
the live-claim control catches this claim when it is live, so the zeros above are **reach**, not
blindness. The script fails if I6 ever stops biting.

### 4.3 P8 was confirmed as filed and refuted in its unrestricted reading

P8 predicted that a declared deletion leaves the live-claim control at **0** and trips the
declared-strike control. **I5a: 0 and 1, as predicted.** **I5b — the same declaration quoting the
refuted sentence verbatim — exits 1 on the live-claim control**, because the quotation is itself read
as a live assertion of the claim.

Scored on I5a, because that is the shape the real C9 site has: its declaration quotes *"over every
poset and every reference order"*, which is not one of the live-claim control's four signatures. **The
choice of which mutant scores the prediction was made after seeing both results**, and is recorded
here rather than left implicit, because choosing the favourable variant after the fact is exactly how
a pre-registration stops being one.

**I5b is a finding in its own right, not a mutant artefact.** A worker who deletes a refuted sentence
and declares the deletion by quoting it *fails* the live-claim control — the correct instrument
produces a red run. The control cannot distinguish quoting a claim from asserting it; mg-0242 §8
measured the same thing corpus-wide (~94% false positive) and it is why the live-claim control reads
one document. Not fixed here: it is a property of signature matching, not of this repair, and
narrowing it would need a finding of its own.

## 5. The reach statement — at the point it reports

> mg-0242: *"If the control can only see strike-at-site, say so at the point it reports — otherwise a
> green control means 'no un-struck claims' and is read as 'no unremediated claims'."*

Before this repair the live-claim control's output contained the word *instrument* **0 times in 28
lines** (P6). It now prints, immediately above its `RESULT` line, which five instruments exist, that
it detects only whether the claim is **live**, that four of the five are invisible to it, which
control sees the fifth, and:

```
    So: PASS = 'no refuted claim is live in this one document'.
    PASS is NOT 'every refutation was remediated', and it is NOT
    'remediated to the standard'.
```

That statement is not prose anybody has to maintain by hand: the instruments script **runs the control
and reads its output**, and fails if the reach statement disappears or stops naming the right number
of instruments. Prose and measurement cannot drift apart without a red run.

**The ledger's own line was the same defect one level up.** It printed *"the repair used three, and
named only one"* directly above a tally of **five** keys — a named-vs-counted error inside the line
that reports the count (P5). The count is now computed: `len(kinds)`.

## 6. What this repair got wrong on the way through

**Its own control bound the wrong grain, silently.** `binding_grain` first matched grain words as bare
substrings, so the ratio in *"…larger than the **repair**'s"* bound to the **pair** grain — where
`6.9×` is right — and the site passed. Found by checking a site the control had passed rather than
trusting the pass. The word *repair* containing the word *pair* is not a curiosity in a corpus about
repairs; it is most of the sentences. Fixed with word boundaries, and the site then failed as it
should have.

**A line-scoped rule fired on four correctly-written sites.** Prose here is hard-wrapped, so
*"under-swept 11.06× in / posets"* is one sentence with its grain named. The rule is now scoped to the
literal's line plus the next. A control that fires on line breaks trains its readers to reflow rather
than to name the grain.

**And it caught this repair's own CI comment.** The step description written to explain the ratio
rule said `6.9x` with no grain beside it, and the control — whose population includes `.github/` —
failed the run. Corrected by quoting the literal, which is what it is: a quotation of the defect, not
an assertion of a ratio.

All three are recorded rather than quietly fixed, because a repair whose own instrument had a
grain-binding defect is the most on-the-nose evidence available that G3's class is not a slip.

## 7. For mg-5854 — every claim here, and the one command that falsifies it

| claim | population | grain | command |
|---|---|---|---|
| §6.1 rows 1–2 correct, 0 gaps in 6 figures | the 3 data rows of §6.1 | one integer per (row × column × quantity) | `python3 scripts/onethird_mg1d03_table_row_audit.py` |
| docstring rows `3/4/5` correct, 0 gaps in 6 figures | 4 rows × 2 columns of the docstring table | one poset count per (n × family) | same |
| 0 ratio assertions without a grain corpus-wide | every `*.md`/`*.py`/`*.yml` in `docs/`, `scripts/`, `.github/` | one site = one ratio literal | same |
| the control bites where the defect is | the tree at `b3bcad9` | 18 gaps | `… --demonstrate b3bcad9` |
| five instruments, no sixth, 10 = REFUTED | the 10 ledger entries | one instrument key per entry | `python3 scripts/onethird_mg1d03_remediation_instruments.py` |
| CI distinguishes exactly one instrument boundary | 7 mutants × 2 controls | one exit code | same |
| the live-claim control states its reach | that control's stdout | word occurrences | same |
| census baseline is empty and green | every population any control names | one integer per population | `python3 scripts/onethird_mg0242_population_census.py` |
| all controls green at HEAD | 9 controls | one exit code | see §8 |

**Every figure in the two audited tables is now obtained by calling the helper on every push.** The
one thing this repair cannot give the auditor is trust in its own reading of those tables — which is
why the rows are parsed out of the files rather than transcribed.

## 8. Exit codes at HEAD (P10) and what was left alone

`census 0 · struck-vs-refuted 0 · live-claim 0 · declared-strike 0 · direction-check 0 ·
table-row-audit 0 · remediation-instruments 0 · mg-9a19 exemption audit 0 · mg-0242 identity re-run 0`
— **9 of 9**, and the mg-3934 static CI control still reports *"every workflow that reads history
fetches it"*: neither new script names a pinned revision on its default path, both taking a revision
from `argv` only.

**Left alone, deliberately:**

* **The declared-strike control's per-block `~~` shielding** (mg-9d7b M9, REPORTED not failed). Not
  this ticket's, and mg-9d7b's reasoning for reporting it stands.
* **The live-claim control's one-document population.** mg-0242 §8 measured the corpus-wide
  generalisation at ~94% false positive; the corpus-wide question is what the declared-strike control
  exists for.
* **`docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md`'s `6.90×` headline** — true at its
  grain, so its grain was named and its figure kept (§3).
* **Ledger entry C5**, still `LIVE` and still routed to pm-onethird. Under the standard written above
  that is the "none" instrument used correctly: contested, flagged, and owned elsewhere.
