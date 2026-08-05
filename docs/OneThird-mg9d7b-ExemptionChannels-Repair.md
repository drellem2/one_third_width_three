# mg-9d7b — every exemption channel enumerated, and each one bounded or made to print what it skips

**Target:** the two controls mg-cd04 (`f6e329c`) left behind, as audited by mg-9a19 (`1e996fb`):
`scripts/onethird_mg8a71_live_claim_control.py` and
`scripts/onethird_mgcd04_declared_strike_control.py`.

**Filed as the CLASS, not as two field fixes.** mg-9a19's H1 and H2 are the same shape twice: an
exemption granted on a marker's say-so with nothing saying how far it reaches. This arc has
repeatedly repaired the next field and left the set. The deliverable here is the **enumeration**;
the bounds are consequences of it.

---

## 0. Verdict

**Both channels are closed, all fifteen are enumerated, and the invariant is now asserted by a
control rather than by this paragraph.**

| | |
|---|---|
| exemption channels enumerated across the two controls | **15** |
| unbounded **and silent** before this repair | **9 violations**, measured at `1e996fb` by the new census |
| unbounded **and silent** after it | **0** |
| still unbounded, **by design**, each printing its own number | **2** — closed fences (4.30% of the corpus) and the inline `~~` strip |
| mutants that moved | **M4 → caught**, **M8 → caught** |

The invariant the repair is really about:

> Every route by which a line leaves a control unchecked is either **BOUNDED** by a named constant,
> or **REPORTED** with a number in that control's own output. Unbounded-and-reported is a decision.
> Bounded-and-quiet is fine — the bound is the statement. **Unbounded and silent** is the defect.

**Three predictions missed, and they are in §6.** One of them (E13) was a prediction against myself
and its failure is the most interesting result here.

---

## 1. THE ENUMERATION — every channel, and what each one costs

This is the deliverable. Printed on every run by both controls, and asserted by
`scripts/onethird_mg9d7b_exemption_channel_census.py`.

### 1.1 `onethird_mg8a71_live_claim_control.py` — 8 channels

| id | route out of the check | disposition | reach at HEAD |
|---|---|---|---|
| **A1** | the EXEMPT label's own sub-paragraph | **BOUNDED** `MAX_LABEL_LINES = 6` | 4 lines of 24 allowed |
| **A2** | an EXEMPT sub-paragraph carrying a QUOTATION | **BOUNDED** `MAX_QUOTED_LINES = 11` *(was unbounded — H1)* | 66 lines, 9 sub-paragraphs, longest 11 |
| **A3** | one EXEMPT block's exempt-**text** total | **BOUNDED** `MAX_EXEMPT_LINES = 27` *(new; see §3)* | largest block uses 27 of 27 |
| **A4** | a blockquote's own blank `>` lines | not text | 18 lines |
| **A5** | inline `~~…~~` spans, stripped from **every** checked unit | **UNBOUNDED BY DESIGN**, reach printed | 3 spans, 460 chars, longest 308 |
| **A6** | the population: one document of the corpus | **UNBOUNDED BY SCOPE**, argued by mg-cd04, printed | 1 document read |
| **A7** | fenced code | **not a channel here** — fences are CHECKED | 34 fence lines, all checked |
| **A8** | label detected in `block[:3]`, exemption granted to sub-paragraph 0 | mismatches reported | 0 |

### 1.2 `onethird_mgcd04_declared_strike_control.py` — 7 channels

| id | route out of the check | disposition | reach at HEAD |
|---|---|---|---|
| **B1** | a CLOSED fenced region | **UNBOUNDED BY DESIGN**, reach printed *(was silent — H2)* | 581 regions, ~4.3% of the corpus, longest 195 |
| **B2** | an **UNCLOSED** fence | **no longer a channel** — checked, not skipped *(was: skip to EOF — H2)* | 1 site, now checked |
| **B3** | one `~~` anywhere in a block backs every declaration in it | **REPORTED**, never failed on *(H3)* | 1 sentence |
| **B4** | a declaration with no same-sentence quotation | reported as a near miss | 1 |
| **B5** | `BASELINE` | **BOUNDED**, printed, fails on drift either way | 2 sites |
| **B6** | `docs/*.md` does not descend | **UNBOUNDED BY SCOPE**, printed *(H4)* | 14 documents in the tree never read |
| **B7** | blank lines | not text | ~23 000 lines |

**The reach column is recomputed by the controls on every run and is deliberately approximate
here.** A corpus-wide count written into prose is a claim that rots — the document count moved twice
while this repair was being written, once for each file it added — and this arc has spent findings
on exactly that. The live figures are the ones the controls print; these are order-of-magnitude
context for reading the table.

### 1.3 Two of these were on nobody's list

**A5 — the inline strike.** `INLINE_STRIKE.sub(" ", text)` deletes text from *every* checked unit —
paragraph, heading and STRIKE block alike — before a signature ever sees it, at any length, and no
run had ever printed a number for it. It is left unbounded, and that is a decision rather than an
oversight: inline `~~` **is** the markup the whole convention rests on, so bounding it would bound
the retain-as-record mechanism itself. What it gets instead is a number.

**A8 — detection span vs exemption span.** The marker is looked for in `block[:3]`; the exemption is
granted to *sub-paragraph 0*. Those are different spans. Where they differ, sub-paragraph 0 is
exempt while carrying no label. Zero occurrences today; reported rather than repaired, because
narrowing detection would change which blocks are exempt at all — a larger change than the finding
justifies.

**And one asymmetry worth stating rather than fixing (A7).** These two controls disagree about
whether a fence is data. The declared-strike control skips fences deliberately; the live-claim
control has no fence rule at all, so fenced content is swept up as an ordinary paragraph and
**checked**. That is the fail-closed side of the disagreement, so it is left alone — but it is a
disagreement between two controls over the same corpus convention, and it now has a number.

---

## 2. H1 — and why the obvious bound would not have closed it

**The finding.** `exempt_partition` bounded the label sub-paragraph and left every quotation-backed
sub-paragraph exempt **entire, at any length**. mg-cd04 moved 59 lines out of the blind spot and
left 66 in it, and the 66 were the unbounded ones.

**The bound is the MEASURED reach, with no headroom, and that is the whole point.** Setting it by
round number does not close the finding. mg-9a19's M4 appends **exactly one line** to the longest
quotation-backed sub-paragraph, so any cap with slack lets the same evasion through one line
further along. Swept rather than argued:

| `MAX_QUOTED_LINES` | HEAD | M4 |
|---|---|---|
| 10 | 0 | **1 caught** |
| **11** *(the measured reach)* | **0** | **1 caught** |
| 12 | 0 | **0 MISSED** |
| 13 | 0 | **0 MISSED** |

This was **predicted before the bound was written** — E1 in
`OneThird-mg9d7b-ExemptionChannels-PREDICTIONS.md`, committed in its own commit ahead of every
script of this repair.

**The label bound is untouched and still exact**, which is the property mg-9a19 confirmed: M5 (line
2) and M6 (line 6) missed, M7 (line 7) caught.

**The design that was tried first and rejected, on evidence.** Exempting only the lines a QUOTATION
span physically touches — line granularity rather than a length bound — is the tighter rule and it
is **wrong here**. It fires `S2-hinges-on-degree` as a false positive at line 502: prose in this
corpus is hard-wrapped at ~100 columns, so a quotation and the commentary that earns it interleave
line by line. `exempt_partition`'s own docstring said so before the attempt; it was right. Recorded
as E3 rather than quietly dropped, because it is the design that would otherwise have shipped.

**The cost of a bound with no headroom**, stated plainly: legitimately lengthening a quoting
sub-paragraph pushes its tail into checked text. Every channel prints its headroom on every run, so
that is visible before it bites, and raising a bound is a one-line change with a finding attached —
the same contract as adding a `BASELINE` entry.

---

## 3. The two cheap ones

**`MAX_EXEMPT_LINES` now exists.** From mg-cd04 to mg-9d7b the live-claim control's docstring named
this identifier **twice** — at lines 47 and 106 — and no such name existed anywhere in the
repository. The bound the prose named was block-level; the bound the code had was
sub-paragraph-level. A reader taking the docstring at its word concluded M4 was impossible. It now
exists, at 27 lines, and bounds a block's exempt **text** (A1 + A2; a block's own blank `>` lines
are A4 and do not spend it). The docstring is a description again rather than a promise.

**The fenced count prints.** mg-9a19's H5: the repair reported 56 blocks, 3 fenced regions and 0
hits, with 1 hit once the fences were removed, and the control itself never printed a fenced number
while its report said *"ALL classified"*. It prints now — regions, lines, share of corpus, longest
region and where it is — for every run, at HEAD and under `--demonstrate`.

---

## 4. H2 — the unclosed fence, which is not a bound problem

**Skipping to EOF on malformed input is the failure mode, not the missing bound.** A length cap
would still let a stray fence at line 3 of a 400-line document swallow the cap's worth of text, and
would still be quiet about why.

So an opening marker with no closing marker is **not treated as a fence at all**: the marker line
itself is checked as a one-line block, everything after it parses normally, and the site is
**reported by name**. Fail-closed, reach zero, and loud.

**Live today**, and printed by the control on every run:

    OneThird-AP-2-Prong3I-beta-RungUniqueness-SD-FLOOR.md:138
        would have skipped 2 lines to EOF; now checked

Two lines is what that particular site happened to hide. Nothing about the mechanism bounded it to
two — which is exactly why the mechanism, not the site, is what changed.

**Closed fences stay unbounded, deliberately.** The rule is length-independent: the thousandth line
of a code block is no more an assertion than the first. Capping it would be a bound with no reason
behind it. What was wrong was never the absence of a cap — it was the absence of a **number**.

---

## 5. The instrument, and how it avoids being a restatement of its author's reading

`scripts/onethird_mg9d7b_exemption_channel_census.py`.

A table of channels copied out of two docstrings proves nothing: it passes exactly when the
author's reading was complete, which is the thing in question. So both halves are mechanical, and
the author does not supply the observed side.

| the census fails when | why that is not the author's opinion |
|---|---|
| a control classifies a line into a **coverage bucket the census was never told about** | a new disposition is what a new exemption channel *is*, from outside the control |
| lines in a non-checking bucket are **not claimed, to the line**, by a declared channel | a skip folded quietly into a familiar bucket still fails |
| a channel declared BOUNDED names an **identifier the module does not define** | this is precisely the `MAX_EXEMPT_LINES` defect, asserted |
| an unbounded channel's reach appears **nowhere in the control's captured stdout** | the reporting half, checked against real output rather than a promise |

**Can it fail?** Both answers are executable.

* `--selftest` builds four broken controls, one per half of the invariant: **4 of 4 rejected.**
* `--demonstrate 1e996fb` loads **both controls from the parent tree** and runs the same invariant
  there: **9 violations**, including `MAX_QUOTED_LINES` and `MAX_EXEMPT_LINES` naming identifiers
  that do not exist, 88 unattributed exempt lines, 4 359 unattributed fenced lines, and A5 / B1 /
  B3 / B6 unbounded and silent. **0 here.**

Wired into `script-controls.yml` after the mg-9a19 step, `--selftest` first.

**mg-9a19's own handshake fired, exactly as built.** Its `RECORDED` table pins each mutant and fails
on movement *in either direction* — its §7 says a future author who closes H1 or H2 "cannot do it
silently". Closing them turned that step red with `a recorded mutant outcome MOVED: M4, M8`. It was
re-recorded deliberately, in the same commit, with the mg-9a19 values kept in
`RECORDED_AT_MG9A19` and printed beside the new ones.

---

## 6. Predictions, written before any script of this repair existed

Committed in their own commit (`6e7c27b`) ahead of every edit. Kept verbatim, misses included.
**11 hit, 3 missed, 1 partial** — and the misses are the useful part.

| # | prediction | outcome |
|---|---|---|
| N1/N2 | 8 channels in the live-claim control, 7 in the declared-strike control | hit — but weakly: I declared the table, and the mechanical half only confirms no *bucket* escapes it |
| N3 | ≥ 2 channels named by neither mg-9a19 nor the ticket | hit — A5 and A8, **both named in advance** in the predictions file, so this is a check on my reading, not a discovery |
| **E1** | a bound of 12 does **NOT** close M4 | **hit**, and confirmed by sweeping 10/11/12/13 |
| E2 | `MAX_QUOTED_LINES = 11` catches M4 and leaves HEAD at 0 | hit |
| E3 | line-granular exemption produces a false positive at HEAD | *(post-measurement; recorded, not forecast)* |
| E4 | HEAD stays exit 0 after the A2 bound | hit |
| **E5** | largest per-block exempt total **33** | **MISSED — it is 27.** I predicted the total *including* the block's blank `>` lines and then shipped a bound that excludes them. The number was wrong because the definition moved under it |
| E6 | the unclosed-fence fix moves exactly 2 lines out of `fenced_code` | hit on the count (4 359 → 4 357), **wrong on the destination**: 1 line to `block`, 1 to `blank`, not 2 to `block` |
| E7 | M8 moves 0 → 1 | hit |
| E8 | M9 stays 0 and is reported rather than failed on | hit |
| E9 | the mg-9a19 instrument **fails** the moment E2 and E7 land | hit, exactly — `MOVED: M4, M8` |
| E10 | printing costs no exit code anywhere | hit — HEAD 0/0, `1b00147^` 1, `1b00147` 1, `--demonstrate bb1cb9b` 0 |
| **E11** | **3** channels in violation before the repair (A2, B1, B2) | **MISSED — 9.** My own enumeration was right about which channels existed and wrong about how many were *silent*. A6, B3, B6 and two attribution gaps were in violation and I did not count them |
| E12 | 0 violations after | hit |
| **E13** | *"the invariant, asserted as code, will find at least one channel I did not think of when I wrote this file"* | **MISSED.** It found none. The declared set survived the mechanical check intact |

**E13 is the one that matters, and I said so in advance.** I predicted against myself that the
census would turn up a channel my reading had missed, and it did not. That means this enumeration
is, on the evidence available today, **a complete restatement of a careful reading rather than a
discovery** — and it means the census's value is prospective, not retrospective: it will catch the
*next* channel, not this generation's. Reporting a clean sweep as a strong result is exactly the
error mg-9a19 called out in its own 19/19, so it is reported as a weak one.

**E5 and E11 are both errors in the same direction**: I under-counted my own residual. That is worth
one sentence rather than a paragraph, and the sentence is that the numbers a repair predicts about
*itself* deserve the same suspicion as the ones it predicts about its parent.

---

## 7. This repair's own defects, kept rather than tidied away

**Three, and the third is the serious one.**

1. **The channel reporter summed a per-block bound.** Its first output printed `A3 … 70 lines
   exempt   BOUNDED 27/block` — the corpus-wide sum against a per-block cap, which reads as a breach
   and is not one. Caught by reading its own output. Fixed to report the largest block, its
   headroom, and how many blocks it is the largest of.
2. **The census's reporting test called a reported channel silent.** It looked for a channel's *id*
   in the control's stdout; the declared-strike control has printed a near-miss **count** since
   mg-cd04 and simply never labelled it, so B4 was flagged as unbounded-and-silent at `1e996fb`
   when its number had been on screen all along. The test now accepts declared evidence strings,
   and the incident is recorded in the source at the site.
3. **Changing `scan()`'s arity broke a consumer no grep for importers finds.**
   `onethird_mg0242_population_census.py` loads the control **dynamically**, so a search for
   `import` statements — which is what I ran before editing — does not see it. It failed with
   `too many values to unpack`. That is the **named-versus-swept shape, in the commit closing a
   named-versus-swept finding**: I enumerated the consumers I could name and did not sweep the ones
   I could not. The call site is now positional and version-tolerant, and it prints the A1/A2/A4
   split; the sweep that would have caught it in the first place (`grep` for every call of the
   changed functions, not for imports of the module) is what found it.

**This is the seventh consecutive deliverable in this lineage to reproduce its own defect class in
its own text, and #3 above is the reproduction.** It is recorded because the streak is the pattern.

### 7.1 This repair's own prose, under the repaired control

mg-9a19's H5 was that mg-cd04's report used the **fence** channel — the one that leaves no record —
where the audit doing the same thing paid two visible `BASELINE` entries. So the same measurement is
owed here, and it is measured rather than asserted:

| document | blocks | fenced regions | evading lines | hits | hits with fences removed |
|---|---|---|---|---|---|
| `OneThird-mg9d7b-ExemptionChannels-Repair.md` (this file) | all | **0** | **0** | **0** | **0** |
| `OneThird-mg9d7b-ExemptionChannels-PREDICTIONS.md` | all | **0** | **0** | **0** | **0** |

**Neither deliverable uses the fence exemption at all**, and removing fences from them changes
nothing, because there are none to remove. Every block in both is checked. That is not a virtue
claimed — it is the one number H5 asked for, and it is 0 twice.

The reason is prosaic and worth stating so it is repeatable rather than lucky: **this report does
not reproduce the G1 defective sentence anywhere.** It did not need to, so it did not, and the
question of how to quote it without either tripping the control or hiding behind a fence never
arose.

---

## 8. What I did **not** do

* **I did not widen either population.** B6 — `docs/*.md` does not descend, so 14 documents in the
  `docs/` tree are never read — is **printed, by name, on every run** and otherwise untouched.
  Widening the glob is mg-cd04's still-open **G3**; mg-9a19 filed H4 separately for that reason and
  had already swept the unread part and found it clean. A6 — the live-claim control reading one
  document — is likewise printed and left, on mg-cd04's argument that the *signatures* cannot be
  widened (mg-0242 §8 measured them at ~94% false positive corpus-wide).
* **I did not close H3 (B3).** Block-scope backing of a sentence-scope declaration is **reported**,
  not failed on. Making it fail produces exactly one new hit, and that hit is the mg-9a19 audit
  quoting this control's own rule — so closing a LOW finding would cost a permanent new tolerance.
  Reporting is the convention this control already uses for near misses.
* **I did not touch G3 or G4**, which mg-cd04 left open and which remain open.
* **I did not re-open C5**, the ledger's one live entry, or any mathematics.
* **I did not rewrite mg-9a19's audit.** Its findings stand as filed; §8 of it says the dispositions
  are pm-onethird's, and this document is where they are recorded. The only thing changed in its
  instrument is the `RECORDED` table, which that instrument exists to have changed deliberately.
* **I did not apply the rule to `scripts/`**, which no control reads and where mg-9a19 §3.1 showed
  the declared-strike rule trips four times — twice inside the module that defines it. Out of scope
  and left as filed.
* **I did not verify the bounds are RIGHT.** The census asserts that no channel is invisible. That
  is a strictly weaker claim than "these are the correct bounds", and the report says so where it
  prints its verdict.

---

## 9. A correction to the ticket's own framing, which it asked for

The brief says *"pm-onethird's framing: the repair bounded one channel and the other remains
unbounded"*, and asks that it be treated as a hypothesis. It holds — but it undercounts twice.

* There were **not two** channels. There are **fifteen**, of which **nine** were in violation of the
  invariant at the parent tree. H1 and H2 were the two large ones, not the two.
* The **fix for H2 is not a bound.** The brief's item 2 asks for each channel to be bounded or to
  print what it skips; item 3 asks for the unclosed fence to be handled explicitly. Those turn out
  to be the same instruction for B1 and the opposite one for B2: the closed fence stays unbounded
  and gains a number, while the unclosed fence stops being an exemption at all. A repair that read
  item 2 alone would have capped the fence skip and left malformed input silently truncating the
  population under the cap.

**And the ticket was right to be filed as a class.** Bounding A2 alone would have left A5 — a
larger, quieter channel in the same control — untouched and unnamed, because nothing on anyone's
list pointed at it.

---

*Deliverable for mg-9d7b. Instruments:
`scripts/onethird_mg9d7b_exemption_channel_census.py` (new; `--selftest`, `--demonstrate <rev>`),
plus channel reporting added to both controls in place. Predictions committed at `6e7c27b` before
any script of this repair existed: 11 hit, 3 missed, 1 partial, and the miss that matters is E13
against myself. Battery green at this branch: live-claim 0, declared-strike 0, ledger 0, population
census 0 (2 baselined gaps), identity re-check 0, mg-9a19 audit 0 (re-recorded), channel census 0.
Negative controls unchanged: `1b00147^` 1, `1b00147` 1, `--demonstrate bb1cb9b` 0.*
