# INDEPENDENT AUDIT of the mg-cd04 repair of mg-0242 G1/G2 (mg-9a19)

**Target:** `f6e329c` (mg-cd04) — *"close mg-0242 G1 + G2 — back the declared strike with markup,
bound the EXEMPT label, and take the population corpus-wide"*, whose deliverable is
`docs/OneThird-mg0242-G1G2-Repair.md`.

**Pre-filed in the same action as its parent.** This audit did not re-do the repair. It ran the
repaired controls, extended the parent's mutant table rather than re-running it, enumerated the
populations, re-derived the ledger drift from both ends, and pointed the repaired control at the
repair's own new prose.

**Instrument:** `scripts/onethird_mg9a19_exemption_population_audit.py` — parts (P) population,
(B) bounds, (M) mutants, (S) self, (L) drift. Exits 1 if any recorded mutant outcome moves in
either direction. In CI on the default path; the history read is behind `--drift`, no revision
named in code (mg-3934).

---

## 0. Verdict

**The repair is sound and its two findings are closed.** G1 is closed at the site and, for the
structural rule, at a population of 242 documents. G2's bound exists, is enforced, and is exact.
The ledger-drift reading is confirmed, and the parent's correction of it (`LIVE 7` was `LIVE 8`)
reproduces independently.

Five findings, none of which reverse that.

| # | finding | severity |
|---|---|---|
| **H1** | G2 bounded **one of two** exemption channels in the block it repaired. The other — a sub-paragraph that carries a quotation — is exempt **entire, at any length**. The evasion the ticket asked for still exits 0 when the refuted sentence is appended to a quoting sub-paragraph instead of opening a new one. | **MEDIUM** |
| **H2** | The **new** corpus-wide control skips fenced code **entirely, on an opening marker, with no length bound** — structurally the same exemption G2 had just removed from its sibling. An **unclosed** fence skips to EOF, and one document in the corpus already has one. | **MEDIUM** |
| **H3** | In that same control the **declaration** test is per sentence and the **backing** test is per block, so one unrelated `~~` span anywhere in a block exempts every declaration in it. | **LOW–MEDIUM** |
| **H4** | Population: the control's glob is non-recursive. `docs/` holds **256** markdown documents and it reads **242**; the repo holds **266**. The 24 unswept were swept here and are **clean**, so this is coverage, not a live defect — but the new population claim is not registered with `onethird_mg0242_population_census.py`, the instrument that exists for exactly this class of claim. | **LOW** |
| **H5** | The repaired control over the repair's own prose: **0 hits, and 1 block that would have been a hit**, evading through the fence channel the same commit created. The sibling act — the mg-0242 audit quoting the same sentence — costs **2 visible `BASELINE` entries**. Same act, two conventions, and the repair put its own text on the one that leaves no record. Sixth consecutive reproduction of the class in this lineage, at low severity. | **LOW** |

**Confirmed and not disturbed:** every do-not-disturb item in §5, all re-run.

---

## 1. The primary question: the population, not the rule

### 1.1 What ranges over what

Measured by part (P), which partitions every `*.md` in the working tree and asserts the buckets sum.
Counts at the audited tree `f6e329c`; the second column is this branch, which adds one document —
this one.

| | at `f6e329c` | here |
|---|---|---|
| `*.md` in the repo | **266** | 267 |
| `docs/` as a directory tree | **256** | 257 |
| read by `onethird_mgcd04_declared_strike_control.py` (`docs/*.md`, non-recursive) | **242** | 243 |
| where the ledger's ten refuted claims live | **3** | 3 |
| read by `onethird_mg8a71_live_claim_control.py` — **where G2 was repaired** | **1** | 1 |

**The difference is the finding, and there are two of them.**

**The first is G2's own.** The parent widened the population for the *structural* rule (G1) and
argued, correctly and with mg-0242 §8's measurement behind it, that the *signature* rule cannot be
widened. But G2 is neither: it is a change to the **classifier** — how far a marker reaches — and
the classifier is not confined to one document. It is imported by
`onethird_mg0242_struck_vs_refuted.py` and applied there to **3** documents in part (A) and to
**242** in part (B). So the rule G2 changed is *enforced* by a control over 1 document and *applied*
over 242, and the mutant battery that demonstrates it mutates only the 1. That is not a defect in
the repair — the parent's scope was G1 and G2 as filed — but it is where the next instance of this
class will come from, and it is the answer the ticket asked for: **the rule's blast radius exceeds
its test surface by a factor of 242.**

**The second is the new control's own.** `docs/` has three subdirectories holding 14 markdown
documents; `glob("*.md")` does not descend. The docstring's *"every `*.md` in `docs/`"* is true of
the glob and false of the directory; the report and the CI comment both say *"242 documents … the
corpus"*. Ten more tracked `.md` files sit outside `docs/` (`README.md`, `generalization.md`,
`simplifications.md`, `audit-step8-*.md`, `lean/*.md`, `notes/*.md`).

**Swept, because a population finding that does not run the rule over the unswept part is the same
finding one level up.** Part (P) applies the declared-strike rule to all 24 unswept documents,
7 244 lines: **0 hits.** The gap is coverage, not a live defect, and this audit says so rather than
implying otherwise by leaving it unmeasured.

What is left open is bookkeeping with a history: `onethird_mg0242_population_census.py` exists to
check that every population a control **names** equals the population it **sweeps**, carries two
baselined doc-level gaps, and was **not touched** by `f6e329c` (empty diff). The repair added a
control that names `242 documents, 100 527 lines` and did not register it. G3 is explicitly out of
mg-cd04's scope; this is not a scope violation, it is the observation that the pile G3 is about grew
by one entry in the commit that closed G1 and G2.

### 1.2 The evasion, constructed after the fix

The ticket asked for a refuted sentence in the tail of a long annotation block, and predicted the
repaired control would now exit 1. **It does — for the parent's construction, and not in general.**

`exempt_partition` grants exemption two ways. The label's own sub-paragraph is exempt on the label's
word, bounded. **Every other sub-paragraph is exempt if it carries a quotation — with no bound at
all.** The parent's M1 appends `> ` + the sentence, opening a *new* sub-paragraph that quotes
nothing, so it is checked. Append the same sentence to a sub-paragraph that **already** carries its
quotation and the whole sub-paragraph, at any length, stays exempt.

The parent's three-mutant table, **extended** (part (M); M1–M3 are the parent's and are asserted by
`onethird_mg0242_struck_vs_refuted.py`):

| mutant | placement | exit | |
|---|---|---|---|
| M1 | refuted sentence as a **new** sub-paragraph in an `ANNOTATION` tail | 1 | caught (was 0 at mg-0242) |
| M2 | the same sentence as a plain paragraph | 1 | caught |
| M3 | the same sentence in the tail of a `STRIKE` block | 1 | caught |
| **M4** | **the same sentence appended to a QUOTATION-BACKED sub-paragraph** (§2.3's `RE-DERIVATION`, the 53-line block mg-0242 named, last sub-paragraph ending line 304) | **0** | **MISSED** |
| **M5** | the same sentence inside the **label** sub-paragraph, line 2 of 6 | **0** | missed — inside the declared bound |
| **M6** | the same sentence at the bound, line 6 of 6 | **0** | missed — at the declared bound |
| **M7** | the same sentence one line past it, line 7 | **1** | caught — **the bound is exact** |

M4 is the finding. M5–M7 are not a finding: they are the parent's declared residual, measured, and
they establish that the bound is enforced to the line rather than approximately.

**Reach at HEAD, in the one document the control reads:** 4 `EXEMPT` blocks, 22 sub-paragraphs —
4 label sub-paragraphs (4 unbacked lines used of the 24 the bound allows), **9 quotation-backed and
unbounded, totalling 66 lines, longest 11**, and 9 non-quoting sub-paragraphs (59 lines) correctly
checked. Before mg-cd04 all 147 of those lines were exempt; 88 remain. The repair moved 59 lines out
of the blind spot and left 66 in it, and the 66 are the ones that are unbounded.

### 1.3 The length bound: it exists, it is enforced, and this is what it is

`MAX_LABEL_LINES = 6`, in `onethird_mg8a71_live_claim_control.py`, applied in `exempt_partition` to
**sub-paragraph 0 only** — the sub-paragraph the label is read from. Enforced exactly: M6 (line 6)
is missed, M7 (line 7) is caught. It is the only length bound added anywhere by `f6e329c`.

**And the bound the prose names is not the bound the code has.** `MAX_EXEMPT_LINES` appears twice in
that control — at line 47, *"and in no case does a label exempt more than MAX_EXEMPT_LINES lines"*,
and again at line 106, *"never past MAX_EXEMPT_LINES"* — and **there is no such identifier anywhere
in the repository**. The constant is `MAX_LABEL_LINES`, and it bounds the label's own sub-paragraph,
not the block. The named bound is the block-level one, which is what G2 asked for; the implemented
bound is the sub-paragraph-level one, which is what H1 is about. A reader who takes the docstring at
its word concludes M4 is impossible. That is H1 stated in the repair's own words, and it is the
cheapest of the five to fix.

---

## 2. The new control's own exemptions (nothing on the brief's list)

### 2.1 The fence is unbounded — the G2 shape, in the instrument written to close G2

`onethird_mgcd04_declared_strike_control.blocks()` skips fenced code. The rule is argued at length
and it is defensible: inside a fence the corpus shows text as data. But the *implementation* has
exactly the property G2 was filed about — **an exemption granted on an opening marker, with no bound
on how far it runs**:

* a fence skips to the closing fence, however long that is;
* an **unclosed** fence skips **to end of file** (M8: the declared-strike defect placed under a bare
  ` ``` ` is not seen — 0 hits, where the same text bare is 1);
* `~~~` opens a fence too, and a fence opened with one marker is closed by the other;
* the skip is **not reported** — the control prints its population as *"ALL classified (block |
  fenced code | blank)"* and never prints the fenced count, so 4 302 of 100 527 lines (4.3%) leave
  the check with no number attached to them.

**Not hypothetical.** `docs/OneThird-AP-2-Prong3I-beta-RungUniqueness-SD-FLOOR.md` has an odd number
of fence lines today: line 138 opens a fence that is never closed, and the skip runs to EOF. It
happens to hide 2 blank-ish lines. Nothing about the mechanism bounds it to 2.

The fix is the one the repair already wrote for the sibling: bound the skip, and print the number.

### 2.2 Declaration per sentence, backing per block

`scan_text` decides the block is fine and returns before any sentence is examined if `"~~"` appears
anywhere in the flattened block. The rule is stated as *"a **sentence** that says text is struck must
carry the markup"*, and the DECLARATION+QUOTATION test is per sentence — the parent argues at length
that sentence scope is the correct scope and prints a near miss to keep the narrowing visible. The
**backing** test stayed at block scope. So a block containing one unrelated struck span exempts
every declaration in it (M9: 0 hits; the same block without the unrelated span is 1). Both scopes are
per-sentence in the rule as written; only one is in the code.

---

## 3. The repair's own prose, under the repaired control

Part (S), over `docs/OneThird-mg0242-G1G2-Repair.md` — 246 lines, the new prose of `f6e329c`:

| | |
|---|---|
| blocks checked | **56** |
| fenced regions (blocks that **evade**) | **3**, totalling **14 lines** |
| hits | **0** |
| hits with the fences removed | **1** |

**The count asked for is 1.** §1 of the repair's report reproduces the G1 defect verbatim — the
`POPULATION CORRECTION` sentence and the quotation it fails to mark — and it is invisible to the
control because it sits in a fence. The other two fenced regions are the `--tree` output and the
old-vs-new classifier transcript, neither of which would be a hit.

Also swept: `docs/OneThird-mgd112-DroppedVerdict-Closeout.md` (the file the repair edited) — 64
blocks, 3 fenced regions, **0 hits, 0 with fences removed**; and
`docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md` — **2 hits, both baselined**, and
still 2 with the fences removed.

**That last line is the finding.** Two documents in this corpus quote the same defective sentence for
the same reason. One of them — the audit that found it — pays for the quotation with two `BASELINE`
entries: keyed by `(file, quoted span)`, versioned, printed on every run, and failing the run if they
stop matching. The other — the repair that closed it, written afterwards, by an author who had just
built the baseline mechanism — pays nothing, because a fence leaves no record. The repair's report
says the alternative to the fence rule *"was a baseline entry for every document that ever discusses
the defect — a control that grows a tolerance each time it is right."* That is a real cost and the
argument is not wrong. But the fence is not the cheaper version of a baseline entry; it is the
version that cannot be counted, and this arc's entire subject matter is the difference between a
population that is named and a population that is swept.

**This is the sixth consecutive deliverable in this lineage to reproduce its own defect class in its
own text, and the mildest of the six.** The quotation is correct, the fence rule is stated in the
docstring, in the CI comment and in the report, and the parent found the rule by tripping its own
control on its own first draft — which is the failure mode working, not hiding. Severity LOW. It is
recorded because the streak is the pattern, and because the remedy is one line: print the fenced
count, so the channel has a number the way the baseline does.

### 3.1 This audit's own deliverable, and its own tooling

**The deliverable.** Part (S) sweeps this document too: **0 fenced regions, 0 evading lines, 0 hits,
0 near misses** — every block in it is checked. The streak in §0's H5 is a claim about six
deliverables, so the seventh had to be measured rather than asserted. It quotes the G1 sentence
nowhere and uses the fence exemption not at all. The line and block counts are recomputed by part (S)
on every CI run rather than written here, because a count written into prose is a claim that rots and
this arc has spent five findings on that.

**The tooling — and it fired on its first run.** Part (P)'s coverage assertion is there because a
NAMED-vs-SWEPT gap is this arc's recurring defect. On the first execution after this report existed
it failed: `population gap: 267 of 266`. The cause was that the two sides of the comparison came
from **different sources** — the repo-wide count from `git ls-files`, the swept count from the
filesystem glob the control actually uses — so a file on disk and not yet in the index was counted
once and named zero times. That is the mg-8d5e shape, in the instrument auditing a finding about the
mg-8d5e shape, caught by the assertion put there for it. Both sides now come from the union of index
and disk, and the untracked count is printed so they stay reconcilable. Recorded rather than quietly
corrected — the same standard §4 holds the parent to.

**The rule against `scripts/`.** Part (S) also applies the declared-strike rule to `scripts/*.py`,
which no control reads. Four hits in two files:

* `onethird_mgcd04_declared_strike_control.py:40` and `:85` — the docstring and the `BASELINE`
  comment, which describe the rule by quoting the verbs and the site. The module that **defines** the
  rule trips it, and is invisible to itself.
* **`onethird_mg9a19_exemption_population_audit.py:250` — this audit's own instrument**, whose
  `DECLARED_DEFECT` constant is the M8/M9 mutant payload.

Left in place and reported rather than reworded. The honest reading: `scripts/` is clean only because
it is not read, and Python source has no counterpart to the fence — the "this is literal data"
marking that `.md` gets does not exist there. Whoever widens the population past `docs/` inherits
that problem, and this line is the evidence they will need.

---

## 4. The ledger drift, re-derived from both ends

The brief: *same ledger, same classifier — `LIVE 7` at `1b00147`, `LIVE 2` here. Re-derive both, at
both commits, and confirm the difference is the repair working and not the ledger moving.*

Re-derived independently in part (L), which reimplements the ten claim patterns and loads the
**pre-repair classifier from git** alongside the working-tree one, so classifier and text vary
separately — something the parent's `--tree` mode cannot do, because it runs one classifier.

| tree | classifier `bb1cb9b` (pre-G2) | classifier `f6e329c` (post-G2) |
|---|---|---|
| `1b00147` | **7** — C3, C4, C5, C6, C8, C9, C10 | **8** — C3, C4, C5, C6, **C7**, C8, C9, C10 |
| `bb1cb9b` | **2** — C5, C9 | **2** — C5, C9 |
| working tree | **1** — C5 | **1** — C5 |

**And the ruler did not move.** Part (L) parses the `LEDGER` literal out of
`onethird_mg0242_struck_vs_refuted.py` at each revision and compares: the ten claim ids and all
eight regexes are **identical** at `ad9ba10` (mg-0242, which filed the `7 → 2` reading) and at
`f6e329c`. The only change is `KNOWN_LIVE`, the baseline — C9 was removed from the tolerance, not
from the ledger. **The mg-8d5e anchor defect — a comparison whose two sides are not the same ruler —
is absent here.**

With ruler and classifier both pinned, the drift decomposes exactly:

* **`7 → 8` at `1b00147` is entirely the classifier**, and the extra claim is **C7**, sitting in the
  *Machine-checked* sub-paragraph of the 53-line `RE-DERIVATION` block, quoting nothing. The parent's
  correction reproduces, and its stronger statement holds: G2 was not only demonstrable by mutation,
  it was concealing a real ledger claim at the arc's own demonstration commit.
* **`2 → 1` from `bb1cb9b` to the working tree is entirely the text** — C9's markup, added by the
  repair. The classifier makes **no difference** at either of those two trees.
* mg-0242's `LIVE 2` at `bb1cb9b` is confirmed under **both** classifiers, so that half of its
  reading was never at risk from G2.

**Verdict: the reading holds, the parent's correction of it holds, and the difference is the repair
working.** Neither the ledger nor its baseline moved in a direction that would flatter the number.

---

## 5. Do not disturb — re-run

| | claim | result |
|---|---|---|
| 1 | ledger at `bb1cb9b`: 10 refuted, **8 struck**, 2 live (C5, C9) | **confirmed** (part (L), both classifiers) |
| 2 | ledger at HEAD: 10 refuted, **9 removed**, **1 live** | **confirmed**, exit 0 |
| 3 | 5 exit codes predicted, 5 hit (E1–E5 of the repair's §5) | **all 5 re-run and reproduced** |
| 4 | C5 live at **line 475 and nowhere else** | **confirmed** — `LIVE @ lines 475`, single site |
| 5 | the live-claim control **covers rather than carries** the two F1 sites | **confirmed**: `BASELINE` is empty; removing §3.2's `~~` → exit 1, removing §5 rec 2's `~~` → exit 1 |
| 6 | negative controls `1b00147^` and `1b00147` still exit 1 | **confirmed** (4 and 2 new sites) |
| 7 | `--demonstrate bb1cb9b` finds `mgd112` §2.2 and nothing else in 239 documents | **confirmed** |
| 8 | population census still green, `537 → 539` G3 gap untouched | **confirmed**, 2 baselined gaps seen (as of this audit; **mg-1d03 closed both, and the census baseline is empty from 2026-08-05**) |
| 9 | M1/M2/M3 all exit 1 | **confirmed** |

Nothing in this audit's changes touches any of the nine.

---

## 6. Predictions, written before any run

Nineteen, written after reading both controls' source and before executing anything, kept verbatim
below. **19 hit, 0 missed** — which is a weak result and is reported as one: predictions made after
reading the implementation are mostly a check that the reading was right, not that the behaviour was
surprising.

| # | prediction | outcome |
|---|---|---|
| E1 | live-claim control at HEAD → 0 | hit |
| E2 | ledger at HEAD → 0; REFUTED 10 / REMOVED 9 / LIVE 1 = C5 | hit |
| E3 | C5 live at line 475 and nowhere else | hit |
| E4 | declared-strike control at HEAD → 0; 2 hits, both baselined; ≥1 near miss | hit (1 near miss) |
| E5 | `--demonstrate bb1cb9b` → 0; exactly 1 unbaselined, in `mgd112` | hit |
| E6 | live-claim on `1b00147^` → 1 | hit (4 sites) |
| E7 | live-claim on `1b00147` → 1 | hit (2 sites) |
| E8 | ledger `--tree 1b00147` → 0; LIVE 8 there, LIVE 1 here | hit |
| E9 | live-claim `BASELINE` empty; un-striking either F1 site → 1 | hit |
| **E10** | **M4 (refuted sentence appended to a quotation-backed sub-paragraph) → 0, MISSED** | **hit** |
| E11 | M1 (new non-quoting sub-paragraph) → 1, caught | hit |
| E12 | declared-strike under an unclosed fence → missed | hit |
| E13 | declared-strike defect outside `docs/*.md` → not read, if the glob is non-recursive | hit — it is |
| E14 | documents the live-claim control ranges over = 1 | hit |
| E15 | documents the ledger's claims live in = 3 | hit |
| E16 | documents the declared-strike control ranges over = 242 | hit |
| E17 | `.md` files outside `docs/*.md` > 0 | hit — 24 |
| E18 | declared-strike over the repair's own report alone → 0 hits | hit |
| E19 | fenced regions in the repair's own report = 3 | hit |

The one that matters is **E10**, which predicted M4 would exit **0** and therefore **contradicted the
brief's own stated expectation** (*"confirm the control now exits 1"*). It exited 0. The brief's
expectation is correct for the construction the parent used and wrong for the general one, and that
gap is H1.

---

## 7. Redundancy, by independence of failure mode

Three instruments touch this repair. They fail for different reasons, which is the point:

| instrument | fails when | shares with the others |
|---|---|---|
| `onethird_mg8a71_live_claim_control.py` | a named refuted inference is asserted in live text in one document | the classifier |
| `onethird_mg0242_struck_vs_refuted.py` | a ledger claim's live/gone state departs from its baseline, or a mutant is missed | imports the classifier |
| **`onethird_mg9a19_exemption_population_audit.py`** | **an exemption channel's reach changes**, or a recorded mutant outcome moves in **either** direction | imports both, and asserts against **neither**'s baseline |

The new instrument's failure mode is deliberately not "a claim is live". It is "the residual moved" —
so it fires on a *repair* as loudly as on a *regression*, and a future author who closes H1 or H2
cannot do it silently. It records what is missed, not what is caught, which is the one thing the
existing two cannot express: `onethird_mg0242_struck_vs_refuted.py` asserts M1–M3 must all be
caught, and has no way to say that M4 is not.

---

## 8. What this audit did not do

* It did **not** repair H1–H5. This is an audit; the residual is named, measured and executable, and
  the dispositions are pm-onethird's.
* It did **not** touch G3 or G4, which mg-cd04 left open and which remain open. H4 is adjacent to G3
  and is filed separately rather than folded into it.
* It did **not** re-open C5, the ledger's one live entry, or any mathematics.
* It did **not** rewrite the repair's report. This document is the record; `f6e329c` stands as filed.

---

*Deliverable for mg-9a19, independent audit of mg-cd04 (`f6e329c`). Instrument:
`scripts/onethird_mg9a19_exemption_population_audit.py` — new, wired into `script-controls.yml`
after the mg-0242 steps, default path reads no history; `--drift 1b00147 bb1cb9b` for the ledger
re-derivation. 19 predictions written before running, 19 hit, of which E10 contradicts the brief.
5 findings, 9 do-not-disturb items re-run, 7 new mutants. Battery re-run green at this branch:
live-claim 0, declared-strike 0, ledger 0, census 0, identity re-check 0, this audit 0.*
