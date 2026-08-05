# mg-76d0 — INDEPENDENT AUDIT of the mg-a471 partial-report repair

**Subject:** `9072f34` — *"close the mg-3946 verdict — a subset run can no longer overwrite the
canonical report, print a cross-population ratio, or exit 0; three counting claims corrected at
every site (mg-a471)"*, merged on `main`.

**Filed LATE.** This audit was not filed in the same action as its parent — mg-a471 went out without
it, against pm-onethird's own standing rule, and the ticket records that. Recorded here because the
lateness is a fact about the *process*, not about the evidence: every measurement below was taken
against `main` at the audit's own HEAD, five days after the repair merged, and nothing about the
five-day gap makes a digest or an exit code weaker. What lateness does cost is the thing this audit
found in §3 — two stale sites that shipped, sat on `main` for five days, and were read by nobody in
between.

**Predictions were pre-registered** in `docs/OneThird-mg76d0-PartialReport-IndependentAudit-Predictions.md`,
committed as `7bc60a8` **before any run below executed**. No prediction has been revised. The misses
are kept as misses.

---

## 0. Verdict

| # | The parent's claim | Verdict |
|---|---|---|
| **1** | A subset run can no longer **overwrite the canonical report** | **HOLDS** (measured, X1–X5) |
| **2** | A subset run can no longer print a **cross-population ratio** | **HOLDS** (measured, X1, X3) |
| **3** | A subset run can no longer **exit 0** | **HOLDS** (measured, X1, X3, X4) |
| **4** | *"three counting claims corrected at every site"* | **REFUTED for the window claim** — 5 corrected, **7 asserting sites**; as merged at `9072f34` two `.yml` comments still said **21 hours**, one of them in a file that commit edited (§3b). Corrected in this commit. |
| **F-i** | *(the floor — named by no brief)* | A **full** run still overwrites the committed acceptance record in place, exit 0 and silent, and no control compares that record with what the code produces (§4) |
| **F-ii** | *(the floor)* | The **exemplar** instrument's committed record — mg-3946's falsifier, the one mg-a471 copied `cases_requested`/`partial_run` from *"so it does not ship the defect it reports"* — is a `partial_run: true` report over **zero** cases with `ALL_PASS: true`, at its canonical path, on `main` (§4) |
| **F-iii** | *(introduced by the repair)* | On a subset that runs a column but exercises no UNSEEN row, the new fallback prints *"the … column was not run"* about a column it ran (§2) |

The three F5 defects were three separate defects and the repair closes **all three** — tested
separately, as the ticket asked, precisely because a repair can close one and leave another. It did
not.

The parent's *other* headline — *"corrected at every site"* — is the one that fails, and it fails in
the same shape it was written to close: **a count corrected in some places and left standing in the
others.** That makes three turns in a row (mg-3934 → mg-3946 → mg-a471) in which the author of the
"corrected at every site" sentence had not corrected it at every site.

---

## 1. What was actually run

`scripts/onethird_mg76d0_partial_report_audit.py`, this audit's own instrument, eight checks,
`data/onethird-mg76d0-partial-report-audit.json`. Every check runs the demo **as merged**, from the
repository root, and reads back three things independently: the exit code, the SHA-256 of *both*
report paths before and after, and the ratio sentences the run printed. The canonical report is
digested around **every** check, so a write to it is caught whether or not the run admits to one.

Per the standing rule that an instrument must not ship the defect it reports — the rule that
produced `cases_requested`/`partial_run` in mg-3946's falsifier, which mg-a471 then copied into the
demo — this instrument carries it one step further out: a subset audit (`--only X1,X7`) writes
`data/onethird-mg76d0-partial-report-audit.PARTIAL.json`, every report records
`checks_requested`/`full_battery`/`partial_run`/`IS_THE_AUDIT`, and an unacknowledged subset audit
exits 2. It also refuses the defect X6 finds in its subject: an unrecognised `--only` selector is
rejected **by name, before any work**, rather than raising five minutes in.

### The eight checks — **8/8 predictions held, none revised**

| # | invocation | predicted | **observed** | canonical path written? | landed at |
|---|---|---|---|---|---|
| X4 | `--gates ""` | 2 | **2** | no | PARTIAL |
| X5 | `--gates "" --partial-ok` | 0 | **0** | no | PARTIAL |
| X6 | `--only NOPE --partial-ok` | 1 | **1** | no | *(nothing)* |
| X1 | `--only M9 --gates widened` | 2 | **2** | no | PARTIAL |
| X2 | `--only M9 --gates widened --partial-ok` | 0 | **0** | no | PARTIAL |
| X3 | `--only M3` | 2 | **2** | no | PARTIAL |
| **X7** | *(no arguments — the full matrix)* | 0 | **0** | **YES** | **canonical** |
| X8 | the mg-3946 falsifier battery | 0 | **0** | no | *(its own path)* |

Baseline checked rather than assumed: the canonical report was at
`39a4ca34…c97318` at the start, exactly the digest `9072f34`'s message asserts.

*Host note.* Another agent was running an uncapped numpy job on this host; a single gate run went
from ~50 s to 14 min and the load average passed 320. The battery was restarted with the BLAS thread
pool capped at 3 (`VECLIB_MAXIMUM_THREADS` and friends), which is why the durations below are what
they are. It changes wall-clock only — an exit code, a SHA-256 and a printed ratio are
thread-count-invariant, and nothing in this audit reads a duration as evidence.

---

## 2. The three defects, tested separately

They were three compounding defects and a repair can close one while leaving another, so each is
answered on its own evidence rather than by one exit code standing in for all three.

### Defect 1 — a subset run overwriting the canonical report. **CLOSED.**

Six subset runs across three shapes — one column with one case (X1, X2), both columns with one case
(X3), no column at all (X4, X5) — and the canonical report's SHA-256 is **unchanged across every
one of them**, measured before and after each check by an instrument that does not ask the run
whether it wrote. Each landed on `…-gate-class-closure.PARTIAL.json` instead, and that path is
gitignored (`.gitignore:36`, `data/*.PARTIAL.json`, verified with `git check-ignore -v`), so the
other route to becoming a committed record is closed too. `git status --porcelain data/` never shows
the canonical path after a subset run.

### Defect 2 — a headline ratio whose halves count different populations. **CLOSED**, with a new fault in the sentence that replaced it.

X1 is the case mg-3946 named as the sharpest form of it. It used to print `1/5 … are caught` and
`0/5 of them were fatal to nothing before it` — five rows in each denominator, over a run that asked
for one row and one column. It now prints:

```
  1/1 were caught by the widened gate
  the pre-widening column was not run
```

and the report carries both denominators as data — `unseen_mutations_run_widened: ["M9"]`,
`unseen_mutations_run_pre_widening: []` — so the sentence is checkable against the artifact rather
than trusted. That is the repair, and it works.

**But the fallback wording is wrong, and X3 measures it.** `--only M3` runs **both** gate columns —
`gates_requested: ["pre-widening","widened"]`, `n_cases: 4` in the report it wrote — and prints:

```
  the widened column was not run
  the pre-widening column was not run
```

Both columns ran. The branch tests `if unseen_run_widened else …`, i.e. whether the **UNSEEN ∩ run**
set is empty, not whether the column was requested; M3 is a *seen* mutation (`mg-5ad1`), so both
intersections are empty and the run reports two columns as not-run when it executed both. mg-a471's
own comment on that branch states its intent exactly — *"a column that was not requested at all gets
said in words rather than quoted as `0/0`, which reads like a measurement and is not one"* — and the
condition written does not test that. The report body contradicts the sentence printed above it,
which is the same shape as the defect being repaired, one layer in: **the population is now
consistent between numerator and denominator, and the sentence that describes an empty population
misnames it.** The honest wording is *"no UNSEEN row was exercised in this column"*, which is true
in all four cases (X1's left column, X3's both, X4/X5's neither).

### Defect 3 — a subset run exiting 0. **CLOSED.**

`--only M3 && echo ok` no longer says the demonstration passed: X3 exits **2**. So do X1 and X4.
`--partial-ok` restores 0 over the rows that ran (X2, X5), which is the narrower question a subset
can answer, and the report still goes to the PARTIAL path and still records `partial_run: true` — so
acknowledging a subset at the command line does not buy a way back to the canonical path. That
separation is the right one and it holds under measurement.

**One hole in it, pre-registered as X5 and confirmed.** `--gates "" --partial-ok` exits **0** having
executed **zero gate runs**, prints *"Every case that RAN held its assertion, and that is the whole
of what this says"*, and writes a report with `ALL_PASS: true` over an empty `cases` list. The
sentence is true and vacuous. `--partial-ok`'s 0 means "every row that ran held", and over no rows
that is not a weaker claim than the demonstration's — it is no claim at all, dressed as a pass. It
is only a hole in the exit code, not in the artifact (the report lands on the PARTIAL path with
`partial_run: true` and an empty case list, so a reader who parses it sees the vacuity), and the fix
is one line: an acknowledged subset that ran nothing should not exit 0.

---

## 4. The floor — what no brief here named

Two findings, both measured, and the second is worse than the first.

### F-i — the canonical path is defended against a subset run **and against nothing else**

X7, a **full** run of the matrix, taking 1780.9 s:

| | |
|---|---|
| exit code | **0** |
| canonical report before | `39a4ca340ffeb74f…` |
| canonical report after | `0cb9031105b6c939…` — **overwritten in place** |
| anything said about it | `wrote data/onethird-mg75f0-gate-class-closure.json`, then straight to `Demonstration complete.` |
| restored by | this audit, with `git checkout --` |

All three of mg-a471's repairs are gated on one predicate, `partial_run`, and a full run is not
partial — so the output path, the ratios, the report body and the exit code all take the other
branch and the committed acceptance record from `9fa4aaa` is replaced by a developer-box run without
a word. The commit message is candid that this happened during the repair itself: *"the full-matrix
run made here was a verification and its output was discarded."* **Discarded by the author's
discipline, not by the instrument** — which is what the `.PARTIAL.json` split exists to stop being
necessary, in the neighbouring case.

And nothing anywhere would notice. There is no control in the corpus that compares the committed
report with what the code produces: `gate-mutation-demo.yml` regenerates it on every gate-touching
merge, uploads it as a build artifact, and never diffs it against the committed one. So the record
can be replaced locally (X7), or drift from the code that claims to produce it, and both are
invisible in either direction.

The asymmetry mg-a471 created is worth stating plainly, because it is the good half of this finding:
a *parser* can now tell a partial report from a full one — except at the one path that matters. The
committed record predates the fields, so `report["partial_run"]` on the only such artifact in the
tree is **absent**, and absent is indistinguishable from `false` to every consumer that uses `.get`.
mg-a471 declines to refresh it for a good reason (`885c1d1`, *"commit mg-5ad1's probe record from an
UNPINNED run"*, is the mistake in the other direction) — but the consequence is that the second line
of defence is not yet present at the path it defends.

### F-ii — the exemplar instrument's committed record is a **zero-case partial run**, and it is on `main` now

mg-a471 cites mg-3946's falsifier as the model it copied from: *"which carries
`cases_requested`/`partial_run` so it does not ship the defect it reports."* Here is that
instrument's committed artifact, `data/onethird-mg3946-closure-demo-falsifier.json`, written by
`0322264` and unchanged since:

```json
{ "cases_requested": [],
  "partial_run": true,
  "part1_2_cases": [],
  "part1_predictions_missed": [],
  "ALL_PASS": true }
```

**The corpus's committed evidence that the demo can fail — six drifts, six exit codes predicted
before running and held — is the report of a run that executed none of the six.** It sits at the
canonical path, unmarked there, with `ALL_PASS: true`, and `part1_predictions_missed: []` is empty
because no prediction was tested, not because none was missed. The 6/6 lives in the prose; the
artifact beside it records zero.

This is F5's failure mode exactly, in the instrument mg-a471 held up as the one that does not have
it. The falsifier has the **field** — so `partial_run: true` is right there for a parser, and that
is the half it genuinely models — but it has **no path split**: one output path, and `json.dump` at
the end of any run whatsoever. mg-a471 took mg-3946's two repairs as AND rather than OR, applied
both to the demo, and applied neither back to the exemplar it took them from. It is also the
committed instance of X5: a vacuous `ALL_PASS: true` over an empty case list, except here it was
committed.

**X8 appears to be the first full execution of that battery on record.** It ran all six drifts,
`part1_predictions_missed: []` — genuinely 6/6 this time — and exited 0. Its output is preserved as
`data/onethird-mg76d0-falsifier-rerun.json` and the committed record was restored with
`git checkout --` rather than replaced: replacing an acceptance artifact with a developer-box run is
`885c1d1`'s mistake and it is not this audit's call to make. **The recommendation is not to commit
my run — it is to give the falsifier the same two-path split mg-a471 gave the demo, and then let a
full run land a non-vacuous record.**

---

## 3. The counting claims — corrected-count against site-count

The ticket asks for the ratio rather than a verdict, *"the parent's defect was fixing one of four."*
Here are four ratios. A **site** below is a place that **asserts** the figure. A place that quotes a
superseded figure as history (*"the ticket said 21 hours"*) is not a site and is not counted — that
distinction is what keeps this from being a word-count.

### (b) the window — **5 corrected / 7 asserting sites. REFUTED.**

`scripts/refinery_gate.sh:165` says the measured figure *"is now the figure at all **FIVE** sites"*.
`docs/OneThird-mg3946-VerdictCloseout.md:219` says *"all five sites now carry the same measured
figure, which is what makes the next reader's grep agree with itself"*. There are seven, and the
next reader's grep does not agree with itself:

| # | site | says | |
|---|---|---|---|
| 1 | `scripts/refinery_gate.sh:144` | 24 h 08 m 55 s | corrected by mg-a471 |
| 2 | `scripts/refinery_gate.sh:250` (the branch text a merge author sees) | 24 h 08 m 55 s | corrected by mg-a471 |
| 3 | `.github/workflows/gate-mutation-demo.yml:35` (header) | 24 h 08 m 55 s | corrected by mg-a471 |
| 4 | `docs/OneThird-mg3934-CI-HistoryDepth.md:53` (§2) | 24 h 08 m 55 s | corrected by mg-a471 |
| 5 | `docs/OneThird-mg3934-CI-HistoryDepth.md:165` (§3.4) | 24 h 08 m 55 s | corrected by mg-a471 |
| **6** | **`.github/workflows/gate-mutation-demo.yml:205`** | **"21 hours"** | **left standing — in a file `9072f34` edited** |
| **7** | **`.github/workflows/script-controls.yml:74`** | **"21 hours"** | **left standing** |

Verbatim, as merged at `9072f34`:

```yaml
# .github/workflows/gate-mutation-demo.yml:203-206
      # It runs here, ahead of the ~30 minutes below, because the failure it
      # catches is one the demonstrations cannot distinguish from their own:
      # `cannot read <gate> at <rev>` looked exactly like a demo failure for 21
      # hours.  Named at the top of the job it is unmistakable.
```

```yaml
# .github/workflows/script-controls.yml:72-75
      # It runs on EVERY commit under scripts/, data/ or docs/, and that is the
      # reason it is here and not only in the paths-filtered job: the defect it
      # is for -- mg-75f0's class-closure demo dead on arrival in CI for 21
      # hours because af7fc2df is not in a depth-1 clone -- was found by a red
      # run, and a second instance in a step that runs later would have been
      # just as invisible.
```

Both are **assertions of the measured window**, not quotations of the ticket: *"looked exactly like
a demo failure for 21 hours"* and *"dead on arrival in CI for 21 hours"* are statements about how
long the outage lasted. The measured answer is **24 h 08 m 55 s**, and mg-a471 is the commit that
established it as the one figure the corpus carries.

One of the two is in `.github/workflows/gate-mutation-demo.yml` — a file `9072f34` opened and
edited, correcting the figure in the header 170 lines above the site it left standing.

**Both are hard to find, and that generalises.** Each splits the phrase across a comment
continuation — `for 21` ends one line, `# hours` begins the next — so `grep -rn "21 hours"` returns
**neither**. This audit's sweep flattens comment continuations before matching, which is why the two
sites are in this table. **A sweep for a stale number in a corpus that hard-wraps its comments must
be wrap-aware, or its "no sites left" result means "no sites left on one line".** That is the
transferable part, and it is worth more than the two comments.

### Concurrent arrival: `mg-a75e` reached the same two sites, from the other direction

**Recorded because it changes the causal story and not the finding.** While this audit was running,
`8d1e17a` (mg-a75e) merged, landing the **same two corrections** — rescued from the uncommitted
working tree of a polecat that had been working mg-a471 and died on 2026-07-31. So the reason the
two sites shipped is **not** that a wrap-blind grep failed to see them: mg-a471's author had found
them and written the fix, and the fix died with the process before it was committed. The wrap
observation above stands as a fact about the corpus and is no longer offered as the explanation.

What the two arcs share is only the answer. mg-a75e had the corrections in hand and had to judge
whether to land them; this audit had nothing but `9072f34` as merged and a sweep, and
**pre-registered `5 corrected / 7 asserting sites` as a refutation of *"all five sites"* before
running anything** (`7bc60a8`, from a base predating `8d1e17a`). Two independent routes to the same
count is worth more than either alone, and it is the reason the corrections in this commit reduce to
one line of annotation: main already carried them by the time this branch rebased.

**What does not change:** the verdict on `9072f34`. As merged, that commit claimed the window figure
was at *"all FIVE sites"* and there were seven. A defect fixed concurrently by someone else is still
a defect the audited commit shipped.

### (a) the revisions — **fully corrected. VERIFIED, re-derived independently.**

The claim *"5 literals, 3 distinct revisions, 3 scripts"* re-derived from the source rather than
from the table:

| literal | site |
|---|---|
| `af7fc2df` | `scripts/onethird_mg75f0_gate_class_closure_demo.py:314` `PRE_WIDENING_REV` |
| `af7fc2df` | `scripts/onethird_mg4f9b_route_axis_probe.py:111` `PRE_WIDENING_REV` |
| `af7fc2df` | `scripts/onethird_mgbd53_widening_audit_probe.py:106` `PRE_WIDENING_REV` |
| `91fa25f` | `scripts/onethird_mg4f9b_route_axis_probe.py:115` `MG75F0_REV` |
| `9fa4aaa` | `scripts/onethird_mg4f9b_route_axis_probe.py:529` `gate_source("9fa4aaa")` |

**5 literals, 3 revisions, 3 scripts** — agreeing with mg-a471 and with mg-3946, and no site still
asserts four. `scripts/onethird_mg3934_ci_history_depth_control.py --static-only` re-run here:
passes its seven self-test drifts and reports one history-reading workflow with `fetch-depth: 0`.

*Boundary case, recorded because the count depends on a convention nobody wrote down:*
`scripts/onethird_mg3946_closure_demo_falsifier.py:151-152` contains two further revision literals,
`'PRE_WIDENING_REV = "af7fc2df"'` and its replacement `'PRE_WIDENING_REV = "9fa4aaa"'`. They are
drift text rather than pins the corpus resolves at its own revisions, so excluding them is right —
but the replacement *is* resolved, inside the drifted tree, by the rebaselined demo. Under
"literals a run can be required to resolve" the count is **7 in 4 scripts**. Not a defect; the
convention should be stated where the count is.

### (c) "eight consecutive runs" — **already correct. VERIFIED, nothing to do.**

The only surviving `8 consecutive` is `docs/OneThird-mg3934-CI-HistoryDepth.md:33`, which is an
explicit quotation of the ticket's undercount immediately corrected in the following table. No site
asserts eight. mg-a471 recorded this as *"verified, nothing to do"* and that is what it is.

### (d) "eighteen gate runs" — **0 corrected / 6 asserting sites; disclosure covers 2.**

The full matrix is `8 cases × 2 gate columns = 16` gate runs, and the committed acceptance record
has exactly **16** entries in `cases`. Six sites say eighteen:

| # | site | |
|---|---|---|
| 1 | `scripts/onethird_mg75f0_gate_class_closure_demo.py:145` (the run-line) | a **code** site |
| 2 | `.github/workflows/gate-mutation-demo.yml:165` | |
| 3 | `.github/workflows/gate-mutation-demo.yml:247` | |
| 4 | `docs/OneThird-mg75f0-GateClassClosure.md:243` | |
| 5 | `docs/OneThird-mg75f0-GateClassClosure.md:607` | mg-a471 edited the lines immediately below this one |
| 6 | `docs/OneThird-mg3946-VerdictCloseout.md:27` | **written by `9072f34` itself** |

mg-a471 **found this** and disclosed it (`VerdictCloseout.md:169-174`, *"Noted, not fixed … outside
this closeout's remit"*). That disclosure is a credit and it is why (d) is not scored as a missed
count. Two things are new here:

* the note names **2** sites; there are **6**, and two of them are in the CI workflow the note does
  not mention;
* **the closeout asserts "eighteen gate runs" in its own §1 opening, 144 lines above its own note
  that the number is 16.** A document that both states a count and states that the count is wrong
  answers whichever of the two a reader reaches first.

All six are corrected in this commit, and the arithmetic is now checkable against the artifact
beside it: `16 = (7 mutations + 1 unmutated) × 2 columns`, and `len(cases) == 16` in the committed
report and in the full run measured in §4.

### The new standing control does not reach any of the three

`8d1e17a` also landed `scripts/onethird_mga471_partial_run_control.py` — a genuinely good piece of
work, and the right shape: it drives the demo's real `main()` over a fake `run_case`, so seven
properties cost **0.3 s** instead of sixteen gate runs, and it carries three self-test drifts of its
own subject. Re-run here: all three drifts fire, all seven properties hold. It closes the gap this
audit's own battery could not — a check nobody can afford to run is a check nobody runs, and 35
minutes on a loaded host is exactly that.

It does not cover any of the three findings above, and the reason is instructive rather than a
criticism: **all seven of its invocations are `--only M9 --gates widened` variants or full-matrix
equivalents.**

* **F-iii** — its property at line 273 asserts that `"the pre-widening column was not run"` appears
  for `--only M9 --gates widened`, where that sentence is **true**. So the control encodes the
  wording as a correctness property in the one case that cannot expose it, and would stay green
  while `--only M3` prints the same sentence about a column it ran.
* **The vacuous `--partial-ok`** — no invocation passes an empty `--gates`, so nothing exercises the
  zero-row case.
* **F-i** — `scenario_not_partial` asserts a full run **does** write the canonical path. That is
  correct as a statement of the design; it is the design that leaves the committed record
  unprotected, so a control that pins the design cannot see it.

Each is one more invocation in a file that already has the harness for it, which is why they are
worth naming precisely rather than describing.

---

## 5. Do not disturb — re-run and report

* **The mg-75f0 demo still fails when it should.** X8 ran mg-3946's battery in full: **6/6
  predictions held**, `part1_predictions_missed: []`, PART 3/4 self-test clean, exit **0**. The six
  predictions were stated before mg-a471 existed and are unchanged and unrevised; mg-a471 moved only
  the invocation, adding `--partial-ok` to all six, and the battery's output confirms the reason —
  every one of the six now prints `*** PARTIAL RUN — THIS IS NOT THE DEMONSTRATION (mg-a471) ***`
  and still returns the exit code its prediction names. Revert the repair and `--partial-ok` becomes
  an unrecognised argument, so `control` fails loudly rather than the fix rotting out quietly; that
  design holds.
* **The noop-mutation case** — M9's replacement byte-identical to its anchor, so the widened gate
  exits 0 and the demo must reject the run — is among the six and held at its predicted **1**.
* **CI at HEAD, measured now:** run `30996384208` on `main`, **success**, **16 m 05 s** against the
  75-minute bound, all thirteen steps green including all four demonstration steps
  (`mg-3934 CI history-depth control`, `mg-7db4 watchlist consistency`, `mg-7db4 probe mutation
  battery`, `mg-60d3 gate mutation demo`, `mg-75f0 gate class-closure demo`). The ticket's figure
  was 16 m 22 s; this is the same job one commit later.
* **The demonstration's own headline is unchanged.** X7's full run: `ALL_PASS: true` over all
  **16** rows, `unseen_mutations_run_widened` and `unseen_mutations_run_pre_widening` both
  `["M5","M6","M7","M8","M9"]`, headline **5/5 and 5/5**. Nothing in this audit touched the subject's
  behaviour.

---

## 5a. Predictions, and the misses

**Eight exit codes pre-registered, eight held, none missed, none revised** — and that is a weaker
result than it looks, so it is worth saying why rather than banking it. Six of the eight (X1–X4, X6,
X7) were read straight off the diff before running; predicting them tests that the code says what it
appears to say, not much more. The two that carried information were **X5**, which predicted a hole
rather than a behaviour — that an acknowledged run over zero rows would exit 0 with `ALL_PASS: true`
— and **X7**, whose registered artifact claim (*a full run overwrites the committed record in place,
silently*) is the floor finding.

The falsifier's own six, re-run here in full: **6/6 held** — `control` 0, `neutered-widening` 1,
`noop-mutation` 1, `rotted-anchor` 1, `rebaselined` 1, `crash-not-catch` 1. Unchanged and unrevised
since mg-3946 stated them.

**Three of this audit's findings were not predicted at all** and are the better half of it: the two
wrapped `21 hours` sites (found by changing the sweep, not by predicting), the false *"column was
not run"* sentence (found by running X3 and reading what it printed), and the falsifier's
zero-case committed record (found because the battery dirtied a file this audit then looked at).
None would have appeared in a run that only checked its own predictions.

---

## 6. What was changed by this commit, and what was not

**Changed** — the stale counts, all of them contradicted by an artifact in the same tree:

* the six `eighteen gate runs` sites (§3d) → **sixteen**, with `8 × 2` written next to the number so
  the next reader can check it without running anything;
* `refinery_gate.sh`'s *"the figure at all FIVE sites"* → **seven**, enumerated.

The two `21 hours` sites are **not** changed here — `8d1e17a` corrected them while this audit was
running (§3b), so this branch adds only the note that a second arc reached the same count
independently and the wrap-blindness fact a future sweep needs.

**Not changed** — the subject's behaviour. No line of
`scripts/onethird_mg75f0_gate_class_closure_demo.py` outside its docstring, and no line of the
falsifier, was touched. The three findings above are reported, not repaired: the
`unseen_run_* is empty` wording (§2), the vacuous `--partial-ok` exit 0 over zero rows (§2), the
canonical path's exposure to a full run and the falsifier's missing path split (§4). They belong to
whoever owns the next turn on this instrument, with the evidence for each already measured here.

---

## 6. Not claimed

* **The two `.yml` sites are corrected in this commit, not merely named.** The finding is about
  mg-a471's *claim*, and the claim is in the git history whatever the working tree says; leaving a
  figure known to be wrong standing in CI comments, in an audit whose whole subject is stale
  figures, would have been the defect a fourth time. The pre-fix text is quoted verbatim in §3 and
  is readable at `9072f34`.
* **This audit did not re-derive the 86 935 s window from the Actions API.** It takes mg-3934's
  timestamp table as given and audits only whether the figure derived from it is stated
  consistently. A wrong window stated consistently everywhere would pass §3 and fail a different
  audit.
* **`ALL_PASS` is not audited.** Whether the demonstration's matrix is *correct* is mg-75f0's
  question and mg-3946's; this audit asks only what a partial run does to the record of it.
