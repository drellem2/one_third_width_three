# mg-3946 — VERDICT CLOSEOUT

**Subject:** the two OPEN items left by mg-3946's verdict on `0322264` + `c5ce07c` — **F5**, the
floor finding, which mg-3946 named and deliberately did not fix; and **F4**, three counting claims
which mg-3946 reported as *"corrected at every site"* and corrected at some of them.

**Verdict on the parent stands unchanged.** GREEN on the SHA repair, AMBER on what it is taken to
have established, RED on the consumer that landed alongside it. Nothing in this closeout reopens
any of those; §3 lists what it preserves and why each item is load-bearing.

---

## Summary

| # | what | state |
|---|---|---|
| **OPEN 1 (F5)** | A `--only`/`--gates` subset run of the mg-75f0 demo overwrote the canonical report with an unmarked partial one, printed a ratio whose halves counted different populations, and exited 0 — **three defects, compounding**. It bit mg-3946's own audit twice. | **REPAIRED**, all three, measured |
| **OPEN 2 (F4)** | "4 distinct revisions" over a table naming three; a rounded window against a measured one; "eight consecutive runs". mg-3946 fixed (c) and the workflow-header half of (b), and left (a) and the doc half of (b) standing. | **CORRECTED at every site**, re-derived rather than copied |

---

## 1. OPEN 1 (F5) — the floor, which bit the audit twice

### 1.1 What it was

`scripts/onethird_mg75f0_gate_class_closure_demo.py` is the demonstration that mg-5ad1's class is
closed: eighteen gate runs, seven mutations, five of them chosen by neither of the tickets whose
repairs are under test. `data/onethird-mg75f0-gate-class-closure.json` is its committed record —
**the file a reader opens to learn what the demonstration showed.**

A `--only`/`--gates` subset run wrote *that file*. Three defects compounded:

1. **The partial artifact sat at the canonical path with nothing saying it was partial.** Same
   schema, same `ALL_PASS: true`, over two rows instead of sixteen. mg-3946's audit hit this twice
   and restored the committed record with `git checkout --` both times.
2. **The headline ratio's halves were over different populations.** `caught` was counted over the
   rows the run exercised; `unseen` was every UNSEEN row in the table. So `--only M9` printed
   *"1/5 mutations … are caught by the widened gate"* — four rows in the denominator that the run
   never ran — and, once mg-3946 added its crash row, `1/6`.
3. **It exited 0 over both.** `demo.py --only M3 && echo passed` said the demonstration passed.

mg-3946 named the first two and offered the repairs as alternatives — *"either to refuse to write
the canonical path on a subset run, or to record the requested subset in the report and make the
headline quote its own denominator. Both are one-liners; neither is mine to choose."* The third it
recorded in the finding and did not carry into the repair sentence.

### 1.2 What was done, and why it is *and* rather than *or*

The two offered repairs answer **two different readers**, so taking either alone leaves the other
reader wrong:

* refusing the canonical path alone leaves a `.PARTIAL.json` that a *parser* cannot distinguish
  from a full report;
* marking the artifact alone leaves the canonical path overwritten, which is what actually cost
  this audit its two `git checkout --`s — nobody parses a file they believe is the full report.

Both were taken, plus the third defect:

**(1) A subset run never writes the canonical path.** It writes
`data/onethird-mg75f0-gate-class-closure.PARTIAL.json`. `data/*.PARTIAL.json` is gitignored, so a
partial report cannot become a committed record by a second route either. `885c1d1` in this
corpus — *"commit mg-5ad1's probe record from an UNPINNED run"* — is the same class of defect one
instrument over, and is the reason the gitignore line is there rather than left to care.

**(2) Every report says what it ran**, at whichever path it lands, near the top of the file:
`cases_requested`, `gates_requested`, `full_matrix`, `partial_run`, `IS_THE_DEMONSTRATION`. This is
copied from mg-3946's own falsifier, which carries `cases_requested`/`partial_run` with the comment
*"so it does not ship the defect it reports"* — the same pair, now in the instrument it was
reported against.

**(3) Both headline ratios are over one population.** Each denominator is the UNSEEN rows this run
exercised **in the column being quoted**, and both denominators are written into the report
(`unseen_mutations_run_widened`, `unseen_mutations_run_pre_widening`) so the printed sentence can be
checked against the artifact instead of trusted.

There are **two** denominators, not one, because `--gates` requests the columns independently:
`--gates widened` runs no left column at all, and *"fatal to nothing before it"* is a claim about
the left column. A column that was not requested is reported in words — *"the pre-widening column
was not run"* — rather than as `0/0`, which reads like a measurement and is not one.

The sharpest form of the old defect is the *second* ratio, not the first: `--only M9 --gates
widened` asked for no left column at all and still printed *"and 0/5 of them were fatal to nothing
before it"*, a sentence about five rows none of which that run touched.

On a full run both denominators are the whole UNSEEN set, so **the demonstration's own headline is
byte-for-byte what it always was: `5/5` and `5/5`.** The repair changes what a *subset* says and
changes nothing about what the demonstration says.

**(4) The exit code.** An unacknowledged subset run exits **2**. `--partial-ok` is the
acknowledgement: it restores the 0/1 answer to the narrower question a subset can actually
answer — *did every case that RAN hold its assertion?* — which is precisely the question
mg-3946's falsifier asks of this file, and the only legitimate caller of a subset run in the
corpus. That battery now passes `--partial-ok` on all six invocations. **Its six predictions are
unchanged and unrevised**; only the invocation moved, and a useful side effect is that reverting
this repair makes `--partial-ok` an unrecognised argument, so the battery's `control` case fails
loudly rather than the fix rotting out quietly.

### 1.3 Measured, not asserted

Canonical report digest before any of it:

```
39a4ca340ffeb74f2a9d78c60b4b147813b739633e8fc785f76e225ec6c97318
  data/onethird-mg75f0-gate-class-closure.json
```

| run | exit | wrote | canonical digest after |
|---|---|---|---|
| `--only M9 --gates widened` | **2** | `…-gate-class-closure.PARTIAL.json` | `39a4ca34…` unchanged |
| `--only M9 --gates widened --partial-ok` | **0** | `…-gate-class-closure.PARTIAL.json` | `39a4ca34…` unchanged |

`git status` after both: `data/` clean. The first run's closing lines, which are the three defects
inverted:

```
wrote data/onethird-mg75f0-gate-class-closure.PARTIAL.json
      PARTIAL -- the committed data/onethird-mg75f0-gate-class-closure.json
      was neither written nor read by this run.

PARTIAL RUN -- NOT THE DEMONSTRATION.  Every case that RAN held its assertion,
and that is the whole of what this says.  Of the UNSEEN rows this run exercised:
  1/1 were caught by the widened gate
  the pre-widening column was not run
...
Exiting 2: a subset run is not a passing demonstration, and `... && echo ok`
must not be able to say it was.
```

and the fields the same run wrote:

```
cases_requested                     ['none', 'M9']
gates_requested                     ['widened']
partial_run                         True
IS_THE_DEMONSTRATION                False
unseen_mutations                    ['M5', 'M6', 'M7', 'M8', 'M9']
unseen_mutations_run_widened        ['M9']
unseen_mutations_run_pre_widening   []
unseen_caught_by_the_widened_gate   ['M9']
```

Where the same invocation used to print `1/5` and overwrite the record, it now prints `1/1`, writes
elsewhere, says `partial_run: True`, and exits 2.

### 1.4 What this does NOT claim

* **Not claimed: that the demo's other artifacts are swept.** This is the mg-75f0 demo's report
  path only. mg-3946's falsifier still writes its own canonical
  `data/onethird-mg3946-closure-demo-falsifier.json` on a `--cases`/`--static-only` run — it
  *marks* the file `partial_run` (which is the half it shipped deliberately) but does not divert
  the path. Named here rather than fixed: it is a different instrument, and mg-3946's verdict
  routed its `cases_requested`/`partial_run` pair as the thing to copy, not that file's path
  handling. Other `--only`-bearing probes in `scripts/` were not audited.
* **Not claimed: that exit 2 is enforced anywhere.** CI runs the full matrix with no flags, so the
  new code path is exercised by no automated caller. The falsifier exercises `--partial-ok` and is
  hand-run — which is the standing residual mg-3946 stated about itself and this closeout does not
  improve.
* **Not claimed: that the committed report was refreshed.**
  `data/onethird-mg75f0-gate-class-closure.json` is still mg-75f0's own acceptance run from
  `9fa4aaa` and therefore carries neither mg-3946's `reported_a_failure` fields nor the
  `cases_requested`/`partial_run` pair added here. That is deliberate and it is the same reasoning
  as F5's: `885c1d1` in this corpus is a commit whose whole subject is *"commit mg-5ad1's probe
  record from an UNPINNED run"*, and replacing a committed acceptance record with a local
  developer-box run is that mistake in the other direction. The full-matrix run below was made to
  **verify** the code path, and its report was discarded rather than committed. CI uploads the
  regenerated report as a build artifact on every gate-touching merge, which is where a current
  one can be read.

**Noted, not fixed** (outside this closeout's remit, recorded so the next reader does not have to
re-find it): `docs/OneThird-mg75f0-GateClassClosure.md` §8 and the demo's own docstring both say
the acceptance test is **"18 gate runs"**. The matrix is 8 cases × 2 columns = **16**, and the
committed report has exactly 16 entries in `cases`. It is the same shape as F4 — a count that the
artifact beside it contradicts — but it is not one of the three F4 named, and mg-3946's verdict
scoped this item to those three.

---

## 2. OPEN 2 (F4) — the three counts, at every site this time

The finding's own shape is the point: **a count corrected in one place and left standing in the
others.** mg-3946 wrote that sentence about mg-3934 and then reproduced it — its F4 row says *"All
corrected at their sites"*, and two of the three were corrected at some of theirs.

### (a) "4 distinct revisions" — was stale, at two sites in one paragraph

`docs/OneThird-mg3934-CI-HistoryDepth.md` §3.3 said *"5 literals, **4 distinct revisions**, 3
scripts"* over a table naming three, said *"any of the **four** revisions"* four lines later, and
contradicted both with *"All **three** revisions"* two lines after that. Untouched by mg-3946,
which corrected the count in its own §3 and left mg-3934's sentence as it found it.

Re-derived from the scripts rather than from the table:

| revision | sites |
|---|---|
| `af7fc2df` | `onethird_mg75f0_gate_class_closure_demo.py:PRE_WIDENING_REV`, `onethird_mgbd53_widening_audit_probe.py:PRE_WIDENING_REV`, `onethird_mg4f9b_route_axis_probe.py:PRE_WIDENING_REV` |
| `91fa25f` | `onethird_mg4f9b_route_axis_probe.py:MG75F0_REV` |
| `9fa4aaa` | `onethird_mg4f9b_route_axis_probe.py`, `gate_source("9fa4aaa")` |

**5 literals, 3 distinct revisions, 3 scripts** — agreeing with mg-3946's independent count, and
now with mg-3934's own sentence. Both stale numbers corrected, with the correction annotated in
place rather than silently applied.

### (b) the window — stated measured, not rounded

The record is the table in `docs/OneThird-mg3934-CI-HistoryDepth.md` §2: twelve consecutive red
runs, first `2026-07-30T05:36:59Z`, last `2026-07-31T05:45:54Z`. The difference is **86 935 s =
24 h 08 m 55 s**.

| site | was | now |
|---|---|---|
| `docs/…-CI-HistoryDepth.md` §2 | "~24 hours" | 24 h 08 m 55 s + both endpoints |
| `docs/…-CI-HistoryDepth.md` §3.4 | "The 24 h" | "The 24 h 08 m 55 s" |
| `scripts/refinery_gate.sh` (READOUT header) | "24 h 09 m" | 24 h 08 m 55 s |
| `scripts/refinery_gate.sh` (the red branch a reader actually sees) | "for 24 h" | "for 24 h 08 m 55 s — twelve consecutive red runs" |
| `.github/workflows/gate-mutation-demo.yml` header | "24 h 09 m" | 24 h 08 m 55 s |

mg-3946 corrected the ticket's "21 hours" to "24 h 09 m" in the two *code* sites and left
"~24 hours" and "The 24 h" standing in the doc. "24 h 09 m" was the measured window rounded to the
minute; all five sites now carry the same measured figure, which is what makes the next reader's
grep agree with itself.

### (c) "eight consecutive runs" — verified already correct

`scripts/refinery_gate.sh` was corrected to twelve by mg-3946 in `0322264`, and a grep of the tree
for `eight consecutive` / `8 consecutive` outside the historical table (which quotes the ticket's
undercount deliberately, and is right to) returns nothing. **No stale site remained.** Recorded
because "verified, nothing to do" and "not checked" are different results and only one of them is
worth anything to the next reader.

---

## 3. What this closeout preserves, and why each is load-bearing

mg-3946's verdict marked these CONFIRMED. None is touched; all are stated here so a later reader
does not have to reconstruct why the F5 repair left them alone.

* **The mg-75f0 demo can fail, and the answer needed building.** Five drifts of the demo's own
  subject, each in an isolated tree; **6/6 exit codes predicted before running and held, none
  revised.** The invocations in that battery gained `--partial-ok`; **the predictions did not
  change**, and adding a flag to a command line is not revising a prediction about what the drifted
  subject does.
* **The direct case:** make M9's replacement byte-identical to its anchor and the widened gate
  exits 0 and the demo rejects the run. The row that had never executed in CI is a row that can
  turn red.
* **F1 was found AND repaired by the auditor: the demo scored a CRASH as a CATCH.** Its right
  column asserted `exit == 1` and nothing else — and a crashing gate exits 1 too. A bare `raise` in
  `_width` printed *"1/6 mutations are caught by the widened gate"* while nothing was caught.
  Aggravating and worth remembering: **`stderr_tail` was kept only for `returncode > 1`, discarding
  the traceback in exactly the case that needs it**, and the line distinguishing the two was
  already being printed and simply never asserted on. The `reported_a_failure` /
  `crashed_rather_than_failed` machinery is untouched here; the F5 repair changes the ratio's
  *denominator* and never its numerator's criterion.
* **Sweep for the still-broken class: NONE**, on an instrument sharing no code — 5 literals /
  3 revisions / 3 scripts, all ancestors of `origin/main`, exactly one CI-executed.
* **In CI at HEAD**, run `30612714474` is green on all four steps in 16m22s against the 75-minute
  bound, and `fetch-depth: 0` cost 2 s against 1 s — 0.2% of the job, constant per job.
* **Its NOT CLAIMED section stands as written**, in particular: *"my falsifier runs nowhere
  automatically — hand-run, 35 min for five cases, so today a control nobody runs, which the doc
  says rather than avoids."* That is still true, and it is still true of the `--partial-ok` path
  added here.

---

## 4. Reproduction

```bash
# the demonstration -- the whole matrix.  Prints 5/5 and 5/5, writes the
# canonical report.                                                      ~13 min
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py

# the F5 repair, both halves, in one invocation each                      ~2 min
shasum -a 256 data/onethird-mg75f0-gate-class-closure.json
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py \
    --only M9 --gates widened                 ; echo "EXIT=$?"   # 2
/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py \
    --only M9 --gates widened --partial-ok    ; echo "EXIT=$?"   # 0
shasum -a 256 data/onethird-mg75f0-gate-class-closure.json       # unchanged
git status --porcelain data/                                     # empty

# the F4 counts, re-derived rather than read off the corrected text
grep -n 'PRE_WIDENING_REV\|MG75F0_REV\|gate_source("' \
    scripts/onethird_mg75f0_gate_class_closure_demo.py \
    scripts/onethird_mgbd53_widening_audit_probe.py \
    scripts/onethird_mg4f9b_route_axis_probe.py
/usr/bin/python3 -c "from datetime import datetime as d; \
  print(d.fromisoformat('2026-07-31T05:45:54') - d.fromisoformat('2026-07-30T05:36:59'))"
```

Interpreter matters: bare `python3` on this host has no numpy.
