# mg-9a59 — a control that could not fail, and a fallback that said the false thing

Closes the two items mg-76d0's audit (`ced6861`) reported and deliberately did
not repair, and extends mg-a75e's standing control (`8d1e17a`) so that it can
reach either of them.

Pre-registration: `docs/OneThird-mg9a59-VacuousPass-Predictions.md`, committed
at `579e6de` before anything was run. 19 predictions; **18 held, 1 held with a
correction** (P3, below). Nothing in that file was amended.

**Ordering, because it is the deliverable and not a formality.** The control's
invocation set was extended and seen RED at `9675910` — a commit that contains
no change to the subject. The repair follows it. `git show 9675910` is the
red; the commit after it is the green.

---

## 1. The population, stated first

Every count below names the population it is over and the grain of the value.

| quantity | before | after | population / grain |
|---|---:|---:|---|
| control invocations | 7 | **11** | one call to the demo's `main()` per invocation, counted by the control's own ledger |
| control assertions | 45 | **70** | one boolean check each. 45 is **measured by subtraction**: 70 total minus the 25 contributed by the four new invocations, both counted by the same ledger |
| self-test drifts | 3 | **6** | one synthetic edit of the subject's source each; each must be CAUGHT |
| assertions failing against the **unrepaired** demo | — | **13 / 70** | the RED demonstration, `9675910` |
| assertions failing against the **repaired** demo | — | **0 / 70** | |
| gate runs in a full demo run | 16 | 16 | 8 cases × 2 columns. **Driver iterations, not gate executions** — see §6 |
| gate runs under `--gates ""` | 0 | 0 | the defect; the exit code and the artifact verdict changed, the count did not |
| gate runs under `--only M3` | 4 | 4 | 2 cases × 2 columns, both columns run |
| sites still **asserting** "21 hours" | 0 | 0 | flattening sweep over 30 occurrences in 8 tracked files |

Numbers taken from elsewhere and **not** re-derived here: mg-76d0's *"5
corrected / 7 asserting sites"*, its *"0.3 s instead of sixteen gate runs"*,
and its 35-minute battery cost. Numbers re-derived here: the vacuous exit 0
(P1), the 4 gate runs under `--only M3` (P5), and the zero-still-asserting
count (P19).

---

## 2. Item 1 — `ALL_PASS: true` over ZERO gate runs

**Measured, before repair** (`--gates "" --partial-ok`): exit **0**,
`cases: []`, `ALL_PASS: true`, report at the PARTIAL path, canonical record
untouched. Every part of that is true and the whole of it is vacuous. The
unacknowledged spelling `--gates ""` exited 2 — for an unrelated reason, the
partial-run rule — while still writing `ALL_PASS: true` over the same empty
list, so the artifact carried the vacuous verdict on **both** paths.

**Why zero is reachable, and only one way.** The matrix is
`len(wanted) × len(gates)`, and `wanted` is unconditionally seeded with
`"none"`, so no `--only` can empty it. Zero gate runs happens exactly when the
gate list is empty. The guard is nonetheless written over `results`, not over
`gates`, so a future edit that finds another route to an empty matrix hits the
same line. (P6 held.)

**The repair, and it is not one line.** The ticket relayed an estimate of a
one-line fix and said not to trust it without checking. Checked: **two lines,
in two different places, read by two different people.**

- the exit code — `if not results: return 2`, placed before every other verdict
  because over an empty matrix there is no verdict to give;
- the artifact — `"ALL_PASS": bool(results) and ok`, plus `n_gate_runs` and
  `gate_runs_per_column` written down beside it.

A one-line fix would have produced a red exit code and a **green artifact**,
and the artifact is what a reader opens six weeks later. That is why D4 and D5
drift the two halves separately: each must be independently seen to fire.

**`--partial-ok` deliberately does not rescue it.** The flag acknowledges *"I
know this is a SUBSET"* and restores the narrower question — *did every case
that RAN hold its assertion?* Over an empty matrix no case ran, so the narrower
question is empty too and there is nothing left for the flag to acknowledge.
Exit 2, the same code an unacknowledged subset gets, for the same reason:
`... && echo ok` must not be able to say this run demonstrated anything.

---

## 3. Item 2 — a fallback whose condition did not implement its stated intent

mg-a471's comment stated the intent:

> a column that was not requested at all gets said in words rather than quoted
> as `0/0`, which reads like a measurement and is not one

The condition asked a different question — *is the set of UNSEEN rows that ran
in this column empty?* — and the two come apart on `--only M3`. M3 is a **SEEN**
row, so both columns ran it (4 gate runs, 2 per column), both `unseen_run_*`
lists were empty, and the run printed **"the widened column was not run"** about
a column it had just run twice, and the same about the other.

**Decision: the comment is right and the condition is wrong — but the intent is
not implementable in two states, which is where the ticket's framing needs
correcting.** See §5.

The reason is about what the fallback protects, not about which text is older.
It guards a reader against reading an empty population as a measurement. There
are two ways to fail that reader:

1. quote `0/0` as though it were measured;
2. assert a column was not run when it was.

(2) is strictly worse. `0/0` is arithmetic a reader can interrogate; *"was not
run"* is a false claim about the run's own conduct, and a reader who believes it
goes looking for a column that is sitting in `cases`. The two-state condition
avoided (1) by committing (2) every time a subset happened to contain no UNSEEN
row.

So: **three states, not two.**

| state | sentence |
|---|---|
| column not in `gates` | *the widened column was not run* |
| column ran, holds no UNSEEN row | *the widened column ran 2 case(s), none of them UNSEEN rows — there is no ratio to quote* |
| column ran with UNSEEN rows | *1/1 were caught by the widened gate* |

The middle state is a fact about the **population**, not about the run. Naming
it satisfies the comment — still no `0/0` — without asserting anything false.

This is explicitly **not** making prose and predicate agree by reflex. The
alternative repair the ticket also offered — reword the comment to describe the
coded behaviour — would have frozen the false sentence in place and blessed it.
Property I keeps a *"not-run"* expectation in its own scenario set for the
mirror-image reason: a fix that merely deleted the sentence would satisfy an
assertion that only forbids it.

---

## 4. Item 3 (mg-a75e's new green control) — extended, seen RED, then green

All seven of the control's subject invocations were `--only M9 --gates widened`
variants or full-matrix equivalents. Its line-273 property asserting *"the
pre-widening column was not run"* **appears** was green for the one invocation
where that sentence is true, while the same sentence was false on `--only M3`;
and no invocation passed an empty `--gates`.

Two properties and four invocations were added **before the demo was touched**:

- **H** — a run that performed zero gate runs does not get to say pass: exit 2
  on both spellings, `ALL_PASS: false`, `n_gate_runs: 0` on the artifact, and
  the words *ZERO GATE RUNS* in the output.
- **I** — a column that ran is never described as not having run, over two
  invocations covering all three states, plus a standing prohibition on `0/0`.

**The RED** (`9675910`, full log at
`data/onethird-mg9a59-control-RED-before-repair.txt`):

```
  population examined: 11 invocations of the demo's main(), 70 individual assertions
  13 of 70 assertions FAILED:
    - H: zero-gate-run run (empty --gates, acknowledged) exited 0, expected 2 ...
    - H: ... reported ALL_PASS True over an EMPTY cases list ...
    - I: --only M3 (both columns run, no UNSEEN row) printed "the widened column
         was not run" about a column it RAN (2 gate runs in it) ...
```

**After the repair**: `all nine properties (A-I) hold: 70/70 assertions over 11
invocations`, and **six** self-test drifts CAUGHT — D1–D3 unchanged and still
firing (P11 held), plus D4 (guard removed → H fires), D5 (`ALL_PASS` back over
an empty population → H fires), D6 (column sentence back to two states → I
fires).

The control now **prints the population it ranged over** next to its verdict,
because a control that reports only a verdict is the same shape as the defect
it was written against.

---

## 5. Corrections to the ticket's framing

**(a) "Fix the condition to the comment" is under-specified, and a literal
reading produces a second false artifact.** The comment describes only the
fallback's *trigger* (a column that was not requested). A condition that tests
exactly that and nothing else sends `--only M3` down the ratio branch, printing
`0/0` — the thing the same comment forbids. Honouring the comment requires a
state the comment never names. Two states cannot do it.

**(b) The one-line estimate was low in a way that matters** — see §2. Not a
quibble about size: the missing line is the one that fixes the *artifact*, and
the artifact outlives the exit code.

**(c) "n_cases 4" is right, and the noun is not.** mg-76d0's audit reads
`n_cases = len(report["cases"])`, and `cases` in the demo's report is a list of
**gate runs**, not of cases: `--only M3` gives `cases_requested: ["none","M3"]`
(length 2) and `cases` of length 4. Same number, different grain. The demo's
report now writes the count as **`n_gate_runs`**, with
`gate_runs_per_column: {"pre-widening": 2, "widened": 2}`, because "cases"
already means something else in that file. The audit's `n_cases` and the demo's
`n_gate_runs` are the same quantity.

**(d) A third instance of item 1, in the instrument that found item 1.**
`onethird_mg76d0_partial_report_audit.py --only "," --partial-ok` selected no
checks — the comprehension drops empty ids and the unknown-id guard has nothing
to reject — and exited **0** with `ALL_PREDICTIONS_HELD: true` over `checks: []`.
The same shape as X5, in the audit that pre-registered X5. Fixed the same way
(`n_checks_run` on the artifact, verdict conjoined with a non-empty population,
exit 2 before any other verdict) and demonstrated by hand: `--only ","` now
exits 2 with `ALL_PREDICTIONS_HELD: false`, while `--only X4` still exits 0 over
a population of 1, so the guard does not over-fire.

**(e) P3 held with a correction to my own wording.** I predicted the vacuous
run's report *"lands at the PARTIAL path, not the canonical one"*. Both files
exist after the run; the canonical one is the fixture's untouched sentinel,
verified byte-identical by digest. The prediction is right about what it meant
and loose about what it said.

**(f) mg-76d0's X5 prediction is NOT amended, and now misses on purpose.**
`predict: 0` was correct about the subject at `9072f34` and stays exactly as
pre-registered. A re-run of that battery against main will report X5 in
`predictions_missed` and exit 1. **That disagreement is the repair landing, not
a regression** — annotated in the script at the check itself so a future reader
meets the explanation where they meet the mismatch.

**(g) Item 3 of the original ticket confirmed, not re-fixed.** A sweep that
flattens comment continuations finds **30** occurrences of the phrase across 8
tracked files; every one is a quotation of the superseded figure inside a
correction, a table of corrections, or an audit narrative. **0 assert it as the
window.** The sweep was demonstrated able to find a wrapped instance before its
clean result was trusted: on a synthetic `for 21\n# hours`, the flattening sweep
returns FOUND where `grep "21 hours"` returns MISSED. The technique is kept; the
ticket's own amendment already withdrew the causal story that motivated it.

---

## 6. What I did NOT do

- **I did not run the real matrix.** No mg-2c34 gate was executed by this work.
  Every demo number here is measured through the control's fake `run_case`, so
  `n_gate_runs: 16` is a count of **driver iterations**, not of gate
  executions. The driver is the entire subject of both defects, which is what
  makes the substitution sound; it is stated rather than glossed because a
  reader could otherwise take 16 for sixteen gate runs. (P18 held as written.)
- **I did not run mg-76d0's 35-minute battery** against the repaired demo. Its
  X5 mismatch above is predicted from the demo's measured exit code, not
  observed through the battery.
- **I did not add a standing control for (d)**, the audit instrument's own
  vacuity. That audit is not wired into CI; its guard was demonstrated red and
  green by hand over 2 invocations and nothing will notice if it regresses.
  **This is a real gap and it is the same gap this ticket exists to close, one
  level up.**
- **I did not establish whether the `--partial-ok` family shares the shape.**
  `onethird_mg3946_closure_demo_falsifier.py` computes
  `ALL_PASS = not missed and not problems` — the same empty conjunction — and
  `--static-only --cases ,` exits 0, but its static PARTS 3/4 run regardless of
  `--cases`, so that run was **not** over an empty population and proves
  nothing either way. Establishing it needs a run with gate runs in it, which I
  did not do. Unresolved, not clean.
- **I did not touch the two `.yml` sites** from the original item 3, or any
  prediction in any `predictions:` commit.
