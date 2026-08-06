# mg-a266 — INDEPENDENT AUDIT of the mg-a471 remainder: can a PASS be true over nothing, and can the re-check see a split phrase?

**This audit was PRE-FILED in the same action as its parent.** pm-onethird
created mg-a266 at 2026-08-05 19:22:21Z alongside mg-9a59, before mg-9a59 had
produced a line of code. Its existence is not evidence that anything went
wrong; it was always going to be run.

**Pre-registration:** `docs/OneThird-mga266-VacuityAndSplitPhrase-Predictions.md`,
committed at `765b6d9` **before any audit code existed**. 21 predictions;
**17 held, 4 missed**. Nothing in that file is amended — the four misses are
scored below (§7) and two of them are findings in their own right.

**Subject:** mg-9a59 at `c64fe68`, with its RED control at `a99c970`. mg-9a59
is DONE and this audit does not re-do it.

**Merge state, checked rather than assumed.** `c64fe68` is **not** on `main` —
neither by ancestry (`git merge-base --is-ancestor` exits non-zero) nor by
`git patch-id --stable` against main's recent history, and `git log main` finds
no commit touching its doc. It sits on this branch, 19 commits ahead of main
along with the rest of tonight's chain. Every re-derivation below is therefore
against the branch state, which is the state that will land.

**Instruments, both new, both committed and re-runnable:**

| file | what it establishes | cost |
|---|---|---|
| `scripts/onethird_mga266_vacuity_enumeration.py` | instruction 1 | ~2 min, 0 gate executions |
| `scripts/onethird_mga266_split_phrase_control.py` | instruction 2 | ~5 s |

---

## 1. The populations, stated first

Every count in this document names the population it is over and the grain of
the value. Numbers that are somebody else's are labelled as theirs.

| quantity | value | population / grain | whose |
|---|---:|---|---|
| argv spellings enumerated | **128** | 8 `--only` × 8 `--gates` × 2 `--partial-ok`; grain = one call to the demo's `main()` | mine |
| assertions over those | **564** | grain = one boolean | mine |
| spellings reaching an **empty** population | **48** | of the 128 | mine |
| … of those, exiting non-zero with `ALL_PASS: false` | **48 / 48** | | mine |
| spellings that **crash** | **32** | of the 128 | mine |
| violations against the **pre-repair** subject | **144** | same 128 spellings, 448 assertions | mine |
| the standing control's subject invocations | **11** | re-derived by recording every `drive()` argv | mg-9a59's, **re-derived and confirmed** |
| distinct argv spellings the control drives | **9** | of my 128 | mine |
| planted split-phrase shapes | **8** | 7 positive, 1 negative; × 4 instruments | mine |
| positive shapes invisible to `grep` | **6 / 7** | | mine |
| `"21 hours"` occurrences at `c64fe68^` | **30** | mg-3946's snippet over 416 files matching `\.(md\|sh\|py\|yml\|txt)$`; grain = one regex match | mg-9a59's, **re-derived and confirmed exactly** |
| files holding them | **9** | same population | mine — **the parent says 8** |
| occurrences asserting the figure | **0** | hand adjudication of all 6 the proxy flagged | mg-9a59's, **re-derived and confirmed** |
| **mg-2c34 gate executions by this audit** | **0** | — | mine |

**`n_gate_runs: 16` anywhere below counts DRIVER ITERATIONS, not gate
executions.** `run_case` is stubbed throughout. The substitution is sound
because both defects under audit live in `main()`, *above* `run_case`, and
every quantity asserted on is computed by `main()` from the shape `run_case`
returns. It is stated rather than glossed because a reader could otherwise take
16 for sixteen gate runs — which is the correction mg-9a59 itself had to make
one level down.

---

## 2. Instruction 1 — ALL_PASS **cannot** be true over an empty population

Not "it wasn't on one run." Two independent arguments, and then the instrument
that could have shown the opposite.

### 2a. Structurally: the two fields cannot disagree

```python
"n_gate_runs": len(results),
"ALL_PASS":    bool(results) and ok,
```

Both are computed from the **same list**. `bool(results)` is false exactly when
`len(results)` is 0. A report carrying `n_gate_runs: 0` **and** `ALL_PASS: true`
is not merely absent from the runs anyone tried — it is **unconstructible**, for
every argv, forever, unless that line is edited.

### 2b. Enumeratively: 128 spellings, 0 escapes

The argv space is a **cross product**, not a hand-picked list, because the exact
defect in the parent's own control was seven invocations that all happened to be
`--only M9 --gates widened` variants. Spellings include the malformed ones: an
empty value, a lone separator, a doubled separator, and names that are not
members.

- **48 of 128** reached an empty population. **Every one**: exit **2**,
  `ALL_PASS: false`, `n_gate_runs: 0`, and the literal words `ZERO GATE RUNS` in
  its output.
- **30 of 128** exited 0. The **minimum** `n_gate_runs` among them is **1** — no
  zero-population run exits 0.
- 564 assertions, **0 failures**.

**Only one route to zero exists**, and this re-derives the parent's P6 rather
than repeating it: `wanted` is unconditionally seeded with `"none"`, so no
`--only` can empty the matrix; only an empty `--gates` can. The guard is
nonetheless written over `results`, so a future edit finding another route hits
the same line.

### 2c. The positive control — without which 2a and 2b are worth nothing

A negative needs an instrument that could have shown the positive. The same
enumeration was run against **three broken subjects**, each of which **must**
fire:

| broken subject | violations / assertions | fired |
|---|---:|---|
| **PC1** the demo's own pre-repair source at `c64fe68^` | **144 / 448** | V1, V2, V3 |
| **PC2** the zero-population guard removed | **96 / 544** | V2, V3 |
| **PC3** `ALL_PASS` put back to `ok` | **48 / 544** | V1 |

PC1's first violation, quoted from the run:

```
V1: `--gates ` wrote ALL_PASS True over n_gate_runs 0 -- a verdict over an empty population
```

The instrument sees the defect when the defect is there. Its clean result over
the repaired subject therefore means something.

### 2d. The real, unstubbed run

The empty case costs nothing to run for real — **for exactly the reason under
audit**: zero gate runs. So one measurement is of the actual program, not a
fixture:

```
scripts/onethird_mg75f0_gate_class_closure_demo.py --gates '' --partial-ok
  exit                         2
  said_zero_gate_runs          True
  artifact_ALL_PASS            False
  artifact_n_gate_runs         0
  artifact_len_cases           0
  canonical_report_unchanged   True
```

---

## 3. **How a reader tells emptiness from success** — the part that is the instruction

"If it reports emptiness, say HOW a reader tells the two apart. A distinction
only visible by reading the source is not a distinction the output makes."

Three runs, and every cell below is quoted from the run's own output:

| what a reader sees | MEASURED-NOTHING | MEASURED-AND-FAILED | MEASURED-AND-PASSED | separates empty from…? |
|---|---|---|---|---|
| **exit code** | `2` | `1` | `0` | **both** |
| artifact `ALL_PASS` | `false` | `false` | `true` | passed only — **not failed** |
| artifact `n_gate_runs` | `0` | `16` | `16` | **both** |
| artifact `len(cases)` | `0` | `16` | `16` | **both** |
| stdout banner | `ZERO GATE RUNS -- THIS RUN MEASURED NOTHING` | `DEMONSTRATION FAILED` | `Demonstration complete.` | **both** |

**Answer.** A reader tells them apart three ways, none of which requires reading
the source: the **exit code** (2 / 1 / 0, three states for three states), the
**`n_gate_runs` field** sitting next to the verdict on the artifact, and a
**banner that names the emptiness in words**. The distinction is one the output
makes.

### RESIDUAL R1 — `ALL_PASS` alone is two-valued over three states

`ALL_PASS: false` is written by an empty run **and** by a failing run. A reader
who greps only that field sees a failure where there was an emptiness, and there
is no field saying *why* the verdict is false.

This is graded a **residual, not a defect**, and the reason is the direction of
the confusion: an empty run is never mistaken for a **passing** one, which is the
defect mg-9a59 was sent to close, and that defect is closed. The remaining
ambiguity costs a reader a wrong diagnosis, not a false green. Naming it anyway,
because the honest answer to "how does a reader tell them apart" has to include
**which field will not help them**.

### FINDING F1 — 32 of 128 spellings crash with an uncaught `KeyError`

| spelling family | count | observed, unstubbed |
|---|---:|---|
| `--gates bogus` | 16 | exit **1**, `KeyError: ('none', 'bogus')`, **no report written** |
| `--only ,` | 8 | exit **1**, `KeyError: ('', 'widened')`, **no report written** |
| `--only MZZZ` | 8 | exit **1**, `KeyError: ('MZZZ', …)`, **no report written** |

Exit codes here are **observed from real subprocesses**, not inferred: in-process
a raise is not an exit code, and what a shell sees is the question that matters
for `… && echo ok`.

**This is not a vacuous pass** — non-zero, and no artifact is left behind for a
later reader to misread. It is reported because it is the rest of the answer to
"enumerate the ways in": a malformed invocation produces a raw traceback rather
than a message, exits **1** (the same code as a genuine `DEMONSTRATION FAILED`),
and in the `--only ,` case does not even name the offending input —
`KeyError: ('', 'widened')` is not a sentence a user can act on.

### FINDING F2 — the demo's own unknown-gate guard is dead code

`build_tree` carries `raise SystemExit(f"unknown gate variant {gate_variant!r}")`
for exactly the `--gates bogus` case. It is **unreachable from the CLI**:
`EXPECTED[(mutation, gate_variant)]` is evaluated first in the loop and raises
`KeyError` before any tree is built. Low severity — the run still fails loudly —
but it is a guard that cannot fire, which is the same species as a control that
cannot fail. My prediction A4 asserted this guard *was* what fires; it is not.

### FINDING F3 — what the standing control's invocation set still cannot reach

The parent's doc says the control was extended from 7 to 11 invocations. **That
11 is re-derived here and confirmed** — not read off the source, but recorded by
wrapping the control's own `drive()` and counting: 77 calls total = 11 subject
invocations + 6 self-test drifts × 11.

Those 11 use **9 distinct argv spellings**, of my 128. Named rather than
reported as full coverage — the parent's own doc says there will be something:

- `--gates ,` and `--gates ,,` — **alternate spellings of the empty gate list.**
  The control tests `--gates ""` only. The guard is written over `results`, so
  these are covered *in fact*; they are not covered *by the control*.
- `--gates bogus`, `--only MZZZ`, `--only ,` — **the entire crash family (F1).**
  No property of the control asserts anything about an argv that makes the demo
  raise.
- `--gates pre-widening` alone, and `--only none` — a run of a single column, and
  a run of only the unmutated case.

A control is allowed to be narrower than an audit. This is the answer to the
question, not an accusation.

---

## 4. Instruction 2 — the re-check **can** find a phrase split across a comment

A checker that silently fails to match a split phrase reports clean because it
**cannot see**, not because there is nothing there. That is not hypothetical:
two `.yml` sites survived three rounds of "corrected at every site" precisely
because each wrapped the phrase across a comment continuation.

Eight planted shapes × four instruments. **`grep` is instrument 0 because it is
the one that was actually in use when those two sites survived.**

| shape | grep | sweep A (comment-flattening) | sweep B (aggressive) | sweep C (mg-3946's own) |
|---|---|---|---|---|
| S0 unsplit, one line | FOUND | FOUND | FOUND | FOUND |
| **S1 `for 21` / `# hours` — the parent's own shape** | **MISSED** | **FOUND** | **FOUND** | **FOUND** |
| S2 python comment continuation | MISSED | FOUND | FOUND | FOUND |
| S3 **string concatenation** | MISSED | **MISSED** | FOUND | **MISSED** |
| S4 **backslash continuation** | MISSED | **MISSED** | FOUND | **MISSED** |
| S5 markdown soft wrap | MISSED | FOUND | FOUND | FOUND |
| S6 comment **across a blank line** | MISSED | FOUND | FOUND | FOUND |
| S7 *(negative)* `MAX_RETRIES = 21` / `# hours are not…` | MISSED | FOUND | FOUND | FOUND |

**PROVEN.** S1 — the exact shape the parent's doc claims — is **FOUND** by the
flattening sweep and **MISSED** by grep, on a deliberately constructed case.
**6 of the 7 positive shapes are invisible to grep.** The technique does what
it is claimed to do, so a clean result from it is worth something. The positive
control is committed and re-runnable, which the parent's was not.

### FINDING F4 — the sweep *is* committed, and my prediction B1 was wrong

I predicted the sweep existed nowhere in the repository. **It does exist**:
`docs/OneThird-mg3946-VerdictCloseout.md` publishes it as a runnable shell +
python block, authored by **mg-3946**, not by mg-9a59. Correcting myself before
anything else in this section, because I nearly filed a finding that was mine.

What remains true, and is the finding worth keeping: it is a **snippet inside
prose**, wired to no CI job and to no control. Nothing re-runs it and nothing
notices if it stops working — and a reader chasing `30 / 8 / 0` has to first
know to look inside a *different* ticket's closeout doc. That snippet is now
transcribed verbatim as **instrument C** so the parent's numbers can be
re-derived with the parent's own tool.

### FINDING F5 — the **30 is confirmed exactly**; the **8 is not**

Holding both the instrument (mg-3946's snippet, verbatim) and the population
(the tree at the parent's own commit) fixed:

| tree | occurrences | files |
|---|---:|---:|
| `c64fe68^` — **what the sweep would have seen**, before its own doc landed | **30** ✔ | **9** ✘ |
| `c64fe68` — after its own doc, which quotes the phrase twice | 32 | 10 |
| `HEAD` — this branch, **as tracked at run time** | 34 | 11 |

The `HEAD` row's population is `git ls-files` **at the moment of the run**, so
it excludes this document, which was not yet committed. That is deliberate and
not an oversight: re-running after committing would raise the number, and
re-recording it here would raise it again. A report that counts itself is the
`c64fe68` row's trap in a loop. The figure that answers the parent's claim is
the first row, and it is stable.

**The 30 reproduces to the digit**, independently, with the parent's own
instrument. That is a real confirmation and it is worth more than the
correction beside it.

**The 8 does not.** The same measurement yields **9** files, and **every file in
that set holds at least one match** — so no exclusion of any single file
recovers 8. The parent's file count is off by one; its occurrence count is
exact.

The third row is the trap worth naming: measuring at `c64fe68` rather than
`c64fe68^` counts the report **inside the population it reports on** — the
mg-ec63 shape, a probe reading a file its own run wrote. Two of those extra
occurrences are the parent's doc quoting the phrase in order to report on it.

### FINDING F6 — what joining lines breaks, and the honest size of it

The parent's paragraph states the technique's **recall** and not its **price**.
The price:

- Over the real tracked tree (612 tracked UTF-8 files, grain = one match): grep
  **28**, sweep A **34**, sweep B **34**. The 6 extra are matches grep cannot
  see. **2** of those span a line break, and — measured, not assumed — **both
  are genuine**. Aggressive flattening (B) buys **0** further matches here.
- **The false positive is real but had to be planted.** S7 —
  `MAX_RETRIES = 21` followed by `# hours are not what this constant counts` —
  is FOUND by every flattening instrument. Nothing in the technique can tell S1
  from S7; only a reader can.

**This corrects the brief's expectation as well as the parent's.** The ticket
said "if the fix is *join lines before matching*, find what that breaks." Over
this tree, at this phrase, it breaks **nothing**: 0 false positives among 34
matches. The failure mode is demonstrable only synthetically. Reporting a
breakage I could not find would have been the mirror of the defect I was sent
to look for.

### FINDING F7 — "0 asserting" holds, but by judgement, and the judgement is now checkable

"Occurrence" is mechanical; "asserts the figure as the window" is a judgement,
and a script pretending to settle it would be the mg-8af0 shape — a row scoring
a string literal. So:

- A stated **proxy** (a ±60-char window containing any of 34 correction markers
  is a quotation) flags **6 of 34** as asserting.
- All **6 were read by hand**. None asserts the figure: four are quotations
  inside corrections or a corrections table, one is narration about how long a
  job *looked* broken, and one is **the phrase inside the sweep snippet's own
  regex literal** — not a claim about a window at all.
- **Hand count: 0. The parent's claim is 0. It holds.**

The adjudication is a **committed table**, not prose, and an occurrence the proxy
flags that is *not* in it **fails the run** — so a new site that nobody has read
cannot be absorbed into a future "0 asserting."

### F8 — item 3 provenance, confirmed

`c64fe68` touches **zero** `.yml` files. The two sites were landed by `8d1e17a`
(mg-a75e) and were **not** re-fixed by the parent, exactly as its §5(g) says.

---

## 5. Did the deliverable reproduce, in its own new code, the defect it was sent to repair?

Asked of the parent, and of me.

**Of the parent: no.** The repair is two lines in two places, both present, both
independently drifted and both seen to fire (PC2, PC3 above).

**Of me: yes, once, and I caught it before committing.** My first draft of
`--prove-empty-guard` — the flag that proves my own vacuity guard fires — wrote
its stub artifact **to the canonical report path**. That is mg-a471's F5
exactly: a run that measured nothing, landing where the record lives. Both
scripts now write `data/*.PROVE-GUARD.json`, and `.gitignore` refuses to commit
it, for the same reason `.PARTIAL.json` is refused.

**And my own guards are not merely claimed.** Both instruments conjoin their
verdict with a non-empty population, and both were **seen to fire**:

```
--prove-empty-guard: THIS FILE'S OWN POPULATION EMPTIED DELIBERATELY
  assertions  : 0
  ZERO ASSERTIONS EVALUATED -- THIS RUN MEASURED NOTHING.
  ALL_HELD is written FALSE, not true-over-an-empty-list.  Exiting 2.
```

Without that flag the guard would have been **unreachable** — a guard nobody
has seen fire, in the instrument sent to look for guards nobody has seen fire.

---

## 6. Corrections to the parent's framing and to mine

**(a) The parent's `8 tracked files` is 9.** §5(g) and the §1 table. The
occurrence count beside it is exact.

**(b) The parent's §5(g) demonstration left nothing behind.** *"The sweep was
demonstrated able to find a wrapped instance before its clean result was
trusted"* is **true** — and was, until this commit, unre-runnable. It now has a
committed positive control.

**(c) The parent's §1 row *"gate runs under `--gates ""`: 0 — the exit code and
the artifact verdict changed, the count did not"* is right and slightly
undersold.** The count did not merely stay 0; it did not previously exist. The
pre-repair report has no `n_gate_runs` field at all, which is why PC1 has to
fall back to `len(cases)` to measure the old subject on the same axis.

**(d) Mine: prediction B1 was wrong** — the sweep is committed (F4).

**(e) Mine: prediction B5 was wrong in the direction that matters.** I predicted
my re-derivation would *not* land on 30. It lands on exactly 30. I had assumed a
different instrument over a different file set would disagree; holding both fixed
to the parent's own choices, it agrees. **Changing two variables and reporting
the disagreement would have been a fabricated finding.**

**(f) Mine: prediction B4 was wrong.** I predicted at least one false positive
over the real tree. There are none (F6).

**(g) Mine: prediction A4 named the wrong exception**, and the correct one is
F2 — a guard that cannot be reached.

**(h) The ticket's own framing, corrected.** Its item 2 said to *"find what
[join-lines] breaks."* Over this population it breaks nothing measurable, and
the cost is demonstrable only on a planted case. Stated rather than manufactured.

---

## 7. Prediction scorecard — 17 held, 4 missed

| held | missed |
|---|---|
| A1 A2 A3 A5 A6 A7 A8 A9 A10 | **A4** — wrong exception; the real one is F2 |
| B2 B3 B6 B7 | **B1** — the sweep *is* committed (F4) |
| C1 C2 C3 C4 | **B4** — no false positive exists over the real tree (F6) |
| | **B5** — my count *does* reproduce the parent's 30 (F5) |

Three of the four misses are misses **in the parent's favour**. Recorded that
way on purpose: an audit whose every surprise runs against its subject is
reporting its own prior, not its measurements.

---

## 8. What I did **not** do

- **I did not execute the mg-2c34 gate. Not once.** Every `n_gate_runs` above
  other than the empty case's `0` counts driver iterations through a stubbed
  `run_case`. A full matrix is ~13 minutes × the variants; the substitution is
  sound because both defects live above `run_case`, but it is a substitution.
- **I did not re-derive the parent's `13 / 70` RED figure.** I established the
  stronger property for the vacuity half — the pre-repair subject fires 144
  violations over my own 128 spellings (PC1) — but the specific 13-of-70 over
  the control's own 11 invocations is **the parent's number, not re-derived
  here.**
- **I did not audit item 2, the three-state column sentence, on its own terms.**
  My dispatch weighted instructions 1 and 2; the fallback appears here only
  where the 128-spelling enumeration crosses it.
- **I did not wire either new script into CI.** Both are re-runnable by hand and
  nothing will notice if they regress. **This is a real gap and it is the same
  gap the parent named against itself** for the mg-76d0 instrument — one level
  up, and now unclosed in two places.
- **I did not resolve whether mg-3946's snippet's own pattern (`21 hours?`,
  which also matches the singular) changes its counts.** I held the phrase fixed
  at `"21 hours"` so the comparison stayed about the flattening. The parent's
  30 may or may not survive the singular; unresolved, not clean.
- **I did not touch any `predictions:` commit**, mine or anyone's.
- **I did not verify the parent against `main`,** because it is not on `main` —
  checked by `git patch-id --stable` and by path, not by ancestry alone (see the
  preamble).
