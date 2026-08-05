# mg-9a59 — pre-registration

Written **before** extending the control, before touching the demo, and before
running anything. Every number below is a prediction about a run that has not
happened yet. A refuted prediction is a result and stays in this file with the
refutation recorded next to it; nothing here is amended after the fact.

Subject: `scripts/onethird_mg75f0_gate_class_closure_demo.py` (the demo) and
`scripts/onethird_mga471_partial_run_control.py` (mg-a75e's standing control,
green as of `8d1e17a`).

Provenance of the two defects: mg-76d0's audit (`ced6861`), items 1 and 2 of
mg-9a59. Both are **reported, not re-derived** at the time of writing — the
predictions below are my re-derivation and P1/P5 are the check on mg-76d0's
report.

---

## A. The subject as committed, before any repair

| # | prediction | grain |
|---|---|---|
| P1 | `--gates "" --partial-ok` exits **0** having run **0** gate runs | exit code, count of `report["cases"]` |
| P2 | that run's report has `ALL_PASS: true` and `cases` of length 0 | JSON field, list length |
| P3 | that run's report lands at the **PARTIAL** path, not the canonical one | which of two paths exists |
| P4 | `--gates ""` **without** `--partial-ok` exits 2 — i.e. the defect is reachable only through the acknowledgement flag | exit code |
| P5 | `--only M3` (a SEEN row) runs **4** gate runs across **both** columns and prints "the widened column was not run" **and** "the pre-widening column was not run" | count of `report["cases"]`, two substrings of stdout |
| P6 | the number of distinct argument shapes that can drive the demo to zero gate runs is exactly **1** — an empty `--gates`. `--only` cannot, because `wanted` is unconditionally seeded with `"none"` | enumeration over the two subsetting flags |

## B. The control before its invocation set is extended

| # | prediction | grain |
|---|---|---|
| P7 | the control at `8d1e17a` passes (exit 0) against the **unrepaired** demo — it is green over a subject carrying both defects | exit code |
| P8 | none of its 7 subject invocations passes an empty `--gates`; none passes `--only M3` | count over the invocation set |

## C. The extended control, still against the unrepaired demo (the RED demonstration)

| # | prediction | grain |
|---|---|---|
| P9 | with two new properties added (H: zero-population; I: column sentence), the control exits **1** against the unrepaired demo | exit code |
| P10 | it names **≥ 3** distinct problems: vacuous exit 0, `ALL_PASS` true over 0 cases, and a false "column was not run" sentence | count of entries in `problems` |
| P11 | the three existing self-test drifts D1–D3 still fire — extending the invocation set does not break the anchor-count assertions | 3 of 3 CAUGHT |

## D. After the repair

| # | prediction | grain |
|---|---|---|
| P12 | `--gates "" --partial-ok` exits **2**, not 0 and not 1 | exit code |
| P13 | its report records `ALL_PASS: false` and `n_gate_runs: 0` | JSON fields |
| P14 | `--only M3` prints neither "was not run" sentence, and still prints no `x/0` ratio | substring absence |
| P15 | a **full** run is unaffected: exit 0, canonical path, `n_gate_runs: 16`, headline `5/5` | exit code, path, count, substring |
| P16 | the extended control exits **0** against the repaired demo, with **9** properties over **≥ 11** invocations | exit code, counts |
| P17 | two new drifts D4 (drop the zero-population guard) and D5 (collapse the column sentence back to two states) are both CAUGHT — 5 of 5 self-tests | count |

## E. What I predict I will NOT be able to do

| # | prediction |
|---|---|
| P18 | I will not run the real 16-gate-run matrix. `n_gate_runs: 16` for P15 is measured through the control's fake `run_case`, which is a count of driver iterations, **not** 16 executions of the mg-2c34 gate. The distinction is stated rather than glossed. |
| P19 | Item 3 of the ticket (two sites saying "21 hours") is already landed by `8d1e17a`; I will confirm and not re-fix. I predict a continuation-flattening sweep finds **0** sites still asserting 21 hours as the figure. |
