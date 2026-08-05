# mg-76d0 — PRE-REGISTRATION

Independent audit of the mg-a471 partial-report repair (`9072f34`). This file is written and
committed **before any of the runs below is executed**. Nothing in it is revised afterwards: a
refuted prediction is a result and is kept as written, with the observed value recorded beside it in
the audit document.

## 0. What was already observed before this commit (NOT predictions)

Recorded here so the two are not confused. These came from reading the diff and sweeping the tree,
before any experiment ran:

* the full matrix is `8 cases × 2 gate columns = 16` gate runs (7 mutations + `none`), and the
  committed report `data/onethird-mg75f0-gate-class-closure.json` has exactly 16 entries in `cases`;
* the committed report carries **none** of the five fields mg-a471 adds
  (`cases_requested`, `gates_requested`, `full_matrix`, `partial_run`, `IS_THE_DEMONSTRATION`)
  — it is still mg-75f0's acceptance run from `9fa4aaa`, which mg-a471 states and defends;
* a line-wrap-aware sweep for the window figure finds **two sites still asserting "21 hours"** —
  `.github/workflows/gate-mutation-demo.yml` (the `mg-3934 CI history-depth control` step comment)
  and `.github/workflows/script-controls.yml` (the static-half step comment). Both split the phrase
  across a comment continuation (`for 21\n# hours`), which is why a plain `grep -n "21 hours"`
  returns neither.

## 1. Pre-registered exit codes

Every invocation is `/usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py <args>`,
run from the repository root.

| # | args | predicted exit | why |
|---|---|---|---|
| X1 | `--only M9 --gates widened` | **2** | unacknowledged subset |
| X2 | `--only M9 --gates widened --partial-ok` | **0** | acknowledged subset, its one row holds |
| X3 | `--only M3` | **2** | subset on the case axis only, both columns |
| X4 | `--gates ""` | **2** | empty column list is a subset; **zero** gate runs |
| X5 | `--gates "" --partial-ok` | **0** | *predicted hole:* acknowledged empty run passes vacuously — `cases: []`, `ALL_PASS: true`, exit 0, having exercised nothing |
| X6 | `--only NOPE --partial-ok` | **1** | `EXPECTED[(m, g)]` KeyErrors before any validation; traceback, no report written |
| X7 | *(no arguments — the full matrix)* | **0** | the demonstration |
| X8 | `scripts/onethird_mg3946_closure_demo_falsifier.py` | **0**, with **6/6** PART-1 predictions held | mg-a471 preserved the battery, moving only the invocation |

## 2. Pre-registered artifact behaviour

* **A1** — X1, X2, X3, X5 write `data/onethird-mg75f0-gate-class-closure.PARTIAL.json` and
  **only** that; the canonical report stays byte-identical at
  `39a4ca340ffeb74f2a9d78c60b4b147813b739633e8fc785f76e225ec6c97318`.
* **A2** — `git status --porcelain data/` is clean of the canonical path after X1–X6.
* **A3** — *the floor.* X7 (a **full** run, exit 0, no warning) **overwrites the committed
  acceptance record in place**. New digest ≠ `39a4ca34…`, `git status data/` shows the canonical
  path modified, and nothing in the run says a committed artifact was just replaced. The repair
  defends the canonical path against a **subset** run and against nothing else.
* **A4** — X7's regenerated report has **16** entries in `cases`, contradicting the *"eighteen full
  runs of the CI gate"* in the demo's own run-line.
* **A5** — X1 prints `1/1 … caught by the widened gate` and, for the column it did not run, the
  words *"the pre-widening column was not run"* rather than a `0/…` ratio.
* **A6** — the PARTIAL path is a single fixed name with no per-invocation identity, so X2's report
  silently replaces X1's; a reader who finds it cannot tell which subset run produced it except by
  reading `cases_requested`.
* **A7** — `git check-ignore -v data/onethird-mg75f0-gate-class-closure.PARTIAL.json` reports the
  `data/*.PARTIAL.json` rule, and `git status --porcelain` never shows the PARTIAL file.

## 3. Pre-registered counting-claim arithmetic

Reported as **corrected-count against site-count**, the form the ticket asks for. The site count is
taken over sites that **assert** the figure, not over sites that quote a superseded one as history.

* **C-b (the window).** Predicted **5 corrected / 7 asserting sites** — the two `.yml` comments
  above are still `21 hours`, and one of them is in a file mg-a471 edited. This **refutes**
  `refinery_gate.sh`'s *"that is now the figure at all FIVE sites"* and the closeout's *"at every
  site"*.
* **C-a (the revisions).** Predicted **fully corrected**; no site still asserts four.
* **C-c (twelve consecutive).** Predicted **fully correct already**; the one `8 consecutive` left is
  an explicit quotation of the ticket's undercount.
* **C-d (eighteen gate runs).** Predicted **0 corrected / 6 asserting sites**, against a note in
  `docs/OneThird-mg3946-VerdictCloseout.md` that names **2**. Predicted further that the closeout's
  own §1 opening asserts *"eighteen gate runs"* 144 lines above its own note that the number is 16.

## 4. This audit's own instrument

`scripts/onethird_mg76d0_partial_report_audit.py`. Per the standing rule that an instrument must not
ship the defect it reports, it records `checks_requested`, `full_battery`, `partial_audit` and
`IS_THE_AUDIT` in its report, writes to a `.PARTIAL.json` sibling when run over a subset, and exits
non-zero on an unacknowledged subset — the same three properties it is auditing in its subject.
