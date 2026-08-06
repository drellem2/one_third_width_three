# mg-a266 — pre-registered predictions

**Committed before any audit code exists.** Nothing below is amended later; where
a prediction misses, the miss is recorded in the report
(`docs/OneThird-mga266-VacuityAndSplitPhrase-IndependentAudit.md`) and this file
is left exactly as written.

**This audit was PRE-FILED in the same action as its parent** — mg-a266 was
created by pm-onethird at 2026-08-05 19:22:21Z alongside mg-9a59, before mg-9a59
had produced a line of code. So the audit's existence is not evidence that
anything went wrong; it was always going to be run.

**Subject.** The parent mg-9a59 is DONE and landed at `c64fe68` (with the RED
control at `a99c970` and its own predictions at `1ef4c79`). This audit does not
re-do it. Two instructions, both of the form *show the instrument CAN fail*:

1. prove `ALL_PASS` cannot be **true** over an empty population;
2. prove the re-check **can find** a phrase split across a comment continuation.

Read so far, before predicting: the three changed scripts and the parent's doc.
Nothing has been executed.

---

## Group A — the vacuous pass (instruction 1)

| # | prediction |
|---|---|
| **A1** | `ALL_PASS` and `n_gate_runs` are computed from the **same** list `results` (`bool(results) and ok` vs `len(results)`), so a report carrying `n_gate_runs: 0` **and** `ALL_PASS: true` is unconstructible by any argv. I predict my enumeration over the argv space produces **zero** such reports. |
| **A2** | The only route to an empty matrix is an empty `--gates`: `wanted` is unconditionally seeded with `"none"`, so no `--only` can empty it. I predict I re-derive this by enumeration and find no second route. This restates the parent's P6; **it is the parent's claim and I am re-deriving it, not repeating it.** |
| **A3** | `--only` naming a row that does not exist (e.g. `--only MZZZ`, or `--only ","` whose comprehension yields empty strings) raises `KeyError` on `EXPECTED[(mutation, gate)]` — the run **crashes**, exit 1, with a traceback and **no report written at all**. Non-zero, so not a vacuous pass; but it is a crash, not a reported emptiness. |
| **A4** | `--gates "bogus"` dies inside `build_tree` with `SystemExit("unknown gate variant")`, exit 1, **no artifact**. |
| **A5** | **In the artifact, `ALL_PASS: false` does not distinguish "measured nothing" from "measured and failed."** Both write `false`. The only discriminator is a *second* field (`n_gate_runs`, or `len(cases)`), and there is no field naming *why* the verdict is false. I predict I will report this as a **residual**: a distinction the output makes only to a reader who thinks to consult a second field. |
| **A6** | At the shell the two **are** distinguishable: empty → exit **2**, real failure → exit **1**, and stdout carries the literal words `ZERO GATE RUNS`. I predict both hold on a real unstubbed run. |
| **A7** | **Positive control on my own instrument.** My enumeration, run against the **pre-repair** demo source (`c64fe68^`), goes RED: at least one argv produces exit 0 with `ALL_PASS: true` over `n_gate_runs: 0`. If it does not go RED, my clean result against `main` is worth nothing and I will say so. |
| **A8** | The empty case performs **zero** gate runs, so it costs ~0 s. I predict a real, unstubbed, end-to-end run of the subject is affordable for the empty case and I will do it that way rather than through a stub. |
| **A9** | The extended invocation set still cannot reach: the two **crash** routes (A3, A4). I predict no property of `onethird_mga471_partial_run_control.py` asserts anything about an argv that makes the demo raise, so "unknown row / unknown gate" is uncovered. I will name whatever else I find rather than reporting full coverage. |
| **A10** | The subject writes the report **before** the zero-population guard returns 2, so the empty run leaves a `.PARTIAL.json` on disk carrying `ALL_PASS: false`, `cases: []`, `n_gate_runs: 0`. The committed canonical report is untouched (byte-identical digest). |

## Group B — the split-phrase re-check (instruction 2)

| # | prediction |
|---|---|
| **B1** | **The continuation-flattening sweep is not committed anywhere.** It appears only as prose in the parent's doc §5(g). I predict `30 occurrences / 8 tracked files / 0 asserting` **cannot be re-derived from anything in the repository**, and that the "demonstrated able to find a wrapped instance" claim has no re-runnable instrument behind it. An orphaned number. |
| **B2** | I build a sweep, plant `for 21\n# hours`, and it is **FOUND**, where `grep -rn "21 hours"` returns MISSED. Positive control passes. |
| **B3** | Third and fourth shapes, deliberately different from the parent's: a **string concatenation** (`"... for 21" "hours ..."`) and a **backslash line continuation**. I predict a flattener that only strips comment markers **misses the string-concatenation shape**, and that catching it requires stripping quotes as well. |
| **B4** | **What join-lines breaks: false positives.** Flattening adjacent lines makes the phrase match across an unrelated boundary — a line ending in `21` followed by a line starting with `hours`. I predict at least **one** such false positive exists over the tracked tree once flattening is aggressive enough to catch B3, and that this is the cost the parent's doc does not state. |
| **B5** | My re-derived occurrence count will **not** be exactly `30 / 8`: different tool, different file set, no committed definition of "tracked files" to match. I predict I report my own number with its population and grain, and mark the parent's 30 as **not re-derived** rather than confirmed. |
| **B6** | The substantive claim — **0 sites still assert "21 hours" as the window** — holds. Every occurrence is a quotation inside a correction, a corrections table, or an audit narrative. |
| **B7** | `.github/workflows/gate-mutation-demo.yml` and `.github/workflows/script-controls.yml` were fixed by `8d1e17a` (mg-a75e), **not** re-fixed by the parent. I predict I confirm this from the patch, and that the parent's §5(g) statement of it is accurate. |

## Group C — standing targets, including on myself

| # | prediction |
|---|---|
| **C1** | **My own instruments must not carry the defect they audit.** Both new scripts will refuse a verdict over an empty population and will say so in their own output, and each will be **self-tested** by drifting that guard out and confirming the drift is caught. If I ship a checker that can pass over zero checks, that is my finding against myself and I will print it. |
| **C2** | Every count I print names its population and grain. |
| **C3** | I predict I find **at least one** thing in the parent worth correcting beyond B1/B5. I do not know what it is yet; naming a number here would be a guess dressed as a prediction. |
| **C4** | I will **not** run the real mg-2c34 gate matrix (~13 min × the variants I need). Every demo number I report other than the empty case is through a stubbed `run_case`; the empty case is real because it costs nothing. I predict I state this in the report as a limit, not gloss it. |
