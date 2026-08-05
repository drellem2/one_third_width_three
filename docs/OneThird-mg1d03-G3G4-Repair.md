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
| P1 | The **other two rows** of closeout §6.1 — the rows this repair is *not* fixing — are **correct** when the figure is obtained by calling the helper rather than reading the table. **0 gaps among the 6 figures.** | population: the 6 numerals in rows 1–2 of §6.1 of `docs/OneThird-mg8a71-VerdictRepairs-Closeout.md`; grain: one integer per (generator × {posets, pairs, triples}) | |
| P2 | The **other four rows** of the `posets_with_identity_extension` docstring table are **correct** when counted. **0 gaps among the 6 per-`n` figures.** | population: the per-`n` rows `3/4/5` of the docstring table in `scripts/onethird_mgfccb_direction_check.py`; grain: one integer per (n × {this family, A001035}) | |
| P3 | With both G3 numbers corrected and the census `BASELINE` **left untouched**, the census **exits 1** with two `BASELINE GAP CLOSED` lines — the re-baseline gate firing, not a regression. | population: one process exit code | |
| P4 | With both entries then removed from `BASELINE`, the census **exits 0** and both comparisons pass as ordinary `OK` checks. | population: one process exit code | |
| P5 | The ledger in `onethird_mg0242_struck_vs_refuted.py` prints *"the repair used three, and named only one"* immediately above a tally that lists **five** distinct instrument keys — a named-vs-counted error **inside the line that reports the count**, the same class as G3. | population: part (A)'s `BY INSTRUMENT` block; grain: distinct instrument keys | |
| P6 | The live-claim control's PASS readout contains **0** occurrences of the word *instrument* — i.e. a green run says nothing about which of the five remediations it can see. | population: the `main()` report block of `scripts/onethird_mg8a71_live_claim_control.py`; grain: word occurrences | |
| P7 | **Deletion-without-declaration is invisible to every control in CI.** A mutant that deletes a refuted claim outright — no `~~`, no annotation, no *"is struck"* — leaves the live-claim control at exit **0** *and* the declared-strike control at exit **0**. | population: 2 process exit codes over the mutated corpus | |
| P8 | **Deletion-declared-as-a-strike is visible to exactly one control.** The same deletion, with the *"is struck with it"* declaration restored and no markup, leaves the live-claim control at exit **0** and trips the declared-strike control (≥1 unbaselined hit). | population: 2 process exit codes over the mutated corpus | |
| P9 | **Rewrite-in-place and rewrite+annotation are indistinguishable from strike-at-site to both controls.** Both mutants exit **0** on both controls. | population: 4 process exit codes over the mutated corpus | |
| P10 | After all repairs, all five controls in `script-controls.yml` that touch this arc exit **0**: census, struck-vs-refuted, live-claim, declared-strike, direction check. | population: 5 process exit codes at HEAD | |
| P11 | Sweeping `docs/`, `scripts/` and `.github/` for the literal `6.9x`/`6.9×` in a **poset-grain** claim finds **more than the one baselined site** — the "corrected at every site" claim will again be one or more sites short. | population: all `*.md`, `*.py`, `*.yml` under `docs/`, `scripts/`, `.github/`; grain: one site = one line asserting the ratio of a poset count | |
| P12 | The five instruments partition the ledger exactly: 4 + 2 + 2 + 1 + 1 = **10 = REFUTED**, with no ledger entry carrying a sixth instrument. | population: the 10 ledger entries of part (A); grain: one instrument key per entry | |

---

*(Sections 1 onward are written after the measurements; this file is committed at §0 first.)*
