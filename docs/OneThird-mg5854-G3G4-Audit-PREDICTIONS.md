# mg-5854 — INDEPENDENT AUDIT of the mg-1d03 G3+G4 repair: PREDICTIONS

**Pre-registration.** Written and committed **before any script in this audit was run** and before
any mutant was built. Nothing below is revised after the fact; a refuted prediction is a RESULT and
stays as written, with the outcome recorded beside it in the report.

Everything here was formed by READING the tree at `13f1e6a` (the parent mg-1d03 commit, already
merged) — reading is not measuring, and the whole point of my brief is that the two disagree.

## What I am predicting about

Seventeen predictions in five groups:

* **Q1–Q3** — exit codes of the controls as they stand.
* **Q4–Q8** — the row census: how many rows are PRESENT vs how many the parent's audit CHECKS, and
  whether the figures survive being re-obtained from an enumerator that shares no line with the
  helper the parent calls.
* **Q9–Q10** — two mutations aimed at the parent's own row-audit, to find what it cannot see.
* **Q11** — the five remediation instruments, constructed at a site the parent did not use.
* **Q12–Q17** — do-not-disturb, the parent's own summary count, and my own tooling.

---

## Q1–Q3 — exit codes at HEAD

| # | run | predicted exit |
|---|---|---|
| **Q1** | `scripts/onethird_mg1d03_table_row_audit.py` | **0** |
| **Q2** | `scripts/onethird_mg1d03_remediation_instruments.py` | **0** |
| **Q3a** | `scripts/onethird_mg8a71_live_claim_control.py` | **0** |
| **Q3b** | `scripts/onethird_mgcd04_declared_strike_control.py` | **0** |
| **Q3c** | `scripts/onethird_mg0242_population_census.py` | **0** |
| **Q3d** | `scripts/onethird_mg0242_struck_vs_refuted.py` | **0** |
| **Q3e** | `scripts/onethird_mg0242_identity_recheck.py` | **0** |
| **Q3f** | `scripts/onethird_mg9a19_exemption_population_audit.py` | **0** |
| **Q3g** | `scripts/onethird_mg9d7b_exemption_channel_census.py` | **0** |
| **Q3h** | `scripts/onethird_mgfccb_direction_check.py` | **0** |
| **Q3i** | `scripts/onethird_mg8a71_audit_instrument.py` | **0** |

## Q4–Q8 — the row census, by CALLING

* **Q4.** Data rows PRESENT in §6.1 of `docs/OneThird-mg8a71-VerdictRepairs-Closeout.md` = **3**;
  data rows the parent's part (A) CHECKS = **3**. Coverage **3/3**.
  *Population: the `|`-delimited non-header, non-separator rows of §6.1. Grain: one table row.*
* **Q5.** Data rows PRESENT in the `posets_with_identity_extension` docstring table = **4**
  (`n = 3`, `4`, `5`, `tot`); rows the parent's part (B) CHECKS = **4**. Coverage **4/4**.
  *Population: the data rows of that one docstring table. Grain: one table row.*
* **Q6.** An enumerator written for this audit and sharing no line with
  `onethird_mgfccb_direction_check.py` returns, at `n = 3,4,5`: identity-extension family
  **7 / 40 / 357**, total **404**; all-labelled family **19 / 219 / 4231**, total **4 469**, equal to
  A001035 as a literal from OEIS. Both AGREE with the helper the parent calls.
  *Population: posets on the labelled ground sets [3],[4],[5]. Grain: one poset.*
* **Q7.** The same independent enumerator returns **6 385** / **31 625** for the identity-extension
  family and **43 842** / **218 166** for the all-labelled family. AGREE.
  *Population: (poset, reference-order) pairs and (poset, reference-order, element) triples over the
  same ground sets. Grain: one pair / one triple.*
* **Q8.** The live-claim control classifies **539** lines of
  `docs/OneThird-L1b-Spread-Locality.md`, and **539 = `len(text.splitlines())`** for that file — the
  swept count is the whole file by an independent measure, not only by its own bucket sum.
  *Population: one document. Grain: one line.*

## Q9–Q10 — two mutations aimed at the parent's row audit

Both are constructed against `scripts/onethird_mg1d03_table_row_audit.py` part (A), which matches
the integers of a §6.1 row as an unordered MULTISET over the WHOLE row and selects rows by the
presence of an `onethird_*.py` name.

* **Q9.** **Column-swap mutant.** Rewrite §6.1 row 1 so every figure sits in the *population NAMED*
  column and the *population SWEPT* column carries no integer at all — multiset over the row
  unchanged. Predicted: the parent's audit exits **0** (**MISSED**). A table whose entire purpose is
  to report NAMED vs SWEPT would then be checked by a rule that cannot tell the two columns apart.
* **Q10.** **Fourth-row mutant.** Append a fourth data row to §6.1 that names no script and carries a
  figure contradicted by the count. Predicted: the parent's audit exits **0** (**MISSED**), because
  `section_61_rows` only collects rows matching `` `onethird_\w+\.py` ``.

## Q11 — the five instruments, constructed at a site OUTSIDE the parent's subject

The parent measured 7 mutants × 2 controls on ledger **C3**, which lives in
`docs/OneThird-L1b-Spread-Locality.md` — the one document the live-claim control reads. **4 of the
ledger's 10 entries do not live there** (C6 in `OneThird-Bbias-Locality-Lemma.md`; C8, C9, C10 in
`OneThird-mgd112-DroppedVerdict-Closeout.md`). I remediate ledger **C9** — *"over every poset and
every reference order"*, in `mgd112` — by each of the five instruments in turn and run **three**
controls, each as CI runs it (no path argument), adding the struck-vs-refuted ledger as a third
because its part (A) reads all three ledger files and its part (B) sweeps all of `docs/`.

Predicted exit codes, `(live-claim, declared-strike, ledger)`:

| mutant | instrument | predicted |
|---|---|---|
| J1 strike-at-site | strike-at-site | (0, 0, 0) |
| J2 rewrite-in-place | rewrite-in-place | (0, 0, 0) |
| J3 rewrite + annotation | rewrite + annotation | (0, 0, 0) |
| J4 deletion, UNDECLARED | (the forbidden form) | (0, 0, 0) |
| J5a deletion, declared, short quote, no markup | DELETION declared as a strike | (0, **1**, 0) |
| J5b deletion, declared, verbatim quote, no markup | DELETION declared as a strike | (0, **1**, **1**) |
| J6 claim RESTORED LIVE (positive control) | none | (**0**, 0, **1**) |

The load-bearing prediction is the **J6 zero in the live-claim column**: at a site outside its
one-document population the live-claim control does not bite even on a claim asserted in plain body
text, so it distinguishes **0 of the 5** instruments there. The ledger control is predicted to
supply the missing reach for J6 — but only because C9 is *already in the ledger*; part (B), which is
the only corpus-wide sweep for a claim nobody has ledgered, is predicted to PRINT a hit and NOT
change the exit code.

## Q12–Q14 — do not disturb

* **Q12.** Both deletions that cut a true clause still leave the true half **verbatim in the same
  section** at HEAD: *"(element, reference-order) cases"* in §2.3 of `Spread-Locality`, and
  *"× **every** reference order"* in the `mgd112` §2.2 table row. **2/2 confirmed.**
* **Q13.** F4's decline to re-widen: the three proven-safe sites in
  `docs/OneThird-Bbias-Locality-Lemma.md` (§0, the §12 row, the §12 narrative) are **byte-identical
  to `bb1cb9b`** — mg-1d03 did not touch that file. **3/3 unchanged.**
* **Q14.** `Var(pos_σ z) = m(m+2)/12` is asserted by
  `scripts/onethird_mg0242_identity_recheck.py` (a CI-wired control) — **confirmed**. AND that same
  script's report **still prints that no control asserts it**, so its own output understates its own
  reach. Predicted: the phrase survives at HEAD (**≥1 occurrence**).

## Q15–Q17 — the parent's summary count, and my own tooling

* **Q15.** The parent states *"of the five instruments, the controls in CI distinguish exactly ONE
  boundary"*. Measured from its own matrix, the five instruments fall into **3** exit-code classes —
  `{strike-at-site, rewrite-in-place, rewrite + annotation}`, `{DELETION declared as a strike}`,
  `{none}` — i.e. **2** boundaries, not 1. Predicted: the "ONE" is a count over the four *removal*
  instruments stated as a count over five, which is a POPULATION mismatch of the same family as G3.
  **Predicted: MIS-STATED.**
* **Q16.** *Check your own tooling for the defect you are repairing.* This lineage is eight for
  eight. Predicted: my own instrument contains **at least one** named-vs-counted or label/grain
  defect found while building it, and it is recorded rather than quietly fixed. **Predicted: YES.**
* **Q17.** `scripts/onethird_mg5854_row_and_instrument_audit.py` at HEAD → exit **0**; the same
  script against each of the Q9/Q10 mutants → exit **1**.

---

*Predictions frozen. Outcomes are recorded in `docs/OneThird-mg5854-G3G4-IndependentAudit.md` §0,
including every miss.*
