# mg-5854 — INDEPENDENT AUDIT of the mg-1d03 G3+G4 repair

**Subject.** `13f1e6a` *"close mg-0242 G3+G4 …"* and its pre-registration `b3bcad9`, both on
`origin/main`. **Verified by content, not by ancestry**: `git patch-id --stable` gives
`f94c754cce546c6521cdc034d242fb8d6f52c7bc` for the repair and
`04e4c8da1452a373a546d55d578b622b2cddb5cb` for the predictions commit, and both match at
`origin/main`. Neither was rebased, so the recorded SHAs happen to resolve — that is luck, not
method, and the local `main` ref in this worktree is stale by four commits, which is exactly the
false negative the lineage warns about.

**Instrument built for this audit:** `scripts/onethird_mg5854_row_and_instrument_audit.py`, wired
into `script-controls.yml`. Everything numeric below is its output.

**Verdict: the repair STANDS.** Both G3 figures are right; every neighbouring row equals what the
helper returns; the five instruments are correctly enumerated and the standard is correctly argued.
**Three findings, none of which reverses it:** one mis-stated figure the repair *introduced* in the
same table it repaired (**A1**, baselined), one count stated over the wrong population in the
sentence that reports the G4 result (**A2**), and — the substantive one — **the control's coverage
does not match the set of claims that exists** (**A3**): outside the one document the live-claim
control reads, *leaving a refuted claim entirely un-remediated is indistinguishable from striking
it*, measured.

---

## 0. Predictions, and what happened

Seventeen predictions, committed in `a20aaf0` before any script was run
(`docs/OneThird-mg5854-G3G4-Audit-PREDICTIONS.md`). **One refuted, and it is the finding.**

| # | prediction | outcome |
|---|---|---|
| Q1 | `onethird_mg1d03_table_row_audit.py` → 0 | ✅ **0** |
| Q2 | `onethird_mg1d03_remediation_instruments.py` → 0 | ✅ **0** |
| Q3a–i | the other nine controls → 0 each | ✅ **0** ×9 (11 of 11 green) |
| Q4 | §6.1: 3 rows present, 3 checked | ✅ **3 / 3** |
| Q5 | docstring table: 4 rows present, 4 checked | ✅ **4 / 4** |
| Q6 | independent enumerator agrees with the helper and with A001035 on the poset counts | ✅ 7/40/357 = **404**; 19/219/4231 = **4 469** |
| Q7 | …and on pairs and triples | ✅ **6 385 / 31 625**, **43 842 / 218 166** |
| Q8 | the swept line count 539 equals `len(text.splitlines())` | ❌ **REFUTED — the file has 538 lines.** Finding **A1** |
| Q9 | column-swap mutant → the parent's row audit exits 0 (MISSED) | ✅ **exit 0, MISSED** |
| Q10 | unnamed-fourth-row mutant → the parent's row audit exits 0 (MISSED) | ✅ **exit 0, MISSED** |
| Q11 | 7 mutants × 3 controls at a ledgered site outside the parent's subject | ✅ **21 of 21 exit codes as predicted** |
| Q12 | both part-true deletions still leave the true half verbatim | ✅ **2/2** |
| Q13 | F4's three proven-safe sites not re-widened | ✅ **3/3** |
| Q14 | `Var(pos_σ z) = m(m+2)/12` asserted by a CI control, *and* that control still says nobody asserts it | ✅ both — asserted, and the stale sentence survives ×1 |
| Q15 | *"of the five instruments … exactly ONE boundary"* is a count over four | ✅ **MIS-STATED.** Finding **A2** |
| Q16 | my own tooling carries a defect of the class I am auditing | ✅ **two of them** (§6) |
| Q17 | my instrument → 0 at HEAD, and catches both mutants | ⚠️ **0, but only with A1 baselined**; both mutants **CAUGHT** |

**The miss is Q8 and it is the point.** I predicted the repaired figure would survive an independent
line count. It did not. Reading the row could never have shown that; only counting the file could —
which is the instruction the parent was given and the one it discharged against the control's own
`split("\n")` rather than against the document.

Q17 is scored **⚠️ rather than ✅** deliberately: the exit code is 0 as predicted, but the prediction
assumed nothing would need baselining to get there, and something did.

---

## 1. What I ran, and the population each number is over

**11 controls at HEAD, 11 exit 0.** *Population: the eleven scripts `script-controls.yml` invokes
that touch this arc. Grain: one process exit code per script.* Nothing in the merged repair is
failing.

---

## 2. Primary: every row of the named-vs-swept tables, BY CALLING

**Rows present, rows checked — two numbers, not one.**

| table | rows PRESENT | rows CHECKED | integer-cells checked |
|---|---|---|---|
| §6.1 of `OneThird-mg8a71-VerdictRepairs-Closeout.md` | **3** | **3** | **14** |
| the table in `posets_with_identity_extension`'s docstring | **4** | **4** | **8** |

*Population: the data rows of those two tables — every `|` line that is neither the header nor the
separator rule. Grain of "rows": one table row. Grain of "integer-cells": **one integer occurrence
per (row × column)** — not one per distinct quantity.* That grain distinction is why my count is 22
where the parent's is 12: the parent reports *"0 gaps in 6 + 6 figures"*, counting each **quantity
once**, while a figure appears **twice per row** (once NAMED, once SWEPT) and row 3 contributes two
more. Both counts are correct at their own grain and neither is the other's; stating which is which
is the entire subject of G3.

**Every figure was obtained by CALLING, and by calling three times.** Not one number in my part (A)
is a literal read from anywhere except the A001035 leg, which is a literal on purpose.

| quantity | this audit's enumerator | the helper the parent calls | OEIS A001035 |
|---|---|---|---|
| identity-extension family, **posets** | **404** | 404 | — |
| identity-extension family, **pairs** | **6 385** | 6 385 | — |
| identity-extension family, **triples** | **31 625** | 31 625 | — |
| all-labelled family, **posets** | **4 469** | 4 469 | **4 469** |
| all-labelled family, **pairs** | **43 842** | 43 842 | — |
| all-labelled family, **triples** | **218 166** | 218 166 | — |
| labelled posets on [3] / [4] / [5] | **19 / 219 / 4 231** | 19 / 219 / 4 231 | **19 / 219 / 4 231** |

*Population: the labelled ground sets [3], [4], [5]. Grain: one poset; one (poset, reference-order)
pair; one (poset, reference-order, element) triple — each named separately, because G3's second half
was one grain's figure written on another's row.*

**Why a third leg was needed at all.** The parent's audit compares the table against the helper. If
the *helper* were wrong, the table and the audit would agree and both be wrong — the audit cannot
fail in that direction by construction. My enumerator brute-forces all `2^(n(n−1))` relations on
`[n]` and tests irreflexivity, antisymmetry and transitivity directly; it neither builds the
identity-extension family nor closes it under `S_n`, which is what both helpers do. Linear
extensions are counted by a second routine, over permutations. **It agrees on all six figures**, so
the helper is sound and the parent's method was safe — but that is now measured rather than assumed.

**Are the corrected figures derived at report time?** Yes, for the two tables and for the ratio: the
parent's audit re-obtains them on every push and its part (C) recomputes the ratio rather than
reading it. **`11.06×` is computed as `4 469/404 = 11.0619` and required to carry the word "posets"
before it is accepted** — that mechanism works and I re-ran it.

---

## 3. Finding A1 — the repaired row is still wrong, by one, at the grain it names

> §6.1 row 3, *population SWEPT* column: **"539/539 lines"**.
> `onethird_mg8a71_live_claim_control.py`'s own report: **"population: 539 lines, ALL classified"**.
> `docs/OneThird-L1b-Spread-Locality.md` has **538 lines.**

`wc -l` = **538**. `len(text.splitlines())` = **538**. **539** is `len(text.split("\n"))` — the
number of fragments, whose last element is the empty string after the file's trailing newline. It is
not a line, and it is bucketed as `blank`.

**Severity, stated exactly.** *Coverage is not affected.* 539 fragments is a **superset** of 538
lines, so nothing goes unswept and the control's internal `sum(coverage) == len(lines)` assertion is
sound. What is wrong is the **grain of the label**, by exactly one unit — in the SWEPT column of the
table whose stated purpose is to report named-vs-swept, one row below where G3 was found, in the
repair for G3.

**This is G3's exact shape, not a near miss.** G3's second half was *"a real number from an adjacent
GRAIN"*. So is this. The provenance is even documented — mg-069f's audit §5 derives *"`wc -l` = 538
⇒ 538 newlines ⇒ 539 `split("\n")` elements"* — but **neither of the two sites that report it as a
population names the grain**, and mg-1d03's own new rule, written for ratios, is that *an assertion
must name its grain and be right at it*. Applied to the population counts in the same table, that
rule fails at row 3.

**Not repaired here, deliberately.** It is carried as the single `BASELINE` entry of my instrument,
in the convention mg-8a71 set and mg-0242 kept: **a baselined gap that closes fails the run**, so
whoever fixes it must re-baseline rather than pass silently. An auditor who repairs its own subject
destroys the record of what was wrong, and mg-1d03 is merged. **Routed to pm-onethird.** The fix is
two words at two sites (`539 lines` → `539 split("\n") fragments over 538 lines`, or recount at the
line grain and write `538`), plus removing the baseline entry.

---

## 4. Second: a claim remediated by each of the five instruments — which does the control catch?

The parent measured 7 mutants × 2 controls on **ledger C3**, in
`docs/OneThird-L1b-Spread-Locality.md` — **the one document the live-claim control reads**. **4 of
the ledger's 10 entries do not live there** (C6 in `Bbias-Locality-Lemma.md`; C8, C9, C10 in
`mgd112-DroppedVerdict-Closeout.md`). So the matrix answers the question on the only subject where
the answer can be non-zero.

I constructed the same seven remediations of one claim at **two sites in `mgd112`**, and ran
**three** controls over each — adding the struck-vs-refuted ledger, which the parent's matrix omits
and whose part (B) sweeps all of `docs/`. Each control is invoked exactly as `script-controls.yml`
invokes it, from the mutant tree's root, with no path argument.

*Population: 2 subjects × 7 mutants × 3 controls = **42 process exit codes**. Grain: one exit code
per (subject × mutant × control).*

### 4.1 A claim the ledger does **not** know, in a document the live-claim control does not read

The subject is the live-claim control's **own S3 signature sentence**. Using its own signature is
the point: a zero here is not *"the control was never asked"*, it is *"the control was asked, in
another document, and could not answer"*.

| mutant | instrument | live-claim | declared-strike | ledger |
|---|---|---|---|---|
| J1 strike-at-site | strike-at-site | 0 | 0 | 0 |
| J2 rewrite-in-place | rewrite-in-place | 0 | 0 | 0 |
| J3 rewrite + annotation | rewrite + annotation | 0 | 0 | 0 |
| J4 deletion, UNDECLARED | (the forbidden form) | 0 | 0 | 0 |
| J5a deletion, declared, short quote | DELETION declared as a strike | 0 | **1** | 0 |
| J5b deletion, declared, verbatim quote | DELETION declared as a strike | 0 | **1** | 0 |
| **J6 none — the claim LEFT LIVE** | **none** | **0** | **0** | **0** |

**Two exit-code classes over seven mutants.** `J6` — a refuted claim asserted in plain body text,
un-remediated by anything — is **byte-for-byte indistinguishable in CI from striking it at the
site**. Every control passes.

**And the ledger control SEES it.** Its corpus sweep counts **22** live hits with the mutant present
against **21** at HEAD, and names `OneThird-mgd112-DroppedVerdict-Closeout.md` in its listing — then
**exits 0**. *Population: **248** documents in `docs/`, 23 691 live text units, 5 signatures. Grain:
one (document, signature, line) hit.* **That population is the MUTANT TREE's, copied before this
report existed** — re-run at HEAD it reads **249 documents, 23 767 live text units, 21 hits**, and
this document adds none. Stated rather than left to drift: a figure whose population is one commit
older than the reader's is how the last three findings in this lineage started. There is no baseline
on the hit count, so a 22nd hit is
indistinguishable from the 21 adjudicated ones. **A corpus-wide sweep that reports and does not
assert is the "sees but does not fail" channel** — the same shape mg-9d7b closed for exemptions,
one level up.

### 4.2 The same seven remediations of a claim the ledger **does** know (C10)

| mutant | live-claim | declared-strike | ledger |
|---|---|---|---|
| J1 strike-at-site | 0 | 0 | 0 |
| J2 rewrite-in-place | 0 | 0 | 0 |
| J3 rewrite + annotation | 0 | 0 | 0 |
| J4 deletion, UNDECLARED | 0 | 0 | 0 |
| J5a deletion, declared, short quote | 0 | **1** | 0 |
| J5b deletion, declared, verbatim quote | 0 | **1** | **1** |
| **J6 none — the claim LEFT LIVE** | **0** | 0 | **1** |

**Four classes.** All 21 exit codes as predicted (Q11).

**Subject substitution, declared.** My prediction named ledger **C9**; I ran **C10**. C9's site is a
sentence wrapped across two lines *inside* an existing POPULATION CORRECTION block, so constructing
seven clean variants there means rewriting the block rather than the sentence. C10 is the same
document, the same ledger, and a single-line site. The substitution was made before the mutants were
built, and the predicted exit codes are unchanged by it.

### 4.3 Finding A3 — what determines detectability is not the instrument

Compare the two tables: **2 classes** against **4**, same seven remediations, same three controls,
same document. The difference is **not** how the claim was remediated. It is whether the claim is

* **(a)** inside the one document the live-claim control reads, or
* **(b)** written into the ledger's `LEDGER` list **by hand**.

**Neither is a property of a remediation instrument.** So *"which of the five can a control see"* is
answered by the **population**, not by the instrument — and the parent's reach statement, which is
otherwise accurate and does say *"in this one document"*, presents the answer as a property of the
instruments.

**Answering the ticket's question directly: the control catches one instrument (`none`), in one
document, plus one boundary (`DELETION` declared but not made) corpus-wide.** For the 4 of 10
ledgered claims outside that document, `none` is caught only because a human listed the claim; for
any refuted claim nobody ledgered, **all five instruments including `none` are indistinguishable and
nothing in CI fails.** The deliverable *does* say so where it reports (`print_reach()` states *"PASS
= 'no refuted claim is live in this one document'"*), so a green result does not overstate — **but
what it says is narrower than what a reader will take "5 remediation instruments are in use in this
arc" to mean**, because the five are enumerated in the same breath as the one-document scope.

**Did the repair mandate one remedy without justifying it?** **No, and this is right.** All four
non-standard instruments are named acceptable in a stated case; `strike-at-site` is argued as the
standard on a *mechanical* ground (it is the only one leaving a trace a control can confirm), not an
aesthetic one; and the ledger's four other uses are adjudicated correct at the site rather than
converted into violations. G4 was a missing standard and it was closed as one. **No regression.**

---

## 5. Finding A2 — "exactly ONE boundary", counted over four of the five

The repair states, in the instruments script, in the live-claim control's report, and in the
ledger's summary:

> *"Of the five, CI distinguishes exactly ONE boundary — a strike DECLARED but not MADE."*

Its **own measured matrix** puts the five instruments in **three** exit-code classes:

| class | instruments | signature |
|---|---|---|
| 1 | strike-at-site, rewrite-in-place, rewrite + annotation | (0, 0) |
| 2 | DELETION declared as a strike | (0, 1) / (1, 1) |
| 3 | none | (1, 0) |

Three classes is **two** boundaries. The "ONE" is correct over the **four instruments that remove
the claim** — `none` does not remove it, so it is not a boundary *between removal instruments* — but
the sentence says **"of the five"**. *Population stated as five, count taken over four.* That is a
population/count mismatch in the sentence that reports the G4 result, and it is the same family as
G3. **Small, and worth naming precisely rather than inflating**: the measurement is right, the
matrix is right, the reach statement is right; the summary sentence names the wrong population for
its number. Routed with A1.

---

## 6. Floor item — what the parent's row audit cannot see, and what mine could not

Nothing in the ticket asked for this. Two mutants of §6.1, each run against both checkers.

| mutant | the parent's `mg1d03_table_row_audit.py` | this audit's part (B) |
|---|---|---|
| **column-swap** — every figure moved into the *NAMED* column, *SWEPT* left with no integer; multiset over the row unchanged | **exit 0 — MISSED** | **CAUGHT** (2 gaps) |
| **extra row** — a fourth §6.1 data row naming no script, carrying `999 999` | **exit 0 — MISSED** | **CAUGHT** (rows present 4, checked 3) |

Both are structural, and both follow from how the parent selects and compares:

* it matches the integers of a row as **one multiset over the whole row**, so it cannot tell the
  NAMED column from the SWEPT column — in the table whose only purpose is to compare them;
* it collects rows by `` `onethird_\w+\.py` ``, so a data row that names no script is **not
  checked and not reported as unchecked**.

Neither is a wrong answer; both are **coverage** — the audit's own named-vs-checked. My part (B)
matches per column and treats an unrecognised data row as a failure, which is why it catches both.

**And my own tooling carried the defect I was auditing — twice.** *This lineage is now nine for
nine.* Both recorded rather than quietly fixed, both in the file's comments at the site:

1. **A decimal read as a population.** My first draft matched the docstring table's small counts
   with a bare `\b\d{1,2}\b`, which read the **`11`** of `(11.06x larger, posets)` as a poset count
   and failed a **correct** row. A number taken at the wrong grain, by the audit written to find
   numbers taken at the wrong grain. Fixed by one regex with `(?<![\w.])`/`(?![\w.])` guards.
2. **A mutant that did not reach its site.** `mutate_extra_row` first took the insertion point from
   `max(… "onethird_" in l)` over the whole file and landed the row in a **later section**; §6.1 was
   unchanged, the checker correctly found no gap, and that read as a **MISS**. Part (E) asserts each
   mutant is caught, so the run failed and said so. The mutant now takes its insertion point from
   the same parser the check uses. **A mutant that does not reach its site measures nothing** — and
   the only reason I know it happened is that the self-test was written to fail.

---

## 7. Third: do not disturb — all three re-run, all three hold

* **D1 — no true material lost. 2/2.** *Population: the two deletions mg-069f's audit §6 adjudicated
  "partly true, cut". Grain: one retained clause.* `(element, reference-order) cases` is present
  ×1 in `Spread-Locality` §2.3; `× **every** reference order` is present ×1 in the `mgd112` §2.2
  table row, two lines above the block that struck the sentence. Both true halves still sit in the
  same section as the deletion.
* **D2 — F4's decline to re-widen. 3/3.** *Population: the three proven-safe sites in
  `Bbias-Locality-Lemma.md` (§0, the §12 attempt-index row, the §12 narrative). Grain: one site.*
  The narrowed universal *"the (A)+(B) route has attacked since mg-8201"* occurs ×2 (§0 and the §12
  row); *"we hold on this route"* occurs ×1 (the §12 narrative). The body's wider Finding 3.4
  phrasing appears **only inside mg-069f's correction table, as a quotation**. Nothing was
  re-widened. mg-1d03 did not touch that file.
* **D3 — `Var(pos_σ z) = m(m+2)/12` is asserted.** `onethird_mg0242_identity_recheck.py` fails on
  `Var(pos z) != m(m+2)/12` and is wired into `script-controls.yml`. **Confirmed.**
  **Recorded, not fixed:** that script's own report still prints *"…which mg-069f put into live body
  text and no control asserts"*, and its docstring still says it *"asserts nothing about it
  anywhere"* — **now false of the script saying it**. A reader of the output concludes the number is
  unchecked when it is checked, one line below the check. Same class as A1: a report describing a
  state the code left. Routed with A1 and A2.

---

## 8. Limits — what this audit did not do

* **The 22 integer-cells are the two tables' cells only.** Figures elsewhere in the closeout (§6.2's
  exit-code table, §6.3's re-derivations) are *not* in my population and I did not check them. The
  ticket scoped me to the named-vs-swept table and its neighbours.
* **`--vs-parent` reads no history but does materialise a tree**, so it is off the default path.
  Every revision this audit names comes from `argv` or from this document; **no pinned SHA is a
  literal in the script**, per the mg-3934 rule, and the mg-3934 static control passes.
* **A3 is a finding about reach, not a proposal.** Whether the live-claim control's population
  should widen was measured and rejected once already (mg-0242 §8: ~94% false positive corpus-wide),
  and `mgcd04_declared_strike_control.py` is the structural answer that generalises. What A3 says is
  narrower: **the ledger's corpus sweep already sees the thing and does not assert on it**, and a
  baseline over that count would close the gap at the cost mg-0242 measured. That is pm-onethird's
  call, not mine, and I did not make it.
* **I did not repair A1, A2 or the D3 stale sentence.** All three are routed. The parent is merged;
  an audit that edits its subject leaves no record of what was wrong.

---

## 9. Routing

**To pm-onethird**, three items, none blocking:

1. **A1** — §6.1 row 3 and the live-claim control's report name **539 lines**; the document has
   **538**. Grain, not coverage. Baselined in
   `scripts/onethird_mg5854_row_and_instrument_audit.py`; closing it fails that control until the
   baseline entry is removed.
2. **A2** — *"of the five … exactly ONE boundary"* is a count over four. One sentence, three sites.
3. **D3's stale line** — `onethird_mg0242_identity_recheck.py` reports that no control asserts
   `Var(pos_σ z) = m(m+2)/12`, while asserting it.

**A3** is the substantive one and is not a defect to fix: **CI cannot tell an un-remediated refuted
claim from a struck one outside one document**, and the ledger's corpus sweep already sees them
without asserting. Disposition is pm-onethird's.
