# INDEPENDENT AUDIT of the mg-069f body-strike and population repair (mg-0242)

**Target:** `bb1cb9b` — *"close the mg-8a71 verdict — strike the two remaining live false claims, fix
the population every control NAMES, restore the true variance clause"* (mg-069f), which closes the
five findings of `docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md` (mg-8a71, `2697c07`).

**Independent audit, pre-filed in the same action as its parent.**

*(Section 1 records predictions written before any of them was run. Everything after §2 is the
result. Misses are kept as written.)*

---

## 0. Disclosure of contamination, made before the derivation

**I read `bb1cb9b`'s commit message before I read any of the documents it changed.** The message is
long (it restates all five findings, the population numbers, the missed prediction, and the flagged
rec-1 disagreement), so I cannot claim a blind read of the repair's own account of itself.

**What was therefore *not* independent:** that the two F1 sites are §3.2 and §5 rec 2; that the
populations at issue are 404/6 385/31 625 and 4 469/43 842/218 166; that rec 1 was flagged and not
acted on. I did not take any of these as *true* on the message's word — every number below was
re-counted and every claim re-read at the site — but I did take them as *where to look*.

**What was independent of it, and is not mentioned in the message, the closeout, or the verdict:**

* the **exempt-block asymmetry** (§4.1) — the label-vs-markup tightening was applied to `STRIKE`
  blocks and not to `EXEMPT` blocks, and an `ANNOTATION` label still exempts an unbounded block;
  found by mutation, demonstrated against a commit where it bites;
* the **live-claim control's own named-vs-swept gap** (§5.2) — the closeout's own named-vs-swept
  table names 537 lines where the control sweeps 539;
* the **corpus-wide** live-claim sweep and population-misstatement sweep (§5, §8) — both controls
  are single-file/single-script by construction, and neither the repair nor the verdict asked what
  the other 239 documents say;
* the **cross-generator identity** check (§5.1) — the corpus now has two independent all-labelled
  poset generators and nobody had checked they agree;
* the **W_m variance closed form** `Var(pos_σ z) = m(m+2)/12`, which mg-069f added to live body
  text in the F5 restoration and which no existing control computes (§7.3).

---

## 1. Predictions, written before running

| # | prediction | basis |
|---|---|---|
| P1 | `posets_with_identity_extension(n)` counts 7 / 40 / 357 = **404**; 6 385 pairs; 31 625 triples | the repair's claim, to be checked by calling and counting |
| P2 | `all_labelled_posets(n)` counts 19 / 219 / 4231 = **4 469**; 43 842 pairs; 218 166 triples | A001035 |
| P3 | `onethird_mgfccb_direction_check.py` → exit **0** | claimed passing |
| P4 | `onethird_mg8a71_audit_instrument.py` → exit **0** | claimed passing |
| P5 | `onethird_mg8a71_live_claim_control.py` at HEAD → exit **0** | claimed passing, baseline empty |
| P6 | same control on `1b00147^` → exit **1** | negative control claimed |
| P7 | same control on `1b00147` → exit **1** | negative control claimed |
| P8 | the live-claim control's docstring names **537** lines; the run will sweep **539** (`wc -l` = 538 ⇒ 538 newlines ⇒ 539 split elements) → **NAMED ≠ SWEPT**, a recurrence of F2 inside F2's own fix | arithmetic on the file |
| P9 | corpus-wide sweep of the four refuted-inference signatures over **all** of `docs/` finds **≥ 1** live hit outside the single controlled file | the control is one file by design; the inference has consumers elsewhere |
| P10 | corpus-wide sweep for the *population* misstatement finds **≥ 1** site not among the five the repair says it corrected | "corrected at every site" is the claim most likely to be one short |
| P11 | **mutant:** move a live assertion of signature S2 into the *tail* of an existing `ANNOTATION` blockquote → control exits **0** (misses it) | exemption is granted per-block from the first 3 lines, with no length bound |
| P12 | §5 rec 1's *"This is the single pin."* is **live and unstruck** at HEAD | the repair says so; verify at the site |
| P13 | (F1) `Σ_x m_x = 2E[inv_e]` and (★) `E[Σ disp²] = 2E[inv_e] + Cross` hold exactly on **43 842** pairs | re-run, in a third independent implementation |
| P14 | all four `W_m` closed forms, ratio exactly `1/3`, and `Var(pos_σ z) = m(m+2)/12` hold | ditto |
| P15 | the locality-lemma diff over the whole repair arc `1b00147^..HEAD` is **4 hunks**, none in §§1–11 | the standing constraint |
| P16 | `poset_family(n)` with the keyword omitted **raises `TypeError`** (refuses); `label_dependent=True` sweeps all 4 469 | keyword-only argument |
| P17 | `all_labelled_posets` (direction check) and `all_posets` (audit instrument) yield the **same set** of posets | two independent generators of the same population |
| P18 | count STRUCK vs count REFUTED over the claim ledger (§3): **struck < refuted** | rec 1 alone forces it |

*(Outcome table filled in at §8 after running. Misses are kept as written above.)*

---

## 2. Verdict

**GREEN on the repair's own five findings. AMBER on completeness: the standard is applied at 8 of
the 10 sites the arc has proved false, and one of the two remaining is unflagged.**

Nothing here overturns mg-069f. All five of its closures hold at the site, every population it names
equals the population it sweeps at script level, every identity and closed form it preserves is
reproduced by a third independent implementation, and the two negative controls still fail. Four
findings, none MEDIUM-or-above on the mathematics:

| # | finding | severity |
|---|---|---|
| **G1** | `mgd112` §2.2's *POPULATION CORRECTION* block says a sentence *"is struck with it"* and **does not strike it** — the exact hole mg-069f found by mutation and closed in the control, reappearing one document over in text mg-069f itself wrote. **Not flagged anywhere.** | **MEDIUM** (process), LOW (content) |
| **G2** | The label-vs-markup tightening was applied to `STRIKE` blocks and **not** to `EXEMPT` ones. An `ANNOTATION` label read from three lines still exempts a block of any length; the longest is **53 lines** and contains the §2.3 population correction mg-069f itself wrote. Demonstrated by mutation. | LOW |
| **G3** | Two named-vs-counted gaps introduced *by the repair*: the closeout's §6.1 table — the table whose purpose is to report named-vs-swept — names **537** lines where the control sweeps **539**; and the direction check's docstring labels the **404 → 4 469 poset** row *"6.9× larger"* where the ratio is **11.06×**. | LOW |
| **G4** | Three different remediation instruments were used on claims proved false (strike-at-site ×4, rewrite-in-place ×2, rewrite+annotation ×2, deletion ×1, nothing ×1) and only the first is named as the standard. The standard as stated — *"an annotation leaves the wrong claim in the body"* — does not distinguish them. | LOW |

**Confirmed, and re-derived rather than accepted:** the direction, both equality sites, both
identities on 43 842 pairs, all four `W_m` closed forms, the exact `1/3`, `Var = m(m+2)/12`, the
population counts at every granularity, the label-dependence guard, the two negative controls, the
four-hunk locality-lemma constraint, and the contamination disclosure.

> ### ✅ DISPOSITION (2026-07-31, mg-cd04): **G1 and G2 are CLOSED.** G3 and G4 stand.
>
> The findings above are left exactly as filed — this is the record of what was found, and an audit
> that is edited by the repair that answers it is no longer a record. What was done to each:
>
> * **G1 — closed at the site and at the population.** The markup was added in `mgd112` §2.2, and
>   the ledger's C9 baseline was removed (the "baseline site disappeared" gate fired as designed).
>   The population question this audit named but could not act on —
>   *"why the control does not look at that document"* — is answered by a new corpus-wide control on
>   the **structure** rather than the signatures: `scripts/onethird_mgcd04_declared_strike_control.py`,
>   242 documents, 2 hits, both of them **this report** quoting the defect it found, and both
>   baselined by name.
> * **G2 — closed.** An `EXEMPT` label now reaches its own sub-paragraph (bounded at 6 lines) plus
>   each later sub-paragraph that carries a quotation. Exempt lines in the target document fall from
>   **147 to 88**; the M1 mutant this audit built now exits **1**, and all three mutants are an
>   assertion rather than a report.
> * **One correction to §3, found by the G2 fix and not by re-reading.** With the exemption bounded,
>   the same ledger at `1b00147` reports **LIVE 8, not 7**: **C7** — the *"over all posets on
>   `n = 3,4,5`"* population claim mg-8a71 F2 proved false — sat in the *Machine-checked*
>   sub-paragraph of the 53-line `RE-DERIVATION` block, quoting nothing, **inside the very blind spot
>   §4.1 names**. So G2 was not only demonstrable by mutation; it was hiding a real ledger claim at
>   this audit's own demonstration commit. The reading §3 gives the drift — the repair working — is
>   unaffected and now **computed claim by claim** rather than narrated.
> * **G3 and G4 are NOT addressed here** and remain open; mg-cd04's scope was G1 + G2.
>
> Full account: `docs/OneThird-mg0242-G1G2-Repair.md`.

---

## 3. Primary: STRUCK against REFUTED

**The two numbers: 10 refuted, 8 struck.**

`scripts/onethird_mg0242_struck_vs_refuted.py` part (A). The ledger is every claim the
mg-fccb → mg-8a71 → mg-069f arc **proves, asserts, or inherits as false** and that lives (or lived) in
body text. Live-vs-marked is decided by **the repair's own classifier**, imported from
`onethird_mg8a71_live_claim_control.py` — the standard being applied is the standard the repair set,
not a stricter one this audit invented.

| id | claim | refuted by | instrument used | live at `bb1cb9b`? |
|---|---|---|---|---|
| C1 | §2.3 *"by Jensen … (B) fails by Θ(n²)"* | mg-1fdb / mg-fccb | strike-at-site | gone |
| C2 | §2.3 *"(B) hinges on capping `m_x`"* | mg-1fdb / mg-fccb | strike-at-site | gone |
| C3 | §3.2 *"Equivalently"* | mg-fccb's own §2.3 derivation | strike-at-site (mg-069f) | gone |
| C4 | §5 rec 2 *"that non-existence **is** (B)"* | mg-fccb's own annotation | strike-at-site (mg-069f) | gone |
| **C5** | §5 rec 1 *"This is the single pin."* | mg-fccb's annotation: *"rec 1 is **not** a pin"* | **none** — routed to pm-onethird | **LIVE**, line 475 |
| C6 | §13 row 2 *"restored … to the body's Finding 3.4 form"* | mg-8a71 F4 | rewrite-in-place | gone |
| C7 | §2.3 *"over all posets on `n = 3,4,5`"* | mg-8a71 F2 | rewrite + annotation | gone |
| C8 | `mgd112` §2.2 row *"over **all** posets"* | mg-8a71 F2 | rewrite + annotation | gone |
| **C9** | `mgd112` §2.2 *"over every poset and every reference order at those sizes"* | mg-8a71 F2 | **deletion, declared as a strike** | **LIVE**, line 144 |
| C10 | `mgd112` §6 *"sweep over all posets `n ≤ 5`"* | mg-8a71 F2 | rewrite-in-place | gone |

**REFUTED 10 · REMOVED FROM LIVE BODY TEXT 8 · STILL LIVE 2.**

Measured at the two pre-repair commits by the same ledger, so the number means something:

| tree | refuted | removed | live |
|---|---|---|---|
| `1b00147` (mg-fccb HEAD — F1's two sites still standing) | 10 | 3 | **7** |
| `bb1cb9b` (HEAD, after mg-069f) | 10 | 8 | **2** |

*(The same ledger at `1b00147^` reports LIVE 5, but that number is not comparable: some ledger
claims had not been written yet, and this instrument measures presence, so "not yet written" and
"struck" are indistinguishable there. `1b00147` is the honest comparison point — every ledger claim
exists in that tree.)*

### 3.1 C5 — flagged, and correctly so

mg-069f's §8 names this precisely, states both sides, and declines to reverse mg-8a71's
adjudication (*"not false, only mis-priced"*) against mg-fccb's annotation (*"rec 1 is **not** a
pin"*). It also explains why no `"single pin"` signature was added to the control — adding one would
encode a disposition nobody has made. **This audit agrees with the handling and adds nothing except
that the sentence is confirmed live at line 475**, and that the corpus sweep in §5 finds it in
exactly one place, so the routing has a bounded target.

### 3.2 C9 — G1, and it is not flagged anywhere

`docs/OneThird-mgd112-DroppedVerdict-Closeout.md:144` opens a blockquote:

> **POPULATION CORRECTION (2026-07-31, mg-069f — mg-8a71 finding F2).** … the sentence that followed
> — *"over every poset and every reference order at those sizes"* — **is struck with it.**

The block **declares the sentence struck and does not strike it**: there is no `~~` markup anywhere
in it. That is precisely the defect mg-069f discovered by mutation on §3.2 and closed in the control
— *"a block may no longer exempt itself by its label"* — reappearing, in the same commit, in text
mg-069f itself wrote, one document over from where the control looks.

By the repair's own convention this is a live assertion. Two structural notes:

* the block reads as a `STRIKE` block to the control (its head contains *"struck"*), so under the
  new rule it is checked with inline strikes removed — and there are none to remove. **mg-069f's own
  tightening would flag it, if the control were pointed at that file.** The control is one file, by
  design; that design is what leaves this uncaught.
* **content severity is LOW**: the surrounding sentence says *"It does not"*, so no reader is misled.
  It is the **process** finding that matters — the rule was closed in the instrument and not in the
  authoring.

The fix is one line: wrap the quoted sentence in `~~…~~`. Not applied here, for the same reason
mg-8a71 did not apply its own findings — this is an audit, and the repair belongs to whoever
dispositions it. It is recorded in this audit's ledger baseline, so it cannot now be lost.

### 3.3 G4 — three instruments, one named standard

The standard mg-fccb stated and mg-069f applied is *strike at the site; an annotation leaves the
wrong claim in the body*. Counted over the ledger, the arc actually used **five** dispositions:

| instrument | count | removes the claim from live body text? |
|---|---|---|
| strike-at-site, retained struck | 4 | yes |
| rewrite-in-place | 2 | yes — but the corpus keeps no record of what was there |
| rewrite + a correction annotation | 2 | yes, with a record |
| deletion, *declared* as a strike | 1 | **no** — C9 |
| none (flagged and routed) | 1 | no — C5 |

The three that work all satisfy the standard as *stated*; the standard simply does not name them, so
nothing distinguishes the two that do keep a record from the one that does not. This is not a defect
in any individual edit — it is why C9 could be written by an author applying the rule in good faith.

---

## 4. The document-level control: does it cover the two F1 sites?

**Yes — it covers them and does not carry them.** `BASELINE = set()`, empty, and the two sites are
reached by live signatures S3 and S4 rather than tolerated:

| run | predicted | actual | what fires |
|---|---|---|---|
| HEAD | 0 | **0** | nothing live |
| `1b00147^` (pre-repair, §2.3 live) | 1 | **1** | S1 + S2 @ 171, S3 @ 245, S4 @ 347 |
| `1b00147` (mg-fccb HEAD, F1's two sites) | 1 | **1** | **S3 @ 306 (§3.2), S4 @ 408 (§5)** |

The third row is the one the verdict asks about: the two F1 sites are what makes the control fail at
`1b00147` and pass at HEAD. They are *detected*, not *baselined*. P5–P7 hit.

### 4.1 G2 — the tightening covers one of the two marker classes

mg-069f closed the hole where a blockquote could exempt itself by **declaring** `STRUCK`. That
tightening was applied to `STRIKE` blocks. `EXEMPT` blocks — `ANNOTATION` / `RE-DERIVATION` — are
still skipped **entirely**, on the strength of a label read from `block[:3]`, with **no bound on how
long the block runs**. Three mutants, exit codes predicted before running:

| mutant | predicted | actual | |
|---|---|---|---|
| **M1** the refuted sentence appended to the **tail of an `ANNOTATION` block** | 0 (missed) | **0** | **MISSED** |
| **M2** the same sentence as an ordinary paragraph | 1 | **1** | caught |
| **M3** the same sentence appended to the **tail of a `STRIKE` block** | 1 | **1** | caught |

M2 is what makes M1 mean something: the sentence is catchable, and the exemption is what hides it.
M3 shows mg-069f's tightening does work — on the class it was applied to.

**This is not hypothetical.** In `OneThird-L1b-Spread-Locality.md` the longest `ANNOTATION` block runs
**lines 252–304, 53 lines**, and the §2.3 *Machine-checked* paragraph **and the `POPULATION,
corrected … mg-069f` paragraph the repair itself added for F2** are inside it. Live, load-bearing,
non-annotation content sits in the control's blind spot because a label three lines up says
`ANNOTATION`. Across the file: 539 lines, **319 checked (59.2%)**, **147 exempt (27.3%)**, 73 blank.

The fix is not "stop exempting annotations" — commentary about a refuted claim must quote it. It is
to bound the exemption the way the strike is now bounded: a marker exempts its own block only while
that block is quotation-and-diagnosis, e.g. end the exempt run at a blank-line-separated
sub-paragraph that carries no quote marker. **Not applied here** — changing the control's semantics
is a repair, not an audit.

---

## 5. Second: every population a control NAMES, counted

`scripts/onethird_mg0242_population_census.py`. **Every helper was called and the results counted.
No name and no docstring was read as evidence.** Runtime ~2 s.

| population NAMED by | named | **counted, by calling the helper** | |
|---|---|---|---|
| `posets_with_identity_extension` (per `n`) | 7 / 40 / 357 | **7 / 40 / 357** | ✅ |
| … total posets / pairs / triples | 404 / 6 385 / 31 625 | **404 / 6 385 / 31 625** | ✅ |
| `all_labelled_posets` (per `n`, A001035) | 19 / 219 / 4231 | **19 / 219 / 4231** | ✅ |
| … total posets / pairs / triples | 4 469 / 43 842 / 218 166 | **4 469 / 43 842 / 218 166** | ✅ |
| `onethird_mg8a71_audit_instrument.all_posets` | 4 469 / 43 842 / 218 166 | **4 469 / 43 842 / 218 166** | ✅ |
| live-claim control, per closeout §6.1 | **537** lines | **539** lines | ❌ **G3** |
| direction-check docstring, poset row | **6.9×** larger | **11.06×** | ❌ **G3** |

### 5.1 A check nobody had run: the two generators are the same SET

The corpus now holds **two independent all-labelled generators** — `all_labelled_posets` (the
`S_n`-orbit of the identity-extension family) and the audit instrument's `all_posets` (three-state
assignment per pair, filtered for transitivity). Both are asserted to return 4 469. **Equal counts
are not an equal population.** Set equality, checked here for the first time:

| `n` | orbit construction | 3-state filter | sets equal |
|---|---|---|---|
| 3 | 19 | 19 | **yes** |
| 4 | 219 | 219 | **yes** |
| 5 | 4231 | 4231 | **yes** |

### 5.2 G3 — two gaps the repair introduced

**537 vs 539.** The closeout's §6.1 is the table whose entire purpose is to report *population NAMED
vs population SWEPT*; its third row reads *"one file, all of it" → **537/537 lines**, … asserted to
sum"*. The control sweeps **539** (`wc -l` = 538 ⇒ 538 newlines ⇒ 539 `split("\n")` elements). The
script's own assertion `sum(coverage) == len(lines)` passes — it compares the sweep against itself
and cannot see a number written in a document. The gap is 2 lines and changes nothing mathematically;
it is reported because **F2's own remediation table is the last place a named-vs-swept gap should
appear**, and because it shows the internal assertion, though sound, does not discharge the external
claim.

**6.9× vs 11.06×.** `onethird_mgfccb_direction_check.py`'s docstring table ends:

```
      tot |          404  |                    4469          (6.9x larger)
```

`4469 / 404 = 11.0619`. **6.9× is the ratio of PAIRS (43 842/6 385 = 6.866) and of TRIPLES
(218 166/31 625 = 6.899)** — correct for the per-element sweep, wrong on the poset row it is attached
to. The same figure recurs in prose (*"would silently under-sweep by 6.9×"*) where it is defensible
under the per-triple reading; the table row is the one place it is unambiguous and wrong. The
label-dependence probe below measures the poset-level under-sweep directly and gets **11.06×**.

### 5.3 `all_posets`'s replacement at a LABEL-DEPENDENT property

The verdict asks whether the replacement *sweeps all labellings or refuses*. **It does both, and
correctly.** The probe uses the sharpest label-dependent property available — *"is the identity
permutation a linear extension of `P`?"*, which is 100% on the small family **by construction** and
9.0% on the labelled one, so a silent substitution is maximally visible:

| call | behaviour |
|---|---|
| `poset_family(n)` | **REFUSES** — `TypeError: missing 1 required keyword-only argument: 'label_dependent'` |
| `poset_family(n, label_dependent=True)` | sweeps **4 469** posets → **404/4 469 = 9.0%**, the true answer |
| `poset_family(n, label_dependent=False)` | sweeps 404 → **404/404 = 100.0%**, the wrong answer, **11.06× under-swept** |

The keyword is keyword-only and has no default, so **a caller cannot fail to choose**. That is the
right design and it closes F2's stated hazard.

**The bounded residual, stated because the closeout states the guard as if it were total.** Parsed
with `ast` (not grepped, so `def` lines and docstrings are not miscounted): **4 call sites go through
`poset_family`, 3 are internal to the family helpers, and 0 real consumers bypass it.** But both
generators remain public module-level names. The guard therefore binds current callers **by
construction** and future ones **by convention** — a documented convention, but not an enforced one.
Making `posets_with_identity_extension` private (leading underscore) would close the difference.

---

## 6. Third: over-correction — was any true material removed?

**No true material was lost from the corpus.** Two deletions did cut a true clause along with a false
one, and in both cases the true half survives verbatim within the same section — so this repair did
**not** repeat F5, which is the failure mode it was told to watch for.

`scripts/onethird_mg0242_struck_vs_refuted.py --deletions bb1cb9b` lists all **38** document/CI lines
the repair deleted. (It is behind a flag, not on the default path — see §8.) Adjudicated at the site:

| deletion | was the deleted text false? | verdict |
|---|---|---|
| §2.3 *"over all posets on `n = 3,4,5` **and every reference order**"* | *"all posets"* false; ***"every reference order" TRUE*** | **partly true, cut** — but the replacement keeps *"(element, reference-order) cases"* and the §2.3 population note restates the family; nothing lost |
| `mgd112` *"over every poset **and every reference order** at those sizes"* | same split | **partly true, cut** — the table row two lines above retains *"× **every** reference order"* verbatim; nothing lost |
| §2.3 *"`b_x = m_x` at the `e`-minimum … (which is why §3.1 stands)"* | true | **replaced by a superset** (e-min **and** e-max) — F3's addition, not a cut |
| §3.2 *"Equivalently: …"* | false | struck and retained struck ✅ |
| §5 rec 2 *"If it does not exist, that non-existence *is* (B)"* | false | struck and retained struck ✅ |
| §13 row 2 *"restored … to the body's Finding 3.4 form"* | false (F4) | rewritten; the row's *finding* column is untouched ✅ |
| CI *"sweeps ALL posets … ~8 s"* | both false | rewritten; the true half (*"actively hunts a counterexample"*, the e-min pin, the §3.1 trap) is retained and extended ✅ |
| CI mg-8a71 step's diagnostic paragraph | true | **rewritten, not cut** — 404, the isomorphism argument and 14.5% all survive in the step-1 comment ✅ |
| CI baseline paragraph + *"Demonstrated to FAIL on `1b00147^`"* | true, but superseded | rewritten; the reproduce command survives and an exit-code table is added ✅ |
| `mgd112` §2.2 / §6 rows | *"all posets"* false | rewritten; *"× every / all reference orders"* retained in both ✅ |

**F4 is the interesting one, and mg-069f got it right.** It found the finding was *wider* than
reported — three narrow sites, not one — and then **declined to widen the text**, on the ground that
three narrower-than-proven statements are a correct record and re-editing proven-safe prose a third
time is itself the over-correction risk. Verified at the far end: `§0`, the `§12` row and the `§12`
narrative are each **at most as strong as** §3.4, so leaving them is sound. Correcting the
*description* and not the *text* is the right call and is the opposite of the F5 mistake.

---

## 7. Fourth: preserve

### 7.1 The contamination disclosure — intact

`docs/OneThird-mgfccb-DirectionRepair-IndependentAudit.md` §1.1, *"Disclosure of contamination, made
before the derivation"* (lines 34–48), is **byte-identical** at `bb1cb9b`; mg-069f touched that file
only to append §9. **No regression.** This audit files its own disclosure at §0 above.

### 7.2 The beyond-the-list identities — re-run in a third implementation

`scripts/onethird_mg0242_identity_recheck.py`, written from the §0/§2.3 definitions with its own
poset enumerator, its own linear-extension generator and its own inversion bookkeeping. It shares no
line with either instrument in CI. **23 s, exact `Fraction`, no sampling.**

| check | population | result |
|---|---|---|
| **(F1)** `Σ_x m_x = 2E[inv_e]` | **43 842** (poset, reference-order) pairs | **0 violations** |
| **(★)** `E[Σ disp²] = 2E[inv_e] + Cross`, as `disp = A_x − B_x` | 43 842 pairs, every `σ` | **0 violations** |
| **(★)** `A_x + B_x` = the inversion **degree** of `x` | 43 842 pairs, every `σ` | **0 violations** |
| **(★)** `Σ_x (A_x+B_x) = 2·inv_σ` (handshake) | 43 842 pairs, every `σ` | **0 violations** |
| **(★)** `Cross` from **its own double sum** `Σ_x Σ_{y≠z} ε_{xy}ε_{xz} E[I_{xy}I_{xz}]` | **1 002** pairs (`n = 3,4`; the `n = 5` double sum is ~3·10⁸ terms) | **0 mismatches** |
| `b_x ≤ m_x` | **218 166** triples | **0 violations** (76 116 strict, 142 050 equal) |
| `b_x = m_x` at the `e`-min | 43 842 | **43 842/43 842** |
| `b_x = m_x` at the `e`-max | 43 842 | **43 842/43 842** |

The strict/equal split (**76 116 / 142 050**) reproduces mg-8a71's instrument exactly, from
independent code. **(★) is stated here as the decomposition it factors into**, because that is its
content — `disp_σ(x)` is a *signed* sum of the pair-inversion indicators involving `x`, so the
diagonal of its square is the inversion degree and the off-diagonal is `Cross`. Computing `Cross` as
`E[Σdisp²] − 2E[inv]` and then "verifying" (★) would be circular; the double-sum recomputation at
`n = 3,4` is what makes it a check.

### 7.3 The four `W_m` closed forms, `1/3`, and `Var = m(m+2)/12`

Recomputed from `L(W_m)` by enumeration at `m = 2,4,6,8,10,12` — **two `m` beyond what any existing
control reaches** — against the closed forms, not from them:

| `m` | `E[inv_e]` | `s(s+1)/(2s+1)` | `Σ b²` | `s(s+1)/(3(2s+1))` | ratio | `Var(pos_σ z)` | `m(m+2)/12` |
|---|---|---|---|---|---|---|---|
| 2 | 2/3 | 2/3 | 2/9 | 2/9 | **1/3** | 2/3 | 2/3 |
| 4 | 6/5 | 6/5 | 2/5 | 2/5 | **1/3** | 2 | 2 |
| 6 | 12/7 | 12/7 | 4/7 | 4/7 | **1/3** | 4 | 4 |
| 8 | 20/9 | 20/9 | 20/27 | 20/27 | **1/3** | 20/3 | 20/3 |
| 10 | 30/11 | 30/11 | 10/11 | 10/11 | **1/3** | 10 | 10 |
| 12 | 42/13 | 42/13 | 14/13 | 14/13 | **1/3** | 14 | 14 |

All four forms hold, `m_z = E[inv_e]` holds, and the ratio is **exactly `1/3`** at every even `m`.

**`Var(pos_σ z) = m(m+2)/12` is the one no control asserted.** mg-069f put it into **live body text**
in the F5 restoration (*"`Var(pos_σ z) = m(m+2)/12 = Θ(n²)` against `E[inv_e] = Θ(n)`"*); the
direction check only mentions it in a print comment and asserts nothing about it. A restored clause
resting on an unasserted number is the F5 risk running the other way. **It is now asserted**, in CI,
in §7.2's instrument. This is one of the two things this audit checked that no list here named.

### 7.4 The locality-lemma diff — 4 hunks, none in §§1–11

Over the **whole arc** `1b00147^..HEAD`, `docs/OneThird-Bbias-Locality-Lemma.md` shows exactly **4**
hunks:

| hunk | new lines | section |
|---|---|---|
| `@@ -38,12 +38,16 @@` | 38–53 | **§0 Verdict** (lines 15–84) |
| `@@ -814,7 +818,7 @@` | 818 | §12 (lines 813–844) |
| `@@ -822,8 +826,9 @@` | 826 | §12 |
| `@@ -837,5 +842,62 @@` | 842–903 | §12 tail → **§13** (lines 845–903) |

**None touches §§1–11** — the mathematics (§1 pinning, §3 re-pricing, §4 lossy step, §6 separations,
§7 local structure, §10 claim ledger, §11 self-audit) is untouched across the entire arc. Constraint
satisfied. P15 hit.

---

## 8. Predictions: 17 of 18 hit, and the misses

| # | predicted | actual |
|---|---|---|
| P1 | 404 / 6 385 / 31 625 | ✅ |
| P2 | 4 469 / 43 842 / 218 166; 19/219/4231 | ✅ |
| P3 | `direction_check` exit 0 | ✅ 0 |
| P4 | `audit_instrument` exit 0 | ✅ 0 |
| P5 | live-claim control at HEAD → 0 | ✅ 0 |
| P6 | on `1b00147^` → 1 | ✅ 1 |
| P7 | on `1b00147` → 1 | ✅ 1, and via **S3 §3.2 + S4 §5** — the F1 sites |
| P8 | named 537 ≠ swept 539 | ✅ 539 — though the `537` turned out to live in the **closeout's §6.1 table**, not in the script's docstring as P8 guessed; the script names only *"the file's line count"*, which is true by construction |
| P9 | ≥ 1 live corpus hit outside the controlled file | ✅ 21 (17 pre-existing) — **but see below** |
| P10 | ≥ 1 population site the repair missed | ❌ **MISS — zero** |
| P11 | exempt-tail mutant → exit 0 (missed) | ✅ 0 |
| P12 | *"single pin"* live and unstruck | ✅ line 475 |
| P13 | (F1) and (★) exact on 43 842 pairs | ✅ 0 violations |
| P14 | four `W_m` forms, `1/3`, `m(m+2)/12` | ✅ to `m = 12` |
| P15 | 4 hunks, none in §§1–11 | ✅ |
| P16 | `poset_family` refuses without the keyword | ✅ `TypeError` |
| P17 | the two all-labelled generators are the same set | ✅ at `n = 3,4,5` |
| P18 | struck < refuted | ✅ 8 < 10 |

### The two misses, kept as written

**P10 missed, and the miss is the finding.** I predicted the repair's *"corrected at every site the
wrong population appeared"* would be one site short — that claim usually is. An independent
corpus-wide sweep for every phrasing that names a poset population (`all posets`, `every poset`,
`4 469`, `31 625`, `43 842`, `218 166`, `6 385`) across **all** of `docs/`, `scripts/` and
`.github/` found **zero** uncorrected sites. Every remaining hit is either a different subject
(general statements about all posets, other probes' own populations, correctly-qualified generators
elsewhere in `scripts/`) or a **quotation of the old wording inside an audit document**, which is
what an audit document is for. **The claim is true as stated.** The two G3 gaps are numbers the
repair *introduced*, not sites it *missed* — a different failure, found by a different sweep.

**P9 hit on the number and missed on the meaning.** 21 live hits across 6 documents — of which 4 are
in *this report*, which quotes what it audits, leaving **17 across 5 pre-existing documents**. Read at
the site, **16 of those 17 are quotations inside audit and closeout documents diagnosing the refuted
claim** — propagation tables, consumer ledgers, quoted sentences. Not one is an assertion. The single
substantive hit is C5, *"the single pin"*, already in the ledger. So: **the refuted inference is
asserted in live body text nowhere in the corpus outside its home document**, which is a stronger
result than the repair claimed and one it did not check.

That sweep also answers, quantitatively, a question mg-069f §8 left as a judgement call — *should
there be a corpus-wide version of the live-claim control?* **Not with this convention.** 16 of 17
hits are legitimate discussion that the convention has **no way to mark**: it exempts only
blockquotes labelled `ANNOTATION`/`RE-DERIVATION`, and audit documents discuss refuted claims in
**tables and prose**. A corpus-wide control on today's rules would be ~94% false-positive. §8's
decision was right; this is the measurement behind it.

### One more miss, inside the instrument

My first ledger pass used a bare `/jensen/` pattern for C1 and flagged §2.3's **corrected** sentence
(*"Jensen gives `E[Σdisp²] ≥ Σ_x E[disp(x)]²` correctly; what fails is the next substitution"*),
which uses Jensen legitimately. The repair's own S1 predicate — *jensen* **and** *m_x* **and**
(*"(B) fails"* or *Θ(n²)*) — does not fire there. Recorded rather than quietly fixed: the ledger now
imports the control's predicates, so the standard applied is the repair's, not a looser one of mine.
A stricter auditor's pattern is not a finding.

### A third miss: an existing control caught my own instrument

I did **not** predict this. `script-controls.yml` checks out at `actions/checkout`'s default depth 1,
deliberately and at length, and my ledger's deletion review read a **pinned revision** (`git show
bb1cb9b`) on its default path. In CI that step would have been **dead on arrival** — correct on a
developer's box, unrunnable on the runner. That is precisely the mg-3934 defect, and **mg-3934's own
static control caught it**, in this worktree, before the branch was pushed:

```
PROBLEMS (1):
  - .github/workflows/script-controls.yml runs code that reads historical revisions --
    scripts/onethird_mg0242_struck_vs_refuted.py (bb1cb9b) -- but its actions/checkout sets
    fetch-depth unset (=1).
```

Fixed by moving the history read behind `--deletions <rev>` (and `--tree <rev>`), so no pinned
revision is named in code and nothing on the default path touches history; the control is clean
again. Recorded because an audit that shipped a dead CI step while reporting on someone else's dead
CI step would be the worst possible outcome, and because it is a working demonstration that mg-3934's
control does the job it was built for, on a script written after it.

### A measurement I had to withdraw

First run of `onethird_mgfccb_direction_check.py` on this host: **28 s**, against the `14.5 s` the
repair wrote into the CI comment (itself a correction of mg-fccb's `~8 s`). Re-measured in isolation:
**19.8 s** cold, **14.7 s** warm. The first figure was taken under concurrent load. **The repair's
14.5 s is confirmed**; the discrepancy was mine. Noted because the alternative — reporting a 2×
runtime drift on the strength of one loaded measurement — is exactly the kind of finding this family
is supposed to catch before it ships.

---

## 9. The floor: what this audit checked that no list here named

Three things, all of them chosen because they sit exactly where a named check stops:

1. **`Var(pos_σ z) = m(m+2)/12`** (§7.3). The preserve list names the two identities and *"all four
   `W_m` closed forms"*; nothing said that the fourth of them was the one mg-069f added to **live
   body text** in the F5 restoration while asserting it **nowhere**. Now asserted, in CI, at
   `m = 2…12`.
2. **The two all-labelled generators are the same SET** (§5.1). The list says *count what each
   helper enumerates*. Both count 4 469; that was never evidence they enumerate the same 4 469. They
   do — checked, at every `n`.
3. **The exempt-block asymmetry** (§4.1). Found by asking of mg-069f's own tightening the question
   mg-069f asked of mg-fccb's: *you stated a rule and applied it to one of the classes it reaches.*
   `STRIKE` blocks now have to back their label with markup; `EXEMPT` blocks still do not, and the
   longest one in the target document swallows 53 lines including text the repair itself wrote.

**And a fourth, negative:** the label-dependence probe was built expecting `poset_family` to have a
hole. It does not. Reporting that it holds is part of the floor too.

---

## 10. Instruments

All three are stdlib-only, exact, deterministic, and wired into
`.github/workflows/script-controls.yml`. Every one is demonstrated against a commit where the defect
it hunts is still present.

| script | what it settles | HEAD | demonstration |
|---|---|---|---|
| `scripts/onethird_mg0242_population_census.py` | every population NAMED, **counted** by calling the helper; cross-generator set identity; label-dependence; guard reach; the control's own line count | **0** (2 baselined doc gaps) | `--demonstrate 2697c07` → `all_posets`, docstring *"All posets on n labelled elements"*, **404 enumerated**: an 11.06× gap, found by counting |
| `scripts/onethird_mg0242_struck_vs_refuted.py` | the 10-claim ledger under the repair's own classifier; 241-document corpus sweep; 3 mutants; deletion review (`--deletions <rev>`) | **0** (2 baselined live sites) | `--tree 1b00147` → **LIVE 7** vs LIVE 2 here |
| `scripts/onethird_mg0242_identity_recheck.py` | (F1), (★), the four `W_m` forms, `1/3`, `Var = m(m+2)/12`, direction and both equality sites — third independent implementation | **0** | it *is* the demonstration: it reproduces 43 842 / 218 166 / 76 116 / 142 050 from code sharing no line with either CI instrument |

Both baselines behave the way mg-8a71's did: a **new** violation fails, and a **baselined** one being
repaired **also** fails, so whoever fixes G1 or G3 is forced to re-baseline rather than pass silently.

---

## 11. What this audit did not do

* It did **not** re-open the mathematics beyond §7.2–7.3. The re-derivation is of the *identities and
  closed forms*, not of Theorems 3.2/3.3, the `(EQ)` redirect, or the §3.1 trap — those rest on
  mg-8a71's hand derivation, which this audit did not repeat.
* It did **not** fix G1, G2 or G3. An audit that repairs what it finds cannot report what it found;
  mg-8a71 did not repair mg-fccb either. All three are one-to-few-line changes and all three are held
  by a control baseline so they cannot be lost.
* It did **not** re-open C5. mg-069f's handling — flag, route, decline to reverse an adjudication —
  is correct, and this audit confirms only that the sentence is live and that it occurs in exactly
  one place.
* It did **not** re-read mg-8a71's cross-doc ledger. Only the rows F4 touches were re-read, at the
  far end, and they confirm mg-069f's widening of F4.

---

*Deliverable for mg-0242. Independent audit, pre-filed in the same action as its parent (mg-069f).
Computation: `scripts/onethird_mg0242_population_census.py` (2 s),
`scripts/onethird_mg0242_struck_vs_refuted.py` (3 s),
`scripts/onethird_mg0242_identity_recheck.py` (23 s) — all three in CI, all three demonstrated
against a commit where their target defect is still present. 18 exit codes and outcomes predicted
before running; 17 hit, 2 misses (P9's meaning, P10) kept as written, plus an unpredicted CI-depth defect
in this audit's own instrument (caught by mg-3934's control), one instrument miss, and one
withdrawn measurement — all recorded in §8.*
