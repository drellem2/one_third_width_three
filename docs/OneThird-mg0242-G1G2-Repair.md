# Closing mg-0242 findings G1 and G2 (mg-cd04)

**Target:** `docs/OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md` (mg-0242, `ad9ba10`) —
the independent audit of `bb1cb9b` (mg-069f), which closed the five findings of mg-8a71's audit of
mg-fccb.

**Scope:** findings **G1** and **G2** only. **G3** (two named-vs-counted gaps the repair introduced)
and **G4** (three remediation instruments, one named standard) are **not addressed here and remain
open**.

**The audit's own findings are not rewritten.** A disposition block was appended to its §2; the
finding text, the severities, the prediction table and the misses stand exactly as filed.

---

## 0. Verdict

| finding | disposition |
|---|---|
| **G1** — a block declares a sentence struck and does not strike it, unflagged, one document over from where the control looks | **CLOSED at the site and at the population** |
| **G2** — the label-vs-markup tightening covers `STRIKE` blocks and not `EXEMPT` ones; a three-line label exempts a block of any length | **CLOSED** |
| the ledger drift `LIVE 7 → LIVE 2` | **reading CONFIRMED, and one claim understated — it was 8, not 7** |
| **G3**, **G4** | untouched, open |

Five exit codes, all predicted before running, all hit — §5.

---

## 1. G1 at the site: one line

`docs/OneThird-mgd112-DroppedVerdict-Closeout.md` §2.2's *POPULATION CORRECTION* block said, verbatim

```
the sentence that followed — *"over every poset and every reference order at those sizes"* — is
struck with it
```

and did not strike it. The quoted sentence carries `~~…~~` now, so the declaration is backed by the
markup it declares. Content severity was LOW and remains so — the adjacent clause says *"It does
not"* — and mg-0242's process reading is the right one: **the rule was closed in the instrument and
not in the authoring**, in the same commit, by the same author.

A dated note records what changed and why, in the corpus's usual form.

**The ledger consequence.** `scripts/onethird_mg0242_struck_vs_refuted.py` carried C9 as a baselined
live site. With the markup in place the classifier reports it gone, the **"baseline site
disappeared"** gate fired — exactly the behaviour mg-8a71 built and mg-0242 kept, so that repairing a
baselined finding cannot pass silently — and C9 was removed from `KNOWN_LIVE` rather than left to
rot. The ledger now reads **REFUTED 10 · REMOVED 9 · LIVE 1**, and the one live entry is C5, which
mg-069f flagged and routed and which is not this instrument's to disposition.

---

## 2. G1 at the population: the question the audit could not ask

mg-0242 put the real finding one level up:

> *A control whose population stops at one document is the same defect one level up.*

That is right, and it is why the one-line fix is not the whole repair. The live-claim control reads
one file, deliberately and at length; the defect was authored into a second file; **no control could
see it**, and the class it belongs to is not file-specific at all.

**Why the obvious generalisation is wrong, and was already measured.** mg-0242 §8 ran the live-claim
control's four *signatures* across all of `docs/` and found **16 of 17 pre-existing hits were
quotations inside audit and closeout documents diagnosing the refuted claim** — legitimate discussion
the convention has no way to mark. A corpus-wide signature control would be ~94% false positive.
That measurement stands, and this repair does **not** widen the signature control's population.

**What generalises is the structure, not the content.**

> A sentence that says text is struck must carry the markup.

No claim, no subject matter, no adjudication — so an audit document quoting a refuted sentence does
not trip it, and a block that promises a strike it did not make does.
`scripts/onethird_mgcd04_declared_strike_control.py` checks exactly that, over **242 documents,
100 527 lines, every line classified and asserted to sum to each file's line count**.

Three design choices, each forced by something the corpus actually contains:

1. **Both halves are required** — a strike declaration *and* a quoted sentence. A block that
   declares a claim struck without quoting anything is reporting an edit made elsewhere, which is
   most of this corpus's prose about strikes.
2. **Scope is the SENTENCE, not the block.** `OneThird-mg8a71-VerdictRepairs-Closeout.md` §0 quotes
   a remediation standard in one sentence and reports, in the next, that two claims elsewhere have
   been struck. That is a true report about another document, and block scope calls it a defect.
   Sentence scope does not. It is printed as a **near miss** — reported, never failed on — so the
   narrowing is visible rather than silent.
3. **The text is flattened before matching.** Prose here is hard-wrapped at ~100 columns and a
   quoted sentence routinely straddles the wrap. **The G1 site itself does** — a line-oriented match
   found nothing at `bb1cb9b`, which is to say it would have missed the one defect the control was
   built for. Recorded because it was a real error in the first draft of this control, caught by
   demanding the demonstration before trusting the pass.
4. **Fenced code is skipped**, and that is a rule rather than a convenience. Inside a fence the
   corpus is showing text as literal data, not asserting it; a `~~` in there would not strike
   anything either. So a fence is the marked way for a document to reproduce a defective block
   verbatim without promising a strike of its own — which is how §1 above quotes the G1 site.
   **Found the way findings in this family usually are:** the first draft of *this* report quoted
   that block as an ordinary blockquote and tripped the control. The alternative was a baseline
   entry for every document that ever discusses the defect — a control that grows a tolerance each
   time it is right.

**At HEAD: 2 hits, both baselined, both `OneThird-mg069f-BodyStrikePopulation-IndependentAudit.md`
quoting the defect it found.** An audit that could not quote the text it found would not be an audit.
Baselined by `(file, quoted span)` rather than by line number, so the entries survive reflow; and as
everywhere in this arc, a baseline entry that stops matching **also** fails the run.

**Demonstrated where the defect is present:** `--demonstrate bb1cb9b` finds `mgd112` §2.2 **and
nothing else in the 239 documents that tree holds**.

---

## 3. G2: an EXEMPT label now reaches only as far as it is backed

mg-069f stopped a `STRIKE` block exempting itself by its label — such a block is checked with inline
`~~` spans removed, so declaring `STRUCK` without the markup fails. That tightening was applied to
**one of the two marker classes**. `EXEMPT` blocks (`ANNOTATION` / `RE-DERIVATION`) were still
skipped **entirely**, on a label read from `block[:3]`, with **no bound on how long the block ran**.

Two rules replace that, and between them every exempt line is now either close to the label or backed
by its own markup:

* the **label's own sub-paragraph** is exempt on the label's word alone — that is what a label is —
  but for at most `MAX_LABEL_LINES = 6` lines. This is the one unbacked exemption left, and it is
  the one that is bounded;
* every **other** sub-paragraph is exempt only if it carries a **quotation**. Commentary about a
  refuted claim has to quote the claim, and that quotation is the entire reason the exemption exists.
  A sub-paragraph that quotes nothing is body text wearing a label three lines up, which is precisely
  the blind spot.

`QUOTATION` deliberately excludes inline code: `` `m_x` `` is on nearly every line of this corpus, and
accepting it would hand the exemption straight back.

**Judged per sub-paragraph, not as a prefix run — and that is not a detail.** mg-0242 suggested
ending the exempt run at the first non-quoting sub-paragraph. Implemented that way it produces **two
false positives** on the unmodified document: §2.3's mg-1fdb annotation interleaves a non-quoting
diagnosis paragraph with quoting ones, so cutting the run merges every quotation after it into one
checked unit and the control fires **on the quotations themselves**. Per sub-paragraph, each is
judged on its own markup. The appended-tail mutant is still caught, because the mutant quotes
nothing. Recorded rather than quietly corrected: the audit's suggested rule was one step short, and
the step is visible only by running it.

### 3.1 Effect, measured

| | before (mg-069f) | after (mg-cd04) |
|---|---|---|
| lines exempt on a label | **147** (27.3%) | **88** (16.3%) |
| lines checked | 319 (59.2%) | **378** (70.1%) |
| checkable units | 69 | 78 |
| longest reach of a single label | **53 lines** | 6 lines unbacked, the rest quotation-backed |
| new live sites at HEAD | — | **none** |

The three mutants mg-0242 built are now an **assertion**, not a report — all three must exit 1:

| mutant | at mg-0242 | now |
|---|---|---|
| **M1** refuted sentence in the tail of an `ANNOTATION` block | **0 — MISSED** | **1 — caught** |
| **M2** the same sentence as an ordinary paragraph | 1 — caught | 1 — caught |
| **M3** the same sentence in the tail of a `STRIKE` block | 1 — caught | 1 — caught |

M1 returning to exit 0 now fails the ledger script with an explicit **G2 regression** message.

---

## 4. The ledger drift: the reading holds, and the number was one short

mg-0242 measured the same ledger at two trees — **LIVE 7** at `1b00147`, **LIVE 2** at `bb1cb9b` —
and read the difference as the repair working. The verdict asked for that reading to be confirmed
rather than accepted, because it is the shape mg-8d5e closed elsewhere.

**It holds, and it is now computed rather than narrated.** `--tree <rev>` diffs the live sets claim by
claim and prints which claims left live text, which entered, and by what instrument:

```
LIVE at 1b00147 : C3, C4, C5, C6, C7, C8, C9, C10
LIVE at HEAD    : C5
LEFT live text  : C3, C4, C6, C7, C8, C9, C10   (7 claims)
ENTERED live text: —
```

Every claim in `LEFT` has a named disposition in the arc (strike-at-site ×2, rewrite-in-place ×2,
rewrite+annotation ×2, and C9, closed here). **Nothing entered.** The direction of the reading is
confirmed.

**Two corrections to the number, both in the direction of the audit's own findings.**

* The script's parenthetical said *"the two sites mg-069f struck are the difference"*. Five claims
  left live text between those trees, not two — C3 and C4 by strike, C6, C8 and C10 by rewrite. The
  claim-by-claim print replaces the narration; the drift never was attributable to two dispositions.
* **`LIVE 7` was itself understated by G2.** Under the bounded exemption the same ledger reports
  **LIVE 8** at `1b00147`. The extra claim is **C7** — *"over all posets on `n = 3,4,5`"*, the
  population claim mg-8a71 F2 proved false — and it was sitting in the *Machine-checked*
  sub-paragraph of the 53-line `RE-DERIVATION` block, quoting nothing, **inside the blind spot
  §4.1 names**. Verified directly by running the pre- and post-repair classifiers against the same
  tree:

  ```
  OLD (mg-069f): C7 'over all posets on' live at 1b00147 -> []
  NEW (mg-cd04): C7 'over all posets on' live at 1b00147 -> [(274, '### 2.3 …')]
  ```

  So G2 was not merely demonstrable by mutation. **It was concealing a real ledger claim at the
  arc's own demonstration commit**, which is a stronger statement than the audit made and one it
  could not have made with the instrument it had.

---

## 5. Exit codes, predicted before running

| # | run | predicted | actual |
|---|---|---|---|
| E1 | live-claim control at HEAD, after the G2 tightening | 0 (no new live site) | **0** |
| E2 | ledger at HEAD, before removing C9 from the baseline | 1 (baseline site disappeared) | **1** |
| E3 | ledger at HEAD, after re-baselining | 0 | **0** |
| E4 | declared-strike control at HEAD | 0 (2 baselined) | **0** |
| E5 | declared-strike control `--demonstrate bb1cb9b` | finds the G1 site | **found, and only it** |

Also re-run green, unchanged by this work: the mg-0242 population census (the live-claim control's
line count is still 539, so G3's `537` gap is untouched and still baselined — true as written here;
**mg-1d03 closed both G3 gaps on 2026-08-05 and the census baseline is now empty**) and the mg-3934 CI
history-depth static control — the new script names no pinned revision on its default path, taking
both history-reading modes from `argv`, which is the discipline mg-3934's control enforces and which
caught an earlier instrument in this same family.

---

## 6. What this repair did not do

* It did **not** touch **G3** or **G4**. Both remain open, both are held by a control baseline, and
  neither is in mg-cd04's scope.
* It did **not** re-open **C5**. mg-069f's handling — flag, route, decline to reverse an adjudication
  — is correct, mg-0242 confirmed it, and nothing here changes it. It is the ledger's one live entry.
* It did **not** rewrite mg-0242's findings. A disposition block was appended to its §2; the finding
  text, severities, predictions and misses stand as filed.
* It did **not** widen the live-claim control's *signature* population to the corpus. mg-0242
  measured that at ~94% false positive and decided against it; that decision stands. Only the
  structural check is corpus-wide.
* It did **not** re-open any mathematics. Nothing here touches a poset, an identity or a closed form.

---

*Deliverable for mg-cd04, closing mg-0242 findings G1 and G2. Instruments:
`scripts/onethird_mgcd04_declared_strike_control.py` (new, in CI, demonstrated against `bb1cb9b`),
`scripts/onethird_mg8a71_live_claim_control.py` (EXEMPT-block tightening),
`scripts/onethird_mg0242_struck_vs_refuted.py` (re-baselined; mutants promoted to assertions; drift
computed rather than narrated). 5 exit codes predicted before running, 5 hit.*
