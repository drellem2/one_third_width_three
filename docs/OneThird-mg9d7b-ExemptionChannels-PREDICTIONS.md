# mg-9d7b PREDICTIONS — written before any line of this repair exists

**Committed before `scripts/onethird_mg9d7b_exemption_channel_census.py` exists and before any edit
to either control.** Kept verbatim afterwards, misses included.

## What is already measured, and what is not

mg-9a19 is an audit I read in full before writing this, and I ran two probe scripts against the two
controls before writing it. **Predictions made after measurement are weak** — mg-9a19 said so about
its own 19/19 and was right — so every row below is tagged:

* **[post]** — I have already observed this number. It is recorded so the repair can be checked
  against it, not offered as a forecast.
* **[fwd]** — I have **not** run this. The repair does not exist yet, so no measurement of it can.

The rows that carry any weight are the **[fwd]** ones.

---

## A. The enumeration itself

| # | | prediction | tag |
|---|---|---|---|
| **N1** | channels in `onethird_mg8a71_live_claim_control.py` by which text leaves unchecked | **8**, of which exactly **1** (A2) is today unbounded *and* silent | **[fwd]** |
| **N2** | channels in `onethird_mgcd04_declared_strike_control.py` | **7**, of which exactly **2** (B1 closed fences, B2 unclosed fences) are today unbounded *and* silent | **[fwd]** |
| **N3** | channels neither mg-9a19 nor the ticket names, found by this enumeration | **≥ 2** | **[fwd]** |

N3 is the one that decides whether this ticket was worth filing as a CLASS. If the enumeration
turns up nothing past H1/H2/H3/H4, then "enumerate every channel" was a longer way of saying "fix
the two findings" and I should say so.

**Named in advance, so the count cannot be padded afterwards.** The two I expect to be new are:

* **A5 — the inline `~~struck~~` strip.** `INLINE_STRIKE.sub(" ", text)` removes text from *every*
  checked unit — paragraphs, headings and STRIKE blocks alike — before the signatures see it. It is
  an exemption channel with no bound and no number attached, and it is on nobody's list.
* **A8 — label detection vs label exemption.** The marker is looked for in `block[:3]`; the
  exemption is granted to **sub-paragraph 0**. Those are not the same span. When they differ,
  sub-paragraph 0 is exempt while carrying no label.

---

## B. Reach at HEAD, before the repair

| # | | prediction | tag |
|---|---|---|---|
| R1 | A1 label-exempt lines / allowance | 4 used of 24 (4 blocks × `MAX_LABEL_LINES` 6) | **[post]** |
| R2 | A2 quotation-exempt lines | **66** over **9** sub-paragraphs, longest **11** | **[post]** |
| R3 | A5 inline-strike spans in the audited document | 3 spans, 466 chars, longest 314, 1 crossing a newline | **[post]** |
| R4 | A8 label/exemption mismatches at HEAD | **0** | **[post]** |
| R5 | B1 fenced regions corpus-wide | 582 regions, 4 359 lines of 101 257 (4.30%), longest 195 | **[post]** |
| R6 | B2 unclosed fences corpus-wide | **1** — `OneThird-AP-2-Prong3I-beta-RungUniqueness-SD-FLOOR.md:138`, reaching 2 lines to EOF | **[post]** |
| R7 | B3 sentences that declare + quote but are exempted by a `~~` elsewhere in their block | **1** | **[post]** |
| R8 | B6 documents in the `docs/` tree not read by the glob | **14** (244 read of 258) | **[post]** |

R5/R6/R8 differ from mg-9a19's figures (582 vs its 4 302 lines, 244 vs 242 documents) because the
corpus grew between `f6e329c` and here. **Predicted: the difference is documents added, not a
measurement disagreement** — **[fwd]**, and if the per-document numbers disagree at `f6e329c` then
one of the two instruments is wrong and that is a finding.

---

## C. The repair's behaviour — the rows that count

| # | prediction | tag |
|---|---|---|
| **E1** | Bounding A2 at `MAX_QUOTED_LINES = 12` **does NOT catch M4.** M4 appends one line to the 11-line sub-paragraph, giving 12, which is inside a bound of 12. A bound with headroom does not close this. | **[fwd]** |
| **E2** | `MAX_QUOTED_LINES = 11` — the measured reach exactly, no headroom — **does** catch M4 (exit 1), and leaves HEAD at exit 0. | **[fwd]** |
| **E3** | Exempting only the lines a QUOTATION physically touches (line granularity instead of a length bound) **produces a false positive at HEAD** — the docstring says hard-wrapping interleaves quotation and commentary, and it is right. | **[post]** — I tried it; it fires `S2-hinges-on-degree` at line 502. Recorded because it is the design I would otherwise have shipped. |
| **E4** | After the A2 bound lands, HEAD stays **exit 0** on the live-claim control, with **0** hits. | **[fwd]** |
| **E5** | A block-level `MAX_EXEMPT_LINES` — the identifier the docstring names twice and the repository does not define — can be given a real value without changing HEAD's verdict. Largest per-block exempt total at HEAD predicted **33** of a 44-line block. | **[fwd]** |
| **E6** | Treating an unclosed fence as **not a fence** (check the remainder, report the site) leaves the declared-strike control at **exit 0** on HEAD, and moves exactly **2** lines from `fenced_code` to `block`. | **[fwd]** |
| **E7** | M8 (declared strike under an unclosed fence) moves **0 → 1**, caught. | **[fwd]** |
| **E8** | M9 (declared strike in a block holding an unrelated `~~`) stays **0**. I intend to *report* B3, not fail on it: the one site at HEAD is the mg-9a19 audit quoting the rule, and failing there buys a new tolerance to close a LOW finding. | **[fwd]** |
| **E9** | `scripts/onethird_mg9a19_exemption_population_audit.py` **fails** the moment E2 and E7 land, because its `RECORDED` table pins M4 and M8 at 0 and fires on movement in either direction. That is the handshake working, not a regression. It has to be re-recorded deliberately, in this commit, with the old values kept visible. | **[fwd]** |
| **E10** | Printing every channel's reach costs the two controls **no** change of exit code anywhere: HEAD 0/0, `1b00147^` 1, `1b00147` 1, `--demonstrate bb1cb9b` 0. | **[fwd]** |

---

## D. The invariant this repair is really about

**No channel may be both unbounded and silent.** Bounded-and-silent is fine (the bound is the
statement). Unbounded-and-reported is fine — the ticket says so. Unbounded-and-silent is the defect,
and it is the one thing the new instrument will assert.

| # | prediction | tag |
|---|---|---|
| **E11** | Under that invariant, **3** channels are in violation before this repair: A2, B1, B2. | **[fwd]** |
| **E12** | After it, **0** — A2 bounded, B2 no longer a channel at all, B1 unbounded **by design** and printing its own 4.3%. | **[fwd]** |
| **E13** | The invariant, asserted as code, will find at least one channel I did not think of when I wrote this file. | **[fwd]** |

E13 is a prediction against myself. If it misses — if the census finds exactly the channels named
here and no others — then the enumeration was a restatement of my own reading and I will say so in
the report rather than presenting a clean sweep as a strong result.

---

## E. What I already know I am not doing

* **H4 (the non-recursive glob).** 14 documents in the `docs/` tree are never read. I will **print**
  that, not fix it: widening the population is G3's subject, mg-9a19 filed H4 separately for exactly
  that reason, and mg-9a19 already swept the unread part and found it clean. Predicted still clean —
  **[fwd]**.
* **G3 and G4**, still open from mg-cd04.
* **Any mathematics.** No claim in the ledger is re-opened.
* **`scripts/*.py`**, which no control reads and which mg-9a19 §3.1 showed trips the declared-strike
  rule four times, twice in the module that defines it. Out of scope here and left as filed.

---

*Written for mg-9d7b before the repair existed. `git log` is the witness: this file is committed in
its own commit, ahead of every script and every edit to either control.*
