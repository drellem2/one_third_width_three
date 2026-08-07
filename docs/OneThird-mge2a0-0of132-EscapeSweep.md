# mg-e2a0 — the `0/132` in `one_third_width_three`: escape sweep, classification, and landing

**Work item.** `mg-e2a0` (repo `one_third_width_three`). Carrier for the half of `aeba7`'s audit
that exceeded `mg-55f2`'s ticket boundary.
**Lands.** `mg-55f2`'s ruling (on `mg-65f5` §1.5) **at its destination**. `onethird_program/STATE.md`
row 3b is already correct and is **not touched here**.
**Does not re-derive.** The sampling-artifact analysis is `mg-65f5` §1.5; the ruling is `mg-55f2`;
the ledger is `STATE.md` row 3b. This document sweeps, classifies, and repairs — nothing more.

---

## 0. The defect, in one line

`STATE.md` row 3b was corrected to say **`0/132` is a sampling artifact and is never quotable
bare** — and then cited, as its source, a document in *this* repo where the figure was still
quotable bare. **We corrected the pointer and left the target.** Four sweeps ran on this corpus
tonight (`mg-372e`, `mg-910c`, `mg-24fb`, `mg-4417`) and every one was scoped to `onethird_program`,
which is exactly how the destination stayed uncorrected.

---

## 1. WHAT THE COUNT IS A COUNT OF — read this before the numbers

A bare count here would be the defect reproducing itself, so:

**Population swept.** All **635 tracked files** in `one_third_width_three` (`git ls-files`, every
extension present: `.md .tex .py .json .yml .txt .sh .toml .lean .pdf` + `LICENSE`). Not `docs/`
only, not `.md` only.

**Claim swept — the claim, not one spelling.** The `mg-b0a6` kill-shot-2 aggregate *"zero
standard-dominance failures over 132 posets"* **and its "clean sweep" framing**, in:

| form | swept as |
|---|---|
| the figure | `0/132`, `0 / 132`, `0 of 132` |
| the bare integer | `132` (every occurrence, then collision-checked one by one) |
| the framing | `clean sweep` (case-insensitive) |
| prose forms, no digits | `0 failures`, `standard dominance` + `universal`/`holds`/`GREEN`, `no counterexamples`, `zero counterexamples`, `counterexample-free`, `airtight` |
| the machine record | the `summary` block of `data/onethird-mgb0a6-spectral-killshot.json`, which carries the claim with **no `132` in it at all** (`standard_dominance_failures: 0`, `standard_dominance_tested: 126`) |

**Rendered artifacts checked.** No `.html` exists in this repo. All 8 `.tex` files have **zero**
hits on every figure spelling, so `main.pdf` and `summary.pdf` cannot carry it. There is no
rendered twin. (`mg-372e`'s corpus had one; this one does not.)

---

## 2. THE COUNT

### 2.1 The number that is *not* the answer, stated so nobody quotes it

**Bare integer `132`: 1,394 occurrences.** **1,341** of those are in `data/*.json`. **Every one of
the 1,380 non-figure hits is a COLLISION** — `|L| = 132` for `enum-n7-#600`, `num_LE: 132`, float
digit-strings (`9.132`, `0.13218…`, `0.99716…3132`), canon ids (`"201602132"`), page ranges
(`1299–1327`), path fragments (`union_closed_1323_proof_steps.txt`, ×11), and source line refs
(`:132`, `step7.tex:1302-1325`, `G1G2Grounded.lean:132`). **`1,394` is the count of a string. It is
not the count of anything true.** A bare integer is exactly the shape most prone to collision, and
this figure *is* a bare integer — which is why every hit was checked individually rather than
blanket-edited.

### 2.2 The figure and its framing

|  | found | LIVE | repaired | left, with reason |
|---|---|---|---|---|
| **the figure** (`0/132` / `0 / 132` / `0 of 132`) | **14** in 4 docs | **2** | **2** | 12 (**4** CITED, **8** DERIVED) |
| **"clean sweep"** | **8** (on 7 lines, 5 files) | **0** | 0 | 8 (1 CITED, 2 DERIVED, **5 COLLISION**) |
| **prose form, no digits** | **6**, all in `KillShot-Probe.md` | **3** | **3** | 3 (1 examined-and-left, 2 covered by the section repair) |
| **the machine record** | **1** (`…killshot.json` `summary`) | 0 | 0 | 1 — self-framing, correct, and it *sharpens* the repair (§4) |
| **bare integer `132`** | **1,394** | 0 | 0 | 1,380 COLLISION + the 14 above |

**Totals: found 29 in-scope occurrences of the claim / LIVE 5 / repaired 5 / left-with-reason 24.**
Plus one document-level banner and one owed-correction discharge (§3.1, §3.2).

---

## 3. THE CLASSIFICATION, occurrence by occurrence

`mg-372e`'s four classes, which earned their keep. **LIVE** = asserted bare, strike in place with
the condition beside it. **CITED** = named as the superseded/conditional figure, leave. **DERIVED**
= inside an argument about it, leave. **COLLISION** = `132` meaning something else, leave and say so.

### 3.1 LIVE — 5 sites, all repaired

**`docs/OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md`** — *this is the destination
`STATE.md` row 3b names, and it carried no correction of any kind before this ticket.*

| site | what was asserted | repair |
|---|---|---|
| `:249` → now `:303` | *"standard dominance is **universal**"* | **The sharpest one in the corpus.** It states as a property of **posets** what was measured only inside the frame. Struck; replaced with the in-frame reading + the refutation of the unconditional form. This is the exact sentence `Reverse-Cheeger:310–313` quotes back at this kill-shot — the correction was written down elsewhere and never arrived here. |
| `:286` → now `:345` | `0 / 132` aggregate row | Row label already carried the frame; the frame's **consequence** was nowhere. Struck with the condition, plus the new `126 + 6` finding (§4). |
| `:20` → now `:63` | kill-shot 2 verdict **GREEN**, bare | Struck → **GREEN-IN-FRAME ONLY**, with the refuted-unconditional / open-conditional split. |
| `:103` → now `:146` | section heading **GREEN**, bare | Struck → **GREEN-IN-FRAME ONLY** + pointer to the banner. |

**`docs/OneThird-StandardDominance-ComparisonRoute.md`**

| site | what was asserted | repair |
|---|---|---|
| `:104` | *"Empirically supported, **0/132** (`mgb0a6`)"* in the SD-Cayley status row | Bare figure in a status table — the single most quotable position in the document. Struck with the frame attached. **Kept honest in both directions:** the 166 refuters are BK-side, so by this document's own §1.1 they refute **SD-BK, not SD-Cayley**. SD-Cayley is *not* refuted here; what is withdrawn is the figure's **strength**, which is `mgb0a6`'s frame under either reading. |

**Plus, not a fifth LIVE site but the load-bearing part of the landing:** a **scope-correction
banner** at the head of `KillShot-Probe.md`, above the executive verdict, so a reader arriving from
`STATE.md` row 3b meets the condition before any verdict.

### 3.2 CITED — 5 occurrences at 3 sites, left

- `ComparisonRoute:110` — quotes the ticket's *"empirically airtight (0/132 counterexamples)"* **in
  order to refute it**. Correct as written.
- `mg65f5-ThreeFollowups:119–120` — quotes `mg-957a`'s escaped *"a clean sweep like row 3b's
  `0/132`"* **in order to strike it** (3 occurrences: the figure at `:119` and `:120`, the framing
  at `:120`). Correct as written.
- `mg2c34-n7-Overlap-Test:775` — names *"the `0/132` is Cayley-walk evidence" catch* as an
  established finding. Correct as written.

**None of these licenses a refuted direction** (`pm-onethird`'s sharpening: a citation that
*licenses* a refuted direction is not safely left as a citation). Each cites the figure precisely to
withdraw or bound it.

### 3.3 DERIVED — 10 occurrences (8 of the figure + 2 of the framing), left

- `ComparisonRoute:108` (§1.1 heading), `:111`, `:653` — §1.1 **is** the argument about the figure.
- `mg65f5-ThreeFollowups:33`, `:34`, `:120` (*"It is not a clean sweep"* — the verdict, not the
  quote), `:123`, `:130`, `:133`, `:337` — §1.5 **is** the finding: its
  abstract, its two sources, its conclusion, its evidence bound. Editing these would fix a document
  into disagreeing with its own subject.

`ComparisonRoute:653` additionally listed the correction as **owed** to `KillShot-Probe.md` and
never landed. It is now marked **✅ DISCHARGED (mg-e2a0)** in place — that correction had been
outstanding since `mg-4a86`.

### 3.4 COLLISION — 1,380 bare-`132` + 5 "clean sweep", left, and named

Bare `132`: as itemized in §2.1. The five "clean sweep" collisions are
`mg77e6-ChannelCensus-IndependentAudit:208`, `mg9d7b-ExemptionChannels-Repair:235`,
`mg9d7b-ExemptionChannels-PREDICTIONS:94`, and `scripts/onethird_mga266_split_phrase_control.py:39`
and `:807` — all about the **exemption-channel census** (*"present a clean sweep as strong"*), a
different subject with no relation to row 3b. The script's two are literal test fixtures for a
split-phrase grep control.

### 3.5 An escape that did NOT happen, reported because absence is a finding too

**`mg-957a`'s escaped phrase *"a clean sweep like row 3b's `0/132`"* does not exist in this repo**
outside `mg-65f5`'s own quotation of it. It travelled within `onethird_program` and was struck
there (`mg-55f2`, `STATE.md` row 10). The thing that escaped *here* was the **figure**, not the
phrase — and it escaped by being the figure's **source**, which is a different and worse escape
route than propagation: nobody copied it here, it was here first, and the correction went to the
copies.

---

## 4. ONE NEW MEASUREMENT, made on the way and in scope

Checking the figure against the data appendix this document publishes:

```
data/onethird-mgb0a6-spectral-killshot.json
  summary.standard_dominance_tested   = 126
  summary.standard_dominance_failures = 0
  rows: 126 entries — n=6:104, n=5:15, n=4:5, n=3:2      (no n=7 row exists)
```

So **`132 = 126 + 6`**, and **the 6 `n = 7` spot-check posets are not in the published data at
all** — the appendix heading itself says *"Full 126-poset table"*. The off-exhaustive sixth of the
denominator, which is precisely the part the moderate-λ `n = 7` refuters sit adjacent to, **is the
part a third party cannot re-check**. A verifier who goes to the data bottoms out at `0 / 126`.

This is a reading of the shipped artifact, not a re-derivation of `mg-65f5`'s analysis, and it is
recorded at `:286` and in the banner.

---

## 5. THE ADJACENT ITEM — read and decided, not assumed

`aeba7` reported without scoring it: *`KillShot-Probe.md` carries `standard dominance | holds` at
`:198` and GREEN at `:20` and `:103`, with the frame declared 88 lines later at `:286`.*

**Verdict: the same defect — and `aeba7` located it imprecisely; the real one is worse. FIXED HERE.**

**Where `aeba7`'s shape is wrong as stated.** The frame is **not** first declared at `:286`. It is
declared at **`:108–111`**, in the kill-shot 2 bullets — *above* `:198`, not 88 lines below it
(*"exhaustively for all **126** both-connected posets `n≤6` … Spot-checked at `n=7` on the six
highest-λ_std both-connected posets"*). `:286`'s row label only repeats it. So the ordering claim
does not hold.

**Why the finding survives its own mislocation, larger than reported.** The frame being present is
not the point — **its consequence is declared nowhere in the document.** `:249` asserts standard
dominance *"is universal"*, bare and unconditional, and that statement is **refuted**. A frame at
`:108` and a verdict at `:20`/`:103`/`:249` that the frame does not license is *exactly* the shape
of the `0/132` finding: **a verdict legible without the condition that qualifies it.** Same defect,
same document, and it is repaired above. `aeba7` was right to flag it and right not to score it.

**`:198` specifically is NOT the same defect — left deliberately, with an in-place note.** The row
`| standard dominance | **holds** |` is a **per-poset measurement** on the N-poset (`2+2`, `n = 4`),
one line in a table of per-poset measurements, and `n = 4` is inside the **exhaustively** swept part
of the frame. The number is correct, complete, and not quotable over posets — it is not the
aggregate claim wearing a different spelling. A note now says so at the table, so the next reader
does not repeat the read.

---

## 6. Scope: what this ticket's boundary is, and where the problem exceeds it

Per the dispatch note — assume this scope is defined by what was known when it was filed.

**Inside, done:** every live occurrence of the figure and its framing in `one_third_width_three`,
across all 635 tracked files, plus the adjacent `KillShot-Probe.md` verdict-before-frame item.

**Outside, and reported rather than treated as this ticket's boundary:**

1. **The structural pattern, now three-for-three tonight.** `mg-4417` (a corrected downstream citing
   an uncorrected upstream), this ticket (a corrected ledger pointing at an uncorrected
   destination), and `ComparisonRoute:653` (a correction *recorded as owed* by `mg-4a86` and never
   landed, discharged here only because this ticket happened to pass through). **Cross-document
   corrections in this corpus routinely stop at a repo boundary, and "corrections owed" lists are
   not a delivery mechanism.** That is a process finding, not a document finding, and it has no
   carrier.
2. **`mg-4a86`'s second owed correction is still owed.** `ComparisonRoute:653` lists two; only #1
   was in this ticket's reach. #2 — `Reverse-Cheeger:273-275`, *"`λ_std ≤ λ₂^BK` (the standard
   sector is a subspace)"*, whose justification is invalid and whose inequality **fails exactly on
   the ordinal sums**, i.e. exactly in the programme's regime of interest — is **untouched**, in
   this repo, in a document that is cited by `STATE.md` row 3b. **It needs a carrier.** I did not
   fix it: it is a different claim, it is not the `0/132`, and silently widening scope is the
   failure mode this ticket exists to correct.
3. **`132` is a bare integer with 1,380 collisions in this repo alone.** Any future sweep that
   greps it without collision-checking will report a number that means nothing.

---

## 7. What I did not do

- **Did not touch `onethird_program/STATE.md`.** Row 3b is correct (`mg-55f2`, confirmed at blob
  `7f73bfc8`). Out of scope and correctly so.
- **Did not re-derive the sampling-artifact analysis**, and did not re-measure `166` or `0/132`.
  Both remain **read-not-measured**, sourced, and are labelled as such wherever this ticket restates
  them. The `126`-vs-`132` finding in §4 *is* mine and is a reading of a shipped file, not a
  re-derivation.
- **Did not delete the figure anywhere.** It is not wrong; it is a correct measurement presented as
  a sweep. Every repair attaches the condition and leaves the number.
- **Did not run the probe.** No script executed; no data file regenerated or altered.
- **Did not audit `mg-55f2` or `aeba7`.** No independent audit was commissioned, deliberately — a
  staleness sweep is a chore and the count-with-its-frame is the control.
- **Did not sweep the other repos.** `onethird_program` was swept by `mg-55f2`; whether the figure
  reached a third repo is unchecked and is item 1 of §6.
