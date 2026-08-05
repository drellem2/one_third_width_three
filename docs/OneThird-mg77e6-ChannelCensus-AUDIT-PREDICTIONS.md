# mg-77e6 PREDICTIONS — written before any line of this audit's code exists

**Committed before `scripts/onethird_mg77e6_sixteenth_channel_probe.py` exists and before any
mutant control is written.** Kept verbatim afterwards, misses included.

**This audit was filed LATE** — after mg-9d7b merged (`mr-d9png12tjv1h244d8420`, branch
`polecat-o9d7b`, commits `6e7c27b` / `c08d044` / `99f3f16`), not in the same action as its parent.
That is stated here rather than backdated. The practical consequence: mg-9d7b's author could not
have known these predictions existed, so nothing here is a target they were writing against — but
equally, I read their finished work before writing this file, which is the weaker position. Every
row is tagged accordingly.

* **[post]** — already observed before this file was written. Recorded so the audit can be checked
  against it, not offered as a forecast.
* **[fwd]** — **not** run. The probe does not exist yet, so no measurement of it can.

The rows that carry weight are the **[fwd]** ones.

---

## 0. What I have already done, before predicting

Read in full: `docs/OneThird-mg9d7b-ExemptionChannels-PREDICTIONS.md`,
`docs/OneThird-mg9d7b-ExemptionChannels-Repair.md`,
`scripts/onethird_mg9d7b_exemption_channel_census.py` (all 439 lines), and grepped the two
controls' coverage/bucket plumbing. Ran the census twice.

| # | | observed | tag |
|---|---|---|---|
| O1 | census at HEAD | **exit 0**, 15 declared channels, 539 + 101 790 lines classified, 0 violations | **[post]** |
| O2 | census `--selftest` | 4 of 4 CAUGHT, exit 0 | **[post]** |

---

## 1. The question this audit was filed to answer

mg-9d7b's E13 predicted against itself that the census *"will find at least one channel I did not
think of"*, and its report records **MISSED — it found none**, concluding the enumeration is
*"a complete restatement of a careful reading rather than a discovery."*

A negative needs an instrument that COULD have shown the positive. So: **build a sixteenth channel
and see whether the census catches it.**

---

## 2. The mechanism I expect to govern the answer — [post], from reading, not running

The census has two halves it calls mechanical (bucket names, attribution) and two it applies only
to channels the author already declared (bound-exists, reported). Reading `audit()`:

* halves (3) and (4) iterate `CHANNELS` — an author-supplied list. An undeclared channel is never
  reached by them at all.
* half (1) fires only on a **new coverage bucket name**.
* half (2) fires only inside `NON_CHECKING`, which is `{exempt_annotation}` for the live-claim
  control and `{fenced_code}` for the declared-strike control.

`blank` is a declared bucket in **both** controls and is in `NON_CHECKING` for **neither**.

So my structural prediction, on which everything below rests:

> **The census's detection class is exactly: channels whose lines land in `exempt_annotation` or
> `fenced_code`, plus channels that invent a new bucket name. Everything else is invisible to its
> mechanical half and reachable only by the author's declaration.**

---

## 3. The sixteenth channels I will build — the rows that count

Each mutant is a real edit to a real control that really removes text from checking. Each is run
through the census's own unmodified `observe()` + `audit()`.

| # | sixteenth channel | prediction | tag |
|---|---|---|---|
| **X1** | **text-level redaction** — live-claim strips a new `%%…%%` span from every checked unit before signatures see it. A5's own class, at any length, printing nothing | **NOT CAUGHT** — census exits 0 and prints "no channel is both unbounded and silent" | **[fwd]** |
| **X2** | **fold into `blank`** — live-claim classifies a marked line into the existing `blank` bucket and skips it | **NOT CAUGHT**. `blank` is familiar (half 1 silent) and outside `NON_CHECKING` (half 2 silent) | **[fwd]** |
| **X3** | **population narrowing** — declared-strike skips whole documents; their lines never enter coverage | **NOT CAUGHT** — a line that never enters is in no bucket | **[fwd]** |
| **X4** | *(positive control)* **new bucket name** — the skip gets its own bucket | **CAUGHT**, by half (1) | **[fwd]** |
| **X5** | *(positive control)* **silent growth of `exempt_annotation`** — extra lines exempted with no channel counter incremented | **CAUGHT**, by half (2), as "unattributed" | **[fwd]** |

**X6 — the arithmetic.** Of the five, **3 MISSED and 2 CAUGHT**. **[fwd]**

**X7 — reach is real, not cosmetic.** For X1 and X2 I will plant a live claim that the unmutated
control CATCHES and the mutated one does not, so the channel is demonstrably a route out of the
check and not a bookkeeping curiosity. Predicted: hits drop, census still exits 0. **[fwd]**

---

## 4. The decisive test — could the census have found the report's own two discoveries?

The report names **A5** and **A8** as the two channels *"on nobody's list"*. If the census's
mechanical half could not have found them either, then they were found by reading, and E13's miss
is a property of the instrument rather than evidence about the world.

Simulate the author who never noticed a channel by **deleting that channel's row from `CHANNELS`**
and re-running against the unmodified controls at HEAD.

| # | prediction | tag |
|---|---|---|
| **D1** | Deleting **A5** → census still **PASSES**. Deleting **A8** → still **PASSES**. Both of the report's discoveries are undiscoverable by its own instrument | **[fwd]** |
| **D2** | Across all 15 rows deleted one at a time: **4 CAUGHT** (A1, A2, A4, B1 — the four whose lines land in a `NON_CHECKING` bucket) and **11 NOT CAUGHT** | **[fwd]** |
| **D3** | Therefore the census's retrospective discovery power over its own declared set is **4/15**, and the two rows the report calls discoveries are both in the 11 | **[fwd]** |

---

## 5. Claims in the deliverable I expect to be wrong

| # | prediction | tag |
|---|---|---|
| **C1** | Report §5: *"`--selftest` builds four broken controls, one per half of the invariant"*. **FALSE as written** — `selftest()` builds four hand-authored `observed` dicts and `_stub()` attribute-bags. No control source is constructed, loaded, or executed. The census docstring says the same thing ("builds a control with an undeclared skip bucket") and is wrong the same way | **[fwd]** (read, not yet confirmed line-by-line) |
| **C2** | The consequence of C1, which is the substantive part: **no selftest case exercises the path from a real control's code to the observed side.** The selftest proves `audit()` reacts to bad *inputs*; it does not probe whether a real channel *produces* those inputs. X1–X3 are predicted to be exactly the gap | **[fwd]** |
| **C3** | The printed count **"15 declared channels"** is `len(CHANNELS)` — **FORCED** by an author-supplied literal. No input to either control moves it. Predicted: neither the census's output nor the report labels it FORCED or names the forcing | **[fwd]** |
| **C4** | Neither the report nor the census states the census's **detection class** (§2 above) anywhere. Predicted: `grep` finds no statement that the mechanical half is confined to `exempt_annotation` / `fenced_code` / new-bucket | **[fwd]** |
| **C5** | **B5's row name is not its measurement.** `BASELINE` is declared `BOUNDED` with bound identifier `BASELINE` — but `BASELINE` is a *list of tolerated sites*, not a bound on any channel's reach. The bound-exists half is satisfied by `hasattr`, which a list of any length satisfies. Predicted: appending a site to `BASELINE` grows the channel without limit and the census stays green | **[fwd]** |

---

## 6. Where I expect the deliverable to hold up

Stated in advance so this audit is not a list built to be long.

| # | prediction | tag |
|---|---|---|
| **H1** | E1 (a bound of 12 does not close M4) is **correct and correctly the interesting one**. Predicted: the 10/11/12/13 sweep reproduces | **[fwd]** |
| **H2** | The report's reach column carries an explicit *"deliberately approximate, recomputed on every run"* caveat, and that caveat **matches its hypothesis** — the numbers have already drifted (report: 581 regions / 4 359 lines; HEAD: 4 372 lines) and the caveat covers exactly that | **[post]** |
| **H3** | §7.1's claim that both mg-9d7b deliverables use the fence channel **0 times** reproduces | **[fwd]** |
| **H4** | §8 "what I did not do" is **honest** — no item on it turns out to have been quietly done | **[fwd]** |
| **H5** | The report's own reading of E13 (*"reported as a weak one"*, *"value is prospective, not retrospective"*) is **not an over-claim**. My finding is predicted to be that it under-explains rather than over-claims: it attributes the miss to its reading being complete when the instrument's blindness is the available explanation | **[fwd]** |

---

## 7. CORRECTING THE TICKET'S FRAMING — asked for, so answered in advance

The brief says the verdict claims E13 found no channel its own reading missed, and asks whether an
instrument that could show the positive exists. Two ways I expect the framing to need correction:

* **The report does not hide the negative — it flags it itself**, in bold, as its most interesting
  result, and says the enumeration is a restatement rather than a discovery. The standing target
  "NEGATIVES REQUIRE THEIR CANDIDATE SPACE" is predicted to land not as *unaudited honesty* but as
  *honest about the wrong thing*: the candidate space that is missing is not the channels, it is
  the **classes of channel the instrument can see**. **[fwd]**
* **"MATERIAL BEYOND THE BRIEF — look there first"** is predicted **NOT** to be where the worst
  finding is this time. mg-9d7b's out-of-brief material (the `mg0242` consumer repair, the mg-9a19
  re-recording, the CI wiring) is all disclosed in §7 and E9. Predicted: the worst finding is in
  the instrument's *core*, not its margins — which would make the standing hypothesis wrong here,
  and I will say so. **[fwd]**

---

## 8. What I already know I am not doing

* **I am not re-doing mg-9d7b.** Only what landed is audited.
* **I am not proposing to widen the census's detection class.** Naming the class is the finding;
  building the wider instrument is a different ticket.
* **No mathematics.** No claim in the ledger is re-opened.
* **I am not auditing mg-9a19 or mg-cd04** except where mg-9d7b's claims about them are checkable.
* **I am not touching either control's behaviour on the corpus.** Mutants live in temp files.

---

*Written for mg-77e6 before the probe existed. `git log` is the witness: this file is committed in
its own commit, ahead of every line of audit code.*
