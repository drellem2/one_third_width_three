# mg-77e6 — INDEPENDENT AUDIT of mg-9d7b: the census checks an enumeration, it does not discover one

**Target:** what mg-9d7b landed — `6e7c27b` (predictions), `c08d044` (repair), `99f3f16` (report
and CI), merged today as `mr-d9png12tjv1h244d8420` from branch `polecat-o9d7b`.

**Filed LATE**, after mg-9d7b merged, rather than in the same action as its parent. Stated here
rather than backdated. Two consequences, both real: mg-9d7b's author could not have been writing
against these predictions, and I read their finished work before writing mine — which is the weaker
position, and is why every prediction row in
`OneThird-mg77e6-ChannelCensus-AUDIT-PREDICTIONS.md` (`dc49345`, committed before any line of probe
code existed) carries a `[post]` / `[fwd]` tag.

**Instrument:** `scripts/onethird_mg77e6_sixteenth_channel_probe.py`, wired into
`script-controls.yml` with a RECORDED handshake.

---

## 0. Verdict

**The census is sound, its verdict is true, and its verdict does not support the conclusion drawn
from it.**

mg-9d7b's E13 predicted the census would find a channel its author's reading had missed. The report
records **MISSED — it found none** and reads that as *"a complete restatement of a careful reading
rather than a discovery."* That reading requires the census to be able to find an undeclared channel
at all. Six were built and run through the census's own unmodified `observe()` and `audit()`:

| | |
|---|---|
| sixteenth channels built | **6** |
| CAUGHT by the census | **2** — X4, X5 |
| MISSED | **4** — X1, X2, X3, X6 |
| of the missed, shown to be a real route out (a planted live claim disappears) | **2 of 2 tested** |
| the census's own 15 declared rows it would re-discover if undeclared | **4** — A1, A2, A4, B1 |
| would it re-discover **A5**? the report's headline discovery | **NO** |
| would it re-discover **A8**? the report's other discovery | **NO** |

**The census's mechanical half fires on exactly two things:** a coverage bucket name it was not told
about, and lines in `exempt_annotation` or `fenced_code` that no declared channel claims. Everything
else reaches only the halves that iterate the author's own `CHANNELS` list. That class is stated
nowhere in the census, the report, or the CI comment.

So the census is a **regression test on a declared enumeration** — a real and useful thing, and the
one mg-9d7b's §5 table actually describes row by row. It is **not** the discovery instrument E13 was
a prediction about, and E13's MISSED is therefore compatible with a complete reading and with an
incomplete one alike. **"I could not find a counterexample" and "there is none" are different
claims, and the census only ever supported the first.**

**Five findings. F1 is the one that matters. Two of my own predictions were wrong, and one of them
became F4.**

---

## 1. F1 (HIGH) — the census's discovery reach is 4 of its own 15 rows, and it is stated nowhere

**The test.** Simulate an author who never noticed a channel: delete that channel's row from
`CHANNELS` and re-audit the **unmodified** controls at HEAD. If the census still passes, that row is
in the census because its author read it off the source — nothing mechanical would have raised it.

| | rows | verdict |
|---|---|---|
| re-discovered | **A1, A2, A4, B1** | the declaration was not load-bearing |
| declaration-only | **A3, A5, A6, A7, A8, B2, B3, B4, B5, B6, B7** | in the census by reading alone |

**Population and grain:** the population is the census's own 15 declared channels; the grain is one
deletion per row, verdict = does `audit()` return ≥ 1 violation against unmodified HEAD controls.

The four it re-discovers are exactly the four whose lines land in a `NON_CHECKING` bucket
(`exempt_annotation`, `fenced_code`), where the attribution half runs. Nothing else is reachable.

**This is generous to the census.** The sweep deletes the census's *declaration* but leaves each
control's own `A1_label` / `A2_quoted` / `B1_fenced_lines` counters in place — instrumentation
mg-9d7b itself added. A genuine never-noticed channel would have neither. 4/15 is an **upper
bound**.

**Why it is HIGH rather than a curiosity: the two channels the report presents as discoveries are
both in the 11.** §1.3 says of A5 *"no run had ever printed a number for it. It is on nobody's
list"*, and both A5 and A8 were named in advance in the predictions file — by reading. The census
would not have raised either. The report's own framing (§5) is that the census *"cannot be satisfied
by a channel the author forgot, because the author does not supply the observed side."* That is true
of the bucket-name half and false of the deliverable as a whole: for 11 of 15 rows the author
supplies both sides.

---

## 2. F2 (HIGH) — three sixteenth channels, all real, none caught

Each mutant is a real edit to a real control, exercised by the corpus the control actually reads,
and judged by the census's own `audit()`.

| | the sixteenth channel | exercised | census |
|---|---|---|---|
| **X1** | **text-level redaction** — live-claim strips inline `` `code` `` spans from every checked unit before the signatures see it. **A5's own class** | the corpus is saturated with inline code; `m_x` in backticks is a component of 3 of the 4 signatures | **MISSED** |
| **X2** | **fold into `blank`** — 17 list-item lines skipped and booked to a bucket that already exists | 17 `- ` lines | **MISSED** |
| **X3** | **population narrowing** — whole documents dropped after `names` is built, so B6's own read/in-tree figures are untouched | every `L1b` document | **MISSED** |
| **X4** | *(positive control)* fenced code skipped into a **new** bucket `lc_fenced` | 11 lines | **CAUGHT** |
| **X5** | *(positive control)* `exempt_annotation` grows with no channel counter | 59 lines | **CAUGHT** |
| **X6** | a **dormant** new bucket — X4's kind, keyed on a marker today's corpus never triggers | 0 lines | **MISSED** |

**The misses are real routes out, not bookkeeping.** A planted sentence tripping
`S2-hinges-on-degree` — a signature the control really carries — scores **1 hit under the pristine
control and 0 under the mutant**, for both X1 and X2. A live claim leaves the check and the census
says *"no channel is both unbounded and silent."*

**Why they are invisible.** X1 removes no *lines* — the unit is still yielded, only its content
shrinks — so no bucket moves. X2 moves lines into `blank`, which is a declared bucket in both
controls and is in `NON_CHECKING` for neither. X3's lines never enter a bucket at all. The census
docstring's promise that *"a skip that is quietly folded into an existing bucket fails here even
though the bucket name is familiar"* holds for `exempt_annotation` and `fenced_code` and **fails for
`blank`, `paragraph`, `quote`, `heading` and `block`** — and `blank` is both familiar and
non-checking, which is precisely the gap.

---

## 3. F3 (MEDIUM) — `--selftest` builds no controls; it hand-feeds the observed side

Report §5: *"`--selftest` builds four broken controls, one per half of the invariant: **4 of 4
rejected**."* The census docstring says the same: *"`--selftest` builds a control with an undeclared
skip bucket."* The CI comment repeats it.

`selftest()` (census lines 305–366) constructs four `observed` dictionaries by hand and two
`_stub()` attribute-bags. **No control source is constructed, loaded, or executed anywhere in it** —
a grep of the function for any load or scan call returns zero.

**The substantive consequence, not the wording.** Every selftest case supplies the observed side
directly, so it tests that `audit()` reacts to bad *inputs*. Nothing tests whether a real channel
*produces* those inputs. That gap is exactly where F2 lives: X1, X2, X3 and X6 are real channels
that never generate the observations the selftest hands over. An instrument whose can-it-fail
demonstration skips the code-to-observation path cannot show that it fails on code.

This is the same shape as the defect mg-9d7b was sent to repair — a name (`MAX_EXEMPT_LINES`,
"builds four broken controls") that the code does not carry — reproduced in the sentence that
certifies the instrument. **Eighth consecutive generation.** mg-9d7b's §7 counted itself as the
seventh and recorded three of its own defects; this is a fourth, in the certification rather than in
the mechanism.

---

## 4. F4 (MEDIUM) — a channel today's corpus does not exercise is invisible even inside the visible class

**This finding is my own prediction miss, promoted.** My first X4 keyed its new bucket on a
`<!--nocheck` marker. It came back MISSED and I recorded a wrong prediction — the marker appears
nowhere in `docs/OneThird-L1b-Spread-Locality.md`, so the branch never ran and no bucket was ever
created. I rebuilt X4 on fence lines (exercised, CAUGHT, prediction restored) and kept the dormant
version as **X6**, because the accident is a finding:

> The census reads **buckets that were populated**, not **branches that exist**. A skip written into
> a control today and triggered by a document added next month is invisible until the day it fires —
> at which point the census fails and blames the document.

That is the one class where the census's *strongest* half is nonetheless blind, and it makes the
census's reach a function of the corpus as well as of the code. It also caught three of my own first
mutants, which is the same error in the auditor: a MISSED from a branch that never ran is a result
about the probe, not about the census. Recorded at the site in the probe source.

---

## 5. F5 (LOW) — B5's row name is not its measurement, and the census does not read exit codes

**(a) `BASELINE` is declared a bound and is not one.** B5 is `BOUNDED` with bound identifier
`BASELINE`. The bound-exists half is `hasattr(mod, bound)`, which a set of **any** size satisfies.
Grown from 2 sites to 4 in-process, the census stays green. `BASELINE` is a *tolerance list*, not a
bound on any channel's reach — the row name is not what the check measures, which is this arc's most
repeated defect. (The declared-strike control does fail on baseline *drift* independently, so the
tolerance is not unwatched; it is just not watched by the row that claims to watch it.)

**(b) The census never consults the exit code of the controls it audits.** `observe()` swallows
`SystemExit`. A control mutated to `sys.exit(1)` on its own run, buckets untouched, yields **0**
census violations. The census's PASS is compatible with the control it audits being RED. Not a
channel, and not wrong — the census is about invisibility, not about verdicts — but *"every
exemption channel in both controls is bounded or reports its own reach"* is printed by a step that
did not notice the control failed.

**(c) `len(CHANNELS)` is FORCED and is not labelled so.** The census prints *"population: 15
declared channels"*. No input to either control moves it; only editing the census does. The standing
convention in this arc is that a count which cannot move must say FORCED and name the forcing.
Neither the census output nor the report does. It is also the census's *own population*, which is
the same fact as F1 stated as a number.

---

## 6. What the deliverable got right, checked rather than granted

Stated because an audit that only lists faults is not measuring.

| | claim | checked |
|---|---|---|
| **E1** | a `MAX_QUOTED_LINES` of 12 does **not** close M4; 11, the measured reach, does | **HOLDS.** Sweep reproduced against mg-9a19's *own* `MUTANT_SENTENCE`: caps 10 and 11 catch, 12 and 13 miss, HEAD scores 0 at every cap. *(Grain: the report's M4 column is the control's exit code; mine is the hit count, 2, because that sentence trips S1 and S2. They agree in sign at every cap, which is what E1 claims.)* |
| **§7.1** | both mg-9d7b deliverables use the fence channel **0 times** | **HOLDS** — 0 fenced lines, 0 hits, 0 hits with fences removed, measured with the declared-strike control. This audit's two documents are also 0 |
| **§8** | "I did not widen either population" | **HOLDS** — no glob changed; the added `rglob` counts the tree for B6's report and reads nothing |
| **§8** | "the only thing changed in mg-9a19's instrument is the `RECORDED` table" | **HOLDS in substance, over-tight in wording.** No assertion changed; ~10 print statements were also rewritten. Narration, not mechanism — recorded for completeness, not as a fault |
| **§6** | E5 and E11 recorded as misses, in the author's own direction | **HOLDS**, and the honesty is not cosmetic: E11's 3-vs-9 is the report contradicting its own §0 headline count in favour of the larger number |
| **§5** | the mg-9a19 handshake fired on `M4, M8` and was re-recorded with old values kept | **HOLDS** — `RECORDED_AT_MG9A19` is present and printed beside the new values |

---

## 7. Correcting the ticket's framing, which it asked for

**The standing hypothesis "MATERIAL BEYOND THE BRIEF — look there first" is WRONG for this
deliverable, and I predicted in advance that it would be.** mg-9d7b's out-of-brief material — the
`onethird_mg0242_population_census.py` consumer repair, the mg-9a19 re-recording, the 76-line CI
comment — is disclosed in §7 and E9 and is accurate. The worst finding is in the instrument's
**core**: the sentence certifying that it cannot be satisfied by a forgotten channel. The brief says
this diagnosis "has been wrong twice this week"; this is the third.

**"NEGATIVES REQUIRE THEIR CANDIDATE SPACE" lands, but not as dishonesty.** The report does not hide
E13's miss — it leads with it, in bold, calls it *"the most interesting result here"*, refuses to
present a clean sweep as strong, and says the census's value is *prospective, not retrospective*.
That last sentence is very nearly this audit's finding. What is missing is the candidate space one
level up: not *which channels* were considered, but **which classes of channel the instrument can
see**. Name that class and E13 stops being a prediction the census could ever have settled.

**And the ticket's own framing needs one correction.** It asks whether the census "can discover one
at all". The answer is not no. It discovers one class — a new coverage bucket, exercised — and X4
proves that class is neither empty nor contrived: the live-claim control adopting its sibling's
fence rule is a change someone might really make, and the census catches it. The finding is that the
class is **narrow, uncharacterised, and excludes both channels the report calls discoveries** — not
that the instrument is inert.

---

## 8. My own predictions, and the two that were wrong

`dc49345`, committed before any probe code existed. **13 hit, 2 missed.**

| # | prediction | outcome |
|---|---|---|
| X1/X2/X3 | a sixteenth channel of each class is NOT caught | **hit**, all three |
| X5 | silent `exempt_annotation` growth IS caught | hit |
| X7 | the missed channels are demonstrably real routes out | hit — 2 of 2 |
| **X4** | a new bucket name IS caught | **MISSED at first, on my own error** — my marker was never exercised by the corpus. Rebuilt exercised: CAUGHT. The failure became **F4** and the dormant version is kept as X6 |
| **X6** | *(the arithmetic)* 3 missed, 2 caught of 5 | **MISSED — 4 of 6**, because X4's first form was inert and X6 was added afterwards |
| D1 | deleting A5 or A8 still passes | hit, both |
| D2 | 4 caught (A1, A2, A4, B1), 11 not | **hit exactly**, including the named set |
| C1/C2 | the selftest builds no controls, and that is the gap | hit — **F3** |
| C3/C4 | `len(CHANNELS)` is FORCED and unlabelled; the detection class is stated nowhere | hit — greps return nothing |
| C5 | `BASELINE` is not a bound and the census stays green as it grows | hit — **F5(a)** |
| H1–H5 | five places the deliverable holds up | hit, all five (§6) |

**The two misses are the same error, and it is the one F4 is about**: I built mutants and did not
check that they *ran*. Three of my first four removed exactly zero lines from the check, and a
MISSED from a branch that never executed is a statement about my probe. That is this audit
reproducing, in its own new code, the defect class it was sent to examine — an instrument reporting
a clean result from a mechanism that never fired. **Ninth consecutive generation, and the first
where the auditor is the one who did it.**

It is recorded rather than tidied, and the repair is asserted rather than promised: the probe now
computes, per mutant, what that mutant actually did to the real corpus, and **exits 1 if any
non-dormant mutant did nothing** — 451 code spans for X1, 17 lines for X2, 2 823 for X3, 11 for X4,
59 for X5, and 0 for X6, which is X6's whole point.

**And that repair broke twice more before it held, both times on grain — which is the third
reproduction in this audit's own code.**

1. Its first form measured every mutant in *lines reclassified*. X1 is a **text-level** channel and
   by construction moves no line between buckets, so the check reported the one mutant whose class
   the census is most blind to as inert and failed the run. A single grain does not fit six
   channels; each mutant now names its own, and X1's is `` `code` `` spans available to redact.
2. Its second form told one-sided removal from two-sided reclassification **by testing the parity of
   the bucket delta** — halving it whenever it came out even. X3 removes 2 823 lines from the
   population; on any corpus where that total landed even it would have been reported as 1 411, a
   wrong number that looks entirely plausible. The population total says which arithmetic applies,
   so it is now asked rather than guessed.

Both are the standing target *"a row name that is not its measurement"*, in the function this audit
added to stop itself committing exactly that.

---

## 9. What I did **not** do

* **I did not widen the census's detection class, or propose the wider instrument.** Naming the
  class is the finding. Deciding whether the arc wants an instrument that can see text-level
  redaction, `blank`-folding, or population narrowing is pm-onethird's call and a different ticket.
* **I did not fix F3.** The selftest's four cases are correct as tests of `audit()`; adding a fifth
  that drives a real control end-to-end is a change to mg-9d7b's instrument, and rewriting the
  instrument I was sent to audit is how an audit stops being independent. The false sentence in §5,
  the census docstring, and the CI comment is **left standing and reported**, in the same three
  places it lives.
* **I did not re-do mg-9d7b, or re-open H1/H2.** Both closures were checked (§6) and both hold.
* **I did not audit mg-9a19 or mg-cd04** except where mg-9d7b's claims about them are checkable.
* ~~I did not test the census's `--demonstrate 1e996fb` path.~~ **Struck — I did, after writing
  this list, and it reproduces: `the census BITES at 1e996fb — 9 violation(s)`.** The line is kept
  struck rather than deleted, because a "did not do" list that quietly loses entries as they get
  done is the same defect as a count written into prose.
* **I did not exhaust the channel classes.** Four classes were built. There is no argument here that
  they are all of them, and by F1's own logic a fifth I did not think of would be invisible to my
  probe for the same reason it is invisible to the census.
* **I did not change either control, or the census, or any corpus document.** Every mutant lives in
  a temp file. The only files this audit adds are its predictions, this report, its probe, and one
  CI step.
* **No mathematics.** No claim in the ledger is re-opened; C5 is untouched.

### 9.1 This audit's own prose, under the controls it audits

mg-9d7b measured its own two documents against the fence channel because mg-9a19's H5 asked it to.
The same measurement is owed here, and it is measured rather than asserted:

| document | fenced regions | evading lines | hits | hits with fences removed | near misses |
|---|---|---|---|---|---|
| `OneThird-mg77e6-ChannelCensus-IndependentAudit.md` (this file) | **0** | **0** | **0** | **0** | **0** |
| `OneThird-mg77e6-ChannelCensus-AUDIT-PREDICTIONS.md` | **0** | **0** | **0** | **0** | **0** |

Every block in both is checked, and §9 above carries a real `~~struck~~` span — a declared strike,
backed by markup at the site, which is the convention rather than an exemption. Whole battery green
with these files in the corpus: live-claim 0, declared-strike 0, mg-9a19 audit 0, mg-0242 population
census 0, mg-9d7b channel census 0, census `--selftest` 4/4, and this audit's probe 0.

---

*Deliverable for mg-77e6, an independent audit of mg-9d7b filed LATE. Instrument:
`scripts/onethird_mg77e6_sixteenth_channel_probe.py` (6 mutant controls, a reach demonstration, a
15-row deletion sweep, and three direct claim checks; RECORDED handshake, fails on movement in
either direction). Predictions committed at `dc49345` before any probe code existed: 13 hit, 2
missed, and both misses are F4. Green under Python 3.9 and 3.14. mg-9d7b's own battery is unchanged
by this audit: census 0, selftest 4/4, and the two closures it shipped both verified holding.*
