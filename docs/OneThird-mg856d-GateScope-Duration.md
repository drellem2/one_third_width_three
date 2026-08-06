# mg-856d — Gate scope and duration: should `script-controls.yml` trigger the mutation demo, and what do the nine duration figures measure?

**Author:** polecat c856d, 2026-08-06.
**Ticket:** mg-856d (pm-onethird), items 2 and 3. Item 1 was retracted by its
author before this work began and is not addressed here — see
[What I did not do](#8-what-i-did-not-do).

---

## 0. Verdict, up front

**Item 2 — should `.github/workflows/script-controls.yml` trigger the
gate-mutation demonstration?**

*Partly. It should keep triggering the **informational** demonstration on
GitHub Actions, and it should stop triggering the **blocking** one in the
refinery gate.* pm-onethird's opinion ("I do not think it should") is right
about the cost and slightly wrong about the object: the trigger is not one
trigger, it is one list serving two consumers whose costs differ by three orders
of magnitude, and only one of them needs narrowing.

**The measurement that decides it.** 12 of the 21 merge requests that fired this
gate's slow path in its first 7.5 days did so **only** because they touched
`script-controls.yml` — 57% of the firings — and neither instrument on that slow
path ever opens the file. *(Population: MRs merged to `origin/main` between
`df7db8b` 2026-07-30 05:08 +0100, the commit that made the gate blocking, and
`origin/main` HEAD on 2026-08-06. Grain: one MR, proxied by the `(mg-XXXX)` tag
in the commit subject. Derived here, not quoted from anywhere.)*

**Item 3 — the duration figures.** The ticket said six; there are **nine**, and
they sit on **three non-convertible clocks**. One of them, `~17 minutes`,
is not stale in the ordinary way — it was *correct when written* and the
configuration it described was dismantled around it eight hours later. All nine
are now in one table in `scripts/refinery_gate.sh`, each with what is timed,
which clock, and its status.

**What it costs and what it saves, in gate time.** *(Clock (b) — local process
wall-clock on the fleet host. Measured 2026-08-06 by
`scripts/onethird_mg856d_gate_cost_measure.sh`, deliberately under contention,
with the load recorded around every row; full output in §7.)*

| | before | after | on |
|---|---|---|---|
| blocking slow path | **5256.5 s = 1 h 27 m 36 s** | 0.4 s + the readout's `gh` calls | a merge whose only watched change is `script-controls.yml` |
| every other merge | 0.2 s | 0.4 s | the new control adds ~0.2 s, unconditionally |

* **Saving:** ~1 h 27 m of the refinery's **one serial slot** on ~57% of the
  merges that currently pay it — 12 MRs in 7.5 days, **1.6 MRs/day**. Under the
  quiet-box figures already in the file (~11 min) the same 12 MRs would be
  ~2 h 20 m of serial slot; under the conditions actually measured they are
  **~17.5 hours**.
* **Cost:** ~0.2 s per merge for the new exemption control, on every merge
  including the ones that skip nothing.
* **Coverage removed:** none. §5 makes that a claim with a proof rather than an
  assurance.

**And the number that outranks all of those.** The measured slow path,
1 h 27 m 36 s, finished **2 m 23 s inside `.pogo/refinery.toml`'s 90-minute gate
timeout — 97.3% of the budget** — on a host that was busy but not
extraordinary (1-minute load average 38→149 during the run, 10 cores). The
brief's claim that gate duration is unbounded relative to the timeout is not a
worry; it is 2 m 23 s from being an outage. **This change does not bound the
slow path.** It removes 57% of the merges that enter it. Bounding it is a
different ticket and someone should open it.

---

## 1. What "being in `WATCHED`" actually buys

`.github/workflows/script-controls.yml` is line 2 of the 17-path `WATCHED`
literal in `scripts/refinery_gate.sh` *(re-derived from `origin/main`, agreeing
with pm-onethird's own re-derivation in the ticket's retraction)*. Being on that
list has exactly two effects, and they are welded together:

| | consumer | what it costs | who pays |
|---|---|---|---|
| **E1** | `scripts/refinery_gate.sh`, run by the refinery before it fast-forwards to `main` | mg-5ad1 blindspot probe + mg-60d3 mutation demo | **the whole fleet** — the refinery has ONE serial slot and every other MR queues behind it |
| **E2** | `.github/workflows/gate-mutation-demo.yml`, `on: push/pull_request: paths:` | mg-3934 full, watchlist consistency, mg-7db4 battery, mg-60d3 demo, mg-75f0 closure demo | GitHub's hosted runner — blocks nothing and holds nothing |

They are welded because
`scripts/onethird_mg7db4_watchlist_consistency.py` property (1) requires the
workflow's `push` paths, its `pull_request` paths and the shell `WATCHED` to be
*the same set*. That is deliberate and it is load-bearing: two copies of a list
that may differ is the shape that rots, and the whole mg-7db4 mechanism exists
because it must not.

**So a decision that removes the path removes E1 and E2 together.** That
constraint is what makes the naive answer wrong, and it is the reason this
change is expressed as a *second* list rather than as a deletion from the first.

---

## 2. The population and the price

*Population: every commit reachable from `origin/main` (424 commits) and, in the
second table, the 46 commits merged after the blocking gate landed. Grain: one
commit, and one MR proxied by the `(mg-XXXX)` subject tag. Both derived here
with `git log --name-only` against the `WATCHED` literal at `origin/main`.*

Over the whole history:

| | commits |
|---|---|
| commits on `origin/main` | 424 |
| touching ≥1 watched path | 36 |
| touching `script-controls.yml` | 19 |
| …where it was the **sole** watched path | **13** |

Since the gate became blocking (`df7db8b`, 2026-07-30 05:08 +0100 → HEAD
2026-08-06):

| | commits | MR-proxies |
|---|---|---|
| all | 46 | 25 |
| fired the slow path (≥1 watched path) | 26 | 21 |
| touched `script-controls.yml` | 15 | 14 |
| …**sole** watched path | **12** | **12** |

**12 / 21 = 57% of every slow-path firing this gate has ever had.**

The twelve are not incidental. They are the repo's standard idiom, and the
subjects say so:

```
839429d4 2026-08-05 docs+scripts+ci: INDEPENDENT AUDIT of mg-9d7b …
cfaff420 2026-08-05 docs+scripts+ci: INDEPENDENT AUDIT of the mg-1d03 G3+G4 repair …
13f1e6ae 2026-08-05 docs+scripts+ci: close mg-0242 G3+G4 …
99f3f16a 2026-08-05 docs+ci: mg-9d7b's report and the CI wiring …
1e996fb4 2026-08-04 docs+scripts+ci: INDEPENDENT AUDIT of the mg-0242 G1/G2 repair …
f6e329c5 2026-07-31 docs+scripts+ci: close mg-0242 G1 + G2 …
ad9ba10a 2026-07-31 docs+scripts+ci: INDEPENDENT AUDIT of the mg-069f body-strike …
bb1cb9be 2026-07-31 docs+scripts+ci: close the mg-8a71 verdict …
2697c074 2026-07-31 docs+scripts+ci: INDEPENDENT AUDIT of the mg-fccb §2.3 direction repair …
1b001475 2026-07-31 docs+scripts+ci: close the mg-d112 verdict …
bd675b66 2026-07-30 docs+ci: the mg-4f9b deliverable …
b3cfb257 2026-07-30 docs+ci: correct mg-7db4's catch matrix for CONTROL E …
```

Every one is *an audit polecat wiring its new control into CI*. That is the
thing this repository does most, and each time it does it, it pays the
gate-mutation demonstration in the fleet's only serial slot. The rate is
**1.6 MRs/day** over the window, and it is not decaying.

---

## 3. Can editing `script-controls.yml` change what the blocking gate asserts?

This is the question the cost has to be justified against, and it had never been
asked — the watchlist checks that the *list* is consistent, complete and
identical in both copies. All three are properties of the list. None of them is
"can path P change instrument I's answer".

### 3.1 What the mechanism already says, if you read it as evidence

`scripts/onethird_mg7db4_watchlist_consistency.py` derives the watchlist as
`MECHANISM | closure | datasets`, where `closure` is the transitive
`onethird_*` import closure of `ROOTS` and `datasets` is what that closure
reads. `.github/workflows/script-controls.yml` is in **`MECHANISM`** — the
hand-declared half. The checker is therefore already telling us, in its own
data structure, that the path is *not reachable from any gated instrument*. It
is watched by fiat, and the fiat's stated reason is "the files the trigger
mechanism is itself made of".

That is a reason to watch it. It is not a reason to spend eleven minutes of
serial refinery time demonstrating something the file cannot affect.

### 3.2 Measured, not inferred

`scripts/onethird_mg856d_watch_sensitivity_probe.py` runs each blocking
instrument under a `sitecustomize` that wraps `builtins.open`, `io.open` and
`os.open` and records every path inside the repository opened for reading;
`subprocess.Popen` is wrapped too, so `git show <rev>:<path>` is recorded
*separately* — reading a file at a revision is not sensitivity to that file's
current bytes, and merging the two would overstate coverage.

**It carries a positive control, because a blind tracer and an insensitive
instrument produce identical reports.** Before any verdict is printed the trace
must contain `scripts/onethird_mg2c34_n7_overlap_test.py` and
`data/onethird-mg8b64-L1b-bk-transport-transfer.json`. If either is missing the
probe exits non-zero and prints nothing at all about sensitivity. A probe
reporting "not read" for all 18 paths because it cannot see would be a very
convincing instance of exactly the defect this arc keeps finding.

Result: see `data/onethird-mg856d-watch-sensitivity.json` and §7.

### 3.3 The claim in the workflow header, tested

`.github/workflows/gate-mutation-demo.yml` justifies the entry in one sentence:

> Editing `script-controls.yml` itself is watched, so adding a step is covered.

**"Covered" by what?** Watching the path fires the mg-60d3 demonstration, and
the demonstration does not read the file. I tested the strongest version of the
mutation that sentence is about — *deleting* a step rather than adding one, and
the step whose loss matters most: the mg-5ad1 blindspot probe, for which
`script-controls.yml` is the **only** home that fires on ordinary commits.

```
mutation: delete the `mg-5ad1 gate blindspot probe` step from script-controls.yml
  onethird_mg7db4_watchlist_consistency.py   -> exit 0
  onethird_mga471_partial_run_control.py     -> exit 0
  onethird_mg3934_ci_history_depth_control.py --static-only -> exit 0
```

Nothing fires. The eleven-minute demonstration that the same edit *does* trigger
would not have fired either. **The header sentence is an over-claim**: the
trigger it names is real, the coverage it implies is not. That is a finding of
this arc's own named class and I am recording it rather than fixing it — see
§8, "what I did not do".

---

## 4. The change

Three parts, in `scripts/refinery_gate.sh`,
`scripts/onethird_mg856d_exemption_control.py` and the two workflows.

### 4.1 A second list, not a shorter first list

```sh
DEMO_INSENSITIVE='.github/workflows/script-controls.yml'
```

`WATCHED` still has the path; both `paths:` blocks of
`gate-mutation-demo.yml` still have it; the mg-7db4 agreement property is
untouched and still self-tests in five ways *(re-run after the change — all five
CAUGHT, §7)*. The gate now computes two sets:

* `HITS` — every watched path that changed. Drives the changed-paths listing and
  the Actions-status readout, both of which still run for an exempt-only merge.
* `DEMANDING` — `HITS` minus `DEMO_INSENSITIVE`. Drives, and only drives, the
  mg-5ad1 probe and the mg-60d3 demonstration.

If `DEMANDING` is empty the gate prints why it is not re-running the
demonstrations, names where they still do run, and exits 0.

### 4.2 The exemption list is checked, not trusted

An exemption list on a gate is the cheapest way in this repository to build a
control that cannot fail. One appended line —
`scripts/onethird_mg60d3_gate_mutation_demo.py` — turns the blocking gate into a
`git diff` and a `grep` forever, and nothing downstream looks any different: it
still runs, still prints, still exits 0.

So `scripts/onethird_mg856d_exemption_control.py` runs on **every** merge,
unconditionally, in milliseconds, before the list is used, and fails the merge
if any of five properties is violated:

| | property | why |
|---|---|---|
| **P1** | every exempt path is still in `WATCHED` | an exemption for an unwatched path is a deletion wearing a narrower word — and it would silently drop the Actions demonstration too |
| **P2** | every exempt path is in mg-7db4's `MECHANISM` and **not** in the derived closure or its datasets | a closure member is watched *because* editing it changes what the demo computes; this makes "never exemptable" mechanical instead of a promise |
| **P3** | no exempt path is one of the trigger's own decision files | exempting the gate script, the workflow, `refinery.toml`, the consistency check or this control is exempting the machinery that decides exemptions |
| **P4** | every exempt path names a `# CATCHER <path> <script> <workflow>` whose script is really run by that workflow and whose workflow's `paths:` really covers the path | "something else catches it" is the sentence every removed control was removed on; here it is parsed against the tree |
| **P5** | the residual still contains the gate script and the demo itself | no sequence of exemptions can reach a state where nothing triggers the demonstration |

It imports `MECHANISM`, `ROOTS`, `import_closure` and `data_reads` from the
mg-7db4 module rather than re-deriving them — the move mg-5ad1's part B made for
the same reason: a second representation could disagree with the first, and then
two green checks would mean nothing together.

**Self-test, run on every invocation.** Each property is re-checked against a
deliberately drifted snapshot and the script exits non-zero unless every drift
FIRES. A check on an exemption list that has never been shown to fail would be
the funniest possible place in this repository to put one. Output in §7.

### 4.3 Wiring

`onethird_mg856d_exemption_control.py` is added to mg-7db4's `MECHANISM`, to
`WATCHED` (now 18 paths) and to both `paths:` blocks — so rewriting the rule for
skipping the demonstration re-runs the demonstration. It is also a step in
`script-controls.yml`, because `script-controls.yml` is the exempt path: an edit
that removes the catcher this file provides should not have to wait for someone
to touch the gate script to be noticed.

---

## 5. WHICH MUTATIONS WOULD NO LONGER BE CAUGHT

This is the section the ticket asked for and the one that decides whether the
change is a saving or a hollowing-out. The honest answer has to be a *set*, not
a reassurance.

**Definition.** A mutation loses its catcher iff it (i) changes what the mg-5ad1
probe or the mg-60d3 demonstration asserts, and (ii) is introduced by a merge
whose only changed watched path is `.github/workflows/script-controls.yml`.

**Claim: that set is empty. Three independent reasons, none of which is "trust
the list".**

1. **Condition (ii) forces the mutated file to be unwatched-and-unmechanism.**
   By mg-7db4's completeness property, every module the gated instruments import
   transitively, and every committed dataset those modules read, is in `WATCHED`.
   A merge that changes what the instruments assert must therefore touch a
   watched path *other than* `script-controls.yml` — at which point `DEMANDING`
   is non-empty and the full slow path runs exactly as before. The only escape
   is a file that influences the instruments while being outside the closure,
   which is precisely the drift the checker exists to refuse and self-tests
   against in five ways (drifts 3 and 4 are that exact case). **That exposure is
   identical before and after this change** — such a file does not trigger the
   demonstration today either, because it is not watched today either.

2. **Condition (i) fails for the exempt file directly, and it is measured.**
   Neither instrument opens `script-controls.yml` (§3.2, §7), so no edit to it
   can change what they assert. Skipping them on its account removes no
   information because running them produced none.

3. **The demonstrations still run on the same commits.** The path is unchanged
   in both `paths:` blocks, so `gate-mutation-demo.yml` — mg-3934 full, the
   watchlist check, the mg-7db4 battery, the mg-60d3 demo *and* the mg-75f0
   closure demo, all five — still fires on every one of those twelve MRs. What
   is dropped is the *blocking* copy of two of the five. Even if reasons 1 and 2
   were both wrong, the demonstration would still be made; it would be made
   ~21 minutes later and on a machine that holds nothing.

**What IS lost, stated plainly rather than argued away.** The *blocking*
property, for that one path: after this change a merge whose only watched change
is `script-controls.yml` can land before its Actions demonstration finishes.
That property is worth exactly what it can prevent, and by reasons 1 and 2 the
set of things it can prevent on those merges is empty. The gate's own
`FAIL-CLOSED` rule survives untouched: every way of *not knowing* — no base ref,
a failed diff, no numpy — still runs the demo. The exemption fires only where
the answer is known in advance.

**What was already not caught, before and after, and is not mine to fix here.**
The step-deletion hole of §3.3. It is not created or widened by this change —
the demonstration was blind to it while blocking, and is blind to it now — but
it is now *named*, and P4 of the new control catches the one instance of it that
this change depends on (deleting the mg-3934 step that is `script-controls.yml`'s
declared catcher). The general case is §8.

---

## 6. Item 3 — the duration figures

### 6.1 There are nine, not six

*Population: duration literals in `scripts/refinery_gate.sh` at `origin/main`
(`84f510a`). Grain: one literal occurrence. pm-onethird enumerated six by
re-reading the file after retracting a figure inherited from a peer; I
re-derived the enumeration independently and found three more — the two rows of
the `WHAT RUNS HERE AND WHAT DOES NOT` ledger and the `echo` above the final
`exec`. The six are theirs; the three are mine.*

The table now lives in the file's header. Its columns are what the ticket's
sharpened ask required: **what is timed, which clock, under what load,** and a
status of MEASURED / HISTORICAL / DERIVED / NOT KNOWN.

### 6.2 The three clocks

They are not convertible and no figure has been carried across them:

* **(a) GitHub Actions wall-clock**, hosted runner — different machine, no fleet
  contention, pays a `pip install`.
* **(b) local process wall-clock on the fleet host** — what the refinery gate
  actually spends. Load-sensitive by roughly 10× (mg-1b8c).
* **(c) end-to-end refinery MR wall-clock** — queue wait + (b) + the merge.
  Bounded below by (b) and **above by nothing**, because the refinery has one
  serial slot and an MR waits behind everything ahead of it.

pm-onethird's own diagnosis stands and is recorded in the table: the `1h17m` of
`mr-d9png12tjv1h244d8420` is clock (c) under a 1-minute load average near 300,
and **what this gate cost inside it is NOT KNOWN and is not recoverable** — the
refinery records MR start and end, not gate start and end. Per pm-pogo's rule,
which is stricter than substituting a better-looking number, that entry stays
NOT KNOWN; the quiet-box 21m of 2026-08-06 is a different clock *and* a
different load regime and is not offered as a replacement.

### 6.3 `~17 minutes` is a harder defect than a stale number

`~17 minutes` entered at `df7db8b` (2026-07-30 05:08 +0100), the commit that
created the file. On that day the blocking gate ran **three** things:

```
$ git show df7db8b:scripts/refinery_gate.sh | grep -n 'echo "==='
  138: mg-5ad1 gate blindspot probe        ~30 s
  142: mg-7db4 probe mutation battery      ~6 min
  146: mg-60d3 gate mutation demo          ~11 min
```

≈ 17 minutes. The figure was **correct**. Eight hours later `245085e` — *"move
the battery out of the blocking gate"* — removed the middle row and did not
touch the sentence. The figure did not rot; **the configuration it described was
dismantled around it.** That is why the new table records a *configuration* as
well as a number, and why the row's status is HISTORICAL with the reason
attached rather than a replacement figure.

*(Both `df7db8b` and `245085e` are mg-7db4's. This is not a criticism of an
absent author: it is the same-file, same-day version of the pattern this arc has
named repeatedly, and it survived seven days in the header of the gate that
enforces the rule against it.)*

### 6.4 The measurement, and the conditions

`scripts/onethird_mg856d_gate_cost_measure.sh` times each blocking component and
records the 1-, 5- and 15-minute load averages immediately before and after each
one. **It was run deliberately under heavy fleet contention**, because a second
point on mg-1b8c's ~10× curve is worth more than a third quiet-box reading, and
because contention is the regime in which the gate has actually hurt.

| component | measured | load (1-min, before → after) | uncontended reference | ratio |
|---|---|---|---|---|
| mg-7db4 watchlist consistency + self-test | 0.2 s | 17 → 17 | — | — |
| mg-5ad1 gate blindspot probe | 105.9 s | 17 → 38 | 26.5 s *(mg-75f0's)* | 4.0× |
| mg-60d3 gate mutation demo | 5150.4 s | 38 → 53, peak 149 | ~11 min *(mg-7db4's)* | ~7.8× |
| **blocking slow path, end to end** | **5256.5 s = 1 h 27 m 36 s** | | | |

Both ratios are *consistent with* mg-1b8c's ~10× and neither equals it, so that
figure is an order of magnitude and not a coefficient. The two ratios differ
from each other by 2×, which is itself the reason not to convert one measured
duration into another by scaling.

**Against the timeout.** `.pogo/refinery.toml` sets `timeout = "90m"`. This run
used **97.3%** of it and missed it by **2 m 23 s**. The comment justifying 90m
says it is "loose enough to survive a busy host"; on the evidence of this single
measurement it is loose enough by two and a half minutes. I have recorded the
figure and its conditions in that file and have **not** changed the timeout —
raising it would be the response of someone who had not noticed that the thing
to bound is the duration.

Sensitivity, so that the numbers reproduce: every (b) figure is sensitive to
fleet load and to nothing else observed to matter. The mg-60d3 demonstration is
**not a single-core job** — measured at ~460% CPU on this 10-core host — so it
contends with itself as well as with the rest of the fleet, which is why its
inflation under load is superlinear rather than proportional to the load
average.

---

## 7. Evidence

*(This section is the raw output of the runs the sections above cite.)*

<!-- EVIDENCE -->

---

## 8. What I did not do

* **Item 1.** Not addressed. Its author retracted it, verified the retraction
  against `origin/main`, and wrote `DO NOT DO IT`. I re-derived the count once
  (`WATCHED` contains 17 paths at `origin/main`, `script-controls.yml` is line
  2) purely to confirm I was working on the same object, and changed nothing
  there.
* **I did not narrow `WATCHED`.** The list is one longer than it was (18), not
  shorter. Nothing left the Actions trigger.
* **I did not touch the other 17 watched paths' status.** The sensitivity probe
  reports on all of them and several besides `script-controls.yml` are also
  NOT READ by the blocking instruments (§7). Each of those is a candidate for
  the same treatment and **none is exempted here** — a cost argument is not a
  licence to sweep, and each would need its own catcher named and verified.
  That is a follow-up, not an omission I am hiding.
* **I did not fix the step-deletion hole** of §3.3 — that no control asserts the
  mechanism's own steps are still wired into `script-controls.yml`. It predates
  this change, is not widened by it, and fixing it properly means deriving
  "which instruments have an ordinary-commit home" rather than hand-listing
  them, which is a design question of its own size.
* **I did not measure on a quiet box.** I could not; the host was at a 1-minute
  load average of 88–105 throughout, from other polecats' work and from my own
  measurement's ~460% CPU. Every figure I report says so. I did not round any of
  them toward the uncontended figures already in the file.
* **I did not re-measure clock (a).** The 21m of 2026-08-06T11:48 is
  pm-onethird's, re-derived by them from the Actions run, and I have marked it
  as theirs rather than re-running a hosted workflow to own the number.
* **I did not change `.pogo/refinery.toml`**, including its 90-minute gate
  timeout. The brief's observation that gate duration is unbounded relative to
  the timeout is correct and this change reduces how often the unbounded path is
  entered; it does not bound it. Bounding it is a different ticket.

---

## 9. Corrections to the ticket's framing

* **"Item 2 is my opinion, not a finding."** It is now a finding, and it lands
  one step to the side of where it was aimed. The over-broad thing is not the
  watchlist entry — the entry is correct, `script-controls.yml` really is
  mechanism — it is the *single* trigger serving a free consumer and an
  expensive one at the same threshold.
* **"charging it seventeen minutes of mutation demonstration".** The seventeen
  is the figure §6.3 shows describes a configuration retired on 2026-07-30. The
  blocking charge is the probe plus the demonstration; the figure is in §7.
* **"the file states its OWN runtime in six different figures".** Nine.
* **The ticket's own `1h17m`** was diagnosed correctly by its author before I
  arrived, and pm-pogo's refusal of `21m` as a substitute is the right call and
  is now written into the table as a rule, not just as an anecdote.
