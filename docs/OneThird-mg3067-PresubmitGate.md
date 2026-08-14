# mg-3067 — the local pre-submit gate

**What landed:** `./presubmit.sh` at the repository root, plus
`scripts/onethird_mg3067_presubmit_steps.py`, which derives what it runs from
`.github/workflows/script-controls.yml`, plus one new step in that workflow that
checks the derivation has not stopped covering the job.

**Whose decision:** pm-onethird's, as product owner, recorded in `mg-69b4` and
carried here by `mg-3067` because `mg-69b4` is archived and a decision with no
ticket is never dispatched. Daniel can override. This document exists so an
override can be on the reasoning rather than on the outcome.

**The decision, in one line:** give this repo a *local* pre-submit gate; do
**not** spend the effort enforcing `onethird_program`'s `build.sh` at the
refinery or in Actions — that is the change that sounds most like `mg-69b4`'s
original title and it would have prevented none of the incidents that motivated
it.

---

## 1. Why a local gate, when the refinery already gates

Not "catch it earlier". The argument is about *which resource pays*.

The refinery is a **serial shared** resource with one slot. A local gate is
**parallel and private**. A defect found at the refinery costs:

* a queue round-trip;
* a reserved worker slot for the duration — which dropped one repo's dispatch
  cap from 3 to 2 and refused a real dispatch on the night this was decided;
* and, when the fault is repo-wide, **N independent rediscoveries** by workers
  who did not cause it.

**The worked example is `mg-457a`.** `main` in this repo was red for 5 hours
because the `mg-cd04` declared-strike control is a repo-wide *document* check
that only ran after merge. `cf63bb3c` introduced the violation and it would have
been red in its own author's worktree immediately. Four commits landed on top of
the red main; a queue-jumping dispatch was needed to repair it; and the mayor had
to mail two workers pre-emptively to stop them "fixing" a control that was
working correctly.

**Cross-product (`mg-856d`).** pm-pogo's standing objection is that this repo's
gate runtime is paid under a *globally serial* refinery — their repo pays for my
gate. Moving the cheap class off the shared slot and onto the author, in
parallel, helps that concern rather than trading against it.

---

## 2. THE LIMIT, stated before anything else it does

**A pre-submit gate catches defects in YOUR tree. It cannot catch interactions
with what lands while you work.** Both classes occurred in one night and they are
not the same problem:

| class | instance | caught by `presubmit.sh`? |
|---|---|---|
| **own-tree** | `mg-457a`'s declared strike, introduced by `cf63bb3`, which made `main` red for 5 hours | **yes — measured, see §2.1** |
| **interaction** | `mg-5058`'s rebase conflict — four files rather than the one its recipe predicted, because `mg-ede8` landed mid-flight and independently issued colliding control ids | **no, and not catchable here.** It did not exist at pre-submit time |

So this is **not a substitute for the refinery gate** and must not be described
as one anywhere. The refinery gates the *rebased* tree, which is the thing only
it can do. `presubmit.sh` is a filter that removes the cheap, private, own-tree
class from a serial shared resource.

The same point is independently why enforcing `onethird_program`'s `build.sh`
was rejected: **the incidents in that repo were interaction-class.**

`presubmit.sh` prints this limit in its own readout on every run, green or red.

### 2.1 The own-tree row is measured, not asserted

The claim "it would have been red in its own author's worktree" is the load-bearing
one in this whole ticket, and it arrives as a sentence in a decision body. It is
now run instead:

```
$ git show f825cfb:scripts/onethird_mgcd04_declared_strike_control.py > /tmp/pre.py
$ cp /tmp/pre.py scripts/.tmp.py && python3 scripts/.tmp.py --demonstrate cf63bb3c
  [*** NEW ***] OneThird-mg52c4-PerPoset-Subposet-Question.md:19
            declares struck: "restriction maps carry local-to-global content"
  FOUND (as intended): OneThird-mg52c4-PerPoset-Subposet-Question.md
RESULT: the control BITES at cf63bb3c — 1 unmade declared strike(s).
```

`f825cfb` is the revision immediately before the `mg-457a` repair, so this is
**the control that was live at the time**, applied to the tree `cf63bb3` produced.
It fires, naming the exact site. `presubmit.sh` runs that control as step 14 of 23,
against the working tree, inside a three-minute run.

**One thing this does not say.** Running the control at HEAD against the same
revision reports *nothing*, because `mg-457a`'s repair added a keyed BASELINE entry
for that site — the strike was real and was made at its destination in the same
commit, so the adjudication was to baseline it rather than to change the document.
The control's rule, regexes and exemption channels were untouched. So the honest
form of the claim is not "the gate would have caught a bug": it is that **the
adjudication would have happened in the author's worktree, before submit, instead
of as a queue-jumping repair against five hours of red `main` with four commits
stacked on top and two workers mailed off a control that was working correctly.**
That is the whole argument for a local gate, and it survives the fact that the
finding turned out to be a describable one.

---

## 3. What it runs, and why there is no list in it

`presubmit.sh` **contains no list of controls.** The list is
`.github/workflows/script-controls.yml`, and it is re-read on every run by
`scripts/onethird_mg3067_presubmit_steps.py`. Two gates that can disagree are
worse than one, so there is exactly one definition of what the fast gate *is*,
and this repo already had it.

That is the same principle as `onethird_program/build.sh`'s header ("There is
exactly one definition of what the gate IS … so the two routes cannot drift apart
into two gate lists that disagree"), applied to a repo where the definition
already lives in the workflow.

A new CI step is picked up on the next local run with **no edit** to
`presubmit.sh` or to the extractor.

**Not in scope, deliberately:** `.github/workflows/gate-mutation-demo.yml` (the
~30-minute demonstration job) and `scripts/refinery_gate.sh` (the blocking
refinery gate). A pre-submit gate that costs those is a pre-submit gate nobody
runs. `presubmit.sh` instead *tells* the author, advisory-only and without
touching its exit code, when their diff touches a path on `refinery_gate.sh`'s
own `WATCHED` variable — read out of that variable, not copied into a second
list.

### 3.1 The two declared transformations

The local run is not byte-identical to the CI run. Both differences are declared
in the extractor's header and **enforced as the only two** by the control in §3.2:

* **T1 — interpreter.** A leading `python3` becomes the interpreter
  `presubmit.sh` selected. Bare `python3` on the fleet host has no numpy and
  `/usr/bin/python3` does; `scripts/refinery_gate.sh` line 231 makes the same
  substitution for the same reason. CI provisions its own 3.12 and has no such
  problem.
* **T2 — provisioning.** `pip install` lines are dropped. They are how the hosted
  runner acquires numpy. Locally the chosen interpreter either already imports
  the named modules or `presubmit.sh` refuses to start — **a gate must not mutate
  the author's environment.**

### 3.2 The control that keeps this honest

`scripts/onethird_mg3067_presubmit_steps.py --check` runs in
`script-controls.yml`. It is order-milliseconds and standard-library only.

| id | assertion |
|---|---|
| C0 | refuses a PASS over an **empty** plan — a parser that finds nothing otherwise exits 0 over zero assertions and reports a gate that runs nothing (`mg-9a59`'s defect class) |
| C1 | the block parser's step count equals an **independent** lexical count of `run:` keys |
| C2 | every line of every `run:` block is either executed locally or is a declared T2 pip line, and the accounting closes |
| C3 | the T2 exemption stays narrow — anything dropped must actually be a `pip install` |
| C4 | no step parses to an empty local command |
| C5 | no bare `python3` survived T1 into the plan |
| C6 | the workflow declares **exactly** the one job the plan covers |

**A remedy is an artifact of the same kind as the defect, so it is subject to
it.** The failure mode this whole file is about — a control that cannot fail — is
exactly the shape a parser-derived plan has. So `--check` runs six synthetic
drifts *before* its own verdict on the real workflow is believed, and each must
be caught:

```
ok   pristine minimal workflow                  clean
ok   a run-block line vanishes from the plan    C2 fires
ok   a step is added to CI                      C1 fires (2 vs 3)
ok   the exemption widens past pip              C4 fires
ok   T1 stops substituting the interpreter      C5 + C2 fire
ok   the job loses its steps                    C0 fires
ok   a step is pip-only                         C4 fires
ok   a second job appears in the workflow       C1 + C6 fire
```

**The eighth drift was a real defect in this file, not a decoration.** It was
written to test the sentence the module prints about itself — *"runs every
control this workflow runs"* — and on its first run it came back **NOT CAUGHT**:
the parser read to end-of-file rather than stopping at the job boundary, so a
second job's steps were silently swept into the local plan while nothing said so.
That is `mg-bd53` finding 5's exact shape — an over-wide statement landing inside
a file's own description of its coverage — reproduced in the gate written to
catch it, and found only because the drift was written before the claim was
believed. The parser now stops at the job boundary and **C6 makes a second job
red**, so that it is a decision somebody makes rather than something the local
gate inherits.

Current reading against the real workflow:

```
steps parsed: 23
independent `run:` count: 23
run-lines: 25 total = 24 executed locally + 1 pip-exempt
pip-exempt modules: numpy
jobs declared: controls
```

**On `mg-9d7b`'s invariant** — every route by which a line leaves a control
unchecked is either BOUNDED by a named constant or REPORTED with a number in the
control's own output; unbounded-and-silent is the defect. T2 is the only such
route here, it is **unbounded** (any number of `pip install` lines would be
dropped), and it is **REPORTED**: the `run-lines` and `pip-exempt modules` rows
above are printed on every run, in CI and locally. Unbounded-and-reported is a
decision, and this is the decision.

---

## 4. `mg-4c4d`'s known cost — measured here, and this repo does NOT have it

`mg-4c4d`, in the sibling repo, records that a branch adding a new *watched
transcript* is red on its first run **by construction**, because the gate cannot
grade a file that has no committed copy. The scope note asked whether this repo
has the same property, and said to put the answer in the gate's own output rather
than leave an author to find it.

**It does not.** Checked two ways:

1. **By reading.** Every history-reading call site in the doc-scanning controls
   is behind an explicit flag that CI never passes — `--demonstrate <rev>`
   (`mg-cd04`, `mg-1d03`), `--drift <base> <repair>` (`mg-9a19`), `--deletions
   <rev>` (`mg-0242`). The default invocation, which is the one the workflow and
   `presubmit.sh` run, grades the **working tree** and reads no revision.
2. **By experiment.** This very document, `presubmit.sh` and
   `scripts/onethird_mg3067_presubmit_steps.py` were all new, previously
   uncommitted files under `docs/` and `scripts/` — the populations those
   controls scan — when the full gate was run over them. Result: **23 of 23
   GREEN**, in 177 s. A file with no committed copy is graded normally here.

So the property is a difference between the two repos, not a shared one, and
`presubmit.sh` says so in a comment at the point where an author would be
looking. What *is* true here is the ordinary consequence of grading the working
tree: a new document is graded on its **content** from the moment it exists, so a
new doc that quotes a figure without its population is red immediately. That is
the control working, not a first-run artifact.

---

### 4.1 A cost `mg-4c4d` does not name, found by running the gate rather than reading it

**Some controls write to the tree they grade.** The `mg-5ad1` blindspot probe
rewrites `data/onethird-mg5ad1-gate-blindspot-probe.json` on every run, and the
rewrite is not empty — on the first local run here it moved ten values, all
floating-point noise in the last digits (`lambda2_BK`
`0.9732050807568882 → …84`, the `c_max`/`c_min` rows, and one
`-1.19e-62 → 1.08e-17`).

CI never notices, because it discards its checkout. **An author's worktree keeps
it.** A gate that silently dirties the tree it is grading teaches authors to
`git add .` over a diff they did not write, which in this repo means committing
last-digit churn into a data file that other instruments read.

`presubmit.sh` therefore snapshots `git status --porcelain` before the run and
reports, after it, every path that was clean before and is not now. **It does not
revert them.** A gate must not mutate the author's tree, and un-mutating it is
still mutating it — a revert would also silently discard a real edit an author
made to that same file while the gate was running.

This was found by running the gate, not by reading it, and it is recorded because
it is the same shape as `mg-4c4d`: a cost the gate adds that the author would
otherwise meet as a surprise.

---

## 5. Duration — with the clock and the load, or it is not a figure

This repo's most-audited defect class is a quantity stated without saying what it
measures (`scripts/refinery_gate.sh`'s DURATION TABLE is the long version). So:

| figure | what is timed | clock | status |
|---|---|---|---|
| **3.6 min** | the whole `Script controls` job — checkout, Python provisioning, all steps | GitHub-hosted runner wall-clock | **MEASURED, not mine.** pm-onethird's, stable across three green runs (`4a24d9cf`, `7dddbdf2`, `bec18a04`). Quoted, not re-derived |
| **≤ 3.6 min** | `presubmit.sh` on an unloaded fleet host | local process wall-clock | **DERIVED, upper bound.** The row above minus checkout and provisioning, which a worktree run does not pay |
| **2 min 57 s** (177 s) | `./presubmit.sh`, 23 of 23 steps GREEN, this worktree, `/usr/bin/python3`, BLAS thread caps set to `POGO_WORKER_CORES=3`, on this branch's tree with all three new files present | local process wall-clock | **MEASURED, mine.** 1-minute load average **15.2 → 11.3** across the run, 10-core host |
| **2 min 59 s** (179 s) | the same gate, same host, one revision of the docs earlier | local process wall-clock | **MEASURED, mine.** 1-minute load average **13.1 → 35.1** |
| **4 min 15 s** (255 s) | the same gate, same host, earlier still | local process wall-clock | **MEASURED, mine.** 1-minute load average **61.7 → 36.8** |

**No row here is a specification of the gate**, because none was taken on a quiet
box: the 1-minute average peaked above 130 during the window these files were
written, well inside the contention regime `mg-1b8c` measured at roughly 10× on
this host. The three readings are kept together because a single reading of a
load-sensitive quantity measures nothing, and together they say something the
best of them alone would not: **177 s at load 15 and 255 s at load 62** — a 44%
spread across a 4× load difference, so this gate is far less load-sensitive than
the blocking slow path, which `mg-856d` measured at 4–8× inflation.

The DERIVED row above is **not** upgraded to MEASURED by substituting the 177 s.
That would be the same error wearing a better number — pm-pogo's rule, which is
stricter than picking the nearest available reading.

What the rows do establish is that the gate is **three minutes, not thirty, even
under contention** — which is the only property the decision rests on. An author
should plan against the ≤ 3.6 min upper bound.

Sensitivity: fleet load, and nothing else observed to matter. Unlike the blocking
gate's slow path, nothing here is concurrent — steps run one at a time, and the
only self-parallelising component is numpy's BLAS inside the `mg-2c34` step,
which is why the thread caps are recorded above rather than left implicit.

---

## 6. The name: `presubmit.sh`, not `build.sh`

`mg-69b4`'s scope note says to follow `onethird_program/build.sh` and states that
this repo "has no `build.sh`, no `refinery.toml`, no Makefile today". **The
`refinery.toml` half of that is false**, and it was checked rather than assumed:
`.pogo/refinery.toml` exists and declares `commands =
["./scripts/refinery_gate.sh"]` with `timeout = "90m"`.

That changes the *name*, because the sibling's name is not decoration. It chose
`build.sh` precisely so pogo's **default gate discovery** — which looks for
`./build.sh` and `./test.sh` at the root when a repo declares no gates of its own
— would find it if `refinery.toml` were ever deleted. Two routes to one gate
list.

Here that mechanism runs backwards. A root `build.sh` in *this* repo would mean
that deleting `.pogo/refinery.toml` silently swaps the blocking gate from
`scripts/refinery_gate.sh` — the gate-mutation demonstration, the thing that
actually blocks — to this fast local one. Merges would stay green while the
demonstration quietly stopped running: "a control nothing invokes", with a
shorter fuse, which is the defect the sibling's header exists to prevent. And
enforcing at the refinery is what `mg-69b4` explicitly decided **against**.

So the **shape** is the sibling's — one definition, every suite runs, the worst
exit wins, no `&&` — and the **name** is not. `git mv presubmit.sh build.sh`
reverses this in one command.

### 6.1 Every step runs; the worst exit wins

Short-circuiting means the first red control hides whether the others are red
too, so an author fixes one thing, re-runs, and meets the second only on the next
round. *Within* a step the commands run under `sh -e`, which is what GitHub's
`run:` does, so a step's own short-circuit is preserved. *Across* steps this
continues where CI's job would stop. **That cannot change the verdict** — the
worst exit is 0 exactly when every step is 0 — only how much you learn per run.

---

## 7. What I did NOT do

* **I did not change what any control checks** — no rule, no regex, no exemption
  channel was touched. This is about *when* they run, not *what* they say.
  `mg-457a`'s control was correct throughout.
* **I did not narrow or widen `refinery_gate.sh`'s `WATCHED` list**, and I did not
  re-derive it. `presubmit.sh`'s advisory notice reads that variable directly.
  (`mg-856d`'s retraction settles that the variable literally holds all seventeen
  entries and that reading it gives the right answer; the "five" was never
  measured and is void.)
* **I did not make this gate blocking**, at the refinery or in Actions. It is run
  by the author. Nothing enforces that it was run — that is a property of the
  decision, not an oversight, and the honest description of what it buys is
  "authors who run it stop paying the serial slot for own-tree defects".
* **I did not measure the local runtime on a quiet box.** The host was under
  heavy load for the whole window — the 1-minute average peaked above 130 — so
  the two figures in §5 carry their loads and the ≤ 3.6 min planning figure stays
  labelled DERIVED rather than being dressed up as a measurement.
* **I did not verify that green here implies green at the refinery**, and it does
  not: this branch's own submission is the next test of that, and a failure there
  would be evidence about the interaction class rather than about this gate.
* **I did not check whether every control is *safe* to run in an author's
  worktree** beyond observing which files this run wrote (§4.1). The `mg-5ad1`
  probe was found writing to the tree; a control that writes somewhere this run
  did not happen to reach would not have been seen. What the gate now does is
  *report* what it wrote, which covers the class rather than the one instance.
* **I did not touch `.pogo/refinery.toml`, `scripts/refinery_gate.sh`, or
  `gate-mutation-demo.yml`.**
