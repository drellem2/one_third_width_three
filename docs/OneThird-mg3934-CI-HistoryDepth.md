# mg-3934 — the class-closure demo had never once executed in CI

**Status: fixed, and the fix is verified in the environment it runs in, not the one it was
written in.** That distinction is the whole subject of this ticket, so the verification log below
is part of the deliverable rather than an appendix to it.

---

## 1. The defect

`.github/workflows/gate-mutation-demo.yml`'s last step runs
`scripts/onethird_mg75f0_gate_class_closure_demo.py`, which builds its pre-widening column by
resolving a pinned historical commit:

```python
PRE_WIDENING_REV = "af7fc2df"     # mg-60d3, "docs+scripts: land the mg-09ea audit"
show = subprocess.run(["git", "show", f"{PRE_WIDENING_REV}:{GATE}"], cwd=REPO, ...)
```

`af7fc2df` is a real commit (`docs+scripts: land the mg-09ea audit of mg-2c34`, 2026-07-29) and
resolves in any full clone. The workflow used `actions/checkout@v5` with no `fetch-depth`, which
defaults to **depth 1** — the runner's clone holds exactly one commit and no historical object at
all. Every run therefore died at:

```
cannot read scripts/onethird_mg2c34_n7_overlap_test.py at af7fc2df: fatal: invalid object name 'af7fc2df'.
```

**The code was correct. The environment was not the one it was verified in.**

## 2. What was actually lost, counted rather than asserted

The ticket reports 8 consecutive red runs since `2026-07-30T09:35Z`. That is right as far as it
goes and it undercounts. The full record, from `gh run list --workflow="Gate mutation demo"`:

| run | branch | conclusion | why |
|---|---|---|---|
| 2026-07-30T04:46:38Z | main | **success** | last green — the step did not exist yet |
| 2026-07-30T05:27Z | — | — | `f589307` wires the mg-75f0 step in |
| 2026-07-30T05:36:59Z | polecat-75f2 | failure | mg-60d3 step failed (a separate, since-fixed harness defect); **mg-75f0 step SKIPPED** |
| 2026-07-30T06:39:18Z | polecat-75f2 | failure | `invalid object name 'af7fc2df'` |
| 2026-07-30T06:43:36Z | main | failure | ditto |
| 2026-07-30T09:10:46Z | polecat-4f9b | failure | ditto |
| 2026-07-30T09:35:12Z | main | failure | ditto |
| 2026-07-30T10:53:07Z | polecat-48dd | failure | ditto |
| 2026-07-30T11:21:56Z | main | failure | ditto |
| 2026-07-31T04:38:39Z | polecat-fccb | failure | ditto |
| 2026-07-31T04:48:38Z | main | failure | ditto |
| 2026-07-31T05:07:19Z | polecat-8a71 | failure | ditto |
| 2026-07-31T05:13:36Z | main | failure | ditto |
| 2026-07-31T05:45:54Z | polecat-069f | failure | ditto |

**12 consecutive red runs over ~24 hours; the mg-75f0 step was reached on 11 of them and failed on
all 11, and was skipped on the 12th. It has executed zero times.**

What is **not** lost, and the ticket is right to insist on the narrower statement: the three
earlier steps — mg-7db4 watchlist consistency, mg-7db4 probe mutation battery, mg-60d3 gate
mutation demo — run before the failing one and pass. Per-step timings on the 2026-07-31T05:13:36Z
job confirm it: watchlist `<1 s`, battery `5m40s`, mg-60d3 demo `4m07s`, all green.

So the loss is exactly one question: **"does the widening catch mutations nobody enumerated?"** It
has had no CI evidence at any point since it was posed.

**Read the first green accordingly.** It is the step's *first execution*, not a restoration.

## 3. The fix

### 3.1 `fetch-depth: 0` (the instance)

On the checkout step of `gate-mutation-demo.yml`. The cost is negligible and was measured rather
than assumed: the whole repository is **2.6 MiB packed over ~380 commits**, and the depth-1
checkout step measured 1 s.

Deliberately *not* applied to `script-controls.yml`, whose depth-1 checkout is correct because
nothing it runs reads history — a condition now machine-checked rather than hoped for (§3.2).

### 3.2 `scripts/onethird_mg3934_ci_history_depth_control.py` (the class)

This defect was found only because it happened to sit in the **last** step of its job. A second
one in a step that runs later would have been just as invisible. The new control closes that:

* **(A) Coupling** — static, order-milliseconds, resolves nothing, so it is sound in a shallow
  checkout. For each workflow: derive the scripts it *executes* (command-shaped `run:` lines, not
  the fifteen script paths in the `paths:` filters), take their transitive `onethird_*` import
  closure, find every module that reads a pinned historical revision, and **fail any workflow that
  reads one without `fetch-depth: 0`.** It also fails the converse — `fetch-depth: 0` with no
  reader left — so a full fetch cannot quietly become dead weight.
* **(B) Resolvability** — every pinned revision literal anywhere in `scripts/` must resolve to a
  commit in *this* checkout. Meaningful only where the history is present, so it is skipped under
  `--static-only` and run in the deep-checkout job.

Where each runs:

| surface | invocation | checkout | why |
|---|---|---|---|
| `script-controls.yml` | `--static-only` | depth 1 | every commit under `scripts/`, `data/`, `docs/` pays milliseconds for (A) |
| `gate-mutation-demo.yml` | full | `fetch-depth: 0` | **first step**; a rotted or unreachable pin now costs seconds, not a ten-minute red |
| `scripts/refinery_gate.sh` | not run | full clone | (A)'s premise — a checkout action with a shallow default — does not apply |

The control is self-testing: seven synthetic drifts, each of which must fire, run on every
invocation before the real check. It is wired into the mg-7db4 watchlist (`MECHANISM`, both copies
of the paths list), so it cannot be neutered without the job that depends on it re-running.

**Its own detection is honest about its limits**, which are stated in the module docstring: a
revision that is *computed* rather than written down is invisible to both properties; the
40-character cap keeps sha256 digests out; (A) is stated per file rather than per job. One
consequence worth naming: the control scans `scripts/` including itself, so its self-test fixture
revisions are **built at run time rather than written as literals** — a quoted hex literal in a
fixture would have made the file report itself as pinning an unresolvable commit. Excluding itself
from the scan was the other way out and is the worse one: a control with a hole shaped exactly
like itself.

### 3.3 The sweep the ticket asked for

Every quoted hex literal of 7–40 characters in `scripts/`, and what runs it:

| script | pinned revs | resolves? | CI-executed? |
|---|---|---|---|
| `onethird_mg75f0_gate_class_closure_demo.py` | `af7fc2df` | yes | **yes** — `gate-mutation-demo.yml`; **this is the one that was failing** |
| `onethird_mgbd53_widening_audit_probe.py` | `af7fc2df` | yes | no |
| `onethird_mg4f9b_route_axis_probe.py` | `af7fc2df`, `91fa25f`, `9fa4aaa` | yes | no |

**5 literals, 4 distinct revisions, 3 scripts. Exactly one of the three is executed by CI, and it
is the one that was red.** The other two are audit probes run by hand on a full clone; they are
not broken today and cannot silently become broken tomorrow, because property (A) fails the
workflow the moment either is wired into a job whose checkout is shallow, and property (B) fails
the deep job the moment any of the four revisions stops resolving.

All three revisions are ancestors of `origin/main`, checked explicitly — a pin reachable from no
surviving branch would still be unfetchable at `fetch-depth: 0`, and (B) is what would see it.

Also swept and clean: `scripts/refinery_gate.sh` uses `git rev-parse`/`git diff` against `origin/main`
and `HEAD`, symbolic refs only, no pinned revision; `onethird_mg8a71_live_claim_control.py`
mentions `git show 1b00147^` only inside a docstring, as a by-hand demonstration, and never
executes it. `lean.yml` runs nothing that touches git history.

### 3.4 The decision the ticket asked for: is a check allowed to stay red worth having?

**Red stays tolerated, and it now has a named consumer.** Both halves of that matter.

*Not blocking.* Making this ~30-minute job block the merge was considered and rejected on exactly
the measured grounds mg-7db4 and mg-75f0 used when they kept the expensive demonstrations out of
`refinery_gate.sh`: the first version of that gate held the refinery queue for 22 minutes and
stretched every concurrent run tenfold. A blocking gate long enough that people want it bypassed
has a shorter life expectancy than the defect it guards.

*But consumed.* The 21 hours happened because nothing read the result — a permanently-red
informational check cannot be told apart from a working one, and it trains every reader to skip
the column. So `scripts/refinery_gate.sh` now **prints this workflow's latest conclusion on `main`
into the refinery's Gate Output**, which `pogo refinery show <mr>` displays to the author of the
merge. The audience is exactly right: the people whose commits can invalidate these
demonstrations, at the moment they merge one. It is inside the watched-paths branch, so ordinary
merges do not pay for it.

That readout is **non-blocking by construction and deliberately not fail-closed** — the only thing
in that file that is not. The fail-closed rule there is about the *demonstration*: not knowing
whether the gate still works must not resolve to "proceed". This is a status lookup over the
network on a host that may have no `gh` and no credential; failing a merge because it timed out
would be a new way to make merges flaky, which is the same disease. All three branches exit 0.

**What is still not claimed: nobody is paged.** The readout makes red visible to a reader who is
already looking at a merge. It does not make anyone look. That residual is stated in the workflow
header too, rather than left for the next audit to find.

---

## 4. Verification — enumerated, and in the environment each thing runs in

The ticket's standing rule for this deliverable is that anything added must be verified where it
will run. What was checked, and how:

### 4.1 The failure, reproduced in a genuine depth-1 clone

`git clone --depth 1 --branch main git@github.com:drellem2/one_third_width_three.git`, i.e. what
`actions/checkout` produces. Confirmed `rev-parse --is-shallow-repository` = `true`,
`rev-list --count HEAD` = 1.

```
$ git show af7fc2df:scripts/onethird_mg2c34_n7_overlap_test.py
fatal: invalid object name 'af7fc2df'.
$ /usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py --only M3
cannot read scripts/onethird_mg2c34_n7_overlap_test.py at af7fc2df: fatal: invalid object name 'af7fc2df'.
EXIT=1
```

Byte-identical to the CI log line. **The reproduction is faithful, so what it says about the fix
is worth something.**

*A trap worth recording, because it nearly produced a false all-clear:* cloning `--depth 1` from
the local path `/Users/daniel/research/one_third_width_three` **succeeds** at reading `af7fc2df`
— that repository's local `main` ref is stale and still points at `af7fc2df` itself, so a depth-1
clone of it contains exactly the object in question. The reproduction has to come from the
GitHub remote. A local shallow clone would have "verified" the wrong environment, which is the
same mistake one level down.

### 4.2 The fix, in a full clone

Same repository cloned without `--depth`: 394 commits, `is-shallow-repository` = `false`,
`git show af7fc2df:<gate>` resolves, and the mg-75f0 demo runs. Full-run result recorded in §4.5.

### 4.3 The new control, in both checkout depths

* Against the **unfixed** tree it fails with one problem naming `gate-mutation-demo.yml`,
  `onethird_mg75f0_gate_class_closure_demo.py` and `af7fc2df` — i.e. it would have caught this
  defect before the first red run.
* Against the **fixed** tree it passes, reporting the (A) matrix and all 5 pinned literals as
  resolving.
* `--static-only` behaves identically on the coupling half in a shallow checkout, resolving
  nothing.
* Self-test: 7 drifts, all fire; the undrifted snapshot is clean. Run on every invocation.

### 4.4 The readout, all three branches exercised

`gh` present and the check red → prints the red banner with conclusion, timestamp, title and URL,
exit 0. `gh` absent from `PATH` → prints the by-hand command, exit 0. Lookup returning nothing →
prints "no completed run readable", exit 0. `sh -n scripts/refinery_gate.sh` clean.

### 4.5 The acceptance run — the mg-75f0 demo's first execution in CI

*(Filled in from the real CI run on this branch, which is the environment in question.)*

See §5.

---

## 5. Acceptance run

<!-- ACCEPTANCE -->
