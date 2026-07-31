# mg-3946 — INDEPENDENT AUDIT of the mg-3934 CI historical-SHA repair

**Subject:** `acbf972` + `2a4c181` (mg-3934) — `fetch-depth: 0` on
`.github/workflows/gate-mutation-demo.yml`, the new
`scripts/onethird_mg3934_ci_history_depth_control.py`, and the `refinery_gate.sh` READOUT.

**Filed in the same action as its parent, before the parent's result was routed.**

---

## Verdict

**GREEN on the SHA repair. AMBER on what the repair is taken to have established. RED on the
consumer that was added alongside it.**

| # | Finding | Severity |
|---|---|---|
| **F1** | The mg-75f0 demo's right column asserts `exit == 1` and nothing else, so **a gate that CRASHES is scored as a mutation the widening CAUGHT** — and for the four rows whose own left-column verdict is `NEVER EXERCISED` a crash-shaped mutation produces a full PASS. `stderr_tail` is captured only when `returncode > 1`, i.e. it is discarded in exactly the case where it is the evidence. Demonstrated by construction; **repaired here**. | **high** |
| **F2** | The `refinery_gate.sh` READOUT — the consumer mg-3934 added *because* nothing consumed the red — **reports an in-progress run as red.** `gh --jq` renders a JSON `null` conclusion as the empty string, never as `"null"`, so the guard cannot fire. It fired wrongly on its **first live use**: MR `mr-d9m4fr2tjv1tur4p9e40` printed `*** as of 2026-07-31T07:13:45Z ***` against a run that completed SUCCESS. **Repaired here.** | **high** |
| **F3** | **Nobody is still nobody.** `refinery_gate.sh` is the only consumer of Actions status in the repository or the fleet. It prints into the refinery's `gate_output`, and the documented polecat merge loop reads `--json … .status` only. mg-3934 says "nobody is paged"; the stronger true statement is that in the automated merge flow **the readout has no reader at all**. | **high** |
| **F4** | **Three counting claims in the remediation that its own record contradicts.** (a) "5 literals, **4 distinct revisions**, 3 scripts" over a table naming **three**, contradicted nine lines later by "All **three** revisions" — re-derived here as **5 / 3 / 3**. (b) "**21 hours**" in the workflow header, `refinery_gate.sh` and the doc, against a measured **24 h 09 m** (first red `2026-07-30T05:36:59Z`, last `2026-07-31T05:45:54Z`). (c) `refinery_gate.sh` still said "**eight** consecutive runs" — the ticket's undercount, which the mg-3934 doc corrects to **twelve** in the *same commit that wrote that file*. All corrected at their sites. | low |
| **F5** | A `--only`/`--gates` subset run of the mg-75f0 demo **overwrites the committed full report with a partial one**, with no marker, and prints a headline (`1/5 mutations … are caught`) whose numerator is over the rows run and denominator over the full set — exiting 0. Hit twice during this audit; the committed record had to be restored with `git checkout --` both times. **Named, not fixed** — see §6. | low |
| **F6** | The reachability question mg-3934 identifies in its own KNOWN LIMITS — a pin reachable from no remote ref is unfetchable at `fetch-depth: 0` — was answered **by hand** ("checked explicitly") and left unmechanised. Made a control here (PART 4). | low |

**Not found:** any second historical-SHA read masked behind the first. See §3 — the population is
named, not counted, and swept by a route that shares no code with mg-3934's.

**Undisturbed:** the three earlier steps still execute and pass. See §5 — verified in CI at HEAD,
not locally.

---

## 1. The primary question: can the mg-75f0 demo FAIL?

The ticket's framing is exact. `scripts/onethird_mg75f0_gate_class_closure_demo.py` had never
executed in CI, so its first green is its **first run**. mg-3934 established that it now RUNS.
Nothing established that it can still FAIL, and *a step nobody has seen fail is unverified however
green it prints*.

The instrument is `scripts/onethird_mg3946_closure_demo_falsifier.py`. It builds an isolated tree
per case — a copy of `scripts/` plus the mg-8b64 dataset, plus the worktree's `.git` pointer copied
verbatim so `git show af7fc2df:<gate>` resolves exactly as it does in the real tree — drifts the
demo's own subject there with an asserted anchor count, and runs the demo in that tree.

**Every exit code was predicted before the run and the predictions are kept as written.**

| case | drift applied to the demo's subject | predicted | measured | held |
|---|---|---|---|---|
| `control` | none | 0 | **0** (530 s) | ✓ |
| `neutered-widening` | the gate's identity comparison narrowed back to the four pre-mg-75f0 fields | 1 | **1** (468 s) | ✓ |
| `noop-mutation` | M9's replacement made byte-identical to its anchor | 1 | **1** (446 s) | ✓ |
| `rotted-anchor` | M9's anchor rewritten in the corpus, semantics unchanged | 1 | **1** (372 s) | ✓ |
| `rebaselined` | `PRE_WIDENING_REV` re-pinned `af7fc2df` → `9fa4aaa` (the mg-75f0 landing) | 1 | **1** (279 s) | ✓ |
| `crash-not-catch` | a row whose "mutation" is a bare `raise` in `_width` | **0** | **0** (557 s) | ✓ — **and that is finding F1** |

**Six predictions, six held, none revised.** The demo can fail, and the five drifts above are five
distinct ways of making it fail.

**Read the rows for what each one shows, because they are not equally strong.**

* **`noop-mutation` is the direct answer to the ticket.** With M9's replacement made identical to
  its anchor, the "mutated" tree is the unmutated tree, the widened gate exits 0, and the demo
  rejects the run: `M9 … exit 0 BAD`. **The M9 assertion itself is falsifiable** — the row that
  had never executed in CI is a row that can turn red.
* **`neutered-widening` fired, but at the `none` row, not at M9** — `none … exit 1 BAD`, `M9 …
  exit 1 ok`. Narrowing the identity loop makes the gate fail on the *unmutated* instrument,
  because the gate carries its own field-census control. So this case demonstrates that the demo
  refuses a broken subject; it does **not** demonstrate the widening being needed to catch M9.
  Stating that distinction rather than counting the case as "the widening was shown load-bearing"
  is the honest reading, and `noop-mutation` is the case that carries the weight.
* **`rebaselined`** shows the demo notices when its left column stops being a comparison: with the
  baseline re-pinned to the widened gate, `M9 … pre-widening exit 1 BAD` and the per-row verdict
  flips from `NEVER EXERCISED` to `EXERCISED AND ABSORBED`. mg-75f0's comment says a pinned SHA
  cannot rot, and that is true; it can still be re-pinned wrongly, and nothing downstream
  re-derives it. The demo does catch that, which is worth having on the record.
* **`rotted-anchor`** dies in `build_tree` before any gate runs, on the demo's own anchor-count
  assertion. That assertion was already there and is now shown to fire.

Total measured cost of the battery: **2 131 s (35 min)** for five cases, eleven full `--no-sweep`
gate runs, on a loaded fleet host.

## 2. What the demo cannot distinguish, and the repair

**This is the finding the ticket's second clause asks for — "is it genuinely testing *does the
widening catch UNSEEN mutations?*" — and the answer is: for four of its seven rows, not
demonstrably.**

The demo's right column asserts `r["exit"] == want`, and `want` is 1. **A gate that crashes exits 1
too.** The left column is a partial guard against that — a mutation that breaks the instrument
outright breaks the *pre-widening* gate as well, which expects 0 — but it is only partial, and the
demo itself says exactly where: the four rows whose measured left-column verdict is **`NEVER
EXERCISED`** (`M5`, `M6`, `M7`, `M9`) are rows the pre-widening gate does not reach. A mutation
that raises *there* yields exit 0 on the left and exit 1 on the right: a full PASS.

Built and measured, not argued. Case `crash-not-catch` adds one row `MX` whose "mutation" is
```
    for r in range(n, 0, -1):   ->   raise RuntimeError('mg-3946 MX')
                                     for r in range(n, 0, -1):
```
in `_width` — a bare `raise`, moving no quantity, catchable by no identity comparison. The demo,
as mg-3934 left it, printed:

```
MX   UNSEEN -- mg-3946's crash-vs-detection     exit 0 ok      exit 1 ok
       (no gate failure reported)
       --> exit 1 (expected 1)  OK
...
Demonstration complete.  1/6 mutations that NEITHER mg-60d3 nor
mg-5ad1 used are caught by the widened gate, and 1/6 of them were fatal to nothing before
it -- so the widening is not a patch on its own witnesses.
```

**Exit 0. "Caught by the widened gate." Nothing was caught; the instrument fell over.**

Two aggravating details, both in the same function:

* `stderr_tail` was captured only `if proc.returncode > 1` — so the traceback, the one artifact
  that distinguishes a crash from a failure, was **discarded in exactly the case where it is the
  evidence**. The `MX` row's stderr was recorded as `""`.
* The information needed to tell them apart was **already extracted and already printed**: the demo
  prints `(no gate failure reported)` one line above its own verdict. It was never asserted on.

### The repair

In `scripts/onethird_mg75f0_gate_class_closure_demo.py`:

* `PASS` for an expected-exit-1 case now requires the gate to have **reported at least one line
  under its own `CONTROL FAILURES` banner**, not merely to have exited 1.
* A row that exits 1 saying nothing is flagged `crashed_rather_than_failed`, printed as
  `*** THE GATE CRASHED, IT DID NOT FAIL ***`, listed in the report JSON, and fails the run.
* `stderr_tail` is kept unconditionally.
* The headline count (`N/N mutations … caught`) is computed over rows the gate *reported*, so the
  sentence and the assertion cannot drift apart.

The strengthening is **not speculative about today's rows**: the CI artifact from run
`30612714474` records 7–11 named control failures for every expected-exit-1 case, so it holds at
HEAD in the environment that matters. `crash-not-catch` is retained in the falsifier as a standing
regression control with its prediction flipped to 1 — revert the strengthening and it fails.

### Demonstrated against the subject with the defect still in it, and then against the repair

| run | subject | `crash-not-catch` | `control` |
|---|---|---|---|
| battery, 09:0x | the demo **as mg-3934 left it** | predicted 0 → **0**, `exit 1 ok`, "1/6 … caught" | 0 |
| re-run, 09:4x | the demo **with the mg-3946 repair** | predicted 1 → **1**, `exit 1 BAD`, DEMONSTRATION FAILED | **0** — the repair does not break the normal path |

The repaired run now prints the `RuntimeError: mg-3946 MX` traceback above the matrix, which the
`returncode > 1` guard had been throwing away.

## 3. The population of historical-SHA reads

The ticket's worry is precise: *the parent found one because it was in the FIRST failing step; a
second in a later step is masked by the first failure.* Two things make that worry answerable
rather than open.

**(a) Nothing was masked in the instance.** The mg-75f0 step was the **last** step in its job, so
no step ran after it to be hidden. Re-verified independently against run `30606216109` (`2697c07`,
from inside the red window): steps 5–7 — watchlist, probe battery, mg-60d3 demo — are all
`success`, and only step 8 is `failure`.

**(b) The population, named rather than counted**, by a route that shares no code with mg-3934's.
`scripts/onethird_mg3946_closure_demo_falsifier.py` PART 3/4 detects a git call by inspecting the
**arguments of `subprocess`/`os` calls in the parsed AST**, builds the import closure from the AST
rather than a regex, reads the **`run:` step bodies themselves** (which mg-3934 does not — it
extracts `scripts/*` invocations only, so a bare `git show` written straight into a step is outside
its detection), and decides whether a literal is a revision by **asking git**, not by a naming
convention.

| workflow | checkout | executes code that resolves a historical commit? | verdict |
|---|---|---|---|
| `gate-mutation-demo.yml` | `fetch-depth: 0` | **yes** — `onethird_mg75f0_gate_class_closure_demo.py` → `af7fc2df` | **FIXED** |
| `script-controls.yml` | unset (=1) | no — closure of 23 modules; the only git-calling member is `onethird_mg3934_ci_history_depth_control.py`, and no literal in it resolves to a commit | EXISTS, correct as-is |
| `lean.yml` | unset (=1) | no — executes no repo script | EXISTS, correct as-is |

No inline `git` in any step body of any workflow. **No second CI-executed historical-SHA read
exists — STILL BROKEN: none.**

The whole-`scripts/` pin population, which is the set mg-3934's property (B) actually gates on:

| script | pins | CI-executed |
|---|---|---|
| `onethird_mg4f9b_route_axis_probe.py` | `91fa25f`, `9fa4aaa`, `af7fc2df` | no |
| `onethird_mg75f0_gate_class_closure_demo.py` | `af7fc2df` | **yes** |
| `onethird_mgbd53_widening_audit_probe.py` | `af7fc2df` | no |

**5 literals, 3 distinct revisions, 3 scripts** — which is mg-3934's table exactly, and not
mg-3934's sentence about it (**F4**: "5 literals, 4 distinct revisions, 3 scripts", contradicted
nine lines later by "All three revisions"). All three are ancestors of `refs/remotes/origin/HEAD`.

**PART 4 (F6) makes the reachability question a control.** mg-3934's (B) asks `git rev-parse
--verify` **in the current checkout**, and its own KNOWN LIMITS says that is not the CI question:
`fetch-depth: 0` fetches *remote refs*, so an object present locally for a local-only reason — a
local branch, a reflog, a dangling commit — is still absent in CI. mg-3934 answered that by hand
("checked explicitly") and left it unmechanised. PART 4 asks it: every pin, is it an ancestor of
some `refs/remotes/*`? This repository makes the gap concrete — its local `refs/heads/main` points
at `af7fc2d`, ~20 commits behind `origin/main`, so *ancestor-of-local-`main`* answers **NO** for
`91fa25f` and `9fa4aaa` while *ancestor-of-`origin/main`* answers **yes**. Local ref state is not
the CI question, and only one of those two checks is.

**The two detectors disagree in both directions, and that is the point of running a second one.**
mg-3934's text route sees `af7fc2df` nested inside a longer string literal (it scans raw source);
the AST route does not (it sees only whole string constants). The AST route resolves 4–6 character
abbreviations and unquoted-adjacent literals; the text route requires 7–40 and quote adjacency.
Neither is a refinement of the other. On today's corpus they return the same three revisions.

## 4. Does a red result reach anybody?

**Plainly: no — and the SHA was the cause of this instance, not of the silence.** The ticket
asked for that sentence rather than a closed ticket, and it is the right sentence.

### 4.1 The consumer's audience, measured

`scripts/refinery_gate.sh` is the **only** reader of a GitHub Actions result anywhere in this
repository or on the fleet. Checked: no `workflow_run` trigger, no `schedule:` in any workflow, no
issue-on-failure step, no notifier, and no `gh run` invocation outside that one file (the only
other hits are historical run URLs quoted in docs). `pogo schedule list` has no entry that reads CI.

Where it prints is the refinery's `gate_output`. Who reads that field:

* `pogo refinery show <mr>` prints it — a **human**, by hand.
* The polecat merge protocol polls `pogo refinery show <id> --json … | jq -r .status` and reads
  **no other field**. `gate_output` *is* in the `--json` payload; nothing in the loop looks at it.
* pogod marks the item done and reaps the author within seconds of the merge landing, so there is
  no post-merge window in which the author would read it either.

So the workflow header's "That is the audience: the people whose commits can invalidate these
demonstrations, at the moment they merge one" describes a channel, not a reader. Corrected at both
sites (**F3**).

### 4.2 The consumer's first live firing was a FALSE RED (F2)

The readout has fired exactly twice, and one of the two was wrong:

| MR | printed | truth |
|---|---|---|
| `mr-d9m4fhitjv1tur4p9e3g` (mg-3934's own merge) | `*** failure as of 2026-07-31T05:13:36Z ***` | correct — run `30606216109` did fail |
| `mr-d9m4fr2tjv1tur4p9e40` (mg-069f, 08:24) | `*** ` *(empty)* ` as of 2026-07-31T07:13:45Z ***` + the full "it is red" paragraph | **wrong** — run `30612119957` was *in progress* and completed **success** |

Mechanism, reproduced live rather than inferred: `gh run list --limit=1` returns the latest run
**including an unfinished one**, and `gh --jq` interpolates a JSON `null` conclusion into a string
as `""`, never as `"null"`. The guard was `[ "${RUN%%<TAB>*}" = "null" ]`, which therefore cannot
fire; control falls to the `else` branch, `CONC` is empty, `"" != "success"`, and the red banner
prints. Confirmed against a live in-progress run:

```
first field = []  equals "null"? NO
```

The window is wide, not narrow: this gate runs ~10 min and the workflow it reports on runs
~16–21 min on the same commit, so a gate-touching merge is *usually* inside the run it is
reporting. **A consumer introduced because a permanently-red check trains readers to skip the
column, whose first act is to invent a red, is the same disease one layer out.**

Repaired: ask for the latest **completed** run (`--status=completed`, `.[0] // empty`), and report
any newer unfinished run separately as *not a conclusion yet* — because "the last completed run was
green" and "a newer run is still deciding" are different facts and a merge author needs both.

### 4.3 What would actually reach somebody

Not proposed here, and named so it is not mistaken for done: a `workflow_run`-triggered job that
mails `human` on `conclusion != success` for `main` would be the first mechanism in this chain that
makes somebody *look* rather than making red *visible to someone already looking*. That is a
repo-wide policy call, like the blocking question mg-7db4 declined, and it is not this ticket's.

## 5. Do not disturb

Verified **in CI at HEAD**, not locally — a full clone cannot reproduce the defect at all, so a
local pass is not evidence. Run [`30612714474`](https://github.com/drellem2/one_third_width_three/actions/runs/30612714474),
`bb1cb9b` on `main`, which is a *different* commit from the parent's acceptance run and therefore
independent evidence:

| step | conclusion | wall |
|---|---|---|
| `actions/checkout@v5` (`fetch-depth: 0`) | success | **2 s** |
| mg-3934 CI history-depth control | success | 1 s |
| mg-7db4 watchlist consistency | success | <1 s |
| mg-7db4 probe mutation battery | success | 4 m 26 s |
| mg-60d3 gate mutation demo | success | 3 m 11 s |
| mg-75f0 gate class-closure demo | success | 8 m 31 s |
| **job total** | **success** | **16 m 22 s** against the 75 min bound |

**All three earlier steps still execute and pass after the checkout change.** `Script controls`
is green on `bb1cb9b` as well.

**Clone cost.** `fetch-depth: 0` measured **2 s** here against **1 s** at depth 1 on the same
repository — a 1 s absolute increase on a 2.6 MiB / ~380-commit history, and 0.2% of the job.
mg-3934's estimate is confirmed on a second run. The cost is a constant per job, so it does not
grow with the demonstrations; it grows with the repository, and this repository is small.

The CI artifact from that run is also the evidence for §2: every expected-exit-1 case reported
between 7 and 11 named control failures, so the strengthened assertion added there holds in the
environment that matters and not merely on a developer's box.

## 6. The floor: one thing no list here named

The ticket asks for at least one audit target it does not name. **I chose the demo's own report
file, and the failure mode is F5.**

A `--only`/`--gates` subset run writes `data/onethird-mg75f0-gate-class-closure.json` at the same
path as a full run, with the same schema and no marker that it is a subset, and **exits 0**. It
also prints a headline computed with a numerator over the rows actually run and a denominator over
the full mutation set — this audit's own subset runs printed `1/5` and, with the crash row added,
`1/6`. Both times the committed record in this worktree was silently replaced by a two-row file,
and both times it had to be restored with `git checkout --`.

That is not hypothetical for this corpus: `885c1d1` is a commit whose entire subject is *"commit
mg-5ad1's probe record from an UNPINNED run, matching the refinery's own environment"* — the same
class of defect, one instrument over. The reason it matters here is that the committed report is
what a reader consults to learn what the demonstration showed, and a subset run makes it say
`ALL_PASS: true` over two rows while looking exactly like a run over eight.

**Left unfixed and named rather than fixed**, because it is the mg-75f0 instrument's own design and
outside this audit's remit to redesign: the honest repairs are either to refuse to write the
canonical path on a subset run, or to record the requested subset in the report and make the
headline quote its own denominator. Both are one-liners; neither is mine to choose.

## 7. Predictions, and the misses

Six exit codes predicted before running in the drift battery, six held. Three more predicted
outside it and all three held: the mg-3934 control at HEAD (0); the `(B)` census after this
audit's own script lands (7 literals in 4 files, since the falsifier itself names `af7fc2df` and
`9fa4aaa` in string form); and the shape of the `gh --jq` null (empty string, not `"null"`). Two
further predictions were made after the repair and are recorded in §2.

**No prediction was missed, and that is worth flagging rather than celebrating** — it means this
audit's instrument agreed with its author about what it would find, which is the weakness mg-75f0
names about its own M5/M6/M7/M9 rows. The two findings that were *not* predicted are the two that
matter most (**F1**, discovered while reading `run_case`, and **F2**, discovered by reading a live
`gate_output` rather than by predicting anything), and neither came from the battery.

## 8. What is not claimed

* **Not claimed: that the mg-75f0 demo is now known to be a good demonstration.** It is now known
  to be *falsifiable* — five drifts, five rejections — and its right column is now known to mean
  "the gate reported a failure" rather than "the process exited 1". Whether its seven mutations are
  a representative sample of mg-5ad1's class is a different question and this audit did not
  reopen it. mg-bd53 (`91fa25f`) already returned RED on that question.
* **Not claimed: that the SHA class is closed for revisions the corpus computes rather than writes
  down.** mg-3934 names this limit and it is real; PART 3's AST route does not close it either. A
  revision read from a file, an environment variable, or `git log` output is invisible to both
  detectors. The remedy `fetch-depth: 0` is nonetheless the same, so the exposure is detection.
* **Not claimed: that anybody will see a red run.** §4. The readout is repaired and more honest;
  it still requires a human to run `pogo refinery show` by hand, and nothing makes one.
* **Not claimed: that the falsifier runs anywhere automatically.** It is a hand-run audit
  instrument, like `mgbd53`'s and `mg4f9b`'s probes — 35 min for five cases, far outside the
  order-seconds rule that governs `script-controls.yml` and outside the "proofs about the checks
  belong in Actions" split `refinery_gate.sh` sets out. **So it is, today, a control nobody runs**,
  which is the disease this whole arc is about, and saying so is better than wiring a 35-minute
  battery into a merge path to avoid saying it. The one assertion that *did* need to run on every
  gate change was put where such things already run — inside the mg-75f0 demo itself, which
  `gate-mutation-demo.yml` executes.
* **Not audited:** the mathematics of the widening (mg-bd53's and mg-56be's remit), the mg-60d3
  demo, the mg-7db4 battery beyond confirming they still pass, and whether `lean.yml` is
  meaningfully covered at all — its last `lean/**` commit predates this arc entirely.
