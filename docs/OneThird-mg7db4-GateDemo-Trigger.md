# mg-7db4 — the gate-mutation demonstration gets a trigger, and the trigger gets coverage

**Ticket:** mg-7db4, filed as an ownership problem and rewritten by pm-onethird on 2026-07-30 into
two required halves after the mg-5ad1 audit landed.
**Depends on:** mg-5ad1 (`docs/OneThird-mg60d3-GateRepair-IndependentAudit.md`, merged `c48d238`).
**Does not close:** mg-75f0 (widen the gate's identity conjunction past 4 of 22 reference fields).

---

## §0 — What was wrong, in one paragraph

`.github/workflows/script-controls.yml` gated the delta-engine controls. Its comment excluded
`scripts/onethird_mg60d3_gate_mutation_demo.py` — the proof those controls can still *fail* — for a
defensible reason (six full gate runs, ~11 min, against an order-seconds rule) and closed with
*"run it on demand when the gate changes."* That sentence named no owner and no mechanism. mg-5ad1
§4 confirmed the exclusion from the workflow source rather than the comment and found the
instruction on **no executable path**: four sequential human steps had to occur for the demo ever to
run again, and every one of them fails silently, because a control that has stopped being able to
fire prints nothing and exits 0.

The audit then found something worse, which is why this ticket has two halves: **scheduling the demo
would not have helped much**. Its `EXPECTED` is a hardcoded 2×3 dict over `{none, M1, M2}`. It is a
regression test on the two repairs already made, not a blindness test — and the auditor wrote two
further one-line mutations (M3, M4) that sail through the repaired gate printing *"All controls and
identity checks PASSED."*

---

## §1 — What was built

Two jobs, one paths list, stated twice because the visible copy and the blocking copy cannot share a
file, plus a third check whose only job is to stop those two copies from drifting.

| piece | file | when it runs | cost |
|---|---|---|---|
| **Trigger, visible** | `.github/workflows/gate-mutation-demo.yml` | push/PR touching a watched path | ~17 min, only then |
| **Trigger, blocking** | `scripts/refinery_gate.sh` + `.pogo/refinery.toml` | every refinery merge; heavy path only on a watched path | milliseconds otherwise |
| *(see §1.4 for what the blocking layer deliberately does **not** run)* | | | |
| **Anti-drift** | `scripts/onethird_mg7db4_watchlist_consistency.py` | every commit (fast gate) + every merge | milliseconds |
| **Standing blindness check** | `scripts/onethird_mg5ad1_gate_blindspot_probe.py` | every commit (fast gate) | ~40 s |
| **Proof the standing check can fail** | `scripts/onethird_mg7db4_probe_mutation_battery.py` | watched paths only | ~6 min |
| **M1/M2 regression** | `scripts/onethird_mg60d3_gate_mutation_demo.py` | watched paths only | ~11 min |

### 1.1 Why the trigger is stated twice

GitHub Actions **cannot enforce anything in this repo.** Checked, not assumed:

```
$ gh api repos/drellem2/one_third_width_three/branches/main/protection
{"message":"Branch not protected", ... "status":"404"}
$ gh api repos/drellem2/one_third_width_three/rulesets
[]
```

Merges are performed by the pogo refinery, which rebases the branch and fast-forwards straight to
`main` without ever reading a check run. A branch mutating the gate would merge while its Actions
run was still starting. Requiring the check on GitHub instead is not available: the refinery pushes
to `main` directly rather than through a PR, so branch protection would block *every* merge in this
repo — a strictly worse outcome than the one being fixed.

So the paths filter also exists at the point where the merge decision is actually made. Before this
ticket the repo had **no refinery gate at all** — no `build.sh`, no `test.sh`, no
`.pogo/refinery.toml` — so nothing stood between a branch and `main`.

### 1.2 Why the duplication is safe

`onethird_mg7db4_watchlist_consistency.py` parses both copies and fails if they disagree. It also
derives the **transitive import closure** of every corpus module the two jobs execute and fails if
the watchlist has stopped naming one — so adding an import to the gated instrument, which moves a
gate-asserted quantity into an unwatched file, is a build failure rather than a silent hole. It
carries five synthetic drifts as a self-test, every one of which must be caught for the script to
exit 0; a consistency check that has never been shown to fail is the defect this ticket is about,
one level further up.

### 1.3 The order-seconds rule is not violated

`script-controls.yml` opens by requiring its steps to be order-seconds. An ordinary commit — a doc,
a data drop, a new probe — pays **nothing** for the two heavy demonstrations: the paths filter does
not match, and the refinery gate is a `git diff` and a `grep`. Only commits that can invalidate the
demonstrations pay for them. What the fast gate did gain is the blindness probe (~40 s) and the
consistency check (milliseconds), which is what pm-onethird's scope change asked for and is within
the rule.

### 1.4 What the blocking layer does not run, and why — measured, not preferred

The first version of `refinery_gate.sh` ran the battery in the blocking gate too. Its own MR then sat
in the refinery **22 minutes** and held the queue for every other author on the fleet, while a
concurrent 25-minute demonstration (mg-75f0's) on the same host stretched each gate run to roughly
ten times its uncontended cost. The mayor asked whether that was expected. It was not, and the right
response was not a bigger timeout on its own.

A blocking gate long enough that people want it bypassed has a shorter life expectancy than the
defect it guards — which is this ticket's own failure mode, arriving one layer further out. So:

| layer | runs | rationale |
|---|---|---|
| **blocking** (refinery) | watchlist consistency; mg-5ad1 probe; **mg-60d3 demo** | the ticket's named property is that a gate change cannot *merge* without the demo having run |
| **informational** (Actions) | + mg-7db4 battery; + mg-75f0 closure demo | these are proofs *about* the checks, not checks on the change |

Agreed with mg-75f0 and applied to my instrument as well as theirs. The gate timeout is `90m`, not
`45m`: on a busy host, contention alone would have produced a spurious failure, and a gate that fails
for reasons unrelated to the change teaches authors that the gate is noise.

---

## §2 — HALF TWO, and the finding that matters more than the job

pm-onethird's instruction was to wire in `onethird_mg5ad1_gate_blindspot_probe.py` because *"Part B
is the reference-field census parsed out of the gate source so it cannot drift from the gate"*, and
to demonstrate the scheduled check failing on a mutation that is **not** M1 or M2.

### 2.1 Measured first: as committed, the probe caught neither M3 nor M4

Before wiring anything in, both audit mutations were rebuilt source-level in an isolated copy of
`scripts/` + `data/`, with an anchor assertion (exactly one occurrence before, exactly one after),
and the **committed** probe run against each:

| mutation | one-line change | committed probe |
|---|---|---|
| **M3** | `bk_frozen_pair`: `min(` → `max(` at the Theorem-E selector | **exit 0 — NOT caught** |
| **M4** | `projector_U`: `s > max(tol, 1e-10)` → `s > 0.0` | **exit 0 — NOT caught** |

So wiring the probe in unchanged would have shipped something green that misses the audit's own
primary witness. Reporting that was worth more than shipping it, which is what the ticket said.

### 2.1a And Part B could not see its own repair being removed

The battery in §2.3 was built to prove the probe's checks fire. On its first run, one row that was
expected to be caught was not: **deleting `match_bk_lambda2` from the gate's `_identity_row_ok`** —
the mg-09ea F3 repair, reverted, one line — left the probe at **exit 0**.

Part B scans a 240-character window after each `rec["match_*"] = ` to find the `ref[...]` lookup that
assignment compares against. In the gate as committed, `match_delta` and `match_bk_lambda2` are
adjacent lines, so the window opened at `match_delta` ran past the end of its own statement and swept
up `ref["bk_lambda2"]` from the line below. The census therefore reported `bk_lambda2` as *compared*
while the conjunction no longer compared it.

Part B makes exactly one assertion — that the F3 repair is present — and it could not detect the F3
repair being removed. That is the reason pm-onethird gave for wiring this probe in, so wiring it in
unfixed would have been shipping green. The window is now cut at the next `rec["match_`; the census
on the unmutated gate is unchanged at 4 of 22 fields, and the reverted-F3 mutation is caught.

**Both of §2.1a and §2.2 were found by building the battery, not by reading the probe.** That is the
argument for the battery being a committed, re-running artifact rather than a one-off check.

*Coordination note, recorded because the code will move.* mg-75f0 is rewriting Part B to import the
gate and **call** its comparison function rather than parse its source, which removes the window
class of bug entirely rather than bounding it. When that lands, the fix in this repo's history
disappears from the file. The finding is the durable part and it belongs here: **a census that parses
the thing it censuses can be defeated by the source layout of that thing**, silently, in the exact
case it exists to detect. That is the argument for the call-based design, and it was measured, not
predicted.

### 2.2 Why M3 got through, and the one-line repair

Part C of the probe, as mg-5ad1 committed it, recomputed `argmin` over the pair list **itself** and
compared that to the committed reference:

```python
pairs = [pc for pc in bk_frozen_pair(Ps[i])["pairs"] if pc["ratio"] is not None]
lo = min(pairs, key=lambda pc: pc["ratio"])
agrees = [int(lo["x"]), int(lo["y"])] == committed      # never reads res["frozen"]
```

M3 flips the selector **inside** `bk_frozen_pair`. The pair *list* is untouched, so Part C's own
`argmin` is untouched, so `agrees` stays `True`. The probe printed *"a comparison IS available"* and
did not make it — **the F3 shape verbatim, in the file written to report the F3 shape.**

mg-7db4 makes the comparison: Part C now also reads `bk_frozen_pair(P)["frozen"]`, the value the
gate actually consumes, and asserts it equals the committed `frozen_pair`. New `sel. ok` column,
5/5 `True` on the unmutated corpus. This guards **one** of the eighteen uncompared reference
fields — the one Part C was already about — and deliberately does not build the general
census-and-compare, which is mg-75f0's ticket and needs its own audit.

### 2.3 The catch matrix, executable

`scripts/onethird_mg7db4_probe_mutation_battery.py` runs the standing check against eight one-line
mutations and asserts the outcome of each, **including the rows nothing catches**. Those rows expect
exit 0. If a later ticket closes one, the battery fails and says so — a coverage table that improves
silently is a coverage table that is wrong.

Measured, `/usr/bin/python3 scripts/onethird_mg7db4_probe_mutation_battery.py`, exit 0, eight of
eight rows as asserted. Committed at `data/onethird-mg7db4-probe-mutation-battery.json`.

| row | one-line mutation | file | standing check |
|---|---|---|---|
| `baseline` | none | — | passes (no false positive) |
| `M3` | Theorem-E frozen-pair selector `min(` → `max(` | `mg8b64` transport probe | **CAUGHT** (Part C, mg-7db4 column) |
| `N1` | Bernoulli variance `p(1-p)` → `p` in `bk_pair_cut` | `mg8b64` transport probe | **CAUGHT** (Part C, mg-5ad1's own check) |
| `N2` | gate drops `match_bk_lambda2` from `_identity_row_ok` | the gate | **CAUGHT** (Part B, after §2.1a) |
| `N4` | committed reference row for `enum-n7-#3` edited to agree with a mutated instrument | the mg-8b64 dataset | **CAUGHT** (Part C) |
| `M4` | `projector_U` rank filter `s > max(tol, 1e-10)` → `s > 0.0` | `mg4a86` sdquant overlap | not caught — §3.1 |
| `N3` | gate drops the `c_min` clause from `_antichain_row_ok` | the gate | not caught by the fast gate; **caught by the mg-60d3 demonstration** |
| `N5` | BK step `1/(2(n−1))` → `1/(n−1)` (= mg-09ea's M1) | `mg4a86` target audit | not caught by the fast gate; **caught by the mg-60d3 demonstration** |

`N3` and `N5` are the reason both jobs exist: neither instrument subsumes the other. `M3` is a
mutation only the probe sees; `N3` and `N5` are mutations only the demonstration sees. A claim that
either one alone is sufficient would be false, and this table is what makes that checkable.

Every mutation is applied source-level to an isolated copy of `scripts/` + `data/` under a temporary
directory, with an anchor assertion — exactly one occurrence before, exactly one after — so a
mutation that silently fails to apply is a hard error rather than a spurious "uncaught" row. `N4` is
row-scoped through the JSON rather than textual, because `"frozen_pair": [3, 5]` occurs at 54 rows of
the committed dataset and a textual replace would rewrite all of them.

### 2.4 The demonstration mutation is not one the guard was built from

`N1` is the row that answers the revised acceptance without circularity. It is neither M1, M2, M3 nor
M4: the Bernoulli variance `p(1-p)` collapsed to `p` in `bk_pair_cut`, a plausible slip. It moves the
ratio non-uniformly, so **Part C's original comparison** — written by mg-5ad1's author, who had never
seen this mutation — fires on it. The guard predates the mutation.

The fast CI gate itself (`onethird_mg2c34_n7_overlap_test.py --no-sweep`) is **blind** to N1: it
compares `num_LE`, `lambda_std`, `delta` and `bk_lambda2`, none of which move. So the demonstration
branch is a case where the gate prints PASSED and the new standing check prints FAILED.

### 2.5 The demonstration, on GitHub, on a pushed branch

Branch `polecat-7db4-mutation-probe` = this MR + N1 and nothing else. Both new mechanisms fired and
failed; the pre-existing gate did not notice.

**Run 30513056335, `Script controls`, conclusion `failure`:**

```
success  mg-8489 fast_Q gate control (can the engine gate fail?)
success  mg-8ff1 Lemma 3.2b counterexample (n=9 witness)
success  mg-2c34 SD-quant overlap controls (can the instrument fail?)   <- BLIND to N1
success  mg-7db4 watchlist consistency (is the trigger still complete?)
failure  mg-5ad1 gate blindspot probe (is the gate blind anywhere?)     <- CAUGHT
```

**Run 30513056294, `Gate mutation demo`, conclusion `failure` after 49 s** — the paths filter fired
on a commit touching only `scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py`, and the
battery refused to proceed:

```
- enum-n7-#3: bk_frozen_pair() RETURNS [0, 3], committed reference frozen_pair is [3, 5]
  -- the Theorem-E pair ledger claim 8 rests on has moved, and no control in
     script-controls.yml can see it
...
The unmutated probe does not pass, so no row below means anything.
```

On this MR's own branch, unmutated, both workflows are green — so the failures above are the
mutation, not the mechanism. The `Script controls` job on `polecat-7db4` ran in **1 m 12 s** with
both new steps included, against 41–64 s before: the probe costs ~30 s on a hosted runner, which is
what pm-onethird estimated and is inside the order-seconds rule.

The demonstration mutation is **N1**, not M1, M2, M3 or M4. The check that caught it was written by
mg-5ad1's author against a mutation they had never seen.

---

## §3 — What is still not covered

Stated plainly, because the alternative is a green tick that means less than it looks like.

1. **M4 is caught by nothing** — not by the gate's controls (structurally: enlarging `U` can only
   increase overlap, so CONTROL B survives; CONTROL C builds its own subspace; CHECK-0 shares
   `projector_U`), and not by the probe, which rebuilds its basis from definitions and never imports
   `projector_U`. It is on the record as an expected-exit-0 row in the battery.
2. **The gate compares 4 of 22 reference fields.** mg-75f0. Not touched here.
3. **The rest of `script-controls.yml` is advisory in this repo.** The mg-8489, mg-8ff1, mg-2c34 and
   mg-5ad1 steps run on Actions only, and Actions does not block a refinery merge. Mirroring the
   whole fast gate into `refinery_gate.sh` would add minutes to every merge for every author; that is
   a repo-wide policy call, not this ticket's. Recorded rather than fixed silently.
4. **The demo remains an M1/M2 regression test.** It is labelled as such in both workflows. It is
   kept because it is not subsumed: the battery's `N3` and `N5` rows are mutations only the demo
   catches.

---

## §4 — Reproducing

```
python3 scripts/onethird_mg7db4_watchlist_consistency.py          # ms, no numpy
/usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py  # ~40 s
/usr/bin/python3 scripts/onethird_mg7db4_probe_mutation_battery.py # ~6 min
/usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py     # ~11 min
./scripts/refinery_gate.sh                                         # what the merge runs
GATE_DEMO_FORCE=1 ./scripts/refinery_gate.sh                       # heavy path on demand
```

Bare `python3` on the fleet host has no numpy; `/usr/bin/python3` does. `refinery_gate.sh` resolves
this itself and **fails** rather than skipping if no interpreter with numpy is found.

Committed outputs: `data/onethird-mg5ad1-gate-blindspot-probe.json`,
`data/onethird-mg7db4-probe-mutation-battery.json`,
`data/onethird-mg60d3-gate-mutation-demo.json`.
