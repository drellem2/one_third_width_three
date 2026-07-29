# CI for the Python controls — what runs, and the evidence it can fail

**mg-4ad1.** Status: **shipped and demonstrated red.**

## The gap this closes

Until 2026-07-29 the repository had exactly one workflow,
[`.github/workflows/lean.yml`](../.github/workflows/lean.yml), filtered on
`paths: ['lean/**', '.github/workflows/lean.yml']`. The last commit touching
`lean/` was `dad80db` on **2026-05-21**. Every commit after that — and there
were dozens — touched only `docs/`, `data/` and `scripts/`.

So CI had not run in over two months. Not a broken trigger: working exactly as
configured. The consequence is what matters — **every Python artifact committed
in that window shipped with no automated coverage of any kind**, including the
load-bearing ones:

| script | role |
| --- | --- |
| `onethird_mg0eac_primitive_delta_search.py` | the delta engine + the five/six-engine gate |
| `onethird_mg8489_fastq_gate_control.py` | the control **proving** that gate can fail |
| `onethird_mg8ff1_lemma32b_counterexample.py` | the n = 9 witness for the F1 repair |
| `onethird_mgc47a_width4_arena_count.py` | the arena counter + repaired `--budget` |
| `audit_mg0eac_*.py` | the independent audit's reproductions |

The mg-8489 control is the sharp case. It works — it was run by hand, 6/6,
exit 0. But nothing ran it automatically, so from the day it landed it
protected nothing unless a human remembered. **A control that is never invoked
is indistinguishable from a control that does not exist**, and it fails in the
reassuring direction: the file is present, it looks like coverage, and the next
reader assumes the engine is guarded.

This is the *population* variant of the defect class this repo has hit
repeatedly (`five_engine_check` not covering `fast_Q`; `--budget` checked only
between levels): the check is correct and its population of invocations is
empty.

## What now runs

[`.github/workflows/script-controls.yml`](../.github/workflows/script-controls.yml),
on push and pull_request touching `scripts/**`, `data/**`, `docs/**`, or the
workflow itself — i.e. the directories this repo actually commits to, which is
precisely the set `lean.yml` excludes.

Two steps, both order-1 s, both pure standard library, both already exiting
non-zero on failure:

1. **`onethird_mg8489_fastq_gate_control.py`** — corrupts `fast_Q` three ways
   and `Q_primary` once, requires `five_engine_check` to raise on each, and
   requires it green before and after patching. 6 rows.
2. **`onethird_mg8ff1_lemma32b_counterexample.py`** — re-derives `|Aut(P)| = 3`,
   `e(P) = 1431`, `δ(P) = 79/159` for the n = 9 witness rather than asserting
   them, so it also exercises `delta_of` from the primitive delta search.

### What deliberately stays out

The searches and the width-4 arena counter. The arena count alone is ~430 s at
n = 10 and the sweeps are far longer. **If a script has no fast self-check
mode, leave it out rather than inventing one** — a slow CI job that gets
disabled is a worse outcome than an honest gap.

## Evidence the workflow can turn red

A green badge that has never been observed red is the same defect one layer up.
Three runs on a scratch branch (`scratch-mg4ad1-cifail`, deleted afterwards),
each isolating one claim:

| run | commit touches | expected | result |
| --- | --- | --- | --- |
| [`30434646834`](https://github.com/drellem2/one_third_width_three/actions/runs/30434646834) | the workflow file only | runs, green | ✅ success, 12 s |
| [`30434671553`](https://github.com/drellem2/one_third_width_three/actions/runs/30434671553) | **`docs/` only** | runs, green | ✅ success, 9 s |
| [`30434716221`](https://github.com/drellem2/one_third_width_three/actions/runs/30434716221) | **`scripts/` only** | **runs, RED** | ❌ failure, 12 s |

Run 2 is the load-bearing one for the *trigger*: a commit touching nothing but
`docs/` — the exact case `lean.yml`'s filter excludes — started a run. A
workflow that is correct but not triggered by the relevant commits reproduces
the original defect.

Run 3 is the load-bearing one for the *control*. The break was not a
throwaway `exit 1`: it removed the M0 `fast_Q` comparison from
`five_engine_check`, reintroducing **exactly the mg-8489 defect** the control
exists to catch. The job failed at the `mg-8489 fast_Q gate control` step with

```
  uncorrupted (M0 + M1..M4 + MC)                 passed  must pass    OK
  fast_Q delta + 1e-6 (audit's probe)            passed  must RAISE   *** WRONG ***
  fast_Q delta OVERSTATED x1.001                 passed  must RAISE   *** WRONG ***
  fast_Q e(P) + 1                                passed  must RAISE   *** WRONG ***
  corrupt Q_primary + 1e-6                       RAISED  must RAISE   OK
  uncorrupted (post-patch restore)               passed  must pass    OK
  fast_Q gate control: FAIL (3/6 rows as required)
##[error]Process completed with exit code 1.
```

Note the `corrupt Q_primary` row stayed OK: the regression check correctly kept
passing while only the `fast_Q` coverage was removed. The failure is specific,
not a blanket crash.

## Adding a control later

Append a step to `script-controls.yml` only if the script is (a) fast, order
seconds; (b) self-contained — standard library, no network, no data fixtures
outside the repo; (c) self-verifying — it already exits non-zero on failure, so
CI does not need to parse its output. Then break it once on a scratch branch
and confirm the run goes red before trusting it.
