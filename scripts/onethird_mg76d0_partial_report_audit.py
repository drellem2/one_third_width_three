#!/usr/bin/env python3
"""mg-76d0 -- INDEPENDENT AUDIT of the mg-a471 partial-report repair (9072f34).

WHAT IS UNDER TEST.  mg-a471 closed mg-3946's F5 by claiming three compounding
defects were repaired together: a `--only`/`--gates` subset run of
`scripts/onethird_mg75f0_gate_class_closure_demo.py` could (1) overwrite the
COMMITTED report at `data/onethird-mg75f0-gate-class-closure.json` with an
unmarked partial one, (2) print a headline ratio whose numerator counted the
rows RUN and whose denominator counted the whole table, and (3) exit 0 over
both.  A repair can close one of three and leave another, so this file tests
each separately and records the three answers separately.

WHAT THIS FILE DOES NOT DO.  It does not re-do the repair and it does not edit
the subject.  Every check below runs the demo AS MERGED, from the repository
root, and reads three things back: the exit code, what exists at each of the
two report paths and with what digest, and the two ratio sentences the run
printed.  The canonical report is digested before and after EVERY check, so a
write to it is caught whether or not the run admits to one.

THE FLOOR (check X7).  The three defects above are all about a SUBSET run.  A
FULL run is not a subset, so none of the three repairs is in its path: it
writes the canonical report, in place, over the committed acceptance record
from `9fa4aaa`, and exits 0.  X7 measures that.  It restores the file with
`git checkout --` afterwards and records that it had to.

THIS INSTRUMENT'S OWN REPORT obeys the rule it is auditing -- the predecessor's
instrument recorded `cases_requested`/`partial_run` "so it does not ship the
defect it reports", and mg-a471 copied that into the demo; this copies it one
step further out.  A subset audit run (`--only X1,X7`) writes
`data/onethird-mg76d0-partial-report-audit.PARTIAL.json`, not the canonical
`data/onethird-mg76d0-partial-report-audit.json`; every report records
`checks_requested`, `full_battery`, `partial_run` and `IS_THE_AUDIT`; and an
unacknowledged subset audit exits 2.  `--partial-ok` acknowledges it.

Run:  /usr/bin/python3 scripts/onethird_mg76d0_partial_report_audit.py
      (numpy required -- the demo needs it; ~35 min, about 40 full gate runs)
      --only X1,X5          run a subset of the checks (PARTIAL, exit 2)
      --partial-ok          acknowledge the subset: 0/1 over the checks that ran
"""

import os
import re
import sys
import json
import time
import argparse
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEMO = os.path.join("scripts", "onethird_mg75f0_gate_class_closure_demo.py")
FALSIFIER = os.path.join("scripts",
                         "onethird_mg3946_closure_demo_falsifier.py")

# The subject's two paths, spelled here rather than imported, so that a rename
# in the subject shows up as a missing file in this audit instead of silently
# retargeting it.
CANON = os.path.join("data", "onethird-mg75f0-gate-class-closure.json")
PARTIAL = os.path.join("data",
                       "onethird-mg75f0-gate-class-closure.PARTIAL.json")

# The digest mg-a471's commit message asserts for the committed acceptance
# record.  Checked, not assumed: if the tree does not start here, every
# before/after comparison below is against a different baseline and the audit
# says so rather than reporting drift as a finding.
ASSERTED_CANON_SHA = ("39a4ca340ffeb74f2a9d78c60b4b147813b739633e"
                      "8fc785f76e225ec6c97318")

REPORT = os.path.join("data", "onethird-mg76d0-partial-report-audit.json")
PARTIAL_REPORT = os.path.join(
    "data", "onethird-mg76d0-partial-report-audit.PARTIAL.json")

PY = "/usr/bin/python3"       # the only interpreter on this host with numpy

# THREAD CAP, and why it is here rather than left to the default.  The gate is
# numpy-heavy and Accelerate will take every core it can see; two of these
# running at once on a shared host (this audit's, and another agent's) drove the
# load average past 200 and a single gate run from ~50 s to 14 min.  Capping the
# BLAS thread pool bounds the contention.  It changes wall-clock only: nothing
# below reads a duration as evidence, and an exit code, a SHA-256 and a printed
# ratio are all thread-count-invariant.
THREAD_CAP = {"VECLIB_MAXIMUM_THREADS": "3", "OMP_NUM_THREADS": "3",
              "OPENBLAS_NUM_THREADS": "3", "MKL_NUM_THREADS": "3",
              "NUMEXPR_NUM_THREADS": "3"}


# ------------------------------------------------------------------ checks ---
# `predict` is the pre-registered exit code from
# docs/OneThird-mg76d0-PartialReport-IndependentAudit-Predictions.md, committed
# before any of these ran.  It is not edited to match an observation.
CHECKS = [
    {"id": "X1", "cmd": [DEMO, "--only", "M9", "--gates", "widened"],
     "predict": 2,
     "asks": "the unacknowledged subset run mg-3946's audit was bitten by "
             "twice: exit code, output path, and both ratio sentences"},
    {"id": "X2", "cmd": [DEMO, "--only", "M9", "--gates", "widened",
                         "--partial-ok"],
     "predict": 0,
     "asks": "the acknowledged subset: does --partial-ok restore 0/1 over the "
             "rows that ran WITHOUT restoring the canonical path"},
    {"id": "X3", "cmd": [DEMO, "--only", "M3"],
     "predict": 2,
     "asks": "partial on the CASE axis only -- both gate columns run, so both "
             "ratios have a denominator and neither may quote the full table"},
    {"id": "X4", "cmd": [DEMO, "--gates", ""],
     "predict": 2,
     "asks": "an empty gate list: every case requested, no column run at all"},
    # mg-9a59 CLOSED THIS HOLE.  `predict: 0` is left EXACTLY as pre-registered
    # -- it was a correct prediction about the subject at 9072f34, it was
    # confirmed, and a prediction is not revised because a later commit changed
    # the world it was about.  So a re-run of this battery against main now
    # reports X5 in `predictions_missed` and this script exits 1.  THAT
    # DISAGREEMENT IS THE REPAIR LANDING, NOT A REGRESSION: the demo now exits
    # 2 with `ALL_PASS: false` and `n_gate_runs: 0`.  The standing control for
    # it is `onethird_mga471_partial_run_control.py`, property H, which is
    # order-seconds and wired into script-controls.yml.
    {"id": "X5", "cmd": [DEMO, "--gates", "", "--partial-ok"],
     "predict": 0,
     "asks": "PREDICTED HOLE -- an acknowledged run that exercises NOTHING.  "
             "Does it pass vacuously with ALL_PASS true over zero cases?  "
             "(CONFIRMED at 9072f34; CLOSED by mg-9a59, so a re-run now "
             "misses this prediction and that is the fix)"},
    {"id": "X6", "cmd": [DEMO, "--only", "NOPE", "--partial-ok"],
     "predict": 1,
     "asks": "PREDICTED HOLE -- --only is never validated against MUTATIONS, "
             "so an unknown row should KeyError rather than be rejected"},
    {"id": "X7", "cmd": [DEMO],
     "predict": 0,
     "asks": "THE FLOOR.  A FULL run is not a subset, so none of the three "
             "repairs is in its path: does it overwrite the committed "
             "acceptance record in place, exit 0, and say nothing?",
     "restores_canon": True},
    {"id": "X8", "cmd": [FALSIFIER],
     "predict": 0,
     "asks": "do-not-disturb: mg-3946's battery, six drifts with their exit "
             "codes predicted before mg-a471 existed and not revised by it"},
]


def sha256(path):
    full = os.path.join(REPO, path)
    if not os.path.exists(full):
        return None
    out = subprocess.run(["shasum", "-a", "256", full],
                         capture_output=True, text=True, cwd=REPO)
    return out.stdout.split()[0] if out.returncode == 0 else None


def git_status_data():
    out = subprocess.run(["git", "status", "--porcelain", "data/"],
                         capture_output=True, text=True, cwd=REPO)
    return [l for l in out.stdout.splitlines() if l.strip()]


def ratio_lines(stdout):
    """The sentences a reader actually takes the headline from.  Kept verbatim:
    the F5 defect was a SENTENCE whose two halves counted different things, so
    a summary of it would be summarising away the evidence."""
    keep = []
    for line in stdout.splitlines():
        if re.search(r"\b\d+/\d+\b", line) or "was not run" in line \
                or "PARTIAL" in line or line.startswith("wrote ") \
                or "Demonstration complete" in line \
                or "Exiting 2" in line or "--partial-ok was given" in line:
            keep.append(line.rstrip())
    return keep


def report_fields(path):
    """The five fields mg-a471 adds, read back off whatever landed."""
    full = os.path.join(REPO, path)
    if not os.path.exists(full):
        return None
    try:
        d = json.load(open(full))
    except Exception as e:                       # a truncated write is a result
        return {"UNPARSEABLE": str(e)}
    return {k: d.get(k, "<< ABSENT >>") for k in
            ("cases_requested", "gates_requested", "partial_run",
             "IS_THE_DEMONSTRATION", "ALL_PASS")} | {
        "n_cases": len(d.get("cases", [])),
        "unseen_mutations_run_widened": d.get("unseen_mutations_run_widened",
                                              "<< ABSENT >>"),
        "unseen_mutations_run_pre_widening": d.get(
            "unseen_mutations_run_pre_widening", "<< ABSENT >>"),
    }


def run_check(c):
    # Remove any PARTIAL left by an earlier check so that "the file exists
    # after this run" cannot be satisfied by a previous run's leftover -- the
    # path carries no per-invocation identity, which is itself finding A6.
    stale = os.path.join(REPO, PARTIAL)
    partial_before = sha256(PARTIAL)
    if os.path.exists(stale):
        os.remove(stale)

    canon_before = sha256(CANON)
    t0 = time.time()
    env = dict(os.environ) | THREAD_CAP
    proc = subprocess.run([PY] + c["cmd"], cwd=REPO, env=env,
                          capture_output=True, text=True)
    secs = round(time.time() - t0, 1)
    canon_after = sha256(CANON)

    r = {
        "id": c["id"],
        "asks": c["asks"],
        "argv": c["cmd"],
        "predicted_exit": c["predict"],
        "exit": proc.returncode,
        "PREDICTION_HELD": proc.returncode == c["predict"],
        "seconds": secs,
        "canonical_sha_before": canon_before,
        "canonical_sha_after": canon_after,
        "canonical_path_written": canon_before != canon_after,
        "partial_path_exists_after": os.path.exists(stale),
        "partial_sha_after": sha256(PARTIAL),
        "partial_sha_of_previous_check": partial_before,
        "canonical_report_fields": None,
        "partial_report_fields": report_fields(PARTIAL),
        "headline_lines": ratio_lines(proc.stdout),
        "stderr_tail": proc.stderr.strip().splitlines()[-4:],
        "git_status_data_after": git_status_data(),
        "canonical_restored_by_this_audit": False,
    }
    if r["canonical_path_written"]:
        r["canonical_report_fields"] = report_fields(CANON)
    if c.get("restores_canon") and r["canonical_path_written"]:
        subprocess.run(["git", "checkout", "--", CANON], cwd=REPO, check=True)
        r["canonical_restored_by_this_audit"] = True
        r["canonical_sha_after_restore"] = sha256(CANON)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="",
                    help="comma-separated check ids, e.g. X1,X5")
    ap.add_argument("--partial-ok", action="store_true",
                    help="acknowledge a subset audit: answer 0/1 over the "
                         "checks that RAN instead of exiting 2")
    args = ap.parse_args()

    all_ids = [c["id"] for c in CHECKS]
    wanted = ([i for i in args.only.split(",") if i] if args.only else all_ids)
    unknown = [i for i in wanted if i not in all_ids]
    if unknown:
        # The defect X6 predicts in the subject, refused here rather than
        # reproduced: an unrecognised selector is rejected by name, before any
        # work, instead of KeyErrorring five minutes in.
        raise SystemExit(f"unknown check id(s): {','.join(unknown)}.  "
                         f"known: {','.join(all_ids)}")
    partial_run = set(wanted) != set(all_ids)

    print("=" * 78)
    print("mg-76d0 -- INDEPENDENT AUDIT of the mg-a471 partial-report repair")
    print("=" * 78)
    start_sha = sha256(CANON)
    print(f"  committed report digest at start : {start_sha}")
    print(f"  mg-a471's commit message asserts : {ASSERTED_CANON_SHA}")
    baseline_agrees = (start_sha == ASSERTED_CANON_SHA)
    print(f"  they agree                       : {baseline_agrees}")
    if not baseline_agrees:
        print("  !! the baseline is not the one mg-a471 measured against; "
              "before/after comparisons below are still sound, but the "
              "asserted digest is not what is on disk")
    if partial_run:
        print()
        print("  *** PARTIAL AUDIT -- NOT THE BATTERY (mg-76d0) ***")
        print(f"  checks this run will run : {','.join(wanted)}")
        print(f"  the full battery is      : {','.join(all_ids)}")
        print(f"  report goes to           : {PARTIAL_REPORT}")
        if not args.partial_ok:
            print("  this run will exit 2 -- pass --partial-ok if you meant "
                  "to ask only about the checks you named.")

    # Cheapest first, and the order is documented rather than implicit: X4/X5/X6
    # run zero gate runs and answer in milliseconds, X1/X2 run two each, X3 four,
    # X7 sixteen and X8 fourteen.  Nothing below depends on the order -- each
    # check digests both report paths for itself -- so this only decides how
    # soon a result exists to read.
    order = ["X4", "X5", "X6", "X1", "X2", "X3", "X7", "X8"]
    results = []
    for c in sorted(CHECKS, key=lambda c: order.index(c["id"])):
        if c["id"] not in wanted:
            continue
        print()
        print("-" * 78)
        print(f"CHECK {c['id']}   predict exit {c['predict']}   "
              f"{' '.join(c['cmd'])}")
        print(f"      {c['asks']}")
        print("-" * 78, flush=True)
        r = run_check(c)
        results.append(r)
        print(f"      --> exit {r['exit']} (predicted {r['predicted_exit']})  "
              f"{'HELD' if r['PREDICTION_HELD'] else '*** MISSED ***'}"
              f"   {r['seconds']}s")
        print(f"      canonical path written by this run : "
              f"{r['canonical_path_written']}")
        print(f"      PARTIAL path exists after          : "
              f"{r['partial_path_exists_after']}")
        for line in r["headline_lines"]:
            print(f"      | {line}")
        if r["canonical_restored_by_this_audit"]:
            print("      *** the committed record was overwritten by this "
                  "run and had to be restored with `git checkout --` ***")
        sys.stdout.flush()

    missed = [r["id"] for r in results if not r["PREDICTION_HELD"]]
    wrote_canon = [r["id"] for r in results if r["canonical_path_written"]]

    report = {
        "what": "mg-76d0 independent audit of the mg-a471 partial-report "
                "repair: can a subset run still overwrite the canonical "
                "report, print a cross-population ratio, or exit 0 -- each "
                "tested separately",
        "subject_commit": "9072f34",
        # What THIS run ran, first in the file, for the same reason mg-a471
        # put it first in the demo's.
        "checks_requested": wanted,
        "full_battery": all_ids,
        "partial_run": partial_run,
        "IS_THE_AUDIT": not partial_run,
        "canonical_report_path": CANON,
        "canonical_sha_at_start": start_sha,
        "canonical_sha_asserted_by_mg_a471": ASSERTED_CANON_SHA,
        "baseline_agrees_with_mg_a471": baseline_agrees,
        "checks": results,
        "predictions_missed": missed,
        "checks_that_wrote_the_canonical_path": wrote_canon,
        # mg-9a59.  THIS INSTRUMENT CARRIED THE DEFECT IT REPORTED.  `--only ","`
        # selects no checks -- the list comprehension drops empty ids and the
        # unknown-id guard has nothing to reject -- so `missed` was empty
        # because nothing ran, `ALL_PREDICTIONS_HELD` was true over zero checks,
        # and with `--partial-ok` this audit exited 0.  The same shape as X5,
        # in the instrument that found X5.  The count is now on the artifact and
        # the verdict is conjoined with there being something to hold.
        "n_checks_run": len(results),
        "ALL_PREDICTIONS_HELD": bool(results) and not missed,
    }
    out = os.path.join(REPO, PARTIAL_REPORT if partial_run else REPORT)
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {os.path.relpath(out, REPO)}")
    if partial_run:
        print(f"      PARTIAL -- {REPORT} was neither written nor read.")

    print()
    print("=" * 78)
    print(f"predictions held : {len(results) - len(missed)}/{len(results)} "
          f"of the checks that RAN ({','.join(r['id'] for r in results)})")
    print(f"missed           : {','.join(missed) if missed else 'none'}")
    print(f"wrote the canonical report : "
          f"{','.join(wrote_canon) if wrote_canon else 'none'}")
    print("=" * 78)

    # mg-9a59, and it precedes every other verdict for the same reason it does
    # in the demo: over zero checks there is no verdict to give.  --partial-ok
    # is not consulted -- it acknowledges a SUBSET of the battery and answers
    # over the checks that RAN, and here none did.
    if not results:
        print("ZERO CHECKS RAN -- THIS AUDIT MEASURED NOTHING (mg-9a59).  "
              "ALL_PREDICTIONS_HELD is\nwritten FALSE, not "
              "true-over-an-empty-list.  Exiting 2 even with --partial-ok.")
        return 2

    if missed:
        return 1
    if partial_run:
        if args.partial_ok:
            print("--partial-ok was given: exiting 0 on the checks that ran.")
            return 0
        print("Exiting 2: a subset audit is not the battery.")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
