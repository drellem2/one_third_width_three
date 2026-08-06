#!/usr/bin/env python3
"""
mg-856d -- WHICH OF THE 17 WATCHED PATHS CAN ACTUALLY CHANGE WHAT THE BLOCKING
GATE ASSERTS?

THE QUESTION THIS ANSWERS, and why it is not the one the watchlist answers.
`scripts/onethird_mg7db4_watchlist_consistency.py` checks that the watchlist is
CONSISTENT: the two copies agree, it contains the mechanism, and it covers the
import closure of the gated instruments and the datasets they read.  All three
are properties of the LIST.  None of them asks the question a cost decision
needs: if I edit watched path P, can the expensive demonstration the edit
triggers come out differently?

For a path in the derived closure the answer is yes by construction -- that is
what "closure" means.  For a path in `MECHANISM` the answer is asserted by hand
and has never been measured.  `.github/workflows/script-controls.yml` is one of
those, and it is the second entry in the list.

HOW IT MEASURES.  Each instrument is run in a subprocess under a `sitecustomize`
that wraps `builtins.open`, `io.open` and `os.open`, and records every path
inside the repository that is opened for READING.  `subprocess.Popen` is wrapped
too, so a `git show <rev>:<path>` is recorded as an argv observation, separately
-- reading a file AT A REVISION is not sensitivity to the file's current bytes,
and conflating the two would overstate coverage.  `PYTHONPATH` and the log path
are inherited, so an instrument that shells out to another interpreter is traced
as well.

POSITIVE CONTROL, because a tracer that sees nothing and an instrument that
reads nothing produce the same report.  Before any verdict is printed, the trace
must contain at least one path known to be read: the gated instrument
`scripts/onethird_mg2c34_n7_overlap_test.py` and the committed dataset
`data/onethird-mg8b64-L1b-bk-transport-transfer.json`.  If either is missing the
probe exits non-zero and prints NOTHING about sensitivity -- a blind instrument
reporting "not read" for all 17 paths is the exact defect this repository has
spent two days auditing, and it would be a very convincing one.

WHAT IT DOES NOT ESTABLISH, stated so a NOT-READ row is not over-read.  "The
instrument never opened this file on THIS input" is not "no input exists on
which it would".  The instruments here are deterministic and take no arguments
on the path the gate runs them, so the single observed trace is the whole of
their behaviour in the gate -- but a future instrument with a data-dependent
read would need this re-run, which is why this is a probe with a recorded date
and not a standing control.

Run:
  /usr/bin/python3 scripts/onethird_mg856d_watch_sensitivity_probe.py [--fast]

  --fast   trace only the order-seconds instruments (skip the ~11-minute
           mg-60d3 demo).  The report says which instruments were traced; a
           NOT-READ verdict from a --fast run covers less and says so.

Writes data/onethird-mg856d-watch-sensitivity.json.  Exits non-zero if the
positive control fails.
"""

import json
import os
import re
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GATE_SH = os.path.join(REPO, "scripts", "refinery_gate.sh")
OUT = os.path.join(REPO, "data", "onethird-mg856d-watch-sensitivity.json")

# The instruments the BLOCKING gate runs, in the order refinery_gate.sh runs
# them.  This is the population the cost question is about: the Actions-only
# demonstrations (mg-7db4 battery, mg-75f0 closure demo) do not hold the
# refinery's serial slot, so they are out of scope here and named as excluded.
BLOCKING = [
    ("mg-7db4 watchlist consistency",
     "scripts/onethird_mg7db4_watchlist_consistency.py", True),
    ("mg-5ad1 gate blindspot probe",
     "scripts/onethird_mg5ad1_gate_blindspot_probe.py", True),
    ("mg-60d3 gate mutation demo",
     "scripts/onethird_mg60d3_gate_mutation_demo.py", False),   # not --fast
]

# Two paths the gate demonstrably reads.  If neither shows up the tracer is
# broken and every "not read" below would be a false negative.
POSITIVE_CONTROL = [
    "scripts/onethird_mg2c34_n7_overlap_test.py",
    "data/onethird-mg8b64-L1b-bk-transport-transfer.json",
]

_SITECUSTOMIZE = r'''
import builtins, io, os, sys
_LOG = os.environ.get("MG856D_TRACE")
if _LOG:
    _ROOT = os.environ.get("MG856D_REPO", "")
    def _emit(kind, payload):
        try:
            with open(_LOG, "a") as fh:
                fh.write("%s\t%s\n" % (kind, payload))
        except Exception:
            pass
    def _rel(p):
        try:
            p = os.path.realpath(str(p))
        except Exception:
            return None
        root = os.path.realpath(_ROOT)
        if p.startswith(root + os.sep):
            return p[len(root) + 1:]
        return None
    _open = builtins.open
    def open(file, mode="r", *a, **kw):
        r = _rel(file)
        if r is not None and "w" not in str(mode) and "a" not in str(mode):
            _emit("open", r)
        return _open(file, mode, *a, **kw)
    builtins.open = open
    io.open = open
    _osopen = os.open
    def _osopen_w(path, flags, *a, **kw):
        r = _rel(path)
        if r is not None and not (flags & (os.O_WRONLY | os.O_RDWR)):
            _emit("open", r)
        return _osopen(path, flags, *a, **kw)
    os.open = _osopen_w
    import subprocess as _sp
    _Popen = _sp.Popen
    class Popen(_Popen):
        def __init__(self, args, *a, **kw):
            try:
                _emit("argv", " ".join(args) if isinstance(args, (list, tuple))
                      else str(args))
            except Exception:
                pass
            _Popen.__init__(self, args, *a, **kw)
    _sp.Popen = Popen
'''


def parse_watchlist():
    with open(GATE_SH) as f:
        m = re.search(r"^WATCHED='([^']*)'", f.read(), re.M)
    return [l.strip() for l in m.group(1).splitlines() if l.strip()]


def trace(rel_script, tracedir, log):
    env = dict(os.environ)
    env["PYTHONPATH"] = tracedir + os.pathsep + env.get("PYTHONPATH", "")
    env["MG856D_TRACE"] = log
    env["MG856D_REPO"] = REPO
    t0 = time.time()
    p = subprocess.run([sys.executable, rel_script], cwd=REPO, env=env,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return p.returncode, time.time() - t0


def main():
    fast = "--fast" in sys.argv
    watched = parse_watchlist()

    tracedir = os.path.join(REPO, ".mg856d-trace")
    os.makedirs(tracedir, exist_ok=True)
    with open(os.path.join(tracedir, "sitecustomize.py"), "w") as f:
        f.write(_SITECUSTOMIZE)

    reads, argvs, ran, skipped = set(), [], [], []
    print("=" * 78)
    print("mg-856d watch-sensitivity probe")
    print("POPULATION: the %d paths in WATCHED.  GRAIN: one path." % len(watched))
    print("INSTRUMENTS: the ones scripts/refinery_gate.sh runs (the BLOCKING")
    print("             layer).  The Actions-only mg-7db4 battery and mg-75f0")
    print("             closure demo are excluded: they do not hold the")
    print("             refinery's serial slot, which is what costs.")
    print("=" * 78)
    for name, rel, in_fast in BLOCKING:
        if fast and not in_fast:
            skipped.append(name)
            print("  %-46s SKIPPED (--fast)" % name)
            continue
        log = os.path.join(tracedir, "trace-%s.tsv" % os.path.basename(rel))
        if os.path.exists(log):
            os.remove(log)
        rc, secs = trace(rel, tracedir, log)
        n = 0
        if os.path.exists(log):
            with open(log) as f:
                for line in f:
                    kind, _, payload = line.rstrip("\n").partition("\t")
                    if kind == "open":
                        reads.add(payload)
                        n += 1
                    elif kind == "argv":
                        argvs.append(payload)
        ran.append(name)
        print("  %-46s %6.1fs  rc=%s  %d repo reads" % (name, secs, rc, n))

    print()
    missed = [p for p in POSITIVE_CONTROL if p not in reads]
    if missed:
        print("POSITIVE CONTROL FAILED -- the tracer did not observe %s." % missed)
        print("Every 'not read' verdict this probe could print would be a false")
        print("negative, so it prints none.")
        return 1
    print("positive control: OK -- the tracer observed %s"
          % ", ".join(POSITIVE_CONTROL))
    print()

    print("-" * 78)
    print("%-58s %s" % ("WATCHED path", "read by the blocking gate?"))
    print("-" * 78)
    rows = []
    for p in watched:
        hit = p in reads
        # a path named on a git argv is read AT A REVISION, not from the tree
        at_rev = any(p in a and "git" in a.split()[0] for a in argvs)
        if hit:
            verdict = "READ"
        elif at_rev:
            verdict = "at-a-revision only"
        else:
            verdict = "NOT READ"
        rows.append({"path": p, "verdict": verdict})
        print("%-58s %s" % (p, verdict))
    print("-" * 78)
    nr = [r["path"] for r in rows if r["verdict"] == "NOT READ"]
    print("%d of %d watched paths are NOT READ by any blocking instrument."
          % (len(nr), len(watched)))
    print("A NOT-READ path cannot change the demonstration its own edit pays")
    print("for.  That is a statement about COST, not about whether watching it")
    print("is wrong -- see docs/OneThird-mg856d-GateScope-Duration.md.")
    if skipped:
        print()
        print("COVERAGE LIMIT: --fast skipped %s, so a NOT-READ row here is over"
              % ", ".join(skipped))
        print("a smaller instrument set than the gate actually runs.")

    with open(OUT, "w") as f:
        json.dump({"generated_by": "scripts/onethird_mg856d_watch_sensitivity_probe.py",
                   "instruments_traced": ran,
                   "instruments_skipped": skipped,
                   "positive_control": POSITIVE_CONTROL,
                   "positive_control_ok": True,
                   "watched_count": len(watched),
                   "rows": rows,
                   "repo_reads_observed": sorted(reads)}, f, indent=2)
        f.write("\n")
    print()
    print("wrote %s" % os.path.relpath(OUT, REPO))

    # The tracer's scratch directory lives inside the repo because it has to be
    # on PYTHONPATH for the traced subprocesses; it is not an artefact of the
    # measurement and must not be left in the tree.
    for name in os.listdir(tracedir):
        os.remove(os.path.join(tracedir, name))
    os.rmdir(tracedir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
