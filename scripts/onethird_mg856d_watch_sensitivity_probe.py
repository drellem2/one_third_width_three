#!/usr/bin/env python3
"""
mg-856d -- WHICH WATCHED PATHS CAN ACTUALLY CHANGE WHAT THE BLOCKING GATE'S
SLOW PATH ASSERTS?

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

TWO COLUMNS, AND ONLY ONE OF THEM IS THE ANSWER.  `scripts/refinery_gate.sh`
runs the mg-7db4 consistency check on EVERY merge and the mg-5ad1 probe plus the
mg-60d3 demonstration only when a watched path changed.  An exemption skips the
second group and never the first, so a path's cost verdict is over the SLOW-PATH
instruments alone.  The consistency check reads nearly every watched path by
design -- that is its job -- and its reads are reported in their own column so
they cannot be mistaken for sensitivity.

HOW IT MEASURES.  Each instrument runs in a subprocess under a `sitecustomize`
that installs a `sys.addaudithook`, recording every path inside the repository
that is opened for READING and every module body that is EXECUTED.
`subprocess.Popen` is recorded separately as an argv observation, because
`git show <rev>:<path>` reads a file AT A REVISION and that is not sensitivity
to the file's current bytes.  `PYTHONPATH` and the log path are inherited, so an
instrument that shells out to another interpreter is traced too.

WHY AN AUDIT HOOK RATHER THAN A WRAPPED `open`, recorded because the wrong
version of this file ran first and looked fine.  A monkey-patched
`builtins.open`/`io.open`/`os.open` misses every import, and on this host it
misses them twice over: CPython loads a module through `io.open_code`, which no
Python-level name intercepts, and Apple's `/usr/bin/python3` redirects bytecode
to `~/Library/Caches/com.apple.python/<abs path>.pyc`, so even the raw `open`
event names a file outside the repository.  The result was a probe reporting the
gated instrument as NOT READ by a probe whose own docstring says it imports it.
The `exec` audit event carries each module body's `co_filename`, which is the
source path, and that is what this now keys on.

POSITIVE CONTROLS, PER COLUMN, because a tracer that cannot see and an
instrument that does not read produce identical reports.  The slow-path column
must show `scripts/onethird_mg2c34_n7_overlap_test.py` and
`data/onethird-mg8b64-L1b-bk-transport-transfer.json`; the always-run column
must show `scripts/refinery_gate.sh` and the demo workflow.  Any miss and the
probe exits non-zero having printed NO sensitivity verdict at all.  An earlier
version had one aggregate control across both columns, and the consistency check
satisfied it single-handed while the slow-path column was completely blind --
a control that could not fail, in the probe written to find controls that cannot
fail.

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
#
# THE `slow` COLUMN IS THE WHOLE POINT, and the first version of this file got
# it wrong.  It aggregated reads across all three instruments and reported all
# 18 watched paths as READ -- true, and useless, because the reader was the
# mg-7db4 consistency check, which parses the workflow, the gate script and the
# entire closure BY DESIGN and runs on every merge whether or not anything
# watched changed.  Its reads say nothing about the cost of the exemption: it
# runs either way.  The question is only ever about the two instruments an
# exemption actually skips, so the verdict is computed over those and the
# consistency check's reads are reported in their own column.
BLOCKING = [
    # (label, script, in --fast, on the SLOW path)
    ("mg-7db4 watchlist consistency",
     "scripts/onethird_mg7db4_watchlist_consistency.py", True, False),
    ("mg-5ad1 gate blindspot probe",
     "scripts/onethird_mg5ad1_gate_blindspot_probe.py", True, True),
    ("mg-60d3 gate mutation demo",
     "scripts/onethird_mg60d3_gate_mutation_demo.py", False, True),
]

# POSITIVE CONTROLS, per column, because a tracer that cannot see and an
# instrument that does not read produce identical reports.
#
# The SLOW-PATH control is the load-bearing one and it is not a formality: both
# slow-path instruments import `onethird_mg2c34_n7_overlap_test` by name, so if
# that path comes back NOT READ the tracer is broken, full stop.  An earlier
# version of this file had only an aggregate control over both columns; the
# consistency check satisfied it on its own while the slow-path column was
# entirely blind, and the report looked completely healthy.  Per-column is the
# repair.
SLOW_POSITIVE_CONTROL = [
    "scripts/onethird_mg2c34_n7_overlap_test.py",
    "data/onethird-mg8b64-L1b-bk-transport-transfer.json",
]
ALWAYS_POSITIVE_CONTROL = [
    "scripts/refinery_gate.sh",
    ".github/workflows/gate-mutation-demo.yml",
]

# WHY AN AUDIT HOOK AND NOT A WRAPPED `open`.  The first version of this file
# monkey-patched `builtins.open`, `io.open` and `os.open`.  It ran, it emitted,
# and it MISSED EVERY IMPORT: CPython's import machinery reads a module through
# `io.open_code` and `_io.FileIO`, neither of which goes through the Python-level
# names a monkey-patch can reach.  The blindspot probe, which reads the gated
# instrument by importing it, traced exactly two file reads -- both the dataset,
# none of the source.  The probe's positive control would have refused to report
# on that trace, which is the control doing its job, and the trace would still
# have been wrong for 90 minutes first.  `sys.addaudithook` sees the `open`
# event from all three paths, so it is what this uses.
_SITECUSTOMIZE = r'''
import os, sys
_LOG = os.environ.get("MG856D_TRACE")
if _LOG:
    _ROOT = os.path.realpath(os.environ.get("MG856D_REPO", ""))
    _state = {"busy": False}

    def _emit(kind, payload):
        if _state["busy"]:
            return
        _state["busy"] = True          # the hook fires on its own log write
        try:
            fh = os.open(_LOG, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o644)
            os.write(fh, ("%s\t%s\n" % (kind, payload)).encode())
            os.close(fh)
        except Exception:
            pass
        finally:
            _state["busy"] = False

    # Cache: the corpus opens the same handful of files thousands of times over
    # six gate runs, and `realpath` is several syscalls.  Without this the hook
    # roughly triples the demo's runtime; with it the overhead is noise.
    _seen = {}

    def _rel(p):
        if not isinstance(p, (str, bytes)):
            return None
        if p in _seen:
            return _seen[p]
        try:
            r = os.path.realpath(os.fsdecode(p))
        except Exception:
            _seen[p] = None
            return None
        r = r[len(_ROOT) + 1:] if r.startswith(_ROOT + os.sep) else None
        _seen[p] = r
        return r

    def _hook(event, args):
        # `exec` carries the code object of every module body that runs, and
        # its co_filename is the SOURCE path.  This is the only reliable signal
        # for "this module was imported" on this host: Apple's /usr/bin/python3
        # redirects bytecode to ~/Library/Caches/com.apple.python/<abs path>.pyc,
        # so the `open` event for an import names a file outside the repository
        # and a repo-prefix test never sees it.  The first version of this probe
        # missed every import for exactly that reason and reported the gated
        # instrument as NOT READ by a probe whose docstring says it imports it.
        if event == "exec":
            try:
                rel = _rel(getattr(args[0], "co_filename", None))
            except Exception:
                rel = None
            if rel is not None:
                _emit("open", rel)
            return
        if event == "open":
            # (path, mode, flags).  mode is None for os.open; treat a write
            # flag or a write mode as "not a read" so the demo's own report
            # files do not appear as inputs.
            mode = args[1] if len(args) > 1 else None
            if isinstance(mode, str) and ("w" in mode or "a" in mode
                                          or "x" in mode or "+" in mode):
                return
            flags = args[2] if len(args) > 2 else 0
            if isinstance(flags, int) and (flags & (os.O_WRONLY | os.O_RDWR)):
                return
            rel = _rel(args[0])
            if rel is not None:
                _emit("open", rel)
        elif event == "subprocess.Popen":
            try:
                a = args[1]
                _emit("argv", " ".join(os.fsdecode(x) for x in a)
                      if isinstance(a, (list, tuple)) else os.fsdecode(a))
            except Exception:
                pass

    sys.addaudithook(_hook)
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

    slow_reads, always_reads, argvs, ran, skipped = set(), set(), [], [], []
    print("=" * 78)
    print("mg-856d watch-sensitivity probe")
    print("POPULATION: the %d paths in WATCHED.  GRAIN: one path." % len(watched))
    print("INSTRUMENTS: the ones scripts/refinery_gate.sh runs.  The Actions-")
    print("             only mg-7db4 battery and mg-75f0 closure demo are")
    print("             excluded: they do not hold the refinery's serial slot,")
    print("             which is what costs.  The verdict column is over the")
    print("             SLOW-PATH instruments only -- the ones an exemption")
    print("             actually skips.  The consistency check runs either way.")
    print("=" * 78)
    for name, rel, in_fast, on_slow in BLOCKING:
        if fast and not in_fast:
            skipped.append(name)
            print("  %-46s SKIPPED (--fast)" % name)
            continue
        reads = slow_reads if on_slow else always_reads
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
        # PER-INSTRUMENT positive control.  The aggregate one below cannot tell
        # "instrument C read nothing" from "instrument A already covered the two
        # control paths" -- and a silently dead tracer on the single expensive
        # instrument is exactly how this probe would produce a confident wrong
        # answer.  Every Python instrument in this repo reads at least its own
        # source, so zero is never a real observation.
        if n == 0:
            print()
            print("TRACER FAILED on %s: zero repo reads is not a possible" % name)
            print("observation -- every instrument here reads at least its own")
            print("source.  Refusing to report sensitivity.")
            return 1

    print()
    failed = False
    for label, want, got in (
            ("SLOW PATH", SLOW_POSITIVE_CONTROL, slow_reads),
            ("always-run check", ALWAYS_POSITIVE_CONTROL, always_reads)):
        if fast and label == "SLOW PATH":
            # the demo is skipped, but the blindspot probe alone still imports
            # the gated instrument, so the control stands
            pass
        missed = [p for p in want if p not in got]
        if missed:
            print("POSITIVE CONTROL FAILED for the %s column -- the tracer did "
                  "not observe %s." % (label, missed))
            failed = True
        else:
            print("positive control (%s): OK -- observed %s"
                  % (label, ", ".join(want)))
    if failed:
        print()
        print("Every 'NOT READ' verdict this probe could print would be a false")
        print("negative, so it prints none.")
        return 1
    print()

    print("-" * 78)
    print("%-58s %-10s %s" % ("WATCHED path", "SLOW PATH", "always-run check"))
    print("-" * 78)
    rows = []
    for p in watched:
        hit = p in slow_reads
        # a path named on a git argv is read AT A REVISION, not from the tree
        at_rev = any(p in a and a.split() and "git" in a.split()[0]
                     for a in argvs)
        if hit:
            verdict = "READ"
        elif at_rev:
            verdict = "at-a-rev"
        else:
            verdict = "NOT READ"
        rows.append({"path": p, "slow_path": verdict,
                     "always_run_check": p in always_reads})
        print("%-58s %-10s %s"
              % (p, verdict, "read" if p in always_reads else "-"))
    print("-" * 78)
    nr = [r["path"] for r in rows if r["slow_path"] == "NOT READ"]
    print("%d of %d watched paths are NOT READ by the slow-path instruments."
          % (len(nr), len(watched)))
    print("A NOT-READ path cannot change the demonstration its own edit pays")
    print("for.  That is a statement about COST and about that path only; it is")
    print("NOT a reason to stop watching it -- the always-run column shows most")
    print("of them are read by the consistency check, which is why they are on")
    print("the list.  See docs/OneThird-mg856d-GateScope-Duration.md.")
    if skipped:
        print()
        print("COVERAGE LIMIT: --fast skipped %s, so a NOT-READ row here is over"
              % ", ".join(skipped))
        print("a smaller instrument set than the gate actually runs, and must")
        print("not be used to justify an exemption.")

    with open(OUT, "w") as f:
        json.dump({"generated_by": "scripts/onethird_mg856d_watch_sensitivity_probe.py",
                   "instruments_traced": ran,
                   "instruments_skipped": skipped,
                   "positive_control_slow": SLOW_POSITIVE_CONTROL,
                   "positive_control_always": ALWAYS_POSITIVE_CONTROL,
                   "positive_control_ok": True,
                   "watched_count": len(watched),
                   "rows": rows,
                   "slow_path_reads_observed": sorted(slow_reads),
                   "always_run_reads_observed": sorted(always_reads)},
                  f, indent=2)
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
