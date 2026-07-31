#!/usr/bin/env python3
"""
mg-7db4 -- is the gate-mutation trigger still complete and still consistent?

WHAT THIS GUARDS.  mg-7db4 gave `scripts/onethird_mg60d3_gate_mutation_demo.py`
a mechanism instead of an instruction: a paths filter that fires the demo on
exactly the commits that can invalidate it.  That paths filter exists in two
copies, because the two places it has to act cannot share a file --

  * `.github/workflows/gate-mutation-demo.yml`  (`on: push:/pull_request: paths:`)
    -- visible, runs on every push, but not consulted by the merge;
  * `scripts/refinery_gate.sh`                  (`WATCHED`)
    -- invisible on GitHub, but it is what the pogo refinery runs before it
    fast-forwards to `main`, so it is the copy that can actually stop a merge.

Two copies of a list is exactly the shape that rots.  This script is the reason
it cannot rot silently.  It is order-milliseconds, imports nothing outside the
standard library, and runs in the fast gate.

THREE PROPERTIES, and the third is the load-bearing one:

  1. AGREEMENT.  The workflow's `push` paths, its `pull_request` paths, and the
     shell script's `WATCHED` are the same set.

  2. IDENTITY.  The watchlist contains the files the mechanism is made of --
     both workflows, the refinery config, the gate script, this script, the
     demo, and the gated instrument.

  3. COMPLETENESS, derived rather than asserted.  The watchlist covers the
     TRANSITIVE CLOSURE of the `onethird_*` corpus modules the gated instrument
     and the demo import, and every committed dataset those modules READ.  This
     is the check that catches the drift nobody would notice: adding an import
     to `onethird_mg2c34_n7_overlap_test.py` moves a quantity the gate asserts
     into a file the trigger does not watch, and from then on that file can be
     edited without the demo ever re-running.  A paths filter that has stopped
     naming the paths that matter is a trigger that has quietly become the
     "run it on demand" sentence this ticket removed.

KNOWN LIMIT, stated rather than papered over.  The dataset scan is a regex over
the corpus's one idiom, `open(os.path.join(REPO, "data", "<name>"))`, with a
trailing `, "w"` marking a write.  A module that reads a dataset some other way
is invisible to it.  The import scan has no such limit -- it is a closure over
every `import onethird_*` / `from onethird_* import` line, resolved to files.

SELF-TEST.  Run with `--selftest` (also run by `main` on every invocation, so
CI gets it for free): each of the three properties is re-checked against a
deliberately drifted copy of the inputs, and this script exits non-zero unless
every one of them FIRES.  A consistency check that has never been shown to fail
is the same defect one level further up, and this file is not going to be the
place that repeats it.

Run:  python3 scripts/onethird_mg7db4_watchlist_consistency.py
Exits non-zero on any inconsistency.  Writes nothing.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

WORKFLOW = ".github/workflows/gate-mutation-demo.yml"
GATE_SH = "scripts/refinery_gate.sh"

# The files the trigger mechanism is itself made of.  These are not derivable
# from the corpus -- they are the mechanism -- so they are named here, and the
# watchlist must contain exactly these plus what is derived below.
MECHANISM = {
    ".github/workflows/gate-mutation-demo.yml",
    ".github/workflows/script-controls.yml",
    ".pogo/refinery.toml",
    "scripts/refinery_gate.sh",
    "scripts/onethird_mg7db4_watchlist_consistency.py",
    # mg-3934: the preflight that decides whether the workflow's checkout is
    # deep enough for the code it runs.  It is mechanism, not a demonstration
    # -- reachable from nothing in ROOTS -- so it is named here.  A step
    # wired into the job without also being watched can be neutered without
    # the job re-running to notice, which is the shape of defect this whole
    # mechanism exists to refuse.
    "scripts/onethird_mg3934_ci_history_depth_control.py",
}

# Roots of the import closure: everything the two jobs actually execute --
# the instrument the gate runs, the M1/M2 regression demo, the standing
# blindness probe, and the battery that proves the probe can fail.
#
# ADDING A DEMONSTRATION: put its script here, not only in the watchlists.  A
# path that is watched but reachable from nothing in ROOTS is rejected below as
# "watched but not part of the gate" -- which is the check refusing to let a
# watchlist grow entries nobody can justify, and equally refusing to let a new
# demonstration be wired into a job without also being watched.
#
# mg-75f0 took that route: `onethird_mg75f0_gate_class_closure_demo.py` is the
# closure demonstration for the widened identity check, added below at the same
# time as its step in gate-mutation-demo.yml and its path in both watchlists.
ROOTS = (
    "scripts/onethird_mg60d3_gate_mutation_demo.py",
    "scripts/onethird_mg2c34_n7_overlap_test.py",
    "scripts/onethird_mg5ad1_gate_blindspot_probe.py",
    "scripts/onethird_mg7db4_probe_mutation_battery.py",
    "scripts/onethird_mg75f0_gate_class_closure_demo.py",
)

_IMPORT_RE = re.compile(r"^\s*(?:from|import)\s+(onethird_\w+)", re.M)
_DATA_RE = re.compile(
    r'open\(os\.path\.join\(REPO,"data","([^"]+)"\)(,"w")?\)')


# ------------------------------------------------------------- readers ------
def disk_reader():
    """Source reader backed by the working tree.  Returns None for a path that
    does not exist, so a deleted module is a reportable problem rather than a
    traceback."""
    def read(rel):
        path = os.path.join(REPO, rel)
        if not os.path.isfile(path):
            return None
        with open(path) as f:
            return f.read()
    return read


def dict_reader(mapping):
    """Source reader over an in-memory dict, for the self-test."""
    return lambda rel: mapping.get(rel)


# ------------------------------------------------------------- parsers ------
def parse_workflow_paths(text):
    """Every `paths:` block in the workflow, as a list of lists.

    Deliberately a hand parser: this script must run under a bare interpreter
    with no PyYAML, on both the fleet host and a hosted runner."""
    blocks, current = [], None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped == "paths:":
            current = []
            blocks.append(current)
            continue
        if current is None:
            continue
        m = re.match(r"^\s*-\s*'([^']+)'\s*$", line)
        if m:
            current.append(m.group(1))
        elif stripped and not stripped.startswith("#"):
            current = None
    return blocks


def parse_shell_watchlist(text):
    """The single-quoted WATCHED heredoc-style literal in refinery_gate.sh."""
    m = re.search(r"^WATCHED='([^']*)'", text, re.M)
    if not m:
        return None
    return [ln.strip() for ln in m.group(1).splitlines() if ln.strip()]


# ------------------------------------------------------------- derivation ---
def import_closure(roots, read):
    """Transitive closure of `onethird_*` corpus modules, as repo-relative
    script paths.  Unresolvable imports are returned separately so a rename
    is reported instead of silently shrinking the closure."""
    seen, missing, queue = set(), set(), list(roots)
    while queue:
        rel = queue.pop()
        if rel in seen:
            continue
        src = read(rel)
        if src is None:
            missing.add(rel)
            continue
        seen.add(rel)
        for mod in _IMPORT_RE.findall(src):
            child = "scripts/%s.py" % mod
            if child not in seen:
                queue.append(child)
    return seen, missing


def data_reads(modules, read):
    """Committed datasets the closure READS (not writes), repo-relative."""
    found = set()
    for rel in sorted(modules):
        src = read(rel)
        if src is None:
            continue
        for name, write in _DATA_RE.findall(re.sub(r"\s+", "", src)):
            if not write:
                found.add("data/%s" % name)
    return found


# ------------------------------------------------------------- the checks ---
def check(read):
    """Return a list of problem strings; empty means consistent."""
    problems = []

    wf = read(WORKFLOW)
    sh = read(GATE_SH)
    if wf is None:
        return ["%s is missing -- the trigger has no workflow" % WORKFLOW]
    if sh is None:
        return ["%s is missing -- the trigger cannot block a merge" % GATE_SH]

    # (1) agreement
    blocks = parse_workflow_paths(wf)
    if len(blocks) < 2:
        problems.append(
            "%s has %d `paths:` block(s); expected 2 (push and pull_request). "
            "A missing filter is a trigger that does not fire."
            % (WORKFLOW, len(blocks)))
    watch = parse_shell_watchlist(sh)
    if watch is None:
        problems.append("no WATCHED='...' literal found in %s" % GATE_SH)
        return problems

    watch_set = set(watch)
    if len(watch_set) != len(watch):
        problems.append("%s WATCHED has duplicate entries" % GATE_SH)
    for i, block in enumerate(blocks):
        if set(block) != watch_set:
            only_wf = sorted(set(block) - watch_set)
            only_sh = sorted(watch_set - set(block))
            problems.append(
                "workflow `paths:` block %d disagrees with %s WATCHED: "
                "only in workflow %s; only in shell %s"
                % (i + 1, GATE_SH, only_wf or "[]", only_sh or "[]"))

    # (2) identity + (3) completeness
    closure, missing = import_closure(ROOTS, read)
    for rel in sorted(missing):
        problems.append(
            "import target %s does not exist -- the closure is broken, so the "
            "watchlist below is derived from an incomplete corpus" % rel)
    datasets = data_reads(closure, read)
    expected = MECHANISM | closure | datasets

    for rel in sorted(expected - watch_set):
        problems.append(
            "%s is reachable from the gate but NOT watched -- editing it would "
            "not re-run the mutation demo" % rel)
    for rel in sorted(watch_set - expected):
        problems.append(
            "%s is watched but is not part of the gate, the mechanism, or the "
            "import closure -- it makes ordinary commits pay for the demo"
            % rel)
    return problems


# ------------------------------------------------------------- self-test ----
def _selftest():
    """Each property, re-checked against a deliberately drifted copy of the
    inputs.  Every case must produce at least one problem."""
    read = disk_reader()
    base = {}
    closure, _ = import_closure(ROOTS, read)
    for rel in sorted(MECHANISM | closure):
        src = read(rel)
        if src is not None:
            base[rel] = src
    for rel in sorted(data_reads(closure, read)):
        base[rel] = ""

    if check(dict_reader(base)):
        print("SELF-TEST FAILED: the undrifted snapshot is already "
              "inconsistent, so nothing below means anything.")
        for p in check(dict_reader(base)):
            print("  - %s" % p)
        return False

    cases = []

    # drift 1: the two copies of the list disagree
    d = dict(base)
    d[GATE_SH] = d[GATE_SH].replace(
        "scripts/onethird_mgb0a6_spectral_killshot_probe.py\n", "", 1)
    cases.append(("shell WATCHED loses an entry the workflow still has", d))

    # drift 2: the workflow loses a paths block entirely
    d = dict(base)
    d[WORKFLOW] = d[WORKFLOW].replace("  pull_request:\n    paths:\n",
                                      "  pull_request:\n", 1)
    cases.append(("workflow loses its pull_request paths filter", d))

    # drift 3: the gated instrument grows an unwatched import
    d = dict(base)
    d["scripts/onethird_mg2c34_n7_overlap_test.py"] = (
        "from onethird_mg7db4_hypothetical_new_instrument import thing\n"
        + d["scripts/onethird_mg2c34_n7_overlap_test.py"])
    d["scripts/onethird_mg7db4_hypothetical_new_instrument.py"] = "pass\n"
    cases.append(("gated instrument imports a module nobody watched", d))

    # drift 4: the gated instrument reads a dataset nobody watched
    d = dict(base)
    d["scripts/onethird_mg2c34_n7_overlap_test.py"] += (
        '\nwith open(os.path.join(REPO, "data",\n'
        '                       "onethird-mg7db4-unwatched.json")) as f:\n'
        '    pass\n')
    d["data/onethird-mg7db4-unwatched.json"] = ""
    cases.append(("gated instrument reads a dataset nobody watched", d))

    # drift 5: the watchlist grows a path with nothing to do with the gate
    d = dict(base)
    d[GATE_SH] = d[GATE_SH].replace(
        "WATCHED='", "WATCHED='docs/OneThird-L1b-Bwall-state.md\n", 1)
    d[WORKFLOW] = d[WORKFLOW].replace(
        "    paths:\n", "    paths:\n      - 'docs/OneThird-L1b-Bwall-state.md'\n")
    cases.append(("watchlist grows a path unrelated to the gate", d))

    ok = True
    print("-" * 78)
    print("SELF-TEST -- each drift must be caught")
    print("-" * 78)
    for desc, mapping in cases:
        problems = check(dict_reader(mapping))
        print("  %-58s %s" % (desc, "CAUGHT" if problems else "MISSED"))
        if not problems:
            ok = False
    print("-" * 78)
    return ok


def main():
    problems = check(disk_reader())
    if problems:
        print("WATCHLIST INCONSISTENT -- the gate-mutation trigger is not "
              "covering what it claims to cover:")
        for p in problems:
            print("  - %s" % p)
        return 1

    read = disk_reader()
    closure, _ = import_closure(ROOTS, read)
    print("watchlist consistent: %d paths; import closure %d modules; "
          "datasets read %d"
          % (len(parse_shell_watchlist(read(GATE_SH))), len(closure),
             len(data_reads(closure, read))))

    if not _selftest():
        print("SELF-TEST FAILED: a drift this check is supposed to catch went "
              "unnoticed, so a green result above proves nothing.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
