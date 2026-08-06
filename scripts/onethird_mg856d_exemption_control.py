#!/usr/bin/env python3
"""
mg-856d -- CAN THE GATE'S DEMO-EXEMPTION LIST BE WIDENED WITHOUT ANYONE NOTICING?

WHAT THIS GUARDS, and why it exists in the same commit as the thing it guards.
mg-856d narrowed the BLOCKING half of the gate-mutation trigger: a merge whose
only watched path is `.github/workflows/script-controls.yml` no longer pays the
mg-60d3 demonstration, because that demonstration was measured and does not read
that file.  The narrowing is expressed as a second shell literal in
`scripts/refinery_gate.sh`:

    DEMO_INSENSITIVE='<paths whose edit cannot change what the demo asserts>'

An exemption list on a gate is the most dangerous object in this repository.
One line appended to it -- `scripts/onethird_mg60d3_gate_mutation_demo.py`, say
-- turns the blocking gate into a `git diff` and a `grep` forever, and nothing
downstream would look any different: the gate would still run, still print, and
still exit 0.  That is this arc's named defect, a control that cannot fail,
reached by adding one line to a control that could.

So the list is not trusted.  FIVE PROPERTIES, checked on every merge, in
milliseconds, standard library only:

  P1 IN THE WATCHLIST.  Every exempt path is still in `WATCHED`.  The exemption
     is about the BLOCKING copy only: the path stays in both `paths:` blocks of
     `.github/workflows/gate-mutation-demo.yml`, so the full ~30-minute
     demonstration still fires on Actions for exactly the same commits.  An
     exemption for a path that has left the watchlist is a deletion wearing a
     narrower word.

  P2 NOT DERIVED.  Every exempt path is in mg-7db4's `MECHANISM` set and is NOT
     in the ROOTS import closure and NOT one of the datasets that closure reads.
     This is the load-bearing one.  A closure member is watched BECAUSE editing
     it can change what the demonstration computes -- that is what closure
     means -- so a closure member can never be honestly exempted, and this
     property makes "never" mechanical instead of a promise.

  P3 NOT THE DECISION ITSELF.  No exempt path is one of the files the gate's own
     decision is made of: the gate script, the workflow, the refinery config,
     mg-7db4's consistency check, or this file.  Those four are how the trigger
     knows anything; exempting one is exempting the exemption check.

  P4 A NAMED, WIRED CATCHER.  Every exempt path carries a `# CATCHER` line in
     `refinery_gate.sh` naming a script and the workflow that runs it, and BOTH
     are verified against the tree: the workflow must actually contain a step
     running that script, and the workflow's `paths:` filter must actually cover
     the exempt path.  "Something else catches this" is the sentence every
     removed control was removed on; here it is parsed rather than believed.

  P5 THE RESIDUAL IS NOT EMPTY.  `WATCHED` minus the exemptions must still
     contain the gate script and the mg-60d3 demo itself, so no sequence of
     exemptions can reach a state where nothing triggers the demonstration.

SELF-TEST, run by `main` on every invocation so CI gets it for free: each of the
five properties is re-checked against a deliberately drifted copy of the inputs
and this script exits non-zero unless every drift FIRES.  A check on an
exemption list that has never been shown to fail would be the funniest possible
place in this repository to put one.

Run:  python3 scripts/onethird_mg856d_exemption_control.py
Exits non-zero on any problem.  Writes nothing.
"""

import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "scripts"))

# Imported, not re-parsed.  mg-5ad1's part B made the same move for the same
# reason: a second representation of MECHANISM/ROOTS here could disagree with
# mg-7db4's, and then two green checks would mean nothing together.
import onethird_mg7db4_watchlist_consistency as W7DB4  # noqa: E402

GATE_SH = "scripts/refinery_gate.sh"
DEMO_WORKFLOW = ".github/workflows/gate-mutation-demo.yml"
THIS = "scripts/onethird_mg856d_exemption_control.py"

# The files the trigger's own decision is made of.  Exempting any of these is
# exempting the machinery that decides exemptions.
DECISION_FILES = {
    GATE_SH,
    DEMO_WORKFLOW,
    ".pogo/refinery.toml",
    "scripts/onethird_mg7db4_watchlist_consistency.py",
    THIS,
}

# The residual trigger must always retain these, whatever is exempted.
RESIDUAL_FLOOR = {
    GATE_SH,
    "scripts/onethird_mg60d3_gate_mutation_demo.py",
}

_CATCHER_RE = re.compile(r"^#\s*CATCHER\s+(\S+)\s+(\S+)\s+(\S+)\s*$", re.M)


# ------------------------------------------------------------- parsers ------
def parse_named_list(text, name):
    """A single-quoted multi-line shell literal, as a list of paths."""
    m = re.search(r"^%s='([^']*)'" % re.escape(name), text, re.M)
    if m is None:
        return None
    return [ln.strip() for ln in m.group(1).splitlines() if ln.strip()]


def parse_catchers(text):
    """`# CATCHER <exempt-path> <catcher-script> <catcher-workflow>` lines."""
    return {m[0]: (m[1], m[2]) for m in _CATCHER_RE.findall(text)}


def workflow_runs(text):
    """Repo-relative scripts a workflow's `run:` steps execute."""
    out = set()
    for m in re.finditer(r"run:\s*(.+)", text):
        for tok in m.group(1).split():
            if tok.startswith("scripts/"):
                out.add(tok)
    return out


def paths_cover(blocks, path):
    """Does any `paths:` block in the workflow match `path`?  The filters this
    repo uses are literals and one-level `dir/**` prefixes; both are handled and
    anything else is treated as NOT covering, which is the safe direction."""
    for block in blocks:
        for pat in block:
            if pat == path:
                return True
            if pat.endswith("/**") and path.startswith(pat[:-2]):
                return True
    return False


# ------------------------------------------------------------- the checks ---
def check(read):
    """Return a list of problem strings; empty means the exemptions are sound."""
    problems = []

    sh = read(GATE_SH)
    if sh is None:
        return ["%s is missing -- there is no gate to exempt anything from"
                % GATE_SH]

    watch = parse_named_list(sh, "WATCHED")
    exempt = parse_named_list(sh, "DEMO_INSENSITIVE")
    if watch is None:
        return ["no WATCHED='...' literal in %s" % GATE_SH]
    if exempt is None:
        return ["no DEMO_INSENSITIVE='...' literal in %s -- mg-856d's narrowing "
                "is expressed by that list, and this control has nothing to "
                "check without it" % GATE_SH]

    watch_set, exempt_set = set(watch), set(exempt)
    catchers = parse_catchers(sh)

    closure, _ = W7DB4.import_closure(W7DB4.ROOTS, read)
    datasets = W7DB4.data_reads(closure, read)
    derived = closure | datasets

    for path in sorted(exempt_set):
        # P1
        if path not in watch_set:
            problems.append(
                "P1: %s is exempt from the blocking demo but is not in WATCHED "
                "-- an exemption for an unwatched path is a deletion, and the "
                "Actions demonstration no longer fires on it either" % path)
        # P2
        if path in derived:
            problems.append(
                "P2: %s is in the gate's derived closure (import closure or a "
                "dataset it reads), so editing it CAN change what the "
                "demonstration asserts -- it cannot be exempt" % path)
        if path not in W7DB4.MECHANISM:
            problems.append(
                "P2: %s is exempt but is not in mg-7db4's MECHANISM set -- only "
                "hand-declared mechanism paths are eligible, so that nothing "
                "derived can be exempted by accident" % path)
        # P3
        if path in DECISION_FILES:
            problems.append(
                "P3: %s is one of the files the trigger's own decision is made "
                "of -- exempting it exempts the machinery that decides "
                "exemptions" % path)
        # P4
        if path not in catchers:
            problems.append(
                "P4: %s is exempt with no `# CATCHER <path> <script> <workflow>` "
                "line in %s -- an exemption whose justification is not written "
                "down is one nobody can review" % (path, GATE_SH))
            continue
        script, wf = catchers[path]
        wf_src = read(wf)
        if wf_src is None:
            problems.append(
                "P4: %s's declared catcher workflow %s does not exist"
                % (path, wf))
            continue
        if script not in workflow_runs(wf_src):
            problems.append(
                "P4: %s's declared catcher %s is not run by any step of %s -- "
                "the catcher named in the exemption is not wired"
                % (path, script, wf))
        if not paths_cover(W7DB4.parse_workflow_paths(wf_src), path):
            problems.append(
                "P4: %s's declared catcher workflow %s does not fire on %s -- "
                "its `paths:` filters do not cover the exempt path"
                % (path, wf, path))

    # P5
    residual = watch_set - exempt_set
    if not residual:
        problems.append(
            "P5: every watched path is exempt -- the blocking demonstration "
            "can no longer be triggered by anything")
    for floor in sorted(RESIDUAL_FLOOR):
        if floor in exempt_set:
            problems.append(
                "P5: %s is exempt -- editing the gate itself, or the demo "
                "itself, must always re-run the demonstration" % floor)

    return problems


# ------------------------------------------------------------- self-test ----
def _selftest():
    read = W7DB4.disk_reader()
    base = {}
    closure, _ = W7DB4.import_closure(W7DB4.ROOTS, read)
    for rel in sorted(W7DB4.MECHANISM | closure | {THIS}):
        src = read(rel)
        if src is not None:
            base[rel] = src
    for rel in sorted(W7DB4.data_reads(closure, read)):
        base[rel] = ""

    if check(W7DB4.dict_reader(base)):
        print("SELF-TEST FAILED: the undrifted snapshot already has problems, "
              "so nothing below means anything.")
        for p in check(W7DB4.dict_reader(base)):
            print("  - %s" % p)
        return False

    def with_exempt(extra):
        d = dict(base)
        d[GATE_SH] = re.sub(r"^DEMO_INSENSITIVE='", "DEMO_INSENSITIVE='%s\n" % extra,
                            d[GATE_SH], count=1, flags=re.M)
        return d

    cases = []

    # P2: a member of the derived closure is exempted
    cases.append(("P2  a closure member is exempted",
                  with_exempt("scripts/onethird_mg2c34_n7_overlap_test.py")))

    # P3: the gate script itself is exempted
    cases.append(("P3  the gate script itself is exempted",
                  with_exempt(GATE_SH)))

    # P1: a path outside WATCHED is exempted
    cases.append(("P1  a path outside WATCHED is exempted",
                  with_exempt("docs/OneThird-L1b-Bwall-state.md")))

    # P4: the declared catcher step is deleted from its workflow
    d = dict(base)
    catchers = parse_catchers(d[GATE_SH])
    assert catchers, "self-test needs at least one CATCHER line to drift"
    (_ex, (cscript, cwf)) = sorted(catchers.items())[0]
    d[cwf] = re.sub(r"^.*%s.*$\n?" % re.escape(cscript), "", d[cwf],
                    count=1, flags=re.M)
    cases.append(("P4  the declared catcher step is deleted", d))

    # P5: everything is exempted
    d = dict(base)
    watch = parse_named_list(d[GATE_SH], "WATCHED")
    d[GATE_SH] = re.sub(r"^DEMO_INSENSITIVE='[^']*'",
                        "DEMO_INSENSITIVE='%s'" % "\n".join(watch),
                        d[GATE_SH], count=1, flags=re.M)
    cases.append(("P5  every watched path is exempted", d))

    ok = True
    print("-" * 78)
    print("SELF-TEST -- each drift must be caught")
    print("-" * 78)
    for desc, mapping in cases:
        problems = check(W7DB4.dict_reader(mapping))
        print("  %-58s %s" % (desc, "CAUGHT" if problems else "MISSED"))
        if not problems:
            ok = False
    print("-" * 78)
    return ok


def main():
    read = W7DB4.disk_reader()
    problems = check(read)
    if problems:
        print("DEMO EXEMPTION UNSOUND -- the blocking gate is skipping the "
              "demonstration on paths it has not justified skipping:")
        for p in problems:
            print("  - %s" % p)
        return 1

    sh = read(GATE_SH)
    exempt = parse_named_list(sh, "DEMO_INSENSITIVE") or []
    watch = parse_named_list(sh, "WATCHED") or []
    print("demo exemptions sound: %d of %d watched paths exempt from the "
          "BLOCKING demo; all still in the Actions trigger"
          % (len(exempt), len(watch)))
    for path in exempt:
        script, wf = parse_catchers(sh)[path]
        print("    %s  <- caught by %s in %s" % (path, script, wf))

    if not _selftest():
        print("SELF-TEST FAILED: a drift this check is supposed to catch went "
              "unnoticed, so a green result above proves nothing.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
