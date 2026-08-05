#!/usr/bin/env python3
"""
mg-a471 -- A SUBSET RUN IS NOT THE DEMONSTRATION.  Standing control for the
mg-3946 F5 repair in `scripts/onethird_mg75f0_gate_class_closure_demo.py`.

WHAT F5 WAS.  A `--only`/`--gates` subset run of the mg-75f0 class-closure demo
wrote `data/onethird-mg75f0-gate-class-closure.json` -- the COMMITTED record, the
file a reader opens to learn what the demonstration showed -- with a two-row
report carrying the same schema, the same `ALL_PASS: true`, no marker, and exit
0.  It bit mg-3946's audit twice; the committed record had to be restored with
`git checkout --` both times.  Three defects compounded: a partial artifact at
the canonical path saying nothing about being partial; a headline ratio whose
numerator was over the rows RUN and denominator over the FULL mutation set; and
a zero exit over both.

WHY THIS FILE EXISTS, AND WHY IT DOES NOT RUN THE GATE.  The repair lives
entirely in the demo's DRIVER -- which path it writes, which population each
denominator is over, which exit code it returns.  None of that depends on what
the mg-2c34 gate computes, and a full matrix is sixteen gate runs (~21 min in
CI, and considerably worse on a loaded box).  A control that expensive is a
control nobody runs, which is this arc's own named failure mode -- mg-3946 said
it of its 35-minute falsifier in the same breath as the finding this file
closes.  So this substitutes a FAKE `run_case` and drives the real `main()`:
order-seconds, no numpy, no gate, no network, and therefore wired into
`script-controls.yml` rather than into the ~30-minute demo workflow.

The trade is stated rather than hidden: this control cannot tell you whether the
widened gate still catches M5, and it does not try.  That is the mg-75f0 demo's
job and the demo still does it.  This asks the one question the demo cannot ask
about itself -- does a subset of it know that it is a subset?

WHAT IT ASSERTS, seven properties over seven invocations:

  A  a FULL run writes the CANONICAL path and nothing else
  B  a FULL run reports partial_run False / IS_THE_DEMONSTRATION True, and both
     headline denominators are the whole UNSEEN set (5/5 and 5/5)
  C  a SUBSET run writes the PARTIAL path and leaves the canonical file
     BYTE-IDENTICAL -- checked by digest, not by mtime
  D  a SUBSET run's report says partial_run True and records cases_requested /
     gates_requested / full_matrix
  E  a SUBSET run's denominators are the rows IT ran, in the column being
     quoted, and a column it did not request is said in words rather than
     quoted as `0/0`
  F  an unacknowledged SUBSET run exits 2; the same run with --partial-ok exits
     0; and a subset run containing a FAILED case exits 1 either way -- the
     failure path dominates the partiality path, which is what keeps
     mg-3946's falsifier's six predictions meaning what they meant
  G  partiality is decided over SETS: `--gates widened,pre-widening` reordered,
     or `--only` naming every mutation by hand, is the full matrix and must NOT
     be treated as partial

AND IT SELF-TESTS FIRST (three synthetic drifts of its own subject, each of
which MUST be caught), because an assertion nobody has seen fail is a claim:

  D1  PARTIAL_REPORT re-pointed at the canonical path  -> C must fire
  D2  the denominators put back over the full UNSEEN set -> E must fire
  D3  the subset exit code put back to 0                -> F must fire

SAFE IN A DEPTH-1 CHECKOUT, and that needs saying out loud because this arc
began with a script that was not.  This file LOADS the demo module, and the demo
resolves the pinned historical revision `af7fc2df` -- which is exactly what
killed it in CI for 24 h 08 m 55 s (mg-3934).  It is safe here because
`pre_widening_gate_source` is replaced BEFORE `main()` is called, so the pin is
never resolved and no git object is read.  mg-3934's control agrees: it derives
each workflow's scripts and their IMPORT CLOSURE, and `importlib` loading at run
time is not a static import, so this file would not be reported either way --
which is a reason to state the property here rather than to rely on being
checked for it.  If a future edit makes this control resolve a revision, it must
move to a `fetch-depth: 0` job.

Run:  /usr/bin/python3 scripts/onethird_mga471_partial_run_control.py
      (order-seconds; no numpy, no gate, no network)
"""

import io
import os
import sys
import json
import types
import shutil
import hashlib
import tempfile
import contextlib
import importlib.util

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEMO = os.path.join(REPO, "scripts",
                    "onethird_mg75f0_gate_class_closure_demo.py")

# The gate the demo names.  This control never runs it; the path only has to
# exist, because `main()` reads it to decide `gate_sources_differ`.
GATE_REL = os.path.join("scripts", "onethird_mg2c34_n7_overlap_test.py")

CANONICAL = os.path.join("data", "onethird-mg75f0-gate-class-closure.json")
PARTIAL = os.path.join("data",
                       "onethird-mg75f0-gate-class-closure.PARTIAL.json")

# A committed report that must survive every subset run untouched.  Its content
# is irrelevant; that it does not change is the whole point.
SENTINEL = '{"this": "is the committed acceptance record, do not overwrite"}\n'
SENTINEL_SHA = hashlib.sha256(SENTINEL.encode()).hexdigest()


# ------------------------------------------------------------- the fixture ---
def load_demo(source=None):
    """A fresh module object each time, so a drift applied to one scenario
    cannot leak into the next."""
    spec = importlib.util.spec_from_file_location("mg75f0_demo_under_test",
                                                  DEMO)
    mod = importlib.util.module_from_spec(spec)
    if source is None:
        spec.loader.exec_module(mod)
    else:
        exec(compile(source, DEMO, "exec"), mod.__dict__)
    return mod


def make_root():
    root = tempfile.mkdtemp(prefix="mga471-control-")
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    with open(os.path.join(root, GATE_REL), "w") as f:
        f.write("# the widened gate, in the working tree (never executed here)\n")
    with open(os.path.join(root, CANONICAL), "w") as f:
        f.write(SENTINEL)
    return root


def fake_run_case_factory(mod, fail_on=()):
    """Stands in for sixteen gate runs.  Returns exactly the shape `main()`
    consumes, with the exit code the matrix expects -- so every case PASSes
    unless it is named in `fail_on`, which is how property F's failure branch
    is reached without a gate that can fail."""
    def fake_run_case(mutation, gate_variant, pre_src, keep=False):
        want = mod.EXPECTED[(mutation, gate_variant)]
        exit_code = want
        if (mutation, gate_variant) in fail_on:
            # The shape of a real miss: the widened gate let a mutation past.
            exit_code = 0 if want == 1 else 1
        reported = exit_code == 1
        # M3/M4/M8 are the rows the pre-widening gate actually EXERCISED, so
        # their stdout moves; the rest are byte-identical to the unmutated run.
        moved = mutation in ("M3", "M4", "M8")
        digest = hashlib.sha256(
            (f"{mutation if moved else 'base'}-{gate_variant}").encode()
        ).hexdigest()
        return {
            "mutation": mutation, "gate": gate_variant,
            "applied": None if mutation == "none" else {"file": "x", "occurrences": 1},
            "exit": exit_code,
            "gate_failures": ["synthetic control failure"] if reported else [],
            "identity_lines": {}, "measured": {}, "field_census_lines": [],
            "stdout_sha256": digest, "stdout_bytes": 1,
            "stderr_tail": "",
        }
    return fake_run_case


def drive(argv, root, fail_on=(), source=None):
    """Run the real `main()` against the fixture and hand back everything the
    assertions need: exit code, stdout, and whichever report it wrote."""
    mod = load_demo(source)
    mod.REPO = root
    mod.pre_widening_gate_source = lambda: ("af7fc2df", "PRE-WIDENING SOURCE")
    mod.run_case = fake_run_case_factory(mod, fail_on)
    old_argv = sys.argv
    sys.argv = ["onethird_mg75f0_gate_class_closure_demo.py"] + argv
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            rc = mod.main()
    finally:
        sys.argv = old_argv
    out = buf.getvalue()
    written = {}
    for rel in (CANONICAL, PARTIAL):
        p = os.path.join(root, rel)
        if os.path.exists(p):
            with open(p) as f:
                body = f.read()
            written[rel] = body
    return rc, out, written


# ------------------------------------------------------------- assertions ---
UNSEEN_ALL = ["M5", "M6", "M7", "M8", "M9"]


def check(problems, cond, label):
    if not cond:
        problems.append(label)
    return cond


def scenario_full(problems, source=None):
    """A and B: the demonstration itself, unchanged by the repair."""
    root = make_root()
    try:
        rc, out, written = drive([], root, source=source)
        check(problems, rc == 0, "A/B: full run did not exit 0")
        check(problems, PARTIAL not in written,
              "A: full run wrote the PARTIAL path")
        check(problems, CANONICAL in written,
              "A: full run did not write the canonical path")
        rep = json.loads(written[CANONICAL])
        check(problems, rep["partial_run"] is False,
              "B: full run reported partial_run True")
        check(problems, rep["IS_THE_DEMONSTRATION"] is True,
              "B: full run reported IS_THE_DEMONSTRATION False")
        check(problems,
              sorted(rep["unseen_mutations_run_widened"]) == UNSEEN_ALL,
              "B: full run's widened denominator is not the whole UNSEEN set")
        check(problems,
              sorted(rep["unseen_mutations_run_pre_widening"]) == UNSEEN_ALL,
              "B: full run's pre-widening denominator is not the whole UNSEEN "
              "set")
        check(problems, "5/5 mutations" in out.replace("\n", " "),
              "B: full run's headline is not 5/5")
        check(problems, "PARTIAL" not in out,
              "B: full run announced itself as partial")
        return out
    finally:
        shutil.rmtree(root, ignore_errors=True)


def scenario_subset(problems, extra_argv, expect_rc, label, source=None):
    """C, D, E and F over one subset invocation."""
    root = make_root()
    try:
        rc, out, written = drive(["--only", "M9", "--gates", "widened"]
                                 + extra_argv, root, source=source)
        check(problems, rc == expect_rc,
              f"F: subset run ({label}) exited {rc}, expected {expect_rc}")

        # C -- the canonical record, by digest rather than by mtime.
        got = hashlib.sha256(written.get(CANONICAL, "").encode()).hexdigest()
        check(problems, got == SENTINEL_SHA,
              f"C: subset run ({label}) changed the canonical report")
        check(problems, PARTIAL in written,
              f"C: subset run ({label}) did not write the PARTIAL path")
        if PARTIAL not in written:
            return out
        rep = json.loads(written[PARTIAL])

        # D -- the report says what it ran.
        check(problems, rep["partial_run"] is True,
              f"D: subset run ({label}) reported partial_run False")
        check(problems, rep["IS_THE_DEMONSTRATION"] is False,
              f"D: subset run ({label}) claimed to be the demonstration")
        check(problems, rep["cases_requested"] == ["none", "M9"],
              f"D: subset run ({label}) cases_requested is "
              f"{rep.get('cases_requested')!r}")
        check(problems, rep["gates_requested"] == ["widened"],
              f"D: subset run ({label}) gates_requested is "
              f"{rep.get('gates_requested')!r}")
        check(problems,
              sorted(rep["full_matrix"]["cases"]) ==
              sorted(["none", "M3", "M4", "M5", "M6", "M7", "M8", "M9"]),
              f"D: subset run ({label}) full_matrix.cases is wrong")

        # E -- one population per ratio.
        check(problems, rep["unseen_mutations_run_widened"] == ["M9"],
              f"E: subset run ({label}) widened denominator is "
              f"{rep.get('unseen_mutations_run_widened')!r}, not ['M9']")
        check(problems, rep["unseen_mutations_run_pre_widening"] == [],
              f"E: subset run ({label}) pre-widening denominator is not empty "
              f"over a run that asked for no pre-widening column")
        if expect_rc != 1:
            flat = " ".join(out.split())
            check(problems, "1/1 were caught by the widened gate" in flat,
                  f"E: subset run ({label}) did not print 1/1 -- got a ratio "
                  f"whose halves are over different populations")
            check(problems, "the pre-widening column was not run" in flat,
                  f"E: subset run ({label}) quoted a ratio for a column it "
                  f"never ran")
            for bad in ("/5", "/6"):
                check(problems, f"1{bad}" not in flat,
                      f"E: subset run ({label}) printed 1{bad} -- the F5 "
                      f"defect verbatim")
        return out
    finally:
        shutil.rmtree(root, ignore_errors=True)


def scenario_not_partial(problems, argv, label, source=None):
    """G: partiality is a question about SETS, not about argument strings."""
    root = make_root()
    try:
        rc, out, written = drive(argv, root, source=source)
        check(problems, rc == 0, f"G: {label} exited {rc}, expected 0")
        check(problems, CANONICAL in written and PARTIAL not in written,
              f"G: {label} was treated as partial")
        if CANONICAL in written:
            rep = json.loads(written[CANONICAL])
            check(problems, rep["partial_run"] is False,
                  f"G: {label} reported partial_run True")
        return out
    finally:
        shutil.rmtree(root, ignore_errors=True)


def all_properties(source=None):
    """Every assertion, over one subject.  Returns the problems it found."""
    problems = []
    scenario_full(problems, source)
    scenario_subset(problems, [], 2, "no --partial-ok", source)
    scenario_subset(problems, ["--partial-ok"], 0, "--partial-ok", source)
    # F's failure branch: a subset run whose one case MISSES.  It must exit 1
    # -- not 2 and not 0 -- or mg-3946's falsifier stops distinguishing a demo
    # that rejected a drift from a demo that merely ran a subset.
    root = make_root()
    try:
        rc, _, _ = drive(["--only", "M9", "--gates", "widened",
                          "--partial-ok"], root,
                         fail_on=(("M9", "widened"),), source=source)
        check(problems, rc == 1,
              f"F: a subset run with a FAILED case exited {rc}, expected 1 "
              f"-- the failure path must dominate the partiality path")
    finally:
        shutil.rmtree(root, ignore_errors=True)
    root = make_root()
    try:
        rc, _, _ = drive(["--only", "M9", "--gates", "widened"], root,
                         fail_on=(("M9", "widened"),), source=source)
        check(problems, rc == 1,
              f"F: a failed subset run without --partial-ok exited {rc}, "
              f"expected 1")
    finally:
        shutil.rmtree(root, ignore_errors=True)
    scenario_not_partial(problems, ["--gates", "widened,pre-widening"],
                         "the two columns in the other order", source)
    scenario_not_partial(problems,
                         ["--only", "M3,M4,M5,M6,M7,M8,M9"],
                         "every mutation named by hand", source)
    return problems


# ------------------------------------------------------------- self-tests ---
# Three drifts of this control's own subject.  Each MUST be caught; a control
# that has never been seen to fire is a claim, not a control.  Same discipline
# the demo applies to its own mutations, including the asserted anchor count.
def _sub(src, old, new, what):
    got = src.count(old)
    if got != 1:
        raise SystemExit(f"mg-a471 self-test {what}: anchor found {got} times, "
                         f"expected 1.  The control cannot vouch for itself.\n"
                         f"Anchor:\n{old}")
    return src.replace(old, new)


def drift_partial_path_is_canonical(src):
    return _sub(src,
                'PARTIAL_REPORT = os.path.join(\n'
                '    "data", "onethird-mg75f0-gate-class-closure.PARTIAL.json")',
                'PARTIAL_REPORT = REPORT',
                "D1 partial-path-is-canonical")


def drift_denominators_over_the_full_set(src):
    return _sub(src,
                "    unseen_run_widened = [m for m in unseen "
                'if _ran(m, "widened")]\n'
                "    unseen_run_pre = [m for m in unseen "
                'if _ran(m, "pre-widening")]',
                "    unseen_run_widened = list(unseen)\n"
                "    unseen_run_pre = list(unseen)",
                "D2 denominators-over-the-full-set")


def drift_subset_exits_zero(src):
    return _sub(src,
                '        print("Exiting 2: a subset run is not a passing '
                'demonstration, and "\n'
                '              "`... && echo ok`\\nmust not be able to say it '
                'was.  Pass "\n'
                '              "--partial-ok if you meant to ask only\\nabout '
                'the rows you "\n'
                '              "named.")\n'
                "        return 2",
                "        return 0",
                "D3 subset-exits-zero")


SELFTESTS = [
    ("D1 partial report path re-pointed at the canonical path",
     drift_partial_path_is_canonical,
     "C: a subset run would overwrite the committed record"),
    ("D2 both denominators put back over the full UNSEEN set",
     drift_denominators_over_the_full_set,
     "E: the ratio's halves would be over different populations again"),
    ("D3 the subset exit code put back to 0",
     drift_subset_exits_zero,
     "F: `--only M3 && echo ok` would say the demonstration passed"),
]


def main():
    print("=" * 78)
    print("mg-a471 -- A SUBSET RUN IS NOT THE DEMONSTRATION")
    print("  standing control for the mg-3946 F5 repair in")
    print(f"  {os.path.relpath(DEMO, REPO)}")
    print("=" * 78)

    with open(DEMO) as f:
        pristine = f.read()

    print("\n=== SELF-TEST: three drifts of the subject, each of which MUST "
          "be caught")
    selftest_ok = True
    for label, drift, expect in SELFTESTS:
        drifted = drift(pristine)
        found = all_properties(drifted)
        if found:
            print(f"  CAUGHT   {label}")
            print(f"           -> {found[0]}")
        else:
            selftest_ok = False
            print(f"  MISSED   {label}")
            print(f"           this control did NOT fire.  It was supposed to "
                  f"report:\n           {expect}")

    print("\n=== THE SUBJECT AS COMMITTED")
    problems = all_properties(None)
    if problems:
        print(f"  {len(problems)} PROBLEM(S):")
        for p in problems:
            print(f"    - {p}")
    else:
        print("  all seven properties (A-G) hold over seven invocations")

    print()
    print("=" * 78)
    if not selftest_ok:
        print("FAILED: this control cannot detect a defect it is written to "
              "detect.  Fix\nthe control before trusting anything it says "
              "about the demo.")
        return 1
    if problems:
        print("FAILED: the mg-3946 F5 repair is not holding.  A --only/--gates "
              "subset run of\nthe mg-75f0 demo must not write the canonical "
              "report, must quote both halves\nof each ratio over one "
              "population, and must not exit 0 unacknowledged.")
        return 1
    print("PASSED: a subset run writes the PARTIAL path, leaves the committed "
          "report\nbyte-identical, records cases_requested/gates_requested/"
          "partial_run, quotes\neach denominator over the rows it ran, and "
          "exits 2 unless acknowledged -- and\nthree drifts that would undo "
          "each of those were caught.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
