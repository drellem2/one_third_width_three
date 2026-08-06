#!/usr/bin/env python3
"""
mg-a266 -- CAN `ALL_PASS` BE TRUE OVER AN EMPTY POPULATION?  An enumeration,
not a spot check.

INDEPENDENT AUDIT of mg-9a59 (`c64fe68`), which is DONE.  This file does not
re-do it and does not re-run its control.  It asks the one question that a
green control cannot answer about itself: is the vacuous pass UNREACHABLE, or
did it merely not happen on the invocations somebody thought to try?

THE DEFECT CLASS, and it is a class -- five siblings tonight:

    exit 0 over zero gate runs                     (mg-9a59, the parent)
    4 of 17 verdicts as the literal False          (mg-0120)
    a row scoring a hardcoded string literal       (mg-8af0)
    a checker returning 0 for an absent document   (mg-1d26)
    43 probes reading a file their own run emptied (mg-ec63)

Every one is a control that reported success because it examined nothing.  So
the property to establish is not "the empty case now exits 2" -- that is one
invocation -- but that EMPTINESS AND SUCCESS ARE DISTINGUISHABLE IN THE OUTPUT,
over the whole space of ways in.

WHAT THIS FILE DOES, in four parts.

  PART 1  ENUMERATION.  128 invocations of the demo's `main()`: 8 spellings of
          `--only` x 8 spellings of `--gates` x `--partial-ok` present/absent.
          The population is the cross product, not a hand-picked list, so
          "no route was found" is a statement about the space rather than
          about the author's imagination.  Five invariants are asserted on
          every one.  The grain of an invocation is one call to `main()`; the
          grain of an assertion is one boolean.

  PART 2  DISTINGUISHABILITY, which is the actual instruction.  Three runs --
          MEASURED-NOTHING, MEASURED-AND-FAILED, MEASURED-AND-PASSED -- and a
          printed table of what a reader can see of each: exit code, the
          artifact's verdict field, the artifact's population field, the
          stdout banner.  A distinction only visible by reading the source is
          not a distinction the output makes, so each discriminator is quoted
          from the run's own output.  This part also records, as a MEASURED
          FACT rather than a complaint, which fields fail to discriminate.

  PART 3  THE POSITIVE CONTROL, without which parts 1 and 2 are worth nothing.
          A negative needs an instrument that could have shown the positive.
          The same enumeration is run against THREE broken subjects -- the
          demo's own pre-repair source at `c64fe68^`, and the two halves of the
          repair drifted out one at a time -- and each MUST produce at least
          one violation.  If a broken subject comes back clean, this file exits
          non-zero and says its clean result over the repaired subject means
          nothing.

  PART 4  WHAT THE STANDING CONTROL CANNOT REACH.  The parent extended
          `onethird_mga471_partial_run_control.py` from 7 to 11 invocations.
          This part re-derives those 11 by recording the argv of every call it
          makes -- not by reading them off the source -- and reports which
          members of the 128-invocation space no property of it examines.

AND IT DOES NOT CARRY THE DEFECT IT AUDITS.  A checker that passes over zero
checks is exactly the shape under audit, so this file refuses a verdict over an
empty population of its own: `ALL_HELD` is conjoined with a non-empty
assertion count, the count is printed next to the verdict, and `--only` naming
nothing exits 2 rather than 0.  Part 3's self-test drifts that guard out and
requires it to fire.

Run:  /usr/bin/python3 scripts/onethird_mga266_vacuity_enumeration.py
      (order-seconds; no numpy, no mg-2c34 gate, no network beyond one
       `git show` of a pinned in-repo revision)
      --only V1,V3     run a subset of the invariants
      --real-empty     ALSO run the empty case UNSTUBBED, as a subprocess,
                       end to end.  Costs nothing: the empty case performs
                       zero gate runs by construction, which is the point.
"""

import io
import os
import re
import sys
import json
import shutil
import hashlib
import argparse
import tempfile
import subprocess
import contextlib
import importlib.util

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEMO_REL = os.path.join("scripts", "onethird_mg75f0_gate_class_closure_demo.py")
DEMO = os.path.join(REPO, DEMO_REL)
CONTROL = os.path.join(REPO, "scripts",
                       "onethird_mga471_partial_run_control.py")
GATE_REL = os.path.join("scripts", "onethird_mg2c34_n7_overlap_test.py")

CANONICAL = os.path.join("data", "onethird-mg75f0-gate-class-closure.json")
PARTIAL = os.path.join("data",
                       "onethird-mg75f0-gate-class-closure.PARTIAL.json")

REPORT = os.path.join("data", "onethird-mga266-vacuity-enumeration.json")

# The revision the parent repaired ON TOP OF.  Pinned, not derived from branch
# topology, for the same reason the demo pins its own baseline: once this lands
# on main a merge-base would drift onto the repaired source and the positive
# control would silently stop being one.
PRE_REPAIR_REV = "c64fe68^"     # the commit before mg-9a59's repair

SENTINEL = '{"this": "is the committed acceptance record, do not overwrite"}\n'
SENTINEL_SHA = hashlib.sha256(SENTINEL.encode()).hexdigest()


# ------------------------------------------------------------- the fixture ---
def demo_source(rev=None):
    """The subject's source: the working tree, or a pinned revision."""
    if rev is None:
        with open(DEMO) as f:
            return f.read()
    show = subprocess.run(["git", "show", f"{rev}:{DEMO_REL}"],
                          cwd=REPO, capture_output=True, text=True)
    if show.returncode != 0:
        raise SystemExit(f"cannot read {DEMO_REL} at {rev}: "
                         f"{show.stderr.strip()}")
    return show.stdout


def load_demo(source):
    spec = importlib.util.spec_from_file_location("mga266_subject", DEMO)
    mod = importlib.util.module_from_spec(spec)
    exec(compile(source, DEMO, "exec"), mod.__dict__)
    return mod


def make_root():
    root = tempfile.mkdtemp(prefix="mga266-enum-")
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    with open(os.path.join(root, GATE_REL), "w") as f:
        f.write("# the widened gate in the working tree (never executed here)\n")
    with open(os.path.join(root, CANONICAL), "w") as f:
        f.write(SENTINEL)
    return root


def fake_run_case_factory(mod, fail_on=()):
    """Stands in for up to sixteen real gate runs at ~50 s each.

    THE SUBSTITUTION IS THE DRIVER'S OWN BOUNDARY: both defects under audit
    live in `main()`, above `run_case`, and every quantity this file asserts on
    -- the exit code, `ALL_PASS`, `n_gate_runs`, the column sentence -- is
    computed by `main()` from the shape `run_case` returns, never from the gate.
    Stated rather than glossed: no mg-2c34 gate is executed by this file, so
    `n_gate_runs: 16` below counts DRIVER ITERATIONS, not gate executions."""
    def fake_run_case(mutation, gate_variant, pre_src, keep=False):
        want = mod.EXPECTED[(mutation, gate_variant)]
        exit_code = want
        if (mutation, gate_variant) in fail_on:
            exit_code = 0 if want == 1 else 1
        reported = exit_code == 1
        moved = mutation in ("M3", "M4", "M8")
        digest = hashlib.sha256(
            f"{mutation if moved else 'base'}-{gate_variant}".encode()
        ).hexdigest()
        return {"mutation": mutation, "gate": gate_variant,
                "applied": None if mutation == "none"
                else {"file": "x", "occurrences": 1},
                "exit": exit_code,
                "gate_failures": ["synthetic control failure"] if reported
                else [],
                "identity_lines": {}, "measured": {}, "field_census_lines": [],
                "stdout_sha256": digest, "stdout_bytes": 1, "stderr_tail": ""}
    return fake_run_case


def drive(argv, source, fail_on=()):
    """One invocation of the subject's `main()` against a throwaway fixture.

    Returns everything a READER of that run could see: the exit code, the
    stdout, and whichever artifact it wrote.  A raise is an outcome too and is
    recorded rather than swallowed -- `--only MZZZ` raises, and a crash is a
    different finding from a vacuous pass."""
    root = make_root()
    try:
        mod = load_demo(source)
        mod.REPO = root
        mod.pre_widening_gate_source = lambda: ("af7fc2df", "PRE-WIDENING SRC")
        mod.run_case = fake_run_case_factory(mod, fail_on)
        old_argv = sys.argv
        sys.argv = ["onethird_mg75f0_gate_class_closure_demo.py"] + argv
        buf = io.StringIO()
        raised = None
        rc = None
        try:
            with contextlib.redirect_stdout(buf):
                rc = mod.main()
        except SystemExit as e:
            # argparse and `raise SystemExit(msg)` both land here.  A string
            # argument means exit 1; an int means that int.
            rc = e.code if isinstance(e.code, int) else 1
            raised = f"SystemExit: {e.code!r}"
        except BaseException as e:            # noqa: BLE001 -- an outcome
            rc = None
            raised = f"{type(e).__name__}: {e}"
        finally:
            sys.argv = old_argv
        out = buf.getvalue()
        written = {}
        for rel in (CANONICAL, PARTIAL):
            p = os.path.join(root, rel)
            if os.path.exists(p):
                with open(p) as f:
                    written[rel] = f.read()
        canonical_sha = hashlib.sha256(
            written.get(CANONICAL, "").encode()).hexdigest()
        report = None
        for rel in (PARTIAL, CANONICAL):
            if rel in written and rel != CANONICAL or (
                    rel == CANONICAL and canonical_sha != SENTINEL_SHA
                    and CANONICAL in written):
                try:
                    report = json.loads(written[rel])
                    break
                except json.JSONDecodeError:
                    pass
        return {"argv": argv, "exit": rc, "raised": raised, "stdout": out,
                "report": report,
                # NOT "files this run wrote": the canonical path is SEEDED
                # with the sentinel by `make_root`, so it is present after
                # every run whether or not the run touched it.  The two
                # questions are kept apart -- what exists, and whether the
                # committed record survived unchanged.
                "paths_present_after": sorted(written),
                "partial_written": PARTIAL in written,
                "canonical_sha": canonical_sha}
    finally:
        shutil.rmtree(root, ignore_errors=True)


# --------------------------------------------------------- the enumeration ---
# The argv space.  A CROSS PRODUCT, deliberately, so the conclusion is about
# the space and not about which invocations occurred to the author -- that is
# the exact failure the parent's own control had (7 invocations, all
# `--only M9 --gates widened` variants, none of which could reach either
# defect).  Each list below is a SPELLING of one flag, including the spellings
# that are malformed: an empty value, a lone separator, a name that is not a
# member.
ONLY_SPELLINGS = [
    [],                                     # every mutation
    ["--only", ""],                         # empty value -> falls back to all
    ["--only", "M9"],                       # one UNSEEN row
    ["--only", "M3"],                       # one SEEN row (the item-2 case)
    ["--only", "none"],                     # names only the unmutated case
    ["--only", ","],                        # lone separator -> empty ids
    ["--only", "MZZZ"],                     # a row that does not exist
    ["--only", "M3,M4,M5,M6,M7,M8,M9"],     # the full set, named by hand
]
GATES_SPELLINGS = [
    [],                                     # both columns
    ["--gates", "widened"],
    ["--gates", "pre-widening"],
    ["--gates", "widened,pre-widening"],    # both, reordered
    ["--gates", ""],                        # THE EMPTY POPULATION
    ["--gates", ","],                       # lone separator -> also empty
    ["--gates", ",,"],                      # ditto
    ["--gates", "bogus"],                   # a column that does not exist
]
PARTIAL_SPELLINGS = [[], ["--partial-ok"]]


def argv_space():
    space = []
    for o in ONLY_SPELLINGS:
        for g in GATES_SPELLINGS:
            for p in PARTIAL_SPELLINGS:
                space.append(o + g + p)
    return space


class Ledger:
    """Problems AND the population they were found over.

    The defect under audit is a verdict computed over an empty population, so
    this file carries the size of its own population next to its own verdict.
    `ALL_HELD` is conjoined with `checks > 0` for the same reason the subject's
    `ALL_PASS` is conjoined with `bool(results)`."""

    def __init__(self):
        self.problems = []
        self.checks = 0
        self.invocations = 0
        self.by_invariant = {}

    def check(self, cond, invariant, label):
        self.checks += 1
        self.by_invariant[invariant] = self.by_invariant.get(invariant, 0) + 1
        if not cond:
            self.problems.append(f"{invariant}: {label}")
        return cond


INVARIANTS = {
    "V1": "no invocation writes an artifact carrying ALL_PASS true over "
          "n_gate_runs 0 -- the vacuous pass, in the artifact",
    "V2": "no invocation exits 0 without a non-empty population behind it -- "
          "the vacuous pass, in the exit code",
    "V3": "an empty population is ANNOUNCED: exit 2, and the literal words "
          "ZERO GATE RUNS in the output",
    "V4": "the reported population size equals the reported population: "
          "n_gate_runs == len(cases), so the count cannot drift from the list",
    "V5": "the committed canonical report is never overwritten except by a "
          "genuine FULL run",
}


def enumerate_space(led, source, invariants, fail_on=()):
    """PART 1.  Every invocation in the space, five invariants on each."""
    rows = []
    for argv in argv_space():
        r = drive(argv, source, fail_on=fail_on)
        rep = r["report"]
        n = None if rep is None else rep.get("n_gate_runs")
        ap = None if rep is None else rep.get("ALL_PASS")
        # `n_gate_runs` is absent from a pre-repair report; fall back to the
        # list it is supposed to count, so the pre-repair source is measured
        # on the same axis rather than excused for not having the field.
        if n is None and rep is not None:
            n = len(rep.get("cases", []))
        spell = " ".join(argv) or "(no flags)"

        if "V1" in invariants and rep is not None:
            led.check(not (n == 0 and ap is True), "V1",
                      f"`{spell}` wrote ALL_PASS {ap!r} over n_gate_runs {n} "
                      f"-- a verdict over an empty population")
        if "V2" in invariants:
            led.check(not (r["exit"] == 0 and (rep is None or not n)), "V2",
                      f"`{spell}` exited 0 with "
                      f"{'no report at all' if rep is None else f'n_gate_runs {n}'}")
        if "V3" in invariants and rep is not None and n == 0:
            led.check(r["exit"] == 2, "V3",
                      f"`{spell}` measured nothing but exited {r['exit']!r}, "
                      f"expected 2")
            led.check("ZERO GATE RUNS" in r["stdout"], "V3",
                      f"`{spell}` measured nothing and never said so: no "
                      f"'ZERO GATE RUNS' in its output")
        if "V4" in invariants and rep is not None and "n_gate_runs" in rep:
            led.check(rep["n_gate_runs"] == len(rep.get("cases", [])), "V4",
                      f"`{spell}` reports n_gate_runs "
                      f"{rep['n_gate_runs']} over {len(rep.get('cases', []))} "
                      f"cases -- the count and the list disagree")
        if "V5" in invariants:
            full = (rep is not None and rep.get("partial_run") is False)
            led.check(full or r["canonical_sha"] == SENTINEL_SHA, "V5",
                      f"`{spell}` overwrote the committed canonical report "
                      f"without being a full run")
        led.invocations += 1
        rows.append({"argv": argv, "spelling": spell, "exit": r["exit"],
                     "raised": r["raised"], "n_gate_runs": n, "ALL_PASS": ap,
                     "partial_written": r["partial_written"],
                     "said_zero_gate_runs": "ZERO GATE RUNS" in r["stdout"],
                     "canonical_untouched":
                         r["canonical_sha"] == SENTINEL_SHA})
    return rows


# ------------------------------------------------------ distinguishability ---
def _quote(out, needle, width=76):
    for line in out.splitlines():
        if needle in line:
            return line.strip()[:width]
    return None


def distinguishability(led, source):
    """PART 2.  The instruction, literally.

    Three runs that a reader must be able to tell apart, and the evidence is
    quoted FROM EACH RUN'S OWN OUTPUT -- not from the source.  The three:

      EMPTY    `--gates "" --partial-ok`  -- measured nothing
      FAILED   a full run in which the widened gate lets M9 past
      PASSED   a full run in which every case holds

    A discriminator is a field or line whose value differs across all three.
    Anything that does NOT differ is recorded as a NON-discriminator, because
    the honest answer to "how does a reader tell them apart" has to include
    what will not help them."""
    runs = {
        "EMPTY": drive(["--gates", "", "--partial-ok"], source),
        "FAILED": drive([], source, fail_on=(("M9", "widened"),)),
        "PASSED": drive([], source),
    }
    table = {}
    for name, r in runs.items():
        rep = r["report"] or {}
        table[name] = {
            "exit": r["exit"],
            "artifact_ALL_PASS": rep.get("ALL_PASS"),
            "artifact_n_gate_runs": rep.get(
                "n_gate_runs", len(rep.get("cases", []))),
            "artifact_len_cases": len(rep.get("cases", [])),
            "partial_written": r["partial_written"],
            "stdout_banner": (_quote(r["stdout"], "ZERO GATE RUNS")
                              or _quote(r["stdout"], "DEMONSTRATION FAILED")
                              or _quote(r["stdout"], "Demonstration complete")),
        }

    fields = ["exit", "artifact_ALL_PASS", "artifact_n_gate_runs",
              "artifact_len_cases", "stdout_banner"]

    def separates(field, a, b):
        return (json.dumps(table[a][field], sort_keys=True)
                != json.dumps(table[b][field], sort_keys=True))

    # WHICH FIELD SEPARATES WHICH PAIR, measured per pair rather than as one
    # three-way verdict.  The first draft of this file asserted that a single
    # field must take three distinct values across the three runs, and
    # `n_gate_runs` failed it -- 0 / 16 / 16.  That assertion was MIS-SPECIFIED,
    # not a defect found: the property the instruction asks for is that
    # EMPTINESS is separable from success, and a field that separates EMPTY
    # from both others does that whether or not it also separates the other
    # two from each other.  Kept as a per-pair matrix because the mis-scoped
    # version hid the finding that the per-pair version makes obvious --
    # see EMPTY-vs-FAILED on `artifact_ALL_PASS`.
    pairs = [("EMPTY", "PASSED"), ("EMPTY", "FAILED"), ("FAILED", "PASSED")]
    verdict = {f: {f"{a}-vs-{b}": separates(f, a, b) for a, b in pairs}
               for f in fields}
    verdict_all3 = {f: len({json.dumps(table[k][f], sort_keys=True)
                            for k in table}) == 3 for f in fields}

    # THE ASSERTIONS.  Not "some field differs somewhere" -- that is satisfied
    # by noise.  Emptiness must be separable from success AND from failure, in
    # the exit code (what a shell sees) and on the artifact (what a reader
    # opens six weeks later), and the output must NAME the emptiness rather
    # than leaving a reader to infer it from a number being zero.
    led.check(separates("exit", "EMPTY", "PASSED"), "D",
              f"the empty run's exit {table['EMPTY']['exit']} collides with "
              f"the passing run's {table['PASSED']['exit']}")
    led.check(separates("exit", "EMPTY", "FAILED"), "D",
              f"the empty run's exit {table['EMPTY']['exit']} collides with "
              f"the failing run's {table['FAILED']['exit']}")
    led.check(any(verdict[f]["EMPTY-vs-PASSED"]
                  for f in ("artifact_ALL_PASS", "artifact_n_gate_runs")), "D",
              "no artifact field separates the empty run from the passing run")
    led.check(any(verdict[f]["EMPTY-vs-FAILED"]
                  for f in ("artifact_ALL_PASS", "artifact_n_gate_runs")), "D",
              "no artifact field separates the empty run from the failing run "
              "-- a reader opening the report cannot tell 'measured nothing' "
              "from 'measured and failed'")
    led.check(table["EMPTY"]["stdout_banner"] is not None
              and "ZERO GATE RUNS" in table["EMPTY"]["stdout_banner"], "D",
              "the empty run's output carries no banner naming its emptiness")
    led.check(table["EMPTY"]["artifact_ALL_PASS"] is False, "D",
              "the empty run's artifact does not say ALL_PASS false")

    # RECORDED, NOT ASSERTED: the residual.  `ALL_PASS` alone is two-valued
    # over three states, so it separates EMPTY from PASSED but NOT from
    # FAILED.  A reader who greps only that field sees a failure where there
    # was an emptiness.  That is the SAFE direction of the confusion -- an
    # empty run is never mistaken for a passing one, which is the defect the
    # parent was sent to close -- so it is reported as a residual rather than
    # asserted as a failure.  Naming it is the point: the distinction the
    # output makes is made by a SECOND field, and a reader has to know to look.
    residual = {
        "ALL_PASS_separates_EMPTY_from_PASSED":
            verdict["artifact_ALL_PASS"]["EMPTY-vs-PASSED"],
        "ALL_PASS_separates_EMPTY_from_FAILED":
            verdict["artifact_ALL_PASS"]["EMPTY-vs-FAILED"],
        "fields_separating_EMPTY_from_FAILED":
            [f for f in fields if verdict[f]["EMPTY-vs-FAILED"]],
        "fields_taking_three_distinct_values": [f for f in fields
                                                if verdict_all3[f]],
        "note": "no single ARTIFACT field takes three distinct values; the "
                "pair (ALL_PASS, n_gate_runs) does.  The exit code alone does.",
    }
    return table, verdict, verdict_all3, residual


# ------------------------------------------------------- positive controls ---
def _sub(src, old, new, label):
    if src.count(old) != 1:
        raise SystemExit(f"{label}: anchor found {src.count(old)} times, "
                         f"expected 1 -- the drift would be a NO-OP and the "
                         f"positive control would be a lie.  Anchor:\n{old}")
    return src.replace(old, new)


def drift_guard_removed(src):
    """The exit-code half of the parent's repair, removed."""
    return _sub(src, "    if not results:\n        print()\n",
                "    if False:\n        print()\n", "PC2 guard-removed")


def drift_all_pass_unconditioned(src):
    """The artifact half, removed.  Separate from PC2 because a report can go
    on saying ALL_PASS true long after the exit code stopped."""
    return _sub(src, '        "ALL_PASS": bool(results) and ok,',
                '        "ALL_PASS": ok,', "PC3 all-pass-unconditioned")


def positive_controls(led, invariants):
    """PART 3.  A NEGATIVE NEEDS AN INSTRUMENT THAT COULD HAVE SHOWN THE
    POSITIVE.  Three broken subjects; each must make the enumeration fire."""
    repaired = demo_source()
    subjects = [
        ("PC1 pre-repair source at " + PRE_REPAIR_REV,
         demo_source(PRE_REPAIR_REV),
         "the vacuous exit 0 as the parent found it"),
        ("PC2 zero-population guard removed", drift_guard_removed(repaired),
         "the exit-code half of the repair drifted out"),
        ("PC3 ALL_PASS unconditioned", drift_all_pass_unconditioned(repaired),
         "the artifact half of the repair drifted out"),
    ]
    out = []
    for name, src, what in subjects:
        probe = Ledger()
        enumerate_space(probe, src, invariants)
        fired = len(probe.problems)
        led.check(fired > 0, "PC",
                  f"{name} produced ZERO violations over "
                  f"{probe.checks} assertions -- this enumeration cannot see "
                  f"the defect it reports absent, so its clean result over the "
                  f"repaired subject is worth nothing")
        out.append({"subject": name, "what": what,
                    "violations": fired, "assertions": probe.checks,
                    "invocations": probe.invocations,
                    "first_three": probe.problems[:3],
                    "invariants_that_fired": sorted(
                        {p.split(":")[0] for p in probe.problems})})
    return out


# ------------------------------------------------------- coverage of the ---
def control_invocations():
    """PART 4.  The 11 invocations the parent's control actually makes,
    RE-DERIVED by recording the argv of every call it drives -- not read off
    the source, because a comment claiming eleven is a claim and a recording
    is an observation."""
    spec = importlib.util.spec_from_file_location("mga471_control", CONTROL)
    mod = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(mod)
    except BaseException as e:                          # noqa: BLE001
        return None, f"could not import the control: {type(e).__name__}: {e}"
    seen = []
    real_drive = mod.drive

    def recording_drive(argv, root, fail_on=(), source=None):
        seen.append(list(argv))
        return real_drive(argv, root, fail_on=fail_on, source=source)

    mod.drive = recording_drive
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            mod.main()
    except BaseException as e:                          # noqa: BLE001
        return seen, f"the control raised during recording: {e}"
    return seen, None


def coverage(led):
    seen, err = control_invocations()
    if seen is None:
        led.check(False, "COV", f"could not re-derive the control's "
                                f"invocations: {err}")
        return {"error": err}
    # A subject invocation is one that drives the demo.  The control also
    # drives it under drifted sources; the argv is what matters here.
    normalised = {" ".join(a) or "(no flags)" for a in seen}
    space = {" ".join(a) or "(no flags)" for a in argv_space()}
    unreached = sorted(space - normalised)
    return {"control_invocations_recorded": len(seen),
            "distinct_argv_spellings_in_the_control": sorted(normalised),
            "argv_space_size": len(space),
            "spellings_the_control_never_drives": unreached,
            "n_unreached": len(unreached),
            "note": "the control's population is 11 invocations of main(); "
                    "this file's is 128 spellings.  The difference is not a "
                    "defect in the control -- a control is allowed to be "
                    "narrower than an audit -- but it IS the answer to 'what "
                    "can the invocation set still not reach', which the "
                    "parent's own doc says there will always be something of.",
            "recording_error": err}


# -------------------------------------------------------- the real, empty ---
def real_empty_run():
    """The empty case, UNSTUBBED, as a subprocess, end to end.

    Affordable for exactly the reason under audit: a run with an empty gate
    list performs ZERO gate runs, so the ~13 minutes a full matrix costs is
    ~0.2 s here.  Everything else in this file goes through the stub; this one
    does not, so at least one measurement of the empty case is of the real
    program and not of a fixture."""
    canon = os.path.join(REPO, CANONICAL)
    before = None
    if os.path.exists(canon):
        with open(canon, "rb") as f:
            before = hashlib.sha256(f.read()).hexdigest()
    # Cleared first, so the report read back below is THIS run's and not a
    # leftover -- the sibling defect mg-ec63 (43 probes reading a file their
    # own run had emptied) is the same mistake with the sign flipped.
    if os.path.exists(os.path.join(REPO, PARTIAL)):
        os.remove(os.path.join(REPO, PARTIAL))
    proc = subprocess.run(
        [sys.executable, DEMO_REL, "--gates", "", "--partial-ok"],
        cwd=REPO, capture_output=True, text=True)
    after = None
    if os.path.exists(canon):
        with open(canon, "rb") as f:
            after = hashlib.sha256(f.read()).hexdigest()
    partial = os.path.join(REPO, PARTIAL)
    rep = None
    if os.path.exists(partial):
        with open(partial) as f:
            rep = json.load(f)
    return {"cmd": f"{DEMO_REL} --gates '' --partial-ok",
            "exit": proc.returncode,
            "said_zero_gate_runs": "ZERO GATE RUNS" in proc.stdout,
            "artifact_ALL_PASS": None if rep is None else rep.get("ALL_PASS"),
            "artifact_n_gate_runs": None if rep is None
            else rep.get("n_gate_runs"),
            "artifact_len_cases": None if rep is None
            else len(rep.get("cases", [])),
            "canonical_report_unchanged": before == after,
            "stdout_tail": proc.stdout[-700:],
            "stderr_tail": proc.stderr[-400:]}


def real_crash_family():
    """The two argv families that RAISE, also unstubbed, as subprocesses.

    In-process this file records `exit: None` for a run that raises, because
    an exception is not an exit code.  What a shell actually sees is a
    different question and it is the one that matters for `... && echo ok`, so
    it is OBSERVED here rather than inferred from `SystemExit` semantics.

    Both spellings below are cheap for a reason worth stating: each raises on
    the FIRST loop iteration, at `EXPECTED[(mutation, gate_variant)]`, before
    any tree is built or any gate is run.  `--only MZZZ` on its own is NOT
    cheap -- its first iteration is the valid pair `("none", "pre-widening")`,
    which runs the real gate for ~50 s before reaching the bad key -- so it is
    deliberately not run here, and that is a gap in this measurement, not a
    property of the subject."""
    out = []
    for argv, why in [
            (["--gates", "bogus"],
             "an unknown gate column; note it dies at EXPECTED, so the "
             "`unknown gate variant` SystemExit in build_tree is never reached"),
            (["--only", ",", "--gates", "widened"],
             "a lone separator: the comprehension yields empty ids"),
            (["--only", "MZZZ", "--gates", "bogus"],
             "an unknown mutation row (paired with an unknown column so the "
             "run raises before any gate executes)")]:
        # Cleared FIRST: `real_empty_run` leaves a PARTIAL report behind, and
        # a stale file would make "this crashing run wrote a report" true of a
        # run that wrote nothing -- the mg-ec63 shape (a probe reading a file
        # its own run had already touched), which is on tonight's list.
        partial = os.path.join(REPO, PARTIAL)
        if os.path.exists(partial):
            os.remove(partial)
        proc = subprocess.run([sys.executable, DEMO_REL] + argv, cwd=REPO,
                              capture_output=True, text=True)
        out.append({
            "cmd": f"{DEMO_REL} {' '.join(argv)}",
            "why": why,
            "exit": proc.returncode,
            "exception": proc.stderr.strip().splitlines()[-1]
            if proc.stderr.strip() else None,
            "names_the_bad_input":
                any(tok in proc.stderr for tok in ("bogus", "MZZZ")),
            "wrote_a_partial_report": os.path.exists(partial),
        })
    return out


# ------------------------------------------------------------------ driver ---
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="",
                    help="comma-separated invariants, e.g. V1,V3")
    ap.add_argument("--real-empty", action="store_true",
                    help="also run the empty case unstubbed, as a subprocess")
    # THE POSITIVE CONTROL ON THIS FILE'S OWN VACUITY GUARD.  Without a route
    # to it, `ALL_HELD = checks > 0 and not problems` is a guard nobody has
    # seen fire -- the shape under audit, in the instrument auditing it.
    ap.add_argument("--prove-empty-guard", action="store_true",
                    help="evaluate zero assertions and confirm this file "
                         "refuses a verdict (must exit 2)")
    args = ap.parse_args()

    if args.prove_empty_guard:
        led = Ledger()
        print("=" * 78)
        print("--prove-empty-guard: THIS FILE'S OWN POPULATION EMPTIED "
              "DELIBERATELY")
        print("=" * 78)
        print(f"  invocations : {led.invocations}")
        print(f"  assertions  : {led.checks}")
        print("  ZERO ASSERTIONS EVALUATED -- THIS RUN MEASURED NOTHING.")
        print("  ALL_HELD is written FALSE, not true-over-an-empty-list.  "
              "Exiting 2.")
        print("  The guard the module docstring claims, SEEN TO FIRE rather "
              "than asserted.")
        # Its own path, not the canonical one: a run that measured nothing
        # must not land where the record lives (mg-a471's F5, the defect one
        # level down from the one under audit).
        stub = REPORT.replace(".json", ".PROVE-GUARD.json")
        with open(os.path.join(REPO, stub), "w") as f:
            json.dump({"what": "--prove-empty-guard", "assertions": 0,
                       "invocations": 0, "ALL_HELD": False,
                       "IS_THE_MEASUREMENT": False}, f, indent=2)
        print(f"  wrote {stub} -- NOT {REPORT}, which is untouched.")
        return 2

    requested = [x for x in args.only.split(",") if x] or sorted(INVARIANTS)
    unknown = [x for x in requested if x not in INVARIANTS]
    if unknown:
        raise SystemExit(f"unknown invariant(s): {','.join(unknown)}.  "
                         f"Known: {','.join(sorted(INVARIANTS))}")

    print("=" * 78)
    print("mg-a266 -- CAN ALL_PASS BE TRUE OVER AN EMPTY POPULATION?")
    print("=" * 78)
    print(f"  subject      : {DEMO_REL} (working tree)")
    print(f"  invariants   : {','.join(requested)}")
    print(f"  argv space   : {len(argv_space())} invocations "
          f"= {len(ONLY_SPELLINGS)} --only x {len(GATES_SPELLINGS)} --gates "
          f"x {len(PARTIAL_SPELLINGS)} --partial-ok")

    led = Ledger()
    print()
    print("PART 1 -- ENUMERATION over the argv space")
    rows = enumerate_space(led, demo_source(), requested)
    empties = [r for r in rows if r["n_gate_runs"] == 0]
    crashes = [r for r in rows if r["raised"]]
    zeros = [r for r in rows if r["exit"] == 0]
    print(f"  {led.invocations} invocations driven, {led.checks} assertions")
    print(f"  invocations whose population was EMPTY : {len(empties)}"
          f"  (exit codes: {sorted({r['exit'] for r in empties})}, "
          f"ALL_PASS: {sorted({str(r['ALL_PASS']) for r in empties})})")
    print(f"  invocations that RAISED                : {len(crashes)}"
          f"  (exit codes: {sorted({str(r['exit']) for r in crashes})})")
    print(f"  invocations that exited 0              : {len(zeros)}"
          f"  (min n_gate_runs among them: "
          f"{min([r['n_gate_runs'] for r in zeros], default=None)})")

    print()
    print("PART 2 -- DISTINGUISHABILITY: what a READER can see")
    table, verdict, verdict_all3, residual = distinguishability(led,
                                                               demo_source())
    print("  " + f"{'':<24}" + "".join(f"{k:<16}" for k in table)
          + "  EMPTY-vs-PASSED  EMPTY-vs-FAILED")
    for field in ["exit", "artifact_ALL_PASS", "artifact_n_gate_runs",
                  "artifact_len_cases"]:
        print(f"  {field:<24}"
              + "".join(f"{str(table[k][field]):<16}" for k in table)
              + f"  {str(verdict[field]['EMPTY-vs-PASSED']):<17}"
              + f"{verdict[field]['EMPTY-vs-FAILED']}")
    for k in table:
        print(f"  {k} banner: {table[k]['stdout_banner']}")
    print(f"  RESIDUAL: ALL_PASS separates EMPTY from FAILED: "
          f"{residual['ALL_PASS_separates_EMPTY_from_FAILED']}"
          f"  -- a reader who greps only ALL_PASS sees a FAILURE, not an "
          f"emptiness")
    print(f"  fields separating EMPTY from FAILED: "
          f"{residual['fields_separating_EMPTY_from_FAILED']}")

    print()
    print("PART 3 -- POSITIVE CONTROL: three broken subjects, each must fire")
    pcs = positive_controls(led, requested)
    for pc in pcs:
        print(f"  {pc['subject']:<44} {pc['violations']:>3} violations / "
              f"{pc['assertions']} assertions  "
              f"{'RED (good)' if pc['violations'] else 'CLEAN -- BLIND'}")
        for p in pc["first_three"]:
            print(f"      {p[:120]}")

    print()
    print("PART 4 -- WHAT THE STANDING CONTROL'S INVOCATION SET CANNOT REACH")
    cov = coverage(led)
    if "error" not in cov:
        print(f"  the control drives {cov['control_invocations_recorded']} "
              f"invocations, {len(cov['distinct_argv_spellings_in_the_control'])}"
              f" distinct spellings")
        print(f"  of this file's {cov['argv_space_size']} spellings it never "
              f"drives {cov['n_unreached']}")
        for s in cov["spellings_the_control_never_drives"][:8]:
            print(f"      never driven: {s}")
        if cov["n_unreached"] > 8:
            print(f"      ... and {cov['n_unreached'] - 8} more")

    real = None
    if args.real_empty:
        print()
        print("PART 5 -- THE EMPTY CASE, UNSTUBBED, END TO END")
        real = real_empty_run()
        for k in ("cmd", "exit", "said_zero_gate_runs", "artifact_ALL_PASS",
                  "artifact_n_gate_runs", "artifact_len_cases",
                  "canonical_report_unchanged"):
            print(f"  {k:<28} {real[k]}")
        led.check(real["exit"] == 2, "R",
                  f"the real empty run exited {real['exit']}, expected 2")
        led.check(real["artifact_ALL_PASS"] is False, "R",
                  "the real empty run's artifact does not say ALL_PASS false")
        led.check(real["artifact_n_gate_runs"] == 0, "R",
                  "the real empty run's artifact does not record 0 gate runs")
        led.check(real["said_zero_gate_runs"], "R",
                  "the real empty run never printed ZERO GATE RUNS")
        led.check(real["canonical_report_unchanged"], "R",
                  "the real empty run changed the committed canonical report")

        print()
        print("  the CRASHING argv families, also unstubbed (what a shell "
              "really sees)")
        crash_real = real_crash_family()
        for c in crash_real:
            print(f"    {c['cmd']}")
            print(f"      exit {c['exit']}  |  {c['exception']}")
            print(f"      names the bad input in its error: "
                  f"{c['names_the_bad_input']}  |  wrote a report: "
                  f"{c['wrote_a_partial_report']}")
            led.check(c["exit"] != 0, "R",
                      f"`{c['cmd']}` exited 0 after raising")
            led.check(not c["wrote_a_partial_report"], "R",
                      f"`{c['cmd']}` raised but still left a report behind")
        real["crash_family"] = crash_real

    report = {
        "what": "mg-a266 independent audit of mg-9a59: is a PASS over an "
                "empty population REACHABLE, and are emptiness and success "
                "distinguishable in the OUTPUT?",
        "subject": DEMO_REL,
        "subject_revision_pinned_for_the_positive_control": PRE_REPAIR_REV,
        "population": {
            "argv_space": len(argv_space()),
            "grain": "one call to the subject's main() per invocation; one "
                     "boolean per assertion",
            "gate_executions": 0,
            "note": "no mg-2c34 gate is executed: run_case is stubbed, so "
                    "n_gate_runs counts DRIVER ITERATIONS.  Both defects "
                    "under audit live in main(), above run_case.",
        },
        "invariants": {k: INVARIANTS[k] for k in requested},
        "invariants_not_requested": sorted(set(INVARIANTS) - set(requested)),
        "enumeration": rows,
        "empty_population_invocations": [r["spelling"] for r in empties],
        "raising_invocations": [
            {"spelling": r["spelling"], "raised": r["raised"],
             "exit": r["exit"],
             "partial_written": r["partial_written"]} for r in crashes],
        "distinguishability": {
            "runs": table,
            "field_separates_pair": verdict,
            "field_takes_three_distinct_values": verdict_all3,
            "residual": residual},
        "positive_controls": pcs,
        "standing_control_coverage": cov,
        "real_unstubbed_empty_run": real,
        "assertions": led.checks,
        "assertions_per_invariant": led.by_invariant,
        "invocations": led.invocations,
        "problems": led.problems,
        # The same conjunction the subject was repaired to carry, in the
        # instrument that audits it.  A run that checked nothing does not get
        # to say ALL_HELD true here either.
        "ALL_HELD": led.checks > 0 and not led.problems,
    }
    with open(os.path.join(REPO, REPORT), "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {REPORT}")

    print()
    print("=" * 78)
    if led.checks == 0:
        print("ZERO ASSERTIONS EVALUATED -- THIS RUN MEASURED NOTHING.")
        print("  ALL_HELD is written FALSE, not true-over-an-empty-list.  "
              "Exiting 2:")
        print("  an audit that examined nothing must not be citable as one "
              "that passed.")
        return 2
    if led.problems:
        print(f"FAILED: {len(led.problems)} of {led.checks} assertions over "
              f"{led.invocations} invocations")
        for p in led.problems[:40]:
            print(f"  - {p}")
        if len(led.problems) > 40:
            print(f"  ... and {len(led.problems) - 40} more")
        return 1
    print(f"HELD: {led.checks}/{led.checks} assertions over {led.invocations} "
          f"invocations of the subject's main().")
    print(f"  Population: {len(argv_space())} argv spellings x "
          f"{len(requested)} invariant families, plus 3 broken subjects each "
          f"required to go RED.")
    print("  ALL_PASS true over an empty population is UNREACHABLE in this "
          "space, and")
    print("  emptiness is separable from success AND from failure by the exit "
          "code, by")
    print("  n_gate_runs on the artifact, and by a named banner in the output.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
