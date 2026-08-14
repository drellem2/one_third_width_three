#!/usr/bin/env python3
"""mg-3067 -- THE PLAN FOR THE LOCAL PRE-SUBMIT GATE, DERIVED FROM CI.

`./presubmit.sh` runs the controls in the author's own worktree before the
branch is submitted.  It does NOT contain a list of what to run.  This module
extracts that list from `.github/workflows/script-controls.yml`, which is the
only place the list exists, so the local gate and the CI job cannot drift into
two gate lists that disagree.  (That is `onethird_program/build.sh`'s own stated
reason for keeping one definition; here the single definition is the workflow,
because the workflow already existed and is the thing GitHub runs.)

A HAND PARSER ON PURPOSE, for the same reason mg-7db4's and mg-3934's are: this
must run under a bare interpreter with no PyYAML, on the fleet host and on a
hosted runner.

================================ THE TWO TRANSFORMATIONS ======================

The local run is not byte-identical to the CI run, and the differences are
declared here rather than discovered.  `--check` enforces that these two are the
ONLY differences -- any other line that fails to make it into the plan is a
control the local gate would silently skip, which is the defect this file exists
to prevent.

  T1  INTERPRETER.  A leading `python3 ` token becomes `"$PY"`, the interpreter
      `presubmit.sh` picked.  Bare `python3` on the fleet host has no numpy and
      /usr/bin/python3 does (scripts/refinery_gate.sh line 231 makes the same
      substitution for the same reason).  CI provisions its own 3.12 and has no
      such problem.

  T2  PROVISIONING.  `pip install ...` lines are DROPPED.  They are how the
      hosted runner acquires numpy; locally the interpreter either already has
      it or `presubmit.sh` refuses to start.  A `pip install` in an author's
      worktree would mutate their environment, which a gate must not do.
      The dropped lines' modules are reported so the caller can precheck them.

Anything else -- a new step, a new line in a `run:` block, a step whose command
changes -- flows through untouched, on the next run, with no edit here.

================================ WHAT THIS IS NOT ============================

The plan covers `script-controls.yml` ONLY.  `gate-mutation-demo.yml` is the
~30-minute demonstration job and `scripts/refinery_gate.sh` is the blocking
refinery gate; neither is in the plan and neither should be.  The point of a
pre-submit gate is that it is cheap enough to run every time.

================================ USAGE =======================================

    python3 scripts/onethird_mg3067_presubmit_steps.py --emit-sh
        POSIX-sh fragment: one `step '<name>' '<command>'` call per CI step,
        in order, for `presubmit.sh` to source.

    python3 scripts/onethird_mg3067_presubmit_steps.py --list
        Human-readable plan.

    python3 scripts/onethird_mg3067_presubmit_steps.py --check
        THE CONTROL.  Runs in script-controls.yml.  Exits non-zero if the plan
        has stopped covering the workflow.  Order-milliseconds, stdlib only.

    python3 scripts/onethird_mg3067_presubmit_steps.py --selftest
        Six synthetic drifts, each of which --check must catch.  Run by
        --check itself before its own verdict is believed.
"""

import os
import re
import shlex
import sys

WORKFLOW = ".github/workflows/script-controls.yml"
JOB = "controls"

# T2's exemption.  Deliberately narrow: a line is exempt only if it is a `pip`
# invocation.  It is NOT "any line the parser did not like".
_PIP_RE = re.compile(r"^\s*(?:python3?\s+-m\s+)?pip\d?\s+install\b(.*)$")
_STEP_RE = re.compile(r"^(\s*)-\s+(name|uses):\s*(.*)$")
_KEY_RE = re.compile(r"^(\s*)([A-Za-z_-]+):\s*(.*)$")
# The independent count used by check (C1): a `run:` key inside a step.
_RUN_KEY_RE = re.compile(r"^\s+run:\s*(.*)$")

PY_PLACEHOLDER = '"$PY"'


# ------------------------------------------------------------- parsing ------
def _unquote(v):
    v = v.strip()
    if len(v) >= 2 and v[0] == v[-1] and v[0] in "'\"":
        return v[1:-1]
    return v


def parse_steps(text):
    """Ordered [(name, [command lines])] for the job's steps.

    Only steps with a `run:` are returned -- `uses:` steps are GitHub actions
    (checkout, setup-python) with no local equivalent, and a checkout inside the
    author's own worktree would be wrong rather than merely redundant.
    """
    lines = text.splitlines()

    # locate `steps:` under jobs.<JOB>, and the indent of the JOB key itself --
    # the parser STOPS when it dedents back to that level.  Reading to end of
    # file instead was this file's own first defect: with a second job present
    # the plan silently grew that job's steps, and the sentence this module
    # prints ("runs every control this workflow runs") became over-wide inside
    # the file's own description of its coverage.  Drift D7 is that case, and
    # C6 is what refuses it.
    start = None
    job_indent = None
    for i, line in enumerate(lines):
        m = re.match(r"^(\s*)%s:\s*$" % re.escape(JOB), line)
        if m and job_indent is None:
            job_indent = len(m.group(1))
            continue
        if job_indent is not None and re.match(r"^\s*steps:\s*$", line):
            start = i + 1
            break
    if start is None:
        return []

    steps = []
    name = None
    cmd = None            # list of lines, or None when not inside a run scalar
    run_indent = None

    def flush():
        if cmd is not None:
            steps.append((name if name is not None else "(unnamed step)",
                          [c for c in cmd]))

    for line in lines[start:]:
        stripped = line.strip()

        # dedented out of this job -- everything after belongs to another job
        if stripped and not stripped.startswith("#"):
            if len(line) - len(line.lstrip()) <= job_indent:
                break

        # inside a block scalar: everything more-indented belongs to it,
        # comments included (a `#` there is a shell comment, not YAML).
        if cmd is not None and run_indent is not None:
            indent = len(line) - len(line.lstrip())
            if stripped and indent > run_indent:
                cmd.append(stripped)
                continue
            if not stripped:
                continue
            run_indent = None   # dedented out of the scalar

        if not stripped or stripped.startswith("#"):
            continue

        m = _STEP_RE.match(line)
        if m:
            flush()
            name, cmd, run_indent = None, None, None
            if m.group(2) == "name":
                name = _unquote(m.group(3))
            continue

        m = _KEY_RE.match(line)
        if not m:
            continue
        key, value = m.group(2), m.group(3).strip()
        if key == "name" and cmd is None:
            name = _unquote(value)
        elif key == "run":
            cmd = []
            if value in ("|", ">", "|-", ">-"):
                run_indent = len(m.group(1))
            else:
                cmd.append(value)
        elif key in ("jobs",):
            break

    flush()
    return steps


# ------------------------------------------------------------- the plan -----
def declared_jobs(text):
    """Every key under `jobs:`, in order.  The plan covers exactly one of them."""
    lines = text.splitlines()
    jobs, jobs_indent, key_indent = [], None, None
    for line in lines:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        indent = len(line) - len(line.lstrip())
        if jobs_indent is None:
            if re.match(r"^jobs:\s*$", line):
                jobs_indent = indent
            continue
        if indent <= jobs_indent:
            break                      # dedented out of `jobs:`
        m = re.match(r"^\s*([A-Za-z0-9_-]+):\s*$", line)
        if m and (key_indent is None or indent == key_indent):
            key_indent = indent
            jobs.append(m.group(1))
    return jobs


def build_plan(steps):
    """[(name, command, dropped)] after T1 and T2.

    `dropped` is the list of pip lines T2 removed from this step.
    """
    plan = []
    for name, raw in steps:
        kept, dropped = [], []
        for line in raw:
            if _PIP_RE.match(line):
                dropped.append(line)
                continue
            kept.append(re.sub(r"^python3?\b", PY_PLACEHOLDER, line))
        plan.append((name, "\n".join(kept), dropped))
    return plan


def pip_modules(plan):
    """Every module name T2 dropped a `pip install` for, deduplicated."""
    mods = []
    for _, _, dropped in plan:
        for line in dropped:
            for tok in _PIP_RE.match(line).group(1).split():
                if tok.startswith("-"):
                    continue
                mod = re.split(r"[<>=!\[]", tok)[0]
                if mod and mod not in mods:
                    mods.append(mod)
    return mods


# ------------------------------------------------------------- the control --
def check(text):
    """(problems, rows).  Every assertion the local plan's coverage rests on."""
    problems, rows = [], []
    steps = parse_steps(text)
    plan = build_plan(steps)

    # C0.  REFUSE A PASS OVER AN EMPTY POPULATION.  mg-9a59's defect, and this
    # file is exactly the shape that has it: a parser that finds nothing exits
    # 0 over zero assertions and reports a gate that runs no controls.
    if not steps:
        problems.append(
            "parsed ZERO steps out of %s -- a plan over an empty population is "
            "not a green gate, it is a gate that runs nothing" % WORKFLOW)
        return problems, rows
    rows.append("steps parsed: %d" % len(steps))

    # C1.  INDEPENDENT COUNT.  A second method that does not share the block
    # parser: count `run:` keys lexically.  If the two disagree the parser has
    # dropped or invented a step.
    lexical = 0
    in_scalar = None
    for line in text.splitlines():
        if in_scalar is not None:
            indent = len(line) - len(line.lstrip())
            if line.strip() and indent > in_scalar:
                continue
            in_scalar = None
        m = _RUN_KEY_RE.match(line)
        if m:
            lexical += 1
            if m.group(1).strip() in ("|", ">", "|-", ">-"):
                in_scalar = len(line) - len(line.lstrip())
    if lexical != len(steps):
        problems.append(
            "step count disagrees between the two methods: block parser %d, "
            "lexical `run:` count %d" % (len(steps), lexical))
    rows.append("independent `run:` count: %d" % lexical)

    # C2.  LINE COVERAGE.  Every line of every CI step is either executed
    # locally or is a declared T2 pip line.  This is the assertion that makes
    # "the local gate runs what CI runs" a checked claim rather than a hope.
    total, executed, exempt = 0, 0, 0
    for (name, raw), (_, command, dropped) in zip(steps, plan):
        cmd_lines = command.splitlines() if command else []
        for line in raw:
            total += 1
            if line in dropped:
                exempt += 1
                continue
            want = re.sub(r"^python3?\b", PY_PLACEHOLDER, line)
            if want in cmd_lines:
                executed += 1
            else:
                problems.append(
                    "step %r: line %r reaches neither the local plan nor the "
                    "pip exemption" % (name, line))
    if executed + exempt != total:
        problems.append("line accounting does not close: %d executed + %d "
                        "exempt != %d total" % (executed, exempt, total))
    rows.append("run-lines: %d total = %d executed locally + %d pip-exempt"
                % (total, executed, exempt))

    # C3.  THE EXEMPTION STAYS NARROW.  Anything dropped must be a pip line.
    for name, _, dropped in plan:
        for line in dropped:
            if not _PIP_RE.match(line):
                problems.append("step %r: %r dropped but is not a pip install"
                                % (name, line))
    rows.append("pip-exempt modules: %s" % (", ".join(pip_modules(plan)) or "none"))

    # C4.  NO STEP IS EMPTY.  A step that parses to no command is a control the
    # plan claims to cover and does not run -- the same shape as C0, per step.
    for name, command, dropped in plan:
        if not command.strip():
            problems.append("step %r has no local command at all (%d pip lines "
                            "dropped)" % (name, len(dropped)))

    # C6.  THE PLAN COVERS THE WHOLE WORKFLOW, NOT PART OF IT.  parse_steps
    # reads the `controls` job and stops at the job boundary, so a second job
    # would be silently outside the plan while this module went on printing
    # "runs every control this workflow runs".  That is an over-wide statement
    # in a file's own description of its coverage -- mg-bd53 finding 5's shape,
    # which this repo has been bitten by.  A second job is therefore RED, and
    # what to do about it is a decision somebody makes rather than something the
    # local gate inherits: either add it to the plan deliberately, or say here
    # why it is out.
    jobs = declared_jobs(text)
    if jobs != [JOB]:
        problems.append(
            "the plan covers job %r, but this workflow declares %s -- either "
            "the extra job's steps are unrun locally, or the claim that this "
            "gate runs every control the workflow runs is over-wide"
            % (JOB, ", ".join(repr(j) for j in jobs) or "no jobs at all"))
    rows.append("jobs declared: %s" % (", ".join(jobs) or "none"))

    # C5.  THE INTERPRETER SUBSTITUTION REACHED EVERY PYTHON LINE.  A bare
    # `python3` surviving into the plan would run the numpy-less interpreter.
    for name, command, _ in plan:
        for line in command.splitlines():
            if re.match(r"^python3?\b", line):
                problems.append("step %r: %r kept a bare interpreter -- T1 did "
                                "not reach it" % (name, line))

    return problems, rows


# ------------------------------------------------------------- self-test ----
_MIN = """\
jobs:
  controls:
    steps:
      - uses: actions/checkout@v5
      - name: 'a'
        run: python3 scripts/a.py
      - name: 'b'
        run: |
          pip install --quiet numpy
          python3 scripts/b.py --no-sweep
"""


def _selftest():
    """Six drifts.  Each must make --check fail; the pristine text must not.

    An exemption list on a gate is the easiest place in this repository to
    build a control that cannot fail (mg-856d's words), and a plan derived from
    a parser is the second easiest.  So the parser's own drifts are run before
    its verdict on the real workflow is believed.
    """
    rows = []
    ok = True

    problems, _ = check(_MIN)
    rows.append(("pristine minimal workflow", not problems,
                 "; ".join(problems) or "clean"))
    ok = ok and not problems

    cases = []

    # D1: the parser stops seeing the block scalar's second line.
    cases.append(("a run-block line vanishes from the plan",
                  _MIN, lambda t: t, "PATCH_DROP_LINE"))
    # D2: a step is added to CI and the plan does not grow.
    cases.append(("a step is added to CI",
                  _MIN + "      - name: 'c'\n        run: python3 scripts/c.py\n",
                  lambda t: t, "PATCH_FREEZE_COUNT"))
    # D3: the pip exemption widens to swallow a real control.
    cases.append(("the exemption widens past pip",
                  _MIN, lambda t: t, "PATCH_WIDE_EXEMPT"))
    # D4: T1 stops substituting the interpreter.
    cases.append(("T1 stops substituting the interpreter",
                  _MIN, lambda t: t, "PATCH_NO_T1"))
    # D5: the job has no steps at all.
    cases.append(("the job loses its steps",
                  "jobs:\n  controls:\n    steps:\n", lambda t: t, None))
    # D6: a step that is nothing but a pip line -- covered, and empty locally.
    cases.append(("a step is pip-only",
                  _MIN + "      - name: 'd'\n        run: pip install --quiet scipy\n",
                  lambda t: t, None))
    # D7: A SECOND JOB.  This one is here because of the CLAIM this file makes
    # in its own output -- "runs every control this workflow runs".  parse_steps
    # reads the `controls` job and only that job, so a second job would make
    # that sentence over-wide inside the file's own description of its coverage,
    # which is mg-bd53 finding 5's exact shape.  C1's lexical `run:` count does
    # not know about jobs, so it catches it; that is asserted here rather than
    # in prose.
    cases.append(("a second job appears in the workflow",
                  _MIN + "  other:\n    steps:\n      - name: 'z'\n"
                         "        run: python3 scripts/z.py\n",
                  lambda t: t, None))

    global _PIP_RE
    saved_pip = _PIP_RE
    for label, text, _fn, patch in cases:
        try:
            if patch == "PATCH_DROP_LINE":
                problems = _with_broken_plan(text, "drop")
            elif patch == "PATCH_FREEZE_COUNT":
                problems = _with_broken_plan(text, "freeze")
            elif patch == "PATCH_WIDE_EXEMPT":
                _PIP_RE = re.compile(r"^\s*(?P<all>.*)$")
                # a catch-all exemption must still be refused by C3/C4
                problems, _ = check(text)
                _PIP_RE = saved_pip
            elif patch == "PATCH_NO_T1":
                problems = _with_broken_plan(text, "not1")
            else:
                problems, _ = check(text)
        finally:
            _PIP_RE = saved_pip
        rows.append((label, bool(problems),
                     "; ".join(problems)[:110] or "NOT CAUGHT"))
        ok = ok and bool(problems)

    print("  mg-3067 parser self-test")
    for label, good, detail in rows:
        print("    %-4s %-42s %s" % ("ok" if good else "FAIL", label, detail))
    return ok


def _with_broken_plan(text, mode):
    """Run check() with build_plan sabotaged, to prove C1/C2/C5 can fire."""
    global build_plan
    real = build_plan

    def broken(steps):
        plan = real(steps)
        if mode == "drop":
            name, command, dropped = plan[-1]
            plan[-1] = (name, "\n".join(command.splitlines()[:-1]) if command
                        else command, dropped)
        elif mode == "freeze":
            plan = plan[:-1]
        elif mode == "not1":
            plan = [(n, c.replace(PY_PLACEHOLDER, "python3"), d)
                    for n, c, d in plan]
        return plan

    build_plan = broken
    try:
        if mode == "freeze":
            # C1 compares parse_steps() against the lexical count, so freeze the
            # parser rather than the plan.
            global parse_steps
            real_parse = parse_steps
            parse_steps = lambda t: real_parse(t)[:-1]   # noqa: E731
            try:
                problems, _ = check(text)
            finally:
                parse_steps = real_parse
        else:
            problems, _ = check(text)
    finally:
        build_plan = real
    return problems


# ------------------------------------------------------------- entry --------
def _read_workflow():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    path = os.path.join(root, WORKFLOW)
    if not os.path.exists(path):
        sys.stderr.write("mg-3067: %s is missing -- the pre-submit gate has no "
                         "plan to derive\n" % WORKFLOW)
        sys.exit(2)
    with open(path, "r", encoding="utf-8") as fh:
        return fh.read()


def main(argv):
    mode = argv[1] if len(argv) > 1 else "--list"

    if mode == "--selftest":
        return 0 if _selftest() else 1

    text = _read_workflow()
    plan = build_plan(parse_steps(text))

    if mode == "--emit-sh":
        if not plan:
            sys.stderr.write("mg-3067: parsed zero steps -- refusing to emit an "
                             "empty gate\n")
            return 2
        for name, command, _ in plan:
            sys.stdout.write("step %s %s\n"
                             % (shlex.quote(name), shlex.quote(command)))
        return 0

    if mode == "--pip-modules":
        for mod in pip_modules(plan):
            print(mod)
        return 0

    if mode == "--list":
        print("mg-3067 pre-submit plan, derived from %s" % WORKFLOW)
        for i, (name, command, dropped) in enumerate(plan, 1):
            print("  %2d. %s" % (i, name))
            for line in command.splitlines():
                print("        %s" % line)
            for line in dropped:
                print("        (T2 dropped) %s" % line)
        return 0

    if mode == "--check":
        if not _selftest():
            print("mg-3067: FAIL -- the parser's own drifts were not all "
                  "caught, so its verdict on the real workflow is not "
                  "believed.")
            return 1
        problems, rows = check(text)
        print("  mg-3067 plan coverage of %s" % WORKFLOW)
        for row in rows:
            print("    %s" % row)
        if problems:
            print("  mg-3067: FAIL -- the local pre-submit plan has stopped "
                  "covering the CI job:")
            for p in problems:
                print("    * %s" % p)
            return 1
        print("  mg-3067: OK -- ./presubmit.sh runs every control this "
              "workflow runs.")
        return 0

    sys.stderr.write("mg-3067: unknown mode %r\n" % mode)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
