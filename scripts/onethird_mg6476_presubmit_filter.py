#!/usr/bin/env python3
"""mg-6476 -- WHICH STEPS OF THE PRE-SUBMIT PLAN CAN THIS BRANCH AFFECT?

`./presubmit.sh` derives its plan from `.github/workflows/script-controls.yml`
(mg-3067).  It ran ALL of it, on every branch.  Measured, that is minutes, and
the single most expensive step -- the mg-2c34 spectral-numerics control -- is a
statement about posets that a branch adding a document, a script and a data file
CANNOT AFFECT.  This module decides, per step, whether the branch's changed
paths intersect the inputs that step reads.

================================ WHY THIS EXISTS ==============================

pm-onethird priced the gate at ~3.6 min (GitHub-hosted `Script controls` wall
time) and wrote, in mg-3067's scope, "reuse the CI steps rather than
reimplementing them".  That instruction is right about DRIFT and blind to COST
ASYMMETRY: CI can afford a long control after a merge; an author cannot afford
it before a submit.  A pre-submit gate that nothing enforces and that costs
double digits of minutes is not slow, it is ABANDONED -- and a gate that is
skipped is worse than no gate, because everyone believes it ran.  The refinery
gate in this same repo already solved this: it is paths-filtered, and on a
commit touching none of its watchlist it is "a git diff and a grep".

================================ THE NO-DRIFT PROPERTY ========================

mg-3067's instruction was guarding a real thing and this module does not spend
it.  Two gates that can disagree about a step's VERDICT are worse than one.
There are two different changes and only one of them is a disagreement:

  SKIPPING a step whose inputs this branch does not touch      -- NOT a
      disagreement.  The step's verdict is a function of its inputs; if no
      input moved, the verdict cannot have moved either.
  RUNNING A DIFFERENT VERSION of a step                        -- IS a
      disagreement, and nothing here does it.  The command text still comes
      from the workflow, through mg-3067's plan, unedited.

This module therefore adds NO second list of steps.  It consumes mg-3067's plan
and derives each step's input set from the step's own command.

================================ HOW A STEP'S INPUTS ARE DERIVED ==============

For each step of the plan, in order:

  1. Each command line must be recognisable as `"$PY" <script> [args]`.  The
     scripts named are the roots.
  2. The transitive `onethird_*` import closure of those roots (the same
     closure mg-7db4's watchlist control derives, for the same reason: an
     import moves a quantity into a file, and a filter that has stopped naming
     the files that matter is a filter that skips a step it should have run).
  3. Every repo-relative path literal appearing in any module of the closure --
     `data/...`, `docs/...`, `scripts/...`, `.github/...` -- plus the corpus's
     `os.path.join(REPO, "data", "<name>")` idiom, plus any command argument
     that is itself a repo path.

  A step whose inputs cannot be derived this way is UNFILTERABLE and ALWAYS
  RUNS.  That is the fail-safe direction and it is taken at the first sign of
  trouble, not the last:

    * a command line that is not `"$PY" <script>` (a bare interpreter flag, a
      shell builtin, anything unrecognised);
    * a script that does not exist on disk;
    * an unresolvable import (the closure is incomplete, so the derived input
      set is a lower bound and a lower bound is not safe to filter on);
    * ANY module in the closure that sweeps a directory (`os.walk`,
      `os.listdir`, `glob`) or shells out (`subprocess`).  Those read paths no
      literal names -- the corpus-wide document controls are exactly this --
      so their input set is not derivable and must not be guessed;
    * ANY module that builds a repo path out of a NAME rather than a string --
      `os.path.join(REPO, "data", REF)`.  It looks exactly like the derivable
      idiom and is not: the file is real and nothing in the module spells it.
      Three modules in this corpus do it, found by looking rather than assumed.

  UNFILTERABLE is not a defect to be repaired away.  Every corpus-sweeping
  document control in this workflow is unfilterable and should be: it reads
  every *.md in docs/, so a branch adding a document DOES change its input.

================================ THE GATE'S OWN FILES =========================

If the change touches the gate itself, filtering is not sound -- the thing
deciding what to skip is the thing that moved.  So the WHOLE plan runs whenever
the changed set meets any of: `presubmit.sh`, any repo-relative path literal
inside it (which is where `.github/workflows/script-controls.yml`,
mg-3067's plan module and `scripts/refinery_gate.sh` come from), this module,
and the import closure of both modules.  Derived from the files, not listed.

================================ WHAT IT DOES NOT CLAIM =======================

It does not claim the derived input set is COMPLETE for a filterable step.  It
claims the derivation is conservative at every point where it could be wrong,
and it makes the claim checkable: `--list` prints every step's classification
and its input set, and `--selftest` runs eight drifts, each of which must be
caught, before any verdict here is believed.

It does not bound how many CORES a step takes.  That is the other half of
mg-6476 and it lives in `presubmit.sh`'s environment (the BLAS thread cap), not
here.  Filtering narrows the POPULATION of branches that pay; it does not bound
the WORST CASE, and a branch that does touch spectral-numerics inputs still
runs the whole thing.  Cross-reference mg-1d05 (pogo): a worker can follow the
core-budget instruction perfectly and still take the box, because the
parallelism is inside a library and invisible at the call site.

================================ USAGE ========================================

    python3 scripts/onethird_mg6476_presubmit_filter.py --list
        Every step, its classification, and the inputs it was derived to read.

    python3 scripts/onethird_mg6476_presubmit_filter.py --emit-sh --changed FILE
        POSIX-sh fragment for presubmit.sh: `step` for a step that runs,
        `skip` for one whose inputs this branch does not touch.  FILE holds one
        changed repo-relative path per line.

    python3 scripts/onethird_mg6476_presubmit_filter.py --check
        THE CONTROL.  Runs in script-controls.yml.  Asserts the derivation
        still closes over the real workflow and that the fail-safe fires.

    python3 scripts/onethird_mg6476_presubmit_filter.py --selftest
        Eight drifts, each of which --check must catch.
"""

import os
import re
import shlex
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import onethird_mg3067_presubmit_steps as PLAN  # noqa: E402

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PRESUBMIT = "presubmit.sh"
SELF = "scripts/onethird_mg6476_presubmit_filter.py"

# The step's command after mg-3067's T1: the interpreter is `"$PY"`.
_PY_CALL_RE = re.compile(r'^"\$PY"\s+(\S+)(.*)$')
_IMPORT_RE = re.compile(r"^\s*(?:from|import)\s+(onethird_\w+)", re.M)

# Repo-relative path literals.  The top-level directories this repository
# actually commits to -- the same set `.github/workflows/script-controls.yml`
# names in its own `paths:` filter, plus the two the corpus reads.
_TOPDIRS = ("scripts", "data", "docs", ".github", "lean", "notes")
_PATH_RE = re.compile(
    r"(?<![\w/.-])((?:%s)/[\w][\w./-]*)" % "|".join(re.escape(d) for d in _TOPDIRS))
# The corpus's one dataset idiom, whitespace-stripped before matching.
_DATA_RE = re.compile(r'open\(os\.path\.join\(REPO,"data","([^"]+)"\)(,"w")?\)')

# Idioms whose read set is not derivable from literals.  A module using any of
# them makes its step UNFILTERABLE.  Deliberately blunt: this list erring wide
# costs runtime, erring narrow costs a skipped control.
_OPAQUE_RE = re.compile(
    r"\bsubprocess\b|\bos\.walk\b|\bos\.listdir\b|\bglob\.|\.glob\(|\.rglob\(|"
    r"\biglob\b|\bos\.scandir\b|\bpopen\b|\bos\.system\b|"
    # ...and the third route, which the `import onethird_*` scan cannot see by
    # construction: a module that LOADS AND RUNS another module dynamically.
    # `scripts/onethird_mga471_partial_run_control.py` and
    # `scripts/onethird_mg77e6_sixteenth_channel_probe.py` both do -- they drive
    # a real `main()` out of a module they name at runtime -- so the code they
    # execute is outside the closure and whatever IT reads is outside the input
    # set.  (`compile(` is deliberately NOT here: nearly every hit is
    # `re.compile`, and an exemption rule that fires on 40 modules to catch 2 is
    # a rule that makes the filter decorative.)
    r"\bimportlib\b|\brunpy\b|\bexec\(|\b__import__\b")

# The second opaque idiom, and the one that is easy to miss because it LOOKS
# like the derivable one: `os.path.join(REPO, "data", REF)` with REF a NAME
# rather than a string.  The dataset is real and the path is a repo path, and no
# literal in the file spells it -- so the derived input set silently omits a
# file the module reads.  Matched against whitespace-stripped source, as the
# corpus's own dataset regex is.
_VARPATH_RE = re.compile(r'os\.path\.join\(REPO,(?:"data",)?[A-Za-z_]')


# ------------------------------------------------------------- readers ------
def disk_reader(root=None):
    root = root or REPO

    def read(rel):
        path = os.path.join(root, rel)
        if not os.path.isfile(path):
            return None
        with open(path, "r", encoding="utf-8") as fh:
            return fh.read()
    return read


def dict_reader(mapping):
    return lambda rel: mapping.get(rel)


# ------------------------------------------------------------- derivation ---
def path_literals(src):
    """Repo-relative path literals in a source file, plus the data idiom.

    Most of these come out of PROSE -- the corpus's modules cite each other's
    paths in docstrings -- and that is deliberate.  Over-wide costs runtime;
    narrow costs a skipped control.

    Trailing punctuation is stripped, and that is not cosmetic: a docstring
    sentence ending "...familyB_sp_probe.py." yields a path that matches NO
    file, so a branch editing the real `.py` would fail to intersect it and the
    step would be skipped.  A sloppy regex here is an under-approximation, which
    is the one direction this module must never err in.
    """
    found = set()
    for p in _PATH_RE.findall(src):
        p = re.sub(r"[^\w/]+$", "", p)
        if p:
            found.add(p)
    for name, _write in _DATA_RE.findall(re.sub(r"\s+", "", src)):
        found.add("data/%s" % name)
    return found


def step_roots(command):
    """([script paths], [unrecognised command lines]) for one step's command."""
    roots, opaque = [], []
    for line in command.splitlines():
        line = line.strip()
        if not line:
            continue
        m = _PY_CALL_RE.match(line)
        if not m:
            opaque.append(line)
            continue
        script, rest = m.group(1), m.group(2)
        if not script.endswith(".py"):
            # `"$PY" --version` and friends: no script, nothing to derive.
            opaque.append(line)
            continue
        roots.append(script)
        for tok in shlex.split(rest) if rest.strip() else []:
            for hit in _PATH_RE.findall(tok):
                roots.append(hit)
    return roots, opaque


def step_inputs(command, read):
    """(kind, inputs, reason) for one step.

    kind is 'filterable' or 'unfilterable'.  `inputs` is the derived set of
    repo-relative paths the step reads; it is meaningful only when filterable.
    """
    roots, opaque = step_roots(command)
    if opaque:
        return "unfilterable", set(), ("command line not a `\"$PY\" <script>` "
                                       "call: %r" % opaque[0])
    if not roots:
        return "unfilterable", set(), "no script could be derived from the command"

    seen, queue = set(), [r for r in roots if r.endswith(".py")]
    inputs = set(r for r in roots if not r.endswith(".py"))
    while queue:
        rel = queue.pop()
        if rel in seen:
            continue
        src = read(rel)
        if src is None:
            return "unfilterable", set(), (
                "%s does not exist, so the import closure is incomplete and the "
                "derived input set is only a lower bound" % rel)
        seen.add(rel)
        hit = _OPAQUE_RE.search(src)
        if hit:
            return "unfilterable", set(), (
                "%s uses %r, so what it reads is not derivable from path "
                "literals" % (rel, hit.group(0)))
        if _VARPATH_RE.search(re.sub(r"\s+", "", src)):
            return "unfilterable", set(), (
                "%s builds a repo path from a NAME rather than a literal, so a "
                "file it reads is spelled nowhere in it" % rel)
        inputs |= path_literals(src)
        for mod in _IMPORT_RE.findall(src):
            child = "scripts/%s.py" % mod
            if child not in seen:
                queue.append(child)

    return "filterable", seen | inputs, ""


def gate_self(read):
    """Files whose change makes filtering unsound, derived from the gate."""
    self_paths = {PRESUBMIT, SELF}
    src = read(PRESUBMIT)
    if src is not None:
        self_paths |= set(_PATH_RE.findall(src))
    for rel in (SELF, "scripts/%s.py" % PLAN.__name__):
        s = read(rel)
        if s is None:
            continue
        self_paths.add(rel)
        self_paths |= set(_PATH_RE.findall(s))
    # Keep only things that look like files this repo tracks.
    return set(p for p in self_paths if not p.endswith("/"))


def classify(plan, read):
    """[(name, kind, inputs, reason)] for every step of the plan, in order.

    A step whose derived closure MEETS the gate's own machinery is forced
    unfilterable, and this is the subtle one.  The two plan-coverage controls
    (mg-3067's `--check` and this module's) read the workflow and the corpus in
    order to decide what the plan IS, so their verdicts are a function of files
    they name nowhere -- an edit to any corpus script can move this module's own
    K4 row.  A control whose verdict depends on the whole tree must not be
    filtered on the literals it happens to contain.  Derived from the
    intersection, not from a list of the two steps.
    """
    selves = gate_self(read)
    out = []
    for name, command, _dropped in plan:
        kind, inputs, reason = step_inputs(command, read)
        if kind == "filterable" and inputs & selves:
            kind, reason = "unfilterable", (
                "its closure meets the gate's own machinery (%s), so its "
                "verdict is a function of files it does not name"
                % sorted(inputs & selves)[0])
            inputs = set()
        out.append((name, kind, inputs, reason))
    return out


def select(plan, changed, read):
    """[(name, run, kind, reason)] -- what runs, what is skipped, and why.

    `changed` is an iterable of repo-relative paths.
    """
    changed = set(changed)
    selves = gate_self(read)
    touched_self = sorted(changed & selves)
    rows = []
    for name, kind, inputs, reason in classify(plan, read):
        if touched_self:
            rows.append((name, True, kind,
                         "the gate's own files changed (%s), so filtering is "
                         "not sound" % touched_self[0]))
        elif kind == "unfilterable":
            rows.append((name, True, kind, reason))
        else:
            hits = sorted(changed & inputs)
            if hits:
                rows.append((name, True, kind, "touches %s" % hits[0]))
            else:
                rows.append((name, False, kind,
                             "none of its %d derived inputs is in this "
                             "branch's %d changed paths" % (len(inputs),
                                                            len(changed))))
    return rows


# ------------------------------------------------------------- the control --
def check(read):
    """(problems, rows).  Every assertion the filter's soundness rests on."""
    problems, rows = [], []
    text = read(PLAN.WORKFLOW)
    if text is None:
        return ["%s is missing" % PLAN.WORKFLOW], rows
    plan = PLAN.build_plan(PLAN.parse_steps(text))

    # K0.  REFUSE A VERDICT OVER AN EMPTY POPULATION.  mg-9a59's defect, and a
    # filter is the shape that has it twice over: a plan of zero steps, and a
    # filter that skips all of them, both report a clean run.
    if not plan:
        problems.append(
            "parsed ZERO steps out of %s -- there is no plan to filter, and a "
            "filter over an empty plan is not a cheap gate, it is no gate"
            % PLAN.WORKFLOW)
        return problems, rows
    rows.append("steps in the plan: %d" % len(plan))

    rowsets = classify(plan, read)
    filt = [r for r in rowsets if r[1] == "filterable"]
    unfilt = [r for r in rowsets if r[1] == "unfilterable"]
    rows.append("filterable: %d   unfilterable (always run): %d"
                % (len(filt), len(unfilt)))

    # K1.  EVERY STEP IS CLASSIFIED, and into exactly one bucket.  A step that
    # reached neither is a step the filter has an opinion about and no rule for.
    if len(filt) + len(unfilt) != len(plan):
        problems.append("classification does not close: %d + %d != %d"
                        % (len(filt), len(unfilt), len(plan)))

    # K2.  A FILTERABLE STEP READS ITS OWN SCRIPT.  If the derived input set
    # does not contain the script the step runs, the filter would skip a step
    # whose own source this branch rewrote.  This is the single assertion that
    # would have to fail for the filter to be actively unsafe.
    for name, kind, inputs, _reason in filt:
        roots, _ = step_roots(dict(
            (n, c) for n, c, _ in plan).get(name, ""))
        for r in roots:
            if r.endswith(".py") and r not in inputs:
                problems.append(
                    "step %r is filterable but its own script %s is not in its "
                    "derived input set" % (name, r))

    # K3.  THE FAIL-SAFE FIRES.  A change to the gate's own files must run the
    # whole plan.  Asserted by running the selector, not by reading the code.
    selves = sorted(gate_self(read))
    if PRESUBMIT not in selves or PLAN.WORKFLOW not in selves:
        problems.append(
            "the gate's own file set is missing %s or %s -- editing the gate "
            "would then be filtered like ordinary work"
            % (PRESUBMIT, PLAN.WORKFLOW))
    forced = select(plan, {PRESUBMIT}, read)
    if not all(run for _n, run, _k, _r in forced):
        problems.append("a change to %s did not force the whole plan to run"
                        % PRESUBMIT)
    rows.append("gate's own files (change -> run everything): %d" % len(selves))

    # K4.  THE FILTER CAN ACTUALLY SKIP SOMETHING, and can actually run
    # something.  Both directions, on the real plan.  A filter that never skips
    # is the 11 minutes this ticket is about; a filter that never runs a step
    # is a gate that grades nothing.
    none_touched = select(plan, {"README.md"}, read)
    ran = sum(1 for _n, run, _k, _r in none_touched if run)
    if ran == len(plan):
        problems.append(
            "a change touching only README.md still runs all %d steps -- the "
            "filter cannot skip anything, so it is decoration" % len(plan))
    if ran == 0:
        problems.append(
            "a change touching only README.md runs ZERO steps -- every step "
            "including the unfilterable ones was dropped")
    rows.append("on a README.md-only change: %d of %d steps run"
                % (ran, len(plan)))

    # K5.  EVERY UNFILTERABLE STEP STATES WHY.  An always-run step with no
    # reason is a rule nobody can review or narrow later.
    for name, _kind, _inputs, reason in unfilt:
        if not reason.strip():
            problems.append("step %r is unfilterable with no stated reason"
                            % name)

    # K6.  PHANTOM INPUTS ARE COUNTED AND SHOWN.  A derived input matching no
    # file is usually harmless (it can never be touched) and is sometimes the
    # visible end of a path literal that was mangled out of prose -- the
    # dangerous case, because the REAL path is then absent from the set and the
    # step would be skipped on a branch that edits it.  Not fatal: a branch
    # deleting a file legitimately produces one.  Reported, so the number cannot
    # grow quietly, which is this corpus's standing rule for anything exempt.
    allinputs = set()
    for _n, _k, inputs, _r in filt:
        allinputs |= inputs
    phantom = sorted(p for p in allinputs if read(p) is None)
    rows.append("derived inputs: %d distinct, %d matching no file in the tree%s"
                % (len(allinputs), len(phantom),
                   (" (%s)" % ", ".join(phantom[:4])) if phantom else ""))

    for name, kind, inputs, reason in rowsets:
        rows.append("  %-12s %-4d %s%s"
                    % (kind, len(inputs), name[:58],
                       "" if kind == "filterable" else "  <- %s" % reason[:70]))
    return problems, rows


# ------------------------------------------------------------- self-test ----
_WF = """\
jobs:
  controls:
    steps:
      - uses: actions/checkout@v5
      - name: 'pure'
        run: python3 scripts/onethird_selftest_pure.py
      - name: 'sweeper'
        run: python3 scripts/onethird_selftest_sweeper.py
      - name: 'version'
        run: python3 --version
"""

_BASE = {
    PLAN.WORKFLOW: _WF,
    PRESUBMIT: ("PLAN_SCRIPT=scripts/onethird_mg3067_presubmit_steps.py\n"
                "WORKFLOW=.github/workflows/script-controls.yml\n"),
    SELF: "",
    "scripts/onethird_mg3067_presubmit_steps.py": "",
    "scripts/onethird_selftest_pure.py": (
        'import onethird_selftest_helper\n'
        'open(os.path.join(REPO, "data", "selftest-input.json"))\n'),
    "scripts/onethird_selftest_helper.py": "pass\n",
    "scripts/onethird_selftest_sweeper.py": "import os\nos.listdir('docs')\n",
}


def _selftest():
    rows, ok = [], True

    problems, _ = check(dict_reader(_BASE))
    rows.append(("pristine minimal plan", not problems,
                 "; ".join(problems) or "clean"))
    ok = ok and not problems

    cases = []

    # D1: a step's own script vanishes -> the closure is incomplete, so the
    # step must become unfilterable rather than filterable over a lower bound.
    # (The `d=d` default argument is not decoration.  Written as a bare
    # closure, every case captured the LAST `d` bound before the loop and D1
    # silently graded D2's input -- caught by this self-test on its first run,
    # in the self-test's own harness.)
    d = dict(_BASE)
    del d["scripts/onethird_selftest_helper.py"]
    cases.append(("an imported module disappears",
                  lambda d=d: _expect_kind(d, "pure", "unfilterable")))

    # D2: the sweeper stops sweeping -> it becomes filterable.  This is the
    # positive control: without it, D-cases that assert "unfilterable" would
    # pass under a filter that calls everything unfilterable.
    d = dict(_BASE)
    d["scripts/onethird_selftest_sweeper.py"] = "pass\n"
    cases.append(("a sweeper stops sweeping (positive control)",
                  lambda d=d: _expect_kind(d, "sweeper", "filterable")))

    # D3: a filterable step must run when its own script is touched.
    cases.append(("a filterable step's own script is touched",
                  lambda: _expect_run(_BASE, "pure",
                                      {"scripts/onethird_selftest_pure.py"},
                                      True)))

    # D4: ... and when a module it IMPORTS is touched.
    cases.append(("a module the step imports is touched",
                  lambda: _expect_run(_BASE, "pure",
                                      {"scripts/onethird_selftest_helper.py"},
                                      True)))

    # D5: ... and when a dataset it READS is touched.
    cases.append(("a dataset the step reads is touched",
                  lambda: _expect_run(_BASE, "pure",
                                      {"data/selftest-input.json"}, True)))

    # D6: ... and must be SKIPPED when none of them is.
    cases.append(("nothing the step reads is touched",
                  lambda: _expect_run(_BASE, "pure",
                                      {"docs/Whatever.md"}, False)))

    # D7: an unfilterable step is never skipped, whatever the change.
    cases.append(("an unfilterable step is offered an unrelated change",
                  lambda: _expect_run(_BASE, "sweeper",
                                      {"data/selftest-input.json"}, True)))

    # D8: THE FAIL-SAFE.  Touching the gate itself runs everything, including
    # the step that reads none of it.
    cases.append(("the gate's own file is touched",
                  lambda: _expect_run(_BASE, "pure", {PRESUBMIT}, True)))

    # D9: the dataset name moves from a LITERAL to a NAME.  The module still
    # reads a real file and now nothing in it spells the path, so the step must
    # stop being filterable.  This is the drift that would be invisible in a
    # diff -- `"selftest-input.json"` -> `REF` is one token.
    d = dict(_BASE)
    d["scripts/onethird_selftest_pure.py"] = (
        'import onethird_selftest_helper\n'
        'REF = "selftest-input.json"\n'
        'open(os.path.join(REPO, "data", REF))\n')
    cases.append(("a dataset path becomes a variable",
                  lambda d=d: _expect_kind(d, "pure", "unfilterable")))

    # D10: the module starts LOADING another module at runtime.  The
    # `import onethird_*` scan cannot see that by construction, so the code it
    # runs -- and everything that code reads -- is outside the derived set.
    d = dict(_BASE)
    d["scripts/onethird_selftest_pure.py"] = (
        'import importlib\n'
        'importlib.import_module("onethird_selftest_helper")\n')
    cases.append(("the module loads another module at runtime",
                  lambda d=d: _expect_kind(d, "pure", "unfilterable")))

    for label, fn in cases:
        try:
            good, detail = fn()
        except Exception as exc:                       # noqa: BLE001
            good, detail = False, "raised %s" % exc
        rows.append((label, good, detail))
        ok = ok and good

    print("  mg-6476 paths-filter self-test")
    for label, good, detail in rows:
        print("    %-4s %-46s %s" % ("ok" if good else "FAIL", label, detail))
    return ok


def _plan_of(mapping):
    return PLAN.build_plan(PLAN.parse_steps(mapping[PLAN.WORKFLOW]))


def _expect_kind(mapping, step_name, want):
    read = dict_reader(mapping)
    for name, kind, _inputs, reason in classify(_plan_of(mapping), read):
        if name == step_name:
            return kind == want, "%s (%s)" % (kind, reason or "-")
    return False, "step %r not in the plan" % step_name


def _expect_run(mapping, step_name, changed, want):
    read = dict_reader(mapping)
    for name, run, _kind, reason in select(_plan_of(mapping), changed, read):
        if name == step_name:
            return run == want, "%s -- %s" % ("RAN" if run else "SKIPPED",
                                              reason)
    return False, "step %r not in the plan" % step_name


# ------------------------------------------------------------- entry --------
def _read_changed(path):
    with open(path, "r", encoding="utf-8") as fh:
        return set(ln.strip() for ln in fh if ln.strip())


def main(argv):
    mode = argv[1] if len(argv) > 1 else "--list"

    if mode == "--selftest":
        return 0 if _selftest() else 1

    read = disk_reader()
    text = read(PLAN.WORKFLOW)
    if text is None:
        sys.stderr.write("mg-6476: %s is missing\n" % PLAN.WORKFLOW)
        return 2
    plan = PLAN.build_plan(PLAN.parse_steps(text))

    if mode == "--check":
        if not _selftest():
            print("mg-6476: FAIL -- the filter's own drifts were not all "
                  "caught, so its verdict on the real plan is not believed.")
            return 1
        problems, rows = check(read)
        print("  mg-6476 paths-filter over %s" % PLAN.WORKFLOW)
        for row in rows:
            print("    %s" % row)
        if problems:
            print("  mg-6476: FAIL -- the pre-submit paths filter is not sound:")
            for p in problems:
                print("    * %s" % p)
            return 1
        print("  mg-6476: OK -- every step is classified, the fail-safe fires, "
              "and skipping is possible in both directions.")
        return 0

    if mode == "--list":
        print("mg-6476 per-step inputs, derived from %s" % PLAN.WORKFLOW)
        for i, (name, kind, inputs, reason) in enumerate(classify(plan, read), 1):
            print("  %2d. [%s] %s" % (i, kind.upper(), name))
            if kind == "unfilterable":
                print("        always runs: %s" % reason)
            else:
                for p in sorted(inputs):
                    print("        %s" % p)
        return 0

    if mode == "--emit-sh":
        if "--changed" not in argv:
            sys.stderr.write("mg-6476: --emit-sh needs --changed FILE\n")
            return 2
        changed = _read_changed(argv[argv.index("--changed") + 1])
        if not plan:
            sys.stderr.write("mg-6476: parsed zero steps -- refusing to emit "
                             "an empty gate\n")
            return 2
        for name, run, _kind, reason in select(plan, changed, read):
            command = dict((n, c) for n, c, _ in plan)[name]
            if run:
                sys.stdout.write("step %s %s\n" % (shlex.quote(name),
                                                   shlex.quote(command)))
            else:
                sys.stdout.write("skip %s %s\n" % (shlex.quote(name),
                                                   shlex.quote(reason)))
        return 0

    sys.stderr.write("mg-6476: unknown mode %r\n" % mode)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
