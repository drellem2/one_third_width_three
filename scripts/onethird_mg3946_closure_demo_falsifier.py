#!/usr/bin/env python3
"""
mg-3946 -- CAN THE mg-75f0 CLASS-CLOSURE DEMO FAIL, and is the population of
historical-SHA reads actually closed?

INDEPENDENT AUDIT of the mg-3934 repair (`fetch-depth: 0` on
`.github/workflows/gate-mutation-demo.yml`, plus
`scripts/onethird_mg3934_ci_history_depth_control.py`).

WHY THIS FILE EXISTS.  mg-3934's own finding is that
`scripts/onethird_mg75f0_gate_class_closure_demo.py` had NEVER EXECUTED in CI:
it resolves `af7fc2df` and `actions/checkout` hands a depth-1 clone.  Its first
green is therefore its FIRST RUN.  A step that has never run is a step nobody
has seen fail, and an exit-0 nobody has ever seen turn into an exit-1 is a
claim, not a demonstration.  mg-3934 measured that the demo now RUNS.  Nothing
measured that it can still FAIL.  That is this file.

  PART 1  CAN IT FAIL?  Five drifts of the demo's own subject, each run in an
          isolated tree, each of which the demo MUST reject.  Plus an undrifted
          control it must accept.  Every case names its predicted exit code
          before the run.

  PART 2  WHAT THE DEMO CANNOT DISTINGUISH.  The demo's right column asserts
          `exit == 1` and nothing else.  A gate that CRASHES exits 1 too.  For
          the four rows whose left-column verdict is "NEVER EXERCISED" this is
          not hypothetical: a mutation that raises inside code the pre-widening
          gate does not reach yields exit 0 on the left and exit 1 on the
          right, i.e. a full PASS, with "the widening caught it" printed and
          nothing having been caught.  Case `crash` builds exactly that and
          measures what the demo says about it.

  PART 3  THE POPULATION OF HISTORICAL-SHA READS, by a route that shares no
          code with mg-3934's.  Detection is by AST (`subprocess`/`os.system`
          argument inspection, import graph) rather than by regex over source
          text, and a revision literal is anything git itself resolves rather
          than anything a naming convention labels.  So the two disagree in
          both directions and the disagreements are reported.

  PART 4  REACHABLE IN CI, WHICH IS NOT THE SAME AS RESOLVABLE HERE.
          mg-3934's property (B) asks `git rev-parse --verify` in the current
          checkout.  A developer's clone answers yes for objects that are in it
          for reasons CI will not reproduce -- a dangling commit, an object kept
          alive by a local branch or a reflog.  `fetch-depth: 0` fetches REMOTE
          REFS.  So the CI-predictive question is whether each pin is an
          ancestor of a remote ref, and this part asks that one.  mg-3934's own
          KNOWN LIMITS names this gap and defers it to (B), which cannot see it.

Run:  /usr/bin/python3 scripts/onethird_mg3946_closure_demo_falsifier.py
      --static-only        PARTS 3 and 4 only (order-seconds, no gate runs)
      --cases c1,c2        subset of PART 1/2 cases
      --selftest           PART 3/4's own drift battery alone
PARTS 1 and 2 are ~35 min: eleven full runs of the mg-2c34 gate, driven through
the demo.  Writes `data/onethird-mg3946-closure-demo-falsifier.json`.
Exits non-zero if any prediction is wrong, or if PART 3/4 find a problem.
"""

import os
import re
import ast
import sys
import json
import time
import shutil
import argparse
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT_DIR = "scripts"
WORKFLOW_DIR = ".github/workflows"

DEMO = "scripts/onethird_mg75f0_gate_class_closure_demo.py"
GATE = "scripts/onethird_mg2c34_n7_overlap_test.py"
PROBE = "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py"
DATASET = "data/onethird-mg8b64-L1b-bk-transport-transfer.json"


# ======================================================================
# PART 1/2 -- the drift battery over the demo
# ======================================================================
# Each case is (drift applied to an isolated tree, demo arguments, predicted
# demo exit code, what a wrong answer would mean).  The predictions are written
# here, before the runs, and are not adjusted afterwards.

def _sub(src, old, new, count=1, what=""):
    """Replace with an asserted occurrence count -- a silent no-match here
    would make a 'drifted' tree undrifted and the case a lie.  Same discipline
    the demo applies to its own mutations."""
    got = src.count(old)
    if got != count:
        raise SystemExit("mg-3946 %s: anchor found %d times, expected %d.\n"
                         "Anchor:\n%s" % (what, got, count, old))
    return src.replace(old, new)


def drift_none(tree):
    return "undrifted -- the demo's subject as committed"


def drift_neuter_widening(tree):
    """Undo the mg-75f0 widening at its load-bearing line: make the identity
    comparison iterate the four legacy fields again instead of the whole
    committed row.  This is the exact property the demo exists to demonstrate,
    so a demo that still exits 0 here is demonstrating nothing."""
    p = os.path.join(tree, GATE)
    src = open(p).read()
    src = _sub(src,
               "    matches, diffs = {}, {}\n    for k in sorted(ref_row):\n",
               "    matches, diffs = {}, {}\n"
               "    for k in ('num_LE', 'lambda_std', 'delta', 'bk_lambda2'):\n",
               1, "neuter-widening")
    open(p, "w").write(src)
    return ("the widened gate's identity comparison narrowed back to the four "
            "pre-mg-75f0 fields")


def drift_mutation_is_noop(tree):
    """Make M9's replacement identical to its anchor.  The anchor-count
    assertion still passes (the anchor is present exactly once), the tree is
    written back unchanged, and the 'mutated' run is the unmutated one.  This
    is the failure mode the demo's own count assertion does NOT cover."""
    p = os.path.join(tree, DEMO)
    src = open(p).read()
    src = _sub(src,
               '        "new": "    for r in range(1, n + 1):",',
               '        "new": "    for r in range(n, 0, -1):",',
               1, "noop-mutation")
    open(p, "w").write(src)
    return "M9's replacement made byte-identical to its anchor (a no-op edit)"


def drift_rotted_anchor(tree):
    """The anchor moves under a refactor.  The demo must die loudly rather
    than run an unmutated tree and call it mutated."""
    p = os.path.join(tree, PROBE)
    src = open(p).read()
    src = _sub(src, "    for r in range(n, 0, -1):",
               "    for r in reversed(range(1, n + 1)):", 1, "rotted-anchor")
    open(p, "w").write(src)
    return "M9's anchor rewritten in the corpus (semantics unchanged)"


def drift_baseline_is_the_widened_gate(tree):
    """Re-pin PRE_WIDENING_REV to the mg-75f0 LANDING commit.  The left column
    then compares the widened gate against itself and stops being a comparison
    -- the exact rot the demo's own comment says a merge-base baseline would
    have suffered and a pinned SHA cannot.  A pinned SHA cannot rot by itself;
    it can still be re-pinned wrongly, and nothing downstream re-derives it."""
    p = os.path.join(tree, DEMO)
    src = open(p).read()
    src = _sub(src, 'PRE_WIDENING_REV = "af7fc2df"',
               'PRE_WIDENING_REV = "9fa4aaa"', 1, "rebaseline")
    open(p, "w").write(src)
    return ("PRE_WIDENING_REV re-pinned from af7fc2df (mg-60d3) to 9fa4aaa "
            "(the mg-75f0 landing), so the left column IS the widened gate")


# PART 2.  A mutation that CRASHES the widened gate rather than being caught by
# it, placed in code the pre-widening gate never reaches, so the left column's
# exit 0 is preserved.  If the demo reports this as a PASS then its right
# column does not distinguish "the widening fired" from "the instrument fell
# over", and its headline sentence -- N/N mutations caught -- is unsupported
# for any row whose left-column verdict is NEVER EXERCISED.
_CRASH_ROW = '''
    "MX": {
        "desc": "mg-3946: a RAISE, not a moved quantity -- _width raises "
                "before scanning.  The pre-widening gate never calls _width "
                "(the demo's own left-column verdict for M9 is NEVER "
                "EXERCISED), so this crashes the widened gate only",
        "seen_by": "UNSEEN -- mg-3946's crash-vs-detection probe",
        "fields": ["width"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": "    for r in range(n, 0, -1):",
        "new": "    raise RuntimeError('mg-3946 MX')\\n"
               "    for r in range(n, 0, -1):",
        "count": 1,
    },
'''


def drift_crash_row(tree):
    p = os.path.join(tree, DEMO)
    src = open(p).read()
    src = _sub(src, '\nMUTATIONS = {\n', '\nMUTATIONS = {\n' + _CRASH_ROW,
               1, "crash-row")
    open(p, "w").write(src)
    return ("a row whose 'mutation' is an unconditional raise in _width, "
            "reached by the widened gate and not by the pre-widening one")


# EVERY CASE BELOW PASSES `--partial-ok`, AND NO PREDICTION CHANGED WITH IT
# (mg-a471).  This battery drives the demo over ONE mutation row, which is
# exactly the subset run this audit reported as F5: the demo used to answer such
# a run with the canonical report path, a ratio whose halves counted different
# populations, and exit 0.  mg-a471 made an unacknowledged subset run exit 2 and
# write elsewhere.  The battery is the caller that legitimately wants the
# narrower question answered -- did the one row that RAN hold? -- so it now says
# so at the command line, and the 0/1 answer it predicts is unchanged, still over
# the same rows, still measured against the same drifts.  The six predictions in
# the table below are the ones stated before the original run and they are not
# revised here; only the invocation is.
#
# A useful side effect: revert mg-a471 and `--partial-ok` becomes an unrecognised
# argument, argparse exits 2, and `control` fails loudly here instead of the fix
# rotting out quietly.
CASES = [
    {"name": "control", "drift": drift_none,
     "args": ["--only", "M9", "--gates", "widened", "--partial-ok"],
     "predict": 0,
     "means": "the undrifted demo accepts its own subject; if this is not 0 "
              "nothing else in PART 1 can be read"},
    {"name": "neutered-widening", "drift": drift_neuter_widening,
     "args": ["--only", "M9", "--gates", "widened", "--partial-ok"],
     "predict": 1,
     "means": "exit 0 here would mean the demo passes with the widening "
              "removed -- it would be asserting nothing about the widening"},
    {"name": "noop-mutation", "drift": drift_mutation_is_noop,
     "args": ["--only", "M9", "--gates", "widened", "--partial-ok"],
     "predict": 1,
     "means": "exit 0 here would mean a 'mutated' run that mutated nothing "
              "still counts as a mutation caught"},
    {"name": "rotted-anchor", "drift": drift_rotted_anchor,
     "args": ["--only", "M9", "--gates", "widened", "--partial-ok"],
     "predict": 1,
     "means": "exit 0 here would mean a refactor silently converts a mutation "
              "row into an unmutated run"},
    {"name": "rebaselined", "drift": drift_baseline_is_the_widened_gate,
     "args": ["--only", "M9", "--gates", "pre-widening", "--partial-ok"],
     "predict": 1,
     "means": "exit 0 here would mean the left column can be re-pinned onto "
              "the widened gate and the demo would not notice it had stopped "
              "being a comparison"},
    # PART 2, AND THE PREDICTION HERE CHANGED ONCE, DELIBERATELY.
    #
    # Against the demo AS mg-3934 LEFT IT the prediction was exit 0 and it
    # HELD, in 557.2 s: the demo printed
    #
    #     MX  ...  exit 0 ok      exit 1 ok
    #           (no gate failure reported)
    #     Demonstration complete.  1/6 mutations ... are caught by the widened
    #     gate, and 1/6 of them were fatal to nothing before it
    #
    # over a "mutation" that is a bare `raise` in `_width`.  The widened gate
    # did not catch it; it fell over.  That measurement is finding F1 and it is
    # kept in docs/OneThird-mg3946-CIHistoryDepth-IndependentAudit.md sec 2.
    #
    # mg-3946 then repaired the demo, so the prediction for the repaired
    # subject is 1 and this case becomes a standing regression control: revert
    # the strengthening and this row goes back to 0 and fails here.
    {"name": "crash-not-catch", "drift": drift_crash_row,
     "args": ["--only", "MX", "--gates", "pre-widening,widened",
              "--partial-ok"],
     "predict": 1,
     "means": "PART 2.  exit 1 = the demo distinguishes a crash from a catch "
              "(the mg-3946 repair, live).  exit 0 = the repair has been "
              "reverted and a crashing gate is again scored as the widening "
              "firing -- which is what it did before this ticket"},
]


def build_demo_tree(root):
    """An isolated copy of the corpus that git still works in: the worktree's
    `.git` pointer is copied verbatim, so `git show <rev>:<path>` -- which the
    demo needs and which is the whole subject of mg-3934 -- resolves exactly as
    it does in the real tree."""
    os.makedirs(os.path.join(root, SCRIPT_DIR))
    os.makedirs(os.path.join(root, "data"))
    for fn in os.listdir(os.path.join(REPO, SCRIPT_DIR)):
        if fn.endswith(".py"):
            shutil.copy2(os.path.join(REPO, SCRIPT_DIR, fn),
                         os.path.join(root, SCRIPT_DIR, fn))
    shutil.copy2(os.path.join(REPO, DATASET), os.path.join(root, DATASET))
    dotgit = os.path.join(REPO, ".git")
    if os.path.isfile(dotgit):
        shutil.copy2(dotgit, os.path.join(root, ".git"))
    else:                                    # a non-worktree clone
        with open(os.path.join(root, ".git"), "w") as f:
            f.write("gitdir: %s\n" % dotgit)


def run_case(case, keep=False):
    root = tempfile.mkdtemp(prefix="mg3946-%s-" % case["name"])
    t0 = time.time()
    try:
        build_demo_tree(root)
        what = case["drift"](root)
        proc = subprocess.run([sys.executable, DEMO] + case["args"],
                              cwd=root, capture_output=True, text=True)
        out = proc.stdout
        return {"case": case["name"], "drift": what, "args": case["args"],
                "predicted_exit": case["predict"], "exit": proc.returncode,
                "PREDICTION_HELD": proc.returncode == case["predict"],
                "seconds": round(time.time() - t0, 1),
                "means": case["means"],
                "demo_matrix": [l for l in out.splitlines()
                                if l.startswith(("none ", "M9 ", "MX ",
                                                 "mutation "))],
                "demo_verdict": [l for l in out.splitlines()
                                 if "DEMONSTRATION" in l
                                 or l.startswith("Demonstration complete")],
                "gate_failure_lines": [l.strip() for l in out.splitlines()
                                       if "GATE FAILURE:" in l][:4],
                "no_gate_failure_reported": out.count(
                    "(no gate failure reported)"),
                "stdout_tail": out[-1500:], "stderr_tail": proc.stderr[-1500:]}
    finally:
        if not keep:
            shutil.rmtree(root, ignore_errors=True)


# ======================================================================
# PART 3 -- the population of historical-SHA reads, by an independent route
# ======================================================================
# mg-3934 detects a git call with a regex over source text and a revision with
# a naming convention plus a 7-40 hex pattern.  This detects a git call by
# INSPECTING THE ARGUMENTS of `subprocess`/`os` calls in the parsed AST, and a
# revision by ASKING GIT whether a literal names a commit.  Neither route is a
# refinement of the other, which is the point: a literal mg-3934's convention
# does not label (a six-character abbreviation, a name with no REV/SHA/COMMIT
# in it, on a line that never says `git`) is invisible to it and visible here.

_HEXISH = re.compile(r"^[0-9a-f]{4,40}$")


def string_literals(tree):
    out = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            out.add(node.value)
        elif isinstance(node, ast.JoinedStr):
            for v in node.values:
                if isinstance(v, ast.Constant) and isinstance(v.value, str):
                    out.add(v.value)
    return out


def calls_git(tree):
    """True iff some call in this module hands git to a subprocess.  Looks at
    the ARGUMENTS, so `["git", "show", rev]`, `"git log ..."` under a shell,
    and `os.system("git ...")` are all one rule."""
    hits = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        for arg in list(node.args) + [k.value for k in node.keywords]:
            if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if re.match(r"^git(\s|$)", arg.value):
                    hits.append(arg.value[:40])
            elif isinstance(arg, (ast.List, ast.Tuple)) and arg.elts:
                first = arg.elts[0]
                if (isinstance(first, ast.Constant)
                        and first.value in ("git", "/usr/bin/git")):
                    hits.append("argv[0]=git")
    return sorted(set(hits))


def imports_of(tree):
    out = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                out.add(a.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            out.add(node.module.split(".")[0])
    return {m for m in out if m.startswith(("onethird_", "posn_", "compat_",
                                            "audit_"))}


def parse_py(rel):
    path = os.path.join(REPO, rel)
    if not os.path.isfile(path):
        return None, None
    src = open(path).read()
    try:
        return src, ast.parse(src)
    except SyntaxError:
        return src, None


def workflow_steps(text):
    """Every `run:` body in a workflow, as text, plus each checkout's
    fetch-depth.  The bodies matter and mg-3934 does not read them: it extracts
    `scripts/*.py` invocations only, so a bare `git show` written straight into
    a step -- no script involved -- is outside its detection entirely."""
    lines = text.splitlines()
    bodies, depths = [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.lstrip().startswith("#"):
            i += 1
            continue
        m = re.match(r"^(\s*)-?\s*run:\s*(\|.*|>.*)?$", line)
        m2 = re.match(r"^(\s*)-?\s*run:\s+(\S.*)$", line)
        if m:
            indent = len(m.group(1))
            i += 1
            block = []
            while i < len(lines):
                nxt = lines[i]
                if nxt.strip() and (len(nxt) - len(nxt.lstrip())) <= indent:
                    break
                block.append(nxt)
                i += 1
            bodies.append("\n".join(block))
            continue
        if m2:
            bodies.append(m2.group(2))
        mc = re.match(r"^(\s*)-\s*uses:\s*actions/checkout", line)
        if mc:
            indent = len(mc.group(1))
            depth = None
            for nxt in lines[i + 1:]:
                if not nxt.strip() or nxt.lstrip().startswith("#"):
                    continue
                if len(nxt) - len(nxt.lstrip()) <= indent:
                    break
                d = re.match(r"^\s*fetch-depth:\s*(\d+)", nxt)
                if d:
                    depth = int(d.group(1))
                    break
            depths.append(depth)
        i += 1
    return bodies, depths


_SCRIPT_IN_BODY = re.compile(r"(scripts/[\w./-]+\.(?:py|sh))")


def resolve_batch(revs):
    """Ask git which candidate literals actually name a commit.  One
    `cat-file --batch-check` call rather than N `rev-parse` calls."""
    revs = sorted(set(revs))
    if not revs:
        return {}
    proc = subprocess.run(["git", "cat-file", "--batch-check"], cwd=REPO,
                          input="\n".join(r + "^{commit}" for r in revs),
                          capture_output=True, text=True)
    out = {}
    for rev, line in zip(revs, proc.stdout.splitlines()):
        out[rev] = ("missing" not in line and "ambiguous" not in line
                    and line.split()[1:2] == ["commit"])
    return out


def reachable_from_remote(rev):
    """PART 4.  `fetch-depth: 0` fetches remote REFS.  An object present here
    for a local-only reason -- a local branch, a reflog, a dangling commit --
    is not in that clone however cleanly `git rev-parse` answers here."""
    refs = subprocess.run(["git", "for-each-ref", "--format=%(refname)",
                           "refs/remotes/"], cwd=REPO,
                          capture_output=True, text=True).stdout.split()
    for ref in refs:
        if subprocess.run(["git", "merge-base", "--is-ancestor", rev, ref],
                          cwd=REPO, capture_output=True).returncode == 0:
            return True, ref
    return False, "no remote ref"


def sweep():
    """The population, named rather than counted: every workflow, every script
    it executes, the transitive corpus closure of each, and for each module in
    that closure whether it shells out to git and which literals in it git
    resolves to commits."""
    problems, rows = [], []
    wf_dir = os.path.join(REPO, WORKFLOW_DIR)
    workflows = sorted(fn for fn in os.listdir(wf_dir)
                       if fn.endswith((".yml", ".yaml")))
    all_revs = set()

    for fn in workflows:
        rel = "%s/%s" % (WORKFLOW_DIR, fn)
        text = open(os.path.join(REPO, rel)).read()
        bodies, depths = workflow_steps(text)

        # (i) history read written straight into a step body, no script at all.
        inline = []
        for b in bodies:
            for mline in b.splitlines():
                if re.search(r"(?<![\w-])git\s+(show|log|rev-parse|cat-file|"
                             r"diff|archive|checkout)", mline):
                    inline.append(mline.strip()[:70])

        # (ii) the scripts the steps execute, and their closure.
        entries = set()
        for b in bodies:
            entries.update(_SCRIPT_IN_BODY.findall(b))
        closure, missing, queue = set(), set(), list(entries)
        while queue:
            r = queue.pop()
            if r in closure or r in missing:
                continue
            if r.endswith(".sh"):
                if os.path.isfile(os.path.join(REPO, r)):
                    closure.add(r)
                else:
                    missing.add(r)
                continue
            src, tree = parse_py(r)
            if src is None:
                missing.add(r)
                continue
            closure.add(r)
            if tree is not None:
                for mod in imports_of(tree):
                    queue.append("%s/%s.py" % (SCRIPT_DIR, mod))

        readers = {}
        for r in sorted(closure):
            if r.endswith(".sh"):
                src = open(os.path.join(REPO, r)).read()
                git_hits = re.findall(r"(?<![\w-])git\s+\w[\w-]*", src)
                lits = set(re.findall(r"[\"']?([0-9a-f]{4,40})[\"']?\b", src))
            else:
                src, tree = parse_py(r)
                if tree is None:
                    continue
                git_hits = calls_git(tree)
                lits = {s for s in string_literals(tree) if _HEXISH.match(s)}
            if not git_hits:
                continue
            hits = sorted(lits)
            all_revs.update(hits)
            readers[r] = {"git": sorted(set(git_hits))[:4], "candidates": hits}

        rows.append({"workflow": rel, "fetch_depths": depths,
                     "entry_scripts": sorted(entries),
                     "closure_size": len(closure),
                     "missing_from_closure": sorted(missing),
                     "inline_git_in_step_bodies": inline,
                     "git_calling_modules": readers})
        if inline and not (depths and all(d == 0 for d in depths)):
            problems.append(
                "%s runs git directly in a step body (%s) with fetch-depth %s "
                "-- mg-3934's (A) reads only `scripts/*` invocations, so an "
                "inline history read is outside its detection" %
                (rel, "; ".join(inline[:2]),
                 ", ".join("unset(=1)" if d is None else str(d)
                           for d in depths) or "no checkout"))

    # The population is not "what CI executes": mg-3934's own property (B)
    # scans ALL of scripts/, so a pin in a hand-run probe that stops being
    # reachable fails the CI preflight in the deep job.  Sweep the whole
    # directory, and name it rather than counting it.
    corpus_pins = {}
    for fn in sorted(os.listdir(os.path.join(REPO, SCRIPT_DIR))):
        if not fn.endswith((".py", ".sh")):
            continue
        rel = "%s/%s" % (SCRIPT_DIR, fn)
        if fn.endswith(".sh"):
            src = open(os.path.join(REPO, rel)).read()
            if not re.search(r"(?<![\w-])git\s+\w", src):
                continue
            lits = set(re.findall(r"[\"']?([0-9a-f]{4,40})[\"']?\b", src))
        else:
            src, tree = parse_py(rel)
            if tree is None or not calls_git(tree):
                continue
            lits = {s for s in string_literals(tree) if _HEXISH.match(s)}
        if lits:
            corpus_pins[rel] = sorted(lits)
            all_revs.update(lits)

    resolved = resolve_batch(all_revs)
    real = sorted(r for r, ok in resolved.items() if ok)
    corpus_revs = {rel: [c for c in cands if resolved.get(c)]
                   for rel, cands in corpus_pins.items()}
    corpus_revs = {k: v for k, v in corpus_revs.items() if v}
    for row in rows:
        deep = bool(row["fetch_depths"]) and all(d == 0
                                                 for d in row["fetch_depths"])
        row["real_revisions_read"] = {}
        for mod, info in row["git_calling_modules"].items():
            hits = [c for c in info["candidates"] if resolved.get(c)]
            if hits:
                row["real_revisions_read"][mod] = hits
        if row["real_revisions_read"] and not deep:
            problems.append(
                "%s executes code that resolves a historical commit (%s) but "
                "its checkout is fetch-depth %s -- STILL BROKEN" %
                (row["workflow"],
                 "; ".join("%s [%s]" % (m, ", ".join(v))
                           for m, v in row["real_revisions_read"].items()),
                 ", ".join("unset(=1)" if d is None else str(d)
                           for d in row["fetch_depths"]) or "no checkout"))

    # PART 4 -- reachable from a remote ref, not merely present here.
    reach = {}
    for rev in real:
        ok, where = reachable_from_remote(rev)
        reach[rev] = {"reachable": ok, "via": where}
        if not ok:
            problems.append(
                "revision %s resolves in THIS checkout but is reachable from "
                "no remote ref, so `fetch-depth: 0` will not fetch it and any "
                "CI step that reads it fails there while passing here" % rev)
    return problems, rows, resolved, reach, corpus_revs


# --------------------------------------------------------------- self-test ---
_SELFTEST_FILES = {
    "inline": ("      - run: |\n          git show abc1234:x\n", None, True),
    "inline-deep": ("      - run: |\n          git show abc1234:x\n", 0, False),
    "plain": ("      - run: echo hello\n", None, False),
}


def selftest():
    """PART 3's own drifts.  The inline-git detection is the property mg-3934
    does not have, so it is the one that must be shown to fire."""
    ok = True
    head = ("name: T\non:\n  push:\njobs:\n  j:\n    runs-on: ubuntu-latest\n"
            "    steps:\n      - uses: actions/checkout@v5\n")
    for name, (step, depth, want_inline) in _SELFTEST_FILES.items():
        text = head + ("        with:\n          fetch-depth: %d\n" % depth
                       if depth is not None else "") + step
        bodies, depths = workflow_steps(text)
        found = any(re.search(r"(?<![\w-])git\s+show", b) for b in bodies)
        deep = bool(depths) and all(d == 0 for d in depths)
        fires = found and not deep
        good = (fires == want_inline)
        ok = ok and good
        print("  %-46s %s" % ("inline-git drift: " + name,
                              "ok" if good else "FAILED"))
    # the AST git detector must see all three idioms and reject a lookalike
    for src, want in [('import subprocess\nsubprocess.run(["git","show","x"])',
                       True),
                      ('import os\nos.system("git log -1")', True),
                      ('print("gitignore is not a git call")', False),
                      ('run(["gitlab","show"])', False)]:
        got = bool(calls_git(ast.parse(src)))
        good = got == want
        ok = ok and good
        print("  %-46s %s" % ("ast git-call: %r" % src.splitlines()[-1][:28],
                              "ok" if good else "FAILED"))
    print("SELF-TEST %s" % ("PASSED" if ok else "FAILED"))
    return ok


# ======================================================================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--static-only", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--cases", default="")
    args = ap.parse_args()

    print("=" * 78)
    print("mg-3946 -- can the mg-75f0 class-closure demo FAIL, and is the "
          "SHA-read class closed?")
    print("=" * 78)
    print("\n=== PART 3/4 self-test")
    st = selftest()
    if args.selftest:
        return 0 if st else 1

    problems, rows, resolved, reach, corpus_revs = sweep()
    print("\n=== PART 3  every workflow x the code it executes")
    for row in rows:
        depths = ", ".join("unset(=1)" if d is None else str(d)
                           for d in row["fetch_depths"]) or "no checkout"
        print("  %-44s fetch-depth %s  (closure %d)"
              % (row["workflow"], depths, row["closure_size"]))
        for e in row["entry_scripts"]:
            print("      executes: %s" % e)
        for line in row["inline_git_in_step_bodies"]:
            print("      INLINE GIT IN A STEP BODY: %s" % line)
        for mod, info in sorted(row["git_calling_modules"].items()):
            print("      calls git: %-56s %s" % (mod, ", ".join(info["git"])))
        for mod, hits in sorted(row["real_revisions_read"].items()):
            print("      READS REVISIONS: %-50s %s" % (mod, ", ".join(hits)))
        if not row["real_revisions_read"]:
            print("      reads no historical revision")

    print("\n=== PART 4  the WHOLE scripts/ pin population, named not counted")
    n_lit = sum(len(v) for v in corpus_revs.values())
    for rel, revs in sorted(corpus_revs.items()):
        print("  %-52s %s" % (rel, ", ".join(revs)))
    print("  --> %d literal(s), %d distinct revision(s), %d script(s): %s"
          % (n_lit, len(set(sum(corpus_revs.values(), []))), len(corpus_revs),
             ", ".join(sorted(set(sum(corpus_revs.values(), []))))))
    print("\n  reachable from a REMOTE ref? (what fetch-depth: 0 actually "
          "fetches -- resolving HERE is not the same question)")
    for rev, info in sorted(reach.items()):
        print("    %-10s %-6s %s" % (rev, "ok" if info["reachable"] else "NO",
                                     info["via"]))
    unresolved = sorted(r for r, ok in resolved.items() if not ok)
    print("  hex-shaped candidates git does NOT resolve (not revisions): %d"
          % len(unresolved))

    results = []
    if not args.static_only:
        wanted = ([c for c in CASES if c["name"] in args.cases.split(",")]
                  if args.cases else CASES)
        print("\n=== PART 1/2  the drift battery over the demo "
              "(%d cases, predictions stated first)" % len(wanted))
        for c in wanted:
            print("\n  %-22s predict demo exit %d   args %s"
                  % (c["name"], c["predict"], " ".join(c["args"])), flush=True)
            r = run_case(c)
            results.append(r)
            print("      drift: %s" % r["drift"])
            print("      --> exit %d in %ss  %s"
                  % (r["exit"], r["seconds"],
                     "PREDICTION HELD" if r["PREDICTION_HELD"]
                     else "PREDICTION MISSED"))
            for line in r["demo_verdict"]:
                print("      demo said: %s" % line.strip()[:100])

    missed = [r for r in results if not r["PREDICTION_HELD"]]
    crash = next((r for r in results if r["case"] == "crash-not-catch"), None)
    report = {
        "what": "mg-3946 independent audit: can the mg-75f0 class-closure demo "
                "fail, and is the population of historical-SHA reads closed?",
        # F5 is a finding of this audit against the demo -- a subset run
        # overwriting the canonical report with no marker -- so this file does
        # not get to have it.  Every report says which cases it actually ran.
        "cases_requested": (args.cases.split(",") if args.cases
                            else ([] if args.static_only
                                  else [c["name"] for c in CASES])),
        "partial_run": bool(args.cases) or args.static_only,
        "part1_2_cases": results,
        "part1_predictions_missed": [r["case"] for r in missed],
        "part2_finding": (None if crash is None else
                          ("THE DEMO CANNOT DISTINGUISH A CRASH FROM A CATCH: "
                           "a mutation that raises inside code the "
                           "pre-widening gate never reaches is reported as a "
                           "mutation the widening caught"
                           if crash["exit"] == 0 else
                           "the demo rejects a crash-shaped mutation")),
        "part3_workflows": rows,
        "part4_scripts_pin_population": corpus_revs,
        "part4_remote_reachability": reach,
        "part3_4_problems": problems,
        "ALL_PASS": not missed and not problems,
    }
    out = os.path.join(REPO, "data",
                       "onethird-mg3946-closure-demo-falsifier.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print("\nwrote %s" % os.path.relpath(out, REPO))

    if problems:
        print("\nPART 3/4 PROBLEMS (%d):" % len(problems))
        for p in problems:
            print("  - %s" % p)
    if missed:
        print("\nPREDICTIONS MISSED (%d) -- kept as written:" % len(missed))
        for r in missed:
            print("  - %s: predicted %d, got %d.  %s"
                  % (r["case"], r["predicted_exit"], r["exit"], r["means"]))
    if not st:
        return 1
    return 1 if (problems or missed) else 0


if __name__ == "__main__":
    sys.exit(main())
