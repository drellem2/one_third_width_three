#!/usr/bin/env python3
"""
mg-3934 -- can every script CI runs actually reach the history it reads?

THE DEFECT THIS IS FOR.  `scripts/onethird_mg75f0_gate_class_closure_demo.py`
resolves a pinned historical commit (`git show af7fc2df:<gate>`) to build its
pre-widening column.  That resolves in a developer's clone, which has every
object, and cannot resolve under `actions/checkout`, whose default
`fetch-depth` is 1 and which therefore hands the job exactly one commit.  The
step was added on 2026-07-30 and failed on its first CI run and on every run
after it, so the demonstration it performs -- "does the widened identity check
catch mutations nobody enumerated?" -- had NEVER ONCE EXECUTED in CI.  Twenty-
one hours of red produced no response, because this repo has no branch
protection and the refinery does not read Actions.

The code was correct.  The environment was not the one it was verified in.
That is a class of defect, not an instance, and the instance was found only
because it happened to be the LAST step in its job: a second one in a step that
runs later would have been just as invisible.  This file closes the class.

TWO PROPERTIES.

  (A) COUPLING -- static, order-milliseconds, and safe in a depth-1 checkout
      because it resolves nothing.  For each workflow in `.github/workflows/`:
      derive the scripts it executes and their transitive `onethird_*` import
      closure, find every module in that closure that reads a HISTORICAL
      REVISION, and require the workflow's `actions/checkout` steps to set
      `fetch-depth: 0` if any does.  This is the half that catches the NEXT
      one, before it runs, in the workflow that would have hidden it.

  (B) RESOLVABILITY -- needs the objects, so it is meaningful only where the
      history is present.  Every pinned revision literal anywhere in
      `scripts/` must resolve to a commit in THIS checkout.  Run where the
      checkout is deep, it is a seconds-long preflight that turns "the pin
      rotted" from a 10-minute red run into an immediate, named failure.  Run
      where the checkout is shallow it fails by construction, which is why it
      is opt-out rather than always-on -- see the flags.

WHERE EACH ONE RUNS, and why they are not the same set:

  `.github/workflows/script-controls.yml`   --static-only   depth-1 by design;
      that workflow's steps read no history and (A) is what keeps it that way.
  `.github/workflows/gate-mutation-demo.yml`  full           `fetch-depth: 0`,
      set by mg-3934; (B) runs first, so a rotted pin costs seconds not ten
      minutes.
  `scripts/refinery_gate.sh`                  not run        the refinery
      operates on a full clone of the repo, so (A)'s premise -- a checkout
      action with a shallow default -- does not apply there.  (B) would pass
      and is left to Actions rather than added to the blocking path.

WHAT COUNTS AS "READS A HISTORICAL REVISION", stated because the detection is
a regex and its limits are the limits of this control.  A PINNED REVISION is a
quoted bare hex literal of 7 to 40 characters, found by any of:

  * assignment to a name containing REV, SHA or COMMIT -- the corpus's idiom;
  * appearance on a line that also mentions `git` -- the inline idiom;
  * appearance anywhere in a file that shells out to git at all -- which is
    what catches a literal handed to a helper (the corpus does this once,
    passing a landing-commit pin straight into a gate_source() call).

A module READS HISTORY iff it both invokes git and contains at least one such
literal.  Deliberately generous: a false positive costs one `fetch-depth: 0`,
a false negative costs a CI step that can never run.

KNOWN LIMITS, the same shape as the one mg-7db4 states.

  * A revision COMPUTED rather than written down -- read from a file, taken
    from an environment variable, derived from `git log` -- is invisible to
    both properties.  The fix (A) imposes is nonetheless the fix for that case
    too, so the exposure is detection, not remedy.
  * The 40-character cap keeps a sha256 digest literal (64 characters) from
    being mistaken for a revision -- applied to the whole PYTHON string, after
    adjacent literals are joined.  The join is not a nicety: 64 characters do
    not fit a 79-column line, so every digest in this corpus is wrapped, and
    before mg-ba2a the cap was applied per quoted piece.  A 42 + 22 wrap put
    the 22 inside the window, (B) called the tail a rotted pin, and main was
    red for eleven hours across four commits over a literal that had never
    been a git object.  A digest whose fragments are joined is 64 characters
    and is excluded, which is what this bullet always claimed.
  * The cap also means this control cannot see a pin in a repository whose
    object format is sha256, where 64 hex characters IS a revision.  This one
    is sha1; if that ever changes, the cap changes with it.
  * (A) is stated per FILE, not per job: a workflow with two jobs, only one of
    which reads history, is required to deepen both checkouts.  Conservative in
    the safe direction, and this repo's workflows have one job each.
  * `fetch-depth: 0` fetches every branch, so a pin reachable from no surviving
    branch is still unreachable in CI.  (B) is what sees that, and it sees it
    in the deep checkout where the failure is unambiguous rather than here.

SELF-TEST.  `--selftest`, also run by `main` on every invocation so CI gets it
for free: each property is re-checked against a deliberately drifted copy of
the inputs and this script exits non-zero unless every drift FIRES.  A control
that has never been shown to fail is the defect one level up, and this file
exists because of a control that had never once run.

Run:  python3 scripts/onethird_mg3934_ci_history_depth_control.py
      --static-only   property (A) only; safe in a shallow checkout
      --selftest      the drift battery alone
Exits non-zero on any problem.  Writes nothing.
"""

import os
import re
import sys
import argparse
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WORKFLOW_DIR = ".github/workflows"
SCRIPT_DIR = "scripts"

# A bare hex revision literal: 7-40 characters, the whole quoted string.  The
# upper bound is what keeps a 64-character sha256 digest out.
_HEX = r"[0-9a-f]{7,40}"
_REV_ASSIGN_RE = re.compile(
    r"^\s*[A-Za-z_]\w*(?:REV|SHA|COMMIT)\w*\s*=\s*[\"'](%s)[\"']" % _HEX,
    re.M | re.I)
_REV_INLINE_RE = re.compile(r"[\"'](%s)[\"']" % _HEX)
_GIT_CALL_RE = re.compile(r"[\"']git[\"']|(?<![\w-])git\s+(?:show|rev-parse|"
                          r"cat-file|log|diff|archive)")
_IMPORT_RE = re.compile(r"^\s*(?:from|import)\s+(onethird_\w+)", re.M)
# Python concatenates adjacent string literals, so `("39a4...3e" "8fc7...18")`
# is ONE 64-character string and not a 42 next to a 22.  The cap above is
# stated over the whole string, so it has to be applied AFTER that join --
# otherwise a wrapped sha256 digest exposes a 22-character tail that lands
# inside the 7-40 window, and (B) fails a pin that was never a revision at all.
# That is not hypothetical: it is mg-ba2a, eleven hours of red main across four
# commits, on the digest in onethird_mg76d0_partial_report_audit.py.  Wrapping
# a 64-character constant is what a 79-column style REQUIRES, so the exposure
# recurs on every digest added to a git-calling module until the join is here.
# Contents exclude quotes, backslashes and newlines: an escape or a triple
# quote simply is not joined, which leaves the old per-literal reading in place
# for those and is the conservative direction.
_ADJACENT_LITERAL_RE = re.compile(
    r"([\"'])([^\"'\\\n]*)\1\s*([\"'])([^\"'\\\n]*)\3")


def join_implicit_concat(src):
    """Collapse runs of adjacent string literals into single literals.

    Iterated to a fixpoint because one pass joins pairwise: `"a" "b" "c"`
    needs two.  Line structure moves -- a joined literal ends up on the line
    its FIRST fragment started on -- which is the reading the git-mentioning
    line scan below wants anyway."""
    prev = None
    while prev != src:
        prev = src
        src = _ADJACENT_LITERAL_RE.sub(
            lambda m: '"%s%s"' % (m.group(2), m.group(4)), src)
    return src
# A script an Actions step EXECUTES.  It must look like a command, not merely
# like a path: gate-mutation-demo.yml names fifteen script paths in its two
# `paths:` filters and neither list is a step.  Comment lines are dropped by
# the caller for the same reason -- both workflows quote example invocations
# inside `#` comments, and a commented command is not a step either.
_RUN_SCRIPT_RE = re.compile(
    r"(?:python[\d.]*\s+|bash\s+|sh\s+|\./)(scripts/[\w./-]+\.(?:py|sh))")
_CHECKOUT_RE = re.compile(r"^(\s*)-\s*uses:\s*actions/checkout")
_FETCH_DEPTH_RE = re.compile(r"^\s*fetch-depth:\s*(\d+)")


# ------------------------------------------------------------- readers ------
def disk_reader():
    """Source reader over the working tree; None for a path that is absent, so
    a rename is a reported problem rather than a traceback."""
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


def disk_lister():
    def lister(rel_dir, suffixes):
        d = os.path.join(REPO, rel_dir)
        if not os.path.isdir(d):
            return []
        return sorted("%s/%s" % (rel_dir, fn) for fn in os.listdir(d)
                      if fn.endswith(suffixes))
    return lister


def dict_lister(mapping):
    def lister(rel_dir, suffixes):
        return sorted(k for k in mapping
                      if k.startswith(rel_dir + "/") and k.endswith(suffixes))
    return lister


# ------------------------------------------------------------- detection ----
def revs_in(src):
    """The pinned revision literals in one source file, as a sorted list.

    Two idioms, deliberately both: the named constant (a REV/SHA/COMMIT name
    assigned a quoted hex string) and the bare literal on a git-mentioning
    line.  A file-level pairing catches the third -- a literal handed to a
    helper that shells out to git elsewhere in the same file.

    Adjacent literals are joined first, so the 7-40 window is applied to the
    whole Python string rather than to a line-wrapped piece of one.

    No quoted hex literal appears in this file, here or anywhere else; see the
    note above the self-test fixtures for why that is load-bearing."""
    src = join_implicit_concat(src)
    found = set(_REV_ASSIGN_RE.findall(src))
    for line in src.splitlines():
        if re.search(r"(?<![\w-])git(?![\w-])", line):
            found.update(_REV_INLINE_RE.findall(line))
    if _GIT_CALL_RE.search(src):
        # The file shells out to git somewhere, so every bare hex literal in
        # it is a candidate revision.  This is the conservative direction: a
        # false positive costs one `fetch-depth: 0`, a false negative costs a
        # step that can never run.
        found.update(_REV_INLINE_RE.findall(src))
    return sorted(found)


def reads_history(src):
    """True iff this module both invokes git and names a pinned revision."""
    return bool(_GIT_CALL_RE.search(src)) and bool(revs_in(src))


def import_closure(roots, read):
    """Transitive closure of `onethird_*` corpus modules, repo-relative.
    Unresolvable imports come back separately so a rename is reported rather
    than silently shrinking the closure."""
    seen, missing, queue = set(), set(), list(roots)
    while queue:
        rel = queue.pop()
        if rel in seen or rel in missing:
            continue
        src = read(rel)
        if src is None:
            missing.add(rel)
            continue
        seen.add(rel)
        for mod in _IMPORT_RE.findall(src):
            child = "%s/%s.py" % (SCRIPT_DIR, mod)
            if child not in seen:
                queue.append(child)
    return seen, missing


# ------------------------------------------------------------- parsers ------
def parse_workflow(text):
    """(entry scripts, checkout fetch-depths) for one workflow file.

    A hand parser on purpose, for the same reason mg-7db4's is: this must run
    under a bare interpreter with no PyYAML, on the fleet host and on a hosted
    runner.  `fetch_depths` has one entry per `actions/checkout` step, None
    where the step sets no `fetch-depth` (which is the depth-1 default and the
    whole subject of this file)."""
    entries, depths = set(), []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        if line.lstrip().startswith("#"):
            continue
        entries.update(_RUN_SCRIPT_RE.findall(line))
    for i, line in enumerate(lines):
        m = _CHECKOUT_RE.match(line)
        if not m:
            continue
        indent = len(m.group(1))
        depth = None
        for nxt in lines[i + 1:]:
            if not nxt.strip() or nxt.lstrip().startswith("#"):
                continue
            if len(nxt) - len(nxt.lstrip()) <= indent:
                break               # dedented out of this step
            d = _FETCH_DEPTH_RE.match(nxt)
            if d:
                depth = int(d.group(1))
                break
        depths.append(depth)
    return sorted(entries), depths


# -------------------------------------------------------------- checks ------
def check_coupling(read, lister):
    """(A).  Returns (problems, report rows).  Resolves nothing, so it is
    correct in a checkout of any depth -- including the depth-1 one it exists
    to reason about."""
    problems, rows = [], []
    workflows = lister(WORKFLOW_DIR, (".yml", ".yaml"))
    if not workflows:
        return (["no workflows found under %s -- this control has nothing to "
                 "check, which is not the same as everything being fine"
                 % WORKFLOW_DIR], rows)

    for wf in workflows:
        text = read(wf)
        if text is None:
            problems.append("%s vanished between listing and reading" % wf)
            continue
        entries, depths = parse_workflow(text)
        py_entries = [e for e in entries if e.endswith(".py")]
        closure, missing = import_closure(py_entries, read)
        for rel in sorted(missing):
            problems.append(
                "%s executes or imports %s, which does not exist -- the "
                "closure is incomplete, so the verdict below is derived from "
                "a corpus with a hole in it" % (wf, rel))
        # Shell entry points are checked as themselves; they have no imports.
        for rel in sorted(e for e in entries if e.endswith(".sh")):
            src = read(rel)
            if src is not None:
                closure = closure | {rel}

        readers = {}
        for rel in sorted(closure):
            src = read(rel)
            if src is not None and reads_history(src):
                readers[rel] = revs_in(src)

        deep = bool(depths) and all(d == 0 for d in depths)
        rows.append({"workflow": wf, "fetch_depths": depths,
                     "history_readers": readers})
        if readers and not deep:
            shown = ", ".join("%s (%s)" % (r, ", ".join(v))
                              for r, v in sorted(readers.items()))
            problems.append(
                "%s runs code that reads historical revisions -- %s -- but "
                "its actions/checkout sets fetch-depth %s.  actions/checkout "
                "defaults to depth 1, so those objects are not in the "
                "runner's clone and the step cannot run there, however "
                "correct it is on a developer's box.  Set `fetch-depth: 0` on "
                "the checkout step, or stop reading history in that job."
                % (wf, shown,
                   ", ".join("unset (=1)" if d is None else str(d)
                             for d in depths) or "no checkout step at all"))
        if not readers and deep:
            problems.append(
                "%s sets fetch-depth: 0 but runs nothing that reads history "
                "-- either a reader was removed and the full fetch is now "
                "dead weight, or the detection below has stopped seeing it.  "
                "Neither should pass silently." % wf)
    return problems, rows


def check_resolvable(read, lister, resolver):
    """(B).  Every pinned revision literal in `scripts/` must resolve to a
    commit HERE.  Meaningful only where the history is present -- which is the
    point: run it in the deep-checkout job and it is a seconds-long preflight
    for a ten-minute one."""
    problems, rows = [], []
    for rel in lister(SCRIPT_DIR, (".py", ".sh")):
        src = read(rel)
        if src is None:
            continue
        for rev in revs_in(src):
            ok, detail = resolver(rev)
            rows.append({"script": rel, "rev": rev, "resolves": ok,
                         "detail": detail})
            if not ok:
                problems.append(
                    "%s pins revision %s, which does not resolve in this "
                    "checkout (%s).  If this is CI, the checkout is shallow "
                    "and the pin is unreachable rather than wrong; if it is a "
                    "full clone, the pin has rotted." % (rel, rev, detail))
    return problems, rows


def git_resolver(cwd):
    def resolve(rev):
        proc = subprocess.run(
            ["git", "rev-parse", "--verify", "--quiet", "%s^{commit}" % rev],
            cwd=cwd, capture_output=True, text=True)
        if proc.returncode != 0:
            return False, (proc.stderr.strip() or "no such object")
        return True, proc.stdout.strip()
    return resolve


# ------------------------------------------------------------ self-test -----
# The fixture revisions are BUILT, not written down, and that is not fussiness:
# this control scans every file in `scripts/`, including itself, and a quoted
# hex literal sitting in a self-test fixture would make this file report itself
# as pinning a revision that can never resolve.  Excluding itself from the scan
# was the other way out and is the worse one -- a control with a hole shaped
# exactly like itself.
_FAKE_REV = "".join("%x" % (i % 16) for i in range(40))   # cannot exist
_READER_SRC = ('import subprocess\n'
               'PRE_WIDENING_REV = "%s"\n'
               'subprocess.run(["git", "show", f"{PRE_WIDENING_REV}:x"])\n'
               % _FAKE_REV[:8])
_PINNED_SRC = ('import subprocess\n'
               'PIN_REV = "%s"\n'
               'subprocess.run(["git", "show", PIN_REV])\n' % _FAKE_REV)
_PLAIN_SRC = 'import os\nprint(os.getcwd())\n'
# A 64-character sha256 digest, WRAPPED as two adjacent string literals the way
# a 79-column style forces.  Python concatenates them into one 64-character
# string; a per-quoted-string regex sees a 42 and a 22, and 22 is inside the
# 7-40 window.  That is the mg-ba2a defect, and the tail it exposed can never
# resolve because it was never an object.  Built, not written down, for the
# reason above the fixtures.
_FAKE_DIGEST = "".join("%x" % ((i * 7) % 16) for i in range(64))
_WRAPPED_DIGEST_SRC = ('import subprocess\n'
                       'ASSERTED_CANON_SHA = ("%s"\n'
                       '                      "%s")\n'
                       'print(ASSERTED_CANON_SHA)\n'
                       'subprocess.run(["git", "status"])\n'
                       % (_FAKE_DIGEST[:42], _FAKE_DIGEST[42:]))
# The converse fixture: a REAL 40-character revision, wrapped the same way.
# Joining must not hide it -- 20 + 20 is still 40 after the join, still inside
# the window, still a pin this control has to see.
_WRAPPED_REV_SRC = ('import subprocess\n'
                    'PIN_REV = ("%s"\n'
                    '           "%s")\n'
                    'subprocess.run(["git", "show", PIN_REV])\n'
                    % (_FAKE_REV[:20], _FAKE_REV[20:]))
_IMPORTER_SRC = ('import onethird_helper\n'
                 'print(onethird_helper)\n')

_WF_HEAD = ("name: T\non:\n  push:\njobs:\n  j:\n    runs-on: ubuntu-latest\n"
            "    steps:\n      - uses: actions/checkout@v5\n")
_WF_DEEP = _WF_HEAD + "        with:\n          fetch-depth: 0\n"


def _wf(head, script):
    return head + "      - run: python3 %s\n" % script


def _selftest():
    """Every drift must produce at least one problem, and the undrifted
    snapshot must produce none.  Cases 1-5 are (A); 6-9 are (B)."""
    ok = True

    def run(name, files, expect_problem, static_only=True, resolver=None):
        nonlocal ok
        read, lister = dict_reader(files), dict_lister(files)
        problems, _ = check_coupling(read, lister)
        if not static_only:
            p2, _ = check_resolvable(read, lister, resolver)
            problems = problems + p2
        fired = bool(problems)
        good = (fired == expect_problem)
        ok = ok and good
        print("  %-58s %s" % (name, "ok" if good else "FAILED"))
        if not good:
            print("      expected problem=%s, got: %s"
                  % (expect_problem, problems or "none"))

    base_plain = {
        ".github/workflows/a.yml": _wf(_WF_HEAD, "scripts/onethird_plain.py"),
        "scripts/onethird_plain.py": _PLAIN_SRC,
    }
    run("undrifted: no history reader, depth unset -> clean",
        base_plain, False)

    run("1. history reader, fetch-depth unset (the mg-3934 defect)",
        {".github/workflows/a.yml": _wf(_WF_HEAD, "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _READER_SRC}, True)

    run("2. history reader, fetch-depth: 1 (explicit shallow)",
        {".github/workflows/a.yml": _wf(
            _WF_HEAD + "        with:\n          fetch-depth: 1\n",
            "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _READER_SRC}, True)

    run("3. history reader, fetch-depth: 0 -> clean (the mg-3934 fix)",
        {".github/workflows/a.yml": _wf(_WF_DEEP, "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _READER_SRC}, False)

    run("4. reader reached only TRANSITIVELY, fetch-depth unset",
        {".github/workflows/a.yml": _wf(_WF_HEAD, "scripts/onethird_top.py"),
         "scripts/onethird_top.py": _IMPORTER_SRC,
         "scripts/onethird_helper.py": _READER_SRC}, True)

    run("5. fetch-depth: 0 with no reader left (dead full fetch)",
        {".github/workflows/a.yml": _wf(_WF_DEEP, "scripts/onethird_plain.py"),
         "scripts/onethird_plain.py": _PLAIN_SRC}, True)

    # (B): the resolver is stubbed, so the case is about this control's
    # plumbing rather than about git.  Git's own verdict on the real pins is
    # exercised for real by the run below the self-test.
    def stub(rev):
        return (rev != _FAKE_REV, "stub")

    run("6. a pinned revision that does not resolve",
        {".github/workflows/a.yml": _wf(_WF_DEEP, "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _PINNED_SRC},
        True, static_only=False, resolver=stub)

    run("7. the same pin, resolving -> clean",
        {".github/workflows/a.yml": _wf(_WF_DEEP, "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _PINNED_SRC},
        False, static_only=False, resolver=lambda rev: (True, "stub"))

    # 8 and 9 are the mg-ba2a pair, and they pull in opposite directions on
    # purpose.  8 is the defect that turned main red for eleven hours: a
    # wrapped sha256 digest must be ONE 64-character string, out of the window,
    # never handed to the resolver.  The resolver here fails everything, so any
    # fragment that leaks through fires.  The workflow is the SHALLOW one --
    # if the digest were (wrongly) a pin, the file would read history and (A)
    # would fire too, so this case is covered from both sides.
    def refuse(rev):
        return False, "stub refuses every literal"

    run("8. a WRAPPED sha256 digest is not a revision (the mg-ba2a defect)",
        {".github/workflows/a.yml": _wf(_WF_HEAD, "scripts/onethird_d.py"),
         "scripts/onethird_d.py": _WRAPPED_DIGEST_SRC},
        False, static_only=False, resolver=refuse)

    run("9. a WRAPPED 40-char revision is still seen (the join has no hole)",
        {".github/workflows/a.yml": _wf(_WF_DEEP, "scripts/onethird_r.py"),
         "scripts/onethird_r.py": _WRAPPED_REV_SRC},
        True, static_only=False, resolver=refuse)

    print("SELF-TEST %s" % ("PASSED" if ok else "FAILED"))
    return 0 if ok else 1


# --------------------------------------------------------------- driver -----
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--static-only", action="store_true",
                    help="property (A) only -- correct in a shallow checkout")
    ap.add_argument("--selftest", action="store_true",
                    help="the drift battery alone")
    args = ap.parse_args()

    print("=== mg-3934 self-test (the drifts this control must catch)")
    st = _selftest()
    if args.selftest:
        return st
    if st:
        print("\nthe self-test failed, so nothing below can be trusted.")
        return st

    read, lister = disk_reader(), disk_lister()
    problems, rows = check_coupling(read, lister)

    print("\n=== (A) workflows x history-reading code")
    for row in rows:
        depths = ", ".join("unset (=1)" if d is None else str(d)
                           for d in row["fetch_depths"]) or "no checkout"
        print("  %-44s fetch-depth %s" % (row["workflow"], depths))
        for rel, revs in sorted(row["history_readers"].items()):
            print("      reads history: %s  [%s]" % (rel, ", ".join(revs)))
        if not row["history_readers"]:
            print("      reads no history")

    if args.static_only:
        print("\n=== (B) skipped (--static-only): this checkout may be "
              "shallow by design")
    else:
        p2, rows2 = check_resolvable(read, lister, git_resolver(REPO))
        problems = problems + p2
        print("\n=== (B) pinned revisions in %s/ (%d literal(s) in %d file(s))"
              % (SCRIPT_DIR, len(rows2),
                 len(set(r["script"] for r in rows2))))
        for r in rows2:
            print("  %-52s %-9s %s"
                  % (r["script"], r["rev"],
                     "ok" if r["resolves"] else "UNRESOLVABLE: " + r["detail"]))

    print()
    if problems:
        print("PROBLEMS (%d):" % len(problems))
        for p in problems:
            print("  - %s" % p)
        return 1
    print("OK -- every workflow that reads history fetches it, and every "
          "pinned revision checked here resolves.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
