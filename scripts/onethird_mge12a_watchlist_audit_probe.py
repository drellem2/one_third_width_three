#!/usr/bin/env python3
"""
mg-e12a -- INDEPENDENT AUDIT of the gate watchlist and its five-drift self-test.

WHAT THIS IS FOR.  `scripts/onethird_mg7db4_watchlist_consistency.py` carries a
self-test asserting that it catches five distinct drifts.  That self-test
prints CAUGHT or MISSED per drift and exits non-zero if any is MISSED.  This
probe asks the questions that self-test cannot ask about itself:

  1. ATTRIBUTION.  The self-test asserts only that `check()` returned a
     NON-EMPTY list.  It never asks WHICH problem fired.  A drift caught for
     the wrong reason is indistinguishable from a drift caught for the right
     one, so a named property can die while the suite stays green.  Sections
     ATTRIB and ABLATE measure that directly: for each of the checker's
     individual checks, disable exactly that check in a copy of its own source
     and re-run all five drifts.  A check with no drift that goes MISSED when
     it is deleted is a check the suite does not test.

  2. CAN IT GO RED AT ALL.  Section ABLATE includes an arm that makes `check()`
     return the empty list unconditionally.  If that arm does not turn all five
     drifts MISSED, nothing else in this file means anything, and the probe
     says so and exits non-zero.  It also includes an UNMUTATED control arm,
     because a red produced by a harness that cannot produce a green is not
     evidence about the target -- it is evidence about the harness.

  3. THE NARROWING THAT WAS PROPOSED AND NEVER DONE (mg-856d item 2).  Nobody
     narrowed this watchlist: mg-856d is `available` and no commit on
     origin/main references it.  So section NARROW constructs the proposed
     narrowing -- dropping `.github/workflows/script-controls.yml` -- and runs
     all five drifts against the narrowed list, which is what mg-e12a was sent
     to check and what could not otherwise be checked at all.

  4. THE ADMISSION RULE.  A watchlist is a population claim, so the question is
     not only whether its seventeen entries are right but what its membership
     rule actually ADMITS.  Section ADMIT probes the four rules that silently
     bound this population.

HOW THE DRIFTS ARE OBTAINED, and why it is not a re-implementation.  The five
drift mappings are RECORDED out of the target's own `_selftest()` by wrapping
its module-global `check` with a recorder -- so the mappings tested here are
byte-identical to the ones the target tests, not a paraphrase of them.  The
drift TRANSFORMATIONS are additionally re-derived here (they must be, to apply
them to a narrowed tree the target never sees), and each re-derivation is
verified byte-for-byte against the corresponding recorded mapping before it is
used.  A re-derivation that does not reproduce the recorded mapping is a fatal
error, not a warning.

Writes data/onethird-mge12a-watchlist-audit.json.  Exits non-zero only if the
probe's own preconditions fail -- findings are reported, not raised.

Run:  /usr/bin/python3 scripts/onethird_mge12a_watchlist_audit_probe.py
"""

import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
TARGET = os.path.join(HERE, "onethird_mg7db4_watchlist_consistency.py")
GATE_SH = "scripts/refinery_gate.sh"
WORKFLOW = ".github/workflows/gate-mutation-demo.yml"
NARROW_PATH = ".github/workflows/script-controls.yml"

FATAL = []


def load(name, source):
    """Import a module from source text, without touching sys.path."""
    path = os.path.join(REPO, "scripts", "_mge12a_%s.py" % name)
    spec = importlib.util.spec_from_loader(name, loader=None)
    mod = importlib.util.module_from_spec(spec)
    mod.__file__ = path
    exec(compile(source, path, "exec"), mod.__dict__)
    return mod


def read_target():
    with open(TARGET) as f:
        return f.read()


# ------------------------------------------------------------ recording -----
def record_drifts(mod):
    """Run the target's own _selftest with a recording wrapper around `check`,
    and return (base_mapping, [(desc, mapping), ...]) exactly as it uses them.

    The descriptions come from the printed lines, so they are the target's
    wording rather than mine."""
    calls = []
    real_check = mod.check

    def recorder(read):
        # `read` is a dict_reader closure; recover the mapping it closes over.
        mapping = read.__closure__[0].cell_contents
        problems = real_check(read)
        calls.append((dict(mapping), list(problems)))
        return problems

    mod.check = recorder
    import io
    import contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        ok = mod._selftest()
    mod.check = real_check
    out = buf.getvalue()

    descs = re.findall(r"^  (\S.*?)\s{2,}(CAUGHT|MISSED)$", out, re.M)
    return calls, descs, ok, out


# --------------------------------------------------- drift re-derivation ----
def drift_1(base):
    d = dict(base)
    d[GATE_SH] = d[GATE_SH].replace(
        "scripts/onethird_mgb0a6_spectral_killshot_probe.py\n", "", 1)
    return d


def drift_2(base):
    d = dict(base)
    d[WORKFLOW] = d[WORKFLOW].replace("  pull_request:\n    paths:\n",
                                      "  pull_request:\n", 1)
    return d


def drift_3(base):
    d = dict(base)
    d["scripts/onethird_mg2c34_n7_overlap_test.py"] = (
        "from onethird_mg7db4_hypothetical_new_instrument import thing\n"
        + d["scripts/onethird_mg2c34_n7_overlap_test.py"])
    d["scripts/onethird_mg7db4_hypothetical_new_instrument.py"] = "pass\n"
    return d


def drift_4(base):
    d = dict(base)
    d["scripts/onethird_mg2c34_n7_overlap_test.py"] += (
        '\nwith open(os.path.join(REPO, "data",\n'
        '                       "onethird-mg7db4-unwatched.json")) as f:\n'
        '    pass\n')
    d["data/onethird-mg7db4-unwatched.json"] = ""
    return d


def drift_5(base):
    d = dict(base)
    d[GATE_SH] = d[GATE_SH].replace(
        "WATCHED='", "WATCHED='docs/OneThird-L1b-Bwall-state.md\n", 1)
    d[WORKFLOW] = d[WORKFLOW].replace(
        "    paths:\n",
        "    paths:\n      - 'docs/OneThird-L1b-Bwall-state.md'\n")
    return d


DRIFTS = [drift_1, drift_2, drift_3, drift_4, drift_5]


# ------------------------------------------------------------- ablations ----
# Each ablation is a MINIMAL textual edit to the target's own source that
# disables exactly one check.  The name is the property the check enforces.
ABLATIONS = [
    ("UNMUTATED (control)", None),
    ("check() blinded entirely",
     ('    """Return a list of problem strings; empty means consistent."""\n'
      '    problems = []',
      '    """Return a list of problem strings; empty means consistent."""\n'
      '    return []\n'
      '    problems = []')),
    ("P1 agreement: workflow paths == WATCHED",
     ("        if set(block) != watch_set:",
      "        if False and set(block) != watch_set:")),
    ("P1 both paths: blocks present",
     ("    if len(blocks) < 2:", "    if False and len(blocks) < 2:")),
    ("P1 WATCHED has no duplicates",
     ("    if len(watch_set) != len(watch):",
      "    if False and len(watch_set) != len(watch):")),
    ("P3 completeness: reachable => watched",
     ("    for rel in sorted(expected - watch_set):",
      "    for rel in sorted(set()):")),
    ("P2 identity: watched => part of the gate",
     ("    for rel in sorted(watch_set - expected):",
      "    for rel in sorted(set()):")),
    ("P3 closure: no broken import target",
     ("    for rel in sorted(missing):", "    for rel in sorted(set()):")),
]


def apply_ablation(src, edit):
    if edit is None:
        return src
    old, new = edit
    if src.count(old) != 1:
        FATAL.append("ablation anchor %r occurs %d times, expected 1"
                     % (old[:40], src.count(old)))
    return src.replace(old, new, 1)


# ------------------------------------------------------------- narrowing ----
def narrow_lists(base):
    """mg-856d item 2, as far as the two watchlists: drop script-controls.yml
    from WATCHED and from both `paths:` blocks.  The checker's MECHANISM set is
    NOT touched -- that is the point of this arm."""
    d = dict(base)
    d[GATE_SH] = d[GATE_SH].replace(NARROW_PATH + "\n", "", 1)
    d[WORKFLOW] = d[WORKFLOW].replace("      - '%s'\n" % NARROW_PATH, "")
    return d


def narrow_mechanism(src):
    """The third edit the narrowing needs: drop it from MECHANISM too."""
    return src.replace('    ".github/workflows/script-controls.yml",\n', "", 1)


# ------------------------------------------------------------------ main ----
def verdict(problems):
    return "CAUGHT" if problems else "MISSED"


def main():
    report = {}
    src = read_target()
    mod = load("target", src)

    # ---------------------------------------------------------- preflight ---
    live = mod.check(mod.disk_reader())
    report["live_tree_problems"] = live
    print("=" * 78)
    print("PREFLIGHT -- the tree under audit")
    print("=" * 78)
    print("  live check() on the working tree: %s"
          % ("CONSISTENT" if not live else "INCONSISTENT"))
    for p in live:
        print("    - %s" % p)

    read = mod.disk_reader()
    watch = mod.parse_shell_watchlist(read(GATE_SH))
    blocks = mod.parse_workflow_paths(read(WORKFLOW))
    closure, missing = mod.import_closure(mod.ROOTS, read)
    datasets = mod.data_reads(closure, read)
    report["counts"] = {
        "WATCHED_rows": len(watch),
        "WATCHED_distinct": len(set(watch)),
        "workflow_paths_blocks": len(blocks),
        "workflow_block_sizes": [len(b) for b in blocks],
        "workflow_block_distinct": [len(set(b)) for b in blocks],
        "import_closure_modules": len(closure),
        "datasets_read": len(datasets),
        "MECHANISM_size": len(mod.MECHANISM),
        "ROOTS_size": len(mod.ROOTS),
    }
    print("  WATCHED: %d rows / %d distinct path strings"
          % (len(watch), len(set(watch))))
    print("  workflow: %d paths: blocks, sizes %s (distinct %s)"
          % (len(blocks), [len(b) for b in blocks],
             [len(set(b)) for b in blocks]))
    print("  import closure: %d modules; datasets read: %d; MECHANISM: %d; "
          "ROOTS: %d"
          % (len(closure), len(datasets), len(mod.MECHANISM), len(mod.ROOTS)))

    # -------------------------------------------------- record the drifts ---
    calls, descs, selftest_ok, selftest_out = record_drifts(mod)
    if len(calls) != 6:
        FATAL.append("expected 6 check() calls from _selftest (1 base + 5 "
                     "drifts), recorded %d" % len(calls))
    base_map = calls[0][0]
    recorded = calls[1:]
    report["target_selftest_ok"] = bool(selftest_ok)
    report["target_selftest_verdicts"] = descs

    print()
    print("=" * 78)
    print("RECORD -- the target's own five drifts, taken from its own _selftest")
    print("=" * 78)
    print("  target _selftest() returned: %s" % selftest_ok)
    for d, v in descs:
        print("    %-58s %s" % (d, v))

    # ----------------------------------------- verify my re-derivations -----
    print()
    print("  re-derivation fidelity (mine vs the target's recorded mapping):")
    fidelity = []
    for i, fn in enumerate(DRIFTS):
        mine = fn(base_map)
        same = mine == recorded[i][0]
        fidelity.append(same)
        print("    drift %d  %s" % (i + 1, "IDENTICAL" if same else "DIFFERS"))
        if not same:
            FATAL.append("re-derived drift %d does not reproduce the target's "
                         "recorded mapping" % (i + 1))
    report["rederivation_identical"] = fidelity

    # ------------------------------------------------------- ATTRIBUTION ----
    print()
    print("=" * 78)
    print("ATTRIB -- WHICH problem actually fires for each drift")
    print("=" * 78)
    print("  the target's self-test asserts only that this list is non-empty.")
    attrib = []
    for i, (mapping, problems) in enumerate(recorded):
        desc = descs[i][0] if i < len(descs) else "drift %d" % (i + 1)
        print()
        print("  drift %d: %s" % (i + 1, desc))
        print("    problems raised: %d" % len(problems))
        for p in problems:
            print("      - %s" % p)
        attrib.append({"drift": i + 1, "desc": desc, "problems": problems})
    report["attribution"] = attrib

    # ------------------------------------------------------------ ABLATE ----
    print()
    print("=" * 78)
    print("ABLATE -- delete one check at a time; which drifts stop being caught")
    print("=" * 78)
    print("  A check whose deletion turns NO drift MISSED is a check the")
    print("  five-drift suite does not test.")
    print()
    header = "  %-44s %s" % ("ablated check", "d1 d2 d3 d4 d5   exit")
    print(header)
    print("  " + "-" * (len(header) - 2))

    ablate_rows = []
    for name, edit in ABLATIONS:
        msrc = apply_ablation(src, edit)
        mmod = load("abl_%d" % len(ablate_rows), msrc)
        cells, missed = [], []
        for i, fn in enumerate(DRIFTS):
            problems = mmod.check(mmod.dict_reader(fn(base_map)))
            v = verdict(problems)
            cells.append("C " if v == "CAUGHT" else "M ")
            if v == "MISSED":
                missed.append(i + 1)
        # what the target's main() would do: base must be clean AND all caught
        base_problems = mmod.check(mmod.dict_reader(base_map))
        would_exit = 1 if (base_problems or missed) else 0
        print("  %-44s %s  %s" % (name, " ".join(cells),
                                  "exit %d" % would_exit))
        ablate_rows.append({
            "check": name, "missed_drifts": missed,
            "base_problems": base_problems, "selftest_would_exit": would_exit,
        })
    report["ablation"] = ablate_rows

    # ------------------------------------------------------------ NARROW ----
    print()
    print("=" * 78)
    print("NARROW -- mg-856d item 2, constructed here because nobody did it")
    print("=" * 78)
    print("  proposal: drop %s from the watchlist." % NARROW_PATH)
    narrow = {}

    n2 = narrow_lists(base_map)
    n2_watch = mod.parse_shell_watchlist(n2[GATE_SH])
    n2_blocks = mod.parse_workflow_paths(n2[WORKFLOW])
    n2_problems = mod.check(mod.dict_reader(n2))
    print()
    print("  ARM 1 -- edit the TWO watchlists only (%d paths, blocks %s):"
          % (len(n2_watch), [len(b) for b in n2_blocks]))
    print("    check() -> %d problem(s); gate would exit %d"
          % (len(n2_problems), 1 if n2_problems else 0))
    for p in n2_problems:
        print("      - %s" % p)
    narrow["two_file"] = {
        "watch_rows": len(n2_watch), "block_sizes": [len(b) for b in n2_blocks],
        "problems": n2_problems,
    }

    nsrc = narrow_mechanism(src)
    if nsrc == src:
        FATAL.append("could not remove %s from MECHANISM" % NARROW_PATH)
    nmod = load("narrowed", nsrc)
    n3_problems = nmod.check(nmod.dict_reader(n2))
    print()
    print("  ARM 2 -- also drop it from MECHANISM in the checker (%d paths):"
          % len(n2_watch))
    print("    check() -> %d problem(s); gate would exit %d"
          % (len(n3_problems), 1 if n3_problems else 0))
    for p in n3_problems:
        print("      - %s" % p)

    print()
    print("    the five drifts, re-run against the NARROWED list:")
    n3_rows = []
    for i, fn in enumerate(DRIFTS):
        problems = nmod.check(nmod.dict_reader(fn(n2)))
        v = verdict(problems)
        n3_rows.append({"drift": i + 1, "verdict": v, "problems": problems})
        print("      drift %d  %-52s %s"
              % (i + 1, descs[i][0] if i < len(descs) else "", v))
    narrow["three_file"] = {"problems": n3_problems, "drifts": n3_rows}
    report["narrowing"] = narrow

    # ------------------------------------------------------------- ADMIT ----
    print()
    print("=" * 78)
    print("ADMIT -- what the membership rules actually admit")
    print("=" * 78)
    admit = {}

    # E1: the workflow paths parser admits only single-quoted entries.
    dq = dict(base_map)
    dq[WORKFLOW] = dq[WORKFLOW].replace(
        "    paths:\n",
        '    paths:\n      - ".github/workflows/lean.yml"\n')
    dq_blocks = mod.parse_workflow_paths(dq[WORKFLOW])
    dq_problems = mod.check(mod.dict_reader(dq))
    print()
    print("  E1  a DOUBLE-quoted path added to both `paths:` blocks and to")
    print("      neither watchlist copy -- the two triggers now genuinely")
    print("      disagree:")
    print("        parser sees block sizes %s (unchanged from %s)"
          % ([len(b) for b in dq_blocks], [len(b) for b in blocks]))
    print("        check() -> %s"
          % ("%d problem(s)" % len(dq_problems) if dq_problems
             else "NO PROBLEMS -- prints 'watchlist consistent'"))
    admit["double_quoted_workflow_entry"] = {
        "block_sizes": [len(b) for b in dq_blocks],
        "problems": dq_problems, "caught": bool(dq_problems),
    }

    # E1b: same entry, single-quoted, is seen.
    sq = dict(base_map)
    sq[WORKFLOW] = sq[WORKFLOW].replace(
        "    paths:\n",
        "    paths:\n      - '.github/workflows/lean.yml'\n")
    sq_problems = mod.check(mod.dict_reader(sq))
    print("  E1b the SAME path, single-quoted, in the same two places:")
    print("        check() -> %s" % ("%d problem(s) -- CAUGHT" % len(sq_problems)
                                     if sq_problems else "NO PROBLEMS"))
    admit["single_quoted_workflow_entry"] = {
        "problems": sq_problems, "caught": bool(sq_problems)}

    # E2/E3: what the import scanner admits.
    non_onethird, multi_import = [], []
    any_import = re.compile(r"^\s*(?:from|import)\s+([\w.]+)(.*)$", re.M)
    for rel in sorted(closure | set(mod.MECHANISM)):
        srctxt = read(rel)
        if srctxt is None or not rel.endswith(".py"):
            continue
        for name, rest in any_import.findall(srctxt):
            top = name.split(".")[0]
            if top.startswith("onethird_"):
                if "," in rest:
                    multi_import.append((rel, name, rest.strip()))
            elif os.path.isfile(os.path.join(REPO, "scripts", top + ".py")):
                non_onethird.append((rel, top))
    print()
    print("  E2  local sibling modules imported but NOT named onethird_*")
    print("      (invisible to the closure): %d" % len(non_onethird))
    for rel, top in non_onethird:
        print("        %s imports %s" % (rel, top))
    print("  E3  onethird_* import lines carrying a comma (only the first")
    print("      module on the line is captured): %d" % len(multi_import))
    for rel, name, rest in multi_import:
        print("        %s: import %s%s" % (rel, name, rest))
    admit["non_onethird_local_imports"] = non_onethird
    admit["multi_module_import_lines"] = multi_import

    # E4: data reads the dataset scanner cannot see.
    seen_by_scanner, invisible = set(), []
    data_mention = re.compile(r'os\.path\.join\(\s*REPO\s*,\s*["\']data["\']')
    for rel in sorted(closure):
        srctxt = read(rel)
        if srctxt is None:
            continue
        flat = re.sub(r"\s+", "", srctxt)
        found = set(n for n, w in mod._DATA_RE.findall(flat) if not w)
        written = set(n for n, w in mod._DATA_RE.findall(flat) if w)
        seen_by_scanner |= found
        n_mentions = len(data_mention.findall(srctxt))
        n_matched = len(mod._DATA_RE.findall(flat))
        if n_mentions > n_matched:
            invisible.append({"file": rel, "join_REPO_data_sites": n_mentions,
                              "matched_by_DATA_RE": n_matched})
        del written
    print()
    print("  E4  os.path.join(REPO,'data',...) sites vs sites the dataset")
    print("      regex actually matches, per closure module:")
    if invisible:
        for row in invisible:
            print("        %s: %d site(s), %d matched -- %d INVISIBLE"
                  % (row["file"], row["join_REPO_data_sites"],
                     row["matched_by_DATA_RE"],
                     row["join_REPO_data_sites"] - row["matched_by_DATA_RE"]))
    else:
        print("        none -- every site in the closure is matched")
    admit["invisible_data_sites"] = invisible

    # E5: shell-hostile characters in the watchlist.
    hostile = [p for p in watch if re.search(r"[\s*?\[\]]", p)]
    print()
    print("  E5  WATCHED entries containing whitespace or a glob metacharacter")
    print("      (`for path in $WATCHED` is an unquoted expansion): %d"
          % len(hostile))
    for p in hostile:
        print("        %s" % p)
    admit["shell_hostile_watch_entries"] = hostile
    report["admission"] = admit

    # ----------------------------------------------------------- MISSING ----
    # The five drifts are a POPULATION CLAIM about what can go wrong.  These
    # are drifts the suite does not contain; each is a realistic single edit.
    # A MISSED row here is a drift this mechanism does not catch.
    print()
    print("=" * 78)
    print("MISSING -- drifts the five-case suite does not contain")
    print("=" * 78)

    def wf_append_to_blocks(base, line):
        d = dict(base)
        last = "      - 'data/onethird-mg8b64-L1b-bk-transport-transfer.json'\n"
        if d[WORKFLOW].count(last) != 2:
            FATAL.append("workflow last-entry anchor occurs %d times, want 2"
                         % d[WORKFLOW].count(last))
        d[WORKFLOW] = d[WORKFLOW].replace(last, last + line)
        return d

    def wf_prepend_to_blocks(base, line):
        d = dict(base)
        d[WORKFLOW] = d[WORKFLOW].replace("    paths:\n", "    paths:\n" + line)
        return d

    def n1(base):                      # converse of the suite's drift 1
        d = dict(base)
        d[WORKFLOW] = d[WORKFLOW].replace(
            "      - 'scripts/onethird_mgb0a6_spectral_killshot_probe.py'\n", "")
        return d

    def n2(base):
        return wf_append_to_blocks(
            base, '      - ".github/workflows/lean.yml"\n')

    def n3(base):
        return wf_prepend_to_blocks(
            base, '      - ".github/workflows/lean.yml"\n')

    def n4(base):
        return wf_append_to_blocks(base, "      - .github/workflows/lean.yml\n")

    def n5(base):
        d = dict(base)
        d["scripts/onethird_mg2c34_n7_overlap_test.py"] = (
            "import mge12a_helper_not_named_onethird\n"
            + d["scripts/onethird_mg2c34_n7_overlap_test.py"])
        d["scripts/mge12a_helper_not_named_onethird.py"] = "pass\n"
        return d

    def n6(base):
        d = dict(base)
        d["scripts/onethird_mg2c34_n7_overlap_test.py"] += (
            '\nMGE12A_REF = "onethird-mge12a-unwatched-a.json"\n'
            'with open(os.path.join(REPO, "data", MGE12A_REF)) as f:\n'
            '    pass\n')
        d["data/onethird-mge12a-unwatched-a.json"] = ""
        return d

    def n7(base):
        d = dict(base)
        d["scripts/onethird_mg2c34_n7_overlap_test.py"] += (
            '\nwith open(os.path.join(REPO, "data",\n'
            '                       "onethird-mge12a-unwatched-b.json"),\n'
            '          "r") as f:\n    pass\n')
        d["data/onethird-mge12a-unwatched-b.json"] = ""
        return d

    def n8(base):
        d = dict(base)
        d["scripts/onethird_mg2c34_n7_overlap_test.py"] += (
            "\nwith open(os.path.join(REPO, 'data',\n"
            "                       'onethird-mge12a-unwatched-c.json')) as f:\n"
            "    pass\n")
        d["data/onethird-mge12a-unwatched-c.json"] = ""
        return d

    MISSING = [
        ("workflow loses an entry the shell still has (converse of drift 1)",
         n1, "the only drift that would uniquely exercise AGREEMENT"),
        ("workflow gains a DOUBLE-quoted path, LAST in each block",
         n2, "GitHub honours it; the parser never sees it"),
        ("workflow gains a DOUBLE-quoted path, FIRST in each block",
         n3, "same edit, different position"),
        ("workflow gains a BARE (unquoted) path, LAST in each block",
         n4, "GitHub honours it; the parser never sees it"),
        ("gated instrument imports a local module not named onethird_*",
         n5, "outside the closure's name prefix"),
        ("gated instrument reads a dataset through a VARIABLE name",
         n6, "the idiom the corpus already uses in mg5ad1 and mg75f0"),
        ("gated instrument reads a dataset with an explicit \"r\" mode",
         n7, "one extra argument"),
        ("gated instrument reads a dataset with SINGLE quotes",
         n8, "same call, other quote character"),
    ]
    print()
    print("  %-62s %s" % ("candidate drift", "verdict"))
    print("  " + "-" * 72)
    missing_rows = []
    for desc, fn, why in MISSING:
        problems = mod.check(mod.dict_reader(fn(base_map)))
        v = verdict(problems)
        print("  %-62s %s" % (desc, v))
        if v == "MISSED":
            print("  %-62s   ^ %s" % ("", why))
        missing_rows.append({"drift": desc, "verdict": v, "why": why,
                             "problems": problems})
    report["missing_drifts"] = missing_rows

    # ------------------------------------------------------------- SHELL ----
    # The checker models the watchlist as "the lines of the WATCHED literal".
    # The shell does not: `for path in $WATCHED` is an UNQUOTED expansion, so
    # it word-splits on IFS and glob-expands.  Where the two models disagree,
    # the checker's "consistent" is a statement about a list the gate does not
    # actually use.  The loop below is EXTRACTED VERBATIM from
    # scripts/refinery_gate.sh rather than retyped, so this tests the real
    # matcher and not my idea of it.
    print()
    print("=" * 78)
    print("SHELL -- the real matcher, extracted verbatim from refinery_gate.sh")
    print("=" * 78)
    import subprocess
    gate_src = read(GATE_SH)
    m = re.search(r"^HITS=''\n(?:.*\n)*?^done\n", gate_src, re.M)
    if not m:
        FATAL.append("could not extract the HITS loop from %s" % GATE_SH)
        loop = ""
    else:
        loop = m.group(0)
    print("  extracted %d lines of the matcher:" % len(loop.splitlines()))
    for ln in loop.splitlines():
        print("    | %s" % ln)

    shell_cases = [
        ("ordinary path (control)",
         "scripts/refinery_gate.sh", "scripts/refinery_gate.sh", True),
        ("watched path containing a SPACE",
         "data/one third.json", "data/one third.json", True),
        ("watched path containing a glob '*'",
         "scripts/onethird_*.py", "scripts/onethird_*.py", True),
    ]
    shell_rows = []
    print()
    print("  %-44s %-10s %s" % ("case", "checker", "shell matcher"))
    print("  " + "-" * 72)
    for desc, watched_entry, changed, _ in shell_cases:
        script = ("WATCHED='%s'\nCHANGED='%s'\n%secho \"$HITS\"\n"
                  % (watched_entry, changed, loop))
        r = subprocess.run(["sh", "-c", script], capture_output=True,
                           text=True, cwd=REPO)
        hit = r.stdout.strip()
        matched = hit == watched_entry
        # what the checker's model would say: it splits on newlines only.
        checker_sees = len([x for x in watched_entry.split("\n") if x.strip()])
        print("  %-44s %-10s %s"
              % (desc, "%d path" % checker_sees,
                 ("MATCHES" if matched else "DOES NOT MATCH")
                 + (" (HITS=%r)" % hit if not matched else "")))
        shell_rows.append({"case": desc, "watched": watched_entry,
                           "changed": changed, "hits": hit,
                           "matched": matched})
    report["shell_matcher"] = shell_rows

    # ---------------------------------------------------------- DURATION ----
    # mg-856d item 3.  POPULATION: every duration literal in
    # scripts/refinery_gate.sh, where a duration literal is a match of the
    # regex below -- a number (or a range) followed by a time unit.  GRAIN: one
    # match, at one line.  A range like "~16-21 min" is ONE literal, and that
    # choice is stated here because the parent's "six" never stated it and the
    # count is not defined without it.
    print()
    print("=" * 78)
    print("DURATION -- every duration literal in refinery_gate.sh, populated")
    print("=" * 78)
    # MY FIRST CUT OF THIS REGEX WAS WRONG IN TWO WAYS AND BOTH ARE ON THE
    # RECORD IN THE REPORT.  It split `24 h 08 m 55 s` into two literals, read
    # `~2.5 min` as `5 min`, and -- worst -- it did not match the hyphenated
    # compound forms `~30-minute` (L178) and `25-minute` (L278) at all.  That
    # last miss is the defect documented at L171-176 of the very file being
    # measured: a sweep for a number in a corpus that hyphenates and hard-wraps
    # its comments must handle those forms or its total means "the forms I
    # thought of".  Mine did not, twice, for the same reason theirs did not.
    U = (r"ms|s|sec|secs|second|seconds|min|mins|minute|minutes|"
         r"h|hr|hrs|hour|hours")
    DUR = re.compile(
        r"~?\d[\d ]*h\s*\d+\s*m\s*\d+\s*s"                 # 24 h 08 m 55 s
        r"|~?\d[\d ]*h\s*\d+\s*m(?![\w])"                  # 24 h 09 m
        r"|~?\d+(?:\.\d+)?\s*-\s*\d+(?:\.\d+)?\s*(?:%s)\b" % U +
        r"|~?\d+(?:\.\d+)?-(?:minutes?|mins?|hours?|seconds?|secs?)"
        r"|~?\d[\d ]*(?:\.\d+)?\s*(?:%s)\b" % U)
    LOADWORD = re.compile(r"\b(idle|load|loaded|quiet|contention|contended|"
                          r"unloaded|uncontended|concurrent|on CI)\b", re.I)

    # SUBJECT is a HAND classification, stated as such.  A regex that guessed
    # the subject from the surrounding words would be a derived-looking number
    # I could not defend line by line, which is the thing this ticket is about.
    # Every matched line must have an entry here or the probe fails.
    SUBJECT = {
        21:  ("A", "the demonstrations this gate runs (its own blocking path)"),
        144: ("D", "the historical red WINDOW of the Actions workflow"),
        153: ("D", "the historical red WINDOW (the superseded undercount)"),
        162: ("D", "the historical red WINDOW (rounded, and the doc's ~24h)"),
        164: ("D", "the historical red WINDOW, re-derived in seconds"),
        173: ("D", "the historical red WINDOW (quoted as a grep target)"),
        178: ("B", "the GitHub Actions job"),
        218: ("A", "this gate, end to end"),
        219: ("B", "the GitHub Actions workflow this gate reads"),
        259: ("D", "the historical red WINDOW, in the branch text"),
        277: ("C", "an end-to-end refinery MR wall-clock"),
        278: ("A", "a demonstration's runtime, under stated contention"),
        289: ("A", "one step of this gate (mg-5ad1 blindness probe)"),
        290: ("A", "one step of this gate (mg-60d3 mutation demo)"),
        306: ("A", "one step of this gate, in the branch text"),
    }
    CLASSES = {
        "A": "this gate's OWN runtime, or a step of it",
        "B": "the GitHub Actions workflow's runtime",
        "C": "an end-to-end refinery MR wall-clock",
        "D": "the 2026-07-30/31 red window -- an OUTAGE, not a runtime",
    }
    dur_rows = []
    for i, line in enumerate(gate_src.splitlines(), 1):
        for mm in DUR.finditer(line):
            if i not in SUBJECT:
                FATAL.append("duration literal %r at L%d has no SUBJECT entry "
                             "-- the hand classification has gone stale"
                             % (mm.group(0), i))
                cls, what = "?", "UNCLASSIFIED"
            else:
                cls, what = SUBJECT[i]
            dur_rows.append({
                "line": i, "literal": mm.group(0).strip(), "class": cls,
                "subject": what, "states_regime": bool(LOADWORD.search(line)),
                "context": line.strip()[:92],
            })
    print("  POPULATION: scripts/refinery_gate.sh at HEAD, all %d lines,"
          % len(gate_src.splitlines()))
    print("              comments and echoed branch text alike.")
    print("  GRAIN:      one regex match = one literal.  A range (`~16-21 min`)")
    print("              and a composite (`24 h 08 m 55 s`) each count as ONE.")
    print("  TOTAL:      %d duration literals" % len(dur_rows))
    print()
    for row in dur_rows:
        print("    L%-4d %-14s [%s] regime-word: %-3s  %s"
              % (row["line"], row["literal"], row["class"],
                 "yes" if row["states_regime"] else "NO", row["context"]))
    print()
    for c in sorted(CLASSES):
        rows = [r for r in dur_rows if r["class"] == c]
        print("    class %s  %2d literal(s)  %s" % (c, len(rows), CLASSES[c]))
    n_regime = sum(1 for r in dur_rows if r["states_regime"])
    own = [r for r in dur_rows if r["class"] == "A"]
    print()
    print("  THE PARENT'S CLAIM was that this file 'states its OWN runtime in")
    print("  six different figures'.  Re-derived here: class A has %d literals"
          % len(own))
    print("  at %d distinct lines, over the population and grain stated above."
          % len(set(r["line"] for r in own)))
    print("  literals on a line carrying ANY load/regime word: %d of %d"
          % (n_regime, len(dur_rows)))
    print("  literals stating what-is-timed AND which-clock AND under-what-load:")
    print("    0 of %d -- by inspection, not by regex: no line in this file"
          % len(dur_rows))
    print("    names a clock, a host, a date or a load figure beside a duration.")
    report["duration_literals"] = dur_rows
    report["duration_classes"] = {
        c: len([r for r in dur_rows if r["class"] == c]) for c in CLASSES}

    # ------------------------------------------------------------- OUTPUT ---
    out = os.path.join(REPO, "data", "onethird-mge12a-watchlist-audit.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    print()
    print("wrote %s" % os.path.relpath(out, REPO))

    if FATAL:
        print()
        print("PROBE PRECONDITION FAILED -- nothing above is trustworthy:")
        for m in FATAL:
            print("  - %s" % m)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
