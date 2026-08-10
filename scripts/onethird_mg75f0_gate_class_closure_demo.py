#!/usr/bin/env python3
"""
mg-75f0 -- IS THE CLASS CLOSED?  Source-level mutation demonstration.

THE CLASS, in mg-5ad1's words: *a quantity the document asserts, computed by code
the CI gate exercises, with no control that can fail.*

mg-09ea found two members (M1, M2).  mg-60d3 repaired both, and the repairs were
derived FROM those two failures -- so their sufficiency against those two is not
evidence about the class.  mg-5ad1 then found two more by one-line edits (M3, M4)
that passed the repaired gate printing "All controls and identity checks PASSED".
The residual was structural: the identity check opened the committed mg-8b64
reference row and compared FOUR of its TWENTY-TWO fields.

mg-75f0 widened the comparison to the whole row (`identity_field_comparisons`,
`IDENTITY_EXCLUDED_REF_FIELDS`) and added CONTROL E (dim U's structural bound and
properness) and CONTROL F (two-sided coverage on real data).

THIS FILE IS THE PART THAT COULD FALSIFY THAT.  Catching M3 and M4 proves only
that the widening covers the two mutations it was written after -- exactly the
mistake mg-60d3 made one level down.  So it also runs THREE mutations that
NEITHER mg-60d3 NOR mg-5ad1 used, chosen before the widened gate was run against
them, each a one-line edit landing in a field that was uncompared until mg-75f0:

  M5  bk_frozen_pair's MIN-PHI selector      min -> max   ->  min_phi_bk,
      (`onethird_mg8b64_..._probe.py`)                        min_phi_bk_pair,
                                                             minphi_phi_t_image
  M6  transport_summary's prefix selector    min -> max   ->  phi_t_min_prefix
  M7  _transport_label_cheeger's volume      min -> max   ->  phi_t_cheeger
      normalisation

M5 is the honest one to look at first: it is M3's structural twin one line down,
in the same function, and it is the test of whether the widening generalises or
merely covers its own witnesses.  M6 and M7 are on the TRANSPORT side of the
probe, not the BK side, and M7 is a normalisation rather than a selector -- so
between them they are not all one shape.

AND ONE MUTATION THIS AUTHOR DID NOT CHOOSE, which is stronger than all three.

  M8  bk_pair_cut's Bernoulli variance      p(1-p) -> p   ->  frozen_ratio, ...

M5/M6/M7 share a weakness that has to be said out loud: the person who wrote the
widening also picked them, and an author picks around the cases their own fix
misses without meaning to.  M8 is mg-7db4's, row N1 of
`scripts/onethird_mg7db4_probe_mutation_battery.py`, written for a different
purpose, independently, and before its author had seen this widening.  It is the
only row in this table selected by nobody who built the thing under test.

ROUTE, and it is deliberately not the mg-60d3 demo's route.  mg-60d3
reconstructs the pre-repair gate IN PROCESS and applies mutations by
monkeypatching every loaded module.  This file instead does what mg-5ad1's audit
did: for each case it builds an ISOLATED TREE holding a copy of `scripts/` plus
the two datasets the gate reads, applies ONE source-level edit there with an
anchor-count assertion so a silent no-match is impossible, and runs the gate in
that tree.  The PRE-WIDENING gate is likewise the real thing -- the gate source
as mg-60d3 merged it (`af7fc2df`, the exact source mg-5ad1 measured M3 and M4
against), extracted with `git show` -- not a reconstruction.

WHAT IS ASSERTED (this file is itself a control and exits non-zero if it fails):

                            pre-widening gate      widened gate
      unmutated                  exit 0               exit 0    (no false positive)
      M3  frozen-pair selector   exit 0 <- mg-5ad1    exit 1
      M4  projector rank filter  exit 0 <- mg-5ad1    exit 1
      M5  min-phi selector       exit 0 <- UNSEEN     exit 1
      M6  prefix selector        exit 0 <- UNSEEN     exit 1
      M7  cheeger normalisation  exit 0 <- UNSEEN     exit 1
      M8  Bernoulli variance     exit 0 <- mg-7db4's   exit 1

The left column is the part that makes the right column mean anything: each
mutation is shown to have been INVISIBLE before, so "exit 1" is the widening
firing and not a pre-existing control doing its job.

Run:  /usr/bin/python3 scripts/onethird_mg75f0_gate_class_closure_demo.py
      (numpy required; ~35 min -- fourteen full runs of the CI gate)
      --only M3,M5      run a subset
      --gates widened   run one gate column only

Writes `data/onethird-mg75f0-gate-class-closure.json`.
"""

import os
import re
import sys
import json
import shutil
import argparse
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GATE = os.path.join("scripts", "onethird_mg2c34_n7_overlap_test.py")

# The two datasets the gate opens: the mg-8b64 reference row block (the identity
# check) and, on a full run, its own output.  --no-sweep never writes.
DATASETS = ["onethird-mg8b64-L1b-bk-transport-transfer.json"]

# --------------------------------------------------------------- mutations ---
# Each is ONE source-level edit: (file, exact anchor, replacement, count).
# `count` is asserted, so a refactor that moves the anchor fails loudly here
# instead of silently producing an unmutated "mutated" run.
MUTATIONS = {
    "M3": {
        "desc": "Theorem-E frozen-pair selector min -> max (mg-5ad1 M3): "
                "moves frozen_pair at 5/5 posets and frozen_pair_overlap_with_U "
                "to exactly 1.0000, the quantity ledger claim 8 rests on",
        "seen_by": "mg-5ad1 (audit finding 1, primary witness)",
        "fields": ["frozen_pair", "frozen_ratio", "frozen_phi_bk", "frozen_p",
                   "frozen_phi_t_image", "frozen_sep_k"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": '    frozen = min((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "new": '    frozen = max((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "count": 1,
    },
    "M4": {
        "desc": "projector_U's rank filter s > max(tol,1e-10) -> s > 0.0 "
                "(mg-5ad1 M4): numerically-null singular directions enter U, "
                "dim U inflates 24/22/20/7/9 -> 49/49/49/21/25, and at #945 "
                "and #809 U becomes the WHOLE space so c = null = 1.0000",
        "seen_by": "mg-5ad1 (audit finding 1, corroborating witness)",
        "fields": ["-- none: no mg-8b64 field moves; this is CONTROL E's case"],
        "file": "scripts/onethird_mg4a86_sdquant_overlap.py",
        "old": "    Q = Uu[:, s > max(tol, 1e-10)]",
        "new": "    Q = Uu[:, s > 0.0]",
        "count": 1,
    },
    "M5": {
        "desc": "bk_frozen_pair's MIN-PHI selector min -> max: the literally "
                "lowest BK pair-cut conductance becomes the highest.  M3's "
                "structural twin, one line down, in a field uncompared until "
                "mg-75f0",
        "seen_by": "UNSEEN -- used by neither mg-60d3 nor mg-5ad1",
        "fields": ["min_phi_bk", "min_phi_bk_pair", "minphi_phi_t_image"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": '    minphi = min((pc for pc in pairs if pc["phi"] is not None),\n'
               '                 key=lambda pc: pc["phi"], default=None)',
        "new": '    minphi = max((pc for pc in pairs if pc["phi"] is not None),\n'
               '                 key=lambda pc: pc["phi"], default=None)',
        "count": 1,
    },
    "M6": {
        "desc": "transport_summary's expected-rank PREFIX selector min -> max: "
                "phi_t_min_prefix reports the WORST transport prefix cut "
                "instead of the best, i.e. the transport Cheeger surrogate the "
                "programme's Cheeger step feeds on",
        "seen_by": "UNSEEN -- used by neither mg-60d3 nor mg-5ad1",
        "fields": ["phi_t_min_prefix"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": '    phi_t_min_prefix = min((pk["Phi_T"] for pk in prefix), '
               'default=float("nan"))',
        "new": '    phi_t_min_prefix = max((pk["Phi_T"] for pk in prefix), '
               'default=float("nan"))',
        "count": 1,
    },
    "M8": {
        # The strongest row in this table, and it is not mine.  M5/M6/M7 were
        # chosen by the same author who wrote the widening, which bounds how
        # much they can say -- an author avoids the mutations their own fix
        # misses, without meaning to.  M8 was authored by mg-7db4, for its own
        # probe battery (row N1), independently and before it had seen the
        # widened gate.  So it is the one mutation here that nobody who built
        # the thing under test selected.
        "desc": "Bernoulli variance p(1-p) -> p in bk_pair_cut, so Theorem E's "
                "ratio E(f_xy)/Var(f_xy) is divided by the wrong variance.  "
                "AUTHORED BY mg-7db4 as its battery's row N1, independently of "
                "this widening and of the author of it",
        "seen_by": "UNSEEN by mg-60d3/mg-5ad1; and NOT CHOSEN BY THIS AUTHOR "
                   "-- mg-7db4's row N1",
        "fields": ["frozen_ratio", "ratio_of_sums", "and whatever else the "
                   "non-uniform argmin shift moves"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": "    var = p * (1 - p)\n",
        "new": "    var = p\n",
        "count": 1,
    },
    "M7": {
        "desc": "_transport_label_cheeger's volume normalisation "
                "min(r, n-r) -> max(r, n-r): the transport Cheeger constant is "
                "divided by the WRONG volume.  A normalisation, not a selector, "
                "so it is not the same shape as M3/M5/M6",
        "seen_by": "UNSEEN -- used by neither mg-60d3 nor mg-5ad1",
        "fields": ["phi_t_cheeger"],
        "file": "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
        "old": "            phi = (leak / tot) / min(r, n - r)",
        "new": "            phi = (leak / tot) / max(r, n - r)",
        "count": 1,
    },
}

# (mutation, gate) -> required exit code.  THIS is the demonstration.
EXPECTED = {}
for _m in ["none"] + sorted(MUTATIONS):
    EXPECTED[(_m, "pre-widening")] = 0        # every one of them was invisible
    EXPECTED[(_m, "widened")] = 0 if _m == "none" else 1


# ------------------------------------------------------------ tree building ---
# The pre-widening gate is PINNED, not derived from the branch topology: it is
# the mg-60d3-repaired gate, the exact source mg-5ad1 measured M3 and M4 against.
# A merge-base would have been fragile in the direction that matters -- once
# mg-75f0 lands on main, a merge-base baseline becomes the WIDENED gate and the
# left column silently stops being a comparison.  A pinned SHA cannot rot.
PRE_WIDENING_REV = "af7fc2df"     # mg-60d3, "docs+scripts: land the mg-09ea audit"


def pre_widening_gate_source():
    """The gate as mg-60d3 merged it: the real source, not a reconstruction."""
    show = subprocess.run(["git", "show", f"{PRE_WIDENING_REV}:{GATE}"],
                          cwd=REPO, capture_output=True, text=True)
    if show.returncode != 0:
        raise SystemExit(f"cannot read {GATE} at {PRE_WIDENING_REV}: "
                         f"{show.stderr.strip()}")
    return PRE_WIDENING_REV, show.stdout


def build_tree(root, mutation, gate_variant, pre_src):
    """An isolated tree with scripts/ + the datasets the gate reads, one
    source-level edit applied, and the requested gate source in place."""
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    for fn in os.listdir(os.path.join(REPO, "scripts")):
        if fn.endswith(".py"):
            shutil.copy2(os.path.join(REPO, "scripts", fn),
                         os.path.join(root, "scripts", fn))
    for fn in DATASETS:
        shutil.copy2(os.path.join(REPO, "data", fn),
                     os.path.join(root, "data", fn))

    if gate_variant == "pre-widening":
        with open(os.path.join(root, GATE), "w") as f:
            f.write(pre_src)
    elif gate_variant != "widened":
        raise SystemExit(f"unknown gate variant {gate_variant!r}")

    applied = None
    if mutation != "none":
        mu = MUTATIONS[mutation]
        path = os.path.join(root, mu["file"])
        with open(path) as f:
            src = f.read()
        got = src.count(mu["old"])
        if got != mu["count"]:
            raise SystemExit(
                f"{mutation}: anchor found {got} times in {mu['file']}, "
                f"expected {mu['count']} -- the mutation would be a NO-OP and "
                f"the run would be a lie.  Anchor:\n{mu['old']}")
        with open(path, "w") as f:
            f.write(src.replace(mu["old"], mu["new"]))
        applied = {"file": mu["file"], "occurrences": got}
    return applied


# ----------------------------------------------------------------- one case ---
FAIL_RE = re.compile(r"^\s+-\s(.*)$")


def extract(stdout):
    """The lines that make the outcome legible: what the gate said failed, and
    the identity/measurement figures each mutation moves."""
    fails, ident, meas, ctrl = [], {}, {}, []
    in_fail = False
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith("CONTROL FAILURES"):
            in_fail = True
            continue
        if in_fail:
            m = FAIL_RE.match(line)
            if m:
                fails.append(m.group(1))
                continue
            if s:
                in_fail = False
        if s.startswith("fields compared"):
            ctrl.append(s)
        if s.startswith("enum-n7-#") and "lam2_BK=" in s:
            ident[s.split()[0]] = s
        elif s.startswith("enum-n7-#") and len(s.split()) >= 12:
            f = s.split()
            meas[f[0]] = {"dim_U": f[2], "c_max": f[7], "c_min": f[8],
                          "null": f[9], "frozcap": f[10], "froz_U": f[11]}
    return fails, ident, meas, ctrl


def run_case(mutation, gate_variant, pre_src, keep=False):
    root = tempfile.mkdtemp(prefix=f"mg75f0-{mutation}-{gate_variant}-")
    try:
        applied = build_tree(root, mutation, gate_variant, pre_src)
        proc = subprocess.run([sys.executable, GATE, "--no-sweep"], cwd=root,
                              capture_output=True, text=True)
        fails, ident, meas, ctrl = extract(proc.stdout)
        return {"mutation": mutation, "gate": gate_variant,
                "applied": applied, "exit": proc.returncode,
                "gate_failures": fails, "identity_lines": ident,
                "measured": meas, "field_census_lines": ctrl,
                "stderr_tail": proc.stderr[-2000:] if proc.returncode > 1 else ""}
    finally:
        if not keep:
            shutil.rmtree(root, ignore_errors=True)


# ------------------------------------------------------------------ driver ---
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="",
                    help="comma-separated subset, e.g. M3,M5 (none is implied)")
    ap.add_argument("--gates", default="pre-widening,widened")
    args = ap.parse_args()

    rev, pre_src = pre_widening_gate_source()
    widened_is_different = (pre_src !=
                            open(os.path.join(REPO, GATE)).read())
    print("=" * 78)
    print("mg-75f0 -- IS THE CLASS CLOSED?  source-level mutation demonstration")
    print("=" * 78)
    print(f"  pre-widening gate source : {GATE} at {rev} (mg-60d3, the source "
          f"mg-5ad1 measured M3/M4 against)")
    print(f"  widened gate source      : {GATE} in the working tree")
    print(f"  the two differ           : {widened_is_different}")
    if not widened_is_different:
        print("  !! the two gate columns are the SAME FILE -- this run cannot "
              "demonstrate anything")

    gates = [g for g in args.gates.split(",") if g]
    wanted = ["none"] + (sorted(MUTATIONS) if not args.only
                         else [m for m in args.only.split(",") if m != "none"])

    results, ok = [], True
    for mutation in wanted:
        for gate_variant in gates:
            want = EXPECTED[(mutation, gate_variant)]
            mu = MUTATIONS.get(mutation, {"desc": "unmutated instrument",
                                          "seen_by": "-", "fields": []})
            print()
            print("-" * 78)
            print(f"CASE  {mutation:<5} gate={gate_variant:<13} "
                  f"(expect exit {want})")
            print(f"      {mu['desc']}")
            print(f"      first used by: {mu['seen_by']}")
            print("-" * 78, flush=True)
            r = run_case(mutation, gate_variant, pre_src)
            r["expected_exit"] = want
            r["PASS"] = (r["exit"] == want)
            r["moves_reference_fields"] = mu["fields"]
            r["desc"] = mu["desc"]
            r["seen_by"] = mu["seen_by"]
            for line in r["field_census_lines"][:2]:
                print(f"      {line}")
            for f in r["gate_failures"]:
                print(f"      GATE FAILURE: {f}")
            if not r["gate_failures"]:
                print("      (no gate failure reported)")
            if not r["PASS"]:
                ok = False
                print(r["stderr_tail"])
            print(f"      --> exit {r['exit']} (expected {want})  "
                  f"{'OK' if r['PASS'] else 'DEMONSTRATION FAILED'}", flush=True)
            results.append(r)

    # ---- the matrix -------------------------------------------------------
    print()
    print("=" * 78)
    print("THE MATRIX")
    print("=" * 78)
    print(f"{'mutation':<10} {'first used by':<38} "
          + "  ".join(f"{g:>13}" for g in gates))
    for mutation in wanted:
        mu = MUTATIONS.get(mutation, {"seen_by": "-"})
        cells = []
        for g in gates:
            r = next((x for x in results
                      if x["mutation"] == mutation and x["gate"] == g), None)
            cells.append("      -      " if r is None else
                         f"exit {r['exit']} {'ok' if r['PASS'] else 'BAD'}"
                         .rjust(13))
        print(f"{mutation:<10} {mu['seen_by'][:38]:<38} " + "  ".join(cells))

    unseen = [m for m in MUTATIONS if MUTATIONS[m]["seen_by"].startswith("UNSEEN")]
    caught = [m for m in unseen
              if any(r["mutation"] == m and r["gate"] == "widened"
                     and r["exit"] == 1 for r in results)]
    invisible = [m for m in unseen
                 if any(r["mutation"] == m and r["gate"] == "pre-widening"
                        and r["exit"] == 0 for r in results)]

    report = {
        "what": "mg-75f0 source-level mutation demonstration: is mg-5ad1's "
                "class -- a quantity the document asserts, computed by code the "
                "CI gate exercises, with no control that can fail -- closed?",
        "gate_command": f"python3 {GATE} --no-sweep",
        "pre_widening_gate_revision": rev,
        "gate_sources_differ": widened_is_different,
        "route": "isolated tree per case (copy of scripts/ + the mg-8b64 "
                 "reference dataset), ONE source-level edit with an "
                 "anchor-count assertion, gate run there; the pre-widening "
                 "gate is the real source at the merge-base, not a "
                 "reconstruction",
        "mutations": {k: {kk: vv for kk, vv in v.items()
                          if kk in ("desc", "seen_by", "fields", "file")}
                      for k, v in MUTATIONS.items()},
        "cases": results,
        "unseen_mutations": unseen,
        "unseen_invisible_to_the_pre_widening_gate": invisible,
        "unseen_caught_by_the_widened_gate": caught,
        "ALL_PASS": ok,
    }
    out = os.path.join(REPO, "data", "onethird-mg75f0-gate-class-closure.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {os.path.relpath(out, REPO)}")

    if not ok:
        print("\nDEMONSTRATION FAILED: the exit-code matrix is not as asserted. "
              "If an UNSEEN\nmutation passed the widened gate, the class is "
              "STILL OPEN and must be reported\nas such rather than papered "
              "over.")
        return 1
    print(f"\nDemonstration complete.  {len(caught)}/{len(unseen)} mutations "
          f"that NEITHER mg-60d3 nor\nmg-5ad1 used are caught by the widened "
          f"gate, and {len(invisible)}/{len(unseen)} of them were invisible to "
          f"the\ngate before it -- so the widening is not a patch on its own "
          f"witnesses.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
