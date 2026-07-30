#!/usr/bin/env python3
"""ACCEPTANCE for CONTROLS G and H -- the corpus-independent references (mg-48dd).

WHAT THIS PROBE IS FOR.  mg-4f9b recorded that the gate CANNOT close the
one-character-selector class and that the class belongs to the audit stage.
mg-56be attacked that negative -- at mg-4f9b's own request -- and refuted it by
exhibiting references the corpus cannot produce.  mg-48dd landed two of them:

    CONTROL G   sum_sigma f = 0     reference = the integer ZERO
    CONTROL H   f^T P_U f < 1 - eps reference = the integer ONE (off-regime only)

This file measures that they fire on the two instances mg-4f9b recorded as open,
that they do NOT fire on correct input, and that regeneration cannot absorb
either one.  It is a NEW instrument, written for this ticket.

WHY IT IS NEW, AND THIS IS THE POINT OF IT.  This lineage's recurring failure is
a control validated by re-running its author's own instrument.  So:

  * `scripts/onethird_mg4f9b_route_axis_probe.py` is NOT run.  It asked not to be
    the thing that validates its own result, which was the correct request and is
    honoured here for the same reason mg-56be honoured it.
  * `scripts/onethird_mg56be_provenance_audit.py` is NOT run either.  It is the
    instrument that PRODUCED I1 and I6; re-running it to confirm them would be
    the same defect one generation later.  Its numbers are reproduced here from
    scratch and reported with my own counts.
  * `scripts/onethird_mgbd53_widening_audit_probe.py` IS run, unchanged and
    md5-verified, on both trees -- but by hand, not from here.  It is the
    instrument that found the last regression and it must not be touched.  The
    both-directions reading (NO row goes 1 -> 0) is in the deliverable.

THE THREE THINGS A CASE MUST SURVIVE TO COUNT, each of which has silently broken
a probe in this arc at least once:

  1. ANCHOR COUNTS.  Every source edit asserts the exact number of occurrences it
     expects to replace.  A mutation that silently applies zero times reports the
     absence of an effect it never introduced (mg-75f0's harness defect).
  2. REGENERATION IS FATAL ON FAILURE and asserts its row count.  mg-56be's own
     §11 records a regeneration that raised AttributeError in a subprocess, was
     swallowed, and nearly produced a false RED against mg-4f9b's headline.
  3. A NEGATIVE CONTROL IN BOTH DIRECTIONS.  The unmutated gate must exit 0 AND
     neither CONTROL G nor CONTROL H may appear in its failure list.  A control
     that fires on correct input is worse than no control.

PART A -- the invariants, measured in-process, no gate runs.  ~40 s.
PART B -- full gate runs (`--no-sweep`) on mutated copies of the tree.  ~6 min.

Run:  /usr/bin/python3 scripts/onethird_mg48dd_corpus_independent_probe.py
      /usr/bin/python3 scripts/onethird_mg48dd_corpus_independent_probe.py --part-a
Output: data/onethird-mg48dd-corpus-independent.json

Interpreter matters -- bare `python3` on this host has no numpy.  BLAS is pinned
to one thread for the same reason mg-bd53's probe pins it.
"""

import os
import sys
import json
import shutil
import hashlib
import argparse
import tempfile
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PINNED = {"OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1",
          "MKL_NUM_THREADS": "1", "VECLIB_MAXIMUM_THREADS": "1",
          "NUMEXPR_NUM_THREADS": "1"}
os.environ.update(PINNED)

import numpy as np  # noqa: E402

GATE = "scripts/onethird_mg2c34_n7_overlap_test.py"
MG8B64 = "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py"
MG4A86_OV = "scripts/onethird_mg4a86_sdquant_overlap.py"
REF_DATASET = "onethird-mg8b64-L1b-bk-transport-transfer.json"

# The rows the gate looks up by name.  Regeneration rewrites exactly these -- the
# author's workflow is "edit a probe, re-run it, commit the numbers", and the
# other 1083 rows are invisible to the gate.
GATE_ROWS = ["enum-n7-#3", "enum-n7-#20", "enum-n7-#600", "enum-n7-#945",
             "enum-n7-#809", "enum-n7-#52", "enum-n7-#88", "fam:N (2+2)"]

# ---------------------------------------------------------------------------
# The mutations.  C2 and M3 are the two instances mg-4f9b's deliverable records
# as OPEN; M4 is the control that says regeneration cannot move a theorem, and
# `none` is the false-positive control.  Anchors are byte-exact and counted.
# ---------------------------------------------------------------------------
MUTATIONS = {
    "C2": {
        "desc": "the gate's own frozen_pair_indicator loses its centring "
                "(mg-bd53's C2) -- the instance that survived FOUR generations",
        "edits": [{"file": GATE,
                   "old": "    f -= f.mean()\n",
                   "new": "    f -= 0.0 * f.mean()\n",
                   "count": 1}],
        "expect_exit": 1,
        "expect_control": "CONTROL G",
        "why": "f is no longer centred, so sum_sigma f != 0.  The reference is "
               "the integer 0 and nothing in the corpus can move it",
    },
    "M3": {
        "desc": "mg-5ad1's Theorem-E frozen-pair selector min -> max "
                "(argmin of the ratio becomes argmax)",
        "edits": [{"file": MG8B64,
                   "old": '    frozen = min((pc for pc in pairs if pc["ratio"] is not None),\n'
                          '                 key=lambda pc: pc["ratio"], default=None)',
                   "new": '    frozen = max((pc for pc in pairs if pc["ratio"] is not None),\n'
                          '                 key=lambda pc: pc["ratio"], default=None)',
                   "count": 1}],
        "expect_exit": 1,
        "expect_control": None,   # caught by the identity check WITHOUT regen
        "why": "without regeneration the identity check catches it, as it has "
               "since mg-75f0.  The interesting row is M3+regen",
    },
    "M4": {
        "desc": "mg-5ad1's projector_U rank filter s > max(tol,1e-10) -> s > 0.0",
        "edits": [{"file": MG4A86_OV,
                   "old": "    Q = Uu[:, s > max(tol, 1e-10)]",
                   "new": "    Q = Uu[:, s > 0.0]",
                   "count": 1}],
        "expect_exit": 1,
        "expect_control": None,
        "why": "THE CONTROL on the whole regeneration experiment.  CONTROL B / "
               "CONTROL E reference (n-1)^2+1, so M4+regen must stay exit 1.  "
               "Without this row the M3/M3+regen pair is an anecdote",
    },
}

CASES = [
    ("none", None, False),
    ("C2", "C2", False),
    ("C2+regen", "C2", True),
    ("M3", "M3", False),
    ("M3+regen", "M3", True),
    ("M4", "M4", False),
    ("M4+regen", "M4", True),
]

# Rewrite exactly the rows the gate reads, using the MUTATED corpus.  Fatal on
# failure, and the caller asserts the count -- see docstring note 2.
REGEN = r'''
import json, sys
sys.path.insert(0, "scripts")
from onethird_mg8b64_L1b_bk_transport_transfer_probe import (
    analyze_poset, biased_families)
from onethird_mgb0a6_spectral_killshot_probe import enumerate_both_connected
names = json.loads(sys.argv[1])
path = "data/%s"
d = json.load(open(path))
Ps = enumerate_both_connected(7)
fams = biased_families()
idx = {r["name"]: i for i, r in enumerate(d["rows"])}
done = []
for nm in names:
    if nm not in idx:
        raise SystemExit("row not in dataset: " + nm)
    if nm.startswith("enum-n7-#"):
        P = Ps[int(nm.split("#")[1])]
    elif nm.startswith("fam:"):
        P = fams[nm[4:]]
    else:
        raise SystemExit("cannot rebuild poset for: " + nm)
    d["rows"][idx[nm]] = analyze_poset(P, nm)
    done.append(nm)
json.dump(d, open(path, "w"), indent=2)
print(json.dumps({"regenerated": done}))
''' % REF_DATASET


# --------------------------------------------------------------- part A -----
def part_a():
    """The two invariants, measured directly.  No gate runs, no subprocesses.

    C2 and M3 are applied HERE by recomputing the affected quantity rather than
    by editing source, so part A and part B are genuinely two measurements of the
    same claim rather than one measurement run twice."""
    from onethird_mgb0a6_spectral_killshot_probe import enumerate_both_connected
    from onethird_mg4a86_sdquant_overlap import projector_U
    from onethird_mg8b64_L1b_bk_transport_transfer_probe import bk_frozen_pair

    Ps = enumerate_both_connected(7)
    OFF = [3, 20, 600]
    rows = []
    for i in OFF:
        P = Ps[i]
        les = P.linear_extensions()
        m = len(les)
        PU, _ = projector_U(P)
        bk = bk_frozen_pair(P)
        pairs = [pc for pc in bk["pairs"] if pc.get("ratio") is not None]

        def indicator(x, y, centre=True):
            f = np.zeros(m)
            for r, perm in enumerate(les):
                pos = {e: k for k, e in enumerate(perm)}
                f[r] = 1.0 if pos[x] < pos[y] else 0.0
            if centre:
                f -= f.mean()
            nrm = np.linalg.norm(f)
            return f / nrm if nrm > 0 else f

        fz = bk["frozen"]
        # the M3 pair: argMAX of the same ratio the gate's corpus argMINs
        m3 = max(pairs, key=lambda pc: pc["ratio"])
        base = indicator(fz["x"], fz["y"])
        c2 = indicator(fz["x"], fz["y"], centre=False)
        mut3 = indicator(m3["x"], m3["y"])

        row = {
            "poset": f"enum-n7-#{i}", "num_LE": m,
            "frozen_pair": [int(fz["x"]), int(fz["y"])],
            "M3_pair": [int(m3["x"]), int(m3["y"])],
            "M3_moves_the_pair": [int(m3["x"]), int(m3["y"])] != [int(fz["x"]), int(fz["y"])],
            # I1 / CONTROL G
            "I1_sum_baseline": float(base.sum()),
            "I1_sum_under_C2": float(c2.sum()),
            # I6 / CONTROL H
            "I6_overlap_baseline": float(base @ (PU @ base)),
            "I6_overlap_under_M3": float(mut3 @ (PU @ mut3)),
        }
        row["G_fires_on_baseline"] = abs(row["I1_sum_baseline"]) >= 1e-9
        row["G_fires_under_C2"] = abs(row["I1_sum_under_C2"]) >= 1e-9
        row["H_fires_on_baseline"] = row["I6_overlap_baseline"] >= 1 - 1e-6
        row["H_fires_under_M3"] = row["I6_overlap_under_M3"] >= 1 - 1e-6
        rows.append(row)

    print("=" * 78)
    print("PART A -- the two invariants, measured in-process at the three "
          "off-regime posets")
    print("=" * 78)
    print(f"{'poset':>14} {'|sum f| base':>13} {'|sum f| C2':>12} "
          f"{'ovlp base':>10} {'ovlp M3':>10} {'1-ovlp M3':>12}")
    for r in rows:
        print(f"{r['poset']:>14} {abs(r['I1_sum_baseline']):>13.3e} "
              f"{abs(r['I1_sum_under_C2']):>12.4f} "
              f"{r['I6_overlap_baseline']:>10.6f} "
              f"{r['I6_overlap_under_M3']:>10.6f} "
              f"{1 - r['I6_overlap_under_M3']:>12.3e}")
    g_ok = (all(r["G_fires_under_C2"] for r in rows)
            and not any(r["G_fires_on_baseline"] for r in rows))
    h_ok = (all(r["H_fires_under_M3"] for r in rows)
            and not any(r["H_fires_on_baseline"] for r in rows))
    print(f"\n  CONTROL G: fires under C2 at {sum(r['G_fires_under_C2'] for r in rows)}"
          f"/{len(rows)}, fires on baseline at "
          f"{sum(r['G_fires_on_baseline'] for r in rows)}/{len(rows)}  -> "
          f"{'PASS' if g_ok else 'FAIL'}")
    print(f"  CONTROL H: fires under M3 at {sum(r['H_fires_under_M3'] for r in rows)}"
          f"/{len(rows)}, fires on baseline at "
          f"{sum(r['H_fires_on_baseline'] for r in rows)}/{len(rows)}  -> "
          f"{'PASS' if h_ok else 'FAIL'}")
    return {"rows": rows, "G_PASS": g_ok, "H_PASS": h_ok}


# --------------------------------------------------------------- part B -----
def build_tree(root, mutation):
    """Copy scripts/ + data/ and apply the mutation, asserting anchor counts."""
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    for d in ("scripts", "data"):
        for fn in os.listdir(os.path.join(REPO, d)):
            src = os.path.join(REPO, d, fn)
            if os.path.isfile(src):
                shutil.copy2(src, os.path.join(root, d, fn))
    applied = []
    if mutation is None:
        return applied
    for e in MUTATIONS[mutation]["edits"]:
        path = os.path.join(root, e["file"])
        with open(path) as f:
            src = f.read()
        n = src.count(e["old"])
        if n != e["count"]:
            raise SystemExit(f"ANCHOR: {mutation} expected {e['count']} "
                             f"occurrence(s) of its anchor in {e['file']}, "
                             f"found {n} -- the mutation did NOT apply and any "
                             f"exit code from this case is meaningless")
        with open(path, "w") as f:
            f.write(src.replace(e["old"], e["new"]))
        applied.append(f"{e['file']} x{n}")
    return applied


def regenerate(root):
    """Fatal on failure, and the row count is asserted by the caller."""
    proc = subprocess.run(["/usr/bin/python3", "-c", REGEN,
                           json.dumps(GATE_ROWS)],
                          cwd=root, capture_output=True, text=True,
                          env=dict(os.environ, **PINNED))
    if proc.returncode != 0:
        raise SystemExit(f"REGENERATION FAILED (fatal by design -- a "
                         f"regeneration that silently no-ops reports the "
                         f"absence of an effect it never produced):\n"
                         f"{proc.stderr[-2000:]}")
    done = json.loads(proc.stdout.strip().splitlines()[-1])["regenerated"]
    if len(done) != len(GATE_ROWS):
        raise SystemExit(f"REGENERATION wrote {len(done)} rows, expected "
                         f"{len(GATE_ROWS)}")
    return done


def gate_failures(stdout):
    out, seen = [], False
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith("CONTROL FAILURES"):
            seen = True
            continue
        if seen:
            if s.startswith("- "):
                out.append(s[2:])
            elif s:
                seen = False
    return out


def run_case(label, mutation, regen):
    root = tempfile.mkdtemp(prefix=f"mg48dd-{label.replace('+', '_')}-")
    try:
        applied = build_tree(root, mutation)
        regenerated = regenerate(root) if regen else None
        proc = subprocess.run(["/usr/bin/python3", GATE, "--no-sweep"],
                              cwd=root, capture_output=True, text=True,
                              env=dict(os.environ, **PINNED))
        fails = gate_failures(proc.stdout)
        return {
            "case": label, "mutation": mutation, "regenerated": regenerated,
            "edits_applied": applied, "exit": proc.returncode,
            "failures": fails,
            "n_CONTROL_G": sum("CONTROL G" in m for m in fails),
            "n_CONTROL_H": sum("CONTROL H" in m for m in fails),
            "n_identity": sum("does not match its committed" in m for m in fails),
            "stdout_sha256": hashlib.sha256(proc.stdout.encode()).hexdigest(),
            "stderr_tail": proc.stderr[-1500:] if proc.returncode > 1 else "",
        }
    finally:
        shutil.rmtree(root, ignore_errors=True)


def part_b(only=None):
    print()
    print("=" * 78)
    print("PART B -- full gate runs on mutated copies of the tree "
          "(`--no-sweep`)")
    print("=" * 78)
    rows = []
    for label, mutation, regen in CASES:
        if only and label not in only:
            continue
        print(f"  running {label} ...", flush=True)
        r = run_case(label, mutation, regen)
        rows.append(r)
        print(f"    exit {r['exit']}   CONTROL G x{r['n_CONTROL_G']}   "
              f"CONTROL H x{r['n_CONTROL_H']}   identity x{r['n_identity']}")
        for m in r["failures"][:4]:
            print(f"      - {m[:150]}")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part-a", action="store_true",
                    help="invariants only, no gate runs (~40 s)")
    ap.add_argument("--only", default=None,
                    help="comma-separated part-B case labels")
    args = ap.parse_args()

    report = {"probe": "mg-48dd corpus-independent controls G and H",
              "gate": GATE}
    report["part_a"] = part_a()
    if not args.part_a:
        only = set(args.only.split(",")) if args.only else None
        report["part_b"] = part_b(only)

        print()
        print("-" * 78)
        print("PART B SUMMARY")
        print("-" * 78)
        print(f"  {'case':>10} {'exit':>5} {'G':>3} {'H':>3} {'ident':>6}  "
              f"reading")
        expect = {
            "none": "no mutation -- exit 0 and NO G/H is the false-positive control",
            "C2": "CONTROL G fires; four generations of this gate exited 0 here",
            "C2+regen": "regeneration cannot move 0 -- G still fires",
            "M3": "caught by the identity check, as since mg-75f0",
            "M3+regen": "identity check ABSORBED it (mg-4f9b's exit 0); "
                        "CONTROL H catches it anyway",
            "M4": "caught by CONTROL B / CONTROL E",
            "M4+regen": "THE CONTROL: regeneration cannot move (n-1)^2+1",
        }
        for r in report["part_b"]:
            print(f"  {r['case']:>10} {r['exit']:>5} {r['n_CONTROL_G']:>3} "
                  f"{r['n_CONTROL_H']:>3} {r['n_identity']:>6}  "
                  f"{expect.get(r['case'], '')}")

    # `--part-a` must NOT overwrite the committed record with a part-B-less
    # copy: the deliverable's §4.1 table is sourced from it.  Same rule the gate
    # applies to its own `--no-sweep` control mode, and for the same reason.
    if args.part_a:
        print("\n(--part-a: invariants only, committed record left untouched)")
    else:
        out = os.path.join(REPO, "data",
                           "onethird-mg48dd-corpus-independent.json")
        with open(out, "w") as f:
            json.dump(report, f, indent=2)
        print(f"\nwrote {os.path.relpath(out, REPO)}")

    # ------------------------------------------------------------- verdict --
    problems = []
    if not report["part_a"]["G_PASS"]:
        problems.append("PART A: CONTROL G does not separate baseline from C2")
    if not report["part_a"]["H_PASS"]:
        problems.append("PART A: CONTROL H does not separate baseline from M3")
    if "part_b" in report:
        by = {r["case"]: r for r in report["part_b"]}
        if "none" in by:
            r = by["none"]
            if r["exit"] != 0:
                problems.append("PART B: the UNMUTATED gate does not exit 0")
            if r["n_CONTROL_G"] or r["n_CONTROL_H"]:
                problems.append("PART B: CONTROL G/H fire on correct input -- a "
                                "control that fires on correct input is worse "
                                "than no control")
        for c in ("C2", "C2+regen"):
            if c in by and by[c]["n_CONTROL_G"] < 1:
                problems.append(f"PART B: {c} did not fire CONTROL G")
        if "M3+regen" in by and by["M3+regen"]["n_CONTROL_H"] < 1:
            problems.append("PART B: M3+regen did not fire CONTROL H -- this is "
                            "the row the whole ticket rests on")
        if "M4+regen" in by and by["M4+regen"]["exit"] != 1:
            problems.append("PART B: M4+regen is not exit 1 -- the regeneration "
                            "control has broken, so no +regen row can be read")
    if problems:
        print("\nPROBE FAILURES:")
        for p in problems:
            print(f"  - {p}")
        return 1
    print("\nAll probe assertions PASSED.")
    print("SCOPE: CONTROLS G and H close `frozen_pair_overlap_with_U`, the "
          "quantity mg-4f9b named as open.\n       They do NOT close the "
          "one-character-selector class in general -- a selector flip landing\n"
          "       on a legitimately-different pair without driving the overlap "
          "to 1 passes both.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
