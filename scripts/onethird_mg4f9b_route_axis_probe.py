#!/usr/bin/env python3
"""
mg-4f9b -- THE ROUTE AXIS: landing mg-bd53's audit consequences, and measuring
why the one-character-selector class survives a fourth generation.

mg-bd53 audited the mg-75f0 gate widening and returned RED on two counts.  This
file is the measurement half of the repair.  It has three parts and they answer
three different questions.

  PART 1  THE ROUTE DECLARATION, structural, seconds.  Of the four quantities
          the pre-widening gate compared, how many still have the GATE'S OWN
          independent recomputation inside `_identity_row_ok`, and does the gate
          SAY which is which?  Read out of `IDENTITY_SECOND_ROUTES` rather than
          hardcoded here, so this part cannot drift from the gate the way
          mg-75f0's comment drifted from mg-75f0's behaviour.

  PART 2  THE MATRIX, three gate columns.  `pre-widening` (af7fc2df),
          `mg75f0-widened` (91fa25f -- byte-identical to the gate at the
          mg-75f0 landing 9fa4aaa, checked), and `repaired` (this tree).  A row
          is interesting when the three columns are not monotone.

  PART 3  THE G3 QUESTION, and it is a QUESTION and not a fix.  pm-onethird's
          record: the AUDIT stage is 3 for 3 on this class and the GATE is 0 for
          2.  The specific hypothesis to test is whether the gate's reference is
          INDEPENDENT of the code a mutation touches, or descends from the same
          computation.  Part 3 measures that directly by doing what an author
          does: mutate the corpus AND regenerate the committed rows, in one
          step, then run the gate.

THE FOUR MUTATIONS OF PART 2.

  B1   mg-bd53's regression row, reproduced as the acceptance test for G1.
       mg-4a86's OWN `lambda_std`, `np.max(w)` -> `np.min(w)`, ONE CHARACTER.
       Pre-widening exit 1; mg75f0-widened exit 0 (the widening removed the
       comparison); repaired exit 1 again.  This row is the whole of G1.

  D1   MINE, and used by neither mg-75f0 nor mg-bd53.  The GATE'S OWN
       `delta_and_frozen_pair` aggregation, `max(best_delta, d)` ->
       `min(best_delta, d)`: delta becomes the min over incomparable pairs of
       min(p, 1-p) instead of the max.  The gate keeps computing it, keeps
       PRINTING it in the measurement table, and after mg-75f0 compares it
       against nothing -- `match_delta` became an alias of mg-8b64's route.  The
       same shape as B1 in a second quantity, which is why mg-bd53 named delta
       beside lambda_std.

  D2   MINE, and used by neither.  mg-8b64's `bk_cheeger_exhaustive` degree
       normalisation, `(n - 1) * mn` -> `(n + 1) * mn`, ONE CHARACTER.  Moves
       `h_bk_exhaustive` and NOTHING else.  Chosen because that field exists
       only on the 54 committed rows with small |L|, and until this ticket the
       identity population was seven n = 7 posets whose rows do not carry it:
       compared at ZERO posets, while every printed census read "0 silently
       uncompared" (mg-bd53 finding 4 -- true per row, false per dataset).  So
       this row is exit 0 on BOTH earlier columns and exit 1 on the repaired
       one, and it is coverage no generation of this gate has ever had.

  M3   mg-5ad1's Theorem-E frozen-pair selector min -> max.  Carried forward
       unchanged as the control that the widening's own catch still works --
       the repair must not cost what mg-75f0 bought.

PART 3, IN DETAIL, because the answer is the deliverable.

  R1   M3 AND a regenerated dataset.  The mutation is applied to mg-8b64 and
       then the committed rows the gate consults are rewritten by the MUTATED
       `analyze_poset` -- which is exactly what an author does between editing
       a probe and committing: re-run it, commit the new numbers.  M3 alone is
       caught at 7/7.  If R1 is exit 0, the gate's identity check is not
       comparing a computation against an independent reference; it is
       comparing a computation against A FROZEN SNAPSHOT OF ITSELF, and it
       detects the mutation only because nobody refreshed the snapshot.

  R2   M4 (mg-5ad1's `projector_U` rank filter, s > max(tol,1e-10) -> s > 0.0)
       AND the same regeneration.  M4 is caught by CONTROL B and CONTROL E,
       whose references are `(n-1)^2 + 1` and `c = 1` -- a rank computed from
       the representation theory of S_n and a known-answer poset.  Those are
       THEOREMS, not stored numbers, and no regeneration can move them.  R2 is
       the contrast that makes R1 a mechanism rather than an anecdote: if R1
       goes 1 -> 0 and R2 stays 1, the distinction is not field coverage and not
       route count, it is WHERE THE REFERENCE COMES FROM.

  The regeneration is TARGETED -- only the rows the gate looks up by name are
  rewritten, because those are the only rows it reads.  Rewriting all 1091 would
  be the same experiment and take hours.

Run:  /usr/bin/python3 scripts/onethird_mg4f9b_route_axis_probe.py
      (numpy required; ~12 min -- sixteen full runs of the CI gate)
      --part1-only     the structural half, seconds
      --only B1,D1     a subset of part 2 (baselines implied)
      --skip-part3     part 2 only
      --part3-only     the G3 experiment on its own, ~3 min

Writes `data/onethird-mg4f9b-route-axis.json`.
"""

import os
import sys
import json
import shutil
import hashlib
import inspect
import argparse
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPTS = os.path.join(REPO, "scripts")
GATE = os.path.join("scripts", "onethird_mg2c34_n7_overlap_test.py")
REF_DATASET = "onethird-mg8b64-L1b-bk-transport-transfer.json"
DATASETS = [REF_DATASET]

# The same pin mg-75f0 and mg-bd53 use, for the same reason.
PRE_WIDENING_REV = "af7fc2df"
# The mg-bd53 audit tree.  Byte-identical to the gate at the mg-75f0 landing
# (9fa4aaa) -- checked, not assumed, and re-checked at run time below, because a
# column that silently became a different gate would make this matrix a lie.
MG75F0_REV = "91fa25f"

MG4A86_SD = "scripts/onethird_mg4a86_standard_dominance_target_audit.py"
MG4A86_OV = "scripts/onethird_mg4a86_sdquant_overlap.py"
MG8B64 = "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py"

GATES = ["pre-widening", "mg75f0-widened", "repaired"]

# Rows the gate looks up by name, across all three columns: the five named
# posets, CONTROL F's two, and the small-|L| poset the repair adds.
GATE_ROWS = ["enum-n7-#3", "enum-n7-#20", "enum-n7-#600", "enum-n7-#945",
             "enum-n7-#809", "enum-n7-#52", "enum-n7-#88", "fam:N (2+2)"]

MUTATIONS = {
    "B1": {
        "desc": "mg-4a86's OWN lambda_std, np.max(w) -> np.min(w).  mg-bd53's "
                "regression row: the PRE-widening gate catches it, the widened "
                "gate does not",
        "mine": False,
        "file": MG4A86_SD,
        "old": "    return float(np.max(w))",
        "new": "    return float(np.min(w))",
        "count": 1,
        "expect": {"pre-widening": 1, "mg75f0-widened": 0, "repaired": 1},
        "why": "G1.  The widening replaced the gate's own route into "
               "match_lambda_std with an alias of mg-8b64's route, so mg-4a86's "
               "implementation lost its only comparison.  Restoring the second "
               "route must make this fatal again WITHOUT giving up the field "
               "widening -- which is what M3 in this same matrix checks",
    },
    "D1": {
        "desc": "the GATE'S OWN delta aggregation, max(best_delta, d) -> "
                "min(best_delta, d): delta becomes a min over incomparable "
                "pairs instead of a max",
        "mine": True,
        "file": GATE,
        "old": "        best_delta = d if best_delta is None else max(best_delta, d)",
        "new": "        best_delta = d if best_delta is None else min(best_delta, d)",
        "count": 1,
        "expect": {"pre-widening": 1, "mg75f0-widened": 0, "repaired": 1},
        "why": "MINE, and neither mg-75f0 nor mg-bd53 used it.  mg-bd53 named "
               "delta beside lambda_std as the second quantity that lost its "
               "route, and measured the loss STRUCTURALLY; this measures it "
               "with a mutation.  The gate computes delta, prints it in the "
               "measurement table, and between mg-75f0 and this ticket "
               "compared it against nothing",
    },
    "D2": {
        "desc": "mg-8b64's bk_cheeger_exhaustive degree normalisation, "
                "(n - 1) * mn -> (n + 1) * mn.  Moves h_bk_exhaustive and "
                "nothing else",
        "mine": True,
        "file": MG8B64,
        "old": "        phi = boundary / ((n - 1) * mn)",
        "new": "        phi = boundary / ((n + 1) * mn)",
        "count": 1,
        "expect": {"pre-widening": 0, "mg75f0-widened": 0, "repaired": 1},
        "why": "MINE, and neither used it.  h_bk_exhaustive is committed on 54 "
               "of the 1091 mg-8b64 rows and was compared at ZERO posets, "
               "because bk_cheeger_exhaustive only returns a value for small "
               "|L| and the identity population was seven n = 7 posets.  Both "
               "earlier columns pass this byte-identically -- they never reach "
               "the line.  The repair adds fam:N (2+2) (|L| = 6) to the "
               "population, which is the whole of G4",
    },
    "M3": {
        "desc": "mg-5ad1's Theorem-E frozen-pair selector min -> max, the "
                "mutation the widening was built to catch",
        "mine": False,
        "file": MG8B64,
        "old": '    frozen = min((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "new": '    frozen = max((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "count": 1,
        "expect": {"pre-widening": 0, "mg75f0-widened": 1, "repaired": 1},
        "why": "the REGRESSION CONTROL for this ticket.  Restoring the route "
               "axis must not cost the field axis: if this row goes 1 -> 0 in "
               "the repaired column, the repair has traded mg-75f0's gain for "
               "mg-bd53's, which is the same mistake in the other direction",
    },
    "M4": {
        "desc": "mg-5ad1's projector_U rank filter s > max(tol,1e-10) -> "
                "s > 0.0.  Caught by CONTROL B and CONTROL E, whose references "
                "are theorems",
        "mine": False,
        "file": MG4A86_OV,
        "old": "    Q = Uu[:, s > max(tol, 1e-10)]",
        "new": "    Q = Uu[:, s > 0.0]",
        "count": 1,
        "expect": {"pre-widening": 0, "mg75f0-widened": 1, "repaired": 1},
        "why": "part 3's contrast case.  M4 moves no committed reference field "
               "-- it is caught by the structural controls, not by the identity "
               "comparison -- which is exactly why regenerating the dataset "
               "cannot rescue it",
    },
}

# ------------------------------------------------------------------ part 3 ---
# Applied INSIDE the isolated tree, after the mutation, by the mutated corpus
# itself.  This is the author's own workflow expressed as four lines: edit the
# probe, re-run it, commit the numbers it now produces.
REGEN_SNIPPET = r'''
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
        continue
    if nm.startswith("enum-n7-#"):
        P = Ps[int(nm.split("#")[1])]
    elif nm.startswith("fam:"):
        P = fams.get(nm[4:])
    else:
        P = None
    if P is None:
        continue
    d["rows"][idx[nm]] = analyze_poset(P, nm)
    done.append(nm)
json.dump(d, open(path, "w"), indent=2)
print("REGENERATED " + ",".join(done))
''' % REF_DATASET

PART3 = {
    "R1": {
        "mutation": "M3",
        "regenerate": True,
        "expect": {"mg75f0-widened": 0, "repaired": 0},
        "question": "M3 is caught at 7/7 by both the widened and the repaired "
                    "gate.  Is it still caught when the author commits the "
                    "numbers the mutated code produces?",
    },
    "R2": {
        "mutation": "M4",
        "regenerate": True,
        "expect": {"mg75f0-widened": 1, "repaired": 1},
        "question": "M4 is caught by CONTROL B and CONTROL E, whose references "
                    "are (n-1)^2+1 and c = 1.  Can regeneration move a "
                    "theorem?",
    },
}


# ------------------------------------------------ part 1, the route axis ------
def part_1():
    """Does the gate DECLARE, per compared quantity, whether it is one-route or
    two-route -- and is each declared second route a real second implementation?

    mg-bd53's part 1 answered the first half of this with a hardcoded table,
    which was correct at audit time and is exactly the kind of second
    representation that goes stale.  Here the table is READ OUT OF THE GATE
    (`IDENTITY_SECOND_ROUTES`) and each entry is checked against the modules it
    names, so a route that is declared and not wired, or wired and not declared,
    fails."""
    sys.path.insert(0, SCRIPTS)
    import onethird_mg2c34_n7_overlap_test as gate

    print("=" * 78)
    print("PART 1 -- the ROUTE axis: what does each comparison actually secure?")
    print("=" * 78)

    failures = []
    declared = getattr(gate, "IDENTITY_SECOND_ROUTES", None)
    if declared is None:
        failures.append(
            "PART 1: the gate has no IDENTITY_SECOND_ROUTES -- the route "
            "structure of its identity check is undeclared again, which is the "
            "state mg-bd53 found and the reason lambda_std lost its comparison "
            "without anyone noticing")
        return {"declared": None}, failures

    for problem in gate._identity_routes_declared():
        failures.append(f"PART 1: {problem}")

    # Resolve each declared second route to a real object, and require it to be
    # a DIFFERENT implementation from the one mg-8b64's row builder uses.  A
    # declaration naming a function that has been unified with the other route
    # is a declaration that has stopped being true.
    import onethird_mg4a86_standard_dominance_target_audit as mg4a86
    import onethird_mgb0a6_spectral_killshot_probe as mgb0a6
    import onethird_mg8b64_L1b_bk_transport_transfer_probe as mg8b64

    distinct = {}
    pairs = {
        "lambda_std": (mg4a86.lambda_std, mgb0a6.standard_block_and_lambda),
        "bk_lambda2": (mg4a86.bk_walk_matrix, mg8b64.bk_walk_matrix),
        "delta": (gate.delta_and_frozen_pair, mg8b64.bk_frozen_pair),
    }
    for field, (a, b) in pairs.items():
        same_module = a.__module__ == b.__module__
        same_source = inspect.getsource(a) == inspect.getsource(b)
        distinct[field] = (not same_module) and (not same_source)

    rows = []
    for _, field in gate.IDENTITY_LEGACY_FIELDS:
        d = declared.get(field, {})
        route = d.get("second_route")
        rows.append({
            "field": field,
            "declared_second_route": route,
            "two_route": route is not None,
            "implementations_are_distinct": distinct.get(field),
            "why": d.get("why", ""),
        })
        if route is not None and distinct.get(field) is False:
            failures.append(
                f"PART 1: {field} declares a second route ({route}) but the two "
                f"implementations are no longer distinct -- the declaration "
                f"promises coverage the code does not have")

    print(f"  {'quantity':<12} {'routes':>8}  {'distinct impls':>15}")
    for r in rows:
        print(f"  {r['field']:<12} {('TWO' if r['two_route'] else 'ONE'):>8}  "
              f"{str(r['implementations_are_distinct']):>15}")
    print()
    for r in rows:
        print(f"  {r['field']}: {r['why'][:300]}")

    two = [r["field"] for r in rows if r["two_route"]]
    print()
    print(f"  two-route quantities: {two}")
    print(f"  (mg-bd53 measured ONE of four -- bk_lambda2 -- after mg-75f0)")

    # The legacy keys must still be inert on their own: the row-wide comparison
    # is what decides, and the second routes are ANDed INTO it rather than
    # sitting beside it.  If this changes, mg-5ad1 part B2 is measuring a
    # different predicate than the gate uses.
    fields = [f for _, f in gate.IDENTITY_LEGACY_FIELDS]
    rec = {"field_matches": {f: True for f in fields},
           "match_num_LE": False, "match_lambda_std": False,
           "match_delta": False, "match_bk_lambda2": False}
    legacy_inert = bool(gate._identity_row_ok(rec))
    rec_bad = {"field_matches": dict({f: True for f in fields},
                                     lambda_std=False)}
    rowwide_decides = not gate._identity_row_ok(rec_bad)
    print(f"  legacy match_* keys inert (routes are ANDed INTO field_matches, "
          f"not beside it): {legacy_inert}")
    print(f"  the row-wide comparison decides _identity_row_ok            : "
          f"{rowwide_decides}")
    if not legacy_inert or not rowwide_decides:
        failures.append(
            "PART 1: the second routes are not folded into `field_matches` -- "
            "mg-5ad1's part B2 perturbs fields and calls `_identity_row_ok` on "
            "`field_matches` alone, so a route ANDed anywhere else is invisible "
            "to the probe that is supposed to enforce this gate")

    return {"declared_routes": rows,
            "two_route_quantities": two,
            "legacy_match_keys_are_inert": legacy_inert,
            "row_wide_comparison_decides": rowwide_decides,
            "implementations_are_distinct": distinct}, failures


# --------------------------------------------------------- part 2, the trees --
def gate_source(rev):
    show = subprocess.run(["git", "show", f"{rev}:{GATE}"],
                          cwd=REPO, capture_output=True, text=True)
    if show.returncode != 0:
        raise SystemExit(f"cannot read {GATE} at {rev}: {show.stderr.strip()}")
    return show.stdout


PINNED = {"OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1",
          "MKL_NUM_THREADS": "1", "VECLIB_MAXIMUM_THREADS": "1",
          "NUMEXPR_NUM_THREADS": "1"}


def build_tree(root, mutation, gate_variant, sources):
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    for fn in os.listdir(SCRIPTS):
        if fn.endswith(".py"):
            shutil.copy2(os.path.join(SCRIPTS, fn),
                         os.path.join(root, "scripts", fn))
    for fn in DATASETS:
        shutil.copy2(os.path.join(REPO, "data", fn),
                     os.path.join(root, "data", fn))
    if gate_variant in sources:
        with open(os.path.join(root, GATE), "w") as f:
            f.write(sources[gate_variant])
    elif gate_variant != "repaired":
        raise SystemExit(f"unknown gate variant {gate_variant!r}")

    if mutation == "none":
        return None
    mu = MUTATIONS[mutation]
    path = os.path.join(root, mu["file"])
    with open(path) as f:
        src = f.read()
    got = src.count(mu["old"])
    if got != mu["count"]:
        raise SystemExit(
            f"{mutation}: anchor found {got} times in {mu['file']}, expected "
            f"{mu['count']} -- the mutation would be a NO-OP and the run would "
            f"be a lie.  Anchor:\n{mu['old']}")
    with open(path, "w") as f:
        f.write(src.replace(mu["old"], mu["new"]))
    return {"file": mu["file"], "occurrences": got}


def regenerate(root):
    """Rewrite the committed rows the gate reads, using the MUTATED corpus.

    This is the author's workflow, not an attack: edit a probe, re-run it,
    commit the numbers.  Deliberately AFTER the mutation is applied and BEFORE
    the gate runs, and deliberately targeted at exactly the rows the gate looks
    up -- rewriting the other 1083 would take hours and change nothing the gate
    can see."""
    proc = subprocess.run(["/usr/bin/python3", "-c", REGEN_SNIPPET,
                           json.dumps(GATE_ROWS)],
                          cwd=root, capture_output=True, text=True,
                          env=dict(os.environ, **PINNED))
    if proc.returncode != 0:
        raise SystemExit(f"regeneration failed:\n{proc.stderr[-2000:]}")
    return proc.stdout.strip()


def run_case(mutation, gate_variant, sources, regen=False):
    root = tempfile.mkdtemp(prefix=f"mg4f9b-{mutation}-{gate_variant}-")
    try:
        applied = build_tree(root, mutation, gate_variant, sources)
        regen_note = regenerate(root) if regen else None
        proc = subprocess.run(["/usr/bin/python3", GATE, "--no-sweep"],
                              cwd=root, capture_output=True, text=True,
                              env=dict(os.environ, **PINNED))
        fails, ident, meas = extract(proc.stdout)
        return {"mutation": mutation, "gate": gate_variant, "applied": applied,
                "regenerated": regen_note, "exit": proc.returncode,
                "gate_failures": fails, "identity_lines": ident,
                "measured_lines": meas,
                "stdout_sha256": hashlib.sha256(
                    proc.stdout.encode()).hexdigest(),
                "stderr_tail": proc.stderr[-2000:] if proc.returncode > 1 else ""}
    finally:
        shutil.rmtree(root, ignore_errors=True)


def extract(stdout):
    fails, ident, meas = [], {}, {}
    in_fail = False
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith("CONTROL FAILURES"):
            in_fail = True
            continue
        if in_fail:
            if s.startswith("- "):
                fails.append(s[2:])
                continue
            if s:
                in_fail = False
        if "lam2_BK=" in s and ("enum-n7-#" in s or s.startswith("fam:")):
            ident[s.split()[0]] = s
        elif s.startswith("enum-n7-#") and len(s.split()) == 12:
            f = s.split()
            meas[f[0]] = {"dim_U": f[2], "lam_std": f[5], "c_max": f[7],
                          "null": f[9], "frozen_pairmode_capture": f[10],
                          "frozen_pair_overlap_with_U": f[11]}
    return fails, ident, meas


def show(mutation, gate_variant, want, desc, r):
    print()
    print("-" * 78)
    print(f"CASE  {mutation:<5} gate={gate_variant:<15} (expect exit {want})")
    print(f"      {desc}")
    print("-" * 78, flush=True)
    if r.get("regenerated"):
        print(f"      {r['regenerated']}")
    for f in r["gate_failures"][:3]:
        print(f"      GATE FAILURE: {f[:200]}")
    if not r["gate_failures"]:
        print("      (no gate failure reported)")
    if not r["PASS"] and r["stderr_tail"]:
        print(r["stderr_tail"][-800:])
    print(f"      --> exit {r['exit']} (expected {want})  "
          f"{'OK' if r['PASS'] else 'ROW DISAGREES'}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--gates", default=",".join(GATES))
    ap.add_argument("--part1-only", action="store_true")
    ap.add_argument("--skip-part3", action="store_true")
    ap.add_argument("--part3-only", action="store_true")
    args = ap.parse_args()

    p1, failures = part_1()
    report = {"what": "mg-4f9b: restore the ROUTE axis mg-75f0 narrowed, close "
                      "mg-bd53 finding 4's per-dataset gap, and MEASURE why the "
                      "one-character-selector class survives the gate",
              "pre_widening_gate_revision": PRE_WIDENING_REV,
              "mg75f0_gate_revision": MG75F0_REV,
              "part_1_route_axis": p1}

    if args.part1_only:
        _write(report, failures)
        return 1 if failures else 0

    sources = {"pre-widening": gate_source(PRE_WIDENING_REV),
               "mg75f0-widened": gate_source(MG75F0_REV)}
    # The mg75f0-widened column must be the gate mg-bd53 audited, and must not
    # be this tree's gate -- a column that has quietly become the other column
    # makes every row below unfalsifiable.
    landing = gate_source("9fa4aaa")
    if sources["mg75f0-widened"] != landing:
        failures.append(
            f"the {MG75F0_REV} gate is NOT byte-identical to the gate at the "
            f"mg-75f0 landing (9fa4aaa) -- the 'mg75f0-widened' column is not "
            f"what it claims to be")
    here = open(os.path.join(REPO, GATE)).read()
    for col, src in sources.items():
        if src == here:
            failures.append(f"the {col!r} column is byte-identical to this "
                            f"tree's gate -- that column cannot demonstrate "
                            f"anything")

    gates = [g for g in args.gates.split(",") if g]
    results = []

    if not args.part3_only:
        wanted = ["none"] + (sorted(MUTATIONS) if not args.only
                             else [m for m in args.only.split(",")
                                   if m != "none"])
        for mutation in wanted:
            for gate_variant in gates:
                mu = MUTATIONS.get(mutation, {
                    "desc": "unmutated instrument",
                    "expect": {g: 0 for g in GATES}})
                want = mu["expect"][gate_variant]
                r = run_case(mutation, gate_variant, sources)
                r["expected_exit"] = want
                r["PASS"] = (r["exit"] == want)
                r["desc"] = mu["desc"]
                r["why"] = mu.get("why", "")
                r["mine"] = mu.get("mine", False)
                r["part"] = 2
                show(mutation, gate_variant, want, mu["desc"], r)
                results.append(r)

        base = {g: next((r["stdout_sha256"] for r in results
                         if r["mutation"] == "none" and r["gate"] == g), None)
                for g in gates}
        for r in results:
            if r["mutation"] == "none" or base.get(r["gate"]) is None:
                continue
            r["stdout_differs_from_unmutated"] = (
                r["stdout_sha256"] != base[r["gate"]])
            r["verdict"] = ("EXERCISED AND ABSORBED"
                            if r["stdout_differs_from_unmutated"]
                            and r["exit"] == 0
                            else "CAUGHT" if r["exit"] == 1
                            else "NEVER EXERCISED")

        print()
        print("=" * 78)
        print("PART 2 -- THE MATRIX")
        print("=" * 78)
        print(f"{'mutation':<10} " + "  ".join(f"{g:>16}" for g in gates)
              + "   mine?  repaired-column verdict")
        for mutation in wanted:
            cells = []
            for g in gates:
                r = next((x for x in results if x["mutation"] == mutation
                          and x["gate"] == g and x["part"] == 2), None)
                cells.append("        -       " if r is None else
                             f"exit {r['exit']} {'ok' if r['PASS'] else 'BAD'}"
                             .rjust(16))
            rep = next((x for x in results if x["mutation"] == mutation
                        and x["gate"] == "repaired" and x["part"] == 2), None)
            mine = MUTATIONS.get(mutation, {}).get("mine", False)
            print(f"{mutation:<10} " + "  ".join(cells)
                  + f"   {'YES' if mine else ' - ':<5}  "
                  + (rep.get("verdict", "") if rep else ""))

    # ------------------------------------------------------------- part 3 ---
    if not args.skip_part3:
        p3_gates = [g for g in gates if g != "pre-widening"]
        for tag, spec in sorted(PART3.items()):
            mu = MUTATIONS[spec["mutation"]]
            for gate_variant in p3_gates:
                want = spec["expect"][gate_variant]
                r = run_case(spec["mutation"], gate_variant, sources,
                             regen=True)
                r["mutation"] = tag
                r["expected_exit"] = want
                r["PASS"] = (r["exit"] == want)
                r["desc"] = (f"{spec['mutation']} AND a regenerated dataset -- "
                             f"{mu['desc']}")
                r["question"] = spec["question"]
                r["part"] = 3
                show(tag, gate_variant, want, r["desc"], r)
                results.append(r)

        print()
        print("=" * 78)
        print("PART 3 -- MUTATE AND REGENERATE: where does the reference come")
        print("          from?")
        print("=" * 78)
        for tag in sorted(PART3):
            spec = PART3[tag]
            print(f"  {tag} ({spec['mutation']} + regeneration): "
                  f"{spec['question']}")
            for g in p3_gates:
                plain = next((x for x in results
                              if x["mutation"] == spec["mutation"]
                              and x["gate"] == g and x["part"] == 2), None)
                regen = next((x for x in results if x["mutation"] == tag
                              and x["gate"] == g), None)
                if regen is None:
                    continue
                pl = "?" if plain is None else plain["exit"]
                print(f"      {g:<16} mutation alone: exit {pl}   "
                      f"mutation + regenerated rows: exit {regen['exit']}")
        print()
        print("  READ IT AS: a row that goes 1 -> 0 has a reference that is a "
              "STORED\n  NUMBER produced by the same corpus.  A row that stays "
              "1 has a reference\n  that is a THEOREM, and regeneration cannot "
              "move it.")

    for r in results:
        if not r["PASS"]:
            failures.append(
                f"PART {r['part']}: {r['mutation']} on the {r['gate']} gate "
                f"exited {r['exit']}, expected {r['expected_exit']}")
    report["cases"] = results
    report["ALL_ROWS_AS_EXPECTED"] = all(r["PASS"] for r in results)
    _write(report, failures)
    return 1 if failures else 0


def _write(report, failures):
    out = os.path.join(REPO, "data", "onethird-mg4f9b-route-axis.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {os.path.relpath(out, REPO)}")
    if failures:
        print("\nROWS DISAGREE WITH WHAT THIS PROBE ASSERTS:")
        for m in failures:
            print(f"  - {m}")
    else:
        print("\nEvery row behaves as asserted.")


if __name__ == "__main__":
    sys.exit(main())
