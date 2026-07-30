#!/usr/bin/env python3
"""
mg-bd53 -- INDEPENDENT AUDIT probe for the mg-75f0 gate widening.

mg-75f0 widened `scripts/onethird_mg2c34_n7_overlap_test.py`'s identity check
from four hand-listed fields to the WHOLE committed mg-8b64 reference row, and
added CONTROL E and CONTROL F.  Its acceptance run reports the widened gate
firing on five mutations neither mg-60d3 nor mg-5ad1 used.

The audit question the ticket set is not "does it catch M3 and M4" and not
"does it catch mg-75f0's own five".  It is: DOES THE WIDENED GATE CATCH A
MUTATION IT WAS NOT BUILT FROM, chosen by somebody who did not build it?  This
file is that test, built from scratch rather than from mg-75f0's demo, and it
carries the answer in both directions.

THE SIX MUTATIONS, none of them mg-75f0's, none of them mg-5ad1's except the
two reproduced deliberately.

  CAUGHT (the widening generalises -- these are the honest positives)
    A1  `standard_block_and_lambda`'s eigenvalue selector argmax -> argmin, in
        mgb0a6.  Moves `lambda_std` AND `transport_gap`.  `transport_gap` is
        moved by NONE of M3/M5/M6/M7/M8/M9, so it is coverage mg-75f0 did not
        measure.
    A2  `bk_frozen_pair`'s MAX-BIAS selector max -> min, in mg-8b64.  Moves
        `max_bias`, again a field no mg-75f0 row touches.  A third selector in
        the same function as M3 (frozen) and M5 (minphi), so it is also the
        direct test of whether the widening covers that function or only the
        two lines of it that have been mutated before.

  NOT CAUGHT (the class, still open, and one of them a REGRESSION)
    B1  mg-4a86's OWN `lambda_std`, `np.max(w)` -> `np.min(w)`.  ONE CHARACTER.
        THE PRE-WIDENING GATE CATCHES THIS AND THE WIDENED GATE DOES NOT.
        Before mg-75f0, `rec["match_lambda_std"]` compared the gate's own
        recomputation -- which goes through mg-4a86's `lambda_std` -- against
        the committed reference.  After mg-75f0 that key is an ALIAS of the
        row-wide comparison, which recomputes `lambda_std` through mg-8b64's
        `analyze_poset` -> `transport_summary` -> mgb0a6's
        `standard_block_and_lambda`: a DIFFERENT implementation, in a different
        module.  So mg-4a86's route lost its only comparison.  The widened gate
        prints `lam_std=-0.048288466 (ref 0.7850482917286934)` and `match=
        True/True/True` on the same line and exits 0.  mg-75f0 noticed this
        exact hazard for `bk_lambda2` and kept its second route with a comment
        saying so; `lambda_std` has the identical two-route structure and was
        not given the same treatment.
    C1  `bk_cheeger_exhaustive`'s volume normalisation min(k,m-k) ->
        max(k,m-k), in mg-8b64.  Moves `h_bk_exhaustive` in 54 of the 1091
        committed rows.  Invisible because the census is per-ROW: the seven
        identity posets are n = 7, their rows have 23 fields, and these two
        fields exist only on the small-|L| rows.  Byte-identical stdout on both
        gate columns.
    C2  the gate's own `frozen_pair_indicator` loses its centring.  Moves
        `frozen_pair_overlap_with_U` -- THE quantity ledger claim 8 rests on,
        and the quantity mg-5ad1 named as the reason M3 mattered -- from
        0.8072/0.8094/0.8096 to 0.9036/0.9076/0.9048, printed by the gate, exit
        0 on BOTH columns.

  REPRODUCED, to check the acceptance run rather than take it on report
    M3  mg-5ad1's frozen-pair selector flip.
    M4  mg-5ad1's rank-filter drop.

PART 1 is fast (no gate runs) and is the structural half of B1: it asks, of
each of the four quantities the pre-widening gate compared, whether the gate's
OWN independent recomputation still participates in `_identity_row_ok`.

PART 2 is the matrix: fourteen full `--no-sweep` gate runs in isolated trees,
one source-level edit each with an anchor-count assertion, the pre-widening
gate the real source at the same pinned `af7fc2df` mg-75f0 uses.

WHAT AN `EXPECTED` FLIP MEANS.  The B1/C1/C2 rows assert exit 0 on the widened
gate because that is what was MEASURED at audit time, not because it is
desirable.  If a later ticket repairs any of them, this file goes red on that
row -- which is the signal to re-point the row at the repair, exactly as
mg-7db4's battery re-pointed N2.  A row flipping 0 -> 1 here is good news
reported as a failure, and the docstring saying so is the difference between
that and a broken audit.

Run:  /usr/bin/python3 scripts/onethird_mgbd53_widening_audit_probe.py
      (numpy required; ~8 min -- fourteen full runs of the CI gate)
      --only A1,B1        run a subset (the unmutated baselines are implied)
      --gates widened     one column only
      --part1-only        the fast structural half, seconds

Writes `data/onethird-mgbd53-widening-audit.json`.
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
DATASETS = ["onethird-mg8b64-L1b-bk-transport-transfer.json"]

# The same pin mg-75f0 uses, for the same reason: a merge-base baseline becomes
# the WIDENED gate once mg-75f0 lands, at which point the left column stops
# being a comparison.  Sharing the pin is deliberate -- a disagreement between
# the two files about what "pre-widening" means would make the columns
# incomparable, and this audit's B1 row is a statement ABOUT that column.
PRE_WIDENING_REV = "af7fc2df"

MG4A86_SD = "scripts/onethird_mg4a86_standard_dominance_target_audit.py"
MG4A86_OV = "scripts/onethird_mg4a86_sdquant_overlap.py"
MGB0A6 = "scripts/onethird_mgb0a6_spectral_killshot_probe.py"
MG8B64 = "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py"

MUTATIONS = {
    "A1": {
        "desc": "standard_block_and_lambda's eigenvalue selector argmax -> "
                "argmin: lambda_std reports the SLOWEST mode on H instead of "
                "the dominant one.  Moves lambda_std and transport_gap",
        "moves": ["lambda_std", "transport_gap"],
        "why_this_one": "transport_gap is moved by none of mg-75f0's seven "
                        "rows, so this is field coverage its acceptance run "
                        "did not measure",
        "file": MGB0A6,
        "old": "    idx = int(np.argmax(w))",
        "new": "    idx = int(np.argmin(w))",
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 1},
    },
    "A2": {
        "desc": "bk_frozen_pair's MAX-BIAS selector max -> min: the most "
                "unbalanced incomparable pair becomes the most balanced one.  "
                "Moves max_bias",
        "moves": ["max_bias"],
        "why_this_one": "the THIRD selector in the function M3 and M5 mutate.  "
                        "If the widening covered those two lines rather than "
                        "the function, this is where it shows",
        "file": MG8B64,
        "old": '    maxbias = max(pairs, key=lambda pc: max(pc["p"], 1 - pc["p"]))',
        "new": '    maxbias = min(pairs, key=lambda pc: max(pc["p"], 1 - pc["p"]))',
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 1},
    },
    "B1": {
        "desc": "mg-4a86's OWN lambda_std, np.max(w) -> np.min(w).  The "
                "pre-widening gate CATCHES this; the widened gate does not.  "
                "A coverage REGRESSION, not a pre-existing gap",
        "moves": ["-- nothing in mg-8b64's recomputation: the mutated route is "
                  "mg-4a86's, which the widened gate no longer compares"],
        "why_this_one": "mg-75f0 kept bk_lambda2's second route on the stated "
                        "reasoning that a mutation in EITHER walk matrix must "
                        "be fatal.  lambda_std has the identical two-route "
                        "structure (mg-4a86's own implementation vs mgb0a6's "
                        "standard_block_and_lambda) and did not get the same "
                        "treatment",
        "file": MG4A86_SD,
        "old": "    return float(np.max(w))",
        "new": "    return float(np.min(w))",
        "count": 1,
        "expect": {"pre-widening": 1, "widened": 0},
    },
    "C1": {
        "desc": "bk_cheeger_exhaustive's volume normalisation min(k,m-k) -> "
                "max(k,m-k) -- M7's shape, a different function.  Moves "
                "h_bk_exhaustive in 54 of the 1091 committed mg-8b64 rows",
        "moves": ["h_bk_exhaustive", "h_bk_argmin_is_pair_cut"],
        "why_this_one": "the census is per-ROW, not per-DATASET.  These two "
                        "fields exist only on rows with |L| <= 15; the seven "
                        "identity posets are n = 7 and their rows have 23 "
                        "fields, so the fields are compared at zero posets and "
                        "part B1's '0 silently uncompared' cannot see them",
        "file": MG8B64,
        "old": "        mn = min(k, m - k)\n        boundary",
        "new": "        mn = max(k, m - k)\n        boundary",
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 0},
    },
    "C2": {
        "desc": "the gate's own frozen_pair_indicator loses its centring.  "
                "Moves frozen_pair_overlap_with_U -- the quantity ledger claim "
                "8 rests on -- from 0.807/0.809/0.810 to 0.904/0.908/0.905, "
                "printed, exit 0 on both columns",
        "moves": ["frozen_pair_overlap_with_U", "frozen_pairmode_capture",
                  "maxbias_pair_overlap_with_U", "maxbias_pairmode_capture"],
        "why_this_one": "the widening secured WHICH PAIR is chosen and not the "
                        "NUMBER computed from it.  mg-75f0 sec 7.2 states the "
                        "residual as 'a quantity the corpus computes but never "
                        "COMMITS'; this quantity IS committed -- in "
                        "data/onethird-mg2c34-n7-overlap.json, the gate's own "
                        "output, which the gate never reads back",
        "file": GATE,
        "old": "    f -= f.mean()\n",
        "new": "    f -= 0.0 * f.mean()\n",
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 0},
    },
    "M3": {
        "desc": "mg-5ad1's Theorem-E frozen-pair selector min -> max, "
                "reproduced here rather than taken on report",
        "moves": ["frozen_pair", "frozen_ratio", "frozen_phi_bk", "frozen_p",
                  "frozen_phi_t_image", "frozen_sep_k"],
        "why_this_one": "the acceptance run's primary row.  An audit that "
                        "accepts the fires on report has audited a table",
        "file": MG8B64,
        "old": '    frozen = min((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "new": '    frozen = max((pc for pc in pairs if pc["ratio"] is not None),\n'
               '                 key=lambda pc: pc["ratio"], default=None)',
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 1},
    },
    "M4": {
        "desc": "mg-5ad1's projector_U rank filter s > max(tol,1e-10) -> "
                "s > 0.0, reproduced",
        "moves": ["-- none; this is CONTROL E's case"],
        "why_this_one": "same reason as M3, and it is the row mg-75f0 says the "
                        "widening does NOT catch, so the claim that CONTROL E "
                        "does is worth measuring separately",
        "file": MG4A86_OV,
        "old": "    Q = Uu[:, s > max(tol, 1e-10)]",
        "new": "    Q = Uu[:, s > 0.0]",
        "count": 1,
        "expect": {"pre-widening": 0, "widened": 1},
    },
}


# ------------------------------------------------ part 1, the second routes ---
def part_1():
    """Of the four quantities the PRE-widening gate compared, how many still
    have the gate's own independent recomputation inside `_identity_row_ok`?

    This is B1 asked structurally, in milliseconds, so the answer does not
    depend on anyone thinking of the right mutation.  The pre-widening
    conjunction was

        rec["match_num_LE"]     = rec["num_LE"]  == ref["num_LE"]
        rec["match_lambda_std"] = |rec["lambda_std"] - ref["lambda_std"]| < 1e-9
        rec["match_delta"]      = |rec["delta"]      - ref["delta"]|      < 1e-9
        rec["match_bk_lambda2"] = |rec["lambda2_BK"] - ref["bk_lambda2"]| < 1e-9

    where every `rec[...]` on the right is the GATE's own recomputation.  After
    mg-75f0 the four `match_*` keys are assigned from the row-wide comparison,
    which recomputes through mg-8b64's `analyze_poset`, and only
    `match_bk_lambda2` is additionally ANDed with the gate's own route.  So the
    question is per quantity: are the two routes the same code?

      num_LE      both `P.linext_count()`             -- same route, nothing lost
      delta       gate: before_prob_dp + its own aggregation
                  mg-8b64: before_prob_dp + its own aggregation
                                                       -- shared primitive,
                                                          separate aggregation
      lambda_std  gate: mg-4a86's `lambda_std`
                  mg-8b64: mgb0a6's `standard_block_and_lambda`
                                                       -- DIFFERENT MODULES,
                                                          different code
      bk_lambda2  kept explicitly, both routes required
    """
    sys.path.insert(0, SCRIPTS)
    import onethird_mg2c34_n7_overlap_test as gate
    import onethird_mg4a86_standard_dominance_target_audit as mg4a86
    import onethird_mgb0a6_spectral_killshot_probe as mgb0a6

    print("=" * 78)
    print("PART 1 -- do the gate's OWN recomputations still gate anything?")
    print("=" * 78)

    fields = [f for _, f in gate.IDENTITY_LEGACY_FIELDS]
    # A `rec` whose row-wide comparison is perfect but whose four legacy keys
    # are all False.  If `_identity_row_ok` accepts it, the legacy keys -- and
    # therefore the gate's own recomputations behind three of them -- are inert.
    rec = {"field_matches": {f: True for f in fields},
           "match_num_LE": False, "match_lambda_std": False,
           "match_delta": False, "match_bk_lambda2": False}
    legacy_inert = bool(gate._identity_row_ok(rec))

    # ... and the converse, so this is a two-sided reading and not one.
    rec_bad = {"field_matches": dict({f: True for f in fields},
                                     lambda_std=False),
               "match_num_LE": True, "match_lambda_std": True,
               "match_delta": True, "match_bk_lambda2": True}
    rowwide_decides = not gate._identity_row_ok(rec_bad)

    # Are mg-4a86's lambda_std and mgb0a6's standard_block_and_lambda actually
    # two implementations?  Compare the source text, so this cannot be fooled
    # by one module re-exporting the other's name.
    src_a = inspect.getsource(mg4a86.lambda_std)
    src_b = inspect.getsource(mgb0a6.standard_block_and_lambda)
    two_routes = (mg4a86.lambda_std.__module__
                  != mgb0a6.standard_block_and_lambda.__module__
                  and src_a != src_b)

    routes = {
        "num_LE": {"gate_route": "Poset.linext_count", "row_route":
                   "Poset.linext_count", "independent": False},
        "lambda_std": {"gate_route":
                       "onethird_mg4a86_standard_dominance_target_audit."
                       "lambda_std",
                       "row_route": "onethird_mgb0a6_spectral_killshot_probe."
                                    "standard_block_and_lambda",
                       "independent": two_routes},
        "delta": {"gate_route": "gate.delta_and_frozen_pair (before_prob_dp "
                                "+ its own max-min aggregation)",
                  "row_route": "mg8b64.bk_frozen_pair (before_prob_dp + its "
                               "own max-min aggregation)",
                  "independent": True},
        "bk_lambda2": {"gate_route": "mg4a86.bk_walk_matrix (kept, ANDed)",
                       "row_route": "mg8b64.bk_walk_matrix",
                       "independent": True},
    }
    still_gated = {"num_LE": False, "lambda_std": False, "delta": False,
                   "bk_lambda2": True}

    print(f"  the four legacy match_* keys are inert  : {legacy_inert}")
    print(f"  the row-wide comparison is what decides : {rowwide_decides}")
    print(f"  mg-4a86 lambda_std and mgb0a6 standard_block_and_lambda are")
    print(f"  two distinct implementations            : {two_routes}")
    print()
    print(f"  {'quantity':<12} {'independent 2nd route':>22}  "
          f"{'still gated after mg-75f0':>26}")
    for k, v in routes.items():
        print(f"  {k:<12} {str(v['independent']):>22}  "
              f"{str(still_gated[k]):>26}")
    lost = sorted(k for k, v in routes.items()
                  if v["independent"] and not still_gated[k])
    print()
    print(f"  quantities that HAD an independent second route and no longer")
    print(f"  have it gated: {lost}")

    failures = []
    if not legacy_inert:
        failures.append(
            "PART 1: the four legacy match_* keys are NOT inert -- the "
            "structure this audit measured has changed.  Re-derive B1 before "
            "trusting the matrix below")
    if not rowwide_decides:
        failures.append(
            "PART 1: the row-wide comparison does not decide _identity_row_ok; "
            "the gate's identity check is not what this audit measured")
    if not two_routes:
        failures.append(
            "PART 1: mg-4a86's lambda_std and mgb0a6's "
            "standard_block_and_lambda are no longer two implementations -- "
            "if they have been unified, B1 is no longer a coverage statement "
            "and this row must be re-derived")
    return {"legacy_match_keys_are_inert": legacy_inert,
            "row_wide_comparison_decides": rowwide_decides,
            "lambda_std_has_two_implementations": two_routes,
            "routes": routes,
            "still_gated_after_mg75f0": still_gated,
            "lost_second_route": lost}, failures


# --------------------------------------------------------- part 2, the trees ---
def pre_widening_source():
    show = subprocess.run(["git", "show", f"{PRE_WIDENING_REV}:{GATE}"],
                          cwd=REPO, capture_output=True, text=True)
    if show.returncode != 0:
        raise SystemExit(f"cannot read {GATE} at {PRE_WIDENING_REV}: "
                         f"{show.stderr.strip()}")
    return show.stdout


def build_tree(root, mutation, gate_variant, pre_src):
    os.makedirs(os.path.join(root, "scripts"))
    os.makedirs(os.path.join(root, "data"))
    for fn in os.listdir(SCRIPTS):
        if fn.endswith(".py"):
            shutil.copy2(os.path.join(SCRIPTS, fn),
                         os.path.join(root, "scripts", fn))
    for fn in DATASETS:
        shutil.copy2(os.path.join(REPO, "data", fn),
                     os.path.join(root, "data", fn))
    if gate_variant == "pre-widening":
        with open(os.path.join(root, GATE), "w") as f:
            f.write(pre_src)
    elif gate_variant != "widened":
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


# Thread pinning, and it is not cosmetic.  Uncontended, the gate's compared
# float fields reproduce to max|diff| = 0.00e+00; single-threaded BLAS on the
# same tree gives 8.88e-16 at #52 and 9.99e-16 at #88.  Six orders under the
# 1e-9 tolerance either way, so nothing is at risk -- but the stdout digest
# below is a byte comparison, and unpinned threads move those digits run to
# run, which would make "the mutation moved nothing" unmeasurable.
PINNED = {"OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1",
          "MKL_NUM_THREADS": "1", "VECLIB_MAXIMUM_THREADS": "1",
          "NUMEXPR_NUM_THREADS": "1"}


def run_case(mutation, gate_variant, pre_src):
    root = tempfile.mkdtemp(prefix=f"mgbd53-{mutation}-{gate_variant}-")
    try:
        applied = build_tree(root, mutation, gate_variant, pre_src)
        proc = subprocess.run(["/usr/bin/python3", GATE, "--no-sweep"],
                              cwd=root, capture_output=True, text=True,
                              env=dict(os.environ, **PINNED))
        fails, ident, meas = extract(proc.stdout)
        return {"mutation": mutation, "gate": gate_variant, "applied": applied,
                "exit": proc.returncode, "gate_failures": fails,
                "identity_lines": ident, "measured_lines": meas,
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
        if s.startswith("enum-n7-#") and "lam2_BK=" in s:
            ident[s.split()[0]] = s
        elif s.startswith("enum-n7-#") and len(s.split()) == 12:
            f = s.split()
            meas[f[0]] = {"dim_U": f[2], "lam_std": f[5], "c_max": f[7],
                          "null": f[9], "frozen_pairmode_capture": f[10],
                          "frozen_pair_overlap_with_U": f[11]}
    return fails, ident, meas


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--gates", default="pre-widening,widened")
    ap.add_argument("--part1-only", action="store_true")
    args = ap.parse_args()

    p1, failures = part_1()
    report = {"what": "mg-bd53 independent audit of the mg-75f0 gate widening: "
                      "does the widened gate catch a mutation it was not built "
                      "from, and did the widening cost any coverage?",
              "pre_widening_gate_revision": PRE_WIDENING_REV,
              "part_1_second_routes": p1}

    if not args.part1_only:
        pre_src = pre_widening_source()
        if pre_src == open(os.path.join(REPO, GATE)).read():
            print("  !! the two gate columns are the SAME FILE -- this run "
                  "cannot demonstrate anything")
        gates = [g for g in args.gates.split(",") if g]
        wanted = ["none"] + (sorted(MUTATIONS) if not args.only
                             else [m for m in args.only.split(",")
                                   if m != "none"])
        results = []
        for mutation in wanted:
            for gate_variant in gates:
                mu = MUTATIONS.get(mutation, {"desc": "unmutated instrument",
                                              "expect": {g: 0 for g in gates}})
                want = mu["expect"][gate_variant]
                print()
                print("-" * 78)
                print(f"CASE  {mutation:<5} gate={gate_variant:<13} "
                      f"(expect exit {want})")
                print(f"      {mu['desc']}")
                print("-" * 78, flush=True)
                r = run_case(mutation, gate_variant, pre_src)
                r["expected_exit"] = want
                r["PASS"] = (r["exit"] == want)
                r["desc"] = mu["desc"]
                r["moves_reference_fields"] = mu.get("moves", [])
                r["why_this_one"] = mu.get("why_this_one", "")
                for f in r["gate_failures"][:3]:
                    print(f"      GATE FAILURE: {f[:160]}")
                if not r["gate_failures"]:
                    print("      (no gate failure reported)")
                if not r["PASS"] and r["stderr_tail"]:
                    print(r["stderr_tail"][-800:])
                print(f"      --> exit {r['exit']} (expected {want})  "
                      f"{'OK' if r['PASS'] else 'AUDIT ROW DISAGREES'}",
                      flush=True)
                results.append(r)

        # Did the mutated run move a printed byte of the same column's
        # unmutated run?  Same taxonomy mg-75f0 uses, applied to both columns.
        base = {g: next((r["stdout_sha256"] for r in results
                         if r["mutation"] == "none" and r["gate"] == g), None)
                for g in gates}
        for r in results:
            if r["mutation"] == "none" or base.get(r["gate"]) is None:
                continue
            r["stdout_differs_from_unmutated"] = (
                r["stdout_sha256"] != base[r["gate"]])
            r["verdict"] = ("EXERCISED AND ABSORBED" if
                            r["stdout_differs_from_unmutated"] and r["exit"] == 0
                            else "CAUGHT" if r["exit"] == 1
                            else "NEVER EXERCISED")

        print()
        print("=" * 78)
        print("THE MATRIX")
        print("=" * 78)
        print(f"{'mutation':<10} " + "  ".join(f"{g:>14}" for g in gates)
              + "   what it means")
        for mutation in wanted:
            cells = []
            for g in gates:
                r = next((x for x in results if x["mutation"] == mutation
                          and x["gate"] == g), None)
                cells.append("       -      " if r is None else
                             f"exit {r['exit']} {'ok' if r['PASS'] else 'BAD'}"
                             .rjust(14))
            note = ""
            if mutation != "none":
                w = next((x for x in results if x["mutation"] == mutation
                          and x["gate"] == "widened"), None)
                if w is not None:
                    note = w.get("verdict", "")
            print(f"{mutation:<10} " + "  ".join(cells) + f"   {note}")

        for r in results:
            if not r["PASS"]:
                failures.append(
                    f"PART 2: {r['mutation']} on the {r['gate']} gate exited "
                    f"{r['exit']}, audit measured {r['expected_exit']}.  If "
                    f"this row went 0 -> 1 the defect was REPAIRED: re-point "
                    f"the row rather than deleting it")
        report["cases"] = results
        report["ALL_ROWS_AS_MEASURED"] = all(r["PASS"] for r in results)

    out = os.path.join(REPO, "data", "onethird-mgbd53-widening-audit.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print()
    print(f"wrote {os.path.relpath(out, REPO)}")

    if failures:
        print("\nAUDIT ROWS DISAGREE WITH WHAT WAS MEASURED:")
        for m in failures:
            print(f"  - {m}")
        return 1
    print("\nEvery row behaves as the audit measured it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
