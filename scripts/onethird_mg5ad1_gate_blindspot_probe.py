#!/usr/bin/env python3
"""
mg-5ad1 -- INDEPENDENT AUDIT probe for the mg-60d3 CI-gate repair.

mg-60d3 (merged af7fc2df) repaired two controls in
`scripts/onethird_mg2c34_n7_overlap_test.py` that had been passing on mutations
that break numbers the deliverable asserts:

  F3  the identity check FETCHED the committed `bk_lambda2` reference and never
      compared it, so lambda_2^BK -- the denominator of R -- had no control that
      could fail.  Repaired by adding `match_bk_lambda2` to `_identity_row_ok`.
  F4  CONTROL B asserted c_max = 1 on the antichains and computed c_min without
      asserting it, so a shrunk U left the favourable reading at 1.  Repaired by
      adding `|c_min - 1| < 1e-8` to `_antichain_row_ok`.

`scripts/onethird_mg60d3_gate_mutation_demo.py` demonstrates that both repairs
FIRE.  That demonstration reproduces (mg-5ad1 rebuilt it by a disjoint route:
the actual pre-repair gate source at 87f0424 plus source-level mutations of the
defining modules, rather than the demo's in-process predicate substitution --
same 2x3 exit-code matrix, same figures).  This file is NOT that reproduction;
it is the part of the audit that is fast enough to be a standing control, and it
records the two questions the demonstration does not answer.

WHAT THIS FILE CHECKS, in order.

PART A -- IS THE F4 REPAIR SOUND IN BOTH DIRECTIONS?  A control tightened past
  what is proven starts failing on legitimate inputs and gets loosened by
  whoever hits it first, at which point the repair is gone.  So: rebuild the BK
  interchange matrix and the one-particle span on A_4, A_5, A_6 FROM DEFINITIONS
  here (no corpus import), and check that asserting c_min

    (i)  is NOT VACUOUS      -- dim of the lambda_2 eigenspace is n-1 > 1, so
                                c_min is a genuinely different reading;
    (ii) is NOT OVER-TIGHT   -- 1 - c_min < 1e-12, the eigenspace lies inside U;
    (iii) is NOT KNIFE-EDGE  -- the nearest eigenvalue EXCLUDED from the
                                eigenspace sits >= 1e6 * EIG_TOL away, so the
                                selection that produces c_min = 1 is not
                                sensitive to the degeneracy tolerance.

  Also confirmed independently: dropping ONE element's position block is a
  provable no-op on U (dim U unchanged), dropping TWO shrinks it by n-1 and
  collapses c_min to 0 -- the premise of M2, and the reason the gate is right
  not to fire on the one-element case.

PART B -- WHAT ELSE IS FETCHED AND DISCARDED?  F3's defect was structural: a
  committed reference value loaded into the report and never compared.  The
  repair added ONE field to the conjunction.  This part censuses the committed
  mg-8b64 reference row against the fields the gate's identity conjunction
  actually reads, parsed out of the gate source rather than hardcoded here.

PART C -- IS THE F3 PATTERN STILL LIVE?  `frozen_pair` is one of the uncompared
  reference fields, and the gate recomputes it (via mg-8b64's own
  `bk_frozen_pair`) to produce `frozen_pairmode_capture` and
  `frozen_pair_overlap_with_U` -- the two quantities ledger claim 8 rests on.
  Checked here: the corpus's argmin-ratio selector reproduces the committed
  `frozen_pair` at every named poset (so a comparison IS available), and
  flipping that one selector to argmax moves the pair at every named poset (so
  the selector is load-bearing).  mg-5ad1 confirmed separately that the flip
  passes the full CI gate with exit 0.

Exits NON-ZERO if any check fails.  Order-seconds; no sweep, no enumeration
beyond the corpus's own n=7 both-connected list.

Run:  /usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py
      (numpy required; bare python3 on this host has no numpy)

Writes `data/onethird-mg5ad1-gate-blindspot-probe.json`.
"""

import os
import re
import sys
import json
import itertools

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

from onethird_mgb0a6_spectral_killshot_probe import (  # noqa: E402
    enumerate_both_connected,
)
from onethird_mg8b64_L1b_bk_transport_transfer_probe import (  # noqa: E402
    bk_frozen_pair,
)

EIG_TOL = 1e-9            # the gate's degeneracy tolerance, quoted
GATE = "onethird_mg2c34_n7_overlap_test.py"
REF = "onethird-mg8b64-L1b-bk-transport-transfer.json"
NAMED = ["enum-n7-#3", "enum-n7-#20", "enum-n7-#600",
         "enum-n7-#945", "enum-n7-#809"]


# ------------------------------------------------- part A, from definitions --
def bk_interchange(n):
    """Lazy BK walk on L(antichain_n) = S_n, rebuilt from the definition: the
    adjacent-transposition interchange process on the n-vertex path, step
    1/(2(n-1)), laziness on the diagonal.  Deliberately NOT imported."""
    les = list(itertools.permutations(range(n)))
    idx = {p: i for i, p in enumerate(les)}
    m = len(les)
    W = np.zeros((m, m))
    step = 1.0 / (2 * (n - 1))
    for p in les:
        i0 = idx[p]
        for i in range(n - 1):
            q = list(p)
            q[i], q[i + 1] = q[i + 1], q[i]
            W[i0, idx[tuple(q)]] += step
    for i in range(m):
        W[i, i] += 1.0 - W[i].sum()
    return (W + W.T) / 2.0, les


def one_particle_basis(n, les, drop=()):
    """Orthonormal basis of U = span{sigma |-> 1[sigma(a) = x]}, optionally with
    the position blocks of the elements in `drop` omitted."""
    m = len(les)
    M = np.zeros((m, n * n))
    for r, p in enumerate(les):
        for a, x in enumerate(p):
            if x in drop:
                continue
            M[r, x * n + a] = 1.0
    Uu, s, _ = np.linalg.svd(M, full_matrices=False)
    tol = max(max(M.shape) * np.finfo(float).eps * (s[0] if len(s) else 0.0),
              1e-10)
    return Uu[:, s > tol]


def part_A():
    rows, failures = [], []
    print("=" * 78)
    print("PART A -- is asserting c_min on the antichain non-vacuous, true, and")
    print("          not knife-edge?  (mg-60d3 F4, audited in both directions)")
    print("=" * 78)
    print(f"{'poset':>12} {'|L|':>6} {'dimU':>5} {'dim_E':>6} {'1-c_max':>10} "
          f"{'1-c_min':>10} {'excl.gap':>10} {'margin/EIG_TOL':>15}")
    for n in (4, 5, 6):
        W, les = bk_interchange(n)
        ev, V = np.linalg.eigh(W)
        o = np.argsort(ev)[::-1]
        ev, V = ev[o], V[:, o]
        lam2 = ev[1]
        Q = one_particle_basis(n, les)
        PU = Q @ Q.T
        inside = [j for j in range(1, len(ev)) if abs(ev[j] - lam2) < EIG_TOL]
        outside = np.array([ev[j] for j in range(1, len(ev))
                            if abs(ev[j] - lam2) >= EIG_TOL])
        Vs = V[:, inside]
        w = np.linalg.eigvalsh(Vs.T @ PU @ Vs)
        excl = float(np.min(np.abs(outside - lam2)))
        row = {
            "poset": f"antichain-{n}", "n": n, "num_LE": len(les),
            "dim_U": int(Q.shape[1]), "dim_U_expected": (n - 1) ** 2 + 1,
            "lambda2_BK": float(lam2),
            "dim_eigenspace": len(inside), "dim_eigenspace_expected": n - 1,
            "c_max": float(w.max()), "c_min": float(w.min()),
            "eigenspace_internal_spread": float(ev[inside].max()
                                                - ev[inside].min()),
            "nearest_excluded_eigenvalue_gap": excl,
            "gap_over_EIG_TOL": excl / EIG_TOL,
        }
        print(f"  antichain-{n:<2} {len(les):>6} {Q.shape[1]:>5} "
              f"{len(inside):>6} {1 - w.max():>10.2e} {1 - w.min():>10.2e} "
              f"{excl:>10.3e} {excl / EIG_TOL:>15.2e}")
        # (i) non-vacuous: a one-dimensional eigenspace would make c_min == c_max
        if row["dim_eigenspace"] != n - 1 or row["dim_eigenspace"] < 2:
            failures.append(f"antichain-{n}: dim_E = {row['dim_eigenspace']}, "
                            f"expected {n - 1} (>1) -- the c_min assertion "
                            f"would be VACUOUS")
        if row["dim_U"] != row["dim_U_expected"]:
            failures.append(f"antichain-{n}: dim U = {row['dim_U']}, expected "
                            f"{row['dim_U_expected']} = (n-1)^2+1")
        # (ii) not over-tight: the eigenspace really does lie inside U
        if abs(1.0 - row["c_min"]) > 1e-12:
            failures.append(f"antichain-{n}: 1 - c_min = "
                            f"{1 - row['c_min']:.3e} > 1e-12 -- the F4 "
                            f"assertion forbids a case the walk permits")
        # (iii) not knife-edge in the degeneracy tolerance
        if row["gap_over_EIG_TOL"] < 1e6:
            failures.append(f"antichain-{n}: nearest excluded eigenvalue is "
                            f"only {row['gap_over_EIG_TOL']:.2e} x EIG_TOL "
                            f"away -- c_min = 1 is tolerance-sensitive")
        # the U-shrink premises, independently
        shrinks = {}
        for drop in ((0,), (0, 1)):
            Qs = one_particle_basis(n, les, drop=drop)
            ws = np.linalg.eigvalsh(Vs.T @ (Qs @ Qs.T) @ Vs)
            shrinks[",".join(map(str, drop))] = {
                "dim_U": int(Qs.shape[1]), "c_max": float(ws.max()),
                "c_min": float(ws.min())}
        row["U_shrunk"] = shrinks
        one, two = shrinks["0"], shrinks["0,1"]
        if one["dim_U"] != row["dim_U"] or abs(one["c_min"] - 1.0) > 1e-9:
            failures.append(f"antichain-{n}: dropping ONE element's block is "
                            f"not the no-op mg-60d3 claims (dim U "
                            f"{row['dim_U']} -> {one['dim_U']})")
        if two["dim_U"] != row["dim_U"] - (n - 1) or abs(two["c_min"]) > 1e-9:
            failures.append(f"antichain-{n}: dropping TWO blocks did not "
                            f"reproduce M2 (dim U -> {two['dim_U']}, "
                            f"c_min -> {two['c_min']:.3e})")
        print(f"{'':>14}drop element 0    : dim U = {one['dim_U']:>3}  "
              f"c_max = {one['c_max']:.9f}  c_min = {one['c_min']:.9f}"
              f"   (no-op on U)")
        print(f"{'':>14}drop elements 0,1 : dim U = {two['dim_U']:>3}  "
              f"c_max = {two['c_max']:.9f}  c_min = {two['c_min']:.9f}"
              f"   (M2: c_max survives, c_min does not)")
        rows.append(row)
    return rows, failures


# ------------------------------------- part B, the fetched-and-discarded census
def part_B():
    """Which committed reference fields does the identity conjunction read?

    Parsed out of the gate source so this census cannot drift away from the
    gate: `_identity_row_ok` names the match_* keys, and each match_* key is
    built from exactly one `ref[...]` lookup."""
    src = open(os.path.join(REPO, "scripts", GATE)).read()
    body = src.split("def _identity_row_ok(rec):")[1].split("\ndef ")[0]
    asserted = sorted(set(re.findall(r'rec\["(match_[a-zA-Z0-9_]+)"\]', body)))
    # each match_* key is built from exactly one `ref[...]` lookup; the
    # assignment may wrap across lines, so scan a bounded window after it
    compared_refs = set()
    for key in asserted:
        anchor = f'rec["{key}"]'
        for piece in src.split(anchor + " =")[1:]:
            compared_refs.update(re.findall(r'ref\["([a-zA-Z0-9_]+)"\]',
                                            piece[:240]))
    compared_refs = sorted(compared_refs)
    with open(os.path.join(REPO, "data", REF)) as f:
        ref_rows = {r["name"]: r for r in json.load(f)["rows"]}
    present = sorted(k for k in ref_rows[NAMED[0]] if k != "name")
    uncompared = [k for k in present if k not in compared_refs]
    print()
    print("=" * 78)
    print("PART B -- census: committed mg-8b64 reference fields vs the fields")
    print("          the gate's identity conjunction actually COMPARES")
    print("=" * 78)
    print(f"  predicates in _identity_row_ok : {len(asserted)}  {asserted}")
    print(f"  reference fields compared      : {len(compared_refs)}  "
          f"{compared_refs}")
    print(f"  reference fields present       : {len(present)}")
    print(f"  fetched-or-available and NOT compared : {len(uncompared)}")
    for k in uncompared:
        print(f"      {k}")
    failures = []
    if not asserted or not compared_refs:
        failures.append("PART B: could not parse the gate's identity "
                        "conjunction -- the census is not valid")
    if "bk_lambda2" not in compared_refs:
        failures.append("PART B: bk_lambda2 is NOT in the identity "
                        "conjunction -- the mg-60d3 F3 repair is absent")
    return {"predicates": asserted, "reference_fields_compared": compared_refs,
            "reference_fields_present": present,
            "reference_fields_uncompared": uncompared}, failures


# ------------------------------- part C, is the F3 pattern still live? --------
def part_C():
    with open(os.path.join(REPO, "data", REF)) as f:
        ref_rows = {r["name"]: r for r in json.load(f)["rows"]}
    Ps = enumerate_both_connected(7)
    print()
    print("=" * 78)
    print("PART C -- the frozen-pair selector: a comparison IS available, and")
    print("          the selector is load-bearing")
    print("=" * 78)
    print(f"{'poset':>14} {'committed':>11} {'argmin ratio':>13} "
          f"{'argmax ratio':>13}  {'agrees':>7} {'flip moves it':>14}")
    rows, failures = [], []
    for name in NAMED:
        i = int(name.split("#")[1])
        pairs = [pc for pc in bk_frozen_pair(Ps[i])["pairs"]
                 if pc["ratio"] is not None]
        lo = min(pairs, key=lambda pc: pc["ratio"])
        hi = max(pairs, key=lambda pc: pc["ratio"])
        committed = list(ref_rows[name]["frozen_pair"])
        argmin = [int(lo["x"]), int(lo["y"])]
        argmax = [int(hi["x"]), int(hi["y"])]
        agrees = argmin == committed
        moves = argmax != argmin
        print(f"{name:>14} {str(committed):>11} {str(argmin):>13} "
              f"{str(argmax):>13}  {str(agrees):>7} {str(moves):>14}")
        if not agrees:
            failures.append(f"{name}: the corpus argmin-ratio selector gives "
                            f"{argmin}, committed reference says {committed} "
                            f"-- no comparison is available after all")
        if not moves:
            failures.append(f"{name}: argmax == argmin, so flipping the "
                            f"selector is not a mutation at this poset")
        rows.append({"name": name, "committed_frozen_pair": committed,
                     "argmin_ratio_pair": argmin, "argmax_ratio_pair": argmax,
                     "argmin_ratio": float(lo["ratio"]),
                     "argmax_ratio": float(hi["ratio"]),
                     "reproduces_committed": agrees,
                     "flip_moves_the_pair": moves})
    return rows, failures


def main():
    A_rows, A_fail = part_A()
    B_census, B_fail = part_B()
    C_rows, C_fail = part_C()
    failures = A_fail + B_fail + C_fail

    report = {
        "what": "mg-5ad1 independent-audit probe for the mg-60d3 CI-gate "
                "repair (af7fc2df) to "
                "scripts/onethird_mg2c34_n7_overlap_test.py",
        "part_A_control_B_two_sided": {
            "question": "does asserting c_min forbid a case the mathematics "
                        "permits, and is it non-vacuous?",
            "EIG_TOL": EIG_TOL, "rows": A_rows},
        "part_B_reference_field_census": B_census,
        "part_C_frozen_pair_selector": {
            "question": "is the F3 shape -- a committed reference value "
                        "fetched/available and never compared -- still live?",
            "rows": C_rows},
        "failures": failures,
        "ALL_PASS": not failures,
    }
    out = os.path.join(REPO, "data", "onethird-mg5ad1-gate-blindspot-probe.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nwrote {os.path.relpath(out, REPO)}")

    if failures:
        print("\nPROBE FAILURES:")
        for m in failures:
            print(f"  - {m}")
        return 1
    print("\nAll checks PASSED:")
    print("  A  the F4 c_min assertion is non-vacuous (dim_E = n-1 > 1), true "
          "to < 1e-12,")
    print("     and not knife-edge (>= 1e6 x EIG_TOL of margin) on all three "
          "antichains.")
    print(f"  B  {len(B_census['reference_fields_compared'])} of "
          f"{len(B_census['reference_fields_present'])} committed reference "
          f"fields are in the identity conjunction.")
    print("  C  the frozen-pair selector reproduces the committed reference "
          "at 5/5 posets")
    print("     (a comparison is available) and a one-character flip moves it "
          "at 5/5.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
