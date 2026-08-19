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
  mg-8b64 reference row against the fields the gate's identity check actually
  compares -- taken FROM THE GATE ITSELF (its own comparison function, called
  here), never from a list maintained in this file.

  When mg-5ad1 first ran it, the answer was 4 of 22.  mg-75f0 widened the gate
  to the whole row, and part B is now what keeps it there: every field must be
  compared or excluded-with-a-reason (B1), every field must be able to make the
  gate FAIL when perturbed (B2), and a field newly added to the reference row
  must be picked up automatically and fail (B3).  B3 is the one that matters
  most: a hand-maintained census goes wrong, silently, the first time someone
  adds a field -- the same defect one turn later.

PART C -- IS THE F3 PATTERN STILL LIVE?  `frozen_pair` was one of the uncompared
  reference fields, and the gate recomputes it (via mg-8b64's own
  `bk_frozen_pair`) to produce `frozen_pairmode_capture` and
  `frozen_pair_overlap_with_U` -- the two quantities ledger claim 8 rests on.
  Checked here: the corpus's argmin-ratio selector reproduces the committed
  `frozen_pair` at every named poset (so a comparison IS available), and
  flipping that one selector to argmax moves the pair at every named poset (so
  the selector is load-bearing).  mg-5ad1 confirmed separately that the flip
  passes the full CI gate with exit 0.  mg-75f0 closed that: `frozen_pair` is
  now one of the 22 compared fields, and part B2 proves perturbing it fires.

PART D -- CAN EACH OF THE GATE'S OTHER PREDICATES FAIL?  Same question as B2,
  asked of CONTROL B, CONTROL E and CONTROL F: each is handed a row it must
  accept and a row it must reject.  mg-5ad1 finding 2 was that the gate's
  proof-of-firing is a ~12-minute hardcoded matrix over two fixed mutations that
  nothing runs; this is the part of it that is fast enough to run every time.

Exits NON-ZERO if any check fails.  Order-seconds; no sweep, no enumeration
beyond the corpus's own n=7 both-connected list.

Run:  /usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py
      (numpy required; bare python3 on this host has no numpy)

Writes `data/onethird-mg5ad1-gate-blindspot-probe.json`.
"""

import os
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
def _perturb(v):
    """A value guaranteed different from `v`, of a shape the comparison will
    actually meet.  Deliberately LARGE for numbers: the point is to prove the
    field is looked at, not to probe the tolerance."""
    if isinstance(v, bool):
        return not v
    if isinstance(v, (int, float)):
        return float(v) + 1.0
    if isinstance(v, list):
        return list(v) + [-1]
    if isinstance(v, str):
        return v + "-PERTURBED"
    if v is None:
        return 0.0
    return "PERTURBED"


def part_B():
    """Does the gate's identity check look at EVERY field of the committed row?

    mg-5ad1's RED finding was measured HERE, by this part: the conjunction
    compared 4 of the committed row's 22 fields, and eighteen -- frozen_pair
    among them -- were opened and never looked at.  mg-75f0 widened the
    comparison to the whole row.  This part is what stops that from silently
    un-widening, and it is deliberately NOT a hand-maintained field list: a
    hand-maintained census becomes wrong the first time someone adds a field,
    silently, which is the SAME defect one turn later.

    Three things are checked, in increasing strength:

      B1  CENSUS.  Every field of the committed reference row is either
          COMPARED by the gate or listed in the gate's own
          `IDENTITY_EXCLUDED_REF_FIELDS` -- with a reason, in the source, next
          to the exclusion.  Reviewable exclusions, not silent ones.  Stale
          exclusions (naming a field that no longer exists) fail too.
      B2  PER-FIELD FIRING.  For EACH field, perturb that field alone in the
          committed row and require the gate's own `_identity_row_ok` to return
          False.  A field that cannot make the gate fail is a field the gate is
          not checking, whatever the census says.
      B3  ANTI-DRIFT CANARY.  Hand the gate's comparison a reference row with a
          field name it has never seen.  The new field must be compared
          automatically, and -- because the row builder does not produce it --
          must FAIL.  This is the "someone adds a field to the mg-8b64 row"
          case, tested rather than trusted.

    The gate's own functions are imported and CALLED, which is strictly stronger
    than parsing its source: a census that agrees with the source but not with
    the behaviour is the defect it is supposed to catch."""
    import onethird_mg2c34_n7_overlap_test as gate      # cheap: no work at import

    with open(os.path.join(REPO, "data", REF)) as f:
        ref_rows = {r["name"]: r for r in json.load(f)["rows"]}
    ref = ref_rows[NAMED[0]]
    present = sorted(ref)
    excluded = dict(gate.IDENTITY_EXCLUDED_REF_FIELDS)
    compared = sorted(gate.identity_field_comparisons(ref, ref)[0])

    print()
    print("=" * 78)
    print("PART B -- does the gate's identity check look at EVERY field of the")
    print("          committed mg-8b64 reference row?")
    print("=" * 78)
    print(f"  reference fields present : {len(present)}")
    print(f"  compared by the gate     : {len(compared)}")
    print(f"  excluded, with a reason  : {len(excluded)}")
    for k, why in sorted(excluded.items()):
        print(f"      {k}: {why}")
    uncompared = [k for k in present if k not in compared and k not in excluded]
    print(f"  neither compared nor excluded : {len(uncompared)}  {uncompared}")

    failures = []
    # ---- B1 census ---------------------------------------------------------
    for k in uncompared:
        failures.append(f"PART B1: reference field {k!r} is neither compared by "
                        f"the gate's identity check nor listed in "
                        f"IDENTITY_EXCLUDED_REF_FIELDS with a reason -- this is "
                        f"the mg-09ea F3 / mg-5ad1 defect, one field later")
    for k, why in excluded.items():
        if k not in present:
            failures.append(f"PART B1: exclusion {k!r} names a field the "
                            f"committed reference row no longer has -- the "
                            f"exclusion list has drifted")
        if not isinstance(why, str) or len(why.strip()) < 20:
            failures.append(f"PART B1: exclusion {k!r} has no stated reason; "
                            f"an exclusion with a reason is reviewable, a bare "
                            f"one is not")
    if "bk_lambda2" not in compared:
        failures.append("PART B1: bk_lambda2 is NOT compared -- the mg-60d3 F3 "
                        "repair is absent")
    if "frozen_pair" not in compared:
        failures.append("PART B1: frozen_pair is NOT compared -- mg-5ad1's M3 "
                        "(the Theorem-E selector flip that moves the quantity "
                        "ledger claim 8 rests on) is live again")

    # ---- B2 per-field firing ----------------------------------------------
    print()
    print("  PER-FIELD FIRING -- perturb one field of the committed row, does")
    print("  the gate's own _identity_row_ok go False?")
    firing = {}
    for k in compared:
        bad = dict(ref)
        bad[k] = _perturb(ref[k])
        matches, _ = gate.identity_field_comparisons(ref, bad)
        fires = not gate._identity_row_ok({"field_matches": matches})
        firing[k] = fires
        if not fires:
            failures.append(f"PART B2: perturbing {k!r} does NOT make the "
                            f"gate's identity check fail -- the field is "
                            f"compared in name only")
    nfire = sum(1 for v in firing.values() if v)
    print(f"    {nfire}/{len(compared)} fields FIRE the gate when perturbed"
          + ("" if nfire == len(compared)
             else "  <-- " + ",".join(k for k, v in firing.items() if not v)))

    # ---- B3 anti-drift canary ---------------------------------------------
    canary = "mg75f0_canary_field_the_row_builder_does_not_produce"
    grown = dict(ref)
    grown[canary] = 1.2345
    cm, _ = gate.identity_field_comparisons(ref, grown)
    canary_compared = canary in cm
    canary_fails = canary_compared and cm[canary] is False
    print(f"  ANTI-DRIFT CANARY -- a field the gate has never seen: "
          f"compared={canary_compared}  fails={canary_fails}")
    if not canary_compared:
        failures.append("PART B3: a field ADDED to the mg-8b64 reference row is "
                        "NOT picked up by the gate's comparison -- the "
                        "comparison is a hardcoded list again, and will go "
                        "silently stale")
    elif not canary_fails:
        failures.append("PART B3: a reference field the row builder does not "
                        "produce is treated as MATCHING -- a missing "
                        "recomputation must be a failure, not a pass")

    return {"reference_fields_present": present,
            "reference_fields_compared": compared,
            "reference_fields_excluded": excluded,
            "reference_fields_uncompared": uncompared,
            "per_field_firing": firing,
            "fields_that_fire": nfire,
            "anti_drift_canary_compared": canary_compared,
            "anti_drift_canary_fails": canary_fails}, failures


# ------------------------- part D, do the gate's OTHER predicates fire? -------
def part_D():
    """The same question as part B, asked of every remaining gate predicate.

    mg-5ad1 finding 2: the gate's proof-of-firing (`onethird_mg60d3_gate_
    mutation_demo.py`) is a hardcoded 2x3 matrix over two fixed mutations, takes
    ~12 min, and is run by nothing.  It answers "do the two known repairs still
    fire?", not "can each predicate fail at all?".  This part answers the second
    question in milliseconds, on synthetic rows, so it can live in CI: each
    predicate is handed a row it must ACCEPT and a row it must REJECT, and the
    rejection is the mg-4ad1 lesson applied to the predicates themselves."""
    import onethird_mg2c34_n7_overlap_test as gate

    good_antichain = {"c_max": 1.0, "c_min": 1.0, "dim_U": 10,
                      "dim_U_known": 10}
    good_proj = {"n": 7, "num_LE": 360, "dim_U": 24,
                 "null_random_subspace": 24 / 360}
    good_two = {"dim_eigenspace": 2, "c_max": 0.5, "c_min": 0.5}

    cases = [
        # (predicate, label, row, must_accept, why this row is the right probe)
        (gate._antichain_row_ok, "CONTROL B", good_antichain, True,
         "the known answer on the antichain"),
        (gate._antichain_row_ok, "CONTROL B / c_max",
         dict(good_antichain, c_max=0.5), False, "favourable reading broken"),
        (gate._antichain_row_ok, "CONTROL B / c_min (mg-09ea F4)",
         dict(good_antichain, c_min=0.0), False,
         "M2's signature: c_max survives a shrink of U, c_min does not"),
        (gate._antichain_row_ok, "CONTROL B / dim U (mg-5ad1 M4)",
         dict(good_antichain, dim_U=16), False,
         "M4's signature: the rank filter admits null directions, so U inflates "
         "to n^2 and both readings still say 1"),
        (gate._projector_row_ok, "CONTROL E", good_proj, True,
         "dim U inside its structural bound and proper"),
        (gate._projector_row_ok, "CONTROL E / bound (mg-5ad1 M4)",
         dict(good_proj, dim_U=49), False,
         "dim U = n^2 > (n-1)^2+1 is not a rank the one-particle span can have"),
        (gate._projector_row_ok, "CONTROL E / vacuity (mg-5ad1 M4)",
         dict(good_proj, dim_U=21, num_LE=21, null_random_subspace=1.0), False,
         "U is the whole space, so c = null = 1 and the measurement is vacuous "
         "by sec 2's own criterion"),
        (gate._two_sided_row_ok, "CONTROL F", good_two, True,
         "degenerate lambda_2 with a reading-independent c"),
        (gate._two_sided_row_ok, "CONTROL F / split readings",
         dict(good_two, c_min=0.4), False, "the reported c is reading-dependent"),
        (gate._two_sided_row_ok, "CONTROL F / coverage gone",
         dict(good_two, dim_eigenspace=1), False,
         "lambda_2 simple, so this control would be vacuous -- the state "
         "mg-5ad1 finding 4 found the real-data two-sided check in"),
    ]

    print()
    print("=" * 78)
    print("PART D -- can each of the gate's predicates FAIL?  (the mg-4ad1")
    print("          lesson, applied to the predicates rather than the gate)")
    print("=" * 78)
    rows, failures = [], []
    for pred, label, row, must_accept, why in cases:
        got = bool(pred(row))
        ok = (got is must_accept)
        verdict = "PASS" if ok else "PROBE FAILED"
        print(f"  {label:<38} expect {'accept' if must_accept else 'REJECT':>6}"
              f"  got {'accept' if got else 'reject':>6}  {verdict}")
        print(f"      {why}")
        if not ok:
            failures.append(f"PART D: {label} "
                            f"{'rejected a legitimate row' if must_accept else 'ACCEPTED a row it must reject'} "
                            f"-- {why}")
        rows.append({"predicate": pred.__name__, "label": label,
                     "must_accept": must_accept, "accepted": got, "PASS": ok,
                     "why": why})
    return rows, failures


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
    D_rows, D_fail = part_D()
    failures = A_fail + B_fail + C_fail + D_fail

    report = {
        "what": "mg-5ad1 independent-audit probe for the mg-60d3 CI-gate "
                "repair (af7fc2df) to "
                "scripts/onethird_mg2c34_n7_overlap_test.py; extended by "
                "mg-75f0 into the standing control that keeps the gate's "
                "identity comparison from narrowing again",
        "part_A_control_B_two_sided": {
            "question": "does asserting c_min forbid a case the mathematics "
                        "permits, and is it non-vacuous?",
            "EIG_TOL": EIG_TOL, "rows": A_rows},
        "part_B_reference_field_census": B_census,
        "part_C_frozen_pair_selector": {
            "question": "is the F3 shape -- a committed reference value "
                        "fetched/available and never compared -- still live?",
            "rows": C_rows},
        "part_D_predicate_firing": {
            "question": "can each of the gate's predicates FAIL at all?",
            "rows": D_rows},
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
          f"fields are compared by the gate,")
    print(f"     {len(B_census['reference_fields_excluded'])} excluded with a "
          f"stated reason, 0 silently uncompared; "
          f"{B_census['fields_that_fire']}/"
          f"{len(B_census['reference_fields_compared'])} fire the gate when")
    print("     perturbed, and a field newly added to the reference row is "
          "compared automatically.")
    print("  C  the frozen-pair selector reproduces the committed reference "
          "at 5/5 posets")
    print("     (a comparison is available) and a one-character flip moves it "
          "at 5/5.")
    print(f"  D  all {len(D_rows)} predicate-firing probes agree: every gate "
          f"predicate accepts the row")
    print("     it must accept and REJECTS the row it must reject.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
