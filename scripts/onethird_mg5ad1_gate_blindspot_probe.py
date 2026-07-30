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
  repair added ONE field to the conjunction.  When mg-5ad1 first ran this part,
  the answer was 4 OF 22.

  mg-75f0 widened the gate's identity check to the whole reference row, and this
  part is now what keeps it there: every field must be compared or
  excluded-with-a-reason (B1), every field must be able to make the gate FAIL
  when perturbed (B2), and a field newly ADDED to the reference row must be
  picked up automatically and fail (B3).  B3 is the one that matters most: a
  hand-maintained census goes wrong, silently, the first time someone adds a
  field -- the same defect one turn later.

  mg-75f0 ALSO CHANGED HOW THE CENSUS IS TAKEN, and the change is a
  strengthening rather than a retreat from the design property that put this
  file in CI.  As mg-5ad1 committed it, part B PARSED the census out of the gate
  source, so it could not drift from a hand-maintained list.  It could still
  drift from the gate's BEHAVIOUR, and did: see the mg-7db4 note preserved on
  `part_B` below, where a 240-character scan window borrowed a `ref[...]` lookup
  from the next line and reported a field as compared while the conjunction no
  longer compared it.  This part now IMPORTS THE GATE AND CALLS ITS OWN
  COMPARISON FUNCTION.  That is strictly stronger than parsing: there is no
  second representation of the census to disagree with the first, so the class
  of bug mg-7db4 found here cannot recur, and B2 measures firing rather than
  inferring it from source text.

PART C -- IS THE F3 PATTERN STILL LIVE?  `frozen_pair` was one of the uncompared
  reference fields, and the gate recomputes it (via mg-8b64's own
  `bk_frozen_pair`) to produce `frozen_pairmode_capture` and
  `frozen_pair_overlap_with_U` -- the two quantities ledger claim 8 rests on.
  Checked here: the corpus's argmin-ratio selector reproduces the committed
  `frozen_pair` at every named poset (so a comparison IS available), and
  flipping that one selector to argmax moves the pair at every named poset (so
  the selector is load-bearing).  mg-5ad1 confirmed separately that the flip
  passes the full CI gate with exit 0.

  mg-7db4 ADDED THE THIRD CHECK, and the reason is worth stating because it is
  the same defect one more time.  As mg-5ad1 committed it, Part C recomputed
  `argmin` over the pair list ITSELF and compared THAT to the committed
  reference.  `bk_frozen_pair`'s own `frozen` field -- the value the gate
  actually consumes -- was never read.  So M3, the audit's own primary witness
  (flip `min` -> `max` at the selector, leaving the pair LIST untouched), ran
  clean through this probe: verified, exit 0.  A census that says "a comparison
  IS available" and does not make it is the F3 shape verbatim, in the file
  written to report the F3 shape.  The `sel. ok` column is that comparison.

  mg-75f0 made `frozen_pair` one of the 22 fields the GATE itself compares, so
  part C is no longer the only thing standing between M3 and a green gate.  It
  is kept, and kept asserting, because it says something the gate's comparison
  does not: that the argmin-ratio selector is what REPRODUCES the committed
  reference, and that a flip still MOVES the pair -- i.e. that M3 remains a real
  mutation rather than one the corpus has drifted past.

PART D -- CAN EACH OF THE GATE'S OTHER PREDICATES FAIL?  The same question as
  B2, asked of CONTROL B, CONTROL E, CONTROL F and -- since mg-48dd -- CONTROL G
  and CONTROL H: each is handed a row it must accept and a row it must REJECT.
  mg-5ad1 finding 2 was that the gate's proof-of-firing is a ~12-minute hardcoded
  matrix over two fixed mutations that nothing ran; this is the part of that
  question which is fast enough to answer on every commit.

  THE LIST IS EXPLICIT, so it is exactly as complete as whoever last added a
  predicate made it.  mg-48dd added the two corpus-independent controls here
  rather than leaving them to its own unwired probe, because "all N
  predicate-firing probes agree" is read by a later author as "all of them", and
  a gate predicate sitting outside this battery is this arc's own defect one
  level in.  A predicate added to the gate and not added here is a hole this
  file cannot report.

Exits NON-ZERO if any check fails.  Order-seconds; no sweep, no enumeration
beyond the corpus's own n=7 both-connected list.

WHAT THIS FILE STILL DOES NOT COVER, so a green run is not read as more than it
is.  This probe never imports `projector_U` and never builds the gate's own U,
so it cannot see mg-5ad1's M4 (the rank filter dropped).  M4 IS now caught, by
the gate's CONTROL E in the same workflow -- but by the GATE, not by this file,
which is why `scripts/onethird_mg7db4_probe_mutation_battery.py` still records
M4 as a probe blind spot.  See docs/OneThird-mg7db4-GateDemo-Trigger.md for the
measured catch matrix, and docs/OneThird-mg75f0-GateClassClosure.md for what the
widening does and does not close.

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
# The gate under audit.  Parts B and D IMPORT this module and call its own
# predicates, so the module name is the whole dependency -- there is no second
# copy of the census here to drift from it (see `part_B`).
GATE = "onethird_mg2c34_n7_overlap_test"
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
    compared 4 of the committed row's 22 fields, and eighteen -- `frozen_pair`
    among them -- were opened and never looked at.  mg-75f0 widened the
    comparison to the whole row.  This part is what stops it un-widening, and it
    is deliberately NOT a hand-maintained field list: a hand-maintained census
    becomes wrong the first time someone adds a field, silently, which is the
    SAME defect one turn later.

    Three things are checked, in increasing strength:

      B1  CENSUS.  Every field of the committed reference row is either COMPARED
          by the gate or listed in the gate's own
          `IDENTITY_EXCLUDED_REF_FIELDS` -- with a reason, in the source, next
          to the exclusion.  Reviewable exclusions, not silent ones.  A STALE
          exclusion, naming a field the row no longer has, fails too.
      B2  PER-FIELD FIRING.  For EACH field, perturb that field alone in the
          committed row and require the gate's own `_identity_row_ok` to return
          False.  A field that cannot make the gate fail is a field the gate is
          not checking, whatever the census says.
      B3  ANTI-DRIFT CANARY.  Hand the gate's comparison a reference row with a
          field name it has never seen.  The new field must be compared
          automatically and -- because the row builder does not produce it --
          must FAIL.  This is the "someone adds a field to the mg-8b64 row"
          case, tested rather than trusted.

    WHY THIS CALLS THE GATE INSTEAD OF PARSING IT (mg-75f0).  As mg-5ad1
    committed it, this part parsed the census out of the gate source, so it could
    not drift from a hand-maintained list.  It could still drift from the gate's
    BEHAVIOUR, and it did.  mg-7db4's note on the version this replaces, kept
    because it is the argument for the replacement:

        "The 240-character scan window used to run on past the end of the
        assignment it was reading and into the NEXT `rec["match_*"] = ...` line.
        In the gate as committed, `match_delta` and `match_bk_lambda2` are
        adjacent, so the window opened at `match_delta` swept up
        `ref["bk_lambda2"]` from the line below it.  Consequence, measured:
        deleting `match_bk_lambda2` from the identity conjunction -- the mg-09ea
        F3 repair, reverted, one line -- left this census still reporting
        `bk_lambda2` as COMPARED, and the probe exited 0.  The one assertion
        part B makes is that the F3 repair is present, and it could not see the
        repair being removed."

    That is a second representation of the census disagreeing with the first.
    Importing the gate and calling `identity_field_comparisons` removes the
    second representation entirely, so the class of bug mg-7db4 found here cannot
    recur, and B2 MEASURES firing instead of inferring it from source text."""
    import onethird_mg2c34_n7_overlap_test as gate    # cheap: no work at import

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
            failures.append(f"PART B1: exclusion {k!r} has no stated reason; an "
                            f"exclusion with a reason is reviewable, a bare one "
                            f"is not")
    if "bk_lambda2" not in compared:
        failures.append("PART B1: bk_lambda2 is NOT compared -- the mg-60d3 F3 "
                        "repair is absent")
    if "frozen_pair" not in compared:
        failures.append("PART B1: frozen_pair is NOT compared -- mg-5ad1's M3 "
                        "(the Theorem-E selector flip that moves the quantity "
                        "ledger claim 8 rests on) is live again")

    # ---- B2 per-field firing ----------------------------------------------
    print()
    print("  PER-FIELD FIRING -- perturb one field of the committed row; does")
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
    """The same question as part B2, asked of every remaining gate predicate.

    mg-5ad1 finding 2: the gate's proof-of-firing
    (`onethird_mg60d3_gate_mutation_demo.py`) is a hardcoded 2x3 matrix over two
    fixed mutations, takes ~11 min, and at the time was run by nothing.  It
    answers "do the two known repairs still fire?", not "can each predicate fail
    at all?".  This part answers the second question in milliseconds, on
    synthetic rows, so it can live in the order-seconds gate: each predicate is
    handed a row it must ACCEPT and a row it must REJECT.

    The rows to reject are not arbitrary -- each is the SIGNATURE of a mutation
    that has actually beaten this gate, so a predicate quietly losing a conjunct
    is caught here rather than eleven minutes later."""
    import onethird_mg2c34_n7_overlap_test as gate

    good_antichain = {"poset": "antichain-4", "c_max": 1.0, "c_min": 1.0,
                      "dim_U": 10, "dim_U_known": 10}
    good_proj = {"n": 7, "num_LE": 360, "dim_U": 24,
                 "null_random_subspace": 24 / 360}
    good_two = {"dim_eigenspace": 2, "c_max": 0.5, "c_min": 0.5}
    # mg-48dd's two corpus-independent controls.  Both take (row, tag) because
    # the gate applies them to each pair selector, so they are bound to the
    # `frozen` selector here to keep the one-argument shape of this table.
    good_centred = {"frozen_pair_indicator_sum": 2.22e-16}
    good_overlap = {"frozen_pair_overlap_with_U": 0.807168}

    def _indicator_centred_ok(row):
        return gate._indicator_centred_ok(row, "frozen")

    def _overlap_proper_ok(row):
        return gate._overlap_proper_ok(row, "frozen")

    cases = [
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
         "to n^2 and BOTH readings still say 1"),
        (gate._projector_row_ok, "CONTROL E", good_proj, True,
         "dim U inside its structural bound and a proper subspace"),
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
         "lambda_2 simple, so this control would be VACUOUS -- the state "
         "mg-5ad1 finding 4 found the real-data two-sided check in"),
        # mg-48dd: the two corpus-INDEPENDENT controls.  Added here rather than
        # left to this ticket's own probe, because "all 10 predicate-firing
        # probes agree" is read by later authors as "all of them", and a gate
        # predicate outside the standing battery is this arc's own defect one
        # level in.
        (_indicator_centred_ok, "CONTROL G", good_centred, True,
         "a mean-centred indicator sums to zero"),
        (_indicator_centred_ok, "CONTROL G / centring lost (mg-bd53 C2)",
         dict(good_centred, frozen_pair_indicator_sum=13.4164), False,
         "C2's signature: `f -= f.mean()` becomes a no-op, so the sum leaves 0 "
         "by sixteen orders of magnitude -- against a reference the corpus "
         "cannot regenerate"),
        (_overlap_proper_ok, "CONTROL H", good_overlap, True,
         "the frozen-pair indicator is well outside U, as the corpus claims"),
        (_overlap_proper_ok, "CONTROL H / indicator in U (mg-5ad1 M3)",
         dict(good_overlap, frozen_pair_overlap_with_U=1.0), False,
         "M3's signature under REGENERATION: the max-ratio pair drives the "
         "overlap to exactly 1, the identity check is absorbed by the refreshed "
         "store, and the vacuity floor is what is left"),
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
        print(f"  {label:<38} expect {'accept' if must_accept else 'REJECT':>6}"
              f"  got {'accept' if got else 'reject':>6}  "
              f"{'PASS' if ok else 'PROBE FAILED'}")
        print(f"      {why}")
        if not ok:
            failures.append(
                f"PART D: {label} "
                + ("rejected a legitimate row" if must_accept
                   else "ACCEPTED a row it must reject")
                + f" -- {why}")
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
    print("PART C -- the frozen-pair selector: a comparison IS available, the")
    print("          selector is load-bearing, and it is MADE (mg-7db4)")
    print("=" * 78)
    print(f"{'poset':>14} {'committed':>11} {'argmin ratio':>13} "
          f"{'argmax ratio':>13} {'corpus sel.':>12}  {'agrees':>7} "
          f"{'flip moves it':>14} {'sel. ok':>8}")
    rows, failures = [], []
    for name in NAMED:
        i = int(name.split("#")[1])
        res = bk_frozen_pair(Ps[i])
        pairs = [pc for pc in res["pairs"] if pc["ratio"] is not None]
        lo = min(pairs, key=lambda pc: pc["ratio"])
        hi = max(pairs, key=lambda pc: pc["ratio"])
        committed = list(ref_rows[name]["frozen_pair"])
        argmin = [int(lo["x"]), int(lo["y"])]
        argmax = [int(hi["x"]), int(hi["y"])]
        # mg-7db4: what the corpus function ACTUALLY returns, as opposed to
        # what this file recomputes.  See the note below on why these differ.
        fz = res["frozen"]
        selector = [int(fz["x"]), int(fz["y"])] if fz is not None else None
        agrees = argmin == committed
        moves = argmax != argmin
        selector_ok = selector == committed
        print(f"{name:>14} {str(committed):>11} {str(argmin):>13} "
              f"{str(argmax):>13} {str(selector):>12}  {str(agrees):>7} "
              f"{str(moves):>14} {str(selector_ok):>8}")
        if not agrees:
            failures.append(f"{name}: the corpus argmin-ratio selector gives "
                            f"{argmin}, committed reference says {committed} "
                            f"-- no comparison is available after all")
        if not moves:
            failures.append(f"{name}: argmax == argmin, so flipping the "
                            f"selector is not a mutation at this poset")
        if not selector_ok:
            failures.append(
                f"{name}: bk_frozen_pair() RETURNS {selector}, committed "
                f"reference frozen_pair is {committed} -- the Theorem-E pair "
                f"ledger claim 8 rests on has moved -- as of mg-75f0 the gate "
                f"compares this field too, so this fires alongside it rather "
                f"than instead of it")
        rows.append({"name": name, "committed_frozen_pair": committed,
                     "argmin_ratio_pair": argmin, "argmax_ratio_pair": argmax,
                     "corpus_selector_pair": selector,
                     "argmin_ratio": float(lo["ratio"]),
                     "argmax_ratio": float(hi["ratio"]),
                     "reproduces_committed": agrees,
                     "flip_moves_the_pair": moves,
                     "selector_matches_committed": selector_ok})
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
        "gate_under_audit": f"scripts/{GATE}.py",
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
    # mg-bd53 finding 4 / mg-4f9b: this census reads ONE row (`NAMED[0]`), so
    # every number below is per ROW and the sentence has to say so.  "0 silently
    # uncompared" was true of this row and false of the dataset it comes from
    # for as long as `h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` -- which
    # exist only on the 54 small-|L| rows -- were compared at zero posets.  The
    # per-DATASET census is the gate's own, beside its identity loop, because no
    # single-row census can make that statement.
    print(f"  B  {len(B_census['reference_fields_compared'])} of "
          f"{len(B_census['reference_fields_present'])} fields OF THE ROW "
          f"{NAMED[0]!r} are COMPARED by the gate,")
    print(f"     {len(B_census['reference_fields_excluded'])} excluded with a "
          f"stated reason, 0 uncompared IN THIS ROW (the per-dataset census "
          f"is the gate's); "
          f"{B_census['fields_that_fire']}/"
          f"{len(B_census['reference_fields_compared'])} fire the")
    print("     gate when perturbed, and a field newly ADDED to the reference "
          "row is compared")
    print("     automatically and fails.")
    print("  C  the frozen-pair selector reproduces the committed reference "
          "at 5/5 posets")
    print("     (a comparison is available), a one-character flip moves it at "
          "5/5, and")
    print("     bk_frozen_pair() still RETURNS the committed pair at 5/5 "
          "(mg-7db4: the")
    print("     comparison is now made, not merely reported available).")
    print(f"  D  all {len(D_rows)} predicate-firing probes agree: every gate "
          f"predicate accepts the row it")
    print("     must accept and REJECTS the row it must reject.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
