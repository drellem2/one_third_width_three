#!/usr/bin/env python3
"""
mg-2c34 -- THE n=7 OVERLAP TEST.

The decisive check of the CONDITIONAL standard-dominance picture: measure the
SD-quant overlap constant c(P) at the three known n=7 OFF-REGIME posets.

=============================================================================
THE TARGET, PINNED FROM THE CORPUS (quoted, not reconstructed)
=============================================================================

(1) WHICH QUANTITY.  `docs/OneThird-StandardDominance-ComparisonRoute.md` and
    `scripts/onethird_mg4a86_sdquant_overlap.py` define it identically:

      "SD-quant(c):  the slowest BK mode f satisfies  ||P_U f||^2 >= c ||f||^2,
       where U = span{ sigma |-> 1[sigma(a)=x] } is the one-particle observable
       span.  This is well-posed WITHOUT U being invariant (which it is not on
       L(P))."
                     -- onethird_mg4a86_sdquant_overlap.py, module docstring

      "This script measures c(P) directly:
         - take the BK eigenspace at lambda_2 (excluding the constant mode),
         - compute the LARGEST overlap over that eigenspace (the most
           favourable reading, which matters because lambda_2 is frequently
           degenerate):
             c(P) = lambda_max( V^T P_U V ),  V = orthonormal basis of the
             eigenspace."
                     -- ibid.

(2) ON WHICH THREE POSETS.

      "The decisive next experiment, cheap and well-specified: compute `c(P)`
       on `enum-n7-#600/#3/#20` from the `mg-8b64` data.  Predicted outcome
       `c ~ 0`, which would show SD-quant is *conditional* on the
       all-pairs-frozen regime"
                     -- OneThird-StandardDominance-ComparisonRoute.md sec 7.3

    Those three names index `enumerate_both_connected(7)` from
    `onethird_mgb0a6_spectral_killshot_probe.py` (mg-8b64's `run()`:
    `targets.append((f"enum-n{n}-#{i}", P))`).  They are the off-regime row
    block of `OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:295-297`.
    IDENTITY IS RE-VERIFIED HERE, not assumed: |L(P)|, lambda_std, delta and
    lambda_2^BK are recomputed and compared against the committed
    `data/onethird-mg8b64-L1b-bk-transport-transfer.json` rows.

(3) UNDER WHICH MEASURE.  The BK walk W is symmetric and doubly stochastic on
    L(P) (lazy (n-1)-regular convention, step8.tex), so its stationary measure
    is UNIFORM on L(P) and the L^2(pi) inner product is the Euclidean one up to
    the global factor 1/|L(P)|.  P_U is therefore the ordinary orthogonal
    projector, and c(P) is measure-unambiguous.  The corpus is CONSISTENT on
    this: `onethird_mg8b64_..._probe.py:bk_walk_matrix` and
    `onethird_mg4a86_standard_dominance_target_audit.py:bk_walk_matrix` build
    the same matrix (verified byte-equal in behaviour by CHECK-0 below).

=============================================================================
WHAT IS ADDED BEYOND THE mg-4a86 INSTRUMENT
=============================================================================
mg-4a86 reports only c_max = lambda_max(V^T P_U V), the MOST FAVOURABLE reading
over a degenerate lambda_2 eigenspace.  For a refutation that is the wrong
tail: a single standard mode hiding inside a degenerate eigenspace would give
c_max ~ 1 while the actual slow dynamics is non-standard.  This script reports,
for every poset:

    c_max     = lambda_max(V^T P_U V)   (mg-4a86's quantity, reproduced exactly)
    c_min     = lambda_min(V^T P_U V)   (the adversarial reading)
    dim_E     = dim of the lambda_2 eigenspace at tol
    dim_U, m  = dim U and |L(P)|
    null      = dim_U / m               (expected ||P_U f||^2 for a RANDOM unit
                                         f: the vacuity floor -- c near `null`
                                         is NO signal in either direction)

and, to test the corpus's stated MECHANISM rather than only its prediction, the
squared correlation of the slow mode with the frozen pair indicator
f_xy = 1[x <_sigma y] ("the slow mode is ... degree-2, the lone frozen pair").

=============================================================================
CONTROLS (the ticket's requirement: show the instrument CAN return the wrong
answer on a case where the answer is known, before trusting it)
=============================================================================
CHECK-0  instrument equivalence: this file's c_max must equal mg-4a86's
         `sd_quant_constant` to 1e-12 on every poset measured.  NOTE, per
         mg-09ea F5: this verifies the WRAPPER, not the instrument -- the two
         call the same `bk_walk_matrix` and the same `projector_U`, so the
         agreement is by construction and bounds no numerical risk.

IDENTITY  THE WHOLE committed mg-8b64 reference row is recomputed and compared,
         field by field, at every poset of the identity population, with ONE
         declared exclusion (the lookup key).  The count is per row and depends
         which row: the seven n=7 rows carry 23 fields and 22 are compared;
         `fam:N (2+2)` carries 25 and 24 are compared, because
         `bk_cheeger_exhaustive` only returns a value for small |L| and its two
         fields exist nowhere else.  ACROSS THE DATASET -- 1091 committed rows,
         25 distinct field names -- 24 are compared at at least one poset and 1
         is excluded with a reason, which the gate asserts rather than states
         (see the per-dataset census beside the identity loop).  mg-bd53
         finding 4 is why that sentence names its population: "22 of 23, 0
         silently uncompared" was true of every row and false of the dataset,
         and `h_bk_exhaustive` / `h_bk_argmin_is_pair_cut` sat at zero
         comparisons underneath it.
         THE OTHER AXIS IS THE ROUTE.  Three of the four legacy quantities are
         compared through TWO independent computations and one through one; each
         says which and why in `IDENTITY_SECOND_ROUTES`, and
         `_identity_routes_declared` fails the gate if a comparison stops
         declaring it.  mg-09ea F3 added lambda_2^BK to a conjunction of three fields;
         mg-5ad1 then measured that the resulting conjunction compared 4 of the
         row's fields (it said "4 of 22"; the n=7 row has 23 -- harmless, and
         corrected here only because this docstring now counts them for a
         reason), and that a ONE-CHARACTER flip of mg-8b64's Theorem-E
         frozen-pair selector (min -> max) moved `frozen_pair` at 5/5 posets and
         `frozen_pair_overlap_with_U` -- the quantity ledger claim 8 rests on --
         to exactly 1.0000, with this gate printing PASSED and exiting 0.  The
         fix is not "compare two more fields": see `IDENTITY_EXCLUDED_REF_FIELDS`
         and `identity_field_comparisons`, which iterate the committed row
         itself so a field ADDED to that row is compared automatically.

CONTROL A (graded, analytic, CAN FAIL AT EVERY POINT).  On a real L(P), build a
         synthetic symmetric walk whose lambda_2 eigenvector is
         v(theta) = cos(theta) u + sin(theta) w  with u a unit vector in
         U (+) const^perp and w a unit vector orthogonal to U.  The true answer
         is c = cos^2(theta), KNOWN in closed form for every theta.  The
         instrument is required to return it to 1e-9 -- including c = 0 at
         theta = 90 deg.  This is the control that shows the instrument is able
         to output 0: an instrument that cannot output 0 cannot refute
         SD-quant, and an instrument that cannot output 1 cannot confirm it.

CONTROL B (known-answer poset).  Antichain A_n, n = 4,5,6: L(P) = S_n and the
         BK chain is the interchange process on the path.  Aldous/CLR gives the
         gap EIGENVALUE: gap(interchange) = gap(one-particle).  Required:
         c_max = 1 AND c_min = 1, i.e. the whole gap EIGENSPACE lies in U -- and
         that is STRICTLY STRONGER than the theorem, see `_antichain_row_ok` for
         what actually licenses it.  Both readings, per mg-09ea F4: c_max is a
         maximum over the lambda_2 eigenspace, so it survives a shrink of U
         that the adversarial reading does not.  Also required, per mg-5ad1's
         residual: dim U = (n-1)^2 + 1 exactly, the known rank of the
         one-particle span on S_n.

CONTROL E (structural bound on dim U, must fail if the projector's rank filter
         is wrong).  U = span{sigma |-> 1[sigma(a) = x]} is spanned by n^2
         position indicators that satisfy 2n-2 independent homogeneous
         relations (the n row-sums are all the constant 1, and so are the n
         column-sums), so ALWAYS dim U <= (n-1)^2 + 1 -- the rank
         `onethird_mg4a86_sector_leakage_and_tempering.sector_leakage` states
         in its own docstring, saturated on S_n.  Required on every measured
         poset: dim U <= (n-1)^2 + 1, and dim U < |L(P)| (if U is the WHOLE
         function space then c == 1 identically and the measurement is vacuous
         by sec 2's own `null` criterion).  See `_projector_row_ok`.

CONTROL C (deliberately BROKEN instrument, must fail control B).  Replace U by
         a fixed coordinate subspace of the SAME dimension.  On the antichain
         the true answer is 1; the broken instrument must NOT return 1.  This
         is what makes CONTROL B non-vacuous.

CONTROL D (dimension-artifact null, must fail on the in-regime posets).
         Replace U by a RANDOM subspace of the same dimension (seeded).  Any
         c ~ 1 that survives this substitution was an artifact of dim U, not
         evidence of standard dominance.

CONTROL F (two-sided reading-dependence, ON REAL DATA).  The gate's
         reading-dependence check (`dim_eigenspace > 1` and
         `|c_max - c_min| > 1e-9`) was VACUOUS on real data: lambda_2^BK is
         simple at all five measured posets (mg-5ad1 finding 4).  The committed
         sweep names exactly four n=7 both-connected posets with a DEGENERATE
         lambda_2 -- #52, #88, #209, #420 -- so the coverage was available and
         unused.  #52 and #88 (the two non-duplicate ones) are measured here:
         required dim_E > 1 (so the check is not vacuous) AND
         |c_max - c_min| <= 1e-9.  See `_two_sided_row_ok`.  Non-vacuity is
         asserted, not hoped for.

WHAT THIS GATE CANNOT SEE, stated because implying coverage it has never had is
the defect this whole lineage is about (mg-4f9b, answering mg-bd53 / mg-5ad1 /
mg-09ea).  Four generations of this gate have each ended with an author
believing the one-character-selector class was closed, and each was followed by
an audit exhibiting a mutation that sailed through.  The outcome record:

    mg-09ea  AUDIT     two controls passing while blind        CAUGHT
    mg-60d3  gate fix  repaired those two instances            class survived
    mg-5ad1  AUDIT     one-character selector flip passes      CAUGHT
    mg-75f0  gate fix  widened 4 fields -> the whole row       class survived
    mg-bd53  AUDIT     a REGRESSION, and the class still open  CAUGHT

The audit stage is 3 for 3 and the gate is 0 for 2.  mg-4f9b measured why rather
than widening a fourth time; `scripts/onethird_mg4f9b_route_axis_probe.py`
part 3 is the experiment and `data/onethird-mg4f9b-route-axis.json` the record.

    THE MECHANISM.  The identity check compares a recomputation against
    `data/onethird-mg8b64-L1b-bk-transport-transfer.json`.  That file is not an
    independent reference: it is a FROZEN SNAPSHOT OF THE SAME CODE PATH, taken
    by mg-8b64's own probe and committed.  At run time the two are genuinely
    independent -- frozen bytes against a live computation -- and that is real
    coverage, which is why every mutation in the audit record was caught by
    SOMETHING.  Across commits they are not independent at all, because the
    author who edits a probe re-runs it and commits the numbers it now produces.
    MEASURED: mg-5ad1's M3 selector flip is exit 1 at 7 of 7 posets; the same
    flip with the rows it moves regenerated by the mutated code is exit 0, on
    the mg-75f0 gate and on this one alike.  The gate is a REGENERATION
    DETECTOR.  It sees a mutation in the window between the edit and the
    refresh, and it is blind the moment the two land together.

    WHY NO AMOUNT OF FIELD WIDENING FIXES THAT.  Widening the field axis (four
    fields -> 23) and widening the route axis (one two-route quantity -> three)
    both raise the number of ways a mutation can move the recomputation away
    from the stored value.  Neither changes where the stored value came from.  A
    mutation that moves the computation AND its own reference together is
    invisible to any number of comparisons against that reference.  This is the
    diagnosis mg-4f9b was asked for, and the honest answer to "can the gate
    close the class" is NO -- not by comparing more.

    WHAT DOES SURVIVE IT, and it is the same experiment's control.  CONTROL A
    (c = cos^2 theta), CONTROL B (c = 1 on the antichain, dim U = (n-1)^2+1),
    CONTROL C (the broken instrument must NOT return 1) and CONTROL E (dim U <=
    (n-1)^2+1, dim U < |L|) compare against CLOSED FORMS AND THEOREMS, not
    against stored numbers.  MEASURED: mg-5ad1's M4 rank-filter mutation is exit
    1 with the dataset regenerated exactly as R1's was -- regeneration cannot
    move (n-1)^2+1.  So the useful distinction in this gate is not how many
    fields a control compares; it is WHERE ITS REFERENCE COMES FROM.  A new
    control is worth more than a wider comparison exactly when it has a
    reference the corpus cannot regenerate.

    WHERE THE CLASS IS ACTUALLY DETECTED: the independent audit stage, 3 for 3,
    by a party who reads the selector and asks whether it is the right one --
    a semantic question no stored value can answer.  That is not a gap to be
    closed by this file; it is the division of labour, and it is recorded here
    so that the next reader of a green gate run knows what green does and does
    not mean.

Reproducibility: no randomness except CONTROL D, which is seeded
(`numpy.random.default_rng(20260729)`).  Every number in the deliverable comes
from `data/onethird-mg2c34-n7-overlap.json`, written by this file.  Note that
this is the gate's OWN output and the gate never reads it back, so nothing in
it is under comparison -- mg-bd53 finding 2 (`frozen_pair_overlap_with_U` moved
by one line of `frozen_pair_indicator`, printed, exit 0) lives here, and per the
paragraph above a read-back would catch that mutation only until someone
regenerated this file too.

Run:  python3 scripts/onethird_mg2c34_n7_overlap_test.py
      (numpy required; ~2 min for the full n=7 sweep)
"""

import os
import sys
import json
import math
import argparse
import itertools

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

from onethird_mgb0a6_spectral_killshot_probe import (  # noqa: E402
    Poset, enumerate_both_connected, before_prob_dp, named_posets,
)
from onethird_mg4a86_standard_dominance_target_audit import (  # noqa: E402
    bk_walk_matrix, lambda_std,
)
from onethird_mg4a86_sector_leakage_and_tempering import (  # noqa: E402
    one_particle_span,
)
from onethird_mg4a86_sdquant_overlap import (  # noqa: E402
    sd_quant_constant as mg4a86_sd_quant_constant,
    projector_U as mg4a86_projector_U,
)
from onethird_mg8b64_L1b_bk_transport_transfer_probe import (  # noqa: E402
    bk_frozen_pair as mg8b64_bk_frozen_pair,
    biased_families as mg8b64_biased_families,
    analyze_poset as mg8b64_analyze_poset,
)

EIG_TOL = 1e-9            # mg-4a86's degeneracy tolerance, kept verbatim
NEAR_TOL = 1e-6           # honest "near-degenerate" band, reported separately
SEED = 20260729

# The three posets the corpus names, plus the in-regime contrast block from
# OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:295-300.
OFF_REGIME = [3, 20, 600]
IN_REGIME = [945, 809]

# CONTROL F's population: the n=7 both-connected posets whose lambda_2^BK is
# DEGENERATE, read off the committed sweep (`dim_eigenspace = 2` at #52, #88,
# #209, #420 and nowhere else in the 946).  #209/#420 measure identically to
# #52/#88 respectively, so two suffice.  Identity is re-verified on these as
# well, so the identity population is SEVEN posets, not five.
DEGENERATE_LAMBDA2 = [52, 88]


# --------------------------------------------------------------- helpers ----
def antichain_poset(n):
    return Poset(n, [])


def slow_eigenspace(W, tol=EIG_TOL):
    """Orthonormal basis of the lambda_2 eigenspace, excluding the top
    (constant) mode.  Same selection rule as mg-4a86's sd_quant_constant."""
    ev, V = np.linalg.eigh(W)
    order = np.argsort(ev)[::-1]
    ev, V = ev[order], V[:, order]
    lam2 = ev[1]
    idx = [j for j in range(1, len(ev)) if abs(ev[j] - lam2) < tol]
    return float(lam2), V[:, idx], ev


# ------------------------------------------- the identity field comparison ---
# mg-5ad1's RED finding, measured: the identity conjunction opened the committed
# mg-8b64 reference row and compared FOUR of its TWENTY-TWO fields.  Eighteen
# were fetched-or-available and never looked at -- frozen_pair, frozen_ratio,
# frozen_p, min_phi_bk_pair, width, num_incomp_pairs, transport_gap among them.
# A one-character flip of mg-8b64's own Theorem-E selector (min -> max) moved
# frozen_pair at 5/5 posets and frozen_pair_overlap_with_U from 0.807/0.809/0.810
# to EXACTLY 1.0000 -- the quantity ledger claim 8 (PROVEN[c]) rests on, in a row
# that itself says "argmin ratio, not the max-bias pair" -- and this gate printed
# "All controls and identity checks PASSED" and exited 0.
#
# The repair mg-60d3 made was derived FROM the two failures mg-09ea found, which
# is why the class survived it: a repair derived from a known failure carries no
# information about the class.  So this is not "add frozen_pair to the
# conjunction".  DEFAULT IS TO COMPARE: the recomputed row is compared against
# the committed row field by field, ITERATING THE COMMITTED ROW, with every
# exclusion named below and given a reason.  A field added to the mg-8b64 row is
# compared automatically; a hand-maintained list would go wrong silently the
# first time someone added one, which is this same defect one turn later.
#
# mg-bd53 FINDING 1, repaired here (mg-4f9b).  The paragraph above describes the
# FIELD axis and it is true.  It is not the only axis.  Widening the field axis
# NARROWED THE ROUTE AXIS, silently: before mg-75f0 the four legacy comparisons
# ran the GATE'S OWN recomputation against the committed value; after it they
# became aliases of the row-wide comparison, which recomputes through mg-8b64's
# `analyze_poset`.  For `lambda_std` and `delta` those are two DIFFERENT
# implementations, so the gate's own route stopped being compared to anything.
# Measured consequence: `np.max(w)` -> `np.min(w)`, one character, in mg-4a86's
# own `lambda_std` made the PRE-widening gate exit 1 and the widened gate exit 0,
# printing `lam_std=-0.048288466 (ref 0.7850482917286934)` and `match=True` on
# the same line.  `IDENTITY_SECOND_ROUTES` below is the repair AND the record.
#
# THE GENERAL POINT, because it is the reusable part.  COMPARING MORE FIELDS
# AGAINST ONE ROUTE IS NOT STRICTLY BETTER THAN COMPARING FEWER FIELDS AGAINST
# TWO ROUTES.  One route detects a mutation that moves the stored value relative
# to the reference.  A mutation that moves the COMPUTATION and the COMPARED VALUE
# TOGETHER is invisible to one route and fatal to two.  A widening that trades
# routes for fields is a coverage change in both directions and must be stated as
# one -- which is what did not happen at mg-75f0.

IDENTITY_EXCLUDED_REF_FIELDS = {
    "name": "the lookup key itself.  The row is FETCHED BY this value "
            "(`ref_rows[name]`), so comparing it is a tautology that cannot "
            "fail.  This is the only exclusion.",
}

IDENTITY_FLOAT_TOL = 1e-9   # the tolerance the mg-09ea F3 repair already used

# Kept for the printed identity line and for the pre-repair reconstruction in
# `scripts/onethird_mg60d3_gate_mutation_demo.py`, which rebinds
# `_identity_row_ok` to a conjunction over exactly these four keys.  They are
# now ALIASES of four of the row-wide comparisons, not the comparison itself.
IDENTITY_LEGACY_FIELDS = [("match_num_LE", "num_LE"),
                          ("match_lambda_std", "lambda_std"),
                          ("match_delta", "delta"),
                          ("match_bk_lambda2", "bk_lambda2")]

# ------------------------------------------------------ the ROUTE axis -------
# ONE ENTRY PER LEGACY COMPARISON, and every entry says one-route or two-route
# and WHY.  Read as a table it is the answer to "what does this comparison
# actually secure?", which is the question mg-75f0's field census cannot ask.
#
#   `second_route`  the gate's OWN recomputation, if it is a different
#                   implementation from mg-8b64's row builder.  When present it
#                   is ANDed into `field_matches[field]` in the identity loop,
#                   so BOTH routes must agree with the committed value.
#   `why`           why there are two routes, or why there is only one.
#
# Machine-readable on purpose, and here is exactly how far that goes, because
# claiming more than a check performs is the defect this file is about.
# `_identity_routes_declared()` below is a GATE CONDITION and checks the CHEAP
# half: every legacy field has an entry, every entry has a real reason, and no
# entry names a field that is not compared.  It does NOT verify that a declared
# route is wired, nor that the two implementations are still distinct -- that
# needs to import three other modules and diff their source, so it lives in
# `scripts/onethird_mg4f9b_route_axis_probe.py` part 1 (seconds, not wired to
# every run).  So: a route that is silently unwired fails in the probe and not
# here.  What cannot happen silently any more is a comparison with no
# declaration at all, which is the state mg-bd53 found.
IDENTITY_SECOND_ROUTES = {
    "num_LE": {
        "second_route": None,
        "why": "ONE ROUTE, and it cannot be two.  Both sides call the same "
               "`Poset.linext_count`; the gate has no independent linear-"
               "extension counter and writing one would be a second copy of "
               "the same DP, not a second route.  A mutation in "
               "`linext_count` moves the recomputation and NOT the committed "
               "JSON, so the single route still catches it -- what it cannot "
               "catch is a mutation shipped together with a regenerated "
               "dataset (see WHAT THIS GATE CANNOT SEE in the header).",
    },
    "lambda_std": {
        "second_route": "onethird_mg4a86_standard_dominance_target_audit."
                        "lambda_std",
        "why": "TWO ROUTES.  The row-wide comparison recomputes `lambda_std` "
               "through mg-8b64's `analyze_poset` -> `transport_summary` -> "
               "mgb0a6's `standard_block_and_lambda`.  The gate additionally "
               "computes it through mg-4a86's own `lambda_std`, a different "
               "implementation in a different module, and both must match the "
               "committed value.  mg-bd53 finding 1: this route existed before "
               "mg-75f0, was dropped silently by it, and a one-character flip "
               "in mg-4a86's `lambda_std` was the measured cost.  Restored.",
    },
    "delta": {
        "second_route": "gate.delta_and_frozen_pair",
        "why": "TWO ROUTES, weaker than lambda_std's and stated as such.  Both "
               "sides call `before_prob_dp` for the pair probabilities, so the "
               "primitive is SHARED; what differs is the aggregation -- the "
               "gate takes max over incomparable pairs of min(p, 1-p) in "
               "`delta_and_frozen_pair`, mg-8b64 aggregates inside "
               "`bk_frozen_pair`.  So this catches a mutation in EITHER "
               "aggregation and NOT one in `before_prob_dp`, which both routes "
               "would move together.  Half a second route, honestly labelled.",
    },
    "bk_lambda2": {
        "second_route": "onethird_mg4a86_standard_dominance_target_audit."
                        "bk_walk_matrix",
        "why": "TWO ROUTES.  The gate builds the BK walk matrix with mg-4a86's "
               "`bk_walk_matrix`, the row-wide comparison with mg-8b64's, so a "
               "mutation in EITHER walk matrix is fatal.  This is the one "
               "mg-75f0 kept deliberately, and it is the reason the other "
               "three entries in this table exist: keeping one and dropping "
               "two without saying so is what mg-bd53 found.",
    },
}


def _identity_routes_declared():
    """Every legacy comparison must appear in `IDENTITY_SECOND_ROUTES` with a
    non-trivial reason.  Cheap, and it is the anti-rot half of the declaration:
    a fifth legacy field, or an entry whose `why` decays to a stub, fails here
    rather than being discovered by the next audit."""
    problems = []
    for _, field in IDENTITY_LEGACY_FIELDS:
        d = IDENTITY_SECOND_ROUTES.get(field)
        if d is None:
            problems.append(f"{field}: compared by the gate but its route "
                            f"structure is undeclared")
            continue
        if len(str(d.get("why", "")).strip()) < 40:
            problems.append(f"{field}: no stated reason for being one-route or "
                            f"two-route")
    for field in IDENTITY_SECOND_ROUTES:
        if field not in [f for _, f in IDENTITY_LEGACY_FIELDS]:
            problems.append(f"{field}: declares a route but is not a compared "
                            f"legacy field -- the declaration has drifted")
    return problems


_MISSING = object()


def _field_match(got, want, tol=IDENTITY_FLOAT_TOL):
    """(ok, abs_diff_or_None) for one reference field.

    Floats to `tol` (they come off an eigendecomposition and must survive a
    different BLAS); ints, bools, lists and None EXACTLY -- `frozen_pair` is a
    pair of labels, and "nearly the same pair" is not a thing."""
    if got is _MISSING:
        return False, None
    if isinstance(want, bool) or isinstance(got, bool):
        return got == want, None
    if isinstance(want, float) and isinstance(got, (int, float)):
        if math.isnan(want) or math.isnan(float(got)):
            return math.isnan(want) and math.isnan(float(got)), None
        d = abs(float(got) - float(want))
        return d < tol, d
    return got == want, None


def identity_field_comparisons(rec_row, ref_row, tol=IDENTITY_FLOAT_TOL):
    """Compare a recomputed mg-8b64 row against the committed one, FIELD BY
    FIELD, over the WHOLE committed row.

    Returns (matches, diffs): `matches[field] -> bool` and, for float fields,
    `diffs[field] -> |recomputed - committed|`.

    Iterating `ref_row` rather than a hardcoded field list is the load-bearing
    property, and the reason this is a function rather than a conjunction: PART B
    of `scripts/onethird_mg5ad1_gate_blindspot_probe.py` calls it directly with
    ONE field of the committed row perturbed at a time and requires that EVERY
    non-excluded field can drive `_identity_row_ok` to False.  A field that
    cannot make the gate fail is a field the gate is not checking."""
    matches, diffs = {}, {}
    for k in sorted(ref_row):
        if k in IDENTITY_EXCLUDED_REF_FIELDS:
            continue
        ok, d = _field_match(rec_row.get(k, _MISSING), ref_row[k], tol)
        matches[k] = ok
        if d is not None:
            diffs[k] = d
    return matches, diffs


# --------------------------------------------------------- gate predicates --
# The gate's failure conditions, at module level and separately named, for two
# reasons: the conjunction is readable in one place, and the mutation
# demonstrations (`scripts/onethird_mg60d3_gate_mutation_demo.py`, and the
# source-level route in `scripts/onethird_mg75f0_gate_class_closure_demo.py`)
# can substitute PRE-REPAIR forms to show which mutations used to pass.  No
# predicate has a switch to weaken it at run time -- the substitution lives in
# the demonstration, never in this file.

def _identity_row_ok(rec):
    """The recomputed mg-8b64 row must match the committed one in EVERY field.

    mg-09ea F3 was the instance: `ref_bk_lambda2` was loaded into the report and
    never used, so lambda_2^BK -- the denominator of R, and the only genuinely
    DYNAMICAL quantity in the document -- had no control that could fail.
    mg-5ad1 measured the class: after that repair, 4 of the row's fields were
    compared.  This now gates on EVERY field of the row it is given except the
    declared exclusion (see `identity_field_comparisons` and
    `IDENTITY_EXCLUDED_REF_FIELDS`), so a mutation anywhere in mg-8b64's own row
    builder that moves any committed quantity ON A ROW THIS GATE READS is fatal.

    THE COUNT IS PER ROW, AND SAYING "all 22" WITHOUT SAYING WHICH ROW IS HOW
    TWO FIELDS REACHED ZERO COMPARISONS (mg-bd53 finding 4).  The seven n=7
    rows carry 23 fields and 22 are compared; `fam:N (2+2)` carries 25 and 24
    are compared.  The per-DATASET statement -- every field name that occurs
    anywhere in the committed dataset is compared at at least one poset or
    declared excluded -- is a separate check, asserted beside the identity loop,
    because no per-row census can make it.

    THE ROUTE AXIS IS SEPARATE AND IS NOT MEASURED HERE.  This predicate reads
    `field_matches`; the second routes are ANDed INTO those entries by the
    identity loop (see `IDENTITY_SECOND_ROUTES`).  That placement is deliberate:
    `scripts/onethird_mg5ad1_gate_blindspot_probe.py` part B2 perturbs one field
    at a time and calls this function on `field_matches` alone, so a route wired
    beside it rather than into it would be invisible to the probe that enforces
    this gate."""
    if "field_matches" not in rec:
        return False          # no committed reference row: nothing was compared
    return all(rec["field_matches"].values())


def _antichain_row_ok(row):
    """CONTROL B: both readings, and the known rank of U.

    mg-09ea F4: c_max is a MAXIMUM over the lambda_2 eigenspace, so a shrunk U
    that still meets that eigenspace leaves c_max = 1 while c_min collapses to
    0.  This is the one-sidedness sec 2.7 identifies as the reason to report
    c_min at all; it was added to the measurement and not to the control.

    WHAT LICENSES c_min = 1 (mg-5ad1 finding 3, AMBER-latent, docstring only).
    Aldous' spectral-gap conjecture as proved by Caputo-Liggett-Richthammer
    gives the gap EIGENVALUE: gap(interchange on the path) = gap(one-particle).
    `c_min = 1` is the strictly stronger statement that the WHOLE gap eigenspace
    lies in the one-particle sector, which additionally requires that no other
    S_n-irrep component of the generator attains that eigenvalue -- and CLR does
    not supply that.  So the licence here is NOT the theorem: it is a VERIFIED
    property of these specific matrices, measured at A_4/A_5/A_6 (and A_7,
    |L| = 5040) by `scripts/onethird_mg5ad1_gate_blindspot_probe.py` part A:
    dim_E = n-1 > 1, 1 - c_min <= 2.7e-15 against a 1e-8 tolerance, and the
    nearest EXCLUDED eigenvalue 3.0e7-1.1e8 x EIG_TOL away, so it is neither
    vacuous nor knife-edge.  Four for four at n = 4,5,6,7.
    The distinction is not pedantry: if this control is ever extended to a
    larger antichain and a legitimate cross-irrep eigenvalue coincidence makes
    it fail, the fix is to narrow the control's POPULATION, not to loosen the
    assertion -- which is what happens when the stated reason is stronger than
    the real one.

    dim U = (n-1)^2 + 1 is the known rank of the one-particle span on S_n (see
    CONTROL E).  Asserted here because it is a known answer on a known-answer
    poset, and because without it a projector whose rank filter admits
    numerically-null directions inflates U and still reads c_max = c_min = 1:
    enlarging U can only INCREASE overlap, so both readings survive it."""
    return (abs(row["c_max"] - 1.0) < 1e-8 and abs(row["c_min"] - 1.0) < 1e-8
            and row["dim_U"] == row["dim_U_known"])


def _projector_row_ok(row):
    """CONTROL E: dim U must respect its structural bound and stay PROPER.

    U = span{sigma |-> 1[sigma(a) = x]} is spanned by the n^2 position
    indicators, which satisfy 2n-2 independent homogeneous relations (the n
    row-sums all equal the constant function 1, and so do the n column-sums), so
    dim U <= n^2 - (2n-2) = (n-1)^2 + 1 on EVERY poset -- the rank
    `onethird_mg4a86_sector_leakage_and_tempering.sector_leakage` states in its
    own docstring, saturated on S_n and verified against the committed sweep
    (0 violations in 946 + 29 + 10 rows).

    The second half is a vacuity floor, not an aesthetic: if dim U = |L(P)| then
    U is the WHOLE function space, c == 1 identically, and sec 2's own criterion
    ("c near `null` is NO signal in either direction") says the measurement
    carries none -- printed as `null = 1.0000` beside `c_max = 1.000000` in the
    same row.  Scoped to the MEASURED posets: on tiny hosts (|L| <= n, e.g. the
    `fam:1||chain*` family) U legitimately is everything, and those rows are a
    falsification probe, not a measurement."""
    return (row["dim_U"] <= (row["n"] - 1) ** 2 + 1
            and row["dim_U"] < row["num_LE"])


def _two_sided_row_ok(row):
    """CONTROL F: the reading-dependence check, with REAL coverage.

    The gate has always failed when `dim_eigenspace > 1` and
    `|c_max - c_min| > 1e-9` -- a reported c that depends on which reading you
    take is not a measurement.  mg-5ad1 finding 4: that check is VACUOUS on real
    data, because lambda_2^BK is simple at all five measured posets, so mg-60d3's
    F4 repair bought two-sided coverage on three synthetic antichains only.
    Coverage was available and unused: the committed sweep has dim_E = 2 at
    enum-n7-#52/#88/#209/#420.  Non-vacuity (dim_E > 1) is asserted here rather
    than assumed, so this control cannot quietly become the vacuous one it
    replaces."""
    return (row["dim_eigenspace"] > 1
            and abs(row["c_max"] - row["c_min"]) <= 1e-9)


def overlap_stats(Vs, PU):
    """(c_max, c_min) over the eigenspace spanned by the columns of Vs."""
    M = Vs.T @ PU @ Vs
    w = np.linalg.eigvalsh(M)
    return float(np.max(w)), float(np.min(w))


def frozen_pair_indicator(P, x, y):
    """f(sigma) = 1[x precedes y], centred, as a vector over L(P)."""
    les = P.linear_extensions()
    f = np.zeros(len(les))
    for r, perm in enumerate(les):
        pos = {e: i for i, e in enumerate(perm)}
        f[r] = 1.0 if pos[x] < pos[y] else 0.0
    f -= f.mean()
    nrm = np.linalg.norm(f)
    return f / nrm if nrm > 0 else f


def delta_and_frozen_pair(P):
    """delta(P) = max over incomparable pairs of min(p, 1-p); frozen pair =
    argmin of the Theorem-E ratio is NOT recomputed here -- we take the
    max-bias (most frozen) pair, which for these posets coincides with the
    mg-8b64 `frozen_pair` and is what the mechanism claim refers to."""
    best_delta = None
    most_frozen = None
    best_bias = -1.0
    for (x, y) in P.incomparable_pairs():
        p = float(before_prob_dp(P, x, y))
        d = min(p, 1 - p)
        best_delta = d if best_delta is None else max(best_delta, d)
        bias = max(p, 1 - p)
        if bias > best_bias:
            best_bias = bias
            most_frozen = (x, y, p)
    return best_delta, most_frozen


def measure(P, name=None, with_mechanism=True):
    """The full measurement on one poset."""
    les = P.linear_extensions()
    m = len(les)
    if m < 2:
        return None
    W = bk_walk_matrix(P)
    lam2, Vs, ev = slow_eigenspace(W)
    PU, dimU = mg4a86_projector_U(P)
    c_max, c_min = overlap_stats(Vs, PU)

    # honest near-degenerate band
    idx_near = [j for j in range(1, len(ev)) if abs(ev[j] - lam2) < NEAR_TOL]
    Vn = None
    ev_sorted = np.sort(ev)[::-1]
    if idx_near:
        _, V = np.linalg.eigh(W)
        order = np.argsort(np.linalg.eigvalsh(W))[::-1]
        # recompute consistently
        evx, Vx = np.linalg.eigh(W)
        o = np.argsort(evx)[::-1]
        Vx = Vx[:, o]
        Vn = Vx[:, idx_near]
    c_max_near, c_min_near = overlap_stats(Vn, PU) if Vn is not None else (None, None)

    row = {
        "name": name,
        "n": P.n,
        "num_LE": m,
        "lambda2_BK": lam2,
        "bk_gap": 1.0 - lam2,
        "lambda_std": float(lambda_std(P)),
        "dim_U": int(dimU),
        "dim_eigenspace": int(Vs.shape[1]),
        "dim_eigenspace_near": (int(Vn.shape[1]) if Vn is not None else None),
        "c_max": c_max,
        "c_min": c_min,
        "c_max_near": c_max_near,
        "c_min_near": c_min_near,
        "null_random_subspace": dimU / m,
    }
    d, mf = delta_and_frozen_pair(P)
    row["delta"] = d
    if with_mechanism:
        # THE MECHANISM TEST.  The corpus's claim is about Theorem E's FROZEN
        # pair (argmin of E(f_xy)/Var(f_xy)) -- mg-8b64's `frozen_pair` -- NOT
        # the max-bias pair.  Use mg-8b64's own selector verbatim.
        bk = mg8b64_bk_frozen_pair(P)
        for tag, pc in (("frozen", bk.get("frozen")),
                        ("maxbias", bk.get("maxbias"))):
            if pc is None:
                continue
            x, y = pc["x"], pc["y"]
            f = frozen_pair_indicator(P, x, y)
            proj = Vs.T @ f
            row[f"{tag}_pair"] = [int(x), int(y)]
            row[f"{tag}_p"] = float(pc["p"])
            # how much of the pair indicator the slow eigenspace captures
            row[f"{tag}_pairmode_capture"] = float(proj @ proj)
            # THE DECISIVE SUB-CHECK: is this degree-2 function itself inside
            # U?  The corpus infers "degree-2 slow mode => c ~ 0"; that
            # inference is only valid if degree-2 pair indicators have small
            # overlap with U on L(P).
            row[f"{tag}_pair_overlap_with_U"] = float(f @ (PU @ f))
        if mf is not None:
            row["most_frozen_p_maxbias"] = mf[2]
        # back-compat key used by the sweep summary
        row["pairmode_capture"] = row.get("frozen_pairmode_capture")
    # CHECK-0: agreement with mg-4a86's own instrument
    c_ref, lam2_ref = mg4a86_sd_quant_constant(P)
    row["check0_mg4a86_c"] = c_ref
    row["check0_abs_diff_c"] = abs(c_ref - c_max)
    row["check0_abs_diff_lam2"] = abs(lam2_ref - lam2)
    return row


# ---------------------------------------------------------------- controls --
def control_A(P, thetas_deg=(0, 30, 45, 60, 90)):
    """Graded analytic control: synthetic walk with a KNOWN slow mode.
    True answer c = cos^2(theta) at every theta, including 0 at 90 deg."""
    les = P.linear_extensions()
    m = len(les)
    PU, dimU = mg4a86_projector_U(P)
    rng = np.random.default_rng(SEED)

    ones = np.ones(m) / math.sqrt(m)
    # u: unit vector in U, orthogonal to constants
    for _ in range(50):
        g = rng.standard_normal(m)
        u = PU @ g
        u -= (u @ ones) * ones
        if np.linalg.norm(u) > 1e-6:
            break
    u /= np.linalg.norm(u)
    # w: unit vector orthogonal to U (hence orthogonal to constants: 1 in U)
    for _ in range(50):
        g = rng.standard_normal(m)
        w = g - PU @ g
        w -= (w @ ones) * ones
        if np.linalg.norm(w) > 1e-6:
            break
    w /= np.linalg.norm(w)

    out = []
    for th in thetas_deg:
        t = math.radians(th)
        v = math.cos(t) * u + math.sin(t) * w
        v /= np.linalg.norm(v)
        # W = 1*(const) + 0.9*(v) + 0.3*(everything else)
        Wsyn = (1.0 * np.outer(ones, ones)
                + 0.9 * np.outer(v, v)
                + 0.3 * (np.eye(m) - np.outer(ones, ones) - np.outer(v, v)))
        Wsyn = (Wsyn + Wsyn.T) / 2.0
        lam2, Vs, _ = slow_eigenspace(Wsyn)
        c_max, c_min = overlap_stats(Vs, PU)
        expected = math.cos(t) ** 2
        out.append({"theta_deg": th, "expected_c": expected,
                    "measured_c_max": c_max, "measured_c_min": c_min,
                    "lambda2_synthetic": lam2,
                    "abs_err": abs(c_max - expected),
                    "PASS": abs(c_max - expected) < 1e-9})
    return {"host_poset_num_LE": m, "dim_U": int(dimU), "rows": out,
            "ALL_PASS": all(r["PASS"] for r in out)}


def control_B_and_C(ns=(4, 5, 6)):
    """B: antichain must give c = 1 (Aldous/CLR).
       C: the same computation with a BROKEN projector must NOT give 1."""
    rows = []
    for n in ns:
        P = antichain_poset(n)
        W = bk_walk_matrix(P)
        lam2, Vs, _ = slow_eigenspace(W)
        PU, dimU = mg4a86_projector_U(P)
        c_max, c_min = overlap_stats(Vs, PU)
        # BROKEN instrument: first dimU coordinate axes of R^{|L|}
        m = W.shape[0]
        Qb = np.zeros((m, dimU))
        for j in range(dimU):
            Qb[j, j] = 1.0
        PUb = Qb @ Qb.T
        cb_max, cb_min = overlap_stats(Vs, PUb)
        row = {
            "poset": f"antichain-{n}", "num_LE": m, "dim_U": int(dimU),
            # the known rank of the one-particle span on S_n (CONTROL E)
            "dim_U_known": (n - 1) ** 2 + 1,
            "lambda2_BK": lam2, "c_max": c_max, "c_min": c_min,
            "broken_c_max": cb_max, "broken_c_min": cb_min,
            "C_PASS_broken_is_not_1": abs(cb_max - 1.0) > 1e-3,
        }
        # mg-09ea F4 repair: BOTH readings, not just c_max (see
        # _antichain_row_ok).  c_min was already computed and never asserted.
        row["B_PASS_c_is_1"] = _antichain_row_ok(row)
        rows.append(row)
    return {"rows": rows,
            "B_ALL_PASS": all(r["B_PASS_c_is_1"] for r in rows),
            "C_ALL_PASS": all(r["C_PASS_broken_is_not_1"] for r in rows)}


def canon(P):
    """A SOUND canonical form for a poset: minimum, over all label-permutations
    that respect the isomorphism-invariant (down-degree, up-degree) profile
    blocks, of the sorted strict relation.

    Needed because mg-8b64's `enumerate_both_connected` dedups by
    `iso_signature`, whose own docstring says it is "not a perfect canonical
    form" -- so its 946 posets are a LOWER BOUND on the number of n=7
    both-connected isomorphism classes, and some classes go unmeasured.  This
    closes that gap instead of caveating it.

    Soundness: every isomorphism preserves each element's (|less|,|greater|)
    profile, so it maps profile blocks onto profile blocks; target label blocks
    are assigned from the SORTED profile keys, which is intrinsic.  Verified
    against a brute min-over-all-7!-permutations canonicalisation: both give
    956 classes."""
    n = P.n
    rel = frozenset((a, b) for b in range(n) for a in P.less[b])
    prof = [(len(P.less[e]), len(P.greater[e])) for e in range(n)]
    groups = {}
    for e in range(n):
        groups.setdefault(prof[e], []).append(e)
    keys = sorted(groups)
    blocks, nxt = {}, 0
    for k in keys:
        blocks[k] = list(range(nxt, nxt + len(groups[k])))
        nxt += len(groups[k])
    best = None
    for combo in itertools.product(*[itertools.permutations(blocks[k])
                                     for k in keys]):
        p = [0] * n
        for k, tgt in zip(keys, combo):
            for src, dst in zip(groups[k], tgt):
                p[src] = dst
        t = tuple(sorted((p[a], p[b]) for (a, b) in rel))
        if best is None or t < best:
            best = t
    return best


def threshold_witness(P, x, y):
    """Does Lemma 3.1's hypothesis hold for the pair (x,y)?  I.e. is there a k
    with  x <_sigma y  <=>  pos_sigma(x) <= k  for every sigma in L(P)?
    If so the degree-2 indicator 1[x <_sigma y] equals sum_{a<=k} 1[sigma(a)=x]
    and lies EXACTLY in U -- which is what breaks the corpus's
    'degree-2 => small overlap with U' inference, by hand."""
    tab = {}
    for perm in P.linear_extensions():
        pos = {e: i for i, e in enumerate(perm)}
        v = pos[x] < pos[y]
        if tab.setdefault(pos[x], v) != v:
            return None
    ks = [k for k, v in tab.items() if v]
    return max(ks) if ks else -1


def control_D(P, name, n_draws=20):
    """Dimension-artifact null: random subspace of dim U, seeded."""
    W = bk_walk_matrix(P)
    _, Vs, _ = slow_eigenspace(W)
    m = W.shape[0]
    _, dimU = mg4a86_projector_U(P)
    # NOT Python's hash(): it is salted per-process (PYTHONHASHSEED), which
    # would make this control's numbers differ between runs.  Every number in
    # the deliverable has to be reproducible, controls included.
    name_key = sum((i + 1) * ord(ch) for i, ch in enumerate(name)) % 1000
    rng = np.random.default_rng(SEED + name_key)
    vals = []
    for _ in range(n_draws):
        G = rng.standard_normal((m, dimU))
        Q, _ = np.linalg.qr(G)
        PR = Q @ Q.T
        vals.append(overlap_stats(Vs, PR)[0])
    return {"name": name, "dim_U": int(dimU), "num_LE": m,
            "random_c_max_mean": float(np.mean(vals)),
            "random_c_max_max": float(np.max(vals)),
            "analytic_null_dimU_over_m": dimU / m}


# ------------------------------------------------------------------- main ---
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-sweep", action="store_true",
                    help="skip the full n=7 both-connected sweep")
    args = ap.parse_args()

    report = {"definition_source": {
        "quantity": "SD-quant c(P) = lambda_max(V^T P_U V) over the BK "
                    "lambda_2 eigenspace (constant mode excluded); U = span"
                    "{sigma -> 1[sigma(a)=x]}",
        "quantity_source": "scripts/onethird_mg4a86_sdquant_overlap.py "
                           "(docstring + sd_quant_constant)",
        "posets": "enum-n7-#600 / #3 / #20 = indices into "
                  "enumerate_both_connected(7) from "
                  "onethird_mgb0a6_spectral_killshot_probe.py",
        "posets_source": "docs/OneThird-StandardDominance-ComparisonRoute.md "
                         "sec 7.3; docs/OneThird-L1b-Reverse-Cheeger-Proof-"
                         "Attempt.md:295-297",
        "measure": "uniform on L(P) (BK walk is symmetric doubly stochastic), "
                   "so P_U is the Euclidean orthogonal projector",
    }, "controls": {}, "identity_check": [], "measured": [], "sweep": None}

    print("=" * 78)
    print("mg-2c34 -- n=7 OVERLAP TEST")
    print("=" * 78)

    Ps = enumerate_both_connected(7)
    print(f"n=7 both-connected posets (deduped): {len(Ps)}")
    named = {f"enum-n7-#{i}": Ps[i] for i in OFF_REGIME + IN_REGIME}

    # -------- controls first, before looking at any answer -----------------
    print()
    print("-" * 78)
    print("CONTROL A -- graded analytic (synthetic slow mode, known c=cos^2 th)")
    print("-" * 78)
    A = control_A(Ps[600])
    report["controls"]["A_graded_analytic"] = A
    for r in A["rows"]:
        print(f"  theta={r['theta_deg']:>3}deg  expected c={r['expected_c']:.6f}  "
              f"measured={r['measured_c_max']:.9f}  err={r['abs_err']:.2e}  "
              f"{'PASS' if r['PASS'] else 'FAIL'}")
    print(f"  ALL_PASS = {A['ALL_PASS']}")

    print()
    print("-" * 78)
    print("CONTROL B/C -- antichain must give c=1; broken projector must not")
    print("-" * 78)
    BC = control_B_and_C()
    report["controls"]["B_antichain_C_broken"] = BC
    for r in BC["rows"]:
        print(f"  {r['poset']:>12}  |L|={r['num_LE']:>5}  dimU={r['dim_U']:>3}  "
              f"c_max={r['c_max']:.9f} c_min={r['c_min']:.9f} "
              f"({'PASS' if r['B_PASS_c_is_1'] else 'FAIL'})  "
              f"broken c={r['broken_c_max']:.6f} "
              f"({'PASS' if r['C_PASS_broken_is_not_1'] else 'FAIL'})")
    print(f"  B_ALL_PASS = {BC['B_ALL_PASS']}   C_ALL_PASS = {BC['C_ALL_PASS']}")

    # -------- identity check against the committed mg-8b64 dataset ---------
    print()
    print("-" * 78)
    print("IDENTITY CHECK -- recomputed vs committed mg-8b64 rows, ALL FIELDS")
    print("-" * 78)
    with open(os.path.join(REPO, "data",
                           "onethird-mg8b64-L1b-bk-transport-transfer.json")) as f:
        ref_rows = {r["name"]: r for r in json.load(f)["rows"]}
    identity_targets = dict(named)
    for i in DEGENERATE_LAMBDA2:                     # CONTROL F's two posets
        identity_targets[f"enum-n7-#{i}"] = Ps[i]
    # mg-bd53 finding 4, decided rather than declared away (mg-4f9b).  The seven
    # posets above are all n=7 with |L| in the thousands, and their committed
    # rows carry 23 fields.  54 of the dataset's 1091 rows carry TWENTY-FIVE:
    # `bk_cheeger_exhaustive` only returns a value when |L| is small enough to
    # enumerate cuts, so `h_bk_exhaustive` and `h_bk_argmin_is_pair_cut` exist
    # ONLY on the small-|L| rows -- and were therefore compared at ZERO posets
    # while both the gate and mg-5ad1's part-B census reported "0 fields
    # silently uncompared".  Both statements were true: the census is per-ROW
    # and the gap is per-DATASET.
    #
    # The choice was between comparing them somewhere and declaring them
    # excluded.  COMPARED, because a declared exclusion here would say "the gate
    # does not check a quantity this corpus commits", which is the thing this
    # whole lineage is about, and because the cost is one poset with |L| = 6.
    # `fam:N (2+2)` is the 2+2 poset: n = 4, |L| = 6, genuinely incomparable
    # pairs (so the frozen-pair block is non-empty), and its `h_bk_exhaustive`
    # moves 0.2222 -> 0.0667 under the volume-normalisation flip mg-bd53's C1
    # used, which both gate columns passed byte-identically.
    IDENTITY_SMALL_L_POSET = "N (2+2)"
    _fams = mg8b64_biased_families()
    identity_targets[f"fam:{IDENTITY_SMALL_L_POSET}"] = \
        _fams[IDENTITY_SMALL_L_POSET]
    for name, P in identity_targets.items():
        ref = ref_rows.get(name)
        rec = {"name": name, "num_LE": P.linext_count(),
               "lambda_std": float(lambda_std(P))}
        d, _ = delta_and_frozen_pair(P)
        rec["delta"] = d
        # mg-09ea F3 repair: recompute lambda_2^BK here so the committed
        # reference value has something to be compared AGAINST.  Kept as a
        # SECOND, independent route to bk_lambda2: this one goes through
        # mg-4a86's `bk_walk_matrix`, the row-wide comparison below goes
        # through mg-8b64's, so a mutation in EITHER walk matrix is fatal.
        rec["lambda2_BK"] = slow_eigenspace(bk_walk_matrix(P))[0]
        if ref:
            # mg-5ad1 finding 1: recompute the WHOLE mg-8b64 row with mg-8b64's
            # own row builder and compare every field of the committed row.
            # The committed JSON is the frozen ground truth; the recomputation
            # is what a mutation moves.
            rec_row = mg8b64_analyze_poset(P, name)
            matches, diffs = identity_field_comparisons(rec_row, ref)
            rec["field_matches"] = matches
            rec["field_abs_diffs"] = diffs
            rec["fields_compared"] = len(matches)
            rec["fields_in_reference_row"] = len(ref)
            rec["fields_excluded"] = sorted(IDENTITY_EXCLUDED_REF_FIELDS)
            rec["fields_mismatched"] = sorted(k for k, ok in matches.items()
                                              if not ok)
            rec["max_abs_diff_over_float_fields"] = (max(diffs.values())
                                                     if diffs else 0.0)
            rec["ref_num_LE"] = ref["num_LE"]
            rec["ref_lambda_std"] = ref["lambda_std"]
            rec["ref_delta"] = ref["delta"]
            rec["ref_bk_lambda2"] = ref["bk_lambda2"]
            # The four legacy keys start as ALIASES of four of the row-wide
            # comparisons -- the FIELD axis, mg-75f0's widening.
            for key, field in IDENTITY_LEGACY_FIELDS:
                rec[key] = matches.get(field, False)
            # ... and then the ROUTE axis is ANDed back in, per
            # `IDENTITY_SECOND_ROUTES`.  Each of these is "the gate's own
            # recomputation must ALSO match the committed value", so a mutation
            # that moves mg-8b64's route and a mutation that moves the gate's
            # route are both fatal.  Three of the four have a second route; the
            # fourth (num_LE) says in the table above why it cannot.
            #
            # lambda_std: mg-4a86's implementation vs mgb0a6's, TWO ROUTES.
            # This is mg-bd53 finding 1 -- it is the comparison mg-75f0 removed,
            # and `np.max(w)` -> `np.min(w)` in mg-4a86's `lambda_std` is the
            # one-character mutation the pre-widening gate caught and the
            # widened gate did not.  Restored here (mg-4f9b).
            rec["second_route_lambda_std_ok"] = bool(
                abs(rec["lambda_std"] - ref["lambda_std"])
                < IDENTITY_FLOAT_TOL)
            rec["match_lambda_std"] = bool(rec["match_lambda_std"]
                                           and rec["second_route_lambda_std_ok"])
            rec["field_matches"]["lambda_std"] = rec["match_lambda_std"]
            # delta: shared `before_prob_dp`, separate aggregations.  A WEAKER
            # second route than lambda_std's and labelled as such in the table
            # -- it catches a mutated aggregation on either side, not a mutated
            # pair probability, which would move both routes together.
            rec["second_route_delta_ok"] = bool(
                abs(rec["delta"] - ref["delta"]) < IDENTITY_FLOAT_TOL)
            rec["match_delta"] = bool(rec["match_delta"]
                                      and rec["second_route_delta_ok"])
            rec["field_matches"]["delta"] = rec["match_delta"]
            # bk_lambda2: mg-4a86's walk matrix vs mg-8b64's, TWO ROUTES.  The
            # one mg-75f0 kept; unchanged, and now one of three rather than one
            # of one.
            rec["second_route_bk_lambda2_ok"] = bool(
                abs(rec["lambda2_BK"] - ref["bk_lambda2"]) < 1e-9)
            rec["match_bk_lambda2"] = bool(rec["match_bk_lambda2"]
                                           and rec["second_route_bk_lambda2_ok"])
            rec["field_matches"]["bk_lambda2"] = rec["match_bk_lambda2"]
            # Recompute AFTER the route conjunctions, not before: a field that
            # matches on mg-8b64's route and fails on the gate's own must appear
            # in the mismatch list, or the diagnostic names the wrong thing --
            # mg-75f0's own CONTROL B message was that defect (its sec 5).
            rec["fields_mismatched"] = sorted(k for k, ok
                                              in rec["field_matches"].items()
                                              if not ok)
            rec["second_routes_failed"] = sorted(
                f for f in ("lambda_std", "delta", "bk_lambda2")
                if not rec[f"second_route_{f}_ok"])
        report["identity_check"].append(rec)
        print(f"  {name:>14}  |L|={rec['num_LE']:>4} (ref {rec.get('ref_num_LE')})  "
              f"lam_std={rec['lambda_std']:.9f} (ref {rec.get('ref_lambda_std')})  "
              f"delta={rec['delta']:.6f}  "
              f"lam2_BK={rec['lambda2_BK']:.9f} (ref {rec.get('ref_bk_lambda2')})  "
              f"match={rec.get('match_num_LE')}/{rec.get('match_lambda_std')}/"
              f"{rec.get('match_delta')}/{rec.get('match_bk_lambda2')}")
        if "field_matches" in rec:
            print(f"{'':>16}fields compared {rec['fields_compared']}"
                  f"/{rec['fields_in_reference_row']} "
                  f"(excluded: {','.join(rec['fields_excluded'])})  "
                  f"max|diff| over float fields = "
                  f"{rec['max_abs_diff_over_float_fields']:.2e}  "
                  f"mismatched: {rec['fields_mismatched'] or 'none'}")

    # ---- the census, per DATASET rather than per ROW (mg-bd53 finding 4) ----
    # The per-row census ("N of M, one declared exclusion") is printed above,
    # once per poset, and it is correct FOR THAT ROW.  It structurally cannot
    # see a field that exists only on rows the identity population does not
    # contain, which is exactly how `h_bk_exhaustive` and
    # `h_bk_argmin_is_pair_cut` reached zero comparisons while every printed
    # census read "0 uncompared".  So census the SCHEMA OF THE WHOLE DATASET
    # against the union of what the population actually compared, and fail if
    # anything is in neither that union nor the declared exclusions.  This is
    # what makes the population choice above self-enforcing: drop the small-|L|
    # poset, or add a field that only appears on rows nobody compares, and the
    # gate says so instead of a later audit.
    dataset_schema = sorted({k for r in ref_rows.values() for k in r})
    compared_union = sorted({f for rec in report["identity_check"]
                             for f in rec.get("field_matches", {})})
    dataset_uncompared = [k for k in dataset_schema
                          if k not in compared_union
                          and k not in IDENTITY_EXCLUDED_REF_FIELDS]
    report["identity_census_over_dataset"] = {
        "rows_in_committed_dataset": len(ref_rows),
        "distinct_field_names_over_ALL_rows": len(dataset_schema),
        "identity_population": sorted(identity_targets),
        "field_names_compared_at_at_least_one_poset": len(compared_union),
        "excluded_with_a_reason": sorted(IDENTITY_EXCLUDED_REF_FIELDS),
        "compared_nowhere": dataset_uncompared,
    }
    print(f"{'':>4}CENSUS OVER THE DATASET (not the row): {len(ref_rows)} "
          f"committed rows, {len(dataset_schema)} distinct field names, "
          f"{len(compared_union)} compared at >=1 of the "
          f"{len(identity_targets)} identity posets, "
          f"{len(IDENTITY_EXCLUDED_REF_FIELDS)} excluded with a reason, "
          f"compared NOWHERE: {dataset_uncompared or 'none'}")

    # -------- THE MEASUREMENT ----------------------------------------------
    print()
    print("=" * 78)
    print("MEASUREMENT -- c(P) at the three off-regime posets (+ in-regime)")
    print("=" * 78)
    print(f"{'poset':>14} {'|L|':>5} {'dimU':>5} {'delta':>7} {'lam2_BK':>10} "
          f"{'lam_std':>9} {'dimE':>5} {'c_max':>9} {'c_min':>9} {'null':>7} "
          f"{'frozcap':>8} {'froz|U':>8}")
    for name, P in named.items():
        row = measure(P, name)
        row["regime"] = ("off-regime" if int(name.split("#")[1]) in OFF_REGIME
                         else "in-regime")
        report["measured"].append(row)
        print(f"{name:>14} {row['num_LE']:>5} {row['dim_U']:>5} "
              f"{row['delta']:>7.4f} {row['lambda2_BK']:>10.6f} "
              f"{row['lambda_std']:>9.6f} {row['dim_eigenspace']:>5} "
              f"{row['c_max']:>9.6f} {row['c_min']:>9.6f} "
              f"{row['null_random_subspace']:>7.4f} "
              f"{row.get('frozen_pairmode_capture', float('nan')):>8.4f} "
              f"{row.get('frozen_pair_overlap_with_U', float('nan')):>8.4f}")
    maxdiff = max(r["check0_abs_diff_c"] for r in report["measured"])
    print(f"\n  CHECK-0 (agreement with mg-4a86 sd_quant_constant): "
          f"max |diff| = {maxdiff:.2e}")
    report["controls"]["check0_max_abs_diff_c"] = maxdiff

    print()
    print("-" * 78)
    print("CONTROL D -- random dim-U subspace null on the measured posets")
    print("-" * 78)
    Dres = []
    for name, P in named.items():
        d = control_D(P, name)
        Dres.append(d)
        print(f"  {name:>14}  random c_max mean={d['random_c_max_mean']:.6f} "
              f"max={d['random_c_max_max']:.6f}  "
              f"analytic null={d['analytic_null_dimU_over_m']:.6f}")
    report["controls"]["D_random_subspace"] = Dres

    # -------- CONTROL F -- two-sided reading-dependence, on REAL data --------
    # mg-5ad1 finding 4: the reading-dependence check is vacuous at the five
    # measured posets because lambda_2^BK is simple there, so mg-60d3's F4
    # repair bought coverage on three synthetic antichains only.  These two
    # posets are the real-data coverage, and dim_E > 1 is ASSERTED so the
    # coverage cannot quietly evaporate.
    print()
    print("-" * 78)
    print("CONTROL F -- two-sided reading-dependence on real posets with a "
          "DEGENERATE lambda_2")
    print("-" * 78)
    Frows = []
    for i in DEGENERATE_LAMBDA2:
        nm = f"enum-n7-#{i}"
        r = measure(Ps[i], nm)
        r["F_PASS_two_sided"] = _two_sided_row_ok(r)
        Frows.append(r)
        print(f"  deg {nm:>14}  |L|={r['num_LE']:>4} dimU={r['dim_U']:>3} "
              f"dimE={r['dim_eigenspace']:>2} c_max={r['c_max']:.9f} "
              f"c_min={r['c_min']:.9f} |c_max-c_min|="
              f"{abs(r['c_max'] - r['c_min']):.2e} "
              f"({'PASS' if r['F_PASS_two_sided'] else 'FAIL'})")
    report["controls"]["F_two_sided_real_coverage"] = {
        "why": "the dim_eigenspace > 1 branch of the gate is vacuous at the "
               "five measured posets (lambda_2^BK simple); these are the n=7 "
               "both-connected posets where it is not",
        "rows": Frows,
        "F_ALL_PASS": all(r["F_PASS_two_sided"] for r in Frows)}
    print(f"  F_ALL_PASS = "
          f"{report['controls']['F_two_sided_real_coverage']['F_ALL_PASS']}")

    # -------- families / named stress posets, n up to 10 --------------------
    # NOT a population: these are the corpus's own mandated stress cases
    # (mg-8b64 `biased_families` + mg-b0a6 `named_posets`).  Their only job
    # here is to bound the "n = 7 is too small to see it" reading -- they can
    # falsify a c ~ 1 pattern at larger n, they cannot establish one.
    print()
    print("-" * 78)
    print("FAMILY / NAMED STRESS POSETS (n up to 10) -- falsification probe only")
    print("-" * 78)
    fam_rows = []
    for nm, P in list(mg8b64_biased_families().items()) + list(named_posets().items()):
        if P.linext_count() < 2 or P.linext_count() > 2200:
            continue
        r = measure(P, f"fam:{nm}")
        if r is None:
            continue
        fam_rows.append(r)
        print(f"  {nm:>26} n={r['n']:>2} |L|={r['num_LE']:>5} dimU={r['dim_U']:>3} "
              f"delta={(('%.4f' % r['delta']) if r['delta'] is not None else '  -   ')} "
              f"lam2={r['lambda2_BK']:.6f} lam_std={r['lambda_std']:.6f} "
              f"c={r['c_max']:.6f} null={r['null_random_subspace']:.4f}")
    report["families"] = fam_rows
    if fam_rows:
        cm = [r["c_max"] for r in fam_rows]
        print(f"  min c over {len(fam_rows)} family posets = {min(cm):.6f} "
              f"(at {fam_rows[cm.index(min(cm))]['name']})")

    # -------- population sweep ---------------------------------------------
    if not args.no_sweep:
        print()
        print("=" * 78)
        print("POPULATION SWEEP -- all n=7 both-connected posets")
        print("=" * 78)
        sweep = []
        for i, P in enumerate(Ps):
            r = measure(P, f"enum-n7-#{i}", with_mechanism=True)
            if r is None:
                continue
            r["index"] = i
            sweep.append(r)
            if (i + 1) % 100 == 0:
                print(f"  ... {i+1}/{len(Ps)}")
        # ---- close the dedup gap: measure every isomorphism class ----------
        # mg-8b64's iso_signature dedup is not a canonical form, so `Ps` misses
        # some classes.  Enumerate undeduped, canonicalise, measure whatever the
        # dedup dropped, and fold it into the population.
        print()
        print("  ISO-COMPLETENESS: closing mg-8b64's dedup gap ...")
        und = enumerate_both_connected(7, dedup=False)
        classes = {}
        for Q in und:
            classes.setdefault(canon(Q), Q)
        have = {canon(Q) for Q in Ps}
        missing = [Q for cf, Q in classes.items() if cf not in have]
        print(f"    naturally-labelled both-connected n=7 : {len(und)}")
        print(f"    TRUE isomorphism classes              : {len(classes)}")
        print(f"    classes in mg-8b64's deduped list     : {len(have)}")
        print(f"    classes DROPPED by its dedup          : {len(missing)}"
              f"  -- measuring them now")
        gap = []
        for j, Q in enumerate(missing):
            r = measure(Q, f"isogap-n7-#{j}")
            if r is None:
                continue
            r["relation"] = sorted((int(a), int(b)) for b in range(Q.n)
                                   for a in Q.less[b])
            gap.append(r)
            print(f"      isogap-n7-#{j}  |L|={r['num_LE']:>4} "
                  f"dimU={r['dim_U']:>3} delta={r['delta']:.4f} "
                  f"c={r['c_max']:.6f} null={r['null_random_subspace']:.4f}")
        report["iso_completeness"] = {
            "naturally_labelled_both_connected": len(und),
            "true_iso_classes": len(classes),
            "classes_in_mg8b64_dedup": len(have),
            "classes_dropped_by_dedup": len(missing),
            "dropped_class_rows": gap,
            "min_c_over_dropped": (min(r["c_max"] for r in gap) if gap else None),
        }
        allc = [r["c_max"] for r in sweep] + [r["c_max"] for r in gap]
        report["iso_completeness"]["min_c_over_ALL_classes"] = min(allc)
        report["iso_completeness"]["classes_measured_total"] = len(allc)
        print(f"    => c measured on ALL {len(allc)} n=7 both-connected "
              f"isomorphism classes; min c = {min(allc):.6f}")

        # ---- Lemma 3.1 verification over the population --------------------
        thr_hit = thr_tot = 0
        for r in sweep:
            if r.get("frozen_pair_overlap_with_U", 0) > 1 - 1e-9:
                thr_tot += 1
                Q = Ps[r["index"]]
                x, y = r["frozen_pair"]
                if threshold_witness(Q, x, y) is not None:
                    thr_hit += 1
        report["lemma_3_1_check"] = {
            "posets_with_frozen_pair_indicator_exactly_in_U": thr_tot,
            "of_which_satisfy_the_threshold_hypothesis": thr_hit,
        }
        print(f"  LEMMA 3.1: of the {thr_tot} posets whose frozen-pair "
              f"indicator lies exactly in U, {thr_hit} satisfy the lemma's "
              f"threshold hypothesis")

        report["sweep"] = {"n": 7, "count": len(sweep), "rows": sweep}
        _sweep_summary(report["sweep"], sweep)

    # `--no-sweep` is the CI control mode.  It must NOT overwrite the committed
    # dataset with a sweep-less copy -- the doc's §5/§6 tables would silently
    # lose their source.
    if args.no_sweep:
        print("\n(--no-sweep: control mode, committed dataset left untouched)")
    else:
        out = os.path.join(REPO, "data", "onethird-mg2c34-n7-overlap.json")
        with open(out, "w") as f:
            json.dump(report, f, indent=2)
        print(f"\nwrote {os.path.relpath(out, REPO)}")

    # ---------------------------------------------------------------- gate --
    # This script is a CONTROL, so it must be able to fail.  Exit non-zero if
    # any control or identity check is wrong -- a control nobody can fail is
    # indistinguishable from no control at all (the mg-4ad1 lesson, applied to
    # this file).
    failures = []
    if not A["ALL_PASS"]:
        failures.append("CONTROL A (graded analytic) did not reproduce cos^2(theta)")
    if not BC["B_ALL_PASS"]:
        # mg-75f0: this message used to read "antichain c != 1 (Aldous/CLR)",
        # which misattributed the cause once `_antichain_row_ok` gained the
        # dim-U conjunct -- under a broken rank filter c IS 1 and it is dim U
        # that is wrong, so the message named the one thing that had not
        # failed, and cited a theorem that does not license the assertion
        # anyway.  A diagnostic that misdirects the reader is the same genre of
        # defect as a control that cannot fail.  All three conjuncts are now
        # printed for every failing row, so the reader does not have to guess.
        bad = "; ".join(
            f"{r['poset']}: c_max={r['c_max']:.9f} c_min={r['c_min']:.9f} "
            f"dim_U={r['dim_U']} (known {r['dim_U_known']})"
            for r in BC["rows"] if not r["B_PASS_c_is_1"])
        failures.append(
            "CONTROL B: the antichain known-answer check failed.  Required: "
            "c_max = c_min = 1 (the whole gap EIGENSPACE inside U -- see "
            "_antichain_row_ok for what licenses that, which is NOT "
            "Aldous/CLR) AND dim U = (n-1)^2+1 (the known rank of the "
            f"one-particle span on S_n).  {bad}")
    if not BC["C_ALL_PASS"]:
        failures.append("CONTROL C: the BROKEN projector still returned 1 -- "
                        "CONTROL B is vacuous")
    if maxdiff > 1e-12:
        failures.append(f"CHECK-0: disagreement with mg-4a86's instrument "
                        f"({maxdiff:.2e})")
    if not report["controls"]["F_two_sided_real_coverage"]["F_ALL_PASS"]:
        failures.append("CONTROL F: two-sided reading-dependence on a real "
                        "poset with degenerate lambda_2 -- either c_max != "
                        "c_min, or the degeneracy that gives this control its "
                        "coverage has gone (see _two_sided_row_ok)")
    for rec in report["identity_check"]:
        if "ref_num_LE" not in rec:
            failures.append(f"{rec['name']}: no mg-8b64 reference row found")
        elif not _identity_row_ok(rec):
            failures.append(f"{rec['name']}: does not match its committed "
                            f"mg-8b64 row -- poset identity is WRONG "
                            f"(num_LE={rec['match_num_LE']} "
                            f"lambda_std={rec['match_lambda_std']} "
                            f"delta={rec['match_delta']} "
                            f"lambda2_BK={rec['match_bk_lambda2']})"
                            + (f"; ALL mismatched fields of the "
                               f"{rec['fields_compared']} compared: "
                               f"{','.join(rec['fields_mismatched'])}"
                               if rec.get("fields_mismatched") else "")
                            + (f"; SECOND ROUTE disagrees on "
                               f"{','.join(rec['second_routes_failed'])} -- "
                               f"the gate's own recomputation differs from the "
                               f"committed value even where mg-8b64's route "
                               f"agrees (see IDENTITY_SECOND_ROUTES)"
                               if rec.get("second_routes_failed") else ""))
    # The ROUTE axis must stay declared.  mg-bd53 finding 1 was a comparison
    # removed with nothing recording that it had been; this is the check that a
    # later edit cannot repeat it silently.
    for problem in _identity_routes_declared():
        failures.append(f"IDENTITY ROUTES: {problem}")
    # The per-DATASET census (mg-bd53 finding 4).  A committed field compared at
    # no poset is the "never exercised" sibling of this arc's defect, and it is
    # invisible to every per-row census by construction.
    if dataset_uncompared:
        failures.append(
            f"IDENTITY CENSUS: {len(dataset_uncompared)} field(s) of the "
            f"committed mg-8b64 dataset are compared at NO poset and are not "
            f"declared exclusions: {','.join(dataset_uncompared)}.  Either add "
            f"a poset to the identity population whose row carries them, or "
            f"list them in IDENTITY_EXCLUDED_REF_FIELDS with a reason -- an "
            f"undeclared exclusion is the mg-09ea/mg-5ad1 defect one field "
            f"later")
    # CONTROL E's population is `report["measured"]`, the five named posets.
    # NOT the family block: on hosts with |L| <= n (the `fam:1||chain*` family)
    # U legitimately IS everything, and those rows are a falsification probe
    # rather than a measurement.  Not CONTROL F's two either -- `projector_U` is
    # global, so a rank-filter mutation cannot hide from five posets and appear
    # at a sixth; adding them would be more lines and no more coverage.
    for r in report["measured"]:
        if r["dim_eigenspace"] > 1 and abs(r["c_max"] - r["c_min"]) > 1e-9:
            failures.append(f"{r['name']}: lambda_2 degenerate with c_max != "
                            f"c_min -- the reported c is reading-dependent")
        if not _projector_row_ok(r):
            failures.append(f"{r['name']}: CONTROL E -- dim U = {r['dim_U']} "
                            f"violates its structural bound "
                            f"(n-1)^2+1 = {(r['n'] - 1) ** 2 + 1} or is not a "
                            f"PROPER subspace of |L| = {r['num_LE']} "
                            f"(null = {r['null_random_subspace']:.4f}); the "
                            f"projector's rank filter is admitting directions "
                            f"the one-particle span does not contain, and "
                            f"c = null is vacuous by sec 2's own criterion")
    if failures:
        print("\nCONTROL FAILURES:")
        for m in failures:
            print(f"  - {m}")
        return 1
    print("\nAll controls and identity checks PASSED.")
    return 0


def _sweep_summary(container, sweep):
    cm = np.array([r["c_max"] for r in sweep])
    cn = np.array([r["c_min"] for r in sweep])
    dl = np.array([r["delta"] for r in sweep])
    nl = np.array([r["null_random_subspace"] for r in sweep])
    gap = np.array([r["bk_gap"] for r in sweep])
    print(f"  posets: {len(sweep)}   c_max: min={cm.min():.6f} "
          f"median={np.median(cm):.6f} max={cm.max():.6f}")
    print(f"  c_min : min={cn.min():.6f} median={np.median(cn):.6f}")
    bands = [(0.0, 1/3), (1/3, 0.40), (0.40, 0.45), (0.45, 0.5001)]
    stats = []
    for lo, hi in bands:
        sel = (dl >= lo) & (dl < hi)
        if not sel.any():
            continue
        s = {"delta_lo": lo, "delta_hi": hi, "count": int(sel.sum()),
             "c_max_min": float(cm[sel].min()),
             "c_max_median": float(np.median(cm[sel])),
             "c_max_max": float(cm[sel].max()),
             "c_min_median": float(np.median(cn[sel])),
             "null_median": float(np.median(nl[sel])),
             "frac_c_below_null": float((cm[sel] < nl[sel]).mean()),
             "frac_c_above_0.9": float((cm[sel] > 0.9).mean())}
        stats.append(s)
        print(f"  delta in [{lo:.4f},{hi:.4f}): n={s['count']:>4}  "
              f"c_max median={s['c_max_median']:.4f} "
              f"min={s['c_max_min']:.4f} max={s['c_max_max']:.4f}  "
              f"null median={s['null_median']:.4f}  "
              f"frac(c>0.9)={s['frac_c_above_0.9']:.3f}  "
              f"frac(c<null)={s['frac_c_below_null']:.3f}")
    container["delta_bands"] = stats
    # the frozen (delta < 1/3) stratum is EMPTY at n=7 (no counterexamples);
    # report the closest-to-frozen decile explicitly rather than silently.
    order = np.argsort(dl)
    k = max(1, len(sweep) // 10)
    idx = order[:k]
    container["lowest_delta_decile"] = {
        "count": int(k), "delta_max": float(dl[idx].max()),
        "c_max_min": float(cm[idx].min()),
        "c_max_median": float(np.median(cm[idx])),
        "frac_c_above_0.9": float((cm[idx] > 0.9).mean())}
    print(f"  lowest-delta decile (delta <= {dl[idx].max():.4f}): "
          f"c_max median={np.median(cm[idx]):.4f} min={cm[idx].min():.4f} "
          f"frac(c>0.9)={(cm[idx] > 0.9).mean():.3f}")
    # correlation of c with delta and with the BK gap
    container["corr_c_delta"] = float(np.corrcoef(cm, dl)[0, 1])
    container["corr_c_bkgap"] = float(np.corrcoef(cm, gap)[0, 1])
    print(f"  corr(c_max, delta) = {container['corr_c_delta']:.4f}   "
          f"corr(c_max, bk_gap) = {container['corr_c_bkgap']:.4f}")

    # THE TRANSFER RATIO.  L1b wants  (1 - lambda_std) <= K (1 - lambda_2^BK).
    # R = required modulus at this poset.  If c controlled the transfer, R would
    # be bounded by a function of c; c is pinned within 2% of 1 across the whole
    # population, so any spread in R is spread c cannot account for.
    ls = np.array([r["lambda_std"] for r in sweep])
    l2 = np.array([r["lambda2_BK"] for r in sweep])
    R = (1.0 - ls) / (1.0 - l2)
    j = int(np.argmax(R))
    container["transfer_ratio"] = {
        "definition": "R = (1 - lambda_std) / (1 - lambda_2^BK); the modulus "
                      "K that L1b would need at this poset",
        "min": float(R.min()), "median": float(np.median(R)),
        "max": float(R.max()),
        "argmax_name": sweep[j]["name"], "argmax_c_max": float(cm[j]),
        "corr_c_R": float(np.corrcoef(cm, R)[0, 1]),
        "corr_c_logR": float(np.corrcoef(cm, np.log(R))[0, 1]),
    }
    print(f"  transfer ratio R=(1-lam_std)/(1-lam2_BK): min={R.min():.4f} "
          f"median={np.median(R):.4f} max={R.max():.4f} "
          f"(at {sweep[j]['name']}, c={cm[j]:.6f})")
    print(f"  corr(c_max, R) = {container['transfer_ratio']['corr_c_R']:.4f} "
          f"-- POSITIVE: higher overlap goes with a LARGER required modulus")

    # the mechanism claim, over the population
    fu = np.array([r["frozen_pair_overlap_with_U"] for r in sweep
                   if r.get("frozen_pair_overlap_with_U") is not None])
    fc = np.array([r["frozen_pairmode_capture"] for r in sweep
                   if r.get("frozen_pairmode_capture") is not None])
    container["frozen_pair_overlap_with_U"] = {
        "min": float(fu.min()), "median": float(np.median(fu)),
        "max": float(fu.max()),
        "frac_exactly_1_within_1e-9": float((fu > 1 - 1e-9).mean()),
        "count_exactly_1": int((fu > 1 - 1e-9).sum()),
    }
    container["frozen_pairmode_capture"] = {
        "min": float(fc.min()), "median": float(np.median(fc)),
        "max": float(fc.max())}
    print(f"  frozen-pair indicator's OWN overlap with U: min={fu.min():.4f} "
          f"median={np.median(fu):.4f} max={fu.max():.4f}; "
          f"EXACTLY 1 in {int((fu > 1 - 1e-9).sum())}/{len(fu)} posets")
    container["dim_eigenspace_max"] = int(max(r["dim_eigenspace"] for r in sweep))
    container["frac_lambda2_simple"] = float(
        np.mean([r["dim_eigenspace"] == 1 for r in sweep]))
    print(f"  lambda_2 eigenspace: max dim = {container['dim_eigenspace_max']}, "
          f"simple in {container['frac_lambda2_simple']*100:.2f}% of posets "
          f"(so c_max = c_min: no favourable-reading loophole)")
    # extreme tails, named
    lo_idx = np.argsort(cm)[:10]
    container["lowest_c_posets"] = [
        {"name": sweep[j]["name"], "c_max": float(cm[j]), "c_min": float(cn[j]),
         "delta": float(dl[j]), "null": float(nl[j]),
         "num_LE": sweep[j]["num_LE"],
         "pairmode_capture": sweep[j].get("pairmode_capture")}
        for j in lo_idx]
    print("  ten lowest c_max:")
    for e in container["lowest_c_posets"]:
        print(f"    {e['name']:>14} c_max={e['c_max']:.6f} "
              f"c_min={e['c_min']:.6f} delta={e['delta']:.4f} "
              f"null={e['null']:.4f} |L|={e['num_LE']}")


if __name__ == "__main__":
    sys.exit(main())
