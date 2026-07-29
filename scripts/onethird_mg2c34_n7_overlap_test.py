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
         `sd_quant_constant` to 1e-12 on every poset measured.

CONTROL A (graded, analytic, CAN FAIL AT EVERY POINT).  On a real L(P), build a
         synthetic symmetric walk whose lambda_2 eigenvector is
         v(theta) = cos(theta) u + sin(theta) w  with u a unit vector in
         U (+) const^perp and w a unit vector orthogonal to U.  The true answer
         is c = cos^2(theta), KNOWN in closed form for every theta.  The
         instrument is required to return it to 1e-9 -- including c = 0 at
         theta = 90 deg.  This is the control that shows the instrument is able
         to output 0: an instrument that cannot output 0 cannot refute
         SD-quant, and an instrument that cannot output 1 cannot confirm it.

CONTROL B (known-answer poset).  Antichain A_n, n = 4,5,6: L(P) = S_n, the BK
         chain is the interchange process on the path, and by Aldous/CLR the
         slowest mode IS the single-particle mode, which lies in U.  Required:
         c = 1.

CONTROL C (deliberately BROKEN instrument, must fail control B).  Replace U by
         a fixed coordinate subspace of the SAME dimension.  On the antichain
         the true answer is 1; the broken instrument must NOT return 1.  This
         is what makes CONTROL B non-vacuous.

CONTROL D (dimension-artifact null, must fail on the in-regime posets).
         Replace U by a RANDOM subspace of the same dimension (seeded).  Any
         c ~ 1 that survives this substitution was an artifact of dim U, not
         evidence of standard dominance.

Reproducibility: no randomness except CONTROL D, which is seeded
(`numpy.random.default_rng(20260729)`).  Every number in the deliverable comes
from `data/onethird-mg2c34-n7-overlap.json`, written by this file.

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
)

EIG_TOL = 1e-9            # mg-4a86's degeneracy tolerance, kept verbatim
NEAR_TOL = 1e-6           # honest "near-degenerate" band, reported separately
SEED = 20260729

# The three posets the corpus names, plus the in-regime contrast block from
# OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:295-300.
OFF_REGIME = [3, 20, 600]
IN_REGIME = [945, 809]


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
        rows.append({
            "poset": f"antichain-{n}", "num_LE": m, "dim_U": int(dimU),
            "lambda2_BK": lam2, "c_max": c_max, "c_min": c_min,
            "B_PASS_c_is_1": abs(c_max - 1.0) < 1e-8,
            "broken_c_max": cb_max,
            "C_PASS_broken_is_not_1": abs(cb_max - 1.0) > 1e-3,
        })
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
              f"c={r['c_max']:.9f} ({'PASS' if r['B_PASS_c_is_1'] else 'FAIL'})  "
              f"broken c={r['broken_c_max']:.6f} "
              f"({'PASS' if r['C_PASS_broken_is_not_1'] else 'FAIL'})")
    print(f"  B_ALL_PASS = {BC['B_ALL_PASS']}   C_ALL_PASS = {BC['C_ALL_PASS']}")

    # -------- identity check against the committed mg-8b64 dataset ---------
    print()
    print("-" * 78)
    print("IDENTITY CHECK -- recomputed vs committed mg-8b64 rows")
    print("-" * 78)
    with open(os.path.join(REPO, "data",
                           "onethird-mg8b64-L1b-bk-transport-transfer.json")) as f:
        ref_rows = {r["name"]: r for r in json.load(f)["rows"]}
    for name, P in named.items():
        ref = ref_rows.get(name)
        rec = {"name": name, "num_LE": P.linext_count(),
               "lambda_std": float(lambda_std(P))}
        d, _ = delta_and_frozen_pair(P)
        rec["delta"] = d
        if ref:
            rec["ref_num_LE"] = ref["num_LE"]
            rec["ref_lambda_std"] = ref["lambda_std"]
            rec["ref_delta"] = ref["delta"]
            rec["ref_bk_lambda2"] = ref["bk_lambda2"]
            rec["match_num_LE"] = rec["num_LE"] == ref["num_LE"]
            rec["match_lambda_std"] = abs(rec["lambda_std"] - ref["lambda_std"]) < 1e-9
            rec["match_delta"] = abs(rec["delta"] - ref["delta"]) < 1e-9
        report["identity_check"].append(rec)
        print(f"  {name:>14}  |L|={rec['num_LE']:>4} (ref {rec.get('ref_num_LE')})  "
              f"lam_std={rec['lambda_std']:.9f} (ref {rec.get('ref_lambda_std')})  "
              f"delta={rec['delta']:.6f}  "
              f"match={rec.get('match_num_LE')}/{rec.get('match_lambda_std')}/"
              f"{rec.get('match_delta')}")

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
        failures.append("CONTROL B: antichain c != 1 (Aldous/CLR)")
    if not BC["C_ALL_PASS"]:
        failures.append("CONTROL C: the BROKEN projector still returned 1 -- "
                        "CONTROL B is vacuous")
    if maxdiff > 1e-12:
        failures.append(f"CHECK-0: disagreement with mg-4a86's instrument "
                        f"({maxdiff:.2e})")
    for rec in report["identity_check"]:
        if "ref_num_LE" not in rec:
            failures.append(f"{rec['name']}: no mg-8b64 reference row found")
        elif not (rec["match_num_LE"] and rec["match_lambda_std"]
                  and rec["match_delta"]):
            failures.append(f"{rec['name']}: does not match its committed "
                            f"mg-8b64 row -- poset identity is WRONG")
    for r in report["measured"]:
        if r["dim_eigenspace"] > 1 and abs(r["c_max"] - r["c_min"]) > 1e-9:
            failures.append(f"{r['name']}: lambda_2 degenerate with c_max != "
                            f"c_min -- the reported c is reading-dependent")
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
