#!/usr/bin/env python3
"""
OneThird mg-8201: BETTER L1b -- certify lambda_std ~ 1 with a NON-INDICATOR
(expected-rank) test vector, avoiding the thin-prefix / LIB bottleneck.

Ticket: mg-8201 (high, repo one_third_width_three). Daniel full-speed, no gate.
Continuation of the 1/3-2/3 spectral / near-ordinal-sum program. Source:
spectral_near_ordinal_sum_program.tex; pm-onethird memory
project_spectral_near_ordinal_sum_program.md. Work THIS program only.

WHY (the circularity diagnosis)
-------------------------------
The prior L1b route (mg-8b64) tried to force lambda_std ~ 1 from a low-conductance
BK PAIR-INDICATOR cut. Certifying bad mixing with a prefix/indicator test function
really certifies a THIN PREFIX -- the near-ordinal-sum CONCLUSION -- not mere bad
mixing. That collapsed to LIB (E[inv_e] = O(n/gamma) linear-inversions), which
Daniel + PM judge the WRONG (near-circular) target: it demands an over-strong
linear-inversions bound.

THE BETTER IDEA
---------------
1 - lambda_std(P) = min_{f in H} energy(f)/||f||^2, where (program Prop.,
transport-energy identity)
    energy(f) = <f,(I-S_P)f> = (1/(2|L|)) sum_{sigma} sum_a (f_a - f_{sigma(a)})^2.
For ANY fixed test vector f in H,
    lambda_std(P) >= R(f) := <f,S_P f>/||f||^2 = 1 - energy(f)/||f||^2.
So a single GLOBAL, SMOOTH test vector with small normalized energy certifies
lambda_std ~ 1 WITHOUT a prefix. The lead candidate (program Sec 7) is the
EXPECTED-RANK vector
    r = T_P u,   u_a = a - (n-1)/2   (centred position),   r_x = E[pos(x)] - (n-1)/2,
which aggregates ALL pairwise biases (Sec 7 identity E[pos(x)] = 1 + sum_z Pr[z<x]).
b0a6 showed the dominant standard eigenvector tracks expected rank; r is its natural
smooth proxy and exploits ALL-pairs-frozen, not a thin prefix.

WHAT THIS SCRIPT DOES
---------------------
STEP 1 (diagnostic, cheap): across the enumerated + family ensemble measure
E[inv_e] (expected # of e-inversions) vs lambda_std. If high lambda (0.9-0.99)
co-occurs with SUPER-linear E[inv_e], the prefix/LIB route is confirmed LOSSY (a
linear-inversions bound is NOT necessary for bad mixing).

STEP 2 (main): for each poset compute R(f) for the non-indicator candidates
    r  = centred expected rank        (the lead candidate)
    u  = centred linear position in e (program Sec 9 crude vector; R(u) > 1/3)
    v  = dominant standard eigenvector (R(v) = lambda_std exactly; the ceiling)
and the bias-signed vector. Track R(r) vs delta and vs max_bias: does R(r) -> 1
in the frozen regime (delta -> 1/3, max_bias -> 1)? Does r beat u toward 1-o(1)?

STEP 3 (LaTeX-first, separate doc): prove or wall. If r empirically drives
lambda_std -> 1 in-regime, attempt a rigorous bound on energy(r) from delta<1/3;
else name the wall.

SKEPTICAL BAR (pm-onethird feedback_empirical_green_is_not_proven): a high Rayleigh
quotient is EMPIRICAL EVIDENCE, not a proof. R(r) is a genuine lower bound on
lambda_std for each poset, but "R(r) -> 1 in-regime" across a finite ensemble is
not a theorem; a claimed proof must bound energy(r) rigorously from delta<1/3.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

import numpy as np

# Reuse the b0a6 engine verbatim (mandated: "reuse the b0a6/3ce3/8b64 engines").
from onethird_mgb0a6_spectral_killshot_probe import (
    Poset,
    ONE_THIRD, TWO_THIRDS,
    transport_matrix, standard_block_and_lambda, expected_rank,
    before_prob_dp,
    enumerate_both_connected, named_posets, _pearson,
    _LCG, _random_poset,
)
from onethird_mg8b64_L1b_bk_transport_transfer_probe import (
    biased_families, _width,
)

LE_ENUM_CAP = 40320   # 8! -- max |L(P)| for a frozen-tower family member (few, cheap)
SAMPLE_LE_CAP = 5040  # 7! -- max |L(P)| for a RANDOM sampled poset (keeps analysis fast)


# ==========================================================================
# Test vectors and their Rayleigh quotients / normalized energies.
# ==========================================================================
def _centre(f: np.ndarray) -> np.ndarray:
    return f - f.mean()


def rayleigh_vec(S: np.ndarray, f: np.ndarray) -> Optional[float]:
    """R(f) = <f,S f>/<f,f> for a vector f (centred onto H first). This is a
    rigorous LOWER bound on lambda_std for every fixed f in H."""
    f = _centre(np.asarray(f, dtype=float))
    d = float(f @ f)
    if d < 1e-14:
        return None
    return float(f @ S @ f) / d


def before_matrix(P: Poset) -> Tuple[np.ndarray, int]:
    """B[x,y] = Pr[element x appears before element y] over uniform LE(P),
    computed ONCE from the enumerated linear extensions. Scales as O(|LE|*n^2),
    NEVER the O(2^n) ideal DP -- essential for the large-n frozen towers."""
    n = P.n
    les = P.linear_extensions()
    tot = len(les)
    cnt = np.zeros((n, n))                       # cnt[x,y] = #LE with x before y
    for perm in les:
        posn = [0] * n
        for i, x in enumerate(perm):
            posn[x] = i
        for x in range(n):
            px = posn[x]
            for y in range(n):
                if px < posn[y]:
                    cnt[x, y] += 1
    return cnt / tot, tot


def _lambda_std_from_S(S: np.ndarray) -> float:
    """Top eigenvalue of S restricted to H = 1^perp."""
    n = S.shape[0]
    M = np.eye(n) - np.ones((n, n)) / n
    w, V = np.linalg.eigh(M)
    B = V[:, [i for i in range(n) if w[i] > 0.5]]
    Sh = B.T @ S @ B
    return float(np.max(np.linalg.eigvalsh(Sh)))


def _row_from(name: str, n: int, S: np.ndarray, B: np.ndarray, er: np.ndarray,
              num_LE: int, width: int, incomp_pairs, sumdisp2: float) -> dict:
    """Shared metric computation from the symmetrized block S, the before-matrix B,
    the expected-rank vector er, and sumdisp2 = E_sigma[sum_a (a - erank(sigma(a)))^2]
    (the expected squared e-rank displacement; feeds the LOCALITY lemma of Step 3).
    Used by BOTH the brute analyze() and the ordinal-sum assembler analyze_osum()."""
    lam = _lambda_std_from_S(S)
    e_order = sorted(range(n), key=lambda x: (er[x], x))
    r = _centre(er.copy())                       # centred expected rank (r = T_P u)
    rank_of = {x: i for i, x in enumerate(e_order)}
    u = np.array([rank_of[x] - (n - 1) / 2.0 for x in range(n)])   # linear pos in e
    bvec = 2.0 * er - (n - 1)                     # signed net-bias (affine of er)
    R_r = rayleigh_vec(S, r)
    R_u = rayleigh_vec(S, u)
    R_b = rayleigh_vec(S, bvec)
    R_v = lam
    # best PREFIX-INDICATOR certificate: max_k R(1_{A_k}), A_k = first k in e-order.
    # This is exactly the prefix/LIB route's test function -- compare R(r) against it.
    best_prefix_R = None
    for k in range(1, n):
        A = e_order[:k]
        f = np.zeros(n)
        f[A] = 1.0
        rq = rayleigh_vec(S, f)
        if rq is not None and (best_prefix_R is None or rq > best_prefix_R):
            best_prefix_R = rq
    pos_e = {x: i for i, x in enumerate(e_order)}
    mins, maxs = [], []
    einv = 0.0
    num_incomp = 0
    for (x, y) in incomp_pairs:
        p = float(B[x, y])
        mins.append(min(p, 1 - p))
        maxs.append(max(p, 1 - p))
        num_incomp += 1
        a, b = (x, y) if pos_e[x] < pos_e[y] else (y, x)
        einv += float(B[b, a])
    delta = max(mins) if num_incomp else None
    max_bias = max(maxs) if num_incomp else None
    row = dict(
        name=name, n=n, num_LE=num_LE, width=width,
        lambda_std=lam, gap=1.0 - lam,
        delta=delta, max_bias=max_bias, num_incomp=num_incomp, E_inv_e=einv,
        R_r=R_r, R_u=R_u, R_bias=R_b, R_v=R_v,
        best_prefix_R=best_prefix_R,
        r_beats_prefix=(1 if (best_prefix_R is not None and R_r is not None
                              and R_r >= best_prefix_R - 1e-9) else 0),
        r_minus_prefix=((R_r - best_prefix_R)
                        if (best_prefix_R is not None and R_r is not None) else None),
        energy_r=(1.0 - R_r) if R_r is not None else None,
        energy_u=(1.0 - R_u) if R_u is not None else None,
        # raw (un-normalized) energy of r and ||r||^2 -- feed the Step-3 scaling laws
        raw_energy_r=float(r @ (np.eye(n) - S) @ r),
        r_norm2=float(r @ r),
        E_sumdisp2=sumdisp2,
        # locality ratio E[sum disp^2] / E[inv_e] -- bounded => LOCALITY lemma holds
        locality_ratio=(sumdisp2 / einv) if einv > 1e-12 else None,
        r_capture=(R_r / lam) if (R_r is not None and lam > 1e-12) else None,
        u_capture=(R_u / lam) if (R_u is not None and lam > 1e-12) else None,
        r_minus_u=((R_r - R_u) if (R_r is not None and R_u is not None) else None),
        ceiling_minus_r=((lam - R_r) if R_r is not None else None),
    )
    return row


def analyze(P: Poset, name: str) -> Optional[dict]:
    n = P.n
    if n < 2:
        return None
    T = transport_matrix(P)
    S = (T + T.T) / 2.0
    B, tot = before_matrix(P)                    # B[x,y]=Pr[x before y] (from LE list)
    er = B.sum(axis=0)                           # E[pos(x)] = sum_y Pr[y before x]
    # E[sum_a (a - erank(sigma(a)))^2]: e-rank displacement, from the LE list.
    e_order = sorted(range(n), key=lambda x: (er[x], x))
    erank = {x: i for i, x in enumerate(e_order)}   # element -> e-rank
    les = P.linear_extensions()
    sd2 = 0.0
    for perm in les:
        for a, x in enumerate(perm):             # position a holds element x
            sd2 += (a - erank[x]) ** 2
    sumdisp2 = sd2 / len(les)
    return _row_from(name, n, S, B, er, tot, _width(P),
                     list(P.incomparable_pairs()), sumdisp2)


def analyze_osum(gadgets: List[Poset], name: str) -> Optional[dict]:
    """EXACT analysis of an ordinal sum g_1 (+) g_2 (+) ... via block structure --
    no n! LE enumeration, so towers reach large n. In an ordinal sum every element
    stays inside its gadget's position block, so the transport matrix is
    block-diagonal (block i = transport of g_i) and the before-matrix is block-local
    (cross-block order is deterministic). LE(P) = product of gadget LEs."""
    offs, off = [], 0
    ns = []
    for g in gadgets:
        offs.append(off)
        ns.append(g.n)
        off += g.n
    n = off
    T = np.zeros((n, n))
    B = np.zeros((n, n))
    er = np.zeros(n)
    num_LE = 1
    incomp = []
    sumdisp2 = 0.0                                # block-additive (elements stay in block)
    for gi, g in enumerate(gadgets):
        o = offs[gi]
        Tg = transport_matrix(g)
        Bg, totg = before_matrix(g)
        num_LE *= totg
        erg = Bg.sum(axis=0)
        T[o:o + g.n, o:o + g.n] = Tg
        B[o:o + g.n, o:o + g.n] = Bg
        er[o:o + g.n] = o + erg
        for (a, b) in g.incomparable_pairs():
            incomp.append((o + a, o + b))
        # gadget e-rank displacement (global = local, cross-block disp is 0)
        g_order = sorted(range(g.n), key=lambda x: (erg[x], x))
        g_erank = {x: i for i, x in enumerate(g_order)}
        gles = g.linear_extensions()
        gsd = 0.0
        for perm in gles:
            for a, x in enumerate(perm):
                gsd += (a - g_erank[x]) ** 2
        sumdisp2 += gsd / len(gles)
    # cross-block order is deterministic: earlier block entirely before later block
    for i in range(len(gadgets)):
        for j in range(len(gadgets)):
            if i < j:
                B[offs[i]:offs[i] + ns[i], offs[j]:offs[j] + ns[j]] = 1.0
    S = (T + T.T) / 2.0
    width = max(_width(g) for g in gadgets)
    return _row_from(name, n, S, B, er, num_LE, width, incomp, sumdisp2)




# ==========================================================================
# Ensemble: enumerated both-connected posets + biased families + frozen-boundary
# asymptotic families (tight3 ordinal-sum tower and width-3 variants).
# ==========================================================================
def frozen_boundary_families() -> List[Tuple[str, List[Poset]]]:
    """Ordinal-sum towers pinned AT the frozen boundary, analyzed EXACTLY via
    analyze_osum (block structure, no n! enumeration) so they reach large n and
    expose the ASYMPTOTIC rate of lambda_std and R(r) -> 1.

    Returned as (name, [gadget Poset, ...]); analyze_osum assembles them.

    tight3 = a||(b<c) has delta = 1/3 EXACTLY and both incomparable pairs biased
    to 2/3 (the extremal 1/3-2/3 boundary gadget). Ordinal-summing m copies keeps
    delta = 1/3, freezes every within-gadget pair at 2/3, and grows n = 3m. Every
    ordinal sum has lambda_std = 1 EXACTLY (the across-block mode has zero
    transport energy), so these are the DECOMPOSABLE endpoint -- the point of the
    tower is to watch how fast R(r) (a single global test vector) chases the
    ceiling 1 as n grows with the frozen boundary held fixed."""
    fam: List[Tuple[str, List[Poset]]] = []
    tight3 = Poset(3, [(1, 2)])                  # a || (b<c), delta 1/3, biases 2/3
    twoAC = Poset(2, [])                          # 2-antichain, delta 1/2 control
    threeAC = Poset(3, [])                        # 3-antichain, width 3, delta 1/2
    bridge = Poset(1, [])                         # singleton spacer

    for m in range(1, 13):                        # n = 3..36
        fam.append((f"tight3^oplus{m} (n={3*m})", [tight3] * m))
    for m in range(2, 13):
        fam.append((f"2AC^oplus{m} (n={2*m})", [twoAC] * m))
    for m in range(2, 13):
        fam.append((f"3AC^oplus{m} (n={3*m})", [threeAC] * m))   # width 3
    for m in range(1, 10):
        gl = []
        for _ in range(m):
            gl += [tight3, bridge]
        fam.append((f"(tight3+bridge)^{m} (n={4*m})", gl))
    return fam


def sample_both_connected(n: int, n_seeds: int, edge_specs, seen_sig) -> List[Tuple[str, Poset]]:
    """Deterministic random both-connected posets at size n (reproducible via the
    b0a6 _LCG). Used for n=7..10 where full enumeration (2^C(n,2) masks) is too
    slow; this cheaply surfaces frozen in-regime posets at larger n."""
    out = []
    k = 0
    for (en, ed) in edge_specs:
        for seed in range(1, n_seeds + 1):
            rng = _LCG(seed * 100003 + n * 7 + en * 13 + ed)
            P = _random_poset(n, rng, en, ed)
            if not P.both_connected():
                continue
            if P.linext_count() > SAMPLE_LE_CAP:
                continue
            sig = P.iso_signature()
            if sig in seen_sig:
                continue
            seen_sig.add(sig)
            out.append((f"rand-n{n}-#{k}", P))
            k += 1
    return out


def build_ensemble(n_lo=3, n_hi=6, sample_hi=10, n_seeds=1500, verbose=True):
    """Return a list of entries (kind, name, obj): kind='brute' -> obj is a Poset
    analyzed by brute LE enumeration; kind='osum' -> obj is a gadget list analyzed
    EXACTLY via analyze_osum (large-n ordinal-sum towers)."""
    ens = []
    seen_sig = set()
    for n in range(n_lo, n_hi + 1):
        cnt = 0
        for P in enumerate_both_connected(n):
            sig = P.iso_signature()
            if sig in seen_sig:
                continue
            seen_sig.add(sig)
            ens.append(("brute", f"enum-n{n}-#{len(ens)}", P))
            cnt += 1
        if verbose:
            print(f"[enum] n={n}: {cnt} both-connected posets", flush=True)
    edge_specs = ((1, 2), (2, 5), (1, 3), (3, 5), (2, 3))
    for n in range(n_hi + 1, sample_hi + 1):
        sub = sample_both_connected(n, n_seeds, edge_specs, seen_sig)
        ens.extend(("brute", nm, P) for nm, P in sub)
        if verbose:
            print(f"[rand] n={n}: {len(sub)} both-connected samples", flush=True)
    for nm, P in named_posets().items():
        ens.append(("brute", f"named:{nm}", P))
    for nm, P in biased_families().items():
        if P.linext_count() <= LE_ENUM_CAP:
            ens.append(("brute", f"fam:{nm}", P))
    for nm, gl in frozen_boundary_families():
        ens.append(("osum", f"frozen:{nm}", gl))
    if verbose:
        print(f"[ensemble] total {len(ens)} entries", flush=True)
    return ens


# ==========================================================================
# Analysis / summary.
# ==========================================================================
def _fit_loglog(ns, ys):
    xs = [math.log(a) for a, b in zip(ns, ys) if a > 0 and b is not None and b > 0]
    zs = [math.log(b) for a, b in zip(ns, ys) if a > 0 and b is not None and b > 0]
    if len(xs) < 2:
        return None
    mx, mz = sum(xs) / len(xs), sum(zs) / len(zs)
    sxx = sum((x - mx) ** 2 for x in xs)
    sxz = sum((x - mx) * (z - mz) for x, z in zip(xs, zs))
    if sxx < 1e-12:
        return None
    slope = sxz / sxx
    inter = mz - slope * mx
    return dict(slope=slope, intercept=inter, n=len(xs))


def summarize(rows: List[dict]) -> dict:
    R = [r for r in rows if r["R_r"] is not None and r["delta"] is not None]
    lam = [r["lambda_std"] for r in R]
    Rr = [r["R_r"] for r in R]
    Ru = [r["R_u"] for r in R]
    delta = [r["delta"] for r in R]
    maxb = [r["max_bias"] for r in R]

    # ---- STEP 1: E[inv_e] vs lambda_std / n (is the prefix/LIB route lossy?) ----
    high_lam = [r for r in R if r["lambda_std"] >= 0.9]
    # within high-lambda, fit E[inv_e] ~ n^slope; slope>1 => super-linear => LOSSY
    step1 = dict(
        n_high_lambda=len(high_lam),
        corr_Einv_lambda=_pearson([r["E_inv_e"] for r in R], lam),
        loglog_Einv_vs_n_all=_fit_loglog([r["n"] for r in R],
                                         [r["E_inv_e"] for r in R]),
        loglog_Einv_vs_n_highlam=_fit_loglog([r["n"] for r in high_lam],
                                             [r["E_inv_e"] for r in high_lam]),
    )
    # explicit co-occurrence witnesses: high lambda AND large E[inv_e]/n
    wit = sorted(
        [dict(name=r["name"], n=r["n"], lambda_std=r["lambda_std"],
              E_inv_e=r["E_inv_e"], Einv_over_n=r["E_inv_e"] / r["n"],
              Einv_over_n2=r["E_inv_e"] / (r["n"] ** 2), delta=r["delta"],
              R_r=r["R_r"])
         for r in high_lam],
        key=lambda d: -d["Einv_over_n"],
    )[:15]
    step1["high_lambda_large_Einv_witnesses"] = wit

    # R(r) vs the best PREFIX-INDICATOR certificate (the LIB route's own object):
    # does the single global smooth vector match/beat every prefix indicator?
    hp = [r for r in R if r.get("best_prefix_R") is not None]
    step1["r_vs_prefix"] = dict(
        n=len(hp),
        r_beats_prefix_frac=float(np.mean([r["r_beats_prefix"] for r in hp])),
        median_R_r=float(np.median([r["R_r"] for r in hp])),
        median_best_prefix_R=float(np.median([r["best_prefix_R"] for r in hp])),
        median_r_minus_prefix=float(np.median([r["r_minus_prefix"] for r in hp])),
        # in the genuine bad-mixing regime (lam>=0.9) specifically
        highlam_r_beats_prefix_frac=float(np.mean(
            [r["r_beats_prefix"] for r in hp if r["lambda_std"] >= 0.9]) or 0.0),
    )
    # LOCALITY probe (Step-3 lemma B): is E[sum disp^2]/E[inv_e] bounded?
    loc = [r for r in R if r.get("locality_ratio") is not None]
    loc_sorted = sorted(loc, key=lambda r: -r["locality_ratio"])
    step1["locality"] = dict(
        n=len(loc),
        ratio_median=float(np.median([r["locality_ratio"] for r in loc])),
        ratio_p90=float(np.percentile([r["locality_ratio"] for r in loc], 90)),
        ratio_max=float(np.max([r["locality_ratio"] for r in loc])),
        # does the ratio grow with n? (fit log ratio ~ slope*log n)
        loglog_ratio_vs_n=_fit_loglog([r["n"] for r in loc],
                                      [r["locality_ratio"] for r in loc]),
        worst=[dict(name=r["name"], n=r["n"], delta=r["delta"], width=r["width"],
                    locality_ratio=r["locality_ratio"], E_inv_e=r["E_inv_e"],
                    lambda_std=r["lambda_std"]) for r in loc_sorted[:10]],
    )
    # energy(r) ~ c * E[inv_e] : fit raw_energy_r against E_inv_e (Step-3 lemma A/law)
    re = [r for r in R if r.get("raw_energy_r") is not None and r["E_inv_e"] > 1e-9]
    if re:
        ratios = [r["raw_energy_r"] / r["E_inv_e"] for r in re]
        step1["energy_over_Einv"] = dict(
            median=float(np.median(ratios)), p90=float(np.percentile(ratios, 90)),
            max=float(np.max(ratios)),
            loglog_vs_n=_fit_loglog([r["n"] for r in re], ratios))

    # ---- STEP 2: R(r) behavior; does R(r) -> 1 in the frozen regime? ----
    # in-regime buckets by delta proximity to 1/3 and by max_bias proximity to 1
    def bucket(pred):
        sub = [r for r in R if pred(r)]
        if not sub:
            return None
        return dict(
            count=len(sub),
            R_r_median=float(np.median([r["R_r"] for r in sub])),
            R_r_min=float(np.min([r["R_r"] for r in sub])),
            R_r_max=float(np.max([r["R_r"] for r in sub])),
            lambda_median=float(np.median([r["lambda_std"] for r in sub])),
            r_capture_median=float(np.median([r["r_capture"] for r in sub
                                              if r["r_capture"] is not None])),
            r_minus_u_median=float(np.median([r["r_minus_u"] for r in sub
                                              if r["r_minus_u"] is not None])),
        )

    step2 = dict(
        corr_delta_Rr=_pearson(delta, Rr),
        corr_maxbias_Rr=_pearson(maxb, Rr),
        corr_Rr_lambda=_pearson(Rr, lam),
        R_r_capture_median=float(np.median([r["r_capture"] for r in R
                                            if r["r_capture"] is not None])),
        R_r_beats_R_u_frac=float(np.mean([1.0 if (r["R_r"] >= r["R_u"] - 1e-9)
                                          else 0.0 for r in R])),
        r_minus_u_median=float(np.median([r["r_minus_u"] for r in R
                                          if r["r_minus_u"] is not None])),
        bucket_delta_le_0p35=bucket(lambda r: r["delta"] <= 0.35 + 1e-9),
        bucket_delta_le_0p40=bucket(lambda r: r["delta"] <= 0.40 + 1e-9),
        bucket_delta_gt_0p45=bucket(lambda r: r["delta"] > 0.45),
        bucket_maxbias_ge_0p66=bucket(lambda r: r["max_bias"] >= 2/3 - 1e-9),
        bucket_maxbias_ge_0p80=bucket(lambda r: r["max_bias"] >= 0.80),
        bucket_maxbias_ge_0p90=bucket(lambda r: r["max_bias"] >= 0.90),
    )
    # smallest-delta posets: their R(r), lambda, capture (the in-regime frontier)
    small_delta = sorted(R, key=lambda r: (r["delta"], -r["max_bias"]))[:20]
    step2["smallest_delta_frontier"] = [
        dict(name=r["name"], n=r["n"], delta=r["delta"], max_bias=r["max_bias"],
             lambda_std=r["lambda_std"], R_r=r["R_r"], R_u=r["R_u"],
             r_capture=r["r_capture"], ceiling_minus_r=r["ceiling_minus_r"])
        for r in small_delta
    ]
    # the frozen-boundary asymptotic tower: R(r) & lambda vs n at delta=1/3
    tower = sorted([r for r in R if r["name"].startswith("frozen:tight3^oplus")],
                   key=lambda r: r["n"])
    step2["frozen_tower_tight3"] = [
        dict(name=r["name"], n=r["n"], delta=r["delta"], lambda_std=r["lambda_std"],
             R_r=r["R_r"], R_u=r["R_u"], gap=r["gap"], energy_r=r["energy_r"],
             ceiling_minus_r=r["ceiling_minus_r"], E_inv_e=r["E_inv_e"])
        for r in tower
    ]
    tower3 = sorted([r for r in R if r["name"].startswith("frozen:3AC^oplus")],
                    key=lambda r: r["n"])
    step2["frozen_tower_3AC"] = [
        dict(name=r["name"], n=r["n"], delta=r["delta"], lambda_std=r["lambda_std"],
             R_r=r["R_r"], R_u=r["R_u"], gap=r["gap"], E_inv_e=r["E_inv_e"])
        for r in tower3
    ]
    # worst-case r-capture (where the lower bound is loosest) among in-regime
    worst = sorted([r for r in R if r["delta"] <= 0.42 and r["r_capture"] is not None],
                   key=lambda r: r["r_capture"])[:15]
    step2["worst_r_capture_inregime"] = [
        dict(name=r["name"], n=r["n"], delta=r["delta"], max_bias=r["max_bias"],
             lambda_std=r["lambda_std"], R_r=r["R_r"], r_capture=r["r_capture"])
        for r in worst
    ]

    return dict(
        n_rows=len(rows), n_analyzed=len(R),
        step1_lossy_diagnostic=step1,
        step2_expected_rank_certificate=step2,
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-lo", type=int, default=3)
    ap.add_argument("--n-hi", type=int, default=6, help="exhaustive enum up to this n")
    ap.add_argument("--sample-hi", type=int, default=9, help="random sample up to this n")
    ap.add_argument("--n-seeds", type=int, default=900)
    ap.add_argument("--out", type=str,
                    default="data/onethird-mg8201-L1b-expected-rank.json")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    ens = build_ensemble(args.n_lo, args.n_hi, args.sample_hi, args.n_seeds,
                         verbose=not args.quiet)
    rows = []
    for i, (kind, nm, obj) in enumerate(ens):
        try:
            row = analyze_osum(obj, nm) if kind == "osum" else analyze(obj, nm)
        except Exception as ex:  # noqa
            row = None
        if row is not None:
            rows.append(row)
        if not args.quiet and (i + 1) % 500 == 0:
            print(f"[analyze] {i+1}/{len(ens)}", flush=True)

    summary = summarize(rows)
    out = dict(summary=summary, rows=rows,
               meta=dict(n_lo=args.n_lo, n_hi=args.n_hi, n_rows=len(rows),
                         program="spectral_near_ordinal_sum",
                         ticket="mg-8201"))
    with open(args.out, "w") as fh:
        json.dump(out, fh, indent=1, default=float)

    if not args.quiet:
        s = summary
        print(f"=== mg-8201 BETTER L1b: expected-rank test-vector probe ===")
        print(f"rows analyzed: {s['n_analyzed']}")
        print()
        print("--- STEP 1: is the prefix/LIB (linear-inversions) route lossy? ---")
        s1 = s["step1_lossy_diagnostic"]
        print(f"  #high-lambda (>=0.9): {s1['n_high_lambda']}")
        print(f"  corr(E[inv_e], lambda_std): {s1['corr_Einv_lambda']:.4f}")
        ll = s1["loglog_Einv_vs_n_highlam"]
        if ll:
            print(f"  E[inv_e] ~ n^slope within high-lambda: slope={ll['slope']:.3f} "
                  f"(n={ll['n']})  [>1 => SUPER-LINEAR => LIB not necessary => LOSSY]")
        print("  high-lambda + large E[inv_e]/n witnesses (top 6):")
        for w in s1["high_lambda_large_Einv_witnesses"][:6]:
            print(f"    {w['name'][:34]:34s} n={w['n']:2d} lam={w['lambda_std']:.3f} "
                  f"E[inv_e]={w['E_inv_e']:.2f} (/n={w['Einv_over_n']:.2f}, "
                  f"/n^2={w['Einv_over_n2']:.3f}) R_r={w['R_r']:.3f}")
        rp = s1.get("r_vs_prefix")
        if rp:
            print(f"  R(r) vs BEST PREFIX-INDICATOR (the LIB route's own object):")
            print(f"    R(r) >= best prefix-R in {rp['r_beats_prefix_frac']*100:.1f}% of posets "
                  f"(and {rp['highlam_r_beats_prefix_frac']*100:.1f}% when lam>=0.9); "
                  f"median R(r)={rp['median_R_r']:.3f} vs prefix={rp['median_best_prefix_R']:.3f}")
        eo = s1.get("energy_over_Einv")
        if eo:
            print(f"  raw energy(r)/E[inv_e]: median={eo['median']:.3f} p90={eo['p90']:.3f} "
                  f"max={eo['max']:.3f}  (energy(r) ~ c*E[inv_e], c=O(1))")
        loc = s1.get("locality")
        if loc:
            ls = loc["loglog_ratio_vs_n"]
            print(f"  LOCALITY E[sum disp^2]/E[inv_e]: median={loc['ratio_median']:.2f} "
                  f"p90={loc['ratio_p90']:.2f} max={loc['ratio_max']:.2f}; "
                  f"ratio~n^{ls['slope']:.2f}" if ls else "")
            print("    worst locality-ratio posets (Step-3 lemma-B stressors):")
            for w in loc["worst"][:5]:
                print(f"      {w['name'][:26]:26s} n={w['n']:2d} ratio={w['locality_ratio']:.2f} "
                      f"Einv={w['E_inv_e']:.2f} lam={w['lambda_std']:.3f} d={w['delta']:.3f}")
        print()
        print("--- STEP 2: expected-rank certificate R(r) ---")
        s2 = s["step2_expected_rank_certificate"]
        print(f"  corr(delta, R(r)): {s2['corr_delta_Rr']:.4f}  "
              f"corr(max_bias, R(r)): {s2['corr_maxbias_Rr']:.4f}")
        print(f"  R(r) capture median (R(r)/lambda_std): {s2['R_r_capture_median']:.4f}")
        print(f"  R(r) >= R(u) fraction: {s2['R_r_beats_R_u_frac']:.3f}   "
              f"median R(r)-R(u): {s2['r_minus_u_median']:.4f}")
        for key in ("bucket_maxbias_ge_0p66", "bucket_maxbias_ge_0p80",
                    "bucket_maxbias_ge_0p90", "bucket_delta_le_0p40",
                    "bucket_delta_le_0p35"):
            b = s2[key]
            if b:
                print(f"  {key:26s}: count={b['count']:4d} "
                      f"R(r) med={b['R_r_median']:.3f} min={b['R_r_min']:.3f} "
                      f"lam med={b['lambda_median']:.3f} "
                      f"capture={b['r_capture_median']:.3f}")
        print("  frozen tight3 tower (delta=1/3, growing n):")
        for t in s2["frozen_tower_tight3"]:
            print(f"    n={t['n']:2d} lam={t['lambda_std']:.4f} R_r={t['R_r']:.4f} "
                  f"R_u={t['R_u']:.4f} gap={t['gap']:.4f} "
                  f"ceil-R_r={t['ceiling_minus_r']:.4f} E[inv]={t['E_inv_e']:.2f}")
        print("  frozen 3AC tower (width 3, delta=1/2 control):")
        for t in s2["frozen_tower_3AC"]:
            print(f"    n={t['n']:2d} lam={t['lambda_std']:.4f} R_r={t['R_r']:.4f} "
                  f"gap={t['gap']:.4f} E[inv]={t['E_inv_e']:.2f}")
        print("  smallest-delta frontier (top 8):")
        for r in s2["smallest_delta_frontier"][:8]:
            print(f"    {r['name'][:30]:30s} n={r['n']:2d} d={r['delta']:.3f} "
                  f"mb={r['max_bias']:.3f} lam={r['lambda_std']:.3f} "
                  f"R_r={r['R_r']:.3f} cap={r['r_capture']:.3f}")
        print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
