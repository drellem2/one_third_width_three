#!/usr/bin/env python3
"""
OneThird mg-8b64: L1b spot-check -- does Theorem E's BK low-conductance pair-cut
FORCE lambda_std ~ 1 in the n-dim element-position TRANSPORT quotient?

Ticket:  mg-8b64 (high, repo one_third_width_three). Daniel-authorized, no gate
         (gate mg-7d8a lifted 2026-07-13 "let's go now, no gate"). SOLE remaining
         gap after mg-b0a6 (kill-shot probe, ALIVE) + mg-3ce3 (L4 stability, GREEN).
         Source: spectral_near_ordinal_sum_program.tex; pm-onethird memory
         project_spectral_near_ordinal_sum_program.md.

THE GAP (L1b)
-------------
The program's falsification chain for a hypothetical MINIMAL COUNTEREXAMPLE P:

    minimal counterexample
      -> low-conductance BK cut   (PROVEN: Theorem E / thm:cex-implies-low-expansion,
                                    step8.tex -- a PAIR-INDICATOR cut S_xy)
      -> ??? (L1b transfer) ???
      -> bad mixing in the TRANSPORT quotient, i.e. lambda_std ~ 1
      -> Cheeger low-conductance prefix -> near ordinal sum
      -> balanced pair by minimality -> contradiction.

Theorem E's cut lives on the BK / adjacent-transposition graph on L(P) and is the
PAIR cut  S_xy = { sigma : x precedes y }  for a "BK-frozen" incomparable pair,
i.e. the pair minimizing  E(f_xy)/Var(f_xy)  (bounded by 2/(gamma*n) for a
gamma-counterexample; step8.tex lem:frozen-pair-existence).

The spectral program instead needs bad mixing in the n-dim element-position
TRANSPORT quotient:  lambda_std ~ 1  (small transport spectral gap 1 - lambda_std).

L1b = THE TRANSFER: does a low-conductance BK pair-cut force lambda_std ~ 1?
This is the repo's own "cuts-by-pairs" open problem -- a Buser-type reverse Cheeger
for width-3 pair cuts (docs/compatibility-geometry-cuts-by-pairs-scoping.md Sec 4.3(i),
Sec 5.2-5.3).

WHAT THIS MEASURES (the transfer, directly)
-------------------------------------------
For each poset P we compute BOTH sides and test the implication.

(a) BK side (n!-scale; capped, n! wall LOGGED):
    - Phi_BK(S_xy) for Theorem E's pair-indicator cuts, for EVERY incomparable
      pair (adjacency counts; exact rationals). The FROZEN pair = argmin of the
      Dirichlet/variance ratio E(f_xy)/Var(f_xy) (Theorem E's actual selection).
    - lambda2(BK): the BK adjacent-transposition-walk spectral gap (Cheeger
      connectivity of the whole BK graph), where |L(P)| is small enough.
    - h(BK): exhaustive Cheeger min-conductance over ALL cuts of L(P), where
      |L(P)| is tiny enough to enumerate 2^|L| subsets.

(b) Transport side (n-dim, cheap; reuses the b0a6 engine verbatim):
    - lambda_std and the transport gap 1 - lambda_std.
    - the transport conductance Phi_T of label cuts (prefixes of the
      expected-rank order + full label-Cheeger for small n).

THEN test L1b as an IMPLICATION:
  - corr(Phi_BK, 1 - lambda_std) across the ensemble (program predicts >0: a low
    BK conductance co-occurs with a small transport gap).
  - the OPERATIONAL TRANSFER: take Theorem E's specific frozen cut S_xy and
    evaluate its image / energy in the transport Dirichlet form -- does a
    low-Phi_BK S_xy map to a low transport conductance label cut?
  - hunt for a REFUTER: a poset with a genuinely LOW-conductance BK pair-cut but
    lambda_std bounded AWAY from 1 (transport gap NOT small). That is the RED.

TEST REGIME
-----------
Real counterexamples do not exist (conjecture believed true), so we DRIVE toward
the counterexample regime: width-3 posets and strongly-biased both-connected
posets (max incomparable-pair bias increasing toward >2/3), tracking the
BK-vs-transport relationship as bias grows. Includes the N-poset family (the
mandated stress case -- NOT an ordinal sum, nonzero defect at every cut) and the
width-3 SP families used in AP-2.

SKEPTICAL BAR (pm-onethird feedback_empirical_green_is_not_proven):
This is EMPIRICAL, not a proof. GREEN here means "low Phi_BK reliably forces small
transport gap on the tested ensemble, with a reported modulus to aim a proof at",
NOT "L1b is proven". A high value on one side is not evidence unless the transfer
holds in the counterexample-driving direction.

VERDICT KEYS
------------
  RED   (L1b likely FALSE): exhibit a poset with low-conductance BK pair-cut but
        lambda_std bounded away from 1 (transfer fails). Program's last gap breaks.
  GREEN : low Phi_BK reliably forces small transport gap; S_xy maps to low
        transport conductance; strengthening toward the counterexample regime.
  AMBER : holds only under extra structure (e.g. width-3 rigidity) -- report which.
"""
from __future__ import annotations

import argparse
import itertools
import math
from fractions import Fraction
from typing import Dict, List, Tuple, Optional

import numpy as np

# Reuse the b0a6 engine verbatim (mandated: "reuse the b0a6/3ce3 engines").
from onethird_mgb0a6_spectral_killshot_probe import (
    Poset,
    ONE_THIRD, TWO_THIRDS,
    transport_matrix, standard_block_and_lambda, expected_rank,
    before_prob_dp, leakage_prefix, prefix_defects, rayleigh,
    enumerate_both_connected, named_posets, _pearson,
)

# n! wall: cap the BK-graph work. Pair-cut conductance (Theorem E's ACTUAL
# quantity) needs only adjacency counts, cheap for any n we can enumerate LE.
# The spectral BK objects (lambda2, exhaustive Cheeger) blow up with |L(P)|.
LE_ENUM_CAP = 40320          # 8! -- max |L(P)| we brute-enumerate (LE wall)
BK_SPECTRUM_CAP = 2200       # max |L(P)| for a dense BK-walk eigendecomposition
BK_CHEEGER_CAP = 15          # max |L(P)| for exhaustive 2^|L| min-conductance
EIG_TOL = 1e-9


# ==========================================================================
# BK adjacent-transposition graph on L(P).
#   Vertices  = linear extensions (position a -> element).
#   Edge      = two extensions differing by ONE adjacent transposition of an
#               incomparable pair (a valid BK move).
#   Degree(L) = #{ i : L[i], L[i+1] incomparable }  (the effective degree <= n-1).
#   Lazy (n-1)-regular walk convention (step8.tex): each position i in [n-1]
#   contributes; incomparable -> swap, comparable -> self-loop.
# ==========================================================================
def _incomp_matrix(P: Poset) -> np.ndarray:
    """Boolean n x n: inc[a,b] = a and b incomparable (a != b)."""
    n = P.n
    inc = np.zeros((n, n), dtype=bool)
    for a in range(n):
        for b in range(n):
            if a != b and not P.comparable(a, b):
                inc[a, b] = True
    return inc


def bk_adjacency_count(P: Poset, x: int, y: int) -> Fraction:
    """Adj_{x,y} = #{ sigma in L(P) : x,y occupy consecutive positions in sigma }.
    Exact integer count returned as Fraction for uniform arithmetic. This is the
    BK edge-boundary of the pair cut S_xy (each x,y adjacency is one crossing
    of C_{x,y}); |partial S_xy| = Adj_{x,y}/2 as unordered edges (step8.tex
    Lemma 3.1 / lem:dirichlet-conductance)."""
    les = P.linear_extensions()
    cnt = 0
    for perm in les:
        for i in range(P.n - 1):
            a, b = perm[i], perm[i + 1]
            if (a == x and b == y) or (a == y and b == x):
                cnt += 1
    return Fraction(cnt, 1)


def bk_pair_cut(P: Poset, x: int, y: int) -> dict:
    """Theorem E's pair-indicator cut S_xy = { sigma : x precedes y }.
    Returns exact rationals:
      p        = Pr[x precedes y]
      var      = p(1-p) = Var(f_xy)
      adj      = Adj_{x,y} (# adjacencies; = # boundary crossings, ordered/pos)
      energy   = E(f_xy) = adj / (2 (n-1) |L|)          (BK Dirichlet form)
      ratio    = E(f_xy)/Var(f_xy)                       (Theorem E frozen ratio)
      phi      = Phi(S_xy) = |partial S_xy| / vol_min    (actual conductance,
                 step8 normalization vol(S)=|S|(n-1))
                 = (adj/2) / ((n-1) * min(p,1-p) * |L|)
    Note phi <= ratio always (Lemma lem:dirichlet-conductance)."""
    n = P.n
    tot = P.linext_count()
    p = before_prob_dp(P, x, y)              # Pr[x precedes y], exact
    var = p * (1 - p)
    adj = bk_adjacency_count(P, x, y)
    L = Fraction(tot, 1)
    energy = adj / (2 * (n - 1) * L)
    ratio = energy / var if var != 0 else None
    mn = min(p, 1 - p)
    phi = (adj / 2) / ((n - 1) * mn * L) if mn != 0 else None
    return dict(x=x, y=y, p=p, var=var, adj=adj, energy=energy,
                ratio=ratio, phi=phi, minvol=mn)


def bk_frozen_pair(P: Poset) -> dict:
    """Scan every incomparable pair; return per-pair data plus the FROZEN pair
    (Theorem E's argmin of E(f_xy)/Var(f_xy)) and the min-Phi pair. Also the
    max-bias pair (largest max(p,1-p)) = the most-frozen/unbalanced pair."""
    pairs = []
    for (x, y) in P.incomparable_pairs():
        pairs.append(bk_pair_cut(P, x, y))
    if not pairs:
        return dict(pairs=[], frozen=None, minphi=None, maxbias=None,
                    delta=None, sum_energy=None, sum_var=None)
    frozen = min((pc for pc in pairs if pc["ratio"] is not None),
                 key=lambda pc: pc["ratio"], default=None)
    minphi = min((pc for pc in pairs if pc["phi"] is not None),
                 key=lambda pc: pc["phi"], default=None)
    maxbias = max(pairs, key=lambda pc: max(pc["p"], 1 - pc["p"]))
    # delta(P) = max over incomparable pairs of min(p,1-p): counterexample
    # regime iff delta < 1/3. Larger delta = closer to a balanced pair existing.
    delta = max(min(pc["p"], 1 - pc["p"]) for pc in pairs)
    sum_energy = sum(pc["energy"] for pc in pairs)
    sum_var = sum(pc["var"] for pc in pairs)
    return dict(pairs=pairs, frozen=frozen, minphi=minphi, maxbias=maxbias,
                delta=delta, sum_energy=sum_energy, sum_var=sum_var)


def bk_walk_matrix(P: Poset):
    """Lazy (n-1)-regular symmetric BK walk on L(P). Returns (W, index) or
    (None, None) if |L(P)| exceeds BK_SPECTRUM_CAP. W[L,L'] = 1/(2(n-1)) for
    each incomparable adjacent position; diagonal = 1 - sum(off-diag)."""
    les = P.linear_extensions()
    m = len(les)
    if m > BK_SPECTRUM_CAP:
        return None, None
    n = P.n
    index = {perm: i for i, perm in enumerate(les)}
    W = np.zeros((m, m))
    step = 1.0 / (2 * (n - 1)) if n > 1 else 0.0
    for perm in les:
        i0 = index[perm]
        for i in range(n - 1):
            a, b = perm[i], perm[i + 1]
            if not P.comparable(a, b):
                nb = list(perm)
                nb[i], nb[i + 1] = nb[i + 1], nb[i]
                j0 = index[tuple(nb)]
                W[i0, j0] += step
    for i0 in range(m):
        W[i0, i0] += 1.0 - W[i0].sum()
    W = (W + W.T) / 2.0
    return W, index


def bk_lambda2(P: Poset) -> Optional[float]:
    """Second-largest eigenvalue of the lazy BK walk (BK spectral gap = 1 - l2).
    None if |L(P)| exceeds the spectrum cap (n! wall LOGGED by caller)."""
    W, _ = bk_walk_matrix(P)
    if W is None:
        return None
    ev = np.linalg.eigvalsh(W)
    ev = np.sort(ev)[::-1]
    return float(ev[1]) if len(ev) > 1 else float("nan")


def bk_cheeger_exhaustive(P: Poset) -> Optional[dict]:
    """Exhaustive Cheeger: min over ALL nonempty proper cuts S of L(P) of
    Phi(S) = |partial S| / ((n-1) min(|S|,|S^c|)). Only for tiny |L(P)|.
    Returns the min conductance and whether the argmin is a PAIR cut."""
    les = P.linear_extensions()
    m = len(les)
    if m > BK_CHEEGER_CAP or m < 2:
        return None
    n = P.n
    index = {perm: i for i, perm in enumerate(les)}
    # edge list (unordered), each an incomparable adjacent swap
    edges = []
    seen = set()
    for perm in les:
        i0 = index[perm]
        for i in range(n - 1):
            a, b = perm[i], perm[i + 1]
            if not P.comparable(a, b):
                nb = list(perm); nb[i], nb[i + 1] = nb[i + 1], nb[i]
                j0 = index[tuple(nb)]
                e = (min(i0, j0), max(i0, j0))
                if e not in seen:
                    seen.add(e); edges.append(e)
    # pair cuts as vertex-index sets, to test whether argmin is a pair cut
    pair_cut_sets = set()
    for (x, y) in P.incomparable_pairs():
        A = frozenset(index[perm] for perm in les
                      if perm.index(x) < perm.index(y))
        pair_cut_sets.add(A)
        pair_cut_sets.add(frozenset(range(m)) - A)
    best = None
    best_A = None
    for bits in range(1, (1 << m) - 1):
        S = frozenset(i for i in range(m) if (bits >> i) & 1)
        k = len(S)
        mn = min(k, m - k)
        boundary = sum(1 for (u, v) in edges if ((u in S) ^ (v in S)))
        phi = boundary / ((n - 1) * mn)
        if best is None or phi < best - 1e-15:
            best, best_A = phi, S
    return dict(h_bk=best, argmin_is_pair_cut=(best_A in pair_cut_sets),
                m=m, n_edges=len(edges))


# ==========================================================================
# Transport side (reused b0a6 engine) + operational transfer of the frozen pair.
# ==========================================================================
def transport_summary(P: Poset) -> dict:
    """lambda_std, transport gap, expected-rank order, and transport conductance
    over prefixes of the expected-rank order (the low-conductance transport cuts
    the program's Cheeger step feeds on)."""
    n = P.n
    S, lam, v, hspec = standard_block_and_lambda(P)
    er = expected_rank(P)
    er_order = sorted(range(n), key=lambda e: (er[e], e))
    # transport conductance of each expected-rank prefix (Phi_T = K_k / |A_k|)
    prefix = []
    for k in range(1, n):
        d = prefix_defects(P, er_order, k)
        prefix.append(dict(k=k, Phi_T=float(d["Phi"]), Delta1=float(d["Delta1"]),
                           Delta0=float(d["Delta0"])))
    phi_t_min_prefix = min((pk["Phi_T"] for pk in prefix), default=float("nan"))
    # full label-Cheeger over all label subsets (small n): min transport
    # conductance E|A\sigma(A)|/min(|A|,|A^c|) over ALL label cuts A.
    phi_t_cheeger = _transport_label_cheeger(P)
    return dict(lambda_std=lam, gap=1.0 - lam,
                er_order=er_order, expected_rank=er,
                prefix=prefix, phi_t_min_prefix=phi_t_min_prefix,
                phi_t_cheeger=phi_t_cheeger, S=S, v=v)


def _transport_label_cheeger(P: Poset) -> float:
    """min over label subsets A of  E|A\\sigma(A)| / min(|A|,|A^c|), the transport
    Cheeger constant. E|A\\sigma(A)| = # elements of A NOT in the first |A|
    positions, averaged over LE. Brute over all subsets (n<=~12)."""
    n = P.n
    les = P.linear_extensions()
    tot = len(les)
    if n > 12:
        return float("nan")
    best = float("inf")
    for r in range(1, n):
        for A in itertools.combinations(range(n), r):
            Aset = set(A)
            leak = 0
            for perm in les:
                first = set(perm[:r])
                leak += len(Aset - first)
            phi = (leak / tot) / min(r, n - r)
            if phi < best:
                best = phi
    return best


def transport_image_of_pair(P: Poset, ts: dict, x: int, y: int, p_xy: Fraction) -> dict:
    """OPERATIONAL TRANSFER: map Theorem E's frozen pair (x,y) to a transport
    label cut and evaluate its energy in the transport Dirichlet form.

    Construction: order labels by expected position (the distinguished order e).
    The frozen pair has x,y strongly ordered (p_xy far from 1/2), so x and y sit
    apart in e. The pair's natural transport cut is the prefix A_k of e that
    SEPARATES x from y with minimum transport conductance (the cut the frozen
    pair 'points at'). We report Phi_T of that cut, and 1 - lambda_std for
    context. Low Phi_BK(S_xy) SHOULD map to low Phi_T here if L1b holds."""
    n = P.n
    er_order = ts["er_order"]
    pos = {e: i for i, e in enumerate(er_order)}
    lo, hi = sorted((pos[x], pos[y]))
    # prefix cuts A_k, k in (lo, hi], separate x from y; pick min-conductance one
    best = None
    best_k = None
    for k in range(lo + 1, hi + 1):
        d = prefix_defects(P, er_order, k)
        phi = float(d["Phi"])
        if best is None or phi < best:
            best, best_k = phi, k
    # if x,y adjacent in e (hi==lo+1) there is exactly one separating prefix
    return dict(x=x, y=y, p_xy=float(p_xy),
                sep_prefix_k=best_k, phi_t_sep=best,
                x_rank=pos[x], y_rank=pos[y])


# ==========================================================================
# Biased / stress families driving toward the counterexample regime.
# ==========================================================================
def biased_families() -> Dict[str, Poset]:
    """Both-connected width-3 posets with a strongly-biased (frozen) incomparable
    pair, plus the mandated N-poset family and width-3 SP families (AP-2 style).
    Goal: increase max incomparable-pair bias toward >2/3 and watch BK-vs-transport."""
    fam: Dict[str, Poset] = {}

    # --- N-poset family (2+2 and stacked / widened variants). NOT ordinal sums. ---
    fam["N (2+2)"] = Poset(4, [(0, 1), (2, 3)])
    # stacked N: 3+3 disjoint chains bridged to stay both-connected
    fam["3+3 bridged"] = Poset(6, [(0, 1), (1, 2), (3, 4), (4, 5), (2, 4)])
    # width-3 "double-N": three 2-chains, cross relations for both-connectivity
    fam["doubleN w3"] = Poset(6, [(0, 1), (2, 3), (4, 5), (1, 4), (3, 4)])

    # --- crown / bipartite S_k^0 : k minima below k maxima minus a perfect
    #     matching (the classic strongly-mixing width-k crowns). width grows;
    #     restrict to width-3 by capping. ---
    # crown S_3^0: minima {0,1,2}, maxima {3,4,5}, i<j edge unless i+3==j (remove matching)
    crown_edges = [(i, 3 + j) for i in range(3) for j in range(3) if i != j]
    fam["crown S3^0 (w3)"] = Poset(6, crown_edges)

    # --- biased ladder: a long width-2 fence with a rider element creating an
    #     increasingly frozen pair as the fence lengthens. ---
    for m in (3, 4, 5, 6):
        # fence 0<1>2<3>4<... (zigzag) forces strong statistical bias on the
        # end pair while keeping both graphs connected.
        edges = []
        for i in range(m - 1):
            if i % 2 == 0:
                edges.append((i, i + 1))      # i < i+1
            else:
                edges.append((i + 1, i))      # i+1 < i
        try:
            P = Poset(m, edges)
            if P.both_connected():
                fam[f"fence{m}"] = P
        except ValueError:
            pass

    # --- width-3 SP (series-parallel) families used in AP-2: ordinal sums of
    #     antichains with a bridge to keep both-connected, driving delta up. ---
    # (2-antichain) oplus (2-antichain): bowtie, an ordinal sum (control: delta=1/2)
    fam["2AC(+)2AC bowtie"] = Poset(4, [(0, 2), (0, 3), (1, 2), (1, 3)])
    # V + Lambda glued (width-3, strongly biased centre pair)
    fam["V+Lambda w3"] = Poset(5, [(0, 2), (1, 2), (2, 3), (2, 4)])
    # 3-antichain oplus single oplus 3-antichain (width 3, ordinal-sum control)
    fam["3AC(+)1(+)3AC"] = Poset(7, [(i, 3) for i in range(3)]
                                + [(3, 4 + j) for j in range(3)])

    # --- "tight" delta ~ 1/3 extremal posets (the balance-boundary regime) ---
    fam["tight3 a||(b<c)"] = Poset(3, [(1, 2)])
    fam["1||chain3"] = Poset(4, [(1, 2), (2, 3)])
    fam["1||chain4"] = Poset(5, [(1, 2), (2, 3), (3, 4)])
    fam["1||chain5"] = Poset(6, [(1, 2), (2, 3), (3, 4), (4, 5)])
    fam["1||chain6"] = Poset(7, [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)])
    fam["1||chain7"] = Poset(8, [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)])

    # --- larger width-3 targeted stress (n=7,8; |L| < LE_ENUM_CAP): drive the
    #     BK side deep (small Phi_BK) while staying both-connected. ---
    # width-3 "triple ladder": three interleaved 2-chains with cross relations
    fam["triple-ladder n8 w3"] = Poset(8, [(0, 1), (2, 3), (4, 5), (6, 7),
                                           (1, 4), (3, 6), (0, 2)])
    # long fence n=8 (max BK-frozen end pair)
    edges = []
    for i in range(7):
        edges.append((i, i + 1) if i % 2 == 0 else (i + 1, i))
    try:
        P = Poset(8, edges)
        if P.both_connected():
            fam["fence8"] = P
    except ValueError:
        pass
    fam["fence7"] = Poset(7, [(i, i + 1) if i % 2 == 0 else (i + 1, i)
                              for i in range(6)])
    # crown S4^0 restricted region is width>3; keep the width-3 crown only.

    return fam


# ==========================================================================
# Driver.
# ==========================================================================
def analyze_poset(P: Poset, name: str) -> dict:
    """Compute BK side + transport side + operational transfer for one poset."""
    bk = bk_frozen_pair(P)
    ts = transport_summary(P)
    lam2 = bk_lambda2(P)                          # BK spectral gap context
    cheeger = bk_cheeger_exhaustive(P)            # exhaustive BK Cheeger (tiny |L|)
    m = P.linext_count()

    row = dict(
        name=name, n=P.n, num_LE=m,
        width=_width(P),
        lambda_std=ts["lambda_std"], transport_gap=ts["gap"],
        phi_t_min_prefix=ts["phi_t_min_prefix"], phi_t_cheeger=ts["phi_t_cheeger"],
        delta=float(bk["delta"]) if bk["delta"] is not None else None,
        num_incomp_pairs=len(bk["pairs"]),
    )
    if bk["frozen"] is not None:
        fr = bk["frozen"]
        row["frozen_pair"] = [fr["x"], fr["y"]]
        row["frozen_ratio"] = float(fr["ratio"])       # E/Var (Theorem E quantity)
        row["frozen_phi_bk"] = float(fr["phi"])        # Phi(S_xy) actual conductance
        row["frozen_p"] = float(fr["p"])
        mp = bk["minphi"]
        row["min_phi_bk"] = float(mp["phi"])           # min pair-cut conductance
        row["min_phi_bk_pair"] = [mp["x"], mp["y"]]
        mb = bk["maxbias"]
        row["max_bias"] = float(max(mb["p"], 1 - mb["p"]))
        # aggregate averaging quantity (Theorem E step-4 ratio-of-sums)
        row["ratio_of_sums"] = (float(bk["sum_energy"] / bk["sum_var"])
                                if bk["sum_var"] else None)
        # OPERATIONAL TRANSFER on the frozen pair
        ti = transport_image_of_pair(P, ts, fr["x"], fr["y"], fr["p"])
        row["frozen_phi_t_image"] = ti["phi_t_sep"]    # transport conductance of image
        row["frozen_sep_k"] = ti["sep_prefix_k"]
        # transfer on the min-phi pair too (the literally-lowest BK cut)
        ti2 = transport_image_of_pair(P, ts, mp["x"], mp["y"], mp["p"])
        row["minphi_phi_t_image"] = ti2["phi_t_sep"]
    row["bk_lambda2"] = lam2
    row["bk_gap"] = (1.0 - lam2) if lam2 is not None else None
    if cheeger is not None:
        row["h_bk_exhaustive"] = cheeger["h_bk"]
        row["h_bk_argmin_is_pair_cut"] = cheeger["argmin_is_pair_cut"]
    return row


def _width(P: Poset) -> int:
    """Width = max antichain size, via a simple greedy/Dilworth-free exact check
    for small n (max independent set in the comparability graph)."""
    n = P.n
    best = 0
    # brute max antichain (n small)
    for r in range(n, 0, -1):
        found = False
        for A in itertools.combinations(range(n), r):
            if all(not P.comparable(a, b) for a, b in itertools.combinations(A, 2)):
                found = True
                break
        if found:
            return r
    return best


def run(n_lo=3, n_hi=7, include_families=True, out_path=None, verbose=True):
    rows = []
    skipped_spectrum = 0
    skipped_le = 0

    targets: List[Tuple[str, Poset]] = []
    if include_families:
        for nm, P in biased_families().items():
            targets.append((f"fam:{nm}", P))
        for nm, P in named_posets().items():
            if P.n <= n_hi + 1:
                targets.append((f"named:{nm}", P))
    for n in range(n_lo, n_hi + 1):
        for i, P in enumerate(enumerate_both_connected(n)):
            targets.append((f"enum-n{n}-#{i}", P))

    for name, P in targets:
        if P.linext_count() > LE_ENUM_CAP:
            skipped_le += 1
            if verbose:
                print(f"  SKIP (LE wall |L|={P.linext_count()} > {LE_ENUM_CAP}): {name}")
            continue
        row = analyze_poset(P, name)
        if row.get("bk_lambda2") is None and P.linext_count() > BK_SPECTRUM_CAP:
            skipped_spectrum += 1
        rows.append(row)
        if verbose:
            _print_row(row)

    summary = _summarize(rows, skipped_spectrum, skipped_le)
    if out_path:
        import json
        with open(out_path, "w") as f:
            json.dump(dict(summary=summary, rows=rows,
                           caps=dict(LE_ENUM_CAP=LE_ENUM_CAP,
                                     BK_SPECTRUM_CAP=BK_SPECTRUM_CAP,
                                     BK_CHEEGER_CAP=BK_CHEEGER_CAP)),
                      f, indent=2)
        print(f"\nwrote {out_path}  ({len(rows)} posets)")
    _print_summary(summary)
    return summary, rows


def _print_row(row):
    fp = row.get("frozen_phi_bk")
    fpt = row.get("frozen_phi_t_image")
    dl = row.get("delta")
    print(f"  [{row['name'][:32]:32s}] n={row['n']} w={row.get('width')} "
          f"|L|={row['num_LE']:5d} delta={('%.3f'%dl) if dl is not None else ' - '} "
          f"lam_std={row['lambda_std']:.4f} gap={row['transport_gap']:.4f} "
          f"Phi_BK(fr)={('%.4f'%fp) if fp is not None else '  -   '} "
          f"Phi_T(img)={('%.4f'%fpt) if fpt is not None else '  -  '} "
          f"bkgap={('%.4f'%row['bk_gap']) if row.get('bk_gap') is not None else ' - '}")


def _finite(xs):
    return [x for x in xs if x is not None and isinstance(x, float) and x == x
            and math.isfinite(x)]


def _summarize(rows, skipped_spectrum, skipped_le):
    import statistics
    # L1b implication vectors: only posets with a frozen pair (>=1 incomp pair)
    fr_rows = [r for r in rows if r.get("frozen_phi_bk") is not None]
    phi_bk = [r["frozen_phi_bk"] for r in fr_rows]
    minphi_bk = [r["min_phi_bk"] for r in fr_rows]
    gap = [r["transport_gap"] for r in fr_rows]
    phi_t_img = [r["frozen_phi_t_image"] for r in fr_rows]
    minphi_t_img = [r["minphi_phi_t_image"] for r in fr_rows]
    frozen_ratio = [r["frozen_ratio"] for r in fr_rows]

    # main L1b correlations (program predicts corr(Phi_BK, gap) > 0)
    corr_phibk_gap = _pearson(phi_bk, gap)
    corr_minphibk_gap = _pearson(minphi_bk, gap)
    corr_ratio_gap = _pearson(frozen_ratio, gap)
    # operational transfer correlation: does low Phi_BK map to low Phi_T image?
    tt_bk = [r["frozen_phi_bk"] for r in fr_rows if r["frozen_phi_t_image"] is not None
             and math.isfinite(r["frozen_phi_t_image"])]
    tt_t = [r["frozen_phi_t_image"] for r in fr_rows if r["frozen_phi_t_image"] is not None
            and math.isfinite(r["frozen_phi_t_image"])]
    corr_transfer = _pearson(tt_bk, tt_t)
    mm_bk = [r["min_phi_bk"] for r in fr_rows if r["minphi_phi_t_image"] is not None
             and math.isfinite(r["minphi_phi_t_image"])]
    mm_t = [r["minphi_phi_t_image"] for r in fr_rows if r["minphi_phi_t_image"] is not None
            and math.isfinite(r["minphi_phi_t_image"])]
    corr_transfer_minphi = _pearson(mm_bk, mm_t)

    # BK spectral gap vs transport gap (the walk-level transfer)
    bk_rows = [r for r in fr_rows if r.get("bk_gap") is not None]
    corr_bkgap_tgap = _pearson([r["bk_gap"] for r in bk_rows],
                               [r["transport_gap"] for r in bk_rows])

    # --- REFUTER HUNT ---
    # RED signature: low BK pair-cut conductance but transport gap NOT small
    # (lambda_std bounded away from 1). We report, among the LOWEST-Phi_BK posets,
    # what the transport gap actually is. If low Phi_BK reliably forces gap->0
    # there should be NO poset with (Phi_BK small AND gap large).
    if phi_bk:
        med_phibk = statistics.median(phi_bk)
        lo_phibk_rows = sorted(fr_rows, key=lambda r: r["frozen_phi_bk"])
        # the 25% lowest-Phi_BK posets: is their transport gap correspondingly small?
        q = max(1, len(lo_phibk_rows) // 4)
        low_bucket = lo_phibk_rows[:q]
        low_bucket_gap = [r["transport_gap"] for r in low_bucket]
        # explicit refuters: Phi_BK below the 25th pct but gap above its median.
        p25_phibk = sorted(phi_bk)[len(phi_bk) // 4]
        p50_gap = statistics.median(gap)
        refuters = [dict(name=r["name"], n=r["n"], phi_bk=r["frozen_phi_bk"],
                         gap=r["transport_gap"], lambda_std=r["lambda_std"],
                         max_bias=r.get("max_bias"), delta=r.get("delta"),
                         phi_t_image=r["frozen_phi_t_image"])
                     for r in fr_rows
                     if r["frozen_phi_bk"] <= p25_phibk
                     and r["transport_gap"] >= p50_gap]
        refuters.sort(key=lambda d: (d["phi_bk"], -d["gap"]))
    else:
        med_phibk = p25_phibk = p50_gap = None
        low_bucket_gap = []
        refuters = []

    # modulus fit: transport_gap ~ C * Phi_BK^alpha  (log-log slope), the empirical
    # modulus to aim a proof at. Fit on posets with both quantities positive.
    fit = _loglog_fit(phi_bk, gap)
    fit_minphi = _loglog_fit(minphi_bk, gap)

    # --- COUNTEREXAMPLE-REGIME CONDITIONING (the crux) ---
    # Theorem E's hypothesis is a gamma-COUNTEREXAMPLE: EVERY pair frozen,
    # i.e. delta(P) = max_pair min(p,1-p) < 1/3. No such poset exists, so we DRIVE
    # toward it: smaller delta = closer to the counterexample regime. The honest
    # L1b test asks, IN THIS REGIME, does low Phi_BK force lambda_std ~ 1 (gap->0)?
    # A single low-Phi_BK pair in an otherwise-balanced poset (large delta) is NOT
    # Theorem E's situation and is not a legitimate refuter.
    dl_rows = [r for r in fr_rows if r.get("delta") is not None]
    dl_rows.sort(key=lambda r: r["delta"])
    # the counterexample-approaching bucket: smallest-delta posets
    def _bucket(thresh):
        b = [r for r in dl_rows if r["delta"] <= thresh]
        if not b:
            return None
        return dict(
            thresh=thresh, n=len(b),
            corr_phibk_gap=_pearson([r["frozen_phi_bk"] for r in b],
                                    [r["transport_gap"] for r in b]),
            lambda_std_min=min(r["lambda_std"] for r in b),
            lambda_std_median=statistics.median([r["lambda_std"] for r in b]),
            lambda_std_max=max(r["lambda_std"] for r in b),
            gap_median=statistics.median([r["transport_gap"] for r in b]),
            gap_max=max(r["transport_gap"] for r in b),
            phi_bk_median=statistics.median([r["frozen_phi_bk"] for r in b]),
        )
    ce_buckets = [b for b in (_bucket(t) for t in (0.34, 0.38, 0.42, 0.5)) if b]
    # in-regime empirical modulus: fit transport_gap ~ C*Phi_BK^alpha on the
    # counterexample-driving bucket (delta<=0.42). This is the modulus to aim a
    # proof at -- the UNCONDITIONED fit is meaningless (dominated by balanced
    # posets whose single frozen pair is an artifact).
    inreg = [r for r in dl_rows if r["delta"] <= 0.42]
    modulus_inregime = _loglog_fit([r["frozen_phi_bk"] for r in inreg],
                                   [r["transport_gap"] for r in inreg])
    # does lambda_std TREND UP as delta trends DOWN toward 1/3? (program predicts yes)
    corr_delta_lambda = _pearson([r["delta"] for r in dl_rows],
                                 [r["lambda_std"] for r in dl_rows])
    # the k smallest-delta posets (deepest into the counterexample regime)
    smallest_delta = [dict(name=r["name"], n=r["n"], delta=r["delta"],
                           lambda_std=r["lambda_std"], gap=r["transport_gap"],
                           frozen_phi_bk=r["frozen_phi_bk"],
                           max_bias=r.get("max_bias"),
                           phi_t_image=r["frozen_phi_t_image"])
                      for r in dl_rows[:20]]
    # REGIME-AWARE refuter: low Phi_BK AND small delta (near counterexample) BUT
    # transport gap large (lambda_std far from 1). THIS is the genuine RED.
    ce_refuters = [dict(name=r["name"], n=r["n"], delta=r["delta"],
                        phi_bk=r["frozen_phi_bk"], gap=r["transport_gap"],
                        lambda_std=r["lambda_std"], max_bias=r.get("max_bias"))
                   for r in dl_rows
                   if r["delta"] <= 0.36 and r["frozen_phi_bk"] <= (p25_phibk or 1)
                   and r["lambda_std"] <= 0.75]
    ce_refuters.sort(key=lambda d: (d["delta"], d["frozen_phi_bk"] if False else -d["lambda_std"]))

    # --- PER-n conditioning: within each n, take the lowest-delta (most
    #     counterexample-like) posets and report their lambda_std. If the program
    #     is right, the deepest-into-the-regime poset at each n should have the
    #     HIGHEST lambda_std, and this should sharpen with n. ---
    per_n = {}
    ns = sorted(set(r["n"] for r in dl_rows))
    for nn in ns:
        b = sorted([r for r in dl_rows if r["n"] == nn], key=lambda r: r["delta"])
        if not b:
            continue
        # lowest-delta third at this n
        k = max(1, len(b) // 3)
        low = b[:k]
        per_n[nn] = dict(
            n=nn, count=len(b),
            min_delta=b[0]["delta"],
            argmin_delta_lambda_std=b[0]["lambda_std"],
            argmin_delta_phi_bk=b[0]["frozen_phi_bk"],
            low_delta_lambda_std_median=statistics.median([r["lambda_std"] for r in low]),
            low_delta_lambda_std_min=min(r["lambda_std"] for r in low),
            low_delta_phi_bk_median=statistics.median([r["frozen_phi_bk"] for r in low]),
            corr_phibk_gap=_pearson([r["frozen_phi_bk"] for r in b],
                                    [r["transport_gap"] for r in b]),
        )

    return dict(
        n_rows=len(rows), n_with_frozen_pair=len(fr_rows),
        skipped_spectrum=skipped_spectrum, skipped_le=skipped_le,
        # main correlations
        corr_frozenPhiBK_transportGap=corr_phibk_gap,
        corr_minPhiBK_transportGap=corr_minphibk_gap,
        corr_frozenRatio_transportGap=corr_ratio_gap,
        corr_operational_transfer_frozen=corr_transfer,
        corr_operational_transfer_minphi=corr_transfer_minphi,
        corr_bkGap_transportGap=corr_bkgap_tgap,
        # buckets / refuter hunt
        median_frozen_phi_bk=med_phibk,
        p25_frozen_phi_bk=p25_phibk,
        median_transport_gap=p50_gap,
        low_phibk_bucket_gap_median=(statistics.median(low_bucket_gap)
                                     if low_bucket_gap else None),
        low_phibk_bucket_gap_max=(max(low_bucket_gap) if low_bucket_gap else None),
        n_refuters=len(refuters),
        refuters=refuters[:25],
        # modulus
        loglog_fit_frozen=fit,
        loglog_fit_minphi=fit_minphi,
        # counterexample-regime conditioning (the crux)
        corr_delta_lambda_std=corr_delta_lambda,
        ce_buckets=ce_buckets,
        modulus_inregime_delta_le_0p42=modulus_inregime,
        smallest_delta_posets=smallest_delta,
        ce_regime_refuters=ce_refuters[:15],
        n_ce_regime_refuters=len(ce_refuters),
        per_n_conditioning=per_n,
        # ranges
        phi_bk_range=[min(phi_bk), max(phi_bk)] if phi_bk else None,
        transport_gap_range=[min(gap), max(gap)] if gap else None,
        max_bias_range=[min(_finite([r.get("max_bias") for r in fr_rows]) or [0]),
                        max(_finite([r.get("max_bias") for r in fr_rows]) or [0])]
        if fr_rows else None,
    )


def _loglog_fit(xs, ys):
    """Least-squares slope/intercept of log(y) vs log(x) over positive pairs.
    Returns dict(slope=alpha, intercept=logC, r, n) for the modulus
    transport_gap ~ C * Phi_BK^alpha. Also the min ratio gap/Phi_BK (a crude
    linear modulus constant)."""
    pts = [(x, y) for x, y in zip(xs, ys)
           if x is not None and y is not None and x > 1e-12 and y > 1e-12]
    if len(pts) < 3:
        return dict(slope=None, intercept=None, r=None, n=len(pts),
                    min_gap_over_phibk=None, max_gap_over_phibk=None)
    lx = [math.log(x) for x, _ in pts]
    ly = [math.log(y) for _, y in pts]
    n = len(pts)
    mx = sum(lx) / n; my = sum(ly) / n
    sxx = sum((a - mx) ** 2 for a in lx)
    sxy = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    slope = sxy / sxx if sxx > 1e-15 else None
    intercept = my - slope * mx if slope is not None else None
    r = _pearson(lx, ly)
    ratios = [y / x for x, y in pts]
    return dict(slope=slope, intercept=intercept, r=r, n=n,
                min_gap_over_phibk=min(ratios), max_gap_over_phibk=max(ratios),
                median_gap_over_phibk=sorted(ratios)[len(ratios) // 2])


def _print_summary(s):
    print("\n" + "=" * 78)
    print("L1b TRANSFER SUMMARY (BK low-conductance pair-cut  ->  lambda_std ~ 1 ?)")
    print("=" * 78)
    print(f"  posets analyzed: {s['n_rows']} (with a frozen pair: {s['n_with_frozen_pair']})")
    print(f"  skipped LE wall: {s['skipped_le']}   skipped BK spectrum cap: {s['skipped_spectrum']}")
    print("\n  -- MAIN L1b IMPLICATION (program predicts POSITIVE correlations) --")
    print(f"  corr(Phi_BK frozen, transport gap)      = {s['corr_frozenPhiBK_transportGap']:+.4f}")
    print(f"  corr(min Phi_BK pair, transport gap)    = {s['corr_minPhiBK_transportGap']:+.4f}")
    print(f"  corr(frozen E/Var ratio, transport gap) = {s['corr_frozenRatio_transportGap']:+.4f}")
    print(f"  corr(BK spectral gap, transport gap)    = {s['corr_bkGap_transportGap']:+.4f}")
    print("\n  -- OPERATIONAL TRANSFER (S_xy image energy in transport form) --")
    print(f"  corr(Phi_BK frozen, Phi_T of its image) = {s['corr_operational_transfer_frozen']:+.4f}")
    print(f"  corr(min Phi_BK,    Phi_T of its image) = {s['corr_operational_transfer_minphi']:+.4f}")
    print("\n  -- REFUTER HUNT (RED = low Phi_BK but transport gap NOT small) --")
    print(f"  median Phi_BK={s['median_frozen_phi_bk']}, 25th pct Phi_BK={s['p25_frozen_phi_bk']}")
    print(f"  median transport gap={s['median_transport_gap']}")
    print(f"  low-Phi_BK bucket (25% lowest): gap median={s['low_phibk_bucket_gap_median']} "
          f"max={s['low_phibk_bucket_gap_max']}")
    print(f"  # refuters (Phi_BK<=p25 AND gap>=median): {s['n_refuters']}")
    for rr in s["refuters"][:12]:
        print(f"     REFUTER? {rr['name'][:30]:30s} Phi_BK={rr['phi_bk']:.4f} "
              f"gap={rr['gap']:.4f} lam_std={rr['lambda_std']:.4f} "
              f"maxbias={rr['max_bias']} Phi_T(img)={rr['phi_t_image']}")
    print("\n  -- EMPIRICAL MODULUS  transport_gap ~ C * Phi_BK^alpha --")
    f = s["loglog_fit_frozen"]
    print(f"  frozen: slope(alpha)={f['slope']}, logC={f['intercept']}, r={f['r']}, n={f['n']}")
    print(f"          gap/Phi_BK ratio: min={f['min_gap_over_phibk']} "
          f"median={f['median_gap_over_phibk']} max={f['max_gap_over_phibk']}")
    print(f"  Phi_BK range={s['phi_bk_range']}  transport_gap range={s['transport_gap_range']}")
    print(f"  max_bias range over ensemble={s['max_bias_range']}")
    print("\n  -- COUNTEREXAMPLE-REGIME CONDITIONING (delta = max_pair min(p,1-p);"
          " counterexample iff delta<1/3) --")
    print(f"  corr(delta, lambda_std) = {s['corr_delta_lambda_std']:+.4f}  "
          f"(program predicts NEGATIVE: delta down -> lambda_std up toward 1)")
    print("  buckets (delta <= thresh): does lambda_std concentrate near 1 as we"
          " approach the counterexample regime?")
    for b in s["ce_buckets"]:
        print(f"    delta<={b['thresh']}: n={b['n']:3d}  lambda_std[min={b['lambda_std_min']:.3f} "
              f"med={b['lambda_std_median']:.3f} max={b['lambda_std_max']:.3f}]  "
              f"gap[med={b['gap_median']:.3f} max={b['gap_max']:.3f}]  "
              f"corr(Phi_BK,gap)={b['corr_phibk_gap']:+.3f}")
    mi = s["modulus_inregime_delta_le_0p42"]
    print(f"  IN-REGIME MODULUS (delta<=0.42): transport_gap ~ C*Phi_BK^alpha  "
          f"alpha={mi['slope']}, logC={mi['intercept']}, r={mi['r']}, n={mi['n']}")
    print(f"    gap/Phi_BK ratio in-regime: min={mi['min_gap_over_phibk']} "
          f"median={mi['median_gap_over_phibk']} max={mi['max_gap_over_phibk']}")
    print("  smallest-delta posets (deepest toward counterexample regime):")
    for r in s["smallest_delta_posets"][:12]:
        print(f"    delta={r['delta']:.3f} lam_std={r['lambda_std']:.3f} "
              f"gap={r['gap']:.3f} Phi_BK={r['frozen_phi_bk']:.4f} "
              f"maxbias={('%.3f'%r['max_bias']) if r['max_bias'] is not None else '-'} "
              f"[{r['name'][:34]}]")
    print(f"  # REGIME-AWARE refuters (delta<=0.36 AND low Phi_BK AND lambda_std<=0.75): "
          f"{s['n_ce_regime_refuters']}")
    for rr in s["ce_regime_refuters"][:10]:
        print(f"     RED? delta={rr['delta']:.3f} lam_std={rr['lambda_std']:.3f} "
              f"gap={rr['gap']:.3f} Phi_BK={rr['phi_bk']:.4f} [{rr['name'][:34]}]")
    print("\n  -- PER-n conditioning (lowest-delta posets at each n; program: min-delta"
          " poset should have HIGH lambda_std, sharpening with n) --")
    for nn, b in sorted(s["per_n_conditioning"].items()):
        print(f"    n={nn}: count={b['count']:4d}  min_delta={b['min_delta']:.3f} "
              f"-> lam_std={b['argmin_delta_lambda_std']:.3f} (Phi_BK={b['argmin_delta_phi_bk']:.4f}); "
              f"low-delta 1/3 bucket lam_std[min={b['low_delta_lambda_std_min']:.3f} "
              f"med={b['low_delta_lambda_std_median']:.3f}] "
              f"corr(Phi_BK,gap)={b['corr_phibk_gap']:+.3f}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n-lo", type=int, default=3)
    ap.add_argument("--n-hi", type=int, default=7,
                    help="max n for exhaustive both-connected enumeration (LE wall logged)")
    ap.add_argument("--no-families", action="store_true")
    ap.add_argument("--dump", type=str, default=None,
                    help="write JSON data table to this path")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    run(n_lo=args.n_lo, n_hi=args.n_hi, include_families=not args.no_families,
        out_path=args.dump, verbose=not args.quiet)


if __name__ == "__main__":
    main()
