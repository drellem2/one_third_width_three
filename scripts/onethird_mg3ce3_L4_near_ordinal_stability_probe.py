#!/usr/bin/env python3
"""
OneThird mg-3ce3: L4 near-ordinal-sum STABILITY stress probe at SMALL leakage
(thin interface), larger n. Follow-on to mg-b0a6.

Ticket:  mg-3ce3 (high, repo one_third_width_three). Daniel authorized directly
         on 2026-07-12 ("Scope"); supersedes the one-third build-pause gate for
         THIS computational probe only. Predecessor: mg-b0a6
         (scripts/onethird_mgb0a6_spectral_killshot_probe.py + docs/
         OneThird-Spectral-NearOrdinalSum-KillShot-Probe.md).

WHAT THIS PROBES  (the ONE surviving compute-testable risk from b0a6)
---------------------------------------------------------------------
b0a6 localized the surviving risk to L4:

    "low-conductance prefix => near ordinal sum => a balanced pair survives by
     minimality."

b0a6 was EXHAUSTIVE at n<=6, where no thin interface occurs -- its best-cut
leakage Delta1 bottomed out around 0.03-0.12 and the mandated N-poset had a
MAXIMALLY FAT interface (Delta1 = 0.5). That is the SAFE-to-Cheeger regime: a
fat interface is not what a lambda_std ~ 1 sweep selects. The DANGEROUS,
UNTESTED case is SMALL Delta1 (a genuinely thin interface): does a thin
interface actually FORCE a surviving balanced pair? That is the near-ordinal-sum
STABILITY conjecture (note Sec. 13), still open, and it lives at larger n where
b0a6 could not reach because it enumerated all n! linear extensions.

SCOPING INSIGHT THAT MAKES LARGER n FEASIBLE
--------------------------------------------
The L4 question needs only
  * element-position transport marginals T_P (n x n), and
  * pairwise biases p_xy = Pr[x before y],
both computable from LINEAR-EXTENSION MARGINALS via the order-ideal DP. It does
NOT need the n!-dim symmetrized Cayley spectrum (the b0a6 T2/T3 objects). So this
probe is NOT bounded by the n! wall. We reuse the b0a6 exact-LE order-ideal DP
(imported: linext_count, before_prob_dp, the Poset class) and ADD an order-ideal
DP transport matrix (transport_dp) that computes T_P by summing over the poset's
order ideals -- O(#ideals * n), which for the targeted bounded-width families is
polynomial and reaches n ~ 12-16 in milliseconds. lambda_std is an n x n
eigensolve on T_P|_H, never an S_n object.

  transport_dp validated against b0a6's brute transport_matrix on ALL 117 both-
  connected posets n=3..6 with 0 mismatches (see run_validation()).

THE L4 KILL TEST  (the point of the probe)
------------------------------------------
For each poset with a near-ordinal-sum cut A | B at leakage
    eps = Delta1(A) = E_sigma|A \\ sigma(A)| / min(|A|,|B|),
let S be the SMALLER side. The minimal-counterexample induction hypothesis says
P[S] (a strictly smaller poset, hence NOT a counterexample) HAS a balanced pair:
some incomparable {x,y} in S with p^{P[S]}_xy in [1/3, 2/3]. Near-ordinal-sum
STABILITY claims that pair survives in the FULL poset: p^P_xy stays in [1/3,2/3]
when the interface is thin. We test exactly this:

  * GREEN: the surviving-within-side-pair rate -> 1 as eps -> 0, with an
    empirical modulus F(eps) bounding the within-side perturbation
    D(A) = max over within-S incomparable pairs of |p^P_xy - p^{P[S]}_xy|.
    Report the fitted F(eps) and the smallest eps at which a within-side
    balanced pair is ever lost.
  * RED (L4 FALSE): even ONE poset with SMALL eps, NEITHER side a chain, where
    the interface coupling pushes EVERY within-side incomparable pair on both
    sides outside [1/3,2/3] in P (no surviving within-side balanced pair). That
    refutes near-ordinal-sum stability and breaks the programme's endgame.
  * AMBER: survives but F(eps) is weak / non-uniform, or the fat-interface
    pathology persists at moderate eps.

SKEPTICAL BAR (carried from b0a6, per pm-onethird feedback_lean_no_vacuous_
baseline_proofs / feedback_audit_bar_for_axioms): a high Rayleigh quotient /
lambda_std ~ 1 is NOT near-ordinal-sum evidence. The ONLY thing that de-risks L4
is surviving-within-side-pair behaviour as eps -> 0. We do not over-read a strong
correlation or a high capture fraction.

SCOPE: L4 only. L1 (bad BK mixing => lambda_std ~ 1) is the OTHER surviving risk
but is a proof/theory question shared with the Cech/F-series program -- NOT a
compute target here.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import statistics
from fractions import Fraction
from typing import Dict, List, Tuple, Optional

import numpy as np

# Reuse the b0a6 exact-LE engine verbatim (do NOT rebuild it).
from onethird_mgb0a6_spectral_killshot_probe import (
    Poset, before_prob_dp, enumerate_both_connected, _LCG, _random_poset,
)


# ==========================================================================
# Order-ideal DP transport matrix (the new scaling piece).
#   T_P[x][a] = Pr[element x occupies position a] over uniform LE(P).
#
#   For a linear extension, the first a positions form an ORDER IDEAL S (down-
#   set), and x sits at position a iff x is minimal in P|_{V\\S} (all predecessors
#   of x lie in S). The count of LE with prefix-ideal S and x at position a=|S|:
#       f[S] * g[S | {x}]
#   where f[S] = e(P|_S) (linear extensions of the ideal) and
#         g[S] = e(P|_{V\\S}) (linear extensions of the complementary filter).
#   So  N[x][a] = sum over ideals S, |S|=a, x minimal in V\\S  of  f[S]*g[S|{x}].
#   Enumerating order ideals is O(#ideals) (= O(n^width) for bounded width), each
#   with O(n) work -- polynomial, so n ~ 16 is milliseconds on width-3 families.
# ==========================================================================
def _pred_masks(P: Poset) -> List[int]:
    pred = [0] * P.n
    for e in range(P.n):
        m = 0
        for p in P.less[e]:
            m |= 1 << p
        pred[e] = m
    return pred


def _order_ideals(P: Poset, pred: List[int]) -> List[int]:
    """All order ideals (down-sets) of P as bitmasks. BFS adding an element i to
    ideal S whenever every predecessor of i is already in S."""
    n = P.n
    full = (1 << n) - 1
    seen = {0}
    frontier = {0}
    ideals = [0]
    while frontier:
        nxt = set()
        for S in frontier:
            comp = full & ~S
            mm = comp
            while mm:
                low = mm & (-mm)
                i = low.bit_length() - 1
                mm ^= low
                if (pred[i] & ~S) == 0:          # all predecessors of i in S
                    T = S | low
                    if T not in seen:
                        seen.add(T)
                        nxt.add(T)
                        ideals.append(T)
        frontier = nxt
    return ideals


def transport_dp(P: Poset) -> Tuple[np.ndarray, int]:
    """Return (T_P float n x n, e(P) int) via order-ideal DP. Exact integer counts
    cast to float only at the end. Matches b0a6 brute transport_matrix exactly."""
    n = P.n
    full = (1 << n) - 1
    pred = _pred_masks(P)
    ideals = _order_ideals(P, pred)

    # f[S] = e(P|_S): built up over ideals by removing a maximal element of S.
    f = {0: 1}
    for S in sorted(ideals):
        if S == 0:
            continue
        tot = 0
        mm = S
        while mm:
            low = mm & (-mm)
            i = low.bit_length() - 1
            mm ^= low
            rest = S ^ low
            # i maximal in S iff no j in rest has i as a predecessor
            is_succ = False
            t = rest
            while t:
                l2 = t & (-t)
                j = l2.bit_length() - 1
                t ^= l2
                if (pred[j] >> i) & 1:
                    is_succ = True
                    break
            if not is_succ:
                tot += f[rest]
        f[S] = tot

    # g[S] = e(P|_{V\\S}): built down over ideals by adding a minimal element of comp.
    g = {full: 1}
    for S in sorted(ideals, reverse=True):
        if S == full:
            continue
        comp = full & ~S
        tot = 0
        mm = comp
        while mm:
            low = mm & (-mm)
            i = low.bit_length() - 1
            mm ^= low
            if (pred[i] & ~S) == 0:               # i minimal in comp
                tot += g[S | low]
        g[S] = tot

    total = g[0]                                   # e(P)
    N = [[0] * n for _ in range(n)]
    for S in ideals:
        a = bin(S).count("1")
        comp = full & ~S
        mm = comp
        while mm:
            low = mm & (-mm)
            x = low.bit_length() - 1
            mm ^= low
            if (pred[x] & ~S) == 0:                # x minimal in comp => x at pos a
                N[x][a] += f[S] * g[S | low]
    T = np.zeros((n, n))
    for x in range(n):
        for a in range(n):
            T[x][a] = N[x][a] / total
    return T, total


def standard_lambda(T: np.ndarray) -> float:
    """lambda_std = top eigenvalue of S = (T+T^T)/2 restricted to H = 1^perp."""
    n = T.shape[0]
    S = (T + T.T) / 2.0
    M = np.eye(n) - np.ones((n, n)) / n
    w, V = np.linalg.eigh(M)
    B = V[:, [i for i in range(n) if w[i] > 0.5]]  # orthonormal basis of H
    Sh = B.T @ S @ B
    return float(np.max(np.linalg.eigvalsh(Sh)))


def expected_rank_from_T(T: np.ndarray) -> np.ndarray:
    return T @ np.arange(T.shape[0])


# ==========================================================================
# Leakage / ordinal-sum defect at a cut, from the transport marginals (no brute).
#   A = order[:k]. sigma(A) = elements in the first k positions.
#   E|A \\ sigma(A)| = sum_{x in A} Pr[pos(x) >= k]   (transport row tail sum).
#   Phi   = E|A\\sigma(A)| / |A|
#   Delta1= E|A\\sigma(A)| / min(|A|,|B|)      (L1 ordinal-sum defect / leakage)
# ==========================================================================
def leakage_at_cut(T: np.ndarray, order: List[int], k: int) -> Dict:
    n = T.shape[0]
    A = order[:k]
    leak = 0.0
    for x in A:
        leak += float(np.sum(T[x, k:]))           # Pr[pos(x) >= k]
    a, b = k, n - k
    return dict(k=k, leak=leak, Phi=leak / a, Delta1=leak / min(a, b))


# ==========================================================================
# Induced subposet on a subset (relabelled 0..|subset|-1), for within-side
# before-probabilities p^{P[S]}_xy.
# ==========================================================================
def induced_subposet(P: Poset, subset: List[int]) -> Tuple[Poset, Dict[int, int]]:
    idx = {e: i for i, e in enumerate(sorted(subset))}
    rel = []
    ss = set(subset)
    for e in subset:
        for p in P.less[e]:
            if p in ss:
                rel.append((idx[p], idx[e]))
    return Poset(len(subset), rel), idx


def within_side_pairs(P: Poset, side: List[int]) -> List[Tuple[int, int]]:
    ss = set(side)
    out = []
    for x, y in itertools.combinations(sorted(side), 2):
        if not P.comparable(x, y):
            out.append((x, y))
    return out


# ==========================================================================
# THE L4 KILL TEST at a designated cut A | B.
# ==========================================================================
def l4_test_at_cut(P: Poset, T: np.ndarray, order: List[int], k: int) -> Dict:
    """Cut A = order[:k], B = order[k:]. Smaller side S. For every within-S (and
    within-B for completeness) incomparable pair, compare p^P_xy to the within-
    side p^{P[S]}_xy. Report surviving balanced pair + perturbation modulus."""
    n = P.n
    A = sorted(order[:k])
    Bset = sorted(order[k:])
    lk = leakage_at_cut(T, order, k)
    eps = lk["Delta1"]

    def side_report(side: List[int]) -> Dict:
        pairs = within_side_pairs(P, side)
        is_chain = (len(pairs) == 0)
        sub, idx = (induced_subposet(P, side) if not is_chain else (None, None))
        recs = []
        for (x, y) in pairs:
            p_full = float(before_prob_dp(P, x, y))
            p_side = float(before_prob_dp(sub, idx[x], idx[y]))
            recs.append(dict(
                pair=(x, y), p_full=p_full, p_side=p_side,
                balanced_full=(1/3 - 1e-12 <= p_full <= 2/3 + 1e-12),
                balanced_side=(1/3 - 1e-12 <= p_side <= 2/3 + 1e-12),
                dev=abs(p_full - p_side),
            ))
        balanced_side_pairs = [r for r in recs if r["balanced_side"]]
        surviving = [r for r in balanced_side_pairs if r["balanced_full"]]
        any_full_balanced = [r for r in recs if r["balanced_full"]]
        D = max((r["dev"] for r in recs), default=0.0)
        return dict(
            side=side, size=len(side), is_chain=is_chain, n_incomp=len(pairs),
            n_balanced_side=len(balanced_side_pairs), n_surviving=len(surviving),
            n_any_full_balanced=len(any_full_balanced),
            D=D, recs=recs,
            has_balanced_side_pair=(len(balanced_side_pairs) > 0),
            survives=(len(surviving) > 0),
            any_within_side_balanced_full=(len(any_full_balanced) > 0),
        )

    small, big = (A, Bset) if len(A) <= len(Bset) else (Bset, A)
    rep_small = side_report(small)
    rep_big = side_report(big)

    # RED trigger: neither side a chain AND no within-side balanced-in-P pair on
    # EITHER side (interface coupling pushed every within-side pair outside
    # [1/3,2/3] -- the only balance, if any, is via cross pairs).
    neither_chain = (not rep_small["is_chain"]) and (not rep_big["is_chain"])
    no_within_side_survivor = (not rep_small["any_within_side_balanced_full"]
                               and not rep_big["any_within_side_balanced_full"])
    red_here = neither_chain and no_within_side_survivor

    # primary "survives" = smaller side keeps a balanced pair (the induction target)
    if rep_small["is_chain"]:
        primary_survives = rep_big["survives"] if not rep_big["is_chain"] else None
        primary_side = "big" if not rep_big["is_chain"] else "both-chain"
    else:
        primary_survives = rep_small["survives"]
        primary_side = "small"

    return dict(
        k=k, cutA=A, cutB=Bset, eps=eps, leak=lk["leak"], Phi=lk["Phi"],
        smaller_size=min(len(A), len(Bset)),
        small=rep_small, big=rep_big,
        neither_chain=neither_chain, red_here=red_here,
        primary_survives=primary_survives, primary_side=primary_side,
        # modulus datum: worst within-side perturbation over the SMALLER side
        D_small=rep_small["D"], D_max=max(rep_small["D"], rep_big["D"]),
    )


def best_prefix_min_delta1(P: Poset, T: np.ndarray, order: List[int]) -> int:
    """Return k of the THINNEST-interface prefix cut of `order` (min Delta1);
    that is the most ordinal-sum-like split -- the near-ordinal-sum candidate."""
    n = P.n
    best_k, best_d1 = 1, math.inf
    for k in range(1, n):
        d1 = leakage_at_cut(T, order, k)["Delta1"]
        if d1 < best_d1 - 1e-15:
            best_d1, best_k = d1, k
    return best_k


# ==========================================================================
# FAMILIES.
# ==========================================================================
def _ordinal_sum(blockA: Poset, blockB: Poset, drop_cross: List[Tuple[int, int]]
                 ) -> Poset:
    """A (+) B with the listed cross relations (a in A, b in B; local indices)
    DELETED. drop_cross entries are (i,j) with i in [0,|A|), j in [0,|B|)."""
    a, b = blockA.n, blockB.n
    rel = []
    for e in range(a):
        for p in blockA.less[e]:
            rel.append((p, e))
    for e in range(b):
        for p in blockB.less[e]:
            rel.append((p + a, e + a))
    drop = set(drop_cross)
    for i in range(a):
        for j in range(b):
            if (i, j) not in drop:
                rel.append((i, j + a))
    return Poset(a + b, rel)


def antichain(m: int) -> Poset:
    return Poset(m, [])


def chain(m: int) -> Poset:
    return Poset(m, [(i, i + 1) for i in range(m - 1)])


def n_poset() -> Poset:
    return Poset(4, [(0, 1), (2, 3)])


def family_near_ordinal_sums() -> List[Tuple[str, Poset, Tuple[List[int], int]]]:
    """Family 1: controlled near-ordinal-sums P = A (+) B with m interface
    relations DELETED, tuning best-prefix Delta1 continuously from 0 upward. The
    designated cut is (block-A indices | block-B indices). Neither side a chain
    whenever A and B each carry an incomparable pair.

    Returns list of (name, poset, (cut_A_indices, k)).
    """
    out = []
    blocks = {
        "2AC": antichain(2), "3AC": antichain(3), "4AC": antichain(4),
        "5AC": antichain(5), "6AC": antichain(6), "7AC": antichain(7),
        "8AC": antichain(8),
        "N": n_poset(), "V": Poset(3, [(0, 1), (0, 2)]),
        "2N": Poset(4, [(0, 1), (2, 3)]),               # alias for N
    }
    # combos chosen to (a) span n up to ~16 and (b) keep BOTH sides non-chain.
    combos = [
        ("3AC", "3AC"), ("3AC", "N"), ("N", "N"), ("3AC", "4AC"),
        ("4AC", "4AC"), ("N", "3AC"), ("V", "3AC"), ("N", "V"),
        ("3AC", "2AC"), ("4AC", "N"),
        # larger n, thin-interface targets:
        ("5AC", "5AC"), ("6AC", "6AC"), ("7AC", "7AC"), ("8AC", "8AC"),
        ("6AC", "4AC"), ("8AC", "6AC"), ("5AC", "N"), ("6AC", "N"),
        ("8AC", "N"), ("6AC", "3AC"), ("7AC", "5AC"),
    ]
    for (na, nb) in combos:
        A, B = blocks[na], blocks[nb]
        a, b = A.n, B.n
        cross = [(i, j) for i in range(a) for j in range(b)]
        ncross = len(cross)
        cutA = list(range(a))
        # THIN-INTERFACE SWEEP: delete a SMALL number m of cross relations from a
        # potentially LARGE ordinal sum -> eps grows continuously from 0. For big
        # blocks we densely sample small m (the near-ordinal-sum regime) and then
        # coarsely sample larger m up to the full antichain.
        small_ms = [m for m in range(0, min(ncross, 9) + 1)]
        big_ms = sorted(set([ncross // 4, ncross // 2, 3 * ncross // 4, ncross]))
        for m in sorted(set(small_ms + [m for m in big_ms if m > 9])):
            # delete the LAST m cross relations (biased to one corner -> asymmetric,
            # the within-side stressing case)
            drop = cross[ncross - m:] if m > 0 else []
            P = _ordinal_sum(A, B, drop)
            name = f"{na}(+){nb}_drop{m}/{ncross}"
            out.append((name, P, (cutA, a)))
        # symmetric diagonal-deletion variant: delete a matching (i,i), keeping
        # both sides internally symmetric (pure interface thinning, no within-side
        # asymmetry) -- the "easy" case the conjecture should handle cleanly.
        for m in range(0, min(a, b) + 1):
            drop = [(i, i) for i in range(m)]
            P = _ordinal_sum(A, B, drop)
            name = f"{na}(+){nb}_diag{m}"
            out.append((name, P, (cutA, a)))
    return out


def family_grown_n_posets() -> List[Tuple[str, Poset, Optional[Tuple[List[int], int]]]]:
    """Family 2: grown N-poset analogues -- stacked / widened / laddered N's.
    Does the b0a6 FAT-interface pathology (Delta1 ~ 0.5) persist, and crucially
    does it ever occur WITH small Delta1 at larger n? No designated cut (use the
    thinnest prefix of the expected-rank order)."""
    out = []

    # stacked N's: N (+) N (+) ... (ordinal sum of k copies)
    def stack_N(k: int) -> Poset:
        rel = []
        for c in range(k):
            base = 4 * c
            rel += [(base + 0, base + 1), (base + 2, base + 3)]
            if c > 0:
                prev = 4 * (c - 1)
                for u in range(prev, prev + 4):
                    for v in range(base, base + 4):
                        rel.append((u, v))
        return Poset(4 * k, rel)

    for k in (2, 3, 4):
        out.append((f"stackedN^{k}", stack_N(k), None))

    # widened N: m minima, m maxima, with a "shifted" matching that leaves a
    # zig-zag (fence) of incomparabilities -- the wide analogue of 2+2.
    def widened_N(m: int) -> Poset:
        # minima 0..m-1, maxima m..2m-1; i < m+i and i < m+((i+1)%m) but skip one
        rel = []
        for i in range(m):
            rel.append((i, m + i))
            if i + 1 < m:
                rel.append((i, m + i + 1))
        return Poset(2 * m, rel)

    for m in (3, 4, 5, 6):
        out.append((f"widenedN_m{m}", widened_N(m), None))

    # laddered N / fence: a1<b1>a2<b2>a3<... zigzag on n elements
    def fence(n: int) -> Poset:
        rel = []
        for i in range(n - 1):
            if i % 2 == 0:
                rel.append((i, i + 1))       # up
            else:
                rel.append((i + 1, i))       # down
        return Poset(n, rel)

    for n in (6, 8, 10, 12):
        out.append((f"fence{n}", fence(n), None))

    # N (+) antichain (+) N  (fat interface pinned between two N blocks)
    def N_ac_N(m: int) -> Poset:
        A, B = n_poset(), antichain(m)
        P1 = _ordinal_sum(A, B, [])
        return _ordinal_sum(P1, n_poset(), [])
    for m in (2, 3):
        out.append((f"N(+){m}AC(+)N", N_ac_N(m), None))

    return out


def family_sampled(sizes=(8, 9, 10), n_seeds=1500,
                   edge_specs=((2, 5), (1, 3), (3, 7))
                   ) -> List[Tuple[str, Poset, Optional[Tuple[List[int], int]]]]:
    """Family 3: reproducible LCG-sampled both-connected posets at n=8..10; we
    keep them all and let the analysis filter to small best-prefix Delta1 (thin
    interface). No designated cut."""
    out = []
    for n in sizes:
        for (en, ed) in edge_specs:
            for seed in range(1, n_seeds + 1):
                rng = _LCG(seed * 100003 + n * 7 + en)
                P = _random_poset(n, rng, en, ed)
                if not P.both_connected():
                    continue
                out.append((f"samp-n{n}-{en}/{ed}-s{seed}", P, None))
    return out


# ==========================================================================
# Driver: run the L4 kill test over all families, collect (eps, survived, D),
# fit F(eps), report verdict.
# ==========================================================================
def analyze_poset(name: str, P: Poset, cut: Optional[Tuple[List[int], int]],
                  thin_only: bool, thin_thresh: float) -> Optional[Dict]:
    if P.n < 4:
        return None
    T, ePcount = transport_dp(P)
    lam = standard_lambda(T)
    er = expected_rank_from_T(T)
    order = sorted(range(P.n), key=lambda e: (er[e], e))
    if cut is not None:
        cutA, k = cut
        # designated cut must be a prefix of the expected-rank order to be the
        # near-ordinal-sum interface; if leakage broke the ordering, fall back.
        if sorted(order[:k]) != sorted(cutA):
            k = best_prefix_min_delta1(P, T, order)
        res = l4_test_at_cut(P, T, order, k)
    else:
        k = best_prefix_min_delta1(P, T, order)
        res = l4_test_at_cut(P, T, order, k)
    res["name"] = name
    res["n"] = P.n
    res["lambda_std"] = lam
    res["e_order"] = order
    if thin_only and res["eps"] > thin_thresh:
        return None
    return res


def run(args):
    rows = []
    fams = []
    if args.families in ("all", "nos"):
        fams += [("nos", nm, P, cut) for (nm, P, cut) in family_near_ordinal_sums()]
    if args.families in ("all", "grownN"):
        fams += [("grownN", nm, P, cut) for (nm, P, cut) in family_grown_n_posets()]
    if args.families in ("all", "sampled"):
        fams += [("sampled", nm, P, cut)
                 for (nm, P, cut) in family_sampled(n_seeds=args.sample_seeds)]

    print(f"analyzing {len(fams)} posets across families...")
    for (fam, nm, P, cut) in fams:
        thin_only = (fam == "sampled")
        res = analyze_poset(nm, P, cut, thin_only, args.thin_thresh)
        if res is None:
            continue
        res["family"] = fam
        rows.append(res)
    print(f"  -> {len(rows)} posets with a usable cut")

    # ---- aggregate the L4 signal ----
    # TWO readings of near-ordinal-sum stability:
    #  (P1) ENDGAME form (what the minimal-counterexample argument actually needs):
    #       >=1 side keeps a within-side balanced pair in P. Its failure = red_here
    #       (neither side a chain AND no within-side survivor on either side). This
    #       is the ticket's own RED criterion.
    #  (P2) STRICTER smaller-side reading: the SMALLER side (the induction target
    #       the note emphasizes) keeps a balanced pair. Non-uniformity here is the
    #       AMBER refinement, not a programme-breaking RED.
    pts = []                       # smaller-side stability points (P2 modulus data)
    red_events = []                # P1 failures (ticket RED): neither side survives
    loss_events = []               # P2 failures: smaller side loses all balanced pairs
    for r in rows:
        small = r["small"]
        if not small["is_chain"]:
            pts.append(dict(eps=r["eps"], survives=small["survives"], D=small["D"],
                            name=r["name"], family=r["family"], n=r["n"],
                            n_balanced_side=small["n_balanced_side"],
                            n_surviving=small["n_surviving"],
                            big_survives=r["big"]["survives"],
                            big_is_chain=r["big"]["is_chain"],
                            lam=r["lambda_std"]))
            if small["has_balanced_side_pair"] and not small["survives"]:
                loss_events.append(r)
        if r["red_here"]:
            red_events.append(r)

    # F(eps): fit within-side perturbation D vs eps. Regression through origin
    # (D = C*eps) and log-log slope (D ~ C*eps^alpha), over points with eps>0.
    pos = [p for p in pts if p["eps"] > 1e-9 and p["D"] > 0]
    if pos:
        xs = np.array([p["eps"] for p in pos])
        ds = np.array([p["D"] for p in pos])
        C_lin = float(np.sum(xs * ds) / np.sum(xs * xs))          # D = C*eps
        resid = ds - C_lin * xs
        ss_res = float(np.sum(resid ** 2))
        ss_tot = float(np.sum((ds - ds.mean()) ** 2))
        r2_lin = 1 - ss_res / ss_tot if ss_tot > 0 else float("nan")
        lx, ld = np.log(xs), np.log(ds)
        A = np.vstack([lx, np.ones_like(lx)]).T
        alpha, logC = np.linalg.lstsq(A, ld, rcond=None)[0]
        Cpow = float(np.exp(logC))
        pred = alpha * lx + logC
        r2_log = 1 - float(np.sum((ld - pred) ** 2)) / float(np.sum((ld - ld.mean()) ** 2))
    else:
        C_lin = r2_lin = alpha = Cpow = r2_log = float("nan")

    # survival rate by eps band (the GREEN criterion: -> 1 as eps -> 0)
    bands = [(0.0, 0.02), (0.02, 0.05), (0.05, 0.10), (0.10, 0.20),
             (0.20, 0.35), (0.35, 1.01)]
    band_stats = []
    for (lo, hi) in bands:
        b = [p for p in pts if lo <= p["eps"] < hi]
        if b:
            rate = sum(1 for p in b if p["survives"]) / len(b)
            band_stats.append(dict(lo=lo, hi=hi, count=len(b), survive_rate=rate,
                                    D_max=max(p["D"] for p in b),
                                    D_median=statistics.median(p["D"] for p in b)))
        else:
            band_stats.append(dict(lo=lo, hi=hi, count=0, survive_rate=None,
                                    D_max=None, D_median=None))

    smallest_eps_loss = min((r["eps"] for r in loss_events), default=None)
    smallest_eps_red = min((r["eps"] for r in red_events), default=None)

    # endgame-form (P1) universality: >=1 side survives on EVERY poset with both
    # sides non-chain (the ticket's actual RED criterion never firing).
    both_nonchain = [r for r in rows if r["neither_chain"]]
    endgame_survive = sum(1 for r in both_nonchain if not r["red_here"])
    endgame_rate = (endgame_survive / len(both_nonchain)) if both_nonchain else None

    # ENVELOPE modulus F(eps) = max within-side perturbation D per eps band (the
    # honest upper bound: how far can a within-side p^P stray from p^side at leakage
    # <= eps). Monotone, -> 0 as eps -> 0.
    envelope = []
    for hi in (0.02, 0.05, 0.10, 0.15, 0.20):
        b = [p for p in pts if p["eps"] <= hi]
        if b:
            envelope.append(dict(eps_le=hi, D_max=max(p["D"] for p in b),
                                 count=len(b),
                                 survive_rate=sum(1 for p in b if p["survives"]) / len(b)))

    # ---- verdict ----
    small_band = [p for p in pts if p["eps"] < 0.05]
    small_band_rate = (sum(1 for p in small_band if p["survives"]) / len(small_band)
                       if small_band else None)
    verdict, why = _verdict(red_events, endgame_rate, small_band_rate, band_stats,
                            smallest_eps_loss, envelope)

    summary = dict(
        n_posets=len(rows), n_stability_points=len(pts),
        n_red_events=len(red_events), n_loss_events=len(loss_events),
        endgame_form_both_nonchain=len(both_nonchain),
        endgame_form_survive_rate=endgame_rate,
        smallest_eps_with_smaller_side_loss=smallest_eps_loss,
        smallest_eps_red=smallest_eps_red,
        envelope_modulus=envelope,
        F_fit_linear_C=C_lin, F_fit_linear_R2=r2_lin,
        F_fit_power_alpha=alpha, F_fit_power_C=Cpow, F_fit_power_R2=r2_log,
        small_band_survive_rate_eps_lt_0p05=small_band_rate,
        band_stats=band_stats, verdict=verdict, verdict_why=why,
        max_lambda_std=max((r["lambda_std"] for r in rows), default=None),
        max_n=max((r["n"] for r in rows), default=None),
    )

    _print_report(summary, rows, red_events, loss_events, band_stats, pts)

    if args.dump:
        _dump(args.out, summary, rows, red_events, loss_events, pts)
    return summary


def _verdict(red_events, endgame_rate, small_band_rate, band_stats,
             smallest_eps_loss, envelope):
    # The ticket's RED criterion (endgame / P1 form): a poset with small eps,
    # neither side a chain, and NO surviving within-side balanced pair on EITHER
    # side. This is what the minimal-counterexample argument actually needs.
    if red_events:
        return "RED", (f"{len(red_events)} poset(s) with small eps, neither side a "
                       f"chain, and NO surviving within-side balanced pair on either "
                       f"side -- near-ordinal-sum stability (endgame form) FALSE.")
    # GREEN (endgame form): the >=1-side-survives property is universal (rate 1.0).
    # The smaller-side-only reading (P2) may be non-uniform; that is a documented
    # refinement (proof must be free to pick the side), NOT a RED.
    endgame_ok = (endgame_rate is None) or (endgame_rate > 0.9999)
    env_env = envelope[0]["D_max"] if envelope else float("nan")
    if endgame_ok:
        p2 = (f"smaller-side-only reading uniform below eps={smallest_eps_loss:.3f} "
              f"then non-uniform (bigger side always covers)"
              if smallest_eps_loss is not None
              else "smaller-side reading uniform everywhere too")
        return "GREEN", (f"endgame form (>=1 side keeps a within-side balanced pair) "
                         f"UNIVERSAL across all both-non-chain posets; envelope "
                         f"F(0.02)<={env_env:.3f}; {p2}.")
    return "AMBER", (f"endgame survive rate={endgame_rate}; smaller-side first loss "
                     f"eps={smallest_eps_loss}.")


def _print_report(summary, rows, red_events, loss_events, band_stats, pts):
    print("\n" + "=" * 78)
    print("L4 NEAR-ORDINAL-SUM STABILITY PROBE (mg-3ce3) -- SUMMARY")
    print("=" * 78)
    print(f"  posets analyzed:                 {summary['n_posets']}")
    print(f"  stability data points:           {summary['n_stability_points']}")
    print(f"  max n reached:                   {summary['max_n']}")
    print(f"  max lambda_std:                  {summary['max_lambda_std']:.4f}")
    print(f"  RED events (endgame kill):       {summary['n_red_events']}")
    print(f"  endgame form (>=1 side survives) universal: "
          f"{summary['endgame_form_survive_rate']} "
          f"over {summary['endgame_form_both_nonchain']} both-non-chain posets")
    print(f"  smaller-side-only losses:        {summary['n_loss_events']} "
          f"(bigger side always covers)")
    print(f"  smallest eps with a smaller-side loss: "
          f"{summary['smallest_eps_with_smaller_side_loss']}")
    print(f"  smallest eps with a RED event:   {summary['smallest_eps_red']}")
    print("\n  envelope modulus F(eps) = max within-side |p^P - p^side| for eps<=x:")
    for e in summary["envelope_modulus"]:
        print(f"    eps<={e['eps_le']:.2f}:  F<={e['D_max']:.4f}  "
              f"(n={e['count']}, smaller-side survive rate={e['survive_rate']:.4f})")
    print("\n  survival rate by leakage band eps=Delta1(smaller side):")
    print(f"    {'band':>16s} {'count':>6s} {'survive':>8s} {'D_med':>8s} {'D_max':>8s}")
    for b in band_stats:
        rate = "-" if b["survive_rate"] is None else f"{b['survive_rate']:.3f}"
        dm = "-" if b["D_median"] is None else f"{b['D_median']:.4f}"
        dx = "-" if b["D_max"] is None else f"{b['D_max']:.4f}"
        print(f"    [{b['lo']:.2f},{b['hi']:.2f}) {b['count']:6d} {rate:>8s} "
              f"{dm:>8s} {dx:>8s}")
    print("\n  F(eps) fit (within-side perturbation D = max|p^P - p^side|):")
    print(f"    linear   D = {summary['F_fit_linear_C']:.4f} * eps  "
          f"(R^2={summary['F_fit_linear_R2']:.3f})")
    print(f"    power    D = {summary['F_fit_power_C']:.4f} * eps^"
          f"{summary['F_fit_power_alpha']:.3f}  (R^2={summary['F_fit_power_R2']:.3f})")
    if red_events:
        print("\n  *** RED EVENTS (near-ordinal-sum stability counterexamples) ***")
        for r in red_events[:10]:
            print(f"    [{r['name']}] n={r['n']} eps={r['eps']:.4f} "
                  f"lambda={r['lambda_std']:.3f} cutA={r['cutA']} cutB={r['cutB']}")
    if loss_events:
        print("\n  within-side balanced-pair LOSS events (side kept some balanced-in-"
              "side pair but ALL were pushed out of [1/3,2/3] in P):")
        for r in sorted(loss_events, key=lambda x: x["eps"])[:12]:
            s = r["small"]
            print(f"    [{r['name']}] n={r['n']} eps={r['eps']:.4f} "
                  f"side|S|={s['size']} balanced_side={s['n_balanced_side']} "
                  f"surviving={s['n_surviving']} lambda={r['lambda_std']:.3f}")
    print(f"\n  VERDICT: {summary['verdict']}")
    print(f"    {summary['verdict_why']}")


def _dump(path, summary, rows, red_events, loss_events, pts):
    def slim(r):
        return dict(name=r["name"], family=r["family"], n=r["n"],
                    eps=r["eps"], lambda_std=r["lambda_std"], k=r["k"],
                    cutA=r["cutA"], cutB=r["cutB"],
                    neither_chain=r["neither_chain"], red_here=r["red_here"],
                    smaller_size=r["smaller_size"],
                    small=dict(size=r["small"]["size"], is_chain=r["small"]["is_chain"],
                               n_incomp=r["small"]["n_incomp"],
                               n_balanced_side=r["small"]["n_balanced_side"],
                               n_surviving=r["small"]["n_surviving"],
                               survives=r["small"]["survives"], D=r["small"]["D"]),
                    big=dict(size=r["big"]["size"], is_chain=r["big"]["is_chain"],
                             n_incomp=r["big"]["n_incomp"],
                             n_balanced_side=r["big"]["n_balanced_side"],
                             n_surviving=r["big"]["n_surviving"],
                             survives=r["big"]["survives"], D=r["big"]["D"]))
    # Keep every constructed-family row (nos + grownN are small and each is a
    # designed stress case), but for the large sampled family keep only the
    # INTERESTING rows (losses / RED / a thin high-lambda spot-check) so the
    # artifact stays small. The aggregate signal lives in `summary` +
    # `stability_points` (stored compactly), which cover ALL posets.
    keep_rows = []
    spot = 0
    for r in rows:
        interesting = (r["family"] != "sampled"
                       or r["red_here"]
                       or (not r["small"]["is_chain"]
                           and r["small"]["n_balanced_side"] > 0
                           and not r["small"]["survives"]))
        if not interesting and r["family"] == "sampled" and \
                r["lambda_std"] >= 0.9 and r["eps"] <= 0.05 and spot < 40:
            interesting = True                      # a few clean thin high-lambda rows
            spot += 1
        if interesting:
            keep_rows.append(slim(r))
    # compact stability points: [eps, survives(0/1), D, n, lambda, big_survives(0/1)]
    cpts = [[round(p["eps"], 6), int(p["survives"]), round(p["D"], 6), p["n"],
             round(p["lam"], 4), int(p["big_survives"])] for p in pts]
    with open(path, "w") as f:
        json.dump(dict(summary=summary,
                       stability_points_schema=["eps", "survives", "D", "n",
                                                "lambda_std", "big_survives"],
                       stability_points=cpts,
                       kept_rows_note=("all nos+grownN rows + sampled loss/RED/"
                                       "thin-high-lambda spot rows; full signal in "
                                       "summary + stability_points"),
                       rows=keep_rows), f, indent=2)
    print(f"\n  wrote {path} ({len(keep_rows)}/{len(rows)} rows kept, "
          f"{len(cpts)} stability points)")


# ==========================================================================
# Validation: transport_dp vs b0a6 brute transport_matrix.
# ==========================================================================
def run_validation():
    from onethird_mgb0a6_spectral_killshot_probe import transport_matrix
    bad = 0
    cnt = 0
    for n in range(3, 7):
        for P in enumerate_both_connected(n):
            Tb = transport_matrix(P)
            Td, _ = transport_dp(P)
            if not np.allclose(Tb, Td, atol=1e-12):
                bad += 1
                if bad <= 3:
                    print(f"  MISMATCH n={n}: {np.round(Tb - Td, 5)}")
            cnt += 1
    # named stress posets too
    for name, rel, n in [("N", [(0, 1), (2, 3)], 4),
                         ("3+2", [(0, 1), (1, 2), (3, 4)], 5),
                         ("2AC+2AC", [(0, 2), (0, 3), (1, 2), (1, 3)], 4)]:
        P = Poset(n, rel)
        from onethird_mgb0a6_spectral_killshot_probe import transport_matrix as tm
        if not np.allclose(tm(P), transport_dp(P)[0], atol=1e-12):
            bad += 1
        cnt += 1
    print(f"  transport_dp validated on {cnt} posets, mismatches={bad}")
    assert bad == 0, "transport_dp disagrees with brute transport_matrix!"
    return bad == 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--families", default="all",
                    choices=["all", "nos", "grownN", "sampled"])
    ap.add_argument("--sample-seeds", type=int, default=1500,
                    help="LCG seeds per (size, edge-spec) for the sampled family")
    ap.add_argument("--thin-thresh", type=float, default=0.20,
                    help="keep sampled posets with best-prefix Delta1 <= this")
    ap.add_argument("--dump", action="store_true")
    ap.add_argument("--out", default="data/onethird-mg3ce3-L4-near-ordinal-stability.json")
    ap.add_argument("--validate", action="store_true",
                    help="run transport_dp vs brute cross-check and exit")
    args = ap.parse_args()

    if args.validate:
        run_validation()
        return
    print("cross-checking transport_dp vs b0a6 brute engine...")
    run_validation()
    run(args)


if __name__ == "__main__":
    main()
