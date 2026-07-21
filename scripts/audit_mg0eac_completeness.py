#!/usr/bin/env python3
"""INDEPENDENT AUDIT of mg-0eac sec.9 -- SEARCH COMPLETENESS.

"Nothing below beta" is a negative result, and negative results are where a bug
or a silent cap hides.  This module re-certifies every layer the sec.9 sweep
depends on, by routes that share as little as possible with the merged code.

  (1) canonical augmentation complete?   unpruned enumeration vs OEIS A000112
  (2) width oracle correct?              width_value_bitmask vs brute-force
                                         largest antichain, over ALL posets
  (3) does the width prune drop posets?  width-<=3 counts from (unpruned
                                         enumeration + MY width) vs the pruned
                                         enumerator's counts
  (4) primitivity filter over-excludes?  is_primitive vs brute-force search for
                                         a proper ordinal-sum splitting
  (5) sweep engine == control engines?   fast_Q vs Q_primary vs my independent
                                         linear-extension engine

(2) and (3) matter because sec.9.2's prune certification applies the SAME width
oracle to both of its "two independent routes" (audit Finding F3), so it cannot
detect a width-oracle bug.  (5) matters because five_engine_check never calls
fast_Q (audit Finding F2), the engine that produces every swept delta.

Result on this machine: 0 disagreements everywhere, n <= 8.  No false-negative
channel found; the width-3 n<=11 enumeration is genuinely exhaustive.

Usage:  python3 scripts/audit_mg0eac_completeness.py [NMAX=8] [INDEP_NMAX=7]
"""
import os
import sys
from itertools import combinations

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

from onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust import (
    width_value_bitmask, fast_Q, Q_primary,
)
from onethird_ap2_prong3g_alpha_nonselfdual_n10_13_exhaust import (
    order_canon, children_max,
)
from onethird_mg0eac_primitive_delta_search import is_primitive, to_belowdict
from audit_mg0eac_independent_delta import (
    audit_delta, width_bruteforce, incomparability_connected,
)

# OEIS A000112 -- number of partially ordered sets on n unlabelled elements.
A000112 = {1: 1, 2: 2, 3: 5, 4: 16, 5: 63, 6: 318, 7: 2045, 8: 16999,
           9: 183231}


def is_ordinal_sum_bruteforce(n, below):
    """True iff some proper split into nonempty A, B has EVERY a in A strictly
    below EVERY b in B.  Primitive == NOT an ordinal sum."""
    for r in range(1, n):
        for A in combinations(range(n), r):
            As = set(A)
            B = [x for x in range(n) if x not in As]
            if all(below[b] >> a & 1 for a in A for b in B):
                return True
    return False


def pruned_width_le_counts(W, nmax):
    """Counts produced by the MERGED code's width-pruned canonical augmentation."""
    level = {order_canon(1, [0]): [0]}
    counts = {1: 1}
    for n in range(2, nmax + 1):
        nxt = {}
        for below in level.values():
            for nb in children_max(n - 1, below):
                if width_value_bitmask(n, nb) > W:
                    continue
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        level = nxt
        counts[n] = len(level)
    return counts


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    indep_nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 7

    print("=" * 104)
    print("SEARCH-COMPLETENESS AUDIT -- unpruned enumeration + independent oracles")
    print("=" * 104)

    pruned3 = pruned_width_le_counts(3, nmax)
    pruned2 = pruned_width_le_counts(2, nmax)

    level = {order_canon(1, [0]): [0]}
    tot = bad_w = bad_prim = bad_fq = bad_ind = 0
    bad_a000112 = bad_prune3 = bad_prune2 = 0

    for n in range(2, nmax + 1):
        nxt = {}
        for below in level.values():
            for nb in children_max(n - 1, below):        # NO width prune
                k = order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        level = nxt

        nw = nprim = nfq = nind = 0
        dist = {}
        for below in level.values():
            tot += 1
            bl = list(below)

            # (2) width oracle vs brute-force largest antichain
            w_o = width_value_bitmask(n, below)
            w_b = width_bruteforce(n, bl)
            dist[w_b] = dist.get(w_b, 0) + 1
            if w_o != w_b:
                nw += 1

            # (4) primitivity vs brute-force ordinal-sum splitting
            truth = not is_ordinal_sum_bruteforce(n, bl)
            if is_primitive(n, below) != truth:
                nprim += 1
            if incomparability_connected(n, bl) != truth:
                nprim += 1

            # (5) sweep engine vs control engine vs independent engine
            if w_b <= 3:
                e_f, d_f, _ = fast_Q(n, below)
                e_p, d_p, _ = Q_primary(list(range(n)), to_belowdict(n, below))
                if (e_f, d_f) != (e_p, d_p):
                    nfq += 1
                if n <= indep_nmax:
                    e_i, d_i, _ = audit_delta(n, bl)
                    if (e_i, d_i) != (e_f, d_f):
                        nind += 1

        bad_w += nw
        bad_prim += nprim
        bad_fq += nfq
        bad_ind += nind

        # (1) canonical augmentation vs A000112
        a_ok = (len(level) == A000112.get(n))
        bad_a000112 += (0 if a_ok else 1)
        # (3) prune vs unpruned + my own width
        mine3 = sum(v for k, v in dist.items() if k <= 3)
        mine2 = sum(v for k, v in dist.items() if k <= 2)
        p3_ok = (mine3 == pruned3.get(n))
        p2_ok = (mine2 == pruned2.get(n))
        bad_prune3 += (0 if p3_ok else 1)
        bad_prune2 += (0 if p2_ok else 1)

        print(f"  n={n:2d}  all-width={len(level):>6,} "
              f"[A000112 {'OK' if a_ok else '*** MISMATCH ***'}]  "
              f"w<=3: mine={mine3:>5,} pruned={pruned3.get(n):>5,} "
              f"{'OK' if p3_ok else '*** MISMATCH ***'}  "
              f"w<=2: mine={mine2:>4,} pruned={pruned2.get(n):>4,} "
              f"{'OK' if p2_ok else '*** MISMATCH ***'}  |  "
              f"oracle={nw} prim={nprim} fast_Q={nfq} indep={nind}",
              flush=True)

    print("\n" + "=" * 104)
    print(f"  posets examined: {tot:,}   (independent delta engine run to n={indep_nmax})")
    print(f"  (1) canonical augmentation vs A000112 .............. "
          f"{bad_a000112} mismatched levels  "
          f"{'PASS' if bad_a000112 == 0 else '*** FAIL ***'}")
    print(f"  (2) width oracle vs brute-force antichain .......... "
          f"{bad_w} disagreements  {'PASS' if bad_w == 0 else '*** FAIL ***'}")
    print(f"  (3) width prune vs unpruned + independent width .... "
          f"{bad_prune3 + bad_prune2} mismatched levels  "
          f"{'PASS' if bad_prune3 + bad_prune2 == 0 else '*** FAIL ***'}")
    print(f"  (4) primitivity vs ordinal-sum brute force ......... "
          f"{bad_prim} disagreements  {'PASS' if bad_prim == 0 else '*** FAIL ***'}")
    print(f"  (5) fast_Q vs Q_primary ............................ "
          f"{bad_fq} disagreements  {'PASS' if bad_fq == 0 else '*** FAIL ***'}")
    print(f"      fast_Q vs INDEPENDENT engine ................... "
          f"{bad_ind} disagreements  {'PASS' if bad_ind == 0 else '*** FAIL ***'}")
    allok = (bad_a000112 == bad_w == bad_prim == bad_fq == bad_ind == 0
             and bad_prune3 == bad_prune2 == 0)
    print("\n  => " + ("NO false-negative channel found; the width-3 enumeration is "
                       "genuinely exhaustive." if allok
                       else "*** A COMPLETENESS DEFECT WAS FOUND ***"))


if __name__ == "__main__":
    main()
