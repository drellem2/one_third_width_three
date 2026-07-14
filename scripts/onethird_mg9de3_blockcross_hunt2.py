#!/usr/bin/env python3
"""mg-9de3 hunt2: (a) validate pipeline on the known frozen tight3 tower (delta=1/3,
ratio 2 for p=2); (b) hill-climb over width-<=3 posets to MAXIMIZE the ratio of a
frozen incomparable chain while keeping full-delta<1/3, at n up to ~16 via fast DP.
"""
import sys, itertools, random
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp
from onethird_mg9de3_blockcross_hunt import (base_pairs, slot_distribution, analyze,
                                             full_delta, width)


# ---------- tight3 tower (ordinal sum of k copies of a||(b<c)) ----------
def tight3_tower(k):
    """k blocks, block i = {a_i, b_i, c_i} with b_i<c_i, a_i free; ordinal sum:
    every element of block i < every element of block i+1."""
    pairs = []
    idx = lambda i, t: 3 * i + t  # t: 0=a,1=b,2=c
    for i in range(k):
        pairs.append((idx(i, 1), idx(i, 2)))  # b_i < c_i
    # ordinal sum: block i entirely below block i+1
    for i in range(k):
        for j in range(i + 1, k):
            for s in range(3):
                for t in range(3):
                    pairs.append((idx(i, s), idx(j, t)))
    return Poset(3 * k, pairs)


def all_frozen_chains(P, min_len=1):
    """Yield (x, chain) for every x and every chain in Inc(x)."""
    for x in range(P.n):
        inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
        for r in range(min_len, len(inc) + 1):
            for sub in itertools.combinations(inc, r):
                if all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                    chain = tuple(sorted(sub, key=lambda z: len(P.less[z])))
                    yield x, chain


def best_frozen_ratio(P, require_full_frozen=True):
    """Return (best_ratio, x, chain, info). A chain qualifies if its x-vs-chain pairs
    are all frozen (per-pair). If require_full_frozen, also require full-delta(P)<1/3."""
    fd, _ = full_delta(P)
    if require_full_frozen and fd >= 1/3 - 1e-12:
        return None
    best = None
    for x, chain in all_frozen_chains(P, min_len=2):
        # per-pair frozen check
        biases = [1 - before_prob_dp(P, x, c) for c in chain]
        dchain = max(min(b, 1 - b) for b in biases)
        if dchain >= Fraction(1, 3):
            continue
        r = analyze(P, x, chain)
        if best is None or r['ratio'] > best[0]:
            best = (r['ratio'], x, chain, r, float(dchain), fd)
    return best


def validate_tower():
    print("=== tight3 tower validation (expect frozen delta~1/3, chain p=2 ratio~2) ===")
    for k in (2, 3, 4, 5):
        P = tight3_tower(k)
        fd, worst = full_delta(P)
        w = width(P)
        # find x=a_0 (element 0) chain (1,2) = b_0<c_0
        r = analyze(P, 0, (1, 2))
        print(f"k={k} n={P.n} width={w} full_delta={fd:.4f} | x=a0 chain=(b0,c0) "
              f"ratio={r['ratio']:.3f} a={[f'{v:.3f}' for v in r['a']]} j={r['j']}")


if __name__ == "__main__":
    validate_tower()
