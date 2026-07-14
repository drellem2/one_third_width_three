#!/usr/bin/env python3
"""mg-9de3 hunt4 (efficient): broad random generation of width-<=3 posets, scanning
(x, incomparable chain) for the block-cross ratio, recording the Pareto frontier
min full-delta vs achieved ratio. Optimizations: fast antichain-of-4 rejection;
full-delta computed lazily only for chains that already show ratio>=2.6.
"""
import sys, itertools, random, collections
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp
from onethird_mg9de3_blockcross_hunt import analyze, full_delta, width


def has_antichain4(P):
    """True iff P has an antichain of size >=4 (i.e. width>=4). Backtracking with
    incomparability adjacency, early exit."""
    n = P.n
    inc = [frozenset(y for y in range(n) if y != v and not P.comparable(v, y)) for v in range(n)]
    def rec(cand, depth):
        if depth == 4:
            return True
        for v in list(cand):
            if rec(cand & inc[v], depth + 1):
                return True
            cand = cand - {v}
        return False
    return rec(frozenset(range(n)), 0)


def maximal_inc_chains(P, x):
    inc = [y for y in range(P.n) if y != x and not P.comparable(x, y)]
    allch = []
    for r in range(2, len(inc) + 1):
        for sub in itertools.combinations(inc, r):
            if all(P.comparable(a, b) for a, b in itertools.combinations(sub, 2)):
                allch.append(frozenset(sub))
    sset = set(allch)
    out = []
    for c in allch:
        if not any(c < d for d in sset):
            out.append(tuple(sorted(c, key=lambda z: len(P.less[z] & set(c)))))
    return out


def gen_poset(n, rho, rng):
    order = list(range(n)); rng.shuffle(order)
    pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < rho:
                pairs.append((order[i], order[j]))
    return Poset(n, pairs)


def main():
    rng = random.Random(9032026)
    best_min_delta_bc = None
    frozen_hits = []
    by_p = collections.defaultdict(lambda: [1e9, None])
    ratio_at_delta = {t: 0.0 for t in [0.30, 0.32, 0.333, 0.34, 0.357, 0.36, 0.38, 0.40, 0.45, 0.50]}
    n_scanned = 0
    TARGET = 120000
    for trial in range(TARGET):
        n = rng.choice([8, 9, 10, 11])
        rho = rng.choice([0.30, 0.38, 0.45, 0.52, 0.60])
        P = gen_poset(n, rho, rng)
        if has_antichain4(P):
            continue
        n_scanned += 1
        fd_cache = None
        for x in range(n):
            for chain in maximal_inc_chains(P, x):
                r = analyze(P, x, chain)
                ratio = r['ratio']; p = len(chain)
                if ratio < 2.6:
                    continue
                # only now compute full delta (expensive)
                if fd_cache is None:
                    fd_cache = full_delta(P)[0]
                fd = fd_cache
                for t in ratio_at_delta:
                    if fd <= t + 1e-12 and ratio > ratio_at_delta[t]:
                        ratio_at_delta[t] = ratio
                if ratio >= 3.0:
                    if fd < by_p[p][0]:
                        by_p[p] = [fd, (ratio, n, r['a'])]
                    if best_min_delta_bc is None or fd < best_min_delta_bc[0]:
                        best_min_delta_bc = (fd, ratio, p, n, r['a'])
                if fd < 1/3 - 1e-9 and ratio > 2.5:
                    frozen_hits.append((fd, ratio, p, n, r['a']))
        if (trial + 1) % 20000 == 0:
            bmd = f"{best_min_delta_bc[0]:.4f}" if best_min_delta_bc else "NA"
            print(f"...{trial+1} trials, {n_scanned} width<=3; best-min-delta(ratio>=3)={bmd}", flush=True)
    print(f"\nTotal width<=3 posets scanned: {n_scanned}")
    print("\n=== Best ratio achievable at or below each full-delta threshold (width<=3) ===")
    for t in sorted(ratio_at_delta):
        print(f"  delta<={t:.3f}: max ratio = {ratio_at_delta[t]:.3f}")
    print("\n=== MIN full-delta among block-crossing (ratio>=3) configs, by chain length p ===")
    for p in sorted(by_p):
        d, wit = by_p[p]
        if wit:
            print(f"  p={p}: min delta = {d:.4f} (ratio={wit[0]:.3f}, n={wit[1]}) a={[f'{v:.2f}' for v in wit[2]]}")
    if best_min_delta_bc:
        print(f"\nGLOBAL best (min) delta for block-cross (ratio>=3): {best_min_delta_bc[0]:.4f} "
              f"(ratio={best_min_delta_bc[1]:.3f}, p={best_min_delta_bc[2]}, n={best_min_delta_bc[3]})")
        print(f"   slot a = {[f'{v:.3f}' for v in best_min_delta_bc[4]]}")
    print(f"\nStrictly-frozen (delta<1/3) width-3 configs with ratio>2.5: {len(frozen_hits)}")
    for h in sorted(frozen_hits)[:10]:
        print(f"   delta={h[0]:.4f} ratio={h[1]:.3f} p={h[2]} n={h[3]} a={[f'{v:.2f}' for v in h[4]]}")


if __name__ == "__main__":
    main()
