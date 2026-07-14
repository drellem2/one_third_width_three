#!/usr/bin/env python3
"""mg-9de3 hunt3: simulated-annealing / random structured search over width-<=3
posets (fast O(2^n) DP) to (i) maximize the ratio of a strictly-frozen incomparable
chain with full-delta(P)<1/3, and (ii) map the frontier: min full-delta achievable
for a block-crossing config (ratio>=3) as a function of chain length p.

We fix ONE distinguished element x and a distinguished long chain C incomparable to
x, and let the search add/remove OTHER relations (a "coupling scaffold") to try to
freeze x while keeping the slot distribution bimodal. Relations that would make x
comparable to a chain element, or create width>3, are forbidden/penalized.
"""
import sys, itertools, random, math
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp
from onethird_mg9de3_blockcross_hunt import base_pairs, slot_distribution, analyze, full_delta, width


def make_poset(n, x, chain, extra_edges):
    """chain: forced c_1<...<c_p. extra_edges: set of directed (a,b). Build poset."""
    pairs = [(chain[i], chain[i + 1]) for i in range(len(chain) - 1)]
    pairs += list(extra_edges)
    return Poset(n, pairs)


def is_x_chain_incomparable(P, x, chain):
    return all(not P.comparable(x, c) for c in chain)


def evaluate(n, x, chain, extra_edges):
    """Return dict(ratio, full_delta, width, ok) for the given config, or None if invalid."""
    try:
        P = make_poset(n, x, chain, extra_edges)
    except ValueError:
        return None  # cyclic
    if not is_x_chain_incomparable(P, x, chain):
        return None
    w = width(P)
    fd, _ = full_delta(P)
    r = analyze(P, x, chain)
    # per-pair chain frozen delta
    biases = [1 - before_prob_dp(P, x, c) for c in chain]
    dchain = float(max(min(b, 1 - b) for b in biases))
    return dict(ratio=r['ratio'], full_delta=fd, dchain=dchain, width=w, a=r['a'], j=r['j'], P=P)


def candidate_edges(n, x, chain):
    """All directed edges we may toggle: any (a,b), a!=b, that does NOT directly relate
    x to a chain element. (Transitive effects still checked at build time.)"""
    chainset = set(chain)
    edges = []
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            # forbid direct x<->chain relations (keep x incomparable to chain)
            if (a == x and b in chainset) or (b == x and a in chainset):
                continue
            edges.append((a, b))
    return edges


POOL = []  # global pool of all visited width<=3 configs: (full_delta, ratio, p, a)


def score(ev, wdelta):
    """Weighted Pareto objective: ratio - wdelta*full_delta, hard-penalize width>3."""
    if ev is None:
        return -1e9
    s = ev['ratio'] - wdelta * ev['full_delta']
    if ev['width'] > 3:
        s -= 100 * (ev['width'] - 3)
    return s


def anneal(n, p, seed, wdelta, iters=1500, T0=1.5):
    rng = random.Random(seed)
    x = n - 1
    chain = tuple(range(p))
    edges = candidate_edges(n, x, chain)
    cur = set()
    for e in edges:
        if rng.random() < 0.12:
            cur.add(e)
    ev = evaluate(n, x, chain, cur)
    cur_s = score(ev, wdelta)
    best = (cur_s, set(cur), ev)
    for it in range(iters):
        T = T0 * (1 - it / iters) + 0.01
        e = rng.choice(edges)
        new = set(cur)
        if e in new:
            new.discard(e)
        else:
            new.add(e)
        ev2 = evaluate(n, x, chain, new)
        s2 = score(ev2, wdelta)
        if ev2 is not None and ev2['width'] <= 3:
            POOL.append((ev2['full_delta'], ev2['ratio'], p, tuple(round(v, 3) for v in ev2['a'])))
        if s2 >= cur_s or rng.random() < math.exp((s2 - cur_s) / T):
            cur, cur_s, ev = new, s2, ev2
            if ev2 is not None and s2 > best[0]:
                best = (s2, set(new), ev2)
    return best


def main():
    print("=== Pareto frontier scan over width<=3 posets (fixed x + forced chain C) ===")
    WEIGHTS = [0.0, 2.0, 5.0, 10.0, 20.0, 50.0]
    for p in (3, 4, 5, 6, 7):
        n = p + 5  # 5 scaffold elements for gates
        for w in WEIGHTS:
            nseeds = 18
            for seed in range(nseeds):
                anneal(n, p, seed * 100 + int(w), w, iters=1000)
    # Now extract frontier from POOL
    print(f"pool size (width<=3 configs visited): {len(POOL)}")
    import collections
    byp = collections.defaultdict(list)
    for (fd, ratio, p, a) in POOL:
        byp[p].append((fd, ratio, a))
    print("\n=== For each p: max ratio among STRICTLY FROZEN (delta<1/3), and min delta among ratio>=3 ===")
    for p in sorted(byp):
        rows = byp[p]
        frozen = [(r, fd, a) for (fd, r, a) in rows if fd < 1/3 - 1e-9]
        bc = [(fd, r, a) for (fd, r, a) in rows if r >= 3.0]
        maxr_frozen = max(frozen, key=lambda t: t[0]) if frozen else None
        mind_bc = min(bc, key=lambda t: t[0]) if bc else None
        print(f"\n--- p={p} ---")
        if maxr_frozen:
            print(f"  strictly-frozen max ratio = {maxr_frozen[0]:.3f} at delta={maxr_frozen[1]:.4f} a={list(maxr_frozen[2])}")
        else:
            print(f"  NO strictly-frozen (delta<1/3) width-3 config visited")
        if mind_bc:
            print(f"  block-cross (ratio>=3) MIN delta = {mind_bc[0]:.4f} (ratio={mind_bc[1]:.3f}) a={list(mind_bc[2])}")
        else:
            maxr = max(rows, key=lambda t: t[1])
            print(f"  no ratio>=3 config; max ratio seen = {maxr[1]:.3f} at delta={maxr[0]:.4f}")
    # Global Pareto: for delta thresholds, best ratio
    print("\n=== GLOBAL: best ratio achievable at or below each delta threshold (width<=3) ===")
    for thr in [0.30, 0.32, 0.333, 0.34, 0.36, 0.38, 0.40, 0.45, 0.50]:
        cand = [r for (fd, r, p, a) in POOL if fd <= thr + 1e-12]
        if cand:
            print(f"  delta<={thr:.3f}: max ratio = {max(cand):.3f}")
        else:
            print(f"  delta<={thr:.3f}: (none)")


if __name__ == "__main__":
    main()
