#!/usr/bin/env python3
"""mg-9de3 hunt6: the SHARP per-chain test at larger n. For every FROZEN CHAIN
(all x-vs-c pairs have min-prob<1/3) in random width-<=3 posets up to n=14, record
ratio E[S^2]/E|S| vs chain length p. Fact 2 (proven+verified) says frozen chain =>
a_j>1/3, which should cap the ratio. We test whether max frozen-chain ratio grows
with p (block-cross realizable) or saturates (barrier). Also tracks the WHOLE-POSET
frozen (delta<1/3) case separately, and the min whole-poset-delta for ratio>=3.
"""
import sys, random, collections
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp
from onethird_mg9de3_blockcross_hunt import analyze, full_delta
from onethird_mg9de3_blockcross_hunt4 import gen_poset, has_antichain4, maximal_inc_chains


def main():
    rng = random.Random(424242)
    # per-chain-frozen: p -> max ratio
    chain_frozen_maxratio = collections.defaultdict(float)
    chain_frozen_witness = {}
    # whole-poset-frozen (delta<1/3): p -> max ratio
    poset_frozen_maxratio = collections.defaultdict(float)
    poset_frozen_count = 0
    # min whole-poset delta among ratio>=3
    min_delta_bc = [1e9, None]
    global_max_chainfrozen = [0.0, None]
    n_scanned = 0
    TARGET = 200000
    for trial in range(TARGET):
        n = rng.choice([9, 10, 11, 12, 13, 14])
        rho = rng.choice([0.45, 0.52, 0.60, 0.68])  # denser -> more frozen, lower width
        P = gen_poset(n, rho, rng)
        if has_antichain4(P):
            continue
        n_scanned += 1
        fd = None
        for x in range(n):
            for chain in maximal_inc_chains(P, x):
                p = len(chain)
                r = analyze(P, x, chain)
                ratio = r['ratio']
                biases = [1 - before_prob_dp(P, x, c) for c in chain]
                dchain = float(max(min(b, 1 - b) for b in biases))
                if dchain < 1/3 - 1e-12:  # FROZEN CHAIN
                    if ratio > chain_frozen_maxratio[p]:
                        chain_frozen_maxratio[p] = ratio
                        chain_frozen_witness[p] = (dchain, r['j'], r['a'], n)
                    if ratio > global_max_chainfrozen[0]:
                        global_max_chainfrozen = [ratio, (p, dchain, n, r['a'])]
                if ratio >= 3.0:
                    if fd is None:
                        fd = full_delta(P)[0]
                    if fd < min_delta_bc[0]:
                        min_delta_bc = [fd, (ratio, p, n, r['a'])]
                    if fd < 1/3 - 1e-12:
                        if ratio > poset_frozen_maxratio[p]:
                            poset_frozen_maxratio[p] = ratio
                        poset_frozen_count += 1
        if (trial + 1) % 50000 == 0:
            print(f"...{trial+1} trials, {n_scanned} width<=3; global max frozen-CHAIN ratio="
                  f"{global_max_chainfrozen[0]:.3f}", flush=True)
    print(f"\nTotal width<=3 posets scanned: {n_scanned}")
    print("\n=== MAX ratio over FROZEN CHAINS (all x-vs-c pairs<1/3), by chain length p ===")
    print("    (Fact 2: frozen chain => a_j>1/3; test if ratio grows with p)")
    for p in sorted(chain_frozen_maxratio):
        r = chain_frozen_maxratio[p]
        w = chain_frozen_witness[p]
        print(f"  p={p}: max ratio={r:.3f}  (dchain={w[0]:.4f}, j={w[1]}, n={w[3]}) a={[f'{v:.2f}' for v in w[2]]}")
    print(f"\nGlobal max frozen-CHAIN ratio = {global_max_chainfrozen[0]:.3f} at {global_max_chainfrozen[1]}")
    print("\n=== WHOLE-POSET frozen (delta<1/3) with ratio>=3 ===")
    if poset_frozen_maxratio:
        for p in sorted(poset_frozen_maxratio):
            print(f"  p={p}: max ratio={poset_frozen_maxratio[p]:.3f}")
    else:
        print("  NONE found (no width-3 poset with delta<1/3 had a ratio>=3 chain).")
    if min_delta_bc[1]:
        print(f"\nMIN whole-poset delta among ratio>=3 configs: {min_delta_bc[0]:.4f} "
              f"(ratio={min_delta_bc[1][0]:.3f}, p={min_delta_bc[1][1]}, n={min_delta_bc[1][2]})")


if __name__ == "__main__":
    main()
