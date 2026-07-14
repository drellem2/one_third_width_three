#!/usr/bin/env python3
"""mg-9de3 hunt5: TARGETED two-lobe gadgets aimed at breaking delta<1/3 with a
block-crossing (ratio>>2) chain. The genuine bimodal mechanism needs a "switch"
that drags the whole incomparable chain C to one side of x. We try designs where
the switch is a second structure, and we SCALE p to see whether the achievable
delta approaches 1/3 from above (barrier real) or dips below (refutation).

All designs kept at width<=3; every reported config is re-verified: width (max
antichain), full-delta over ALL incomparable pairs, and ratio.
"""
import sys, itertools
from fractions import Fraction
sys.path.insert(0, "scripts")
from onethird_mgb0a6_spectral_killshot_probe import Poset, before_prob_dp
from onethird_mg9de3_blockcross_hunt import analyze, full_delta, width, base_pairs


def rep(name, P, x, chain):
    w = width(P)
    fd, worst = full_delta(P)
    r = analyze(P, x, chain)
    frozen = fd < 1/3 - 1e-12
    flag = ""
    if frozen and r['ratio'] > 2.5:
        flag = "   <<<<< FROZEN & ratio>2.5 REFUTATION CANDIDATE"
    elif frozen:
        flag = "   [frozen]"
    print(f"[{name}] n={P.n} p={len(chain)} width={w} delta={fd:.4f} ratio={r['ratio']:.3f} "
          f"j={r['j']} frozen={frozen}{flag}")
    print(f"     a={[f'{v:.3f}' for v in r['a']]}  worstpair={worst}")
    return dict(n=P.n, p=len(chain), width=w, delta=fd, ratio=r['ratio'], frozen=frozen)


# ---- Design 1: x with down-CHAIN D and up-CHAIN U, plus incomparable chain C
#      where C is coupled to a single "switch" element s that is below U-bottom and
#      above D-top, creating a narrow window that flips. ----
def design_gate_switch(p, dlen, ulen):
    """Elements: chain C = 0..p-1. x = p. down-chain D = p+1..p+dlen (D chain, top=D_last<x).
    up-chain U = next ulen (bottom=U_first, x<U_first). Keep width<=3."""
    n = p + 1 + dlen + ulen
    C = tuple(range(p))
    x = p
    D = list(range(p + 1, p + 1 + dlen))
    U = list(range(p + 1 + dlen, p + 1 + dlen + ulen))
    pairs = [(C[i], C[i + 1]) for i in range(p - 1)]
    pairs += [(D[i], D[i + 1]) for i in range(dlen - 1)]
    pairs += [(U[i], U[i + 1]) for i in range(ulen - 1)]
    pairs.append((D[-1], x))   # D below x
    pairs.append((x, U[0]))    # x below U
    # couple chain to gate: chain sits between D and U as a block
    pairs.append((D[-1], C[0]))   # D below chain
    pairs.append((C[-1], U[0]))   # chain below U
    return Poset(n, pairs), x, C


# ---- Design 2: two parallel incomparable chains C and C' (both incomparable to x
#      and to each other), sharing a common down gate d and up gate u. The two chains
#      co-move because they share the same window. slot_C may be bimodal if C' pushes. ----
def design_twin_chains(p, q):
    """C = 0..p-1, C' = p..p+q-1, x = p+q, d = next, u = next.
    d<x<u, d<C[0], d<C'[0], C[-1]<u, C'[-1]<u.  C,C' incomparable to each other and x."""
    n = p + q + 3
    C = tuple(range(p))
    Cp = tuple(range(p, p + q))
    x = p + q
    d = p + q + 1
    u = p + q + 2
    pairs = [(C[i], C[i + 1]) for i in range(p - 1)]
    pairs += [(Cp[i], Cp[i + 1]) for i in range(q - 1)]
    pairs += [(d, x), (x, u), (d, C[0]), (d, Cp[0]), (C[-1], u), (Cp[-1], u)]
    return Poset(n, pairs), x, C


# ---- Design 3: "reflected coupling" — x above a bottom b and below a top t; the chain
#      C is incomparable to x but c_1 is forced above b and c_p below t, AND a switch
#      element w (incomparable to x) sits so that when w is low, C is dragged low. ----
def design_switch_chain(p):
    """C=0..p-1, x=p, b=p+1(bottom<x), t=p+2(top>x), w=p+3 (switch, incomp x).
    b<w, w<t. b<C[0], C[-1]<t. w incomparable to all C? then {x,w,c} antichain=3."""
    n = p + 4
    C = tuple(range(p))
    x = p; b = p + 1; t = p + 2; w = p + 3
    pairs = [(C[i], C[i + 1]) for i in range(p - 1)]
    pairs += [(b, x), (x, t), (b, w), (w, t), (b, C[0]), (C[-1], t)]
    return Poset(n, pairs), x, C


def design_freebias(p, g, h):
    """x with down-chain of length g and up-chain of length h; chain C incomparable to
    EVERYTHING (fully free). Sweeping g,h biases x's rank -> shows frozen<=>unimodal."""
    n = p + 1 + g + h
    C = tuple(range(p))
    x = p
    D = list(range(p + 1, p + 1 + g))
    U = list(range(p + 1 + g, p + 1 + g + h))
    pairs = [(C[i], C[i + 1]) for i in range(p - 1)]
    pairs += [(D[i], D[i + 1]) for i in range(g - 1)]
    pairs += [(U[i], U[i + 1]) for i in range(h - 1)]
    if g:
        pairs.append((D[-1], x))
    if h:
        pairs.append((x, U[0]))
    return Poset(n, pairs), x, C


def tradeoff_sweep():
    print("=== TRADEOFF SWEEP: x biased by down/up gates, chain C fully free ===")
    print("    (shows: as delta drops below ~1/2 toward frozen, slot becomes UNIMODAL, ratio drops)")
    for p in (5, 7, 9):
        print(f"  -- p={p} --")
        for (g, h) in [(0, 0), (2, 0), (4, 0), (6, 0), (p, 0), (2 * p, 0), (p, 1), (2 * p, 2)]:
            P, x, C = design_freebias(p, g, h)
            if width(P) > 3:
                continue
            fd, _ = full_delta(P)
            r = analyze(P, x, C)
            fr = "FROZEN" if fd < 1/3 - 1e-12 else "      "
            print(f"    g={g:2d} h={h:2d} n={P.n:2d} delta={fd:.4f} {fr} ratio={r['ratio']:.3f} "
                  f"j={r['j']} a0={r['a'][0]:.3f} ap={r['a'][-1]:.3f}")


if __name__ == "__main__":
    tradeoff_sweep()
    print()
    print("=== Design 1: gate + chain-as-block between D and U (should be UNIMODAL) ===")
    for p in (3, 5, 7):
        for (d, u) in [(1, 1), (2, 2), (3, 1)]:
            rep(f"gate d={d} u={u}", *design_gate_switch(p, d, u))
    print("\n=== Design 2: twin parallel incomparable chains sharing a gate ===")
    for p in (3, 4, 5):
        for q in (2, 3, 4):
            rep(f"twin q={q}", *design_twin_chains(p, q))
    print("\n=== Design 3: single switch element w dragging chain C ===")
    for p in (3, 4, 5, 6):
        rep("switch", *design_switch_chain(p))
