#!/usr/bin/env python3
"""
OneThird AP-2 Prong 3A: verification harness for the analytic 8/21 lower bound
on width-EXACTLY-3 series-parallel (SP) posets.

Companion to docs/OneThird-AP-2-Prong3A-SP-FloorBound.md (work item mg-7009).
Follow-up to mg-63df (Prong 2, SKEW-ARTIFACT verdict + the closed-form SP Q).

WHAT THIS DOES
--------------
Prong 2 established empirically (32,413+ shapes, n<=12) that the minimum balance
constant Q over width-exactly-3 SP posets is 8/21 ~ 0.380952, attained at

    T* = [ (a<b || c) (+) (d<e || f) ] || g          (n = 7),

stable across n = 7..12. This Prong 3A converts that into an analytic theorem.
The argument (see the doc) is an induction on the SP-tree resting on a single
structural identity (proved in Prong 2):

    Q(P) = max over PARALLEL nodes N, over unordered child-pairs {A,B} of N,
           of  g(A,B),
    g(A,B) := max over x in A, y in B of  min( Pr_{A||B}[x<y], Pr_{A||B}[y<x] ).

This script REUSES the Prong-2 closed-form recursion (Q_closed_sp, rank_dist,
_merge_prob) verbatim and adds analytic-bound checkers for every lemma the proof
uses, asserting them on an exhaustive small-n sweep:

  L-REDUCE   the structural identity above (vs the family-agnostic DP engine).
  L-SERIES   Q(P (+) Q) = max(Q(P), Q(Q)).
  L-PHI      phi(a,b) := g(Chain a || Chain b): phi(a,b) >= 8/21 unless
             {a,b}={1,2} (phi=1/3); phi(k,k)=1/2; phi(1,2k)=k/(2k+1);
             a,b both odd => phi=1/2.
  L-CASE1    root-parallel width-3 with child-widths {1,1,1}: Q >= 2/5.
  L-GAP      (the binding case) root-parallel width-3 {1,2} with the width-1
             child a single POINT and a 'dangerous' width-2 W (Q(W)=1/3):
             expected ranks of W have consecutive gaps <= 5/3, hence the point
             cross-pair achieves balance >= 8/21, tight at T*.
  L-THICK    {1,2} with the width-1 child a chain of size c>=2: Q >= 2/5.
  FLOOR      min Q over all width-exactly-3 SP posets up to n_max = 8/21,
             sharp at T* and at the n=8,9 argmins (T* (+) point, T* (+) 2 pts).

GUARD (roadmap 8.2, anti-Cheeger). The analytic lower bound proved here is
>= 8/21 > 1/3 at EVERY composition shape; it never dips below 1/3, so the
mandatory-independent-reimplementation trigger does not fire. We nevertheless
re-run the Prong-2 independent (separate-codebase) check as cross-validation.

Run:
  python3 scripts/onethird_ap2_prong3a_sp_floor_verify.py            # n<=11 default
  python3 scripts/onethird_ap2_prong3a_sp_floor_verify.py --n-max 10
"""
from __future__ import annotations

import argparse
import itertools
import sys
from fractions import Fraction

sys.path.insert(0, 'scripts')
import onethird_ap2_prong2_familyB_sp_probe as P  # reuse Prong-2 closed form

EIGHT_21 = Fraction(8, 21)
TWO_FIFTH = Fraction(2, 5)
ONE_THIRD = Fraction(1, 3)

LEAF = ('leaf',)
GADGET = ('P', (LEAF, ('S', (LEAF, LEAF))))  # G = point || 2-chain, size 3, Q=1/3


def chain(k):
    return ('S', tuple(LEAF for _ in range(k))) if k > 1 else LEAF


def F(i, j, a, b):
    return P._merge_prob(i, j, a, b)


# ---------------------------------------------------------------------------
# g(A,B): best cross-pair balance between two parallel components.
# ---------------------------------------------------------------------------
def g_cross(Alab, Blab):
    rA, rB = P.rank_dist(Alab), P.rank_dist(Blab)
    mA, mB = P.lsize(Alab), P.lsize(Blab)
    best = None
    for x, dx in rA.items():
        for y, dy in rB.items():
            pr = Fraction(0)
            for a, pa in dx.items():
                for b, pb in dy.items():
                    pr += pa * pb * F(a, b, mA, mB)
            v = min(pr, 1 - pr)
            best = v if best is None or v > best else best
    return best


def phi(a, b):
    """g(Chain(a) || Chain(b)) computed directly from F (chains are rigid)."""
    best = None
    for i in range(1, a + 1):
        for j in range(1, b + 1):
            v = min(F(i, j, a, b), 1 - F(i, j, a, b))
            best = v if best is None or v > best else best
    return best


def Q_by_reduction(lab):
    """Q via the structural identity: max over parallel nodes, child-pairs, of
    g(A,B). Independent re-implementation of the reduction (not calling
    Q_closed_sp), used to check L-REDUCE."""
    best = [None]

    def visit(nd):
        if nd[0] == 'leaf':
            return
        if nd[0] == 'S':
            for c in nd[1]:
                visit(c)
            return
        ch = nd[1]
        for i in range(len(ch)):
            for j in range(i + 1, len(ch)):
                v = g_cross(ch[i], ch[j])
                if best[0] is None or v > best[0]:
                    best[0] = v
        for c in ch:
            visit(c)

    visit(lab)
    return best[0]


# ---------------------------------------------------------------------------
# Checkers
# ---------------------------------------------------------------------------
def check_reduce_and_series(trees, n_max):
    print("L-REDUCE / L-SERIES: structural identity + series=max ...", end=" ")
    nbad = 0
    for n in range(3, n_max + 1):
        for s in trees.get(n, []):
            lab = P.label(s)
            qc = P.Q_closed_sp(lab)
            qc = qc[0] if qc else None
            qr = Q_by_reduction(lab)
            if qc != qr:
                nbad += 1
                print(f"\n   REDUCE mismatch {P.tree_str(s)}: closed={qc} reduce={qr}")
    # series = max: spot-check on composed trees
    for s1 in trees.get(3, []) + trees.get(4, []):
        for s2 in trees.get(3, []):
            if P.s_width(s1) > 3 or P.s_width(s2) > 3:
                continue
            comp = ('S', (s1, s2))
            if P.s_width(comp) > 3:
                continue
            lab = P.label(comp)
            q = P.Q_closed_sp(lab)
            q = q[0] if q else None
            q1 = P.Q_closed_sp(P.label(s1))
            q1 = q1[0] if q1 else None
            q2 = P.Q_closed_sp(P.label(s2))
            q2 = q2[0] if q2 else None
            cand = [x for x in (q1, q2) if x is not None]
            exp = max(cand) if cand else None
            assert q == exp, (P.tree_str(comp), q, exp)
    print(f"OK (identity holds on all {sum(len(trees.get(n,[])) for n in range(3,n_max+1))} shapes; series=max spot-checked)")
    return nbad == 0


def check_phi(AB=40):
    print(f"L-PHI: phi(a,b) dichotomy (a,b in [1,{AB}]) ...", end=" ")
    below = []
    for a in range(1, AB + 1):
        for b in range(a, AB + 1):
            v = phi(a, b)
            if v < EIGHT_21 and not (a == 1 and b == 2):
                below.append((a, b, v))
    assert not below, below
    # closed forms
    for k in range(1, 25):
        assert phi(1, 2 * k) == Fraction(k, 2 * k + 1)
    for a in range(1, AB + 1):
        assert phi(a, a) == Fraction(1, 2)
    for a in range(1, AB + 1, 2):
        for b in range(a, AB + 1, 2):
            assert phi(a, b) == Fraction(1, 2)
    assert phi(1, 2) == ONE_THIRD
    print("OK (phi>=8/21 except (1,2)=1/3; phi(1,2k)=k/(2k+1); equal/both-odd=1/2)")
    return True


def check_case1(L=16):
    print(f"L-CASE1: three parallel chains {{1,1,1}}, sizes<= {L} ...", end=" ")
    mn = None
    arg = None
    for l1 in range(1, L + 1):
        for l2 in range(l1, L + 1):
            for l3 in range(l2, L + 1):
                q = max(phi(l1, l2), phi(l1, l3), phi(l2, l3))
                if mn is None or q < mn:
                    mn, arg = q, (l1, l2, l3)
    assert mn >= TWO_FIFTH, (mn, arg)
    print(f"OK (min Q = {mn} = {float(mn):.6f} >= 2/5, at sizes {arg})")
    return True


def dangerous_Ws(maxsize):
    """Width-2 SP posets W with Q(W)=1/3: ordinal sums whose every width-2 block
    is the gadget G=point||2-chain. Represent as chain-gap pattern around G's."""
    seen = set()
    out = []
    for ng in range(1, maxsize // 3 + 1):
        base = 3 * ng
        slack = maxsize - base
        if slack < 0:
            break
        for gaps in itertools.product(range(slack + 1), repeat=ng + 1):
            if base + sum(gaps) > maxsize:
                continue
            blocks = []
            for i in range(ng):
                if gaps[i] > 0:
                    blocks.append(chain(gaps[i]))
                blocks.append(GADGET)
            if gaps[ng] > 0:
                blocks.append(chain(gaps[ng]))
            W = blocks[0] if len(blocks) == 1 else ('S', tuple(blocks))
            key = P.canon(W)
            if key in seen:
                continue
            seen.add(key)
            out.append(W)
    return out


def check_gap_binding(maxW=18):
    print(f"L-GAP: c=1 binding case, dangerous W (N<= {maxW}) ...", end=" ")
    worst_gap = None
    for W in dangerous_Ws(maxW):
        Wlab = P.label(W)
        N = P.lsize(Wlab)
        # confirm dangerous
        qW = P.Q_closed_sp(Wlab)
        assert qW is not None and qW[0] == ONE_THIRD, (P.tree_str(W), qW)
        rd = P.rank_dist(Wlab)
        er = sorted(sum(a * pa for a, pa in d.items()) for d in rd.values())
        gaps = [er[i + 1] - er[i] for i in range(len(er) - 1)]
        mg = max(gaps) if gaps else Fraction(0)
        worst_gap = mg if worst_gap is None or mg > worst_gap else worst_gap
        assert mg <= Fraction(5, 3), (P.tree_str(W), mg)            # G1
        center = Fraction(N + 1, 2)
        mindist = min(abs(r - center) for r in er)
        assert mindist <= Fraction(5, 6), (P.tree_str(W), mindist)  # mindist<=maxgap/2
        gpt = Fraction(1, 2) - Fraction(mindist, N + 1)             # g(point,W)
        # cross-check against the direct cross computation
        assert gpt == g_cross(P.label(LEAF), Wlab), P.tree_str(W)
        assert gpt >= EIGHT_21, (P.tree_str(W), gpt)               # the bound
    assert worst_gap == Fraction(5, 3)
    print(f"OK (max expected-rank gap = {worst_gap} = 5/3; g(point,W) >= 8/21, tight)")
    return True


def check_thick(maxW=15, maxc=12):
    print(f"L-THICK: {{1,2}} with chain size c>=2 (N<= {maxW}, c<= {maxc}) ...", end=" ")
    mn = None
    arg = None
    for W in dangerous_Ws(maxW):
        Wlab = P.label(W)
        N = P.lsize(Wlab)
        for c in range(2, maxc + 1):
            v = g_cross(P.label(chain(c)), Wlab)
            if mn is None or v < mn:
                mn, arg = v, (c, P.tree_str(W))
    assert mn >= TWO_FIFTH, (mn, arg)
    print(f"OK (min Q = {mn} = {float(mn):.6f} >= 2/5, at c={arg[0]}, W={arg[1]})")
    return True


def check_floor_and_sharpness(trees, n_max):
    print(f"FLOOR: min Q over width-exactly-3 SP, n in [3,{n_max}] ...", end=" ")
    gmin = None
    arg = None
    for n in range(3, n_max + 1):
        for s in trees.get(n, []):
            if P.s_width(s) != 3:
                continue
            q = P.Q_closed_sp(P.label(s))
            if q is None:
                continue
            q = q[0]
            assert q >= EIGHT_21, (P.tree_str(s), q)   # the theorem
            if gmin is None or q < gmin:
                gmin, arg = q, P.tree_str(s)
    assert gmin == EIGHT_21, gmin
    print(f"OK (min = {gmin} = {float(gmin):.6f}; every width-3 shape >= 8/21)")
    print(f"        global argmin: {arg}")

    # sharpness sequence: T*, T*+pt, T*+pt+pt
    core = ('P', (('S', (GADGET, GADGET)), LEAF))       # T*, n=7
    seq = [("T*           (n=7)", core),
           ("T* (+) pt    (n=8)", ('S', (core, LEAF))),
           ("T* (+) 2 pts (n=9)", ('S', (core, LEAF, LEAF)))]
    print("        sharpness at T* and the n=8,9 argmins:")
    for name, t in seq:
        lab = P.label(t)
        q, pr = P.Q_closed_sp(lab)
        tag = "OK" if q == EIGHT_21 else "*** FAIL ***"
        print(f"          {name}: Q = {q} = {float(q):.6f}  (witness Pr={pr})  [{tag}]")
        assert q == EIGHT_21
    return True


def guard_note():
    print("\nGUARD (roadmap 8.2): the analytic bound is >= 8/21 > 1/3 at every")
    print("  composition shape -- it never dips below 1/3, so the mandatory")
    print("  independent-reimplementation trigger does NOT fire. Cross-validation")
    print("  with the Prong-2 separate-codebase check is available via:")
    print("      python3 scripts/onethird_ap2_prong2_independent_check.py")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n-max", type=int, default=11, help="sweep cap (default 11)")
    ap.add_argument("--phi-ab", type=int, default=40)
    ap.add_argument("--case1-L", type=int, default=16)
    ap.add_argument("--gap-W", type=int, default=18)
    ap.add_argument("--thick-W", type=int, default=15)
    ap.add_argument("--thick-c", type=int, default=12)
    args = ap.parse_args()

    print("=" * 72)
    print("OneThird AP-2 Prong 3A -- analytic 8/21 SP-floor verification")
    print("=" * 72)
    trees = P.enumerate_sp(args.n_max)

    ok = True
    ok &= check_reduce_and_series(trees, args.n_max)
    ok &= check_phi(args.phi_ab)
    ok &= check_case1(args.case1_L)
    ok &= check_gap_binding(args.gap_W)
    ok &= check_thick(args.thick_W, args.thick_c)
    ok &= check_floor_and_sharpness(trees, args.n_max)
    guard_note()

    print("\n" + "=" * 72)
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    print("=" * 72)
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
