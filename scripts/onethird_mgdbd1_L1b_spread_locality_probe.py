#!/usr/bin/env python3
"""OneThird mg-dbd1: close L1b via the mg-8201 expected-rank certificate ---
prove/wall (A) SPREAD  ||r||^2 = Omega(n^3)  and  (B) LOCALITY  E[sum disp^2] = O(E[inv_e]).

Ticket: mg-dbd1 (high, repo one_third_width_three). Spectral / near-ordinal-sum
program ONLY (Cech / F-series ignored per Daniel). Reuses the mg-b0a6 engine and
the mg-8201 certificate (docs/OneThird-L1b-ExpectedRank-Certificate.md); it does
NOT re-derive the certificate. LaTeX-first: this script only supplies the
numerical CHECKS behind the proof of (A) and the WALL diagnosis of (B); the proof
lives in docs/OneThird-L1b-Spread-Locality.md.

WHAT IT CHECKS
  1. IDENTITY (star):  E[sum_x disp(x)^2] = 2 E[inv_e]
                        + sum_x sum_{y!=z} eps_xy eps_xz E[I_xy I_xz],
     the exact decomposition that localises the LOCALITY lemma (B) to a
     same-element inversion-CORRELATION term.  disp(x)=pos_sigma(x)-erank(x),
     I_xy = 1 iff pair {x,y} is e-inverted in sigma, eps_xy = sign(erank(y)-erank(x)).
  2. SPREAD band (proof of A):  with e-rank k in 0..n-1 and d_k = E[pos] of the
     e-rank-k element,   (2/3) k  <=  d_k  <=  (2/3) k + (n-1)/3   (frozen).
     -> ||r||^2 = sum_k (d_k-(n-1)/2)^2 >= (n-1)^3 / 1152 = Omega(n^3).
     We verify the band holds on every frozen poset in reach and report ||r||^2/n^3.
  3. LOCALITY ratio  E[sum disp^2]/E[inv_e], max_x m_x (expected inversion degree),
     d_1 = E[pos(e-min)], max|disp|, on:
       - the tight3 = a||(b<c) ordinal-sum tower (the only reachable frozen family;
         delta=1/3 boundary, THIN);
       - targeted "x crosses a frozen chain" constructions (the ticket's named (B)
         falsifier mechanism);
       - a random width-3 search filtered to strictly-frozen delta<1/3.

KEY REACH LIMITATION (honest).  Exact linear-extension enumeration is O(n!), so
brute reach is n<=9 -- exactly the range in which mg-8201 could not exhibit a
quadratic-E[inv_e] frozen poset.  Worse, strictly-frozen (delta<1/3) width-3
both-connected posets are so rare that 20000 random dense trials at n<=9 produced
ZERO.  The quadratic-E[inv_e] regime where (B)'s correlation term could blow up is
therefore DOUBLY out of empirical reach; (B) is walled, not settled, here.
"""
from __future__ import annotations
import sys, itertools, random
sys.path.insert(0, "scripts")
import numpy as np
from onethird_mgb0a6_spectral_killshot_probe import Poset


def _posn(P):
    les = P.linear_extensions()
    L = len(les); n = P.n
    posn = np.zeros((L, n), dtype=np.int32)
    for s, perm in enumerate(les):
        for a, x in enumerate(perm):
            posn[s, x] = a
    return posn, L


def analyze(P, name, cap=300_000):
    n = P.n
    if P.linext_count() > cap:
        return dict(name=name, n=n, skip=True, L=P.linext_count())
    posn, L = _posn(P)
    B = (posn[:, :, None] < posn[:, None, :]).mean(0)     # B[x,y]=Pr[x before y]
    er = B.sum(0)                                         # E[pos(x)], 0-indexed
    e_order = sorted(range(n), key=lambda x: (er[x], x))
    erank = np.zeros(n, dtype=int)
    for i, x in enumerate(e_order):
        erank[x] = i
    incomp = list(P.incomparable_pairs())
    einv = 0.0; deltas = []; q = np.zeros((n, n))
    for (x, y) in incomp:
        p = B[x, y]; deltas.append(min(p, 1 - p))
        hi, lo = (x, y) if erank[x] > erank[y] else (y, x)
        wp = B[hi, lo]; einv += wp; q[x, y] = wp; q[y, x] = wp
    delta = max(deltas) if deltas else 0.0
    disp = posn - erank[None, :]
    sd2 = float((disp.astype(float) ** 2).sum(1).mean())
    m = q.sum(1); r = er - er.mean(); Edisp = er - erank
    band_ok = bool(np.all(((2/3) * erank - 1e-9 <= er) &
                          (er <= (2/3) * erank + (n - 1) / 3 + 1e-9)))
    return dict(name=name, n=n, L=L, delta=delta, E_inv=einv, E_sumdisp2=sd2,
                ratio=(sd2 / einv if einv > 1e-12 else None),
                rn2_over_n3=float(r @ r) / n ** 3, max_m=float(m.max()),
                max_absdisp=int(np.abs(disp).max()),
                max_absEdisp=float(np.abs(Edisp).max()), d1=float(er.min()),
                band_ok=band_ok, num_incomp=len(incomp), Einv_over_n=einv / n)


def check_identity(P):
    """Verify (star): E[sum disp^2] = 2 E[inv] + cross.  Returns (lhs,rhs,einv)."""
    n = P.n; posn, L = _posn(P)
    B = (posn[:, :, None] < posn[:, None, :]).mean(0)
    er = B.sum(0)
    e_order = sorted(range(n), key=lambda x: (er[x], x))
    erank = np.zeros(n, dtype=int)
    for i, x in enumerate(e_order):
        erank[x] = i
    disp = posn - erank[None, :]
    lhs = float((disp.astype(float) ** 2).sum(1).mean())
    einv = 0.0
    for x in range(n):
        for y in range(x + 1, n):
            if not P.comparable(x, y):
                hi, lo = (x, y) if erank[x] > erank[y] else (y, x)
                einv += B[hi, lo]
    I = np.zeros((L, n, n))                     # I[s,x,y]=1 iff {x,y} e-inverted in sigma_s
    for x in range(n):
        for y in range(n):
            if x == y:
                continue
            hi, lo = (x, y) if erank[x] > erank[y] else (y, x)
            I[:, x, y] = (posn[:, hi] < posn[:, lo]).astype(float)
    eps = np.sign(erank[None, :] - erank[:, None])
    cross = 0.0
    for x in range(n):
        for y in range(n):
            if y == x:
                continue
            for z in range(n):
                if z == x or z == y:
                    continue
                cross += eps[x, y] * eps[x, z] * float((I[:, x, y] * I[:, x, z]).mean())
    return lhs, 2 * einv + cross, einv


def tight3_osum(m):
    """Ordinal sum of m copies of tight3 = a||(b<c). delta=1/3, THIN, width 3.
    #LE = 3^m, so reachable to large m WITHOUT n! blowup only because #LE is tiny."""
    pairs = []
    for k in range(m):
        pairs.append((3 * k + 1, 3 * k + 2))
    for k in range(m):
        for j in range(k + 1, m):
            for a in range(3):
                for b in range(3):
                    pairs.append((3 * k + a, 3 * j + b))
    return Poset(3 * m, pairs)


def x_crosses_chain(p, mode):
    """Attempt the (B) falsifier: e-min x=0 frozen before an incomparable chain
    Y=1..p while occasionally trailing it. mode 'a'=cap above all; 'c'=shadow chain."""
    pairs = [(i, i + 1) for i in range(1, p)]
    if mode == "a":
        n = p + 2; t = p + 1
        for y in range(1, p + 1):
            pairs.append((y, t))
        pairs.append((0, t))
    elif mode == "c":
        n = 2 * p + 1
        W = list(range(p + 1, 2 * p + 1))
        for i in range(p - 1):
            pairs.append((W[i], W[i + 1]))
        for a in range(p):
            pairs.append((W[a], a + 1))
        pairs.append((0, W[0]))
    return Poset(n, pairs)


def width_le3(P):
    for S in itertools.combinations(range(P.n), 4):
        if all(not P.comparable(a, b) for a, b in itertools.combinations(S, 2)):
            return False
    return True


def rand_w3(n, rng, pc):
    chains = [[e for e in range(n) if e % 3 == c] for c in range(3)]
    pairs = []
    for ch in chains:
        for i in range(len(ch) - 1):
            pairs.append((ch[i], ch[i + 1]))
    for a in range(n):
        for b in range(a + 1, n):
            if a % 3 == b % 3:
                continue
            if rng.random() < pc:
                pairs.append((a, b))
    try:
        return Poset(n, pairs)
    except ValueError:
        return None


def _pr(r):
    if r.get("skip"):
        print(f"  {r['name']:16s} n={r['n']:2d} SKIP L={r['L']}"); return
    print(f"  {r['name']:16s} n={r['n']:2d} d={r['delta']:.3f} #inc={r['num_incomp']:2d} "
          f"Einv={r['E_inv']:5.2f}(/n={r['Einv_over_n']:.2f}) ratio={r['ratio']:.3f} "
          f"maxm={r['max_m']:.2f} maxdisp={r['max_absdisp']} d1={r['d1']:.2f} "
          f"rn2/n3={r['rn2_over_n3']:.4f} bnd={r['band_ok']}", flush=True)


def main():
    print("=== 1. IDENTITY (star): E[sum disp^2] = 2 E[inv] + cross ===")
    for pairs, n in [([(1, 2)], 3), ([(0, 2), (1, 3)], 4),
                     ([(1, 2), (3, 4), (0, 3)], 5)]:
        l, r, e = check_identity(Poset(n, pairs))
        print(f"  n={n}: lhs={l:.6f} rhs={r:.6f} match={abs(l-r)<1e-9} E[inv]={e:.4f}")

    # brute LE is O(n!), so the tower is only computed here to n<=9 (m<=3); the
    # large-n tower asymptotics (||r||^2/n^3 -> 1/12, ratio -> 2, E[inv]=2n/9) are
    # in mg-8201's data via its block-diagonal analyze_osum (no n! blowup).
    print("=== 2+3. tight3 ordinal-sum tower to n<=9 (THIN; see mg-8201 for n->36) ===")
    for m in range(1, 4):
        _pr(analyze(tight3_osum(m), f"tight3^{m}"))

    print("=== targeted x-crosses-chain (named (B) falsifier mechanism) ===")
    for p in range(2, 7):
        for mode in ("a", "c"):
            P = x_crosses_chain(p, mode)
            if not width_le3(P):
                print(f"  xchain-p{p}-{mode}: WIDTH>3"); continue
            _pr(analyze(P, f"xchain-p{p}-{mode}"))

    print("=== strictly-frozen (delta<1/3) width-3 random search, n<=9 ===")
    rng = random.Random(7); frozen = []; tested = 0
    for _ in range(20000):
        n = rng.choice([6, 7, 8, 9])
        P = rand_w3(n, rng, rng.uniform(0.45, 0.9))
        if P is None or not P.both_connected():
            continue
        if P.linext_count() > 30000:
            continue
        tested += 1
        r = analyze(P, f"n{n}")
        if r.get("skip") or r["num_incomp"] == 0:
            continue
        if r["delta"] < 1/3 - 1e-9:
            frozen.append(r)
    print(f"  tested {tested}; found {len(frozen)} strictly-frozen width-3 posets")
    if frozen:
        ratios = [f["ratio"] for f in frozen if f["ratio"]]
        print(f"  ratio median={np.median(ratios):.3f} max={np.max(ratios):.3f}; "
              f"max_m={max(f['max_m'] for f in frozen):.2f}; "
              f"d1={max(f['d1'] for f in frozen):.2f}; "
              f"band_ok all={all(f['band_ok'] for f in frozen)}")


if __name__ == "__main__":
    main()
