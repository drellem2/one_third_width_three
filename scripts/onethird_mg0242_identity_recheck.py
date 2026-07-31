#!/usr/bin/env python3
"""mg-0242 — independent re-run of the identities and closed forms mg-069f preserves.

WHY A THIRD IMPLEMENTATION.  The verdict names these as the checks that
"distinguish a corrected sentence from a differently-wrong one, and no direction
check can see them".  Re-running mg-8a71's instrument would test that its code
still runs, not that its answers are right.  This is written from the DEFINITIONS
in OneThird-L1b-Spread-Locality.md §0/§2.3 alone -- its own poset enumerator, its
own linear-extension generator, its own inversion bookkeeping -- and it shares no
line with either existing script.  Where it agrees, the agreement is evidence.

WHAT IT CHECKS.

  (I)  (F1)  Sum_x m_x = 2 E[inv_e]
       exact, on the FULL labelled population: 4 469 posets on n = 3,4,5,
       43 842 (poset, reference-order) pairs, 218 166 element triples.

  (II) (star) E[Sum_x disp^2] = 2 E[inv_e] + Cross
       The content of (star) is a DECOMPOSITION, not a number: disp_sigma(x) is a
       signed sum of the pair-inversion indicators involving x, so the diagonal of
       its square is the inversion degree and the off-diagonal is Cross.  Checked
       as the three statements it factors into, per (poset, e, sigma), on all
       43 842 pairs:
           (a) disp_sigma(x) = A_x - B_x
           (b) A_x + B_x = #{y != x : the pair {x,y} is inverted in sigma vs e}
           (c) Sum_x (A_x + B_x) = 2 * inv_sigma(e)             [handshake]
       and then, so that the DEFINITION of Cross is checked too and not just the
       bookkeeping, Cross is recomputed on n = 3,4 from its own double sum
           Cross = Sum_x Sum_{y != z} eps_xy eps_xz E[I_xy I_xz]
       and compared against E[Sum disp^2] - 2E[inv_e].

  (III) The four W_m closed forms, recomputed from L(W_m) by enumeration:
           m_z = E[inv_e] = s(s+1)/(2s+1)
           Sum_x b_x^2   = s(s+1)/(3(2s+1))
           ratio         = 1/3          EXACTLY, every even m
           Var(pos_sigma z) = ((m+1)^2 - 1)/12 = m(m+2)/12
       The fourth is the one NO EXISTING CONTROL COMPUTES.  mg-069f put it into
       live body text in the F5 restoration ("Var(pos_sigma z) = m(m+2)/12 =
       Theta(n^2)") and asserts nothing about it anywhere; the direction check
       only prints it in a comment.  A restored clause resting on an unchecked
       number is the F5 risk running in the other direction.

  (IV) b_x <= m_x, and the two equality sites, on the same full population --
       so that this instrument reproduces the verdict independently rather than
       inheriting it.

Exact rational arithmetic, standard library only, no sampling.  Exits non-zero on
any mismatch.

Run:  python3 scripts/onethird_mg0242_identity_recheck.py
"""

import itertools
import sys
from fractions import Fraction

NS = (3, 4, 5)


# --------------------------------------------------------------- enumeration ---


def labelled_posets(n):
    """Every partial order on the labelled set {0..n-1}, as a frozenset of pairs.

    Built by choosing, for each unordered pair, one of {incomparable, a<b, b<a}
    and keeping the transitively closed choices.  Antisymmetry is automatic (a
    pair gets at most one direction) and reflexivity is not represented.
    """
    pairs = list(itertools.combinations(range(n), 2))
    for choice in itertools.product((0, 1, 2), repeat=len(pairs)):
        rel = set()
        for (a, b), c in zip(pairs, choice):
            if c == 1:
                rel.add((a, b))
            elif c == 2:
                rel.add((b, a))
        if all((a, d) in rel for (a, b) in rel for (c, d) in rel
               if b == c and a != d):
            yield frozenset(rel)


def extensions(n, rel):
    """Every linear extension, grown minimal-element-first (not n!-filtered)."""
    preds = {x: {a for (a, b) in rel if b == x} for x in range(n)}
    out, prefix, placed = [], [], set()

    def grow():
        if len(prefix) == n:
            out.append(tuple(prefix))
            return
        for x in range(n):
            if x not in placed and preds[x] <= placed:
                placed.add(x)
                prefix.append(x)
                grow()
                prefix.pop()
                placed.discard(x)

    grow()
    return out


# ----------------------------------------------------------------- the checks ---


def sweep(n, verbose_fail):
    """Parts (I), (II a-c) and (IV) at one n.  Returns a counter dict."""
    R = dict(posets=0, pairs=0, triples=0,
             bad_F1=0, bad_decomp=0, bad_degree=0, bad_handshake=0,
             bad_direction=0, bad_emin=0, bad_emax=0,
             strict=0, equal=0)
    for rel in labelled_posets(n):
        R["posets"] += 1
        exts = extensions(n, rel)
        N = len(exts)
        w = Fraction(1, N)
        # precompute, per sigma, the position map
        posmaps = [{x: i for i, x in enumerate(s)} for s in exts]
        for e in exts:                      # every reference order
            R["pairs"] += 1
            erank = {x: i for i, x in enumerate(e)}
            EA = [Fraction(0)] * n
            EB = [Fraction(0)] * n
            Einv = Fraction(0)
            for pos in posmaps:
                inv = 0
                inv_deg = [0] * n
                for a, b in itertools.combinations(range(n), 2):
                    if (erank[a] < erank[b]) != (pos[a] < pos[b]):
                        inv += 1
                        inv_deg[a] += 1
                        inv_deg[b] += 1
                Einv += w * inv
                for x in range(n):
                    A = sum(1 for y in range(n)
                            if erank[y] > erank[x] and pos[y] < pos[x])
                    B = sum(1 for y in range(n)
                            if erank[y] < erank[x] and pos[y] > pos[x])
                    # (II a) displacement IS the signed inversion sum
                    if pos[x] - erank[x] != A - B:
                        R["bad_decomp"] += 1
                    # (II b) inversion DEGREE is the unsigned one
                    if A + B != inv_deg[x]:
                        R["bad_degree"] += 1
                    EA[x] += w * A
                    EB[x] += w * B
                # (II c) handshake
                if sum(inv_deg) != 2 * inv:
                    R["bad_handshake"] += 1
            m = [EA[x] + EB[x] for x in range(n)]
            b = [abs(EA[x] - EB[x]) for x in range(n)]
            # (I) (F1)
            if sum(m) != 2 * Einv:
                R["bad_F1"] += 1
                if verbose_fail:
                    print(f"    (F1) FAILS: n={n} rel={sorted(rel)} e={e}")
            # (IV)
            for x in range(n):
                R["triples"] += 1
                if b[x] > m[x]:
                    R["bad_direction"] += 1
                elif b[x] < m[x]:
                    R["strict"] += 1
                else:
                    R["equal"] += 1
            if b[e[0]] != m[e[0]]:
                R["bad_emin"] += 1
            if b[e[-1]] != m[e[-1]]:
                R["bad_emax"] += 1
    return R


def cross_double_sum(n):
    """(II) with Cross recomputed from ITS OWN definition, exhaustively.

    Cross = Sum_x Sum_{y != z, both != x} eps_xy eps_xz E[I_xy I_xz],
    with eps_xy = +1 if y is e-above x and -1 if e-below, and I_xy the indicator
    that the pair {x,y} is inverted.  Compared against E[Sum disp^2] - 2E[inv_e].
    Run at n = 3,4 (1 002 (poset, e) pairs) -- the n = 5 double sum is 3e8 terms.
    """
    checked = bad = 0
    for rel in labelled_posets(n):
        exts = extensions(n, rel)
        N = len(exts)
        w = Fraction(1, N)
        posmaps = [{x: i for i, x in enumerate(s)} for s in exts]
        for e in exts:
            erank = {x: i for i, x in enumerate(e)}
            Einv = Fraction(0)
            Edisp2 = Fraction(0)
            cross = Fraction(0)
            for pos in posmaps:
                inv = 0
                I = [[0] * n for _ in range(n)]
                for a, bb in itertools.combinations(range(n), 2):
                    if (erank[a] < erank[bb]) != (pos[a] < pos[bb]):
                        inv += 1
                        I[a][bb] = I[bb][a] = 1
                Einv += w * inv
                for x in range(n):
                    Edisp2 += w * (pos[x] - erank[x]) ** 2
                    for y in range(n):
                        if y == x:
                            continue
                        for z in range(n):
                            if z == x or z == y:
                                continue
                            ey = 1 if erank[y] > erank[x] else -1
                            ez = 1 if erank[z] > erank[x] else -1
                            cross += w * ey * ez * I[x][y] * I[x][z]
            checked += 1
            if Edisp2 != 2 * Einv + cross:
                bad += 1
    return checked, bad


# ------------------------------------------------------------------- W_m -----


def w_m_forms(m):
    """The four closed forms, recomputed from L(W_m) itself."""
    n = m + 1
    rel = frozenset((i, i + 1) for i in range(m - 1))
    # transitive closure of the chain 0 < 1 < ... < m-1; element m is free
    rel = frozenset((i, j) for i in range(m) for j in range(i + 1, m))
    exts = extensions(n, rel)
    N = len(exts)
    w = Fraction(1, N)
    s = m // 2
    t = -(-(m - 1) // 2)
    e = tuple(list(range(t)) + [m] + list(range(t, m)))
    erank = {x: i for i, x in enumerate(e)}
    EA = [Fraction(0)] * n
    EB = [Fraction(0)] * n
    Einv = Fraction(0)
    Epos_z = Fraction(0)
    Epos_z2 = Fraction(0)
    for sigma in exts:
        pos = {x: i for i, x in enumerate(sigma)}
        inv = sum(1 for a, b in itertools.combinations(range(n), 2)
                  if (erank[a] < erank[b]) != (pos[a] < pos[b]))
        Einv += w * inv
        Epos_z += w * pos[m]
        Epos_z2 += w * pos[m] ** 2
        for x in range(n):
            EA[x] += w * sum(1 for y in range(n)
                             if erank[y] > erank[x] and pos[y] < pos[x])
            EB[x] += w * sum(1 for y in range(n)
                             if erank[y] < erank[x] and pos[y] > pos[x])
    mm = [EA[x] + EB[x] for x in range(n)]
    bb = [abs(EA[x] - EB[x]) for x in range(n)]
    return dict(m=m, s=s, m_z=mm[m], E_inv=Einv, sum_b2=sum(v * v for v in bb),
                var_z=Epos_z2 - Epos_z ** 2, num_le=N)


def main():
    fail = []

    print("=" * 92)
    print("mg-0242 — independent re-run of the identities and closed forms")
    print("=" * 92)
    print()
    print("(III) The four W_m closed forms, recomputed from L(W_m) by enumeration")
    print(f"  {'m':>3} {'|L|':>5} {'m_z = E[inv_e]':>16} {'s(s+1)/(2s+1)':>16}"
          f" {'Sum b^2':>12} {'s(s+1)/(3(2s+1))':>18} {'ratio':>7}"
          f" {'Var(pos z)':>12} {'m(m+2)/12':>12}")
    for m in (2, 4, 6, 8, 10, 12):
        r = w_m_forms(m)
        s = r["s"]
        f1 = Fraction(s * (s + 1), 2 * s + 1)
        f2 = Fraction(s * (s + 1), 3 * (2 * s + 1))
        f4 = Fraction(m * (m + 2), 12)
        ratio = r["sum_b2"] / r["E_inv"]
        print(f"  {m:>3} {r['num_le']:>5} {str(r['E_inv']):>16} {str(f1):>16}"
              f" {str(r['sum_b2']):>12} {str(f2):>18} {str(ratio):>7}"
              f" {str(r['var_z']):>12} {str(f4):>12}")
        if r["m_z"] != r["E_inv"]:
            fail.append(f"W_{m}: m_z != E[inv_e]")
        if r["E_inv"] != f1:
            fail.append(f"W_{m}: E[inv_e] != s(s+1)/(2s+1)")
        if r["sum_b2"] != f2:
            fail.append(f"W_{m}: Sum b^2 != s(s+1)/(3(2s+1))")
        if ratio != Fraction(1, 3):
            fail.append(f"W_{m}: ratio != 1/3  (got {ratio})")
        if r["var_z"] != f4:
            fail.append(f"W_{m}: Var(pos z) != m(m+2)/12  (got {r['var_z']})")
    print("  => all four forms reproduced, including Var(pos_sigma z) = m(m+2)/12,")
    print("     which mg-069f put into live body text and no control asserts.")
    print()

    print("(II, definition) Cross recomputed from its own double sum, n = 3,4")
    tot_checked = tot_bad = 0
    for n in (3, 4):
        checked, bad = cross_double_sum(n)
        tot_checked += checked
        tot_bad += bad
        print(f"  n={n}: {checked} (poset, e) pairs, mismatches with "
              f"E[Sum disp^2] - 2E[inv_e]: {bad}")
    if tot_bad:
        fail.append(f"(star) Cross double sum mismatched on {tot_bad} pairs")
    print(f"  => (star) holds with Cross computed from its DEFINITION on "
          f"{tot_checked} pairs")
    print()

    print("(I), (II a-c), (IV) on the FULL labelled population")
    tot = dict()
    for n in NS:
        R = sweep(n, verbose_fail=True)
        for k, v in R.items():
            tot[k] = tot.get(k, 0) + v
        print(f"  n={n}: {R['posets']:>5} posets, {R['pairs']:>6} pairs, "
              f"{R['triples']:>7} triples")
    print(f"  TOTAL: {tot['posets']} posets, {tot['pairs']} pairs, "
          f"{tot['triples']} triples")
    if (tot["posets"], tot["pairs"], tot["triples"]) != (4469, 43842, 218166):
        fail.append(f"population is {(tot['posets'], tot['pairs'], tot['triples'])},"
                    " not (4469, 43842, 218166)")
    print()
    print(f"  (F1)   Sum_x m_x = 2E[inv_e]            : violations {tot['bad_F1']}"
          f" / {tot['pairs']}")
    print(f"  (star a) disp = A_x - B_x               : violations {tot['bad_decomp']}")
    print(f"  (star b) A_x + B_x = inversion degree   : violations {tot['bad_degree']}")
    print(f"  (star c) Sum_x deg = 2 inv (handshake)  : violations "
          f"{tot['bad_handshake']}")
    print(f"  b_x <= m_x                              : violations "
          f"{tot['bad_direction']} / {tot['triples']}"
          f"   (strict {tot['strict']}, equal {tot['equal']})")
    print(f"  b_x = m_x at the e-MINIMUM              : failures {tot['bad_emin']}"
          f" / {tot['pairs']}")
    print(f"  b_x = m_x at the e-MAXIMUM              : failures {tot['bad_emax']}"
          f" / {tot['pairs']}")
    for k in ("bad_F1", "bad_decomp", "bad_degree", "bad_handshake",
              "bad_direction", "bad_emin", "bad_emax"):
        if tot[k]:
            fail.append(f"{k} = {tot[k]}")

    print()
    print("=" * 92)
    if fail:
        print("RESULT: FAIL")
        for f in fail:
            print(f"  - {f}")
        return 1
    print("RESULT: PASS — every identity and closed form mg-069f preserves is")
    print("        reproduced by an implementation that shares no code with the")
    print("        two instruments already in CI.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
