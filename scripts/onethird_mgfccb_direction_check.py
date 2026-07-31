#!/usr/bin/env python3
"""
mg-fccb — direction check for the `b` vs `m` inequality in
`docs/OneThird-L1b-Spread-Locality.md` §2.3, and for this deliverable's own claims.

Self-contained: stdlib only (exact rational arithmetic via `fractions`), no numpy,
no dependency on the mg-b0a6 engine. Deterministic, brute-force LE enumeration.

Definitions (matching `OneThird-L1b-Spread-Locality.md` §2.3 and
`OneThird-Bbias-Locality-Lemma.md` §4):

    sigma ~ uniform on L(P);  e = a fixed reference linear extension
    disp_sigma(x) = pos_sigma(x) - rank_e(x)          (0-indexed positions)
    A_x = #{y : rank_e(y) > rank_e(x), y before x in sigma}
    B_x = #{y : rank_e(y) < rank_e(x), y after  x in sigma}
    disp_sigma(x) = A_x - B_x
    m_x = E[A_x] + E[B_x]     (expected inversion degree; a SUM)
    b_x = |E[disp(x)]| = |E[A_x] - E[B_x]|   (per-element bias; a DIFFERENCE)

The three questions this script settles:

  (1) DIRECTION.  Is `b_x <= m_x` (triangle inequality, the relation that is
      available) or `b_x >= m_x` (what §2.3's struck sentence needed)?
  (2) WITNESS.    On W_m = C_m (+) C_1, does `max_x m_x = Theta(n)` with
      `E[inv_e] = Theta(n)` force the deterministic part of (B),
      `Sum_x b_x^2`, to be Theta(n^2) -- as the struck sentence concluded?
  (3) SELF-CHECK. This deliverable claims `Sum_x b_x^2 / E[inv_e] = 1/3` exactly
      on W_m for every even m, and that (B) nonetheless fails on W_m through the
      VARIANCE term.  Both are checked exactly.

Run:  python3 scripts/onethird_mgfccb_direction_check.py
"""

from fractions import Fraction
from itertools import permutations, combinations

# ---------------------------------------------------------------- poset engine


class Poset:
    """Poset on ground set range(n) given by a strict-order relation set."""

    def __init__(self, n, relations):
        self.n = n
        # transitive closure of `relations` (pairs (a, b) meaning a < b)
        less = {(a, b) for a, b in relations}
        changed = True
        while changed:
            changed = False
            for a, b in list(less):
                for c, d in list(less):
                    if b == c and (a, d) not in less:
                        less.add((a, d))
                        changed = True
        self.less = less

    def leq(self, a, b):
        return a == b or (a, b) in self.less

    def incomparable(self, a, b):
        return a != b and (a, b) not in self.less and (b, a) not in self.less

    def linear_extensions(self):
        for perm in permutations(range(self.n)):
            pos = {x: i for i, x in enumerate(perm)}
            if all(pos[a] < pos[b] for a, b in self.less):
                yield perm


def stats(poset, e=None):
    """Exact per-element statistics against reference order `e`.

    Returns a dict with m_x, b_x, E[disp^2] totals, E[inv_e], all exact Fractions.
    """
    les = list(poset.linear_extensions())
    N = len(les)
    assert N > 0
    if e is None:
        e = les[0]
    rank_e = {x: i for i, x in enumerate(e)}

    n = poset.n
    EA = {x: Fraction(0) for x in range(n)}
    EB = {x: Fraction(0) for x in range(n)}
    Edisp = {x: Fraction(0) for x in range(n)}
    Edisp2 = {x: Fraction(0) for x in range(n)}
    Einv = Fraction(0)

    w = Fraction(1, N)
    for perm in les:
        pos = {x: i for i, x in enumerate(perm)}
        inv = 0
        for a, b in combinations(range(n), 2):
            if poset.incomparable(a, b):
                # inverted iff e-order and sigma-order disagree
                if (rank_e[a] < rank_e[b]) != (pos[a] < pos[b]):
                    inv += 1
        Einv += w * inv
        for x in range(n):
            A = sum(1 for y in range(n) if rank_e[y] > rank_e[x] and pos[y] < pos[x])
            B = sum(1 for y in range(n) if rank_e[y] < rank_e[x] and pos[y] > pos[x])
            d = pos[x] - rank_e[x]
            assert d == A - B, "disp = A - B identity failed"
            EA[x] += w * A
            EB[x] += w * B
            Edisp[x] += w * d
            Edisp2[x] += w * d * d

    m = {x: EA[x] + EB[x] for x in range(n)}
    b = {x: abs(Edisp[x]) for x in range(n)}
    return {
        "n": n,
        "num_le": N,
        "m": m,
        "b": b,
        "E_inv": Einv,
        "sum_b2": sum(v * v for v in b.values()),
        "sum_m2": sum(v * v for v in m.values()),
        "E_sum_disp2": sum(Edisp2.values()),
        "sum_m": sum(m.values()),
    }


# ---------------------------------------------------------------- test posets


def W(m):
    """W_m = C_m (+) C_1: an m-chain c_1<...<c_m, plus one incomparable point z.

    Ground set: 0..m-1 are c_1..c_m, m is z.
    """
    return Poset(m + 1, [(i, i + 1) for i in range(m - 1)])


def W_reference_order(m):
    """The reference order e of mg-a58f §6.1: c_i <_e z iff i < (m+1)/2."""
    t = -(-(m - 1) // 2)  # ceil((m-1)/2)
    return tuple(list(range(t)) + [m] + list(range(t, m)))


def all_posets(n):
    """All posets on n labelled elements (small n only), as Poset objects."""
    pairs = list(combinations(range(n), 2))
    seen = set()
    for mask in range(1 << len(pairs)):
        rels = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        p = Poset(n, rels)
        key = frozenset(p.less)
        if key in seen:
            continue
        # reject non-posets (the closure must stay antisymmetric)
        if any((b, a) in p.less for a, b in p.less):
            continue
        seen.add(key)
        yield p


# ---------------------------------------------------------------- the checks


def check_1_direction():
    print("=" * 78)
    print("(1) DIRECTION: is b_x <= m_x, or b_x >= m_x?")
    print("=" * 78)
    worst_ratio = None
    total = 0
    violations_le = 0  # counts b_x >  m_x  (would support the struck sentence)
    strict_lt = 0      # counts b_x <  m_x  (the lossy direction)
    for n in (3, 4, 5):
        for p in all_posets(n):
            les = list(p.linear_extensions())
            if not les:
                continue
            for e in les:  # every choice of reference order, not just one
                s = stats(p, e)
                for x in range(n):
                    total += 1
                    if s["b"][x] > s["m"][x]:
                        violations_le += 1
                    if s["b"][x] < s["m"][x]:
                        strict_lt += 1
                    if s["m"][x] > 0:
                        r = s["b"][x] / s["m"][x]
                        if worst_ratio is None or r > worst_ratio:
                            worst_ratio = r
    print(f"  (element, reference-order) pairs examined : {total}")
    print(f"  cases with b_x >  m_x                     : {violations_le}")
    print(f"  cases with b_x <  m_x (strictly lossy)    : {strict_lt}")
    print(f"  max observed b_x / m_x                    : {worst_ratio}")
    assert violations_le == 0, "b_x <= m_x was violated -- would break the fix"
    print("  => b_x <= m_x ALWAYS.  The reverse substitution b_x -> m_x under a")
    print("     LOWER bound (what the struck sentence needed) is never available.")
    print()
    return violations_le == 0


def check_2_witness():
    print("=" * 78)
    print("(2) WITNESS W_m: does max_x m_x = Theta(n) force Sum_x b_x^2 = Theta(n^2)?")
    print("=" * 78)
    print(f"  {'m':>3} {'n':>3} {'max m_x':>10} {'E[inv_e]':>10} "
          f"{'Sum b_x^2':>10} {'ratio':>8} {'(max m)^2':>10}")
    rows = []
    for m in range(1, 9):
        p = W(m)
        e = W_reference_order(m)
        s = stats(p, e)
        max_m = max(s["m"].values())
        ratio = s["sum_b2"] / s["E_inv"]
        rows.append((m, s, max_m, ratio))
        print(f"  {m:>3} {m+1:>3} {str(max_m):>10} {str(s['E_inv']):>10} "
              f"{str(s['sum_b2']):>10} {str(ratio):>8} {str(max_m**2):>10}")
    print()
    print("  The struck sentence concluded `E[Sum disp^2] >= m_x^2 = Theta(n^2)`")
    print("  from `m_x = Theta(n)` and `E[inv_e] = Theta(n)`.  On W_m both")
    print("  hypotheses hold, yet Sum_x b_x^2 stays O(n) -- the DETERMINISTIC part")
    print("  of (B) is satisfied.  The inference fails on its own configuration.")
    for m, s, max_m, ratio in rows:
        assert s["sum_b2"] <= s["n"], "Sum b_x^2 exceeded n on W_m"
    print("  checked: Sum_x b_x^2 <= n for every m above.  OK")
    print()
    return rows


def check_3_selfcheck(rows):
    print("=" * 78)
    print("(3) SELF-CHECK of this deliverable's own two new claims")
    print("=" * 78)
    print("  (3a) claim: Sum_x b_x^2 / E[inv_e] = 1/3 EXACTLY on W_m for even m")
    ok_a = True
    for m, s, max_m, ratio in rows:
        if m % 2 == 0:
            flag = "OK" if ratio == Fraction(1, 3) else "MISMATCH"
            if ratio != Fraction(1, 3):
                ok_a = False
            print(f"       m={m:<2} ratio = {ratio}   {flag}")
    assert ok_a, "the 1/3 claim is wrong"
    print("       also checked: closed form Sum_x b_x^2 = s(s+1)/(3(2s+1)), m=2s")
    for m, s, max_m, ratio in rows:
        if m % 2 == 0:
            ss = m // 2
            closed = Fraction(ss * (ss + 1), 3 * (2 * ss + 1))
            assert s["sum_b2"] == closed, f"closed form failed at m={m}"
    print("       closed form matches at every even m above.  OK")
    print()
    print("  (3b) claim: (B) DOES fail on W_m, but through the VARIANCE term")
    print(f"       {'m':>3} {'E[Sum disp^2]':>14} {'E[inv_e]':>10} "
          f"{'(B) ratio':>12} {'Sum b_x^2':>10} {'variance part':>14}")
    prev = None
    for m, s, max_m, ratio in rows:
        bratio = s["E_sum_disp2"] / s["E_inv"]
        var_part = s["E_sum_disp2"] - s["sum_b2"]
        print(f"       {m:>3} {str(s['E_sum_disp2']):>14} {str(s['E_inv']):>10} "
              f"{str(bratio):>12} {str(s['sum_b2']):>10} {str(var_part):>14}")
        if prev is not None:
            # non-decreasing (m=1 and m=2 tie at 2; growth is strict from m=2 on)
            assert bratio >= prev, "(B) ratio should be non-decreasing in m on W_m"
        prev = bratio
    first = rows[0][1]["E_sum_disp2"] / rows[0][1]["E_inv"]
    assert prev > first, "(B) ratio should grow overall in m on W_m"
    print("       (B) ratio grows linearly in m => (B) fails on W_m.")
    print("       (asymptotically ~ m/3, from Var(pos z) = m(m+2)/12 over")
    print("        E[inv_e] ~ m/4; lower-order terms still dominate at m <= 8.)")
    print("       The whole growth sits in the variance part, NOT in Sum_x b_x^2,")
    print("       which is exactly what the struck sentence mis-attributed.")
    print()
    print("  (3c) claim: Sum_x m_x = 2 E[inv_e] identically (mg-a58f Thm 3.2 (F1))")
    for m, s, max_m, ratio in rows:
        assert s["sum_m"] == 2 * s["E_inv"], f"(F1) failed at m={m}"
    print("       verified on every W_m above.  OK")
    print()


def check_4_emin():
    print("=" * 78)
    print("(4) The e-MINIMAL element: where b_x = m_x, so §3.1's falsifier IS valid")
    print("=" * 78)
    bad = 0
    total = 0
    for n in (3, 4, 5):
        for p in all_posets(n):
            for e in p.linear_extensions():
                s = stats(p, e)
                x = e[0]  # the e-minimal element
                total += 1
                if s["b"][x] != s["m"][x]:
                    bad += 1
    print(f"  (poset, reference-order) pairs examined : {total}")
    print(f"  cases with b_x != m_x at the e-minimum  : {bad}")
    assert bad == 0
    print("  => at the e-minimum B_x = 0, so b_x = m_x and the substitution IS")
    print("     legitimate.  §3.1 stands; only its generalisation to max_x fails.")
    print()


if __name__ == "__main__":
    print()
    print("mg-fccb — inequality-direction check for Spread-Locality §2.3")
    print("exact rational arithmetic; no sampling; no external dependencies")
    print()
    check_1_direction()
    rows = check_2_witness()
    check_3_selfcheck(rows)
    check_4_emin()
    print("=" * 78)
    print("ALL CHECKS PASSED")
    print("=" * 78)
