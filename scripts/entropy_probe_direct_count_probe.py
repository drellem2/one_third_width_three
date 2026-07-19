"""mg-f82f follow-up probes for docs/entropy-probe-direct-count.md.

(1) Lemma 5: for an incomparable pair p, swapping the two elements when they are
    L-adjacent is an involution exchanging the orientations, so
    Pr[p L-adjacent, minority first] = Pr[p L-adjacent]/2 <= delta.  With
    sum_p Pr[p L-adjacent] >= 1 this yields the coherence-free  delta >= 1/(2m).
(2) Theorem B: for an e-window W,  delta >= (1 - p_W)/s_W,  p_W = Pr[L|_W = e|_W].
(3) The barrier (doc section 7): does a small delta force a small s?
(4) Window conjecture W3: is  p_W <= 1/3  on size-3 windows when delta <= 1/3?

Exact rational arithmetic, one representative per isomorphism class, n <= 6.
Every claim is asserted, not merely printed.
"""
import itertools
from fractions import Fraction

from entropy_probe_direct_count_verify import (upward_posets, linear_extensions,
                                               independent_sets_on_path)

HALF = Fraction(1, 2)
THIRD = Fraction(1, 3)
rows = []                 # (delta, s, m, e(P), n, i(T))
windows = []              # (p_W, delta)


def analyse(n):
    for rel in upward_posets(n):
        inc = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in rel]
        if not inc:
            continue                                    # chain
        L = linear_extensions(n, rel)
        eP = len(L)
        before = {p: Fraction(sum(1 for q in L if q.index(p[0]) < q.index(p[1])), eP)
                  for p in inc}
        delta = max(min(before[p], 1 - before[p]) for p in inc)
        m = len(inc)

        # ---- (1) Lemma 5 and the coherence-free bound; no reference order needed
        total_adjacent = Fraction(0)
        for (x, y) in inc:
            fwd = sum(1 for q in L if q.index(x) + 1 == q.index(y))
            bwd = sum(1 for q in L if q.index(y) + 1 == q.index(x))
            assert fwd == bwd, ("Lemma 5 involution FAILS", sorted(rel), (x, y))
            total_adjacent += Fraction(fwd + bwd, eP)
        assert total_adjacent >= 1, ("sum Pr[p adjacent] >= 1 FAILS", sorted(rel))
        assert delta >= Fraction(1, 2 * m), ("delta >= 1/(2m) FAILS", sorted(rel))

        # ---- the coherent reference order, when it is defined
        if any(before[p] == HALF for p in inc):
            continue
        def maj(a, b):
            if (a, b) in rel:
                return True
            if (b, a) in rel:
                return False
            return (before[(a, b)] if a < b else 1 - before[(b, a)]) > HALF
        if any(maj(a, b) and maj(b, c) and not maj(a, c)
               for a, b, c in itertools.permutations(range(n), 3)):
            continue
        e = sorted(range(n), key=lambda v: -sum(maj(v, w) for w in range(n) if w != v))
        free = lambda i: (min(e[i], e[i + 1]), max(e[i], e[i + 1])) in inc
        T = [i for i in range(n - 1) if free(i)]
        rows.append((delta, len(T), m, eP, n, independent_sets_on_path(T)))

        # ---- (2)+(4) size-3 windows with both slots free
        for k in range(n - 2):
            if not (free(k) and free(k + 1)):
                continue
            x, y, z = e[k], e[k + 1], e[k + 2]
            pW = Fraction(sum(1 for q in L
                              if q.index(x) < q.index(y) < q.index(z)), eP)
            assert delta >= (1 - pW) / 2, ("Theorem B FAILS", sorted(rel), pW)
            windows.append((pW, delta))


for n in range(2, 7):
    analyse(n)

print("Lemma 5, sum Pr[adjacent] >= 1, delta >= 1/(2m): verified on every "
      "non-chain iso class with n <= 6")
print(f"Theorem B: verified on all {len(windows)} size-3 windows with both slots free")
print()
print("barrier check -- does a small delta force a small s?")
print(f"{'delta <= t':>12} {'#posets':>8} {'max s':>6} {'max m':>6}")
for t in ("1/3", "2/5", "1/2"):
    t = Fraction(t)
    sel = [r for r in rows if r[0] <= t]
    print(f"{str(t):>12} {len(sel):>8} {max(r[1] for r in sel):>6} "
          f"{max(r[2] for r in sel):>6}")
tight = [r for r in rows if r[0] <= THIRD]
print(f"\ns == m on all {len(tight)} classes with delta <= 1/3? "
      f"{all(r[1] == r[2] for r in tight)}   (s,m) seen: "
      f"{sorted(set((r[1], r[2]) for r in tight))}")

wt = [w for w in windows if w[1] <= THIRD]
print(f"\nwindow conjecture W3 -- max p_W over the {len(wt)} windows with "
      f"delta <= 1/3: {max(p for p, _ in wt)}  (target 1/3)")
print(f"max p_W overall: {max(p for p, _ in windows)}  "
      f"(attained only where delta > 1/3, so W3's hypothesis does not apply)")
assert all(p <= THIRD for p, _ in wt), "W3 FAILS at n <= 6"

print("\nbound (1 - 1/i(T))/s, block T vs spread T (general record 0.2764):")
fib = [1, 2, 3, 5, 8, 13]
for s in range(1, 6):
    blk, spr = (1 - Fraction(1, fib[s])) / s, (1 - Fraction(1, 2 ** s)) / s
    print(f"  s={s}: block {str(blk):>6} = {float(blk):.4f} | "
          f"spread {str(spr):>7} = {float(spr):.4f}")
