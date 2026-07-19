"""Bounded numerical check of the consecutive-slot bound (Theorem A).

Claim:  if the majority tournament of P is strict (no incomparable pair has
probability exactly 1/2) and transitive, with reference linear order
e = a_1 < ... < a_n, and
   T = { i : a_i, a_{i+1} incomparable in P },   s = |T|,
then          delta(P) >= (1 - 1/e(P)) / s.

Also checks the auxiliary lower bound  e(P) >= i(T) := #{S subset of T with no
two consecutive integers}.

Enumeration is over one representative per isomorphism class: every finite
poset can be relabelled along a linear extension so that all relations point
upward in the labelling, and delta, e(P), s are isomorphism invariants.
"""
import itertools
from fractions import Fraction

HALF = Fraction(1, 2)


def upward_posets(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        rel = frozenset(p for k, p in enumerate(pairs) if mask >> k & 1)
        if all(not (j == k and (i, l) not in rel)
               for (i, j) in rel for (k, l) in rel):
            yield rel


def linear_extensions(n, rel):
    return [p for p in itertools.permutations(range(n))
            if all(p.index(i) < p.index(j) for (i, j) in rel)]


def independent_sets_on_path(T):
    T = sorted(T)
    return sum(1 for r in range(len(T) + 1) for S in itertools.combinations(T, r)
               if all(S[k + 1] - S[k] != 1 for k in range(len(S) - 1)))


def run(n):
    tested = skipped_tie = skipped_cyc = 0
    worst = worst_ind = None
    for rel in upward_posets(n):
        inc = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in rel]
        if not inc:
            continue                                    # chain
        L = linear_extensions(n, rel)
        eP = len(L)
        before = {p: Fraction(sum(1 for q in L if q.index(p[0]) < q.index(p[1])), eP)
                  for p in inc}
        delta = max(min(before[p], 1 - before[p]) for p in inc)

        if any(before[p] == HALF for p in inc):
            skipped_tie += 1                            # e not well defined
            continue

        def maj(a, b):                                  # True iff a beats b
            if (a, b) in rel:
                return True
            if (b, a) in rel:
                return False
            return (before[(a, b)] if a < b else 1 - before[(b, a)]) > HALF

        if any(maj(a, b) and maj(b, c) and not maj(a, c)
               for a, b, c in itertools.permutations(range(n), 3)):
            skipped_cyc += 1                            # majorities cycle
            continue

        e = sorted(range(n), key=lambda v: -sum(maj(v, w) for w in range(n) if w != v))
        posE = {v: k for k, v in enumerate(e)}
        assert all(posE[i] < posE[j] for (i, j) in rel), "e is not a linear extension"

        T = [i for i in range(n - 1)
             if (min(e[i], e[i + 1]), max(e[i], e[i + 1])) in inc]
        s = len(T)
        assert s >= 1, "a non-chain must have a free consecutive slot"

        bound = (1 - Fraction(1, eP)) / s
        assert delta >= bound, ("Theorem A FAILS", sorted(rel), delta, bound)
        ind = independent_sets_on_path(T)
        assert eP >= ind, ("e(P) >= i(T) FAILS", sorted(rel), eP, ind)

        tested += 1
        if worst is None or delta - bound < worst[0]:
            worst = (delta - bound, delta, bound, s, eP, sorted(rel))
        if worst_ind is None or eP - ind < worst_ind[0]:
            worst_ind = (eP - ind, eP, ind, s, sorted(rel))

    print(f"n={n}: {tested} iso classes with a strict transitive majority tournament "
          f"(skipped {skipped_tie} with a 1/2 tie, {skipped_cyc} with a majority cycle)")
    if tested:
        g, d, b, s, eP, rel = worst
        print(f"   Theorem A holds in all {tested}.  tightest: delta={d}, bound={b}, "
              f"gap={g}, s={s}, e(P)={eP}, rel={rel}")
        _, eP2, ind2, s2, rel2 = worst_ind
        print(f"   e(P) >= i(T) holds in all {tested}.  tightest: e(P)={eP2}, "
              f"i(T)={ind2}, s={s2}, rel={rel2}")


if __name__ == "__main__":
    for n in (2, 3, 4, 5, 6):
        run(n)
