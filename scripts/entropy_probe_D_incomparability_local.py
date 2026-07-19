#!/usr/bin/env python3
"""Entropy probe D (mg-e2de): does the incomparability graph determine delta?

Elementary, self-contained. Enumerates all posets on n <= 6 elements up to
isomorphism, groups them by the ISOMORPHISM CLASS OF THEIR INCOMPARABILITY
GRAPH, and reports groups containing posets with different balance constants
delta (and/or different linear-extension counts e).

A group with two distinct delta values is a proof that delta is NOT a function
of the incomparability graph.

Everything is brute force; n <= 6 so the whole run is seconds.
"""

from itertools import combinations, permutations
from functools import lru_cache
import sys


# ---------------------------------------------------------------- posets

def gen_posets(n):
    """All labelled posets on {0..n-1} for which 0<1<...<n-1 is a linear
    extension, i.e. all transitively-closed subsets of the strict upper
    triangle.  Every isomorphism class is hit at least once."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m = len(pairs)
    for mask in range(1 << m):
        rel = set(p for k, p in enumerate(pairs) if mask >> k & 1)
        ok = True
        for (a, b) in rel:
            if not ok:
                break
            for (c, d) in rel:
                if b == c and (a, d) not in rel:
                    ok = False
                    break
        if ok:
            yield frozenset(rel)


def canon(n, rel):
    """Canonical form of a relation (set of ordered pairs) under relabelling."""
    best = None
    for p in permutations(range(n)):
        img = tuple(sorted((p[a], p[b]) for (a, b) in rel))
        if best is None or img < best:
            best = img
    return best


def canon_graph(n, edges):
    """Canonical form of an undirected graph given as a set of frozensets."""
    best = None
    for p in permutations(range(n)):
        img = tuple(sorted(tuple(sorted((p[a], p[b]))) for (a, b) in edges))
        if best is None or img < best:
            best = img
    return best


def incomparability_edges(n, rel):
    return [(i, j) for i in range(n) for j in range(i + 1, n)
            if (i, j) not in rel and (j, i) not in rel]


# ------------------------------------------------- linear extension counts

def count_ext(n, below):
    """#linear extensions, DP over down-sets.  below[v] = bitmask of v's
    strict predecessors."""
    full = (1 << n) - 1

    @lru_cache(maxsize=None)
    def f(S):
        if S == full:
            return 1
        t = 0
        for v in range(n):
            if not (S >> v & 1) and (below[v] & ~S) == 0:
                t += f(S | 1 << v)
        return t

    r = f(0)
    f.cache_clear()
    return r


def below_masks(n, rel):
    b = [0] * n
    for (a, c) in rel:
        b[c] |= 1 << a
    return tuple(b)


def transitive_closure_add(n, rel, x, y):
    """rel with x<y added, transitively closed (rel is a poset, x||y)."""
    new = set(rel)
    new.add((x, y))
    changed = True
    while changed:
        changed = False
        for (a, b) in list(new):
            for (c, d) in list(new):
                if b == c and (a, d) not in new:
                    new.add((a, d))
                    changed = True
    return new


def delta(n, rel):
    """Balance constant: max over incomparable pairs of min(Pr[x<y],Pr[y<x])."""
    e = count_ext(n, below_masks(n, rel))
    best = 0.0
    witness = None
    for (x, y) in incomparability_edges(n, rel):
        exy = count_ext(n, below_masks(n, transitive_closure_add(n, rel, x, y)))
        p = exy / e
        val = min(p, 1 - p)
        if val > best:
            best, witness = val, (x, y, exy, e)
    return best, witness, e


# ------------------------------------------------------------------ main

def run(n):
    seen = {}
    for rel in gen_posets(n):
        c = canon(n, rel)
        if c in seen:
            continue
        seen[c] = rel

    groups = {}
    for c, rel in seen.items():
        g = canon_graph(n, incomparability_edges(n, rel))
        d, w, e = delta(n, rel)
        groups.setdefault(g, []).append((round(d, 6), e, sorted(rel), w))

    print(f"n={n}: {len(seen)} posets up to iso, "
          f"{len(groups)} incomparability-graph classes")

    split_delta, split_e = [], []
    for g, members in groups.items():
        if len({m[0] for m in members}) > 1:
            split_delta.append((g, members))
        if len({m[1] for m in members}) > 1:
            split_e.append((g, members))

    print(f"  graph classes with >1 distinct delta: {len(split_delta)}")
    print(f"  graph classes with >1 distinct e:     {len(split_e)}")

    for g, members in sorted(split_delta, key=lambda t: len(t[1]))[:4]:
        print("\n  --- incomparability graph edges:", g)
        for d, e, rel, w in sorted(members):
            print(f"      delta={d}  e={e}  relation={rel}")
            print(f"        witness pair {w[0]},{w[1]}: {w[2]}/{w[3]}")
    return split_delta


if __name__ == "__main__":
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(3, top + 1):
        run(n)
        print()
