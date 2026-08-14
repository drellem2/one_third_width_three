#!/usr/bin/env /usr/bin/python3
"""mg-9cd1 -- INDEPENDENT audit instrument for mg-72e4's height-1 anchor result.

Written from scratch for the audit.  It does NOT import, read, or call
scripts/compat_geom_mg72e4_height1_anchor.py; every routine below (transitive closure,
height-1 enumeration, orbit counting, atoms, the crosscut complex, homology) is a second
implementation, and where a second ALGORITHM was available it is used rather than a
second spelling of the same one:

  * labelled height-1 counts are obtained in CLOSED FORM by inclusion-exclusion over
    isolated vertices, not by enumeration;
  * isomorphism classes are obtained by UNION-FIND orbit counting under adjacent
    transpositions, not by canonical-form minimisation over S_n;
  * Betti numbers are computed mod two primes DIFFERENT from the target instrument's.

Sections
  A. labelled height-1 census, closed form, n = 3..7, and the split by c
  B. iso classes and class sizes by orbit counting, n = 3..7
  C. Gamma(P) low-degree homology for EVERY n=7 class -- the margin / Conjecture-C test
     that the target document performs on only 146 of its 163 classes
  D. n <= 6 full margins, and the star K_{n-1,1} inference rule checked where measurable
  E. crosscut reduction re-checked against a direct upper-link computation at n = 4
"""

import itertools
import json
import os
import sys
from collections import defaultdict

# deliberately different primes from the target instrument's (1_000_003, 999_983)
PRIMES = (2_147_483_647, 1_000_000_007)


# --------------------------------------------------------------------------- A. counting
def binom(a, b):
    if b < 0 or b > a:
        return 0
    r = 1
    for i in range(b):
        r = r * (a - i) // (i + 1)
    return r


def bipartite_no_isolated(a, b):
    """# bipartite graphs on labelled parts of sizes a,b with no isolated vertex."""
    s = 0
    for i in range(a + 1):
        for j in range(b + 1):
            s += (-1) ** (i + j) * binom(a, i) * binom(b, j) * 2 ** ((a - i) * (b - j))
    return s


def bipartite_no_isolated_by_edges(a, b):
    """dict e -> # bipartite graphs on labelled parts a,b, no isolated vertex, e edges."""
    out = defaultdict(int)
    for i in range(a + 1):
        for j in range(b + 1):
            sgn = (-1) ** (i + j) * binom(a, i) * binom(b, j)
            m = (a - i) * (b - j)
            for e in range(m + 1):
                out[e] += sgn * binom(m, e)
    return {e: v for e, v in out.items() if v}


def labelled_height1_census(n):
    """A height-1 poset on [n] is a tail set T, a head set H (disjoint) and a bipartite
    relation T x H with no isolated vertex in T u H.  Everything else is free."""
    total = 0
    by_c = defaultdict(int)
    for a in range(1, n):
        for b in range(1, n - a + 1):
            ways = binom(n, a) * binom(n - a, b)
            total += ways * bipartite_no_isolated(a, b)
            for e, v in bipartite_no_isolated_by_edges(a, b).items():
                if e:
                    by_c[e] += ways * v
    return total, dict(by_c)


# --------------------------------------------------------------------------- posets
def close(pairs, n):
    """Transitive closure as a frozenset of pairs, or None if not acyclic."""
    succ = [set() for _ in range(n)]
    for (a, b) in pairs:
        if a == b:
            return None
        succ[a].add(b)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            add = set()
            for j in succ[i]:
                add |= succ[j]
            if not add <= succ[i]:
                succ[i] |= add
                changed = True
    for i in range(n):
        if i in succ[i]:
            return None
    return frozenset((i, j) for i in range(n) for j in succ[i])


def total_size(n):
    return n * (n - 1) // 2


def enum_height1(n):
    """Every labelled height-1 poset on [n] with >= 1 relation, by direct construction."""
    out = set()
    verts = range(n)
    for a in range(1, n):
        for T in itertools.combinations(verts, a):
            rest = [x for x in verts if x not in T]
            for b in range(1, len(rest) + 1):
                for H in itertools.combinations(rest, b):
                    cand = [(t, h) for t in T for h in H]
                    for mask in range(1, 1 << len(cand)):
                        E = [cand[i] for i in range(len(cand)) if mask >> i & 1]
                        if len({e[0] for e in E}) != a or len({e[1] for e in E}) != b:
                            continue
                        out.add(frozenset(E))
    return out


# --------------------------------------------------------------------------- B. orbits
def orbit_classes(n, posets):
    """Iso classes by union-find under the adjacent transpositions (which generate S_n)."""
    idx = {P: i for i, P in enumerate(sorted(posets, key=lambda P: (len(P), sorted(P))))}
    parent = list(range(len(idx)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x, y):
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[max(rx, ry)] = min(rx, ry)

    gens = []
    for k in range(n - 1):
        perm = list(range(n))
        perm[k], perm[k + 1] = perm[k + 1], perm[k]
        gens.append(perm)
    for P, i in idx.items():
        for perm in gens:
            Q = frozenset((perm[x], perm[y]) for (x, y) in P)
            union(i, idx[Q])
    groups = defaultdict(list)
    for P, i in idx.items():
        groups[find(i)].append(P)
    reps = []
    for g, members in groups.items():
        rep = min(members, key=lambda P: (len(P), sorted(P)))
        reps.append((rep, len(members)))
    return sorted(reps, key=lambda pr: (len(pr[0]), sorted(pr[0])))


# --------------------------------------------------------------------------- crosscut
def atoms(P, n):
    """Minimal elements of U(P) = {Q in PPF_n : Q > P}."""
    T = total_size(n)
    cands = {}
    for x in range(n):
        for y in range(n):
            if x == y or (x, y) in P:
                continue
            Q = close(set(P) | {(x, y)}, n)
            if Q is None or len(Q) == T:
                continue
            cands[Q] = True
    keys = list(cands)
    return sorted([Q for Q in keys if not any(R < Q for R in keys)],
                  key=lambda Q: (len(Q), sorted(Q)))


def gamma_faces(P, n, ats, dmax):
    """Faces of Gamma(P) of dimension <= dmax, by dimension.  Built by DFS with pruning."""
    T = total_size(n)
    m = len(ats)
    faces = defaultdict(list)

    def rec(prefix, cur):
        d = len(prefix) - 1
        faces[d].append(tuple(prefix))
        if d >= dmax:
            return
        for j in range(prefix[-1] + 1, m):
            Q = close(cur | ats[j], n)
            if Q is None or len(Q) == T:
                continue
            rec(prefix + [j], Q)

    for i in range(m):
        rec([i], set(ats[i]))
    return faces


# --------------------------------------------------------------------------- homology
def rank_mod_p(cols, p):
    """Rank of a sparse matrix given as columns {row: val}."""
    piv = {}
    rank = 0
    for col in cols:
        c = {r: v % p for r, v in col.items() if v % p}
        while c:
            r = max(c)
            if r not in piv:
                inv = pow(c[r], p - 2, p)
                piv[r] = {k: (v * inv) % p for k, v in c.items()}
                rank += 1
                break
            f = c[r]
            for k, v in piv[r].items():
                nv = (c.get(k, 0) - f * v) % p
                if nv:
                    c[k] = nv
                else:
                    c.pop(k, None)
    return rank


def reduced_betti(faces, dmax):
    """Reduced Betti numbers in degrees -1..dmax from a face dict (augmented complex)."""
    if not any(faces.get(d) for d in faces):
        return {-1: 1}
    res = []
    for p in PRIMES:
        pos = {-1: {(): 0}}
        for d in range(0, dmax + 2):
            pos[d] = {f: i for i, f in enumerate(faces.get(d, []))}
        ranks = {}
        for d in range(0, dmax + 2):
            below = pos[d - 1]
            cols = []
            for f in faces.get(d, []):
                col = {}
                for i in range(len(f)):
                    j = below[f[:i] + f[i + 1:]]
                    col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
                cols.append(col)
            ranks[d] = rank_mod_p(cols, p)
        b = {}
        for d in range(-1, dmax + 1):
            nd = 1 if d == -1 else len(faces.get(d, []))
            b[d] = nd - ranks.get(d, 0) - ranks.get(d + 1, 0)
        res.append(tuple(b[d] for d in range(-1, dmax + 1)))
    if len(set(res)) != 1:
        raise RuntimeError("prime disagreement %r" % (res,))
    return {d: res[0][d + 1] for d in range(-1, dmax + 1)}


def order_complex(elts, dmax):
    """Faces (chains) of the order complex of a set of posets ordered by inclusion."""
    el = sorted(elts, key=lambda P: (len(P), sorted(P)))
    up = [[j for j, b in enumerate(el) if el[i] < b] for i in range(len(el))]
    faces = defaultdict(list)
    frontier = []
    for i in range(len(el)):
        faces[0].append((i,))
        frontier.append((i,))
    d = 0
    while frontier and d < dmax:
        nxt = []
        for ch in frontier:
            for j in up[ch[-1]]:
                nxt.append(ch + (j,))
        d += 1
        if nxt:
            faces[d] = nxt
        frontier = nxt
    return {d: [tuple(sorted(f)) for f in v] for d, v in faces.items() if v}


def all_posets(n):
    seen = {frozenset()}
    frontier = [frozenset()]
    while frontier:
        nxt = []
        for P in frontier:
            for x in range(n):
                for y in range(n):
                    if x == y or (x, y) in P:
                        continue
                    Q = close(set(P) | {(x, y)}, n)
                    if Q is not None and Q not in seen:
                        seen.add(Q)
                        nxt.append(Q)
        frontier = nxt
    return seen


def ppf(n):
    T = total_size(n)
    return [P for P in all_posets(n) if P and len(P) != T]


# --------------------------------------------------------------------------- main
def main():
    out = {"audit": "mg-9cd1", "of": "mg-72e4 @ 75fb81d", "primes": list(PRIMES)}
    what = sys.argv[1] if len(sys.argv) > 1 else "all"

    if what in ("all", "A"):
        sec = {}
        for n in range(3, 8):
            tot, by_c = labelled_height1_census(n)
            sec[str(n)] = {"labelled_total": tot,
                           "by_c": {str(k): v for k, v in sorted(by_c.items())}}
            print("A n=%d labelled height-1 = %d ; by c = %s" % (n, tot, sorted(by_c.items())),
                  flush=True)
        n7 = sec["7"]["by_c"]
        sec["7_c_ge_7"] = sum(v for k, v in n7.items() if int(k) >= 7)
        n6 = sec["6"]["by_c"]
        sec["6_c_ge_6"] = sum(v for k, v in n6.items() if int(k) >= 6)
        print("A  n=7 c>=7 :", sec["7_c_ge_7"], "   n=6 c>=6 :", sec["6_c_ge_6"], flush=True)
        out["A_labelled_census"] = sec

    if what in ("all", "B"):
        sec = {}
        for n in range(3, 8):
            posets = enum_height1(n)
            reps = orbit_classes(n, posets)
            bysize = defaultdict(int)
            for P, k in reps:
                bysize[len(P)] += 1
            sec[str(n)] = {"labelled": len(posets), "iso_classes": len(reps),
                           "sum_class_sizes": sum(k for _, k in reps),
                           "classes_by_c": {str(k): v for k, v in sorted(bysize.items())}}
            print("B n=%d labelled=%d iso=%d (sizes sum %d) by c=%s"
                  % (n, len(posets), len(reps), sum(k for _, k in reps),
                     sorted(bysize.items())), flush=True)
        out["B_iso_classes"] = sec

    if what in ("all", "C"):
        # every n=7 class, low-degree homology of Gamma(P): degrees -1..CDEG
        CDEG = int(os.environ.get("AUDIT_CDEG", "3"))
        n = 7
        reps = orbit_classes(n, enum_height1(n))
        rows = []
        for P, mult in reps:
            c = len(P)
            d = n - c - 1
            ats = atoms(P, n)
            f = gamma_faces(P, n, ats, dmax=CDEG + 1)
            b = reduced_betti(f, CDEG)
            nz = sorted(k for k, v in b.items() if v)
            rows.append({"c": c, "class_size": mult, "n_atoms": len(ats),
                         "needed_degree": d,
                         "betti_low": {str(k): v for k, v in b.items() if v},
                         "beta_needed": b.get(d) if d <= CDEG else None,
                         "first_nonzero_le_%d" % CDEG: (nz[0] if nz else None)})
            print("C c=%2d sz=%6d atoms=%2d d=%2d betti(-1..%d)=%s"
                  % (c, mult, len(ats), d, CDEG,
                     {k: v for k, v in b.items() if v}), flush=True)
        out["C_n7_low_degree"] = {"max_degree": CDEG, "rows": rows,
                                  "classes_with_homology_below_%d" % (n - 3):
                                      [r for r in rows
                                       if any(int(k) < n - 3 for k in r["betti_low"])]}

    if what in ("all", "D"):
        sec = {}
        for n in range(3, 7):
            reps = orbit_classes(n, enum_height1(n))
            rows = []
            for P, mult in reps:
                c = len(P)
                d = n - c - 1
                ats = atoms(P, n)
                f = gamma_faces(P, n, ats, dmax=len(ats))
                b = reduced_betti(f, max(f) if f else 0) if f else {-1: 1}
                nz = sorted(k for k, v in b.items() if v)
                rows.append({"c": c, "class_size": mult, "n_atoms": len(ats),
                             "needed_degree": d,
                             "beta_needed": (1 if (d == -1 and not ats) else b.get(d, 0)),
                             "full_betti": {str(k): v for k, v in b.items() if v},
                             "first_nonzero": (nz[0] if nz else None),
                             "margin": (None if not nz else nz[0] - d)})
            margins = [r["margin"] for r in rows if r["margin"] is not None]
            viol = [r for r in rows if r["beta_needed"]]
            sec[str(n)] = {"iso_classes": len(rows),
                           "labelled": sum(r["class_size"] for r in rows),
                           "violations": len(viol),
                           "min_margin": min(margins) if margins else None,
                           "nonacyclic": sum(1 for r in rows if r["full_betti"]),
                           "degrees_with_homology": sorted({int(k) for r in rows
                                                            for k in r["full_betti"]}),
                           "rows": rows}
            print("D n=%d iso=%d labelled=%d violations=%d min_margin=%s degrees=%s"
                  % (n, len(rows), sec[str(n)]["labelled"], len(viol),
                     sec[str(n)]["min_margin"], sec[str(n)]["degrees_with_homology"]),
                  flush=True)
        out["D_n_le_6_full"] = sec

    if what in ("all", "E"):
        # crosscut vs a DIRECT upper-link computation, all vertices of Delta_4
        n = 4
        uni = ppf(n)
        agree, rows = 0, []
        for P in sorted(uni, key=lambda Q: (len(Q), sorted(Q))):
            up = [Q for Q in uni if P < Q]
            bd = reduced_betti(order_complex(up, 99), 6) if up else {-1: 1}
            ats = atoms(P, n)
            f = gamma_faces(P, n, ats, dmax=len(ats))
            bg = reduced_betti(f, 6) if f else {-1: 1}
            same = all(bd.get(k, 0) == bg.get(k, 0) for k in range(-1, 7))
            agree += same
            rows.append({"c": len(P), "direct": {str(k): v for k, v in bd.items() if v},
                         "gamma": {str(k): v for k, v in bg.items() if v}, "agree": same})
        print("E n=4: crosscut == direct on %d/%d vertices of Delta_4" % (agree, len(rows)),
              flush=True)
        out["E_crosscut_vs_direct_n4"] = {"vertices": len(rows), "agree": agree,
                                          "rows": rows}

    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "data", "onethird-mg9cd1-independent-audit-%s.json" % what)
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    print("wrote", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
