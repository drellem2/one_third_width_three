#!/usr/bin/env /usr/bin/python3
"""mg-72e4 -- is  H~_{n-2}(lk_{Delta_n} P) = 0  at HEIGHT-1 vertices a THEOREM or a
small-n coincidence?

The question (mg-e08a's single named follow-up, restated by mg-1b3b at
docs/OneThird-mg52c4-PerPoset-Subposet-Question.md Sec.5).  Verified by measurement at
n = 3, 4, 5 only; every case is a one-degree near-miss and no dimension argument forces it.

WHAT THIS INSTRUMENT DOES

1.  REDUCTION.  For height-1 P, mg-52c4 Theorem A (A2) gives Delta(Lbar(P)) ~ S^{c-2}, so the
    join formula turns the target into

        H~_{n-2}(lk P) = H~_{n-c-1}(U),      U := Delta(upP \\ {P}),   c := |Comp(P)|.

    (Already recorded by mg-e08a Sec.7.  Re-derived and re-measured here, not imported.)

2.  CROSSCUT.  U is astronomically large for small c (its vertex set is most of PPF_n).  But
    M := {P} + (upP \\ {P}) + 1hat is a LATTICE (meet = intersection of relation sets), so
    Bjorner's crosscut theorem applies to its atoms:

        U  ~  Gamma(P) := { A subset of Atoms(P) : tc(P u UA) is a non-total partial order }

    where Atoms(P) = the minimal proper refinements of P = the DISTINCT tc(P u {r}) that are
    still non-total.  Gamma(P) lives on at most n(n-1) - 2c vertices.  This is the whole
    computational content of the ticket: it turns an infeasible measurement into a cheap one.

3.  MEASUREMENT.  beta~_{n-c-1}(Gamma(P)) for every height-1 iso class at n = 3..NMAX.

4.  CONTROLS.  The crosscut reduction is checked against a DIRECT computation of
    Delta(upP \\ {P}) and of lk_{Delta_n}(P) at n = 3, 4 (all vertices, not only height-1),
    and the join formula is checked the same way.  Negative controls are in Sec. CONTROLS.

Everything is re-implemented from scratch (stdlib only); nothing is imported from the repo, so
this is an independent check of mg-e08a's numbers as well as a new measurement.

Run:  /usr/bin/python3 scripts/compat_geom_mg72e4_height1_anchor.py
"""

import itertools
import json
import os
import sys
from collections import defaultdict

PRIMES = (1_000_003, 999_983)


# --------------------------------------------------------------------------- posets
def tc(pairs, n):
    """Transitive closure of a set of ordered pairs on range(n).
    Returns a frozenset, or None if the relation has a cycle (not a partial order)."""
    adj = [0] * n
    for (a, b) in pairs:
        if a == b:
            return None
        adj[a] |= 1 << b
    for k in range(n):
        bit = 1 << k
        for i in range(n):
            if adj[i] & bit:
                adj[i] |= adj[k]
    for i in range(n):
        if adj[i] & (1 << i):
            return None
    return frozenset((i, j) for i in range(n) for j in range(n) if adj[i] >> j & 1)


def is_total(P, n):
    return len(P) == n * (n - 1) // 2


def height_at_least_2(P):
    """P has a 3-chain iff some pair of its relations composes."""
    tails = defaultdict(set)
    for (a, b) in P:
        tails[a].add(b)
    for (a, b) in P:
        if tails[b]:
            return True
    return False


def incomparable_pairs(P, n):
    comp = set()
    for (a, b) in P:
        comp.add((a, b) if a < b else (b, a))
    return [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in comp]


def all_partial_orders(n):
    """Every transitively closed acyclic relation on range(n), by BFS upward from the empty one."""
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    seen = {frozenset()}
    frontier = [frozenset()]
    while frontier:
        nxt = []
        for P in frontier:
            for r in pairs:
                if r in P:
                    continue
                Q = tc(P | {r}, n)
                if Q is not None and Q not in seen:
                    seen.add(Q)
                    nxt.append(Q)
        frontier = nxt
    return seen


def ppf(n):
    """PPF_n : nonempty, non-total partial orders on [n]."""
    return [P for P in all_partial_orders(n) if P and not is_total(P, n)]


# ------------------------------------------------------------------ height-1 enumeration
def height1_posets(n):
    """Every height-1 partial order on range(n) with at least one relation.
    Height 1 <=> no two relations compose <=> no element is both a head and a tail."""
    out = set()
    elts = list(range(n))
    for k in range(1, n):
        for lower in itertools.combinations(elts, k):
            upper = [x for x in elts if x not in lower]
            cand = [(a, b) for a in lower for b in upper]
            for m in range(1, len(cand) + 1):
                for E in itertools.combinations(cand, m):
                    out.add(frozenset(E))
    return out


def canonical(P, n):
    best = None
    for perm in itertools.permutations(range(n)):
        img = frozenset((perm[a], perm[b]) for (a, b) in P)
        key = tuple(sorted(img))
        if best is None or key < best:
            best = key
    return best


def height1_iso_classes(n):
    """One representative per isomorphism class, with the class size."""
    reps = {}
    counts = defaultdict(int)
    for P in height1_posets(n):
        k = canonical(P, n)
        counts[k] += 1
        if k not in reps:
            reps[k] = P
    return [(reps[k], counts[k]) for k in sorted(reps)]


# --------------------------------------------------------------------------- homology
def _rank_mod_p(cols, nrows, p):
    """Rank of a sparse matrix given as a list of {row: coeff} columns."""
    pivots = {}
    rank = 0
    for col in cols:
        c = {r: v % p for r, v in col.items() if v % p}
        while c:
            r = max(c)
            if r not in pivots:
                inv = pow(c[r], p - 2, p)
                pivots[r] = {rr: (vv * inv) % p for rr, vv in c.items()}
                rank += 1
                break
            f = c[r]
            pr = pivots[r]
            for rr, vv in pr.items():
                nv = (c.get(rr, 0) - f * vv) % p
                if nv:
                    c[rr] = nv
                elif rr in c:
                    del c[rr]
    return rank


def reduced_betti_range(faces_by_dim, dmax):
    """Reduced Betti numbers in degrees -1 .. dmax, from faces of dimension <= dmax+1.

    faces_by_dim[d] is a list of sorted tuples of vertices, len == d+1.
    Uses the AUGMENTED chain complex: C_{-1} = field, generated by the empty face.
    """
    total = sum(len(v) for v in faces_by_dim.values())
    if total == 0:
        return {-1: 1}
    results = []
    for p in PRIMES:
        idx = {d: {f: i for i, f in enumerate(faces_by_dim.get(d, []))} for d in range(-1, dmax + 2)}
        idx[-1] = {(): 0}
        ranks = {}
        for d in range(0, dmax + 2):
            fs = faces_by_dim.get(d, [])
            lower = idx[d - 1]
            cols = []
            for f in fs:
                col = {}
                for i in range(len(f)):
                    j = lower[f[:i] + f[i + 1:]]
                    col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
                cols.append(col)
            ranks[d] = _rank_mod_p(cols, max(1, len(lower)), p)
        betti = {}
        for d in range(-1, dmax + 1):
            ndim = 1 if d == -1 else len(faces_by_dim.get(d, []))
            betti[d] = ndim - ranks.get(d, 0) - ranks.get(d + 1, 0)
        results.append(tuple(betti[d] for d in range(-1, dmax + 1)))
    if len(set(results)) != 1:
        raise RuntimeError("prime disagreement: %r" % (results,))
    return {d: results[0][d + 1] for d in range(-1, dmax + 1)}


def order_complex_faces(elements, dmax=None):
    """All chains of a poset given as a list of frozensets ordered by inclusion,
    grouped by dimension (dim = len(chain) - 1).  dmax caps the dimension."""
    elts = sorted(elements, key=lambda P: (len(P), sorted(P)))
    n_e = len(elts)
    pos = {e: i for i, e in enumerate(elts)}
    up = [[] for _ in range(n_e)]
    for i, a in enumerate(elts):
        for j, b in enumerate(elts):
            if i != j and a < b:
                up[i].append(j)
    faces = defaultdict(list)
    for i in range(n_e):
        faces[0].append((i,))
    frontier = [(i,) for i in range(n_e)]
    d = 0
    while frontier and (dmax is None or d < dmax):
        nxt = []
        for ch in frontier:
            for j in up[ch[-1]]:
                nxt.append(ch + (j,))
        d += 1
        if nxt:
            faces[d] = nxt
        frontier = nxt
    # vertices are indices; chains are increasing in the poset order, but the tuples must be
    # sorted for the boundary map: elts is sorted by (size, content) which refines inclusion.
    return {d: [tuple(sorted(f)) for f in v] for d, v in faces.items() if v}


# --------------------------------------------------------------------------- crosscut
def atoms_of_upper(P, n):
    """The minimal elements of upP \\ {P} inside PPF_n = the distinct non-total tc(P u {r})."""
    inc = incomparable_pairs(P, n)
    out = {}
    for (x, y) in inc:
        for r in ((x, y), (y, x)):
            Q = tc(P | {r}, n)
            if Q is None or is_total(Q, n):
                continue
            out.setdefault(Q, r)
    # keep only the MINIMAL ones (an atom must not contain another atom properly)
    keys = list(out)
    minimal = [Q for Q in keys if not any(R < Q for R in keys)]
    return sorted(minimal, key=lambda Q: (len(Q), sorted(Q)))


def gamma_faces(P, n, atoms, dmax):
    """Faces of the crosscut complex Gamma(P), by dimension, up to dimension dmax.

    A subset A of atoms is a face iff tc(P u UA) is a non-total partial order.
    Built by DFS so that non-faces prune their supersets (Gamma is a simplicial complex:
    if tc of a union is non-total then so is tc of any sub-union, since it is contained in it).
    """
    m = len(atoms)
    faces = defaultdict(list)
    if m == 0:
        return faces

    def rec(prefix, cur):
        d = len(prefix) - 1
        faces[d].append(tuple(prefix))
        if d >= dmax:
            return
        for j in range(prefix[-1] + 1 if prefix else 0, m):
            U = cur | atoms[j]
            Q = tc(U, n)
            if Q is None or is_total(Q, n):
                continue
            rec(prefix + [j], Q)

    for i in range(m):
        rec([i], atoms[i])
    return faces


# --------------------------------------------------------------------------- link (direct)
def upper_link_poset(P, n, universe):
    return [Q for Q in universe if P < Q]


def link_poset(P, n, universe):
    return [Q for Q in universe if P < Q or Q < P]


def lower_poset(P, n, universe):
    return [Q for Q in universe if Q < P]


def betti_vector(elements, dmax=None):
    """Full reduced Betti vector of the order complex, as a dict degree -> value."""
    if not elements:
        return {-1: 1}
    faces = order_complex_faces(elements, dmax=None if dmax is None else dmax + 1)
    top = max(faces)
    return reduced_betti_range(faces, top)


def join_predicted(b1, b2, dmax):
    """Reduced Betti of X * Y from those of X and Y (field coefficients):
    H~_k(X*Y) = sum_{i+j=k-1} H~_i(X) x H~_j(Y)."""
    out = defaultdict(int)
    for i, v in b1.items():
        for j, w in b2.items():
            if v and w:
                out[i + j + 1] += v * w
    return {d: out.get(d, 0) for d in range(-1, dmax + 1)}


# --------------------------------------------------------------------------- report
def main():
    NMAX = int(os.environ.get("MG72E4_NMAX", "6"))
    report = {"ticket": "mg-72e4", "nmax": NMAX}
    failures = []

    # ---------------- CONTROL H1: the homology routine against known answers
    def facets_to_faces(facets):
        fs = set()
        for F in facets:
            for k in range(1, len(F) + 1):
                for s in itertools.combinations(sorted(F), k):
                    fs.add(s)
        by = defaultdict(list)
        for s in fs:
            by[len(s) - 1].append(s)
        return {d: sorted(v) for d, v in by.items()}

    h1 = {}
    for k in range(1, 6):  # boundary of a k-simplex is S^{k-1}
        facets = list(itertools.combinations(range(k + 1), k))
        b = reduced_betti_range(facets_to_faces(facets), k - 1)
        h1["bd_simplex_%d" % k] = {str(d): v for d, v in b.items()}
        want = {d: (1 if d == k - 1 else 0) for d in range(-1, k)}
        if b != want:
            failures.append("H1 bd_simplex_%d: %r != %r" % (k, b, want))
    # Z_7 torus (the standard 7-vertex triangulation)
    torus = [tuple(sorted(((i + a) % 7 for a in s))) for i in range(7) for s in ((0, 1, 3), (0, 1, 5))]
    b = reduced_betti_range(facets_to_faces(torus), 2)
    h1["torus_Z7"] = {str(d): v for d, v in b.items()}
    if (b.get(0), b.get(1), b.get(2)) != (0, 2, 1):
        failures.append("H1 torus: %r" % (b,))
    # empty complex
    if reduced_betti_range({}, 2) != {-1: 1}:
        failures.append("H1 empty complex")
    h1["empty"] = "S^{-1}"
    report["control_H1_known_answers"] = h1

    # ---------------- CONTROLS at n = 3, 4: crosscut vs direct, and the join formula
    cross = {}
    for n in (3, 4):
        universe = ppf(n)
        rows = []
        for P in sorted(universe, key=lambda Q: (len(Q), sorted(Q))):
            up = upper_link_poset(P, n, universe)
            lo = lower_poset(P, n, universe)
            lk = link_poset(P, n, universe)
            b_up_direct = betti_vector(up)
            atoms = atoms_of_upper(P, n)
            g = gamma_faces(P, n, atoms, dmax=len(atoms))
            b_gamma = reduced_betti_range(g, max(g) if g else 0) if g else {-1: 1}
            dmax = max(list(b_up_direct) + list(b_gamma))
            norm = lambda b: tuple(b.get(d, 0) for d in range(-1, dmax + 1))
            ok_cross = norm(b_up_direct) == norm(b_gamma)
            b_lo = betti_vector(lo)
            b_lk = betti_vector(lk)
            dmax2 = max(list(b_lk) + [-1])
            pred = join_predicted(b_lo, b_up_direct, dmax2)
            ok_join = tuple(b_lk.get(d, 0) for d in range(-1, dmax2 + 1)) == \
                      tuple(pred.get(d, 0) for d in range(-1, dmax2 + 1))
            anchor = b_lk.get(n - 2, 0)
            if not ok_cross:
                failures.append("CROSSCUT n=%d P=%r: direct %r vs Gamma %r"
                                % (n, sorted(P), b_up_direct, b_gamma))
            if not ok_join:
                failures.append("JOIN n=%d P=%r" % (n, sorted(P)))
            rows.append({
                "P": sorted(map(list, P)), "c": len(P),
                "height_ge_2": height_at_least_2(P),
                "n_atoms": len(atoms),
                "betti_upper_direct": {str(d): v for d, v in b_up_direct.items()},
                "betti_gamma": {str(d): v for d, v in b_gamma.items()},
                "crosscut_agrees": ok_cross,
                "join_formula_agrees": ok_join,
                "betti_link": {str(d): v for d, v in b_lk.items()},
                "anchor_degree_betti": anchor,
            })
        cross[str(n)] = {
            "vertices": len(rows),
            "crosscut_agrees_all": all(r["crosscut_agrees"] for r in rows),
            "join_agrees_all": all(r["join_formula_agrees"] for r in rows),
            "anchor_nonzero_count": sum(1 for r in rows if r["anchor_degree_betti"]),
            "links_non_contractible": sum(
                1 for r in rows if any(v for d, v in r["betti_link"].items())),
            "rows": rows,
        }
    report["control_crosscut_and_join"] = cross

    # ---------------- the measurement: height-1 iso classes, n = 3 .. NMAX
    meas = {}
    for n in range(3, NMAX + 1):
        d_needed = lambda c: n - c - 1
        classes = height1_iso_classes(n)
        rows = []
        for P, mult in classes:
            c = len(P)
            d = d_needed(c)
            atoms = atoms_of_upper(P, n)
            if d < -1:
                bd, bnext = 0, None
                gsize = len(atoms)
            elif d == -1:
                bd = 1 if not atoms else 0
                bnext = None
                gsize = len(atoms)
            else:
                g = gamma_faces(P, n, atoms, dmax=d + 2)
                b = reduced_betti_range(g, d + 1) if g else {-1: 1}
                bd = b.get(d, 0)
                bnext = b.get(d + 1, 0)
                gsize = len(atoms)
            rows.append({
                "P": sorted(map(list, P)), "c": c, "class_size": mult,
                "needed_degree": d, "n_atoms": gsize,
                "betti_needed": bd, "betti_one_above": bnext,
            })
        bad = [r for r in rows if r["betti_needed"]]
        meas[str(n)] = {
            "iso_classes": len(rows),
            "labeled_total": sum(r["class_size"] for r in rows),
            "violations": len(bad),
            "violating_classes": bad,
            "near_miss_classes": sum(1 for r in rows if r["betti_one_above"]),
            "rows": rows,
        }
        print("n=%d: %d height-1 iso classes (%d labeled), %d violations, %d one-degree near-misses"
              % (n, len(rows), meas[str(n)]["labeled_total"], len(bad),
                 meas[str(n)]["near_miss_classes"]), flush=True)
    report["measurement_height1"] = meas

    # ---------------- NEGATIVE CONTROLS
    neg = {}
    # N1: the SWAPPED claim -- "the needed degree is n-c" -- must go RED.
    swapped_red = 0
    swapped_total = 0
    for n in range(4, NMAX + 1):
        for r in meas[str(n)]["rows"]:
            if r["betti_one_above"] is not None:
                swapped_total += 1
                if r["betti_one_above"]:
                    swapped_red += 1
    neg["N1_swapped_degree_is_n_minus_c"] = {
        "claim": "beta~_{n-c}(Gamma) = 0 as well",
        "instances": swapped_total, "refuted_on": swapped_red,
        "discriminating": swapped_red > 0,
    }
    # N2: perturb -- for a HEIGHT>=2 poset the lower factor is contractible, so the link is
    # contractible; the anchor-degree Betti of the link must be 0 for a DIFFERENT reason.
    n = 4
    universe = ppf(n)
    h2 = [r for r in cross["4"]["rows"] if r["height_ge_2"]]
    neg["N2_height_ge_2_links"] = {
        "count": len(h2),
        "all_links_contractible": all(
            not any(v for v in r["betti_link"].values()) for r in h2),
    }
    # N3: the instrument must be able to REPORT a non-zero anchor.  Feed it a complex whose
    # anchor degree is non-zero: the link of a height-1 vertex at n=4 in degree 3 (= n-1).
    n3 = [r for r in cross["4"]["rows"] if r["betti_link"].get("3", 0)]
    neg["N3_instrument_can_see_nonzero"] = {
        "n": 4, "degree": 3,
        "vertices_with_nonzero_beta3": len(n3),
        "values": sorted(set(r["betti_link"]["3"] for r in n3)),
    }
    report["negative_controls"] = neg

    report["ALL_PASS"] = not failures
    report["failures"] = failures

    out = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "data", "onethird-mg72e4-height1-anchor.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("ALL_PASS =", report["ALL_PASS"])
    if failures:
        for x in failures[:20]:
            print("  FAIL", x)
    print("wrote", out)
    return 0 if report["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
