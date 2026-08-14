#!/usr/bin/env /usr/bin/python3
"""mg-dd84 -- the LAST HOLE in the n = 7 min-margin denominator: the 3 height-1 classes
at c <= 2 (252 of 227 892 labelled vertices) bounded only at `margin >= 1`.

WHAT WAS OPEN
-------------
mg-72e4 published "min margin 4" at n = 7; mg-9cd1 audited it and found the denominator
unstated (its D2); mg-0f24 derived it -- 146 -> 148 -> **160 of 163**, and NOT 148 + 14 = 162,
because the two stars are in both sets.  Three classes were left over:

    c = 1   P = {(0,1)}                42 labelled vertices, 30 atoms, d = 5
    c = 2   P = {(0,1),(0,2)}  ("V")  105 labelled vertices, 26 atoms, d = 4
    c = 2   P = {(0,2),(1,2)}  ("^")  105 labelled vertices, 26 atoms, d = 4

`margin >= 4` needs beta~ through degree 8 for the first and 7 for the other two.  p9cd1
stopped short of that for a stated RESOURCE reason, not a mathematical one, and named
mg-bcd7's cone/LES decomposition as the route to look for before brute force.

WHAT THIS INSTRUMENT DOES
-------------------------
It does not compute Gamma(P): Gamma has ~10^6 faces through the degrees in question and worse
above them.  It extends mg-bcd7's decomposition

        Gamma(P) = X \\ F ,     X contractible (a cone),     F an upward-closed filter

from "compute two Betti numbers" to "identify the filter's chain complex exactly", which
closes every degree at once rather than four more of them:

  L1  X IS A CONE, in one of two DUAL forms.  Either some element s of [n] is carried by NO
      atom as a head (no atom's relation set contains any pair (y, s)) -- then s is a source of
      tc(P u US) for every face S of X and adjoining the atom alpha_0 = tc(P u {(s, x)}), whose
      new pairs all leave s, can never close a cycle; or some element t is carried by no atom
      as a TAIL, and alpha_0 = tc(P u {(x, t)}) works the same way.  Either way X is a cone
      with apex alpha_0 and H~_*(X) = 0.  P = {(0,1),(0,2)} needs the first form and its dual
      P = {(0,2),(1,2)} needs the second; writing only the first is what this instrument's own
      L1 check caught, by reporting "X not shown to be a cone" for the second.

  L2  F SPLITS OVER THE TOTAL ORDERS IT REALISES.  Every face of F has tc(P u US) equal to a
      total order L containing P, determined by the face.  A boundary face either stays in F
      with the SAME L or leaves F.  So the relative chain complex C_*(X, Gamma) -- free on F
      -- is a DIRECT SUM over the realised L.

  L3  EACH SUMMAND IS THE AUGMENTED CHAIN COMPLEX OF A SIMPLEX.  A cover pair (x, y) of L is
      contained in exactly one atom that is contained in L, namely tc(P u {(x,y)}); so the
      faces of F with order L are exactly Req(L) u T for T a subset of
      Opt(L) := A_L \\ Req(L), where Req(L) carries the covers of L not already in P and A_L is
      the set of atoms contained in L.  Deleting an element of Req leaves F; deleting one of
      Opt stays inside the same block.  That is the augmented chain complex of the full
      simplex on Opt(L), shifted by |Req(L)|.

  L4  Opt(L) IS NON-EMPTY for every realised L, at every n >= 4 for all three families.  The
      augmented chain complex of a simplex on a non-empty vertex set is EXACT.

  ==>  H_k(X, Gamma) = 0 for EVERY k, so H~_k(Gamma) = 0 for every k.

L4 is the hypothesis that fails, and is checked here to fail, at n = 3 -- where these
complexes really are non-trivial (Gamma = S^0; mg-72e4's "all 12 links at n = 3
non-contractible").  The instrument reports that rather than hiding it, because a hypothesis
that is never false is not doing any work.

COEFFICIENTS -- read this before quoting anything
-------------------------------------------------
The exactness in L3/L4 is over Z: the relative chain complex is free and each summand is exact
as a complex of free abelian groups.  So the conclusion is Z-acyclic, hence Q-acyclic.  It is
NOT a claim that Gamma(P) is contractible and this instrument never computes a homotopy group.
The mod-p ranks below CORROBORATE the vanishing in the degrees they reach; they do not
establish the integral statement.  In the top two degrees only p = 2 is affordable, and that
is the safe direction: rank_2 <= rank_Q so beta_Q <= beta_2, and beta_2 = 0 forces rational
vanishing (mg-9cd1 Sec.4.3's argument, reused).

Run: /usr/bin/python3 scripts/compat_geom_mgdd84_n7_cle2_margin.py
Output: data/onethird-mgdd84-n7-cle2-margin.json
stdlib only; nothing is imported from the repo except in step V0, where mg-72e4's own atom
routine, tc and rank routine are used deliberately as an external control.
"""

import itertools
import json
import os
import random
import sys
import time
from collections import defaultdict

PRIMES = (2, 3, 5, 7, 46337, 999983, 1000003)
SMALL_PRIMES = (2, 1000003)

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
OUT = os.path.join(REPO, "data", "onethird-mgdd84-n7-cle2-margin.json")

# How many columns a single BLOCK may have before this instrument drops from all seven primes
# to p = 2 alone.  A budget, not a feasibility bound -- and p = 2 is the direction that is
# safe (beta_Q <= beta_2, so a vanishing mod-2 reading forces rational vanishing).
ALL_PRIMES_CAP = 20000
# How many columns a degree may have before the un-blocked GLOBAL rank -- the check that the
# block decomposition is not doing the work -- is skipped as too expensive.
GLOBAL_CAP = 50000

FAMILIES = [
    ("c1", "P = {(0,1)}", lambda n: frozenset([(0, 1)])),
    ("c2_V", "P = {(0,1),(0,2)}", lambda n: frozenset([(0, 1), (0, 2)])),
    ("c2_L", "P = {(0,2),(1,2)}", lambda n: frozenset([(0, 2), (1, 2)])),
]


# --------------------------------------------------------------------------- relations
def tc(pairs, n):
    """Transitive closure on range(n) as a frozenset of pairs; None if it has a cycle.
    Written from scratch; V0 checks it against mg-72e4's tc on 2 000 random relations."""
    adj = [0] * n
    for (a, b) in pairs:
        if a == b:
            return None
        adj[a] |= 1 << b
    for k in range(n):
        bk = 1 << k
        ak = adj[k]
        for i in range(n):
            if adj[i] & bk:
                adj[i] |= ak
    for i in range(n):
        if adj[i] >> i & 1:
            return None
    return frozenset((i, j) for i in range(n) for j in range(n) if adj[i] >> j & 1)


def is_total(R, n):
    return len(R) == n * (n - 1) // 2


def atoms_of(P, n):
    """Minimal elements of {Q in PPF_n : Q strictly contains P}: the minimal distinct non-total
    tc(P u {r}).  Returns a sorted list of (relation set, generating pair)."""
    cand = {}
    for x in range(n):
        for y in range(n):
            if x == y or (x, y) in P:
                continue
            Q = tc(P | {(x, y)}, n)
            if Q is None or is_total(Q, n):
                continue
            cand.setdefault(Q, (x, y))
    keys = list(cand)
    minimal = [Q for Q in keys if not any(R < Q for R in keys)]
    minimal.sort(key=lambda Q: (len(Q), sorted(Q)))
    return [(Q, cand[Q]) for Q in minimal]


def _binom(a, b):
    if b < 0 or b > a:
        return 0
    r = 1
    for i in range(b):
        r = r * (a - i) // (i + 1)
    return r


# --------------------------------------------------------------------------- linear algebra
def rank_mod_p(cols, p):
    """Rank over F_p of a sparse matrix given as a list of {row: coeff} columns."""
    pivots = {}
    rank = 0
    for col in cols:
        c = {r: v % p for r, v in col.items() if v % p}
        while c:
            r = max(c)
            pr = pivots.get(r)
            if pr is None:
                inv = pow(c[r], p - 2, p)
                pivots[r] = {rr: (vv * inv) % p for rr, vv in c.items()}
                rank += 1
                break
            f = c[r]
            for rr, vv in pr.items():
                nv = (c.get(rr, 0) - f * vv) % p
                if nv:
                    c[rr] = nv
                elif rr in c:
                    del c[rr]
    return rank


def rank_mod_2_bitset(cols):
    """Rank over F_2, columns as {row: coeff} dicts, via big-int bitsets.  Same answer as
    rank_mod_p(cols, 2) -- V0 checks that on the real matrices where both are affordable."""
    pivots = {}
    rank = 0
    for col in cols:
        v = 0
        for r, c in col.items():
            if c & 1:
                v ^= 1 << r
        while v:
            top = v.bit_length() - 1
            pv = pivots.get(top)
            if pv is None:
                pivots[top] = v
                rank += 1
                break
            v ^= pv
    return rank


def reduced_betti(faces_by_dim, dmax, primes=SMALL_PRIMES):
    """Reduced Betti numbers in degrees -1..dmax; needs faces through dimension dmax+1.
    Augmented complex: C_{-1} generated by the empty face."""
    out = {}
    for p in primes:
        idx = {-1: {(): 0}}
        for d in range(0, dmax + 2):
            idx[d] = {f: i for i, f in enumerate(faces_by_dim.get(d, []))}
        ranks = {}
        for d in range(0, dmax + 2):
            lower = idx[d - 1]
            cols = []
            for f in faces_by_dim.get(d, []):
                col = {}
                for i in range(len(f)):
                    j = lower[f[:i] + f[i + 1:]]
                    col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
                cols.append(col)
            ranks[d] = rank_mod_p(cols, p)
        b = []
        for d in range(-1, dmax + 1):
            ndim = 1 if d == -1 else len(faces_by_dim.get(d, []))
            b.append(ndim - ranks.get(d, 0) - ranks.get(d + 1, 0))
        out[p] = tuple(b)
    return out


# --------------------------------------------------------------------------- decomposition
def structure(P, n):
    """L1-L4 for one class at one n: atoms, the cone apex, the realised total orders and their
    Req/Opt.  Everything here is measured on the poset, nothing is assumed."""
    at = atoms_of(P, n)
    atoms = [a for a, _ in at]
    gens = [g for _, g in at]
    aidx = {A: i for i, A in enumerate(atoms)}

    # L1 comes in a source form and a DUAL sink form, and the three classes need both: the
    # "V" P = {(0,1),(0,2)} has a source no atom points into, the "^" P = {(0,2),(1,2)} has a
    # SINK no atom points out of.  Only the source form was written first, and the c2_L class
    # is what caught it -- the instrument reported "X not shown to be a cone" rather than
    # quietly using an unjustified LES.
    heads = {y for A in atoms for (_, y) in A}
    tails = {x for A in atoms for (x, _) in A}
    sources = [s for s in range(n) if s not in heads]
    sinks = [t for t in range(n) if t not in tails]
    apex, apex_form = None, None
    for s in sources:
        for i, g in enumerate(gens):
            if g[0] == s:
                apex, apex_form = i, "source"
                break
        if apex is not None:
            break
    if apex is None:
        for t in sinks:
            for i, g in enumerate(gens):
                if g[1] == t:
                    apex, apex_form = i, "sink"
                    break
            if apex is not None:
                break

    realised = []
    n_tot = 0
    mults = set()
    for perm in itertools.permutations(range(n)):
        L = frozenset((perm[i], perm[j]) for i in range(n) for j in range(i + 1, n))
        if not (P <= L):
            continue
        n_tot += 1
        covers = [(perm[i], perm[i + 1]) for i in range(n - 1)]
        req, ok = [], True
        for cv in covers:
            if cv in P:
                continue
            A = tc(P | {cv}, n)
            if A not in aidx:
                ok = False
                break
            req.append(aidx[A])
        if not ok:
            continue
        AL = [i for i, B in enumerate(atoms) if B <= L]
        for cv in covers:
            if cv in P:
                continue
            mults.add(sum(1 for i in AL if cv in atoms[i]))
        req = tuple(sorted(set(req)))
        realised.append((L, req, tuple(sorted(set(AL) - set(req)))))
    return {
        "atoms": atoms, "gens": gens, "apex": apex, "apex_form": apex_form,
        "sources": sources, "sinks": sinks,
        "realised": realised, "n_total_orders": n_tot,
        "cover_atom_multiplicities": sorted(mults),
    }


def cone_check(P, n, atoms, apex, upto):
    """Exhaustive corroboration of L1: adjoining the apex atom to any face of X of size <= upto
    keeps it in X."""
    if apex is None:
        return 0, False
    checked = 0
    for k in range(0, upto + 1):
        for S in itertools.combinations(range(len(atoms)), k):
            if apex in S:
                continue
            U = set(P)
            for i in S:
                U |= atoms[i]
            if tc(U, n) is None:
                continue
            checked += 1
            if tc(U | atoms[apex], n) is None:
                return checked, False
    return checked, True


def enumerate_filter(P, n, atoms, realised, dmax, shortcut=True):
    """Faces of F of dimension <= dmax, by upward BFS from the minimal faces Req(L), with
    membership decided by the RAW predicate `tc(P u US) is a total order`.

    shortcut=True additionally skips a candidate atom whose relation set is not contained in
    the parent's total order L.  That skip is exact -- if alpha is not inside L then
    tc(P u US u alpha) strictly contains the total order L and so has a cycle -- and V6 runs
    the enumeration BOTH ways at n = 4, 5, 6 and checks the outputs are identical."""
    faces = defaultdict(list)
    order_of = {}          # face -> a small integer id for its total order (interned)
    ids = {}               # total order -> id
    orders = []            # id -> total order
    frontier = []
    for L, req, _opt in realised:
        f = tuple(req)
        if f in order_of:
            continue
        U = set(P)
        for i in f:
            U |= atoms[i]
        R = tc(U, n)
        if R is None or not is_total(R, n):
            raise RuntimeError("Req(L) does not generate a total order")
        if R not in ids:
            ids[R] = len(orders)
            orders.append(R)
        order_of[f] = ids[R]
        faces[len(f) - 1].append(f)
        frontier.append(f)
    while frontier and (len(frontier[0]) - 1) < dmax:
        nxt = []
        for f in frontier:
            L = orders[order_of[f]]
            fs = set(f)
            for i in range(len(atoms)):
                if i in fs:
                    continue
                if shortcut and not (atoms[i] <= L):
                    continue
                g = tuple(sorted(f + (i,)))
                if g in order_of:
                    continue
                U = set(P)
                for j in g:
                    U |= atoms[j]
                R = tc(U, n)
                if R is None or not is_total(R, n):
                    continue
                if R not in ids:
                    ids[R] = len(orders)
                    orders.append(R)
                order_of[g] = ids[R]
                faces[len(g) - 1].append(g)
                nxt.append(g)
        frontier = nxt
    for k in faces:
        faces[k].sort()
    return faces, order_of, orders


def minimal_filter_faces(P, n, atoms, upto):
    """Every subset of the atoms of size <= upto whose tc is a total order, minimal ones only,
    by DFS with pruning.  A brute-force control on the upward enumeration: if F had a minimal
    face larger than every Req(L), the BFS could miss a whole block."""
    found = set()

    def rec(prefix, cur, start):
        for i in range(start, len(atoms)):
            U = cur | atoms[i]
            R = tc(U, n)
            if R is None:
                continue                    # cyclic: every superset is too
            nf = prefix + (i,)
            if is_total(R, n):
                found.add(nf)               # in F, and minimal along this branch
                continue
            if len(nf) < upto:
                rec(nf, R, i + 1)

    rec((), frozenset(P), 0)
    return {f for f in found if not any(set(g) < set(f) for g in found)}


def relative_homology(faces, order_of, dmax):
    """H_k(X, Gamma) for k <= dmax from the relative chain complex, which is free on F.

    Every degree is computed BLOCKED (per total order, ranks summed) and, where the degree is
    small enough, GLOBALLY as one matrix as well; the two must agree.  The blocked route is
    legitimate only because `boundary_crossings` is 0, which is measured below, not assumed."""
    dims = {k: len(v) for k, v in faces.items()}
    idx = {k: {f: i for i, f in enumerate(v)} for k, v in faces.items()}
    ranks = {}
    ranks_global = {}
    primes_used = {}
    for k in range(0, dmax + 2):
        fs = faces.get(k, [])
        if not fs:
            ranks[k] = {p: 0 for p in PRIMES}
            primes_used[k] = list(PRIMES)
            ranks_global[k] = None
            continue
        lower = idx.get(k - 1, {})
        cols, blocks = [], defaultdict(list)
        for f in fs:
            col = {}
            for i in range(len(f)):
                j = lower.get(f[:i] + f[i + 1:])
                if j is None:
                    continue              # the face left F: zero in the relative complex
                col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
            cols.append(col)
            blocks[order_of[f]].append(col)
        biggest = max(len(v) for v in blocks.values())
        ps = PRIMES if biggest <= ALL_PRIMES_CAP else (2,)
        primes_used[k] = list(ps)
        r = {}
        for p in ps:
            r[p] = sum(rank_mod_p(v, p) for v in blocks.values())
        if 2 in ps:                       # the bitset route, as a second reading of p = 2
            r2 = sum(rank_mod_2_bitset(v) for v in blocks.values())
            if r2 != r[2]:
                raise RuntimeError("bitset and sparse rank disagree at p = 2, degree %d" % k)
        ranks[k] = r
        if len(fs) <= GLOBAL_CAP:
            ranks_global[k] = {p: rank_mod_p(cols, p) for p in ps}
        else:
            ranks_global[k] = None
    H = {}
    for k in range(0, dmax + 1):
        ps = sorted(set(primes_used[k]) & set(primes_used[k + 1]))
        vals = {p: dims.get(k, 0) - ranks[k].get(p, 0) - ranks[k + 1].get(p, 0) for p in ps}
        H[str(k)] = {"primes": ps, "value": sorted(set(vals.values()))}
    return {
        "dims": {str(k): v for k, v in sorted(dims.items())},
        "rank_blocked": {str(k): {str(p): v for p, v in sorted(r.items())}
                         for k, r in sorted(ranks.items())},
        "rank_global": {str(k): (None if g is None else {str(p): v for p, v in sorted(g.items())})
                        for k, g in sorted(ranks_global.items())},
        "global_and_blocked_agree": all(
            g is None or all(g[p] == ranks[k][p] for p in g) for k, g in ranks_global.items()),
        "H": H,
    }


def analyse(P, n, need_dim, cone_upto=None, do_minimal=True):
    """Full analysis of one class at one n.  need_dim = top relative degree wanted;
    beta~_{need_dim - 1}(Gamma) falls out of it."""
    res = {"n": n, "P": sorted(map(list, P)), "c": len(P), "d_needed_degree": n - len(P) - 1}
    st = structure(P, n)
    atoms, realised = st["atoms"], st["realised"]
    res["n_atoms"] = len(atoms)
    res["L1_sources_carried_by_no_atom_head"] = st["sources"]
    res["L1_sinks_carried_by_no_atom_tail"] = st["sinks"]
    res["L1_apex_form"] = st["apex_form"]
    res["L1_apex_generating_pair"] = list(st["gens"][st["apex"]]) if st["apex"] is not None else None
    res["L1_is_cone"] = st["apex"] is not None
    if cone_upto is None:
        cone_upto = 4 if len(atoms) >= 26 else 6
    ck, cok = cone_check(P, n, atoms, st["apex"], cone_upto)
    res["L1_cone_faces_checked"] = ck
    res["L1_cone_check_size"] = cone_upto
    res["L1_cone_check_passes"] = cok

    res["L2_total_orders_containing_P"] = st["n_total_orders"]
    res["L2_realised_total_orders"] = len(realised)
    res["L3_cover_atom_multiplicities"] = st["cover_atom_multiplicities"]
    res["L3_req_sizes"] = sorted({len(r[1]) for r in realised})
    res["L4_opt_sizes"] = sorted({len(r[2]) for r in realised})
    res["L4_opt_all_nonempty"] = bool(realised) and all(len(r[2]) > 0 for r in realised)

    closed = defaultdict(int)
    for _, req, opt in realised:
        for t in range(len(opt) + 1):
            closed[len(req) + t - 1] += _binom(len(opt), t)
    res["F_closed_form_by_dim"] = {str(k): v for k, v in sorted(closed.items())}

    t0 = time.time()
    faces, order_of, orders = enumerate_filter(P, n, atoms, realised, need_dim + 1)
    res["F_enum_seconds"] = round(time.time() - t0, 2)
    res["F_direct_by_dim"] = {str(k): len(v) for k, v in sorted(faces.items())}
    res["F_closed_form_matches_direct"] = all(len(v) == closed[k] for k, v in faces.items())

    if do_minimal:
        mx = max(len(r[1]) for r in realised) if realised else 0
        mins = minimal_filter_faces(P, n, atoms, mx)
        res["F_minimal_faces_bruteforce"] = len(mins)
        res["F_minimal_faces_are_exactly_the_Req"] = (mins == {r[1] for r in realised})

    # L3, verified face by face: each block is {Req u T : T subset of Opt}
    byL = defaultdict(set)
    for k, v in faces.items():
        for f in v:
            byL[orders[order_of[f]]].add(f)
    bad = 0
    for L, req, opt in realised:
        got = byL.get(L, set())
        want = set()
        for t in range(0, need_dim + 2 - len(req) + 1):
            if len(req) + t - 1 > need_dim + 1:
                break
            for T in itertools.combinations(opt, t):
                want.add(tuple(sorted(req + T)))
        if got != want:
            bad += 1
    res["L3_blocks_that_are_not_a_shifted_simplex"] = bad

    cross = 0
    for k, v in faces.items():
        for f in v:
            Lf = order_of[f]
            for i in range(len(f)):
                g = f[:i] + f[i + 1:]
                if g in order_of and order_of[g] != Lf:
                    cross += 1
    res["L2_boundary_crossings_between_blocks"] = cross

    t0 = time.time()
    rel = relative_homology(faces, order_of, need_dim)
    rel["seconds"] = round(time.time() - t0, 2)
    res["relative"] = rel
    res["beta_tilde_gamma"] = {str(k - 1): rel["H"][str(k)] for k in range(0, need_dim + 1)}
    res["relative_complex_empty_below_dim"] = min(faces) if faces else None
    return res


# --------------------------------------------------------------------------- brute force
def gamma_full(P, n, atoms, cap=400000):
    """Every face of Gamma(P) by DFS with pruning, or None if it exceeds `cap`."""
    faces = defaultdict(list)
    faces[-1] = [()]
    total = [1]

    def rec(prefix, cur, start):
        for i in range(start, len(atoms)):
            U = cur | atoms[i]
            R = tc(U, n)
            if R is None or is_total(R, n):
                continue
            nf = prefix + (i,)
            faces[len(nf) - 1].append(nf)
            total[0] += 1
            if total[0] > cap:
                return False
            if not rec(nf, R, i + 1):
                return False
        return True

    sys.setrecursionlimit(10000)
    if not rec((), frozenset(P), 0):
        return None
    for k in faces:
        faces[k].sort()
    return faces


# --------------------------------------------------------------------------- controls
def _downward(facets):
    faces = defaultdict(set)
    for F in facets:
        for k in range(0, len(F) + 1):
            for S in itertools.combinations(sorted(F), k):
                faces[len(S) - 1].add(S)
    return {k: sorted(v) for k, v in faces.items()}


def control_readers():
    """The homology reader against independently known answers, including the Q-vs-F_2 trap."""
    out = {}
    for k in range(1, 6):
        faces = defaultdict(list)
        for s in range(0, k + 1):
            for S in itertools.combinations(range(k + 1), s):
                faces[len(S) - 1].append(S)
        out["boundary_of_simplex_%d_is_S%d" % (k, k - 1)] = {
            str(p): list(v) for p, v in reduced_betti(faces, k).items()}
    tor = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2),
           (0, 1, 5), (1, 2, 6), (2, 3, 0), (3, 4, 1), (4, 5, 2), (5, 6, 3), (6, 0, 4)]
    out["torus_Z7"] = {str(p): list(v) for p, v in
                       reduced_betti(_downward(tor), 2).items()}
    rp2 = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5), (1, 2, 4), (2, 3, 5),
           (1, 3, 4), (1, 3, 5), (2, 4, 5)]
    out["RP2_6"] = {str(p): list(v) for p, v in
                    reduced_betti(_downward(rp2), 2).items()}
    return out


def control_filter_substitution(P, n, need_dim, seed=20260814):
    """mg-bcd7's V6, re-run for this instrument: replace the true filter by a DIFFERENT family
    of the same number of generators of the same size, inside the same X.  The answer has to
    move -- otherwise the measurement is reading the shape of the code, not the filter."""
    st = structure(P, n)
    atoms, realised = st["atoms"], st["realised"]
    gsize = len(realised[0][1])
    true_gens = {r[1] for r in realised}
    # every face of X of the generator size that is NOT in the true filter
    pool = []
    for S in itertools.combinations(range(len(atoms)), gsize):
        if S in true_gens:
            continue
        U = set(P)
        for i in S:
            U |= atoms[i]
        R = tc(U, n)
        if R is None or is_total(R, n):
            continue
        pool.append(S)
    rng = random.Random(seed)
    variants = {"lex_first": pool[:len(true_gens)],
                "lex_last": pool[-len(true_gens):],
                "random": rng.sample(pool, min(len(true_gens), len(pool)))}
    out = {"generator_size": gsize, "n_true_generators": len(true_gens),
           "pool_size": len(pool), "variants": {}}
    for name, gens in variants.items():
        faces = defaultdict(list)
        seen = {}
        frontier = []
        for f in gens:
            seen[f] = 0
            faces[len(f) - 1].append(f)
            frontier.append(f)
        while frontier and (len(frontier[0]) - 1) < need_dim + 1:
            nxt = []
            for f in frontier:
                fs = set(f)
                for i in range(len(atoms)):
                    if i in fs:
                        continue
                    g = tuple(sorted(f + (i,)))
                    if g in seen:
                        continue
                    U = set(P)
                    for j in g:
                        U |= atoms[j]
                    if tc(U, n) is None:
                        continue
                    seen[g] = 0
                    faces[len(g) - 1].append(g)
                    nxt.append(g)
            frontier = nxt
        for k in faces:
            faces[k].sort()
        rel = relative_homology(faces, seen, need_dim)
        out["variants"][name] = {"dims": rel["dims"], "H": rel["H"],
                                 "nonzero": any(v["value"] != [0] for v in rel["H"].values())}
    out["at_least_one_moves"] = any(v["nonzero"] for v in out["variants"].values())
    return out


def cross_check_against_mg72e4():
    """The one deliberate import from the repo: mg-72e4's own tc, atom routine, rank routine
    and class census, used as an external control on this instrument's own."""
    out = {"available": False}
    try:
        sys.path.insert(0, HERE)
        import compat_geom_mg72e4_height1_anchor as M
    except Exception as e:                                     # pragma: no cover
        out["error"] = repr(e)
        return out
    out["available"] = True
    detail, agree = {}, True
    for key, _, mk in FAMILIES:
        P = mk(7)
        mine = {a for a, _ in atoms_of(P, 7)}
        theirs = set(M.atoms_of_upper(P, 7))
        detail[key] = {"mine": len(mine), "mg72e4": len(theirs), "same_set": mine == theirs}
        agree = agree and mine == theirs
    classes = M.height1_iso_classes_fast(7)
    cle2 = sorted(([sorted(map(list, P)), size, len(M.atoms_of_upper(P, 7))]
                   for P, size in classes if len(P) <= 2), key=lambda t: (len(t[0]), t[0]))
    detail["c_le_2_classes_at_n7"] = cle2
    detail["c_le_2_over_the_20_atom_margin_gate"] = [t for t in cle2 if t[2] > 20]
    detail["n_classes_at_n7"] = len(classes)
    detail["labelled_vertices_at_n7"] = sum(s for _, s in classes)
    out["atoms_agree"] = agree
    out["detail"] = detail
    rng = random.Random(20260814)
    pairs = [(i, j) for i in range(5) for j in range(5) if i != j]
    same = 0
    for _ in range(2000):
        S = set(rng.sample(pairs, rng.randint(0, 8)))
        same += (tc(S, 5) == M.tc(S, 5))
    out["tc_agreement_over_2000_random_relations_n5"] = same
    ok2 = ok3 = True
    for _ in range(200):
        cols = [{rng.randint(0, 25): rng.randint(1, 6) for _ in range(rng.randint(0, 5))}
                for _ in range(rng.randint(1, 30))]
        for p in SMALL_PRIMES:
            if rank_mod_p(cols, p) != M._rank_mod_p(cols, 26, p):
                ok3 = False
        if rank_mod_2_bitset(cols) != rank_mod_p(cols, 2):
            ok2 = False
    out["rank_routine_agrees_with_mg72e4"] = ok3
    out["bitset_rank_agrees_with_sparse_rank"] = ok2
    return out


# --------------------------------------------------------------------------- main
def main():
    t_start = time.time()
    rep = {"ticket": "mg-dd84", "primes": list(PRIMES), "all_primes_block_cap": ALL_PRIMES_CAP, "global_rank_cap": GLOBAL_CAP,
           "results": {}}

    print("V0  cross-checks against mg-72e4's own routines ...", flush=True)
    rep["V0_cross_check_mg72e4"] = cross_check_against_mg72e4()
    for row in rep["V0_cross_check_mg72e4"]["detail"]["c_le_2_classes_at_n7"]:
        print("     c<=2 class %-24s labelled=%4d atoms=%d" % (row[0], row[1], row[2]),
              flush=True)

    print("V1  homology-reader controls ...", flush=True)
    rep["V1_reader_controls"] = control_readers()
    print("     torus_Z7 =", rep["V1_reader_controls"]["torus_Z7"],
          " RP2_6 =", rep["V1_reader_controls"]["RP2_6"], flush=True)

    NEED = {"c1": 9, "c2_V": 8, "c2_L": 8}
    for key, label, mk in FAMILIES:
        print("V2  n=7  %s  (%s)  need relative degree <= %d ..." % (label, key, NEED[key]),
              flush=True)
        t0 = time.time()
        r = analyse(mk(7), 7, NEED[key])
        r["seconds"] = round(time.time() - t0, 1)
        r["label"] = label
        rep["results"]["n7_" + key] = r
        print("     atoms=%d realisedL=%d/%d |Req|=%s |Opt|=%s cone=%s(%s apex %s)" % (
            r["n_atoms"], r["L2_realised_total_orders"], r["L2_total_orders_containing_P"],
            r["L3_req_sizes"], r["L4_opt_sizes"], r["L1_is_cone"], r["L1_apex_form"],
            r["L1_apex_generating_pair"]), flush=True)
        print("     F by dim: %s" % json.dumps(r["F_direct_by_dim"]), flush=True)
        print("     beta~(Gamma): %s   [%.1fs]" % (
            json.dumps({k: v["value"] for k, v in r["beta_tilde_gamma"].items()}),
            r["seconds"]), flush=True)

    print("V3  brute-force cross-check at n = 3..6 ...", flush=True)
    bf = {}
    for key, label, mk in FAMILIES:
        for n in (3, 4, 5, 6):
            P = mk(n)
            if max(max(p) for p in P) >= n:
                continue
            at = atoms_of(P, n)
            atoms = [a for a, _ in at]
            if not atoms:
                continue
            t0 = time.time()
            e = {"n": n, "class": key, "n_atoms": len(atoms)}
            full = gamma_full(P, n, atoms)
            if full is None:
                e["brute_force"] = "over cap"
            else:
                e["gamma_faces"] = sum(len(v) for v in full.values()) - 1
                dmax = max(full)
                while dmax > 0 and sum(len(full.get(d, [])) for d in range(0, dmax + 2)) > 40000:
                    dmax -= 1
                e["direct_dmax"] = dmax
                e["direct_beta_tilde"] = {str(p): list(v) for p, v in
                                          reduced_betti(full, dmax).items()}
            rel = analyse(P, n, min(6, len(atoms) - 1), cone_upto=min(6, len(atoms)))
            e["relative_beta_tilde"] = {k: v["value"] for k, v in rel["beta_tilde_gamma"].items()}
            e["L1_is_cone"] = rel["L1_is_cone"]
            e["L4_opt_all_nonempty"] = rel["L4_opt_all_nonempty"]
            e["L4_opt_sizes"] = rel["L4_opt_sizes"]
            e["realised_total_orders"] = rel["L2_realised_total_orders"]
            e["F_closed_form_matches_direct"] = rel["F_closed_form_matches_direct"]
            if full is not None:
                d1 = {int(k): v for k, v in e["relative_beta_tilde"].items()}
                dv = e["direct_beta_tilde"]["1000003"]
                d2 = {d - 1: dv[d] for d in range(len(dv))}
                common = sorted(set(d1) & set(d2))
                e["agree_on_degrees"] = common
                e["agree"] = all(d1[d] == [d2[d]] for d in common)
            e["seconds"] = round(time.time() - t0, 1)
            bf["%s_n%d" % (key, n)] = e
            print("     %-5s n=%d atoms=%2d cone=%-5s optNE=%-5s direct=%s relative=%s %s" % (
                key, n, len(atoms), e["L1_is_cone"], e["L4_opt_all_nonempty"],
                e.get("direct_beta_tilde", {}).get("1000003"), e["relative_beta_tilde"],
                "AGREE" if e.get("agree") else ("-" if full is None else "MISMATCH")),
                flush=True)
    rep["V3_brute_force_cross_check"] = bf

    print("V4  filter-substitution negative control (n = 6) ...", flush=True)
    sub = {}
    for key, label, mk in FAMILIES:
        sub[key] = control_filter_substitution(mk(6), 6, 5)
        print("     %-5s pool=%d  moves=%s  %s" % (
            key, sub[key]["pool_size"], sub[key]["at_least_one_moves"],
            json.dumps({k: {d: h["value"] for d, h in v["H"].items()}
                        for k, v in sub[key]["variants"].items()})), flush=True)
    rep["V4_filter_substitution"] = sub

    print("V5  reproduce mg-bcd7's published numbers ...", flush=True)
    r1 = rep["results"]["n7_c1"]
    rep["V5_reproduces_mgbcd7"] = {
        "F_dims_5_6_7": [r1["F_direct_by_dim"].get("5"), r1["F_direct_by_dim"].get("6"),
                         r1["F_direct_by_dim"].get("7")],
        "expected": [120, 1680, 10920],
        "rank_d6_d7_at_1000003": [r1["relative"]["rank_blocked"]["6"].get("1000003"),
                                  r1["relative"]["rank_blocked"]["7"].get("1000003")],
        "expected_ranks": [120, 1560],
        "beta4_beta5": [r1["beta_tilde_gamma"]["4"]["value"],
                        r1["beta_tilde_gamma"]["5"]["value"]],
    }
    print("     ", json.dumps(rep["V5_reproduces_mgbcd7"]), flush=True)

    print("V6  enumeration shortcut vs the unrestricted enumeration ...", flush=True)
    sc = {}
    for key, label, mk in FAMILIES:
        for n in (4, 5, 6):
            P = mk(n)
            if max(max(p) for p in P) >= n:
                continue
            st = structure(P, n)
            if not st["realised"]:
                continue
            a, _, _ = enumerate_filter(P, n, st["atoms"], st["realised"], 6, shortcut=True)
            b, _, _ = enumerate_filter(P, n, st["atoms"], st["realised"], 6, shortcut=False)
            same = {k: sorted(v) for k, v in a.items()} == {k: sorted(v) for k, v in b.items()}
            sc["%s_n%d" % (key, n)] = {"identical": same,
                                       "faces": {str(k): len(v) for k, v in sorted(a.items())}}
    rep["V6_shortcut_vs_unrestricted"] = sc
    print("     identical everywhere:",
          all(v["identical"] for v in sc.values()), flush=True)

    # V7 -- the hypotheses L1/L3/L4 at every n this instrument can afford, which is what turns
    # mg-bcd7 Sec.7's "observed pattern" for the c = 1 family into a statement with a reason.
    # Only structure() is called: no filter is enumerated and no rank is taken.
    print("V7  L1/L3/L4 across n = 3..8 (structure only) ...", flush=True)
    hyp = {}
    for key, label, mk in FAMILIES:
        for n in range(3, 9):
            P = mk(n)
            if max(max(p) for p in P) >= n:
                continue
            st = structure(P, n)
            realised = st["realised"]
            e = {"n": n, "class": key, "n_atoms": len(st["atoms"]),
                 "L1_is_cone": st["apex"] is not None, "L1_apex_form": st["apex_form"],
                 "realised_total_orders": len(realised),
                 "total_orders_containing_P": st["n_total_orders"],
                 "L3_cover_atom_multiplicities": st["cover_atom_multiplicities"],
                 "req_sizes": sorted({len(r[1]) for r in realised}),
                 "opt_sizes": sorted({len(r[2]) for r in realised})}
            e["L4_opt_all_nonempty"] = bool(realised) and all(len(r[2]) > 0 for r in realised)
            e["acyclic_by_L1_L4"] = (e["L1_is_cone"] and e["L4_opt_all_nonempty"]
                                     and e["L3_cover_atom_multiplicities"] == [1])
            hyp["%s_n%d" % (key, n)] = e
            print("     %-5s n=%d atoms=%2d cone=%-5s(%s) realisedL=%-4d |Req|=%s |Opt|=%s "
                  "-> acyclic=%s" % (key, n, e["n_atoms"], e["L1_is_cone"], e["L1_apex_form"],
                                     e["realised_total_orders"], e["req_sizes"],
                                     e["opt_sizes"], e["acyclic_by_L1_L4"]), flush=True)
    rep["V7_hypotheses_by_n"] = hyp

    # V8 -- WHICH hypothesis is load-bearing.  The mechanism must not be quoted as a proof of the
    # census, and the honest way to say so is to point at the classes it fails on and name the
    # step that fails.  Measured, because the first draft of this document asserted that L1 AND
    # L4 fail at the stars and only L1 does.
    print("V8  where the mechanism FAILS (classes known to carry homology) ...", flush=True)
    hard = {
        "K_6_1_star": frozenset((0, v) for v in range(1, 7)),
        "K_1_6_star": frozenset((v, 6) for v in range(0, 6)),
        "K_3_4": frozenset((i, j) for i in range(3) for j in range(3, 7)),
    }
    where = {}
    for name, P in hard.items():
        st = structure(P, 7)
        r = st["realised"]
        e = {"n_atoms": len(st["atoms"]),
             "L1_is_cone": st["apex"] is not None, "L1_apex_form": st["apex_form"],
             "L1_sources_carried_by_no_atom_head": st["sources"],
             "L1_sinks_carried_by_no_atom_tail": st["sinks"],
             "L3_cover_atom_multiplicities": st["cover_atom_multiplicities"],
             "realised_total_orders": len(r),
             "req_sizes": sorted({len(x[1]) for x in r}),
             "opt_sizes": sorted({len(x[2]) for x in r})}
        e["L4_opt_all_nonempty"] = bool(r) and all(len(x[2]) > 0 for x in r)
        e["failing_step"] = ("L1" if not e["L1_is_cone"] else
                             ("L4" if not e["L4_opt_all_nonempty"] else "none"))
        where[name] = e
        print("     %-11s cone=%-5s optNE=%-5s covermult=%s -> fails at %s" % (
            name, e["L1_is_cone"], e["L4_opt_all_nonempty"],
            e["L3_cover_atom_multiplicities"], e["failing_step"]), flush=True)
    rep["V8_where_the_mechanism_fails"] = where

    # ---------------------------------------------------------------- verdict
    fails = []
    v0 = rep["V0_cross_check_mg72e4"]
    if not v0.get("atoms_agree"):
        fails.append("V0: atoms disagree with mg-72e4")
    if v0.get("tc_agreement_over_2000_random_relations_n5") != 2000:
        fails.append("V0: tc disagrees with mg-72e4")
    if not v0.get("rank_routine_agrees_with_mg72e4") or not v0.get("bitset_rank_agrees_with_sparse_rank"):
        fails.append("V0: rank routines disagree")
    if rep["V1_reader_controls"]["torus_Z7"]["1000003"] != [0, 0, 2, 1]:
        fails.append("V1: torus control wrong")
    if rep["V1_reader_controls"]["RP2_6"]["1000003"] != [0, 0, 0, 0] or \
       rep["V1_reader_controls"]["RP2_6"]["2"] != [0, 0, 1, 1]:
        fails.append("V1: RP2 control wrong")
    for k, r in rep["results"].items():
        if not (r["L1_is_cone"] and r["L1_cone_check_passes"]):
            fails.append(k + ": X not shown to be a cone")
        if not r["L4_opt_all_nonempty"]:
            fails.append(k + ": some realised total order has empty Opt")
        if r["L2_boundary_crossings_between_blocks"] != 0:
            fails.append(k + ": relative boundary crosses blocks")
        if r["L3_blocks_that_are_not_a_shifted_simplex"] != 0:
            fails.append(k + ": a block is not a shifted simplex")
        if r["L3_cover_atom_multiplicities"] != [1]:
            fails.append(k + ": a cover of L lies in more than one atom of L")
        if not r["F_closed_form_matches_direct"]:
            fails.append(k + ": closed form disagrees with direct enumeration")
        if not r.get("F_minimal_faces_are_exactly_the_Req"):
            fails.append(k + ": minimal filter faces are not the Req(L)")
        if not r["relative"]["global_and_blocked_agree"]:
            fails.append(k + ": global and blocked ranks disagree")
        for d, h in r["beta_tilde_gamma"].items():
            if h["value"] != [0]:
                fails.append("%s: beta~_%s = %s" % (k, d, h["value"]))
    for k, e in rep["V3_brute_force_cross_check"].items():
        if e.get("agree") is False:
            fails.append("V3 " + k + ": brute force disagrees")
    for k, s in rep["V4_filter_substitution"].items():
        if not s["at_least_one_moves"]:
            fails.append("V4 " + k + ": no substituted filter moved the answer")
    if rep["V5_reproduces_mgbcd7"]["F_dims_5_6_7"] != [120, 1680, 10920]:
        fails.append("V5: mg-bcd7 face counts not reproduced")
    if rep["V5_reproduces_mgbcd7"]["rank_d6_d7_at_1000003"] != [120, 1560]:
        fails.append("V5: mg-bcd7 ranks not reproduced")
    if not all(v["identical"] for v in rep["V6_shortcut_vs_unrestricted"].values()):
        fails.append("V6: enumeration shortcut changes the answer")
    for k, e in rep["V7_hypotheses_by_n"].items():
        if e["n"] >= 4 and not e["acyclic_by_L1_L4"]:
            fails.append("V7 " + k + ": L1/L3/L4 do not all hold at n >= 4")
        if e["n"] == 3 and e["acyclic_by_L1_L4"]:
            fails.append("V7 " + k + ": L4 was expected to FAIL at n = 3 and did not")
    for k, e in rep["V8_where_the_mechanism_fails"].items():
        if e["failing_step"] == "none":
            fails.append("V8 " + k + ": the mechanism does NOT fail on a class that carries "
                                     "homology -- the argument would then prove something false")

    rep["failures"] = fails
    rep["ALL_PASS"] = not fails
    rep["seconds"] = round(time.time() - t_start, 1)
    with open(OUT, "w") as fh:
        json.dump(rep, fh, indent=1, sort_keys=True)
    print("\nALL_PASS = %s  %s   [%.1fs]  -> %s" % (rep["ALL_PASS"], fails, rep["seconds"], OUT))
    return 0 if rep["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
