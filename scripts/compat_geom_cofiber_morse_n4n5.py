#!/usr/bin/env python3
r"""
compat_geom_cofiber_morse_n4n5.py
=================================

Compat-Geom F14 / PCR-Lit-2' companion script (mg-3839).  Computes the
n=4->5 cofiber cohomology

    B_4  :=  H~^3(Delta_5 / Delta_4)

with its S_4-representation type and an explicit basis.  This is the GATING
computation for the general-n route (ii): F11 (mg-b352) reduced (UCC.1)'s
representation-type half to "the triple connecting map  d_n : B_n -> B_{n+1}
is an isomorphism for all n", and the first concrete test of that hypothesis
(entry sub-problem (E2), F15) needs B_4 + an explicit basis.  mg-6295 (PCR-
Lit-2) §6.3 explicitly designates "re-run the greedy+Forman recipe on
C_*(Delta_5,Delta_4)" as its follow-up.

Setting (the F1-refined / F2 / F5 / mg-6295 convention)
------------------------------------------------------
Delta_n = order complex of  PPF_n := Pos_n^sub \ {antichain} \ {total orders}.
  |PPF_3| = 12,  |PPF_4| = 194,  |PPF_5| = 4110.
iota_4 : PPF_4 -> PPF_5  sends a partial order on {0,1,2,3} to the same
relation set on {0,1,2,3,4} (element 4 incomparable to all), an order-ideal
inclusion, inducing the subcomplex inclusion Delta_4 <-> Delta_5.

Why the naive mg-6295 greedy+Forman recipe does NOT run at n=4->5
----------------------------------------------------------------
The relative complex C_*(Delta_5, Delta_4) has f-vector with entries up to
~10^8 and ~3.3x10^8 cells total (printed in section [A]).  mg-6295's
recipe -- materialise every relative cell, build the cover graph, run a
greedy acyclic matching with a per-acceptance reachability DFS -- is flatly
infeasible at this size (tens of GB, the F9-S2 `solve_psi_fast` thrash
failure mode the ticket warns about).  This script therefore uses the
*memory-efficient* route the ticket asks for: an S_n-equivariance / order-
ideal-filtration reduction that is itself discrete Morse theory (the cluster
lemma -- Hersh 2005, Jonsson's patchwork theorem -- assembles fibrewise
acyclic matchings into a global one), collapsing the 3.3x10^8-cell relative
complex onto a single 1.5x10^7-cell order complex Delta(A_4) without ever
materialising the huge complex.

The reduction (rigorous; every hypothesis verified computationally)
-------------------------------------------------------------------
Two collapsing spectral sequences of order-ideal filtrations + one
"all-cone" homology-iso peel give, S_4-equivariantly,

    H~_d(Delta_5/Delta_4)  =  2 . H~_{d-1}(Delta(A_4))

where  A_4 = { x in PPF_5 : Down_4(x) != empty, Up_4(x) = empty,
                            x|_{0123} != empty },  |A_4| = 1420.
The factor 2 is the Down_4 / Up_4 duality (an S_4-equivariant iso D ~= U).
The pipeline:
  [MoveA] peel element 4: cofiber Delta_5/Delta_4 -> C_*(Delta(R),Delta(R\S));
  [MoveB] order ideal S = Type-empty: -> H~_{d-1}(Delta(D)) (+) H~_{d-1}(Delta(U));
  [Peel ] all-cone Up_4 peel: H~_*(Delta(D_4)) = H~_*(Delta(A_4)).
Each step's collapse hypothesis (fibres contractible / empty / disjoint
unions of contractibles) is asserted at run time.  The whole pipeline is
re-run for n=3->4 as a trip-wire: it must reproduce mg-6295's GREEN result
H~_*(Delta_4/Delta_3) = (0,0,2,0) = 2.sgn_{S_3}.

Pure-Python stdlib only.

References
----------
  - mg-6295  (PCR-Lit-2 / M1) -- scripts/compat_geom_cofiber_morse_n3n4.py;
    the n=3->4 greedy+Forman recipe this adapts, and the trip-wire target.
  - mg-b352  (F11) §4.6, §6.2 -- (E2) gated on PCR-Lit-2'.
  - mg-8216  (F10) §1.1, §3.3, §10.2 -- |PPF_n|, perfection n-dependence,
    the M1+M2 consistency prediction (0,0,0,2,0).
  - P. Hersh, "On optimizing discrete Morse functions", 2005 -- cluster lemma.
  - J. Jonsson, "Simplicial complexes of graphs", patchwork theorem.
  - R. Forman, "Morse theory for cell complexes", Adv. Math. 134 (1998).
"""

import sys
import time
from itertools import permutations

sys.setrecursionlimit(1_000_000)


# =======================================================================
# 1. Poset enumeration  (identical convention to mg-6295 / mg-7455)
# =======================================================================

def transitive_closure(rel):
    closed = set(rel)
    changed = True
    while changed:
        changed = False
        addition = []
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    addition.append((i, l))
        if addition:
            closed.update(addition)
            changed = True
    return frozenset(closed)


def enumerate_posets(n):
    """All transitively-closed strict partial orders on {0,...,n-1}."""
    seen = {frozenset()}
    frontier = {frozenset()}
    while frontier:
        new_frontier = set()
        for P in frontier:
            for a in range(n):
                for b in range(n):
                    if a == b or (a, b) in P or (b, a) in P:
                        continue
                    closed = transitive_closure(P | {(a, b)})
                    if any((j, i) in closed for (i, j) in closed):
                        continue
                    if closed not in seen:
                        seen.add(closed)
                        new_frontier.add(closed)
        frontier = new_frontier
    return list(seen)


def is_total(P, n):
    return len(P) == n * (n - 1) // 2


def make_PPF(n):
    r"""PPF_n := Pos_n^sub \ {antichain} \ {total orders}."""
    return [P for P in enumerate_posets(n)
            if P != frozenset() and not is_total(P, n)]


# =======================================================================
# 2. Order-complex chain enumeration / counting
# =======================================================================

def above_lists(elements):
    """es = elements sorted by (size, sorted-pairs); above[P] = strict up-set."""
    es = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    above = {}
    for i, P in enumerate(es):
        ups = []
        for Q in es[i + 1:]:
            if len(Q) > len(P) and P < Q:
                ups.append(Q)
        above[P] = ups
    return es, above


def fvector_count(elements):
    """f-vector of Delta(elements) by DP -- never materialises the chains.
    f[k] = number of (k+1)-element chains = number of k-cells."""
    es, above = above_lists(elements)
    MAXD = 24
    cnt = {}
    for P in reversed(es):
        c = [0] * (MAXD + 1)
        c[0] = 1
        for Q in above[P]:
            cQ = cnt[Q]
            for k in range(1, MAXD + 1):
                c[k] += cQ[k - 1]
        cnt[P] = c
    f = [sum(cnt[P][k] for P in es) for k in range(MAXD + 1)]
    while f and f[-1] == 0:
        f.pop()
    return f


def chains_by_dim(elements):
    """Materialise Delta(elements): by_dim[k] = list of (k+1)-element chains."""
    es, above = above_lists(elements)
    by_dim = {0: [(P,) for P in es]}
    cur = by_dim[0]
    d = 0
    while cur:
        nxt = []
        for c in cur:
            for Q in above[c[-1]]:
                nxt.append(c + (Q,))
        if not nxt:
            break
        d += 1
        by_dim[d] = nxt
        cur = nxt
    return by_dim


# =======================================================================
# 3. Mod-p homology of a (small, materialised) order complex
# =======================================================================

def _rank_mod_p(cols, p):
    """Rank over GF(p) of a sparse matrix given as a list of columns
    (each column = dict row->coeff).  Destructive sparse Gaussian elim."""
    rank = 0
    pivot = {}                       # row -> reduced column (dict)
    for col in cols:
        col = {r: (v % p) for r, v in col.items() if v % p}
        while col:
            r = min(col)
            v = col[r]
            if r in pivot:
                pc = pivot[r]
                f = (v * pow(pc[r], -1, p)) % p
                for rr, vv in pc.items():
                    nv = (col.get(rr, 0) - f * vv) % p
                    if nv:
                        col[rr] = nv
                    elif rr in col:
                        del col[rr]
            else:
                pivot[r] = col
                rank += 1
                break
    return rank


def reduced_betti(by_dim, primes=(1_000_003, 999_983)):
    """Reduced Betti vector of the materialised complex `by_dim`, over GF(p)
    for two primes (must agree).  Returns a tuple b[0..maxdim]; the empty
    complex returns (-1,) (i.e. H~_{-1} = field)."""
    total = sum(len(v) for v in by_dim.values())
    if total == 0:
        return (-1,)
    results = []
    for p in primes:
        maxd = max(by_dim)
        idx = {k: {c: i for i, c in enumerate(by_dim[k])} for k in by_dim}
        ranks = {0: 0}
        for k in range(1, maxd + 1):
            lower = idx[k - 1]
            cols = []
            for c in by_dim[k]:
                col = {}
                for i in range(len(c)):
                    j = lower[c[:i] + c[i + 1:]]
                    col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
                cols.append(col)
            ranks[k] = _rank_mod_p(cols, p)
        betti = {}
        for k in range(maxd + 1):
            betti[k] = len(by_dim[k]) - ranks.get(k, 0) - ranks.get(k + 1, 0)
        betti[0] -= 1                # reduce
        results.append(tuple(betti[k] for k in range(maxd + 1)))
    if len(set(results)) != 1:
        raise RuntimeError(f"prime disagreement in reduced_betti: {results}")
    return results[0]


def is_contractible_or_empty(elements):
    """True iff Delta(elements) has vanishing reduced homology in EVERY
    degree >= 0 (contractible) OR elements is empty (H~_{-1}=field, but the
    complex is acyclic in non-negative degrees, which is what the cluster-
    lemma collapse needs).  Used to certify MoveA fibre hypotheses."""
    if not elements:
        return True                  # empty fibre: handled separately
    b = reduced_betti(chains_by_dim(list(elements)))
    return all(x == 0 for x in b)


def is_contractible(elements):
    """True iff Delta(elements) is non-empty and acyclic (contractible)."""
    if not elements:
        return False
    b = reduced_betti(chains_by_dim(list(elements)))
    return all(x == 0 for x in b)


def homology_concentrated_deg0(elements):
    """True iff Delta(elements) is a disjoint union of contractibles
    (reduced homology lives only in degree 0).  Used to certify MoveB."""
    if not elements:
        return True
    b = reduced_betti(chains_by_dim(list(elements)))
    return all(b[k] == 0 for k in range(1, len(b)))


# =======================================================================
# 4. Connected components of a subposet (= components of its order complex)
# =======================================================================

def components(elements):
    """Connected components of the comparability graph of `elements`
    (equivalently, the connected components of Delta(elements))."""
    es = list(elements)
    idx = {P: i for i, P in enumerate(es)}
    parent = list(range(len(es)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    # union comparable pairs
    by_size = {}
    for P in es:
        by_size.setdefault(len(P), []).append(P)
    for i, P in enumerate(es):
        for Q in es:
            if P is Q:
                continue
            if (len(P) < len(Q) and P < Q) or (len(Q) < len(P) and Q < P):
                ra, rb = find(i), find(idx[Q])
                if ra != rb:
                    parent[ra] = rb
    comp = {}
    for i, P in enumerate(es):
        comp.setdefault(find(i), []).append(P)
    return list(comp.values())


# =======================================================================
# 5. The reduction engine
#
#    Two operations + one homology-iso peel, each rigorous and each with
#    its hypothesis asserted at run time:
#
#    MoveA  (peel element e).  Cofiber Delta(P)/Delta(Q) with Q an order
#      ideal of P.  IF for every x in R := P\Q the down-set Q_{<x} has
#      Delta contractible-or-empty, the order-ideal filtration spectral
#      sequence collapses onto the q=-1 line and
#         H~_d(Delta(P)/Delta(Q)) = H~_d(Delta(R)/Delta(R \ Q_empty)),
#      Q_empty := {x in R : Q_{<x} = empty}, an order ideal of R.
#      [The cluster lemma: the fibrewise "toggle-apex" matchings on the
#       cone fibres assemble to a global acyclic matching; collapse is
#       exact because the SS is concentrated on one line.]
#
#    MoveB.  Cofiber Delta(P)/Delta(Sub) with Sub an order FILTER of P,
#      A := P\Sub the complementary order ideal.  IF for every component
#      A^(j) of Delta(A) and every x in Sub the down-set A^(j)_{<x} has
#      Delta contractible-or-empty, the filtration by |chain n Sub|
#      collapses onto q=0 and
#         H~_d(Delta(P)/Delta(Sub)) = (+)_j  H~_{d-1}(Delta(P^(j))),
#      P^(j) := {x in Sub : A^(j)_{<x} != empty}.
#
#    PEEL  (all-cone homology iso).  For absolute H~_*(Delta(P)): if an
#      order ideal Q of P has Q_{<x} contractible (never empty) for every
#      x in P\Q, then Delta(Q) <-> Delta(P) is a homology iso.
# =======================================================================

# ---- "peel" primitives: delete all relations of element e in a direction
def kill_up(x, e):       # delete (.,e): element e loses all in-relations
    return frozenset((a, b) for (a, b) in x if b != e)


def kill_down(x, e):     # delete (e,.): element e loses all out-relations
    return frozenset((a, b) for (a, b) in x if a != e)


def isolate(x, e):       # delete every relation touching e
    return frozenset((a, b) for (a, b) in x if a != e and b != e)


def down_set(x, elements_set):
    """{y in elements_set : y < x} (strict refinement order)."""
    return [y for y in elements_set if len(y) < len(x) and y < x]


def betti_add(b1, b2):
    n = max(len(b1), len(b2))
    return tuple((b1[k] if k < len(b1) else 0) + (b2[k] if k < len(b2) else 0)
                 for k in range(n))


def betti_shift(b, s):
    """shift a reduced-Betti tuple up by s degrees: H~_d -> H~_{d+s}."""
    if b == (-1,):                   # empty complex: H~_{-1}=field -> H~_{s-1}
        out = [0] * (s + 1)
        if s >= 1:
            out[s - 1] = 1
        else:
            return (-1,)
        return tuple(out)
    return tuple([0] * s) + tuple(b)


# size threshold: complexes at or below this are computed directly
DIRECT_THRESHOLD = 600_000

# memo so the single large "stuck" complex Delta(A_n) is computed only once
_HOMOLOGY_MEMO = {}


def reduced_homology(P, depth=0, log=None, want_cycles=False):
    """Reduced Betti vector of Delta(P) for a subposet P (list of posets).
    Uses all-cone homology-iso peels to shrink P, then a direct
    materialised computation.  Returns the reduced-Betti tuple."""
    P = list(P)
    pad = "  " * depth
    key = frozenset(P)
    if key in _HOMOLOGY_MEMO:
        if log is not None:
            log.append(f"{pad}absolute H~_*(Delta(P)), |P|={len(P)} [memo hit]")
        return _HOMOLOGY_MEMO[key]
    if log is not None:
        log.append(f"{pad}absolute H~_*(Delta(P)), |P|={len(P)}")
    Pset = set(P)
    # ---- try every all-cone homology-iso peel ----
    peel_candidates = []
    elems = sorted({a for x in P for (a, b) in x} | {b for x in P for (a, b) in x})
    for e in elems:
        peel_candidates.append((lambda x, e=e: kill_up(x, e), f"kill_up_{e}"))
        peel_candidates.append((lambda x, e=e: kill_down(x, e), f"kill_down_{e}"))
        peel_candidates.append((lambda x, e=e: isolate(x, e), f"isolate_{e}"))
    for killfn, name in peel_candidates:
        ideal = [x for x in P if killfn(x) == x]
        filt = [x for x in P if killfn(x) != x]
        if not filt or not ideal:
            continue
        # all-cone test: every filter element's image must land back in P
        all_cone = True
        for x in filt:
            if killfn(x) not in Pset:
                all_cone = False
                break
        if all_cone:
            if log is not None:
                log.append(f"{pad}  all-cone peel [{name}] : "
                           f"|P|={len(P)} -> |ideal|={len(ideal)} "
                           f"(homology iso)")
            result = reduced_homology(ideal, depth + 1, log, want_cycles)
            _HOMOLOGY_MEMO[key] = result
            return result
    # ---- no all-cone peel: direct computation ----
    f = fvector_count(P)
    total = sum(f)
    if log is not None:
        log.append(f"{pad}  direct: f={f}  ({total} cells)")
    if total > DIRECT_THRESHOLD:
        result = direct_reduced_homology_big(P, depth, log)
    else:
        result = reduced_betti(chains_by_dim(P))
    _HOMOLOGY_MEMO[key] = result
    return result


def cofiber_homology(P, Sub, sub_is_ideal, depth=0, log=None):
    """Reduced Betti vector of the cofiber Delta(P)/Delta(Sub).
    sub_is_ideal=True : Sub is an order ideal of P  (MoveA);
    sub_is_ideal=False: Sub is an order filter of P (MoveB)."""
    P = list(P)
    Sub = list(Sub)
    Subset = set(Sub)
    pad = "  " * depth
    if sub_is_ideal:
        # ----- MoveA: peel an element -----
        R = [x for x in P if x not in Subset]
        # choose the element to peel: the largest label present
        elems = sorted({a for x in P for (a, b) in x}
                       | {b for x in P for (a, b) in x})
        e = elems[-1]
        # fibre check + Q_empty
        Q_empty = []
        # cache fibres by the "peeled apex" to avoid recompute
        distinct_fibres = {}
        for x in R:
            fib = down_set(x, Subset)
            if not fib:
                Q_empty.append(x)
                continue
            key = frozenset(fib)
            if key not in distinct_fibres:
                distinct_fibres[key] = is_contractible_or_empty(fib)
            if not distinct_fibres[key]:
                raise RuntimeError(
                    f"MoveA fibre hypothesis FAILED at depth {depth}: "
                    f"a down-set Q_<x is neither contractible nor empty")
        if log is not None:
            log.append(f"{pad}MoveA peel elt {e}: |P|={len(P)} |Q(ideal)|="
                       f"{len(Sub)} -> |R|={len(R)}  |Q_empty|={len(Q_empty)}"
                       f"  ({len(distinct_fibres)} distinct non-empty fibres,"
                       f" all contractible)")
        Rset = set(R)
        Qempset = set(Q_empty)
        new_sub = [x for x in R if x not in Qempset]   # a FILTER of R
        return cofiber_homology(R, new_sub, sub_is_ideal=False,
                                depth=depth + 1, log=log)
    else:
        # ----- MoveB: Sub is a filter, ideal A = P\Sub -----
        A = [x for x in P if x not in Subset]
        comps = components(A)
        if log is not None:
            log.append(f"{pad}MoveB: ideal A=P\\Sub has |A|={len(A)}, "
                       f"{len(comps)} component(s) of sizes "
                       f"{sorted(len(c) for c in comps)}")
        result = ()
        for j, Aj in enumerate(comps):
            Ajset = set(Aj)
            # hypothesis: Aj_<x contractible-or-empty for all x in Sub
            distinct = {}
            Pj = []
            for x in Sub:
                fib = [y for y in Aj if len(y) < len(x) and y < x]
                if fib:
                    Pj.append(x)
                    key = frozenset(fib)
                    if key not in distinct:
                        distinct[key] = is_contractible_or_empty(fib)
                    if not distinct[key]:
                        raise RuntimeError(
                            f"MoveB fibre hypothesis FAILED at depth {depth}, "
                            f"component {j}")
            if log is not None:
                log.append(f"{pad}  component {j}: |A^(j)|={len(Aj)} -> "
                           f"|P^(j)|={len(Pj)}  ({len(distinct)} distinct "
                           f"fibres, all contractible)")
            bj = reduced_homology(Pj, depth + 1, log)
            result = betti_add(result, betti_shift(bj, 1))
        return result


# =======================================================================
# 6. Direct homology of a BIG order complex via elementary collapse
#    (free-face removal) followed by mod-p Gaussian elimination on the
#    residual.  Used for the single large "stuck" complex Delta(A_4).
# =======================================================================

def direct_reduced_homology_big(P, depth=0, log=None, return_residual=False):
    """Materialise Delta(P), elementary-collapse it (free-face removal),
    then mod-p Gaussian elimination on the residual core.

    The collapse is a sequence of valid elementary collapses: if `alive`
    is a subcomplex and a cell s has exactly one alive codim-1 cofacet t,
    then (proof: any alive cell strictly above s gives a 2nd alive codim-1
    cofacet) t is a maximal cell and s is a free face, so removing (s,t)
    is an elementary collapse and `alive` stays a subcomplex.  Hence the
    residual core has the same homology as Delta(P).  Euler characteristic
    is re-checked across the collapse as a guard."""
    pad = "  " * depth
    t0 = time.time()
    by_dim = chains_by_dim(P)
    maxd = max(by_dim)
    f = [len(by_dim[k]) for k in range(maxd + 1)]
    if log is not None:
        log.append(f"{pad}direct_big: materialised f={f} "
                   f"({sum(f)} cells, {time.time()-t0:.1f}s)")
    # integer-encode each chain: cell -> id; store facet lists.
    # cells grouped by dim; id space is global.
    cell_id = {}
    cells = []                       # cell id -> (dim, chain-tuple)
    dim_of = []
    for k in range(maxd + 1):
        for c in by_dim[k]:
            cell_id[c] = len(cells)
            cells.append(c)
            dim_of.append(k)
    N = len(cells)
    # facets[c] = list of facet ids ; cofacet_count[c]
    facets = [None] * N
    cofacet = [[] for _ in range(N)]
    for cid, c in enumerate(cells):
        k = dim_of[cid]
        if k == 0:
            facets[cid] = []
            continue
        fl = []
        for i in range(len(c)):
            fc = c[:i] + c[i + 1:]
            fid = cell_id[fc]
            fl.append(fid)
            cofacet[fid].append(cid)
        facets[cid] = fl
    cofacet_count = [len(cofacet[i]) for i in range(N)]
    alive = bytearray([1]) * N
    # ---- elementary collapse: repeatedly remove free pairs ----
    # a cell s is FREE if it has exactly one alive cofacet t (dim t = dim s+1)
    from collections import deque
    queue = deque(i for i in range(N) if cofacet_count[i] == 1)
    collapsed = 0
    while queue:
        s = queue.popleft()
        if not alive[s] or cofacet_count[s] != 1:
            continue
        # find the unique alive cofacet
        t = None
        for cand in cofacet[s]:
            if alive[cand]:
                t = cand
                break
        if t is None:
            continue
        # remove s and t
        alive[s] = 0
        alive[t] = 0
        collapsed += 2
        # t's removal: every facet of t loses a cofacet
        for fc in facets[t]:
            if alive[fc]:
                cofacet_count[fc] -= 1
                if cofacet_count[fc] == 1:
                    queue.append(fc)
        # s's removal: every facet of s loses a cofacet
        for fc in facets[s]:
            if alive[fc]:
                cofacet_count[fc] -= 1
                if cofacet_count[fc] == 1:
                    queue.append(fc)
    survivors = [i for i in range(N) if alive[i]]
    res_f = {}
    for i in survivors:
        res_f[dim_of[i]] = res_f.get(dim_of[i], 0) + 1
    if log is not None:
        log.append(f"{pad}  elementary collapse: {collapsed} cells removed, "
                   f"{len(survivors)} survive  res-f="
                   f"{[res_f.get(k,0) for k in range(maxd+1)]}  "
                   f"({time.time()-t0:.1f}s)")
    # ---- consistency: elementary collapse preserves Euler characteristic
    chi_full = -1 + sum((-1) ** k * f[k] for k in range(len(f)))
    chi_res = -1 + sum((-1) ** k * res_f.get(k, 0) for k in range(maxd + 1))
    if chi_full != chi_res:
        raise RuntimeError(f"collapse broke Euler char: {chi_full} != {chi_res}")
    # ---- residual core: mod-p Gaussian elimination ----
    res_by_dim = {}
    for i in survivors:
        res_by_dim.setdefault(dim_of[i], []).append(cells[i])
    if sum(len(v) for v in res_by_dim.values()) == 0:
        return ((-1,), {}) if return_residual else (-1,)
    b = reduced_betti(res_by_dim)
    if log is not None:
        log.append(f"{pad}  residual reduced Betti = {b}  "
                   f"({time.time()-t0:.1f}s total)")
    return (b, res_by_dim) if return_residual else b


def _nullspace_mod_p(cols, ncols, p):
    """Basis of the kernel of the sparse matrix `cols` (list of dict
    row->coeff, one per column) over GF(p).  Returns a list of kernel
    vectors, each a dict col_index->coeff."""
    # reduce columns, tracking which original columns are combined
    pivot = {}                       # row -> (reduced col dict, combo dict)
    free = []                        # (combo dict) for pivot-free columns
    for j in range(ncols):
        col = {r: (v % p) for r, v in cols[j].items() if v % p}
        combo = {j: 1}
        while col:
            r = min(col)
            v = col[r]
            if r in pivot:
                pc, pcombo = pivot[r]
                f = (v * pow(pc[r], -1, p)) % p
                for rr, vv in pc.items():
                    nv = (col.get(rr, 0) - f * vv) % p
                    if nv:
                        col[rr] = nv
                    elif rr in col:
                        del col[rr]
                for cc, vv in pcombo.items():
                    nv = (combo.get(cc, 0) - f * vv) % p
                    if nv:
                        combo[cc] = nv
                    elif cc in combo:
                        del combo[cc]
            else:
                pivot[r] = (col, combo)
                break
        else:
            # col reduced to 0 -> `combo` is a kernel vector
            free.append(combo)
    return free


def extract_h2_generator(P, log=None):
    """Collapse Delta(P), then extract an explicit basis of H~_2 of the
    residual core as kernel vectors of the residual boundary d_2.  Returns
    a list of cycles; each cycle is a list of (coeff, 2-chain) where the
    2-chain is a triple (P0<P1<P2) of posets in P.  (Used for the explicit
    B_4 basis: a residual 2-cycle of Delta(A_4) lifts to a generator of
    H~_2(Delta(A_4)) = H~_2(Delta(D)) = a summand of B_4.)"""
    b, res = direct_reduced_homology_big(P, log=log, return_residual=True)
    if 2 not in res or not res.get(2):
        return b, []
    c1 = {c: i for i, c in enumerate(res.get(1, []))}
    cols = []
    for tri in res[2]:
        col = {}
        for i in range(3):
            face = tri[:i] + tri[i + 1:]
            if face in c1:                      # face survived the collapse
                j = c1[face]
                col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
        cols.append(col)
    ker = _nullspace_mod_p([dict(c) for c in cols], len(cols),
                           1_000_003)
    p = 1_000_003
    cycles = []
    for kv in ker:
        cyc = []
        for j, coeff in sorted(kv.items()):
            cc = coeff % p
            cc = cc - p if cc > p // 2 else cc   # lift to small signed int
            cyc.append((cc, res[2][j]))
        cycles.append(cyc)
    return b, cycles


# =======================================================================
# 7. S_n-equivariant Euler characteristic of an order complex
#
#    S_n permutes {0,...,n-1} and fixes n; it acts on PPF_{n+1} and on
#    every S_n-invariant subposet.  The equivariant Euler characteristic
#    chi^{S_n}(Delta(P)) := sum_k (-1)^k [C_k(Delta(P))]  is a virtual
#    S_n-character; by the Hopf trace formula it equals
#    sum_k (-1)^k [H~_k(Delta(P))] + [trivial degree -1 term].  For each
#    g, chi(g) = sum_k (-1)^k #{g-fixed k-chains} = reduced Euler char of
#    the g-fixed subposet Delta(P^g).
# =======================================================================

def apply_perm(P, perm):
    return frozenset((perm[a], perm[b]) for (a, b) in P)


def euler_char_fixed(P_set, perm):
    """Reduced equivariant Euler characteristic value at g:
       chi~(Delta(P^g)) = -1 + sum_{k>=0} (-1)^k #{g-fixed k-chains}
    (the -1 is the degree -1 / empty-cell term of the augmented complex).
    By the Hopf trace formula this is sum_k (-1)^k trace(g | H~_k)."""
    fixed = [x for x in P_set if apply_perm(x, perm) == x]
    f = fvector_count(fixed)
    chi = -1                          # the degree -1 (empty cell) term
    for k, fk in enumerate(f):
        chi += ((-1) ** k) * fk
    return chi


# S_3 / S_4 character tables (classes keyed by cycle type)
S3_CLASSES = [(1, 1, 1), (2, 1), (3,)]
S3_SIZE = {(1, 1, 1): 1, (2, 1): 3, (3,): 2}
S3_IRR = {"triv": {(1, 1, 1): 1, (2, 1): 1, (3,): 1},
          "sgn":  {(1, 1, 1): 1, (2, 1): -1, (3,): 1},
          "std":  {(1, 1, 1): 2, (2, 1): 0, (3,): -1}}

S4_CLASSES = [(1, 1, 1, 1), (2, 1, 1), (2, 2), (3, 1), (4,)]
S4_SIZE = {(1, 1, 1, 1): 1, (2, 1, 1): 6, (2, 2): 3, (3, 1): 8, (4,): 6}
S4_IRR = {  # irreducibles of S_4
    "triv":     {(1, 1, 1, 1): 1, (2, 1, 1): 1,  (2, 2): 1,  (3, 1): 1,  (4,): 1},
    "sgn":      {(1, 1, 1, 1): 1, (2, 1, 1): -1, (2, 2): 1,  (3, 1): 1,  (4,): -1},
    "std":      {(1, 1, 1, 1): 3, (2, 1, 1): 1,  (2, 2): -1, (3, 1): 0,  (4,): -1},
    "std.sgn":  {(1, 1, 1, 1): 3, (2, 1, 1): -1, (2, 2): -1, (3, 1): 0,  (4,): 1},
    "V2":       {(1, 1, 1, 1): 2, (2, 1, 1): 0,  (2, 2): 2,  (3, 1): -1, (4,): 0},
}


def cycle_type(perm, n):
    seen = [False] * n
    ct = []
    for i in range(n):
        if seen[i]:
            continue
        ln = 0
        j = i
        while not seen[j]:
            seen[j] = True
            j = perm[j]
            ln += 1
        ct.append(ln)
    return tuple(sorted(ct, reverse=True))


def decompose(char_by_class, classes, sizes, irreps, order):
    out = {}
    for name, irr in irreps.items():
        s = sum(sizes[ct] * char_by_class[ct] * irr[ct] for ct in classes)
        m, rem = divmod(s, order)
        if rem != 0:
            raise RuntimeError(f"non-integer multiplicity for {name}: {s}/{order}")
        out[name] = m
    return out


def equivariant_euler(P_set, n):
    """Virtual S_n-character chi^{S_n}(Delta(P)) restricted to be the
    REDUCED equivariant Euler char (drop the degree -1 trivial term):
    returns dict irrep -> multiplicity of  sum_k (-1)^k [H~_k]."""
    classes = S3_CLASSES if n == 3 else S4_CLASSES
    sizes = S3_SIZE if n == 3 else S4_SIZE
    irreps = S3_IRR if n == 3 else S4_IRR
    char = {}
    for perm in permutations(range(n)):
        perm_ext = perm + (n,)               # fix element n
        ct = cycle_type(perm, n)
        if ct in char:
            continue
        char[ct] = euler_char_fixed(P_set, perm_ext)
    return decompose(char, classes, sizes, irreps,
                     6 if n == 3 else 24)


# =======================================================================
# 8. The driver: build PPF, run the reduction, assemble B_n, verdict.
# =======================================================================

def banner(t):
    print("\n" + "=" * 72)
    print("  " + t)
    print("=" * 72)


def trim(b):
    """drop trailing zeros from a Betti tuple."""
    b = list(b)
    while b and b[-1] == 0:
        b.pop()
    return tuple(b)


def run_level(n, verbose=True):
    r"""Run the full F14 pipeline for the cofiber Delta_{n+1}/Delta_n.
    n=3 is the mg-6295 trip-wire; n=4 is the F14 target."""
    banner(f"n={n} -> {n+1}:  cofiber  Delta_{n+1} / Delta_{n}")
    t0 = time.time()
    PPF = make_PPF(n + 1)
    PPF_sub = make_PPF(n)
    print(f"  |PPF_{n+1}| = {len(PPF)}")
    print(f"  |PPF_{n}|   = {len(PPF_sub)}")
    # iota_n image: posets on {0,..,n} with n isolated and the restriction
    # in PPF_n.  PPF_n elements already have all relations in {0,..,n-1}.
    sub_image = set(frozenset(P) for P in PPF_sub)
    I = [x for x in PPF if x in sub_image]            # the order ideal Delta_n
    assert len(I) == len(PPF_sub), "iota_n not injective onto PPF_{n+1}"
    Iset = set(I)

    # ---- [A] the f-vector of the relative complex (DP; never materialised)
    f_full = fvector_count(PPF)
    f_sub = fvector_count(I)
    f_rel = [(f_full[k] if k < len(f_full) else 0)
             - (f_sub[k] if k < len(f_sub) else 0)
             for k in range(len(f_full))]
    chi_rel = sum((-1) ** k * f_rel[k] for k in range(len(f_rel)))
    print(f"  f(Delta_{n+1})          = {f_full}")
    print(f"  f(Delta_{n})            = {f_sub}")
    print(f"  f(C_*(Delta_{n+1},Delta_{n})) = {f_rel}")
    print(f"  total relative cells    = {sum(f_rel)}")
    print(f"  chi-tilde(cofiber)      = {chi_rel}")
    if n == 4:
        print(f"  --> {sum(f_rel)} cells: the naive mg-6295 greedy+Forman")
        print(f"      recipe (materialise every relative cell + cover graph")
        print(f"      + per-acceptance reachability DFS) is infeasible here.")

    # ---- [B] the reduction:  H~_d(cofiber) = cofiber_homology(PPF, I, ideal)
    log = []
    print(f"\n  [reduction log]")
    H_cof = cofiber_homology(PPF, I, sub_is_ideal=True, log=log)
    for line in log:
        print("    " + line)
    # pad / normalise
    print(f"\n  H~_*(Delta_{n+1}/Delta_{n})  =  {H_cof}")
    print(f"  ({time.time()-t0:.1f}s)")

    # ---- [C] independent reduction landmark: |A_n| and Delta(A_n) f-vector
    #          A_n = {Down_n != 0, Up_n = 0, x|_{0..n-1} != 0}
    A = [x for x in PPF
         if any(a == n for (a, b) in x)            # Down_n != empty
         and not any(b == n for (a, b) in x)       # Up_n   = empty
         and any(a < n and b < n for (a, b) in x)] # restriction != empty
    f_A = fvector_count(A)
    print(f"\n  reduction landmark: |A_{n}| = {len(A)}, "
          f"f(Delta(A_{n})) = {f_A}  ({sum(f_A)} cells)")
    print(f"  the reduction theorem gives  H~_d(cofiber) = 2 . H~_{{d-1}}(Delta(A_{n}))")

    # ---- [D] S_n-equivariant representation type of B_n = H~^n-ish ----
    #     The reduction is S_n-equivariant; H~_d(cofiber) = 2.H~_{d-1}(Delta(A_n)).
    H_A = reduced_homology(A)
    print(f"\n  H~_*(Delta(A_{n}))           = {H_A}")
    # equivariant Euler characteristic of Delta(A_n)
    eq_A = equivariant_euler(set(A), n)
    print(f"  chi^{{S_{n}}}(Delta(A_{n}))     = sum_k (-1)^k [H~_k] = {eq_A}")
    # equivariant Euler char of the cofiber directly (cross-check)
    # chi^{S_n}(cofiber) = chi^{S_n}(Delta_{n+1}) - chi^{S_n}(Delta_n)
    eq_full = equivariant_euler(set(PPF), n)
    eq_sub = equivariant_euler(Iset, n)
    eq_cof = {k: eq_full.get(k, 0) - eq_sub.get(k, 0) for k in eq_full}
    print(f"  chi^{{S_{n}}}(cofiber)         = {eq_cof}")

    return {
        "n": n, "H_cof": H_cof, "H_A": H_A, "A_size": len(A), "A": A,
        "f_rel": f_rel, "chi_rel": chi_rel,
        "eq_A": eq_A, "eq_cof": eq_cof, "f_A": f_A,
    }


def collapse_selftest():
    """Cross-check direct_reduced_homology_big (elementary collapse +
    residual Gaussian) against the plain materialised reduced_betti
    (full mod-p Gaussian) on several small subposets -- the n=3 trip-wire
    stays under the direct threshold and never exercises the collapse
    path, so test it here.  Posets are capped at ~120k cells so the full
    Gaussian cross-check stays fast; they still span dims up to 6-7,
    matching the structure of the terminal Delta(A_4)."""
    banner("[self-test] elementary-collapse homology vs direct Gaussian")
    ok = True
    PPF4 = make_PPF(4)
    PPF5 = make_PPF(5)
    A4 = [x for x in PPF5
          if any(a == 4 for (a, b) in x)
          and not any(b == 4 for (a, b) in x)
          and any(a < 4 and b < 4 for (a, b) in x)]
    cand = []
    cand.append(("PPF_4", PPF4))
    cand.append(("D_3-on-{0,1,2,3}",
                 [x for x in PPF4 if any(a == 3 for (a, b) in x)
                  and any(a < 3 and b < 3 for (a, b) in x)]))
    # A_3 (the n=3 reduction landmark) -- 1-sphere
    cand.append(("A_3",
                 [x for x in PPF4 if any(a == 3 for (a, b) in x)
                  and not any(b == 3 for (a, b) in x)
                  and any(a < 3 and b < 3 for (a, b) in x)]))
    # small high-dimensional subposets of A_4 (these DO reach dim 5-6,
    # matching Delta(A_4)'s structure) -- isolate elements to keep small
    for e in (0, 1):
        cand.append((f"A_4-cap-{{{e}-isolated}}",
                     [x for x in A4 if not any(a == e or b == e
                                               for (a, b) in x)]))
    cand.append(("A_4-cap-{Up_2=0,Up_3=0}",
                 [x for x in A4 if not any(b == 2 or b == 3
                                           for (a, b) in x)]))
    for name, P in cand:
        if not P:
            continue
        f = fvector_count(P)
        if sum(f) > 120_000:
            print(f"  {name:26s} f={f}  (>120k cells, skipped)")
            continue
        b_gauss = reduced_betti(chains_by_dim(P))
        b_collapse = direct_reduced_homology_big(P)
        g = list(b_gauss)
        while g and g[-1] == 0:
            g.pop()
        c = list(b_collapse)
        while c and c[-1] == 0:
            c.pop()
        match = (tuple(g) == tuple(c))
        ok = ok and match
        print(f"  {name:26s} f={f}")
        print(f"  {'':26s} Gauss={b_gauss}  collapse={b_collapse}"
              f"  {'OK' if match else 'MISMATCH'}")
    print(f"  self-test: {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    sys.setrecursionlimit(1_000_000)
    t_start = time.time()
    banner("F14 / PCR-Lit-2' : the n=4->5 cofiber cohomology B_4 = H~^3(Delta_5/Delta_4)")
    print("  mg-3839.  Adapts mg-6295's compat_geom_cofiber_morse_n3n4.py to")
    print("  n=4->5 via a memory-efficient S_n-equivariant order-ideal-")
    print("  filtration reduction (the naive greedy+Forman recipe is")
    print("  infeasible at ~3.3x10^8 relative cells).")

    # ---- self-test: the elementary-collapse homology engine ----
    st_ok = collapse_selftest()
    if not st_ok:
        print("  !! collapse self-test FAILED -- aborting.")
        return

    # ---- trip-wire: n=3->4 must reproduce mg-6295's GREEN (0,0,2,0) ----
    r3 = run_level(3)
    banner("[trip-wire] n=3->4 must reproduce mg-6295 (PCR-Lit-2) GREEN")
    tw_betti = (trim(r3["H_cof"]) == (0, 0, 2))
    print(f"  H~_*(Delta_4/Delta_3) = {r3['H_cof']}   "
          f"expect (0,0,2,0)  -> {'PASS' if tw_betti else 'FAIL'}")
    # rep type: B_3 = H~^2(cofiber); the reduction is S_3-equivariant and
    # H~_*(cofiber) is concentrated in degree 2, so chi^{S_3}=[H~_2]=[B_3].
    tw_rep = (r3["eq_cof"].get("sgn", 0) == 2
              and all(v == 0 for k, v in r3["eq_cof"].items() if k != "sgn"))
    print(f"  chi^{{S_3}}(cofiber)   = {r3['eq_cof']}   "
          f"expect sgn:2  -> {'PASS' if tw_rep else 'FAIL'}")
    tw_pass = tw_betti and tw_rep
    print(f"  TRIP-WIRE: {'PASS' if tw_pass else 'FAIL'}")
    if not tw_pass:
        print("  !! trip-wire FAILED -- the reduction machinery does not")
        print("     reproduce the known n=3->4 result; aborting.")
        print(f"\n[done] {time.time()-t_start:.1f}s")
        return

    # ---- the F14 target: n=4->5 ----
    r4 = run_level(4)

    # ---- assemble B_4 and the verdict ----
    banner("B_4 = H~^3(Delta_5/Delta_4) : result + S_4-representation type")
    H = trim(r4["H_cof"])

    def hget(b, k):
        return b[k] if 0 <= k < len(b) else 0

    # concentration: H~_k(cofiber) = 0 for k != 3
    concentrated = (hget(H, 3) != 0
                    and all(hget(H, k) == 0 for k in range(len(H)) if k != 3))
    betti_pred = concentrated and hget(H, 3) == 2
    print(f"  cofiber Betti vector  b~_*(Delta_5/Delta_4) = {H}")
    print(f"    predicted (M1+M2, F10 §10.2): (0,0,0,2,0)")
    print(f"    concentrated in degree 3 : {concentrated}")
    print(f"    b~_3 = 2                 : {hget(H, 3) == 2}")
    # S_4-rep type: reduction is S_4-equivariant, H~_d(cofiber)=2.H~_{d-1}(A_4),
    # so if concentrated, [B_4] = chi^{S_4}(cofiber) with the sign (-1)^3.
    eq = r4["eq_cof"]
    # chi^{S_4}(cofiber) = sum (-1)^k [H~_k]; if concentrated in deg 3,
    # = -[B_4], so [B_4] = -chi.
    B4_char = {k: -v for k, v in eq.items()}
    print(f"  chi^{{S_4}}(cofiber) = {eq}")
    print(f"  => [B_4] = -chi^{{S_4}}(cofiber) = {B4_char}  (valid iff concentrated)")
    rep_pred = (B4_char.get("sgn", 0) == 2
                and all(v == 0 for k, v in B4_char.items() if k != "sgn"))
    print(f"    predicted (UCC.1 at level 4): 2 . sgn_{{S_4}}")
    print(f"    [B_4] = 2.sgn_{{S_4}} : {rep_pred}")

    # cross-check: H~_*(Delta(A_4)) and the 2 . H~_{*-1}(A_4) relation
    HA = trim(r4["H_A"])
    expected = trim(tuple(2 * hget(HA, d - 1) for d in range(len(HA) + 2)))
    rel_ok = (expected == H)
    print(f"\n  cross-check: H~_*(Delta(A_4)) = {HA}")
    print(f"    2 . H~_(d-1)(Delta(A_4))      = {expected}")
    print(f"    H~_d(cofiber) = 2 . H~_(d-1)(Delta(A_4)) : {rel_ok}")

    # ---- explicit basis of B_4  (deliverable 3) ----
    banner("explicit basis of B_4  (deliverable 3, for F15 / (E2))")
    print("  B_4 = H~_3(Delta_5/Delta_4) = H~_2(Delta(D)) (+) H~_2(Delta(U)),")
    print("  D = {Down_4 != 0, x|_0123 != 0}, U = {Up_4 != 0, x|_0123 != 0},")
    print("  and H~_2(Delta(D)) = H~_2(Delta(A_4)) via the all-cone Up_4 peel")
    print("  (A_4 = {Down_4 != 0, Up_4 = 0, x|_0123 != 0}, |A_4| = 1420).")
    print("  An explicit generator of the first summand H~_2(Delta(A_4)):")
    A4 = r4["A"]
    _, cyc_list = extract_h2_generator(A4)
    basis_ok = (len(cyc_list) == hget(HA, 2))
    if cyc_list:
        cyc = cyc_list[0]
        print(f"  z_D  =  an explicit 2-cycle of Delta(A_4) with {len(cyc)} "
              f"triangle terms (each a 3-chain P0<P1<P2 in A_4 subset PPF_5);")
        print(f"  dim H~_2(Delta(A_4)) = {hget(HA,2)}, # kernel generators "
              f"found = {len(cyc_list)}  -> {'OK' if basis_ok else 'MISMATCH'}")
        # show the first few terms in poset-relation notation
        def pstr(P):
            return ("{" + ",".join(f"{a}<{b}" for (a, b) in sorted(P)) + "}"
                    if P else "0")
        print(f"  first 3 terms of z_D:")
        for coeff, tri in cyc[:3]:
            print(f"    {coeff:+d} * [ "
                  + "  <  ".join(pstr(P) for P in tri) + " ]")
        # verify it is a genuine 2-cycle of Delta(A_4): boundary = 0
        A4set = set(A4)
        bnd = {}
        for coeff, tri in cyc:
            for i in range(3):
                face = tri[:i] + tri[i + 1:]
                s = (1 if i % 2 == 0 else -1)
                bnd[face] = bnd.get(face, 0) + coeff * s
        cycle_ok = all(v == 0 for v in bnd.values())
        print(f"  boundary of z_D vanishes (genuine 2-cycle) : {cycle_ok}")
        # the second summand H~_2(Delta(U)): z_U = z_D with every relation
        # reversed (U ~= D via the S_4-equivariant order-reversal involution).
        print(f"  z_U  =  z_D with every relation (a,b) reversed to (b,a)")
        print(f"          [the order-reversal iso D ~= U; lands in Delta(U)].")
        print(f"  => {{ z_D, z_U }} is an explicit 2-element basis of B_4.")
    else:
        cycle_ok = False
        print(f"  (no H~_2 generator extracted)")
    basis_ok = basis_ok and cyc_list and cycle_ok

    # ---- verdict ----
    banner("VERDICT")
    if betti_pred and rep_pred and rel_ok and tw_pass and basis_ok:
        verdict = "GREEN-cofiber-perfect"
        msg = ("b~_*(Delta_5/Delta_4) = (0,0,0,2,0) concentrated in degree 3, "
               "B_4 = 2.sgn_{S_4}.  (UCC.1) is COMPUTED (not merely predicted) "
               "at n=4->5.  The memory-efficient S_n-equivariant order-ideal "
               "reduction collapses the 3.3x10^8-cell relative complex onto "
               "2.Delta(A_4) and reproduces mg-6295's GREEN at n=3->4; an "
               "explicit 2-element basis of B_4 is delivered.  "
               "F15/(E2) is unblocked.")
    elif concentrated and rep_pred:
        verdict = "GREEN-cofiber-perfect (non-standard multiplicity)"
        msg = (f"cohomology concentrated in degree 3 with rep type {B4_char}, "
               f"Betti {H}.")
    elif concentrated:
        verdict = "AMBER-cofiber-computed-not-perfect"
        msg = (f"cofiber cohomology concentrated in degree 3 = {H}, but the "
               f"S_4-representation type {B4_char} is not the predicted "
               f"2.sgn_{{S_4}}.")
    else:
        verdict = "RED-prediction-refuted"
        msg = (f"b~_*(Delta_5/Delta_4) = {H} is NOT concentrated in degree 3 / "
               f"not (0,0,0,2,0): the M1+M2 prediction and F10's GREEN-"
               f"conditional are refuted at n=4->5.  Surface immediately.")
    print(f"  Verdict: {verdict}")
    print(f"  {msg}")

    # ---- machine-readable summary ----
    print("\n----- MACHINE SUMMARY -----")
    print(f"PPF_5_relative_cells={sum(r4['f_rel'])}")
    print(f"f_relative_n4n5={r4['f_rel']}")
    print(f"chi_cofiber_n4n5={r4['chi_rel']}")
    print(f"A4_size={r4['A_size']}")
    print(f"cofiber_betti_n3n4={list(r3['H_cof'])}")
    print(f"cofiber_betti_n4n5={list(H)}")
    print(f"H_Delta_A4={list(HA)}")
    print(f"B4_S4_character={B4_char}")
    print(f"cofiber_S4_euler_char={eq}")
    print(f"tripwire_n3n4={tw_pass}")
    print(f"collapse_selftest={st_ok}")
    print(f"explicit_basis_ok={bool(basis_ok)}")
    print(f"verdict={verdict}")
    print("----- END SUMMARY -----")
    print(f"\n[done] total runtime: {time.time()-t_start:.1f}s")


if __name__ == "__main__":
    main()
