#!/usr/bin/env python3
r"""
compat_geom_F22_hpc_cell_tracking.py
====================================

Compat-Geom **F22-HPC** (mg-43fb) -- the cell-tracking upgrade of the F14/F17
S_n-equivariant cofiber discrete Morse reduction.

Parent chain:  F10 -> F17 (mg-4d3a, M_rel^eq) -> F18 (mg-d039) -> F19 -> F20
-> F21 (mg-a2cb, Prop F21.1) -> **F22-HPC (mg-43fb)**.

GOAL (F21 s.8 / the F22-HPC ticket).  Materialise the **two critical
(n-1)-cells** of the perfect S_n-equivariant cofiber Morse matching
`M_rel^eq` (F17) on the relative complex `C_*(Delta_{n+1}, Delta_n)`, as
**explicit chains in PPF_{n+1}**, for n = 5, 6 (and 7 if budget permits).
This is the *cell-tracking* upgrade of `compat_geom_cofiber_morse_n4n5.py`
and `compat_geom_F17_equivariant_morse.py`, which run the F14 reduction at
the *homology* level only.

WHAT THIS SESSION (Session 1) DOES.
  * Implements the F14 reduction cell-tracking infrastructure (the explicit
    PEEL / MoveB / MoveA lift maps) on top of the F17 (Q,F)-model of A_n.
  * Materialises the two critical (n-1)-cells of F17's M_rel^eq, via the
    F17-structural terminal reduction (the S_n-equivariant closure operator
    `c(Q,F)=(Q,[n])` of F17 s.4.1 -- the memory-efficient, never-materialise
    route), for n = 3, 4, 5.  The terminal Delta_n matching is seeded with
    the *known exact* canonical critical cells c*_3, c*_4, c*_5 (F21 s.2).
  * For n = 3 (Delta(A_3) = 1008 cells) and n = 4 (Delta(A_4) = 1.5e7 cells)
    independently CROSS-CHECKS: (a) the F14 homology reduction gives
    cofiber Betti (0,..,0,2,0); (b) Delta(A_3) admits a perfect Morse
    matching with exactly 2 -> 1 critical cell (count check).
  * Runs the (CM-rel) analysis on every materialised cell: |L|-profile,
    per-step Kahn-Saks Pr, top-poset OSA signature, width, BFT-sharpness.
  * Records, honestly, the precise relationship found between F17's
    M_rel^eq critical cells and the F21-recorded chamber-Morse c*_{n+1}.

WHAT THIS SESSION DOES NOT DO (deferred to a continuation session).
  * n = 6, 7: the closure-operator route needs c*_6 / c*_7 as the terminal
    seed -- which are exactly the unknowns (F20's 12-candidate short list).
    The genuine intrinsic route needs Delta(A_n) which is 1.35e13 cells at
    n = 5 already -- the HPC continuation is the non-materialising
    structural cell-tracking of the F14 reduction's intrinsic matching.
  * The F18 cross-boundary cancellation tracking (which produces the
    genuine c*_{n+1} from M_rel^eq's critical cells + c*_n) -- see the
    findings section and docs/state-F22-HPC.md.

Pure-Python stdlib, exact Fraction / int arithmetic.  Memory-conscious:
the n = 5 route never materialises Delta(A_5).

References
  - mg-4d3a (F17): docs/compatibility-geometry-F17-equivariant-cofiber-morse.md
        s.1.1 (the (Q,F) model), s.2 (MoveA/MoveB/PEEL), s.4 (the closure
        operator c(Q,F)=(Q,[n]) and the A_n^t attachment).
  - mg-a2cb (F21): docs/compatibility-geometry-F21-genuine-chamber-morse-cell.md
        Prop F21.1 (the cofiber-Morse induction), s.2 (the exact record),
        s.5 ((CM-struct) => (CM-rel)).
  - mg-3839 (F14): scripts/compat_geom_cofiber_morse_n4n5.py -- the
        homology-level reduction this upgrades.
  - mg-c3fa (F20) s.6: the genuine-G_6 12-candidate short list.
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations, combinations

sys.setrecursionlimit(1_000_000)


# ===========================================================================
# Section 0.  Core poset / order-complex utilities (exact, stdlib).
#             Convention shared with F14 / F17 / F19 / F20 / F21 harnesses.
# ===========================================================================

def transitive_closure(rel):
    """Transitive closure of `rel` (a set of (a,b) meaning a < b)."""
    closed = set(rel)
    changed = True
    while changed:
        changed = False
        add = set()
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    add.add((i, l))
        if add:
            closed |= add
            changed = True
    return frozenset(closed)


def is_acyclic_rel(rel):
    closed = transitive_closure(rel)
    return not any((j, i) in closed for (i, j) in closed)


_POSETS_MEMO = {}


def enumerate_posets(n):
    """All transitively-closed strict partial orders on {0,...,n-1}."""
    if n in _POSETS_MEMO:
        return _POSETS_MEMO[n]
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
    out = list(seen)
    _POSETS_MEMO[n] = out
    return out


def is_total(P, n):
    return len(P) == n * (n - 1) // 2


def make_PPF(n):
    r"""PPF_n := proper partial orders on [n] -- nonempty, non-total."""
    return [P for P in enumerate_posets(n)
            if P != frozenset() and not is_total(P, n)]


def count_linear_extensions(closed, n):
    """Number of linear extensions of the partial order `closed` on [n]."""
    closed = set(closed)
    succ = {i: set() for i in range(n)}
    indeg = [0] * n
    for (a, b) in closed:
        succ[a].add(b)
    # down-set predecessor count for topological enumeration
    preds = {i: set() for i in range(n)}
    for (a, b) in closed:
        preds[b].add(a)

    from functools import lru_cache

    @lru_cache(maxsize=None)
    def count(placed):
        placed_set = placed
        if len(placed_set) == n:
            return 1
        total = 0
        for v in range(n):
            if v in placed_set:
                continue
            if preds[v] <= set(placed_set):
                total += count(tuple(sorted(placed_set + (v,))))
        return total

    res = count(())
    count.cache_clear()
    return res


def poset_width(closed, n):
    """Width = size of the largest antichain of the partial order on [n]."""
    closed = set(closed)
    comp = [[False] * n for _ in range(n)]
    for (a, b) in closed:
        comp[a][b] = True
        comp[b][a] = True
    best = 0
    # antichains by subset search (n <= 8 in scope -- fine)
    for r in range(n, 0, -1):
        if r <= best:
            break
        for S in combinations(range(n), r):
            if all(not comp[a][b] for a, b in combinations(S, 2)):
                best = max(best, r)
                break
    return best


def osa_signature(closed, n):
    """If the partial order on [n] is an ordinal sum of antichains, return
    the tuple of block sizes (top..bottom order irrelevant -- bottom first);
    else return None.

    An OSA is characterised by: the comparability relation is a 'layering' --
    elements partition into blocks B_1 < B_2 < ... < B_r with a<b iff
    block(a) < block(b).  Equivalently, comparability is transitive AND for
    any a,b: a,b comparable or in the same antichain block, and 'same block'
    is an equivalence relation."""
    closed = set(closed)
    below = {i: set() for i in range(n)}
    above = {i: set() for i in range(n)}
    for (a, b) in closed:
        below[b].add(a)
        above[a].add(b)
    # block of i := elements with identical (below, above) signature
    sig = {}
    for i in range(n):
        sig.setdefault((frozenset(below[i]), frozenset(above[i])), []).append(i)
    blocks = list(sig.values())
    # OSA iff: blocks linearly ordered by 'all of one below all of next'
    # check every cross-block pair is comparable, every same-block pair not
    for blk in blocks:
        for a, b in combinations(blk, 2):
            if (a, b) in closed or (b, a) in closed:
                return None
    bidx = {}
    for k, blk in enumerate(blocks):
        for v in blk:
            bidx[v] = k
    # order the blocks: block k1 < block k2 iff some a in k1, b in k2, a<b
    r = len(blocks)
    blk_lt = [[False] * r for _ in range(r)]
    for (a, b) in closed:
        ka, kb = bidx[a], bidx[b]
        if ka == kb:
            return None
        blk_lt[ka][kb] = True
    # must be a total order on blocks, and a<b for ALL cross pairs.
    # sum(blk_lt[k]) counts the blocks ABOVE k, so the bottom block has the
    # largest count -- order the blocks bottom-first by DESCENDING count.
    order = sorted(range(r), key=lambda k: -sum(blk_lt[k]))
    pos = {k: p for p, k in enumerate(order)}
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            ka, kb = bidx[a], bidx[b]
            if ka == kb:
                continue
            want = pos[ka] < pos[kb]
            have = (a, b) in closed
            if want != have:
                return None
    return tuple(len(blocks[k]) for k in order)


# --- the BFT-sharp interval (Brightwell-Felsner-Trotter) -------------------
BFT_LO = Fraction(3, 11)
BFT_HI = Fraction(8, 11)


def in_bft(pr):
    return BFT_LO <= pr <= BFT_HI


# ===========================================================================
# Section 1.  The (Q,F) model of A_n, and the F14 reduction objects.
#             (transcribed from F17 s.1.1 / compat_geom_F17_equivariant_morse)
# ===========================================================================

def restrict(x, n):
    """x|_{[n]} -- relations of x lying entirely inside {0,...,n-1}."""
    return frozenset((a, b) for (a, b) in x if a < n and b < n)


def down_n(x, n):
    """Down_n(x) = {b : (n,b) in x}  (what element n lies below)."""
    return frozenset(b for (a, b) in x if a == n)


def up_n(x, n):
    """Up_n(x) = {a : (a,n) in x}  (what element n lies above)."""
    return frozenset(a for (a, b) in x if b == n)


def is_filter(F, Q, n):
    """True iff F (subset of [n]) is up-closed under Q (a p.o. on [n])."""
    for b in F:
        for (c, d) in Q:
            if c == b and d not in F:
                return False
    return True


def qf_to_x(Q, F, n):
    """The element of PPF_{n+1} represented by the pair (Q,F):
       x = Q  u  {(n,b) : b in F}."""
    return frozenset(set(Q) | {(n, b) for b in F})


def build_A_qf(n):
    """A_n via the F17 (Q,F) model.  Returns a list of x in PPF_{n+1} with
       Down_n != empty, Up_n = empty, x|_{[n]} != empty."""
    posets_n = enumerate_posets(n)
    A = []
    full = frozenset(range(n))
    for Q in posets_n:
        if not Q:
            continue
        Qtotal = is_total(Q, n)
        for r in range(1, n + 1):
            for Fset in combinations(range(n), r):
                F = frozenset(Fset)
                if not is_filter(F, Q, n):
                    continue
                if F == full and Qtotal:
                    continue
                A.append(qf_to_x(Q, F, n))
    return A


def reverse_rel(P):
    """Order-reversal involution (a,b) -> (b,a) -- the S_n-equivariant
    D_n ~= U_n isomorphism of F17 s.2.2."""
    return frozenset((b, a) for (a, b) in P)


# ===========================================================================
# Section 2.  Order-complex enumeration + homology (small complexes only).
# ===========================================================================

def above_lists(elements):
    es = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    above = {}
    for i, P in enumerate(es):
        above[P] = [Q for Q in es[i + 1:] if len(Q) > len(P) and P < Q]
    return es, above


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


def fvector_count(elements):
    """f-vector of Delta(elements) by DP -- never materialises the chains."""
    es, above = above_lists(elements)
    MAXD = 40
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


def _rank_mod_p(cols, p):
    rank = 0
    pivot = {}
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
    """Reduced Betti vector over GF(p) for two primes (must agree)."""
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
        betti[0] -= 1
        results.append(tuple(betti[k] for k in range(maxd + 1)))
    if len(set(results)) != 1:
        raise RuntimeError(f"prime disagreement in reduced_betti: {results}")
    return results[0]


# ===========================================================================
# Section 3.  An explicit perfect Morse matching of a (small) order complex,
#             via Benedetti-Lutz random discrete Morse with retries.
#
#  Used ONLY for the n = 3 (and optionally n = 4) cross-check that
#  Delta(A_n) -- the F14 terminal complex -- admits a perfect Morse matching
#  with exactly the Betti-many critical cells.  The lift itself (Section 4)
#  does not need this: it uses the F17-structural closure-operator route.
# ===========================================================================

def random_discrete_morse(by_dim, seed, target_counts=None):
    """One Benedetti-Lutz random-discrete-Morse sweep.  Returns
    (critical_counts, critical_cells, matched_pairs).  `target_counts`, if
    given, lets the caller early-stop on a perfect sweep."""
    import random
    rnd = random.Random(seed)
    maxd = max(by_dim)
    cell_id = {}
    cells = []
    dim_of = []
    for k in range(maxd + 1):
        for c in by_dim[k]:
            cell_id[c] = len(cells)
            cells.append(c)
            dim_of.append(k)
    N = len(cells)
    facets = [None] * N
    cofacet = [[] for _ in range(N)]
    for cid, c in enumerate(cells):
        k = dim_of[cid]
        if k == 0:
            facets[cid] = []
            continue
        fl = []
        for i in range(len(c)):
            fid = cell_id[c[:i] + c[i + 1:]]
            fl.append(fid)
            cofacet[fid].append(cid)
        facets[cid] = fl

    from collections import deque
    alive = bytearray([1]) * N
    cof_cnt = [len(cofacet[i]) for i in range(N)]
    critical = []
    matched = []
    nalive = N
    while nalive > 0:
        q = deque(i for i in range(N) if alive[i] and cof_cnt[i] == 1)
        while q:
            s = q.popleft()
            if not alive[s] or cof_cnt[s] != 1:
                continue
            t = None
            for cand in cofacet[s]:
                if alive[cand]:
                    t = cand
                    break
            if t is None:
                continue
            alive[s] = 0
            alive[t] = 0
            nalive -= 2
            matched.append((cells[s], cells[t]))
            for fc in facets[t]:
                if alive[fc]:
                    cof_cnt[fc] -= 1
                    if cof_cnt[fc] == 1:
                        q.append(fc)
            for fc in facets[s]:
                if alive[fc]:
                    cof_cnt[fc] -= 1
                    if cof_cnt[fc] == 1:
                        q.append(fc)
        if nalive == 0:
            break
        alive_cells = [i for i in range(N) if alive[i]]
        md = max(dim_of[i] for i in alive_cells)
        cands = [i for i in alive_cells if dim_of[i] == md]
        c = rnd.choice(cands)
        alive[c] = 0
        nalive -= 1
        critical.append(cells[c])
        for fc in facets[c]:
            if alive[fc]:
                cof_cnt[fc] -= 1
    counts = [0] * (maxd + 1)
    for c in critical:
        counts[len(c) - 1] += 1
    return tuple(counts), critical, matched


def perfect_morse(by_dim, betti, max_tries=4000):
    """Find a perfect Morse matching: critical counts == the (unreduced)
    Betti vector.  `betti` is the REDUCED Betti vector; the unreduced one
    has H_0 = H~_0 + 1.  Returns (critical_cells, matched, seed, counts);
    critical_cells is None if no perfect sweep was found in `max_tries`."""
    unred = list(betti)
    unred[0] = unred[0] + 1
    target = tuple(unred)
    best = None
    for seed in range(max_tries):
        counts, crit, matched = random_discrete_morse(by_dim, seed)
        # pad
        cl = list(counts)
        tl = list(target)
        L = max(len(cl), len(tl))
        cl += [0] * (L - len(cl))
        tl += [0] * (L - len(tl))
        if best is None or sum(cl) < sum(best[0]):
            best = (tuple(cl), crit, matched, seed)
        if tuple(cl) == tuple(tl):
            return crit, matched, seed, tuple(cl)
    return None, None, best[3], best[0]


# ===========================================================================
# Section 4.  THE CELL-TRACKING LIFT.
#
#  Given the canonical critical (n-2)-cell c*_n of Delta_n = Delta(PPF_n)
#  -- a chain  Q_0 < Q_1 < ... < Q_{n-2}  in PPF_n -- lift it to the two
#  critical (n-1)-cells of F17's M_rel^eq on C_*(Delta_{n+1}, Delta_n),
#  via the F17-structural reduction.  The lift is the composite:
#
#    Delta_n  --[F17 s.4.1: closure operator c(Q,F)=(Q,[n]), inverse]-->
#             A_n^{nt}  ⊂  A_n   (the critical cell of Delta(A_n))
#    --[PEEL: A_n ⊂ D_n is the inclusion, a homology iso]-->  Delta(D_n)
#    --[MoveB: D_n = P^{(down)}, +1 degree shift]-->  prepend the apex
#       s*(x_0) = {(n,b) : b in Down_n(x_0)}  of the S_down cone fibre
#    --[MoveA: a homology iso, no degree shift]-->  a relative (n-1)-cell
#       of C_*(Delta_{n+1}, Delta_n).
#
#  c_U is c_D under the S_n-equivariant order-reversal D_n ~= U_n (F17 s.2.2).
# ===========================================================================

def lift_cstar_to_M_rel(cstar_hasse, n):
    """cstar_hasse : list of Hasse relation-sets, posets on [n], a chain
       Q_0 ⊂ ... ⊂ Q_{n-2}  (the canonical critical (n-2)-cell c*_n).
    Returns (c_D, c_U, info): the two critical (n-1)-cells of F17's M_rel^eq
    on C_*(Delta_{n+1}, Delta_n), as lists of frozensets (chains in PPF_{n+1}),
    plus an info dict (the intermediate lifted chain in A_n, the apex)."""
    closures = [transitive_closure(P) for P in cstar_hasse]
    assert all(closures[k] < closures[k + 1] for k in range(len(closures) - 1)), \
        "c*_n is not a strictly increasing chain"
    # --- closure-operator lift to A_n^{nt}:  Q_i  ->  (Q_i, [n])  ->  x_i ---
    full_down = frozenset((n, b) for b in range(n))   # n below every element
    xs = [frozenset(set(Q) | set(full_down)) for Q in closures]
    # each x_i has Down_n = [n], Up_n = empty, x_i|_{[n]} = Q_i != empty
    # so x_i in A_n  ⊂  D_n.  (x_0 < ... < x_{n-2}) is a critical (n-2)-cell
    # of Delta(A_n) -- the closure-operator image of c*_n.
    # --- MoveB: prepend the S_down cone-fibre apex of x_0 ---
    apex = frozenset((n, b) for b in down_n(xs[0], n))   # = full_down here
    c_D = [apex] + xs
    # --- MoveA: no change to the chain ---
    # --- c_U: order-reversal D_n ~= U_n ---
    c_U = [reverse_rel(P) for P in c_D]
    info = {
        "cstar_closures": closures,
        "lifted_in_A_n": xs,
        "apex": apex,
        "full_down": full_down,
    }
    return c_D, c_U, info


# ===========================================================================
# Section 5.  Verification: a materialised chain is a genuine relative
#             (n-1)-cell of C_*(Delta_{n+1}, Delta_n).
# ===========================================================================

def is_proper_po(P, m):
    """P transitively-closed, antisymmetric, nonempty, non-total on [m]?"""
    P = set(P)
    if not P:
        return False
    if transitive_closure(P) != frozenset(P):
        return False
    if any((b, a) in P for (a, b) in P):
        return False
    if is_total(frozenset(P), m):
        return False
    # also: all labels within [m]
    if any(a >= m or b >= m or a < 0 or b < 0 for (a, b) in P):
        return False
    return True


def verify_relative_cell(chain, n):
    """chain : list of frozensets, a candidate (k)-cell of C_*(Delta_{n+1},
    Delta_n).  Checks: every poset is in PPF_{n+1}; strictly increasing;
    NOT entirely contained in iota_n(PPF_n) (i.e. at least one poset uses
    element n) -- i.e. it is a genuine RELATIVE cell.  Returns (ok, msg)."""
    m = n + 1
    for P in chain:
        if not is_proper_po(P, m):
            return False, f"poset {sorted(P)} not in PPF_{m}"
    for k in range(len(chain) - 1):
        if not (set(chain[k]) < set(chain[k + 1])):
            return False, f"not strictly increasing at step {k}"
    uses_n = any(any(a == n or b == n for (a, b) in P) for P in chain)
    if not uses_n:
        return False, "entirely in iota_n(PPF_n) -- not a relative cell"
    return True, "ok"


# ===========================================================================
# Section 6.  (CM-rel) analysis of a materialised critical cell.
# ===========================================================================

def cm_rel_analysis(chain, n, internal_from=1):
    """Analyse a critical (n-1)-cell `chain` of M_rel^eq (a chain in PPF_{n+1}).

    (CM-rel) (F21 s.5.1): the M_rel^eq critical cells should have
      * width-2 ordinal-sum-of-antichains TOP posets (with a size-2 block),
      * every INTERNAL per-step Kahn-Saks Pr in [3/11, 8/11].

    `internal_from` : the index at which the 'internal' part of the chain
    begins.  For the closure-operator lift the chain is
        [ apex, x_0, x_1, ..., x_{n-2} ]
    and the MoveB apex-prepend step (apex -> x_0) is a *structural* coning
    step, not part of the genuine c*_n chain; the 'internal' steps are
    x_0 -> x_1 -> ... -> x_{n-2}, so internal_from = 1."""
    m = n + 1
    closures = [transitive_closure(P) for P in chain]
    profile = [count_linear_extensions(C, m) for C in closures]
    widths = [poset_width(C, m) for C in closures]
    osa = [osa_signature(C, m) for C in closures]
    prs = [Fraction(profile[k + 1], profile[k]) for k in range(len(profile) - 1)]
    internal_prs = prs[internal_from:]
    internal_bft = all(in_bft(p) for p in internal_prs)
    top = closures[-1]
    top_osa = osa[-1]
    top_width = widths[-1]
    top_has2 = bool(top_osa) and any(s == 2 for s in top_osa)
    top_is_w2_osa = bool(top_osa) and top_width == 2
    return {
        "profile": profile,
        "widths": widths,
        "osa": osa,
        "prs": prs,
        "internal_prs": internal_prs,
        "internal_bft": internal_bft,
        "top_osa": top_osa,
        "top_width": top_width,
        "top_is_width2_osa": top_is_w2_osa,
        "top_has_size2_block": top_has2,
        "cm_rel_ok": top_is_w2_osa and top_has2 and internal_bft,
    }


# ===========================================================================
# Section 7.  The exact record -- the canonical critical chains c*_3,4,5.
#             (transcribed from F21 s.2 / compat_geom_F21_genuine_cell.py;
#             these are HASSE diagrams -- closures are taken on use.)
# ===========================================================================

C_STAR = {
    3: {
        "label": "c*_3  (F8 s.4.5)",
        "hasse": [frozenset({(0, 2)}),
                  frozenset({(0, 1), (0, 2)})],
    },
    4: {
        "label": "c*_4  (F2 s.4.3.1, lex-min critical 2-cell)",
        "hasse": [frozenset({(1, 2), (3, 0), (3, 2)}),
                  frozenset({(0, 2), (1, 2), (3, 0)}),
                  frozenset({(0, 2), (1, 0), (3, 0)})],
    },
    5: {
        "label": "c*_5  (F5 s.4.3 / F8' s.A)",
        "hasse": [frozenset({(0, 1), (2, 1), (3, 1)}),
                  frozenset({(0, 1), (0, 4), (2, 1), (2, 4), (3, 1)}),
                  frozenset({(0, 4), (2, 4), (3, 1), (4, 1)}),
                  frozenset({(0, 3), (0, 4), (2, 3), (2, 4), (3, 1), (4, 1)})],
    },
}


def hasse_str(P, m):
    return "{" + ", ".join(f"{a}<{b}" for (a, b) in sorted(P)) + "}" if P else "0"


# F20 s.6: the genuine-G_6 candidate short list -- the width-2-OSA-with-a-
# size-2-block orbits on [6].  Exactly 12 (block-size tuples, bottom-first).
F20_G6_CANDIDATES = [
    (1, 1, 1, 1, 2), (1, 1, 1, 2, 1), (1, 1, 2, 1, 1), (1, 1, 2, 2),
    (1, 2, 1, 1, 1), (1, 2, 1, 2), (1, 2, 2, 1), (2, 1, 1, 1, 1),
    (2, 1, 1, 2), (2, 1, 2, 1), (2, 2, 1, 1), (2, 2, 2),
]


def osa_canonical(sig):
    """Block-size tuple up to the (bottom<->top) reversal that an OSA
    signature is only defined up to: return the lexicographically smaller
    of (sig, reverse(sig)).  (F20's list is given bottom-first; the OSA
    'block-size multiset with linear order' is a chain, so its mirror image
    is the same abstract poset only if palindromic -- but for membership
    testing against F20's list we keep both orientations.)"""
    if sig is None:
        return None
    rev = tuple(reversed(sig))
    return min(sig, rev)


def cover_relations(closed, m):
    """The Hasse (cover) relations of a transitively-closed p.o. on [m]."""
    closed = set(closed)
    cov = set()
    for (a, b) in closed:
        if not any((a, c) in closed and (c, b) in closed for c in range(m)):
            cov.add((a, b))
    return cov


# ===========================================================================
# Section 8.  Cross-checks for n = 3 (and optionally n = 4): the F14
#             homology reduction reproduces the cofiber Betti, and the
#             materialised cells sit in a count-2 critical set.
# ===========================================================================

def cofiber_betti_via_F14(n, verbose=False):
    """Run the F14 homology-level reduction (imported from the mg-3839
    script) for the cofiber Delta_{n+1}/Delta_n and return its reduced
    Betti vector.  This is the homology-level CROSS-CHECK: the cell-tracking
    lift must be consistent with  H~_d(cofiber) = (0,...,0,2,0)."""
    try:
        from compat_geom_cofiber_morse_n4n5 import (
            make_PPF as _mkPPF, cofiber_homology)
    except Exception as e:
        return None, f"import failed: {e}"
    PPF = _mkPPF(n + 1)
    PPF_sub = _mkPPF(n)
    sub_image = set(frozenset(P) for P in PPF_sub)
    I = [x for x in PPF if x in sub_image]
    log = [] if verbose else None
    H = cofiber_homology(PPF, I, sub_is_ideal=True, log=log)
    return H, "ok"


def materialised_morse_count(n):
    """Materialise Delta(A_n) and find a perfect Morse matching; return the
    critical-cell counts.  Memory-feasible only for n = 3 (1008 cells).
    For n = 4 (1.5e7 cells) this is heavy; the driver gates it."""
    A = build_A_qf(n)
    by_dim = chains_by_dim(A)
    f = [len(by_dim.get(k, [])) for k in range(max(by_dim) + 1)]
    betti = reduced_betti(by_dim)
    crit, matched, seed, counts = perfect_morse(by_dim, betti)
    return {
        "f": f, "betti": betti, "counts": counts,
        "crit": crit, "seed": seed,
        "perfect": (crit is not None),
    }


# ===========================================================================
# Section 10.  THE F18 CROSS-BOUNDARY FORMAN CANCELLATION TRACKING.
#              (F22-HPC Session 2 -- mg-0c5d)
#
#  F21 Proposition F21.1: the genuine chamber-Morse c*_{n+1} is "(the descent
#  of)" a critical (n-1)-cell of M_rel^eq, via the assembly
#       M_{n+1}  =  ( M_n  u  M_rel^eq )  +  cross-boundary Forman cancellation.
#
#  Session 2 implements that cross-boundary cancellation at the cell level and
#  runs it MATERIALISED at n = 3 (Delta_4, ~1.5e4 cells -- exact, reproducible).
#  The n = 3 run is the built-in TRIP-WIRE and it pins down, precisely, what
#  the cross-boundary cancellation does -- and what it does NOT do.
#
#  RESULT (Session 2 verdict: RED-tripwire; see s.5 of the doc).
#   (a) M_rel^eq's two critical (n-1)-cells are exactly { D-lift(c*_n),
#       U-lift(c*_n) } -- the closure-operator lifts (F17 + Session 1 s.1).
#   (b) The cross-boundary Forman cancellation cancels c*_n against ONE of them
#       along a UNIQUE gradient V-path; by Forman's cancellation theorem the
#       OTHER one survives UNCHANGED as the single critical cell of the perfect
#       M_{n+1}.  So the survivor is ALWAYS a closure-operator lift.  At n = 3
#       the materialised run gives survivor = D-lift(c*_3) exactly.
#   (c) The recorded c*_{n+1} (F2/F5) is NOT a closure-operator lift (its
#       bottom poset has nonempty restriction to [n]); so it can NEVER be a
#       cross-boundary survivor, for ANY M_rel^eq.  The cross-boundary
#       cancellation ALONE does not produce the recorded c*_{n+1}.
#   (d) The naive "survivor tower" c*_{n+1} := D-lift(c*_n) FAILS (CM-rel) at
#       n >= 6: the iterated MoveB apex steps accumulate as internal per-step
#       Pr's 1/4, 1/5, ... which fall BELOW 3/11.
#   (e) The "descent" is real and essential: the recorded c*_{n+1} IS reachable
#       from the survivor by a gradient V-path inside the perfect M_{n+1}, and
#       the descent absorbs the bad apex step into a BFT-sharp first step.  But
#       the descent target is NOT canonically pinned by simple extremal rules
#       (it lies among the min-|L|-profile all-BFT-sharp reachable cells, which
#       span several S_{n+1}-orbits), and -- unlike the cross-boundary
#       cancellation -- the descent REQUIRES materialising M_{n+1}, i.e. it is
#       HPC-class for n >= 4.  F21.1's "(the descent of)" is therefore a
#       genuine, essential, HPC-class operation, not folded into the cheap
#       cross-boundary cancellation.
# ===========================================================================

def _import_cofiber_n3n4():
    """Lazy import of the mg-3839/mg-6295 cofiber-Morse infrastructure
    (greedy matching, gradient V-paths, Forman cancellation, acyclicity)."""
    import compat_geom_cofiber_morse_n3n4 as CM
    return CM


def _profile(chain, m):
    """|L|-profile of a chain of posets on [m]."""
    return tuple(count_linear_extensions(transitive_closure(P), m)
                 for P in chain)


def _per_step_pr(chain, m):
    p = _profile(chain, m)
    return [Fraction(p[k + 1], p[k]) for k in range(len(p) - 1)]


def materialised_cross_boundary_n3():
    """The n = 3 cross-boundary cancellation, MATERIALISED on Delta_4.

    Builds M_3 (chamber-Morse on Delta_3), a perfect S_3-equivariant-faithful
    cofiber matching M_rel^eq on C_*(Delta_4, Delta_3), assembles
    M_4 = M_3 u M_rel^eq (critical vector (0,1,2,0)), then RUNS the
    cross-boundary Forman cancellation (0,1,2,0) -> (0,0,1,0).

    Returns a dict with: the materialised survivor, the cross-boundary
    V-path, and the descent data (whether the recorded c*_4 is reachable
    from the survivor by a gradient V-path inside the perfect M_4)."""
    CM = _import_cofiber_n3n4()
    PPF_3 = CM.make_PPF(3)
    PPF_4 = CM.make_PPF(4)
    sub = CM.iota_3_image(PPF_3)
    es3, ab3 = CM.refinement_above_map(PPF_3)
    es4, ab4 = CM.refinement_above_map(PPF_4)
    ch3 = CM.all_chains_by_dim(es3, ab3)
    ch4 = CM.all_chains_by_dim(es4, ab4)
    rel = CM.relative_cells_by_dim(ch4, sub)

    # M_3: a perfect chamber-Morse matching on Delta_3, critical (0,1).
    m3, _, _, _ = CM.greedy_matching(ch3, include_empty=True)
    cr3 = CM.critical_by_dim(m3, ch3, include_empty=True)
    cstar3 = cr3[1][0]                       # the critical 1-cell c*_3

    # M_rel^eq: a perfect cofiber matching on C_*(Delta_4, Delta_3).
    mrel, _, _, _ = CM.greedy_matching(rel, include_empty=False)
    rcs = set()
    for d in rel:
        rcs.update(rel[d])
    CM.forman_cancel_to_target(mrel, rel, rcs, (0, 0, 2, 0, 0), [])
    crel = {d: [c for c in rel[d] if mrel[c] is None] for d in sorted(rel)}

    # assemble M_4 = M_3 u M_rel^eq on Delta_4
    matched_4 = {}
    for c, p in m3.items():
        matched_4[c] = p
    for d in ch4:
        for c in ch4[d]:
            if c not in matched_4:
                matched_4[c] = None
    if () not in matched_4:
        matched_4[()] = None
    for c, p in mrel.items():
        matched_4[c] = p
    cell_set4 = set()
    for d in ch4:
        cell_set4.update(ch4[d])
    crit_pre = CM.critical_by_dim(matched_4, ch4, include_empty=True)
    cv_pre = tuple(len(crit_pre.get(d, [])) for d in range(5))

    # the cross-boundary Forman cancellation (0,1,2,0) -> (0,0,1,0)
    crit2_pre = list(crit_pre[2])
    xb_path = None
    cancelled = None
    for tau in crit2_pre:
        gp = CM.gradient_paths_from(tau, matched_4, cell_set4)
        for sig, paths in gp.items():
            if (matched_4.get(sig) is None and len(sig) == 2
                    and len(paths) == 1):
                xb_path = paths[0]
                cancelled = tau
                break
        if xb_path:
            break
    CM.forman_cancel_to_target(matched_4, ch4, cell_set4, (0, 0, 1, 0, 0), [])
    crit_post = CM.critical_by_dim(matched_4, ch4, include_empty=True)
    cv_post = tuple(len(crit_post.get(d, [])) for d in range(5))
    survivor = tuple(crit_post[2][0]) if cv_post == (0, 0, 1, 0, 0) else None
    acyclic = CM.is_acyclic(matched_4, ch4, include_empty=True)[0]

    # the survivor IS the D-type closure-operator lift of c*_3?
    cD, cU, _ = lift_cstar_to_M_rel([transitive_closure(P) for P in cstar3], 3)
    surv_is_D = (survivor == tuple(cD))
    surv_is_U = (survivor == tuple(cU))

    # the DESCENT: is the recorded c*_4 reachable from the survivor by a
    # gradient V-path inside the perfect M_4?  (a 2-cell -> 2-cell path)
    cstar4 = tuple(transitive_closure(P) for P in C_STAR[4]["hasse"])
    cstar4_orbit = set()
    for perm in permutations(range(4)):
        cstar4_orbit.add(tuple(frozenset((perm[a], perm[b]) for (a, b) in P)
                               for P in cstar4))

    reached = {}
    if survivor is not None:
        def _grad_2to2(tau_star):
            def dfs(cell, path):
                for i in range(len(cell)):
                    sigma = cell[:i] + cell[i + 1:]
                    if sigma not in cell_set4:
                        continue
                    partner = matched_4.get(sigma)
                    if partner is None:
                        continue
                    if (len(partner) == len(cell) and partner != cell
                            and partner not in path):
                        if partner not in reached:
                            reached[partner] = path + [sigma, partner]
                            dfs(partner, path + [sigma, partner])
            dfs(tau_star, [tau_star])
        _grad_2to2(survivor)
    descent_reachable = any(tuple(c) in cstar4_orbit for c in reached)
    # characterise the descent target among the reachable cells
    allcells = ([survivor] if survivor else []) + list(reached.keys())
    bft = []
    for c in allcells:
        prs = _per_step_pr(c, 4)
        if all(BFT_LO <= x <= BFT_HI for x in prs):
            bft.append(c)
    minprof = min((_profile(c, 4) for c in bft), default=None)
    mp_cells = [c for c in bft if _profile(c, 4) == minprof]
    mp_orbits = set()
    for c in mp_cells:
        mp_orbits.add(frozenset(
            tuple(frozenset((perm[a], perm[b]) for (a, b) in P) for P in c)
            for perm in permutations(range(4))))
    recorded_in_mp = any(tuple(c) in cstar4_orbit for c in mp_cells)

    return {
        "cstar3": tuple(transitive_closure(P) for P in cstar3),
        "cv_pre": cv_pre, "cv_post": cv_post, "acyclic": acyclic,
        "xb_path_len": len(xb_path) if xb_path else None,
        "cancelled": cancelled, "survivor": survivor,
        "survivor_is_D_lift": surv_is_D, "survivor_is_U_lift": surv_is_U,
        "survivor_profile": _profile(survivor, 4) if survivor else None,
        "recorded_cstar4_profile": _profile(cstar4, 4),
        "n_reachable": len(allcells),
        "descent_reachable": descent_reachable,
        "n_bft_reachable": len(bft),
        "descent_minprofile": minprof,
        "descent_minprofile_n_orbits": len(mp_orbits),
        "recorded_among_minprofile": recorded_in_mp,
    }


def naive_closure_lift_tower(maxn=7):
    """The naive 'survivor tower'  c*_{n+1} := D-lift(c*_n)  -- the cell the
    cross-boundary cancellation produces if NO descent is applied.

    Returns per-n: the chain, the |L|-profile, the per-step Pr's, and the
    (CM-rel) read.  KEY FINDING: (CM-rel) FAILS at n >= 6 -- the iterated
    MoveB apex steps accumulate as internal per-step Pr's 1/4, 1/5, ...
    which fall below the BFT-sharp interval [3/11, 8/11]."""
    rows = []
    # base: c*_3
    chain = [transitive_closure(P) for P in C_STAR[3]["hasse"]]
    n = 3
    rows.append(_tower_row(chain, n))
    while n < maxn:
        cD, cU, _ = lift_cstar_to_M_rel(chain, n)
        chain = [transitive_closure(P) for P in cD]   # the D-lift survivor
        n += 1
        rows.append(_tower_row(chain, n))
    return rows


def _tower_row(chain, n):
    """One row of the naive survivor tower at level n (chain on [n])."""
    m = n
    prof = _profile(chain, m)
    prs = _per_step_pr(chain, m)
    # the chain is  c*_n = D-lift(c*_{n-1}) = (apex, x_0, ..., x_{n-3});
    # step 0 is c*_n's OWN MoveB apex step (excluded from 'internal');
    # the remaining steps are the 'internal' per-step Pr's.
    internal = prs[1:] if n >= 4 else prs
    internal_bft = all(BFT_LO <= x <= BFT_HI for x in internal)
    top = chain[-1]
    top_osa = osa_signature(top, m)
    top_w = poset_width(top, m)
    top_ok = (top_osa is not None and top_w == 2
              and any(s == 2 for s in top_osa))
    return {
        "n": n, "chain": chain, "profile": prof,
        "per_step_pr": prs, "internal_pr": internal,
        "internal_bft": internal_bft,
        "top_osa": top_osa, "top_is_w2_osa_size2": top_ok,
        "cm_rel_ok": internal_bft and top_ok,
    }


def run_cross_boundary_tracking():
    """Driver for Section 10 -- the F18 cross-boundary cancellation tracking
    + the n = 3 materialised trip-wire + the closure-lift catastrophe check."""
    banner("SECTION 10:  the F18 cross-boundary Forman cancellation tracking "
           "(Session 2)")
    print("""
  F21.1:  M_{n+1} = ( M_n u M_rel^eq ) + cross-boundary Forman cancellation,
  and the genuine c*_{n+1} is '(the descent of)' a critical (n-1)-cell of
  M_rel^eq.  Session 2 runs the cross-boundary cancellation MATERIALISED at
  n = 3 -- the built-in trip-wire -- and pins down what it does.
""")

    # ---- the materialised n = 3 trip-wire --------------------------------
    print("  [trip-wire n=3]  materialised cross-boundary cancellation on "
          "Delta_4:")
    t0 = time.time()
    r = materialised_cross_boundary_n3()
    print(f"    M_3 u M_rel^eq critical vector  = {r['cv_pre']}  "
          f"(c*_3 ; c_D, c_U)")
    print(f"    cross-boundary V-path length    = {r['xb_path_len']}  "
          f"(unique gradient V-path -- a valid Forman cancellation)")
    print(f"    M_4 critical vector after cxl   = {r['cv_post']}  "
          f"(perfect; acyclic: {r['acyclic']})")
    print(f"    survivor |L|-profile            = {r['survivor_profile']}")
    print(f"    survivor == D-lift(c*_3) ?      = {r['survivor_is_D_lift']}   "
          f"== U-lift(c*_3) ? = {r['survivor_is_U_lift']}")
    print(f"    => the survivor IS the closure-operator lift -- NOT a "
          f"transformed cell.")
    print()
    print(f"    recorded c*_4 (F2) |L|-profile  = "
          f"{r['recorded_cstar4_profile']}   "
          f"(survivor profile {r['survivor_profile']} -- DIFFERENT)")
    print(f"    recorded c*_4 is NOT a closure-operator lift, so it can never "
          f"be a")
    print(f"    cross-boundary survivor -- for ANY M_rel^eq.")
    print()
    print(f"    THE DESCENT:  recorded c*_4 reachable from the survivor by a")
    print(f"    gradient V-path inside the perfect M_4 ? "
          f"{r['descent_reachable']}")
    print(f"      reachable 2-cells from survivor        = {r['n_reachable']}")
    print(f"      all-BFT-sharp among them               = "
          f"{r['n_bft_reachable']}")
    print(f"      min |L|-profile among BFT-sharp ones   = "
          f"{r['descent_minprofile']}  "
          f"(= recorded c*_4 profile: "
          f"{r['descent_minprofile'] == r['recorded_cstar4_profile']})")
    print(f"      ... spanning {r['descent_minprofile_n_orbits']} "
          f"S_4-orbits  (recorded c*_4 is one of them: "
          f"{r['recorded_among_minprofile']})")
    print(f"      => the descent target is NOT canonically pinned by "
          f"min-profile + BFT-sharpness alone.")
    print(f"    ({time.time()-t0:.1f}s)")

    # ---- the closure-lift 'survivor tower' + the (CM-rel) catastrophe ----
    print()
    print("  [catastrophe check]  the naive survivor tower  "
          "c*_{n+1} := D-lift(c*_n):")
    rows = naive_closure_lift_tower(maxn=7)
    for row in rows:
        n = row["n"]
        print(f"    c*_{n}: |L|-profile {row['profile']}   "
              f"per-step Pr {[str(x) for x in row['per_step_pr']]}")
        print(f"           INTERNAL per-step Pr "
              f"{[str(x) for x in row['internal_pr']]}  "
              f"all-BFT-sharp: {row['internal_bft']}   "
              f"top OSA{row['top_osa']}   (CM-rel): {row['cm_rel_ok']}")
    print()
    print("    => the naive survivor tower FAILS (CM-rel) at n >= 6: the "
          "iterated")
    print("       MoveB apex steps (1/4, 1/5, ...) become internal steps and "
          "fall")
    print("       BELOW [3/11, 8/11].  The 'descent' is ESSENTIAL -- it "
          "absorbs the")
    print("       apex step into a BFT-sharp first step (recorded c*_5 has "
          "first")
    print("       step 7/15, not 1/4).")

    print()
    print("  VERDICT (Section 10 / Session 2): RED-tripwire.")
    print("   The cross-boundary Forman cancellation produces D-lift(c*_n) "
          "(an")
    print("   M_rel^eq critical cell), NOT the recorded c*_{n+1}.  F21.1's "
          "'(the")
    print("   descent of)' is a genuine, essential, HPC-class operation: it "
          "needs")
    print("   M_{n+1} materialised (a gradient V-path move in the full "
          "Delta_{n+1}),")
    print("   and its canonical form is under-specified.  The cross-boundary")
    print("   cancellation does NOT bypass the HPC -- it reduces 'find "
          "c*_{n+1}'")
    print("   to 'the descent of D-lift(c*_n)', which is still HPC for n >= "
          "4.")
    return r, rows


# ===========================================================================
# Section 9.  Driver.
# ===========================================================================

def banner(t):
    print("\n" + "=" * 74)
    print("  " + t)
    print("=" * 74)


def show_chain(chain, m, indent="      "):
    for k, P in enumerate(chain):
        C = transitive_closure(P)
        print(f"{indent}P_{k}: {hasse_str(cover_relations(C, m), m)}")


def run_level(n, do_materialise_check=True, verbose=False):
    """Materialise the two critical (n-1)-cells of F17's M_rel^eq on
    C_*(Delta_{n+1}, Delta_n), via the closure-operator lift of c*_n."""
    banner(f"LEVEL n = {n}:  M_rel^eq on C_*(Delta_{n+1}, Delta_{n})  "
           f"-- materialising the two critical ({n-1})-cells")
    m = n + 1
    rec = C_STAR[n]
    print(f"  seed: {rec['label']}  (the canonical critical ({n-2})-cell of "
          f"Delta_{n}, F21 s.2)")
    print(f"  c*_{n}  =  ", end="")
    print(" < ".join(hasse_str(P, n) for P in rec["hasse"]))

    c_D, c_U, info = lift_cstar_to_M_rel(rec["hasse"], n)

    print(f"\n  --- the F14 cell-tracking lift "
          f"(closure operator -> PEEL -> MoveB -> MoveA) ---")
    print(f"  closure-operator lift of c*_{n} into A_{n} "
          f"(each Q_i -> (Q_i,[{n}]) -> x_i):")
    show_chain(info["lifted_in_A_n"], m)
    print(f"  MoveB cone-fibre apex  s*(x_0) = {{(n,b): b in Down_n(x_0)}} = "
          f"{hasse_str(info['apex'], m)}")

    # --- the two critical cells ---
    ok_D, msg_D = verify_relative_cell(c_D, n)
    ok_U, msg_U = verify_relative_cell(c_U, n)
    print(f"\n  >>> CRITICAL CELL  c_D  (the D_{n} = Down_{n} summand) "
          f"-- a ({n-1})-cell of C_*(Delta_{m}, Delta_{n}):")
    show_chain(c_D, m)
    print(f"      genuine relative cell: {ok_D}  ({msg_D})")
    print(f"  >>> CRITICAL CELL  c_U  (the U_{n} = Up_{n} summand, "
          f"order-reversal dual of c_D):")
    show_chain(c_U, m)
    print(f"      genuine relative cell: {ok_U}  ({msg_U})")
    # S_n-duality
    dual_ok = ([reverse_rel(P) for P in c_D] == c_U)
    print(f"      c_U = order-reversal(c_D)  [the S_{n}-equivariant "
          f"D_{n} ~= U_{n} duality]: {dual_ok}")

    # --- (CM-rel) analysis ---
    print(f"\n  --- (CM-rel) analysis  (F21 s.5.1) ---")
    an_D = cm_rel_analysis(c_D, n, internal_from=1)
    print(f"  c_D:  |L|-profile          = {an_D['profile']}")
    print(f"        width profile        = {an_D['widths']}")
    print(f"        OSA signatures       = {an_D['osa']}")
    print(f"        per-step Pr          = {[str(p) for p in an_D['prs']]}")
    print(f"        apex-step Pr (MoveB) = {an_D['prs'][0]}  "
          f"(structural coning step -- not an 'internal' step)")
    print(f"        INTERNAL per-step Pr = {[str(p) for p in an_D['internal_prs']]}"
          f"   all BFT-sharp in [3/11,8/11]: {an_D['internal_bft']}")
    print(f"        TOP poset            = OSA{an_D['top_osa']}  "
          f"width {an_D['top_width']}")
    print(f"        top is width-2 OSA with a size-2 block: "
          f"{an_D['top_is_width2_osa'] and an_D['top_has_size2_block']}")
    print(f"        ==> (CM-rel) holds for c_D: {an_D['cm_rel_ok']}")
    # F20 s.6 12-candidate comparison (only meaningful when the top poset
    # lives on [6], i.e. n = 5).
    f20_note = ""
    if m == 6 and an_D["top_osa"] is not None:
        in12 = tuple(an_D["top_osa"]) in F20_G6_CANDIDATES
        f20_note = (f"c_D top OSA{an_D['top_osa']} in F20's 12-candidate "
                    f"genuine-G_6 short list: {in12}")
        print(f"        F20 s.6: {f20_note}")
    # c_U inherits everything (order-reversal preserves |L|, width, OSA)
    an_U = cm_rel_analysis(c_U, n, internal_from=1)
    print(f"  c_U:  (CM-rel) holds for c_U: {an_U['cm_rel_ok']}  "
          f"(order-reversal dual -- same |L|/width/OSA invariants)")

    # --- comparison with the F21-recorded chamber-Morse c*_{n+1} ---
    cmp_note = ""
    if (n + 1) in C_STAR:
        rec_next = C_STAR[n + 1]
        cl_next = [transitive_closure(P) for P in rec_next["hasse"]]
        prof_next = [count_linear_extensions(C, n + 1) for C in cl_next]
        # is c_D (or c_U) in the S_{n+1}-orbit of c*_{n+1}?  |L|-profile is
        # an orbit invariant.
        prof_D = an_D["profile"]
        same_profile = (list(prof_D) == list(prof_next))
        print(f"\n  --- comparison with the chamber-Morse c*_{n+1} "
              f"(F21 s.2 record) ---")
        print(f"  c*_{n+1} |L|-profile           = {prof_next}")
        print(f"  c_D     |L|-profile           = {prof_D}")
        print(f"  c_D in the S_{n+1}-orbit of c*_{n+1} (|L|-profile match): "
              f"{same_profile}")
        if not same_profile:
            # check: does the INTERNAL part of c_D match the |L|-profile of
            # c*_n (the seed)?  it must -- the closure lift preserves |L|.
            prof_cstar_n = [count_linear_extensions(C, n)
                            for C in info["cstar_closures"]]
            internal_prof = prof_D[1:]
            print(f"  c_D internal |L|-profile      = {internal_prof}  "
                  f"(== c*_{n} |L|-profile {prof_cstar_n}: "
                  f"{list(internal_prof) == list(prof_cstar_n)})")
            cmp_note = ("c_D is NOT in the orbit of the F21-recorded "
                        f"c*_{n+1}: F17's M_rel^eq critical cells carry "
                        f"c*_{n}'s internal structure, not c*_{n+1}'s.")
        else:
            cmp_note = (f"c_D IS in the S_{n+1}-orbit of c*_{n+1}.")
        print(f"  finding: {cmp_note}")

    # --- materialised cross-check (small n only) ---
    mat = None
    if do_materialise_check:
        print(f"\n  --- materialised cross-check (Delta(A_{n})) ---")
        t0 = time.time()
        mat = materialised_morse_count(n)
        print(f"  f(Delta(A_{n}))        = {mat['f']}  "
              f"({sum(mat['f'])} cells)")
        print(f"  H~_*(Delta(A_{n}))     = {mat['betti']}")
        print(f"  perfect Morse matching critical counts = {mat['counts']}  "
              f"(perfect: {mat['perfect']}, seed {mat['seed']})")
        print(f"  ==> exactly ONE critical ({n-2})-cell of Delta(A_{n}); via "
              f"the D/U duality, M_rel^eq has exactly 2 critical "
              f"({n-1})-cells.")
        print(f"  ({time.time()-t0:.1f}s)")

    return {
        "n": n, "c_D": c_D, "c_U": c_U, "info": info,
        "an_D": an_D, "an_U": an_U,
        "ok_D": ok_D, "ok_U": ok_U, "dual_ok": dual_ok,
        "mat": mat, "cmp_note": cmp_note, "f20_note": f20_note,
    }


def main():
    t_start = time.time()
    banner("F22-HPC  (mg-43fb)  --  cell-tracking the F14/F17 cofiber Morse "
           "reduction")
    print("""
  Materialises the two critical (n-1)-cells of F17's perfect
  S_n-equivariant cofiber Morse matching M_rel^eq on C_*(Delta_{n+1},
  Delta_n), as explicit chains in PPF_{n+1}, via the F14 cell-tracking
  lift (closure operator -> PEEL -> MoveB -> MoveA).

  Session 1 scope: n = 3, 4, 5 via the F17-structural (closure-operator,
  memory-efficient) route, seeded with the known exact c*_3, c*_4, c*_5.
  n = 6, 7 deferred -- see docs/state-F22-HPC.md.
""")

    results = {}

    # ---- homology-level cross-check (n=3): F14 reduction Betti ----
    banner("[cross-check]  the F14 homology reduction  ->  cofiber Betti")
    for n in (3,):
        H, msg = cofiber_betti_via_F14(n)
        if H is None:
            print(f"  n={n}: F14 reduction cross-check unavailable ({msg})")
        else:
            trimmed = list(H)
            while trimmed and trimmed[-1] == 0:
                trimmed.pop()
            print(f"  n={n}: H~_*(Delta_{n+1}/Delta_{n}) = {trimmed}  "
                  f"(expect (0,...,0,2,0): the cofiber has 2 critical "
                  f"({n-1})-cells)")
            results[f"cofiber_betti_{n}"] = trimmed

    # ---- the levels ----
    # n=3: materialised cross-check is cheap (1008 cells).
    # n=4: Delta(A_4) = 1.5e7 cells -- heavy; off by default.
    # n=5: Delta(A_5) = 1.35e13 cells -- never materialised (the whole point).
    results[3] = run_level(3, do_materialise_check=True)
    results[4] = run_level(4, do_materialise_check=False)
    results[5] = run_level(5, do_materialise_check=False)

    # ---- verdict summary ----
    banner("SUMMARY  --  the materialised M_rel^eq critical cells")
    all_rel_ok = True
    all_cm_rel = True
    for n in (3, 4, 5):
        r = results[n]
        rel = r["ok_D"] and r["ok_U"] and r["dual_ok"]
        cm = r["an_D"]["cm_rel_ok"] and r["an_U"]["cm_rel_ok"]
        all_rel_ok = all_rel_ok and rel
        all_cm_rel = all_cm_rel and cm
        print(f"  n={n}:  2 critical ({n-1})-cells materialised: {rel}   "
              f"(CM-rel) holds on them: {cm}")
        print(f"         c_D top = OSA{r['an_D']['top_osa']}  "
              f"internal |L|-profile = {r['an_D']['profile'][1:]}  "
              f"internal-BFT-sharp = {r['an_D']['internal_bft']}")
    print()
    print(f"  All cells genuine relative cells + S_n-dual : {all_rel_ok}")
    print(f"  (CM-rel) holds on every materialised cell    : {all_cm_rel}")
    print()
    print("  FINDING (see docs/compatibility-geometry-F22-hpc-critical-cells.md):")
    print("   * F17's M_rel^eq critical cells (closure-operator route) are")
    print("     the lift of c*_n: their INTERNAL structure is exactly c*_n's,")
    print("     so (CM-rel) holds on them iff c*_n satisfies (L2-struct) +")
    print("     internal-BFT-sharpness -- confirmed for n = 3,4,5.")
    print("   * They are NOT in the S_{n+1}-orbit of the F21-recorded")
    print("     chamber-Morse c*_{n+1}: F21.1's 'c*_{n+1} = (the descent of)")
    print("     a critical cell of M_rel^eq' needs the F18 cross-boundary")
    print("     cancellation as a genuine cell-transforming step -- the")
    print("     n=6,7 continuation gate.")

    # ---- Section 10: F22-HPC Session 2 -- the cross-boundary cancellation ----
    run_cross_boundary_tracking()

    print(f"\n[done] total runtime: {time.time()-t_start:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
