#!/usr/bin/env python3
r"""
compat_geom_partial_squared.py
==============================

Compat-Geom F16 companion script (mg-f893).

Route (ii) WEAKER form: the bounded central-stability presentation for the
degree-shift-aware cofiber-cohomology object  ((B_n)_n, {partial_n}).

This script is a *verification harness* for the structural argument in
docs/compatibility-geometry-F16-central-stability-presentation.md.  The F16
result is pure homological algebra -- it needs no computation to be
rigorous -- but the script provides an explicit, cochain-level,
independent cross-check of the single load-bearing identity:

       UNCONDITIONAL LEMMA (F16 sec.2):  partial_{n+1} o partial_n = 0 .

The proof is one line of homological algebra.  By F15's factorisation
Lemma 3.1 (unconditional),

       partial_n = delta_{n+1} o q_n ,

so   partial_{n+1} o partial_n
       = delta_{n+2} o q_{n+1} o delta_{n+1} o q_n
       = delta_{n+2} o ( q_{n+1} o delta_{n+1} ) o q_n .

And   q_{n+1} o delta_{n+1} = 0   because q_{n+1} and delta_{n+1} are
*consecutive* maps in the (exact) pair LES of (Delta_{n+2}, Delta_{n+1}):

   .. -> H~^{n-1}(Delta_{n+1}) --delta_{n+1}--> H~^n(Delta_{n+2}/Delta_{n+1})
                               --q_{n+1}-----> H~^n(Delta_{n+2}) -> ..

exactness at H~^n(Delta_{n+2}/Delta_{n+1}) gives im(delta_{n+1}) = ker(q_{n+1}).

So  partial_{n+1} o partial_n = 0  for ALL n, with no hypotheses -- it uses
only Lemma 3.1 and exactness of a pair long exact sequence.

What the script checks
----------------------
  [A]  enumerate PPF_3, PPF_4, iota_3, the relative cells of (Delta_4,Delta_3);
       verify cardinalities and f-vectors against mg-6295 / F15.
  [B]  mod-p ranks of d^1(Delta_4), d^1_rel, d^2(Delta_4): re-derive
       b~_2(Delta_4) = 1 = dim H~^2(Delta_4) and b~_2(Delta_4/Delta_3) = 2
       = dim B_3.  (Light trip-wire; F15 sec.[B] does the full Betti sweep.)
  [C]  THE COCHAIN-LEVEL CHECK.  Construct an explicit 1-cocycle phi
       representing a generator of H~^1(Delta_3); extend it by zero to a
       1-cochain psi on Delta_4; form d(psi) in C^2(Delta_4).  Then:
         - d(psi) is a relative 2-cocycle  =>  it represents delta_3[phi] in B_3 ;
         - [d(psi)] =/= 0 in B_3           =>  delta_3 =/= 0, i.e. delta_3 is
                                              INJECTIVE  ((UCC.2) at n=3) ;
         - [d(psi)] = 0 in H~^2(Delta_4)   =>  q_3([d(psi)]) = 0, i.e.
                                              q_3 o delta_3 = 0 .
       The point: the SAME cochain d(psi) is a non-trivial class in the
       cofiber B_3 but an honest coboundary (= d psi) in the absolute
       complex Delta_4.  That is exactly  q_3 o delta_3 = 0  -- the n=3
       instance of the engine of partial^2 = 0 -- exhibited with explicit
       representatives, not merely deduced from Betti numbers + exactness.
  [D]  the engine, one level up:  partial_4 o partial_3 = 0  reduces to
       q_4 o delta_4 = 0, which is the SAME homological-algebra fact
       (exactness of the pair LES of (Delta_5,Delta_4)).  No Delta_5
       enumeration is needed -- exactness is a theorem, not a computation.
  [E]  generation-degree bookkeeping.  Under concentration ((UCC.1)
       concentration half, M1's deliverable: H^k_n = 0 for k =/= n-1,
       dim B_n = 2) the C-module H collapses onto the diagonal complex
       (B_n, partial_n), and partial is the ONLY degree-raising structure
       map.  With partial^2 = 0 this forces the generators object
       H~_0(H)_n = B_n / im(partial_{n-1}) to have UNBOUNDED support:
       no bounded set of generators reaches B_n for large n.  Hence
       ((B_n)_n,{partial_n}) admits NO bounded central-stability
       presentation.  With (UCC.2) in addition, H~_0(H)_n is exactly
       1-dimensional for every n -- "exactly one genuinely new generator
       per level, forever".
  [F]  verdict.

Established external inputs (cited; NOT recomputed -- Delta_5 has
~3.3x10^8 relative cells, out of scope):
  - Hyp(5): H~^*(Delta_5) = sgn_{S_5} concentrated in degree 3 (F10,
    verified n<=6).  Used only to instantiate [D] at n=3 (delta_4
    injective); the partial^2 = 0 lemma itself needs NO Delta_5 fact.
  - B_4 = 2.sgn_{S_4} (F14, mg-3839).  Not needed by this script's checks.

Pure-Python stdlib only.  Runtime ~ 1-3 min (the mod-p rank of d^2(Delta_4),
5232 columns, dominates).

NO new axioms; NO Lean changes.

References
----------
  - mg-8355 (F15) docs/compatibility-geometry-F15-e2-partial-test.md --
    Lemma 3.1 (partial_n = delta_{n+1} o q_n, unconditional); sec.6.4 (the
    per-step structure); scripts/compat_geom_partial_3.py (the poset /
    chain / mod-p machinery transcribed and adapted below).
  - mg-ecf6 (F13) docs/compatibility-geometry-F13-shift-aware-
    functoriality.md -- the degree-shift-aware functor category C; Cor.7.7
    (under concentration, H collapses onto the diagonal); Prop.6.1
    (partial-composites left "unconstrained" -- F16 resolves this: they
    vanish).
  - mg-3839 (F14) -- B_4 = 2.sgn_{S_4}.
  - mg-59f3 (PCR-2) -- delta_3 injective ((UCC.2) at n=3); [C] re-derives it.
  - mg-8216 (F10) -- (UCC); Hyp(n) verified n<=6.
  - A. Putman, Stability in the homology of congruence subgroups (2015);
    P. Patzt, Central stability homology (2017+) -- the route-(ii)
    machinery; F16 shows its bounded-presentation hypothesis fails here.
"""

import sys
import time
from itertools import permutations


# =======================================================================
# 1. Poset enumeration
#    (transcribed from F15 / mg-6295 -- identical convention)
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
    antichain = frozenset()
    seen = {antichain}
    frontier = {antichain}
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
# 2. Order-complex chains
# =======================================================================

def refinement_above_map(elements):
    """Strict refinement P < Q (Q has strictly more relations)."""
    es = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    above = {P: [] for P in es}
    for P in es:
        for Q in es:
            if P != Q and P < Q:
                above[P].append(Q)
    return es, above


def all_chains_by_dim(elements, above):
    """by_dim[k] = list of (k+1)-element strict chains (tuples, ascending)."""
    by_dim = {0: [(P,) for P in elements]}
    cur = by_dim[0]
    dim = 0
    while cur:
        nxt = []
        for c in cur:
            for Q in above[c[-1]]:
                nxt.append(c + (Q,))
        if not nxt:
            break
        dim += 1
        by_dim[dim] = nxt
        cur = nxt
    return by_dim


def f_vector(chains_by_dim):
    return [len(chains_by_dim[d]) for d in sorted(chains_by_dim)]


def iota_image(PPF_small):
    """Image of iota : PPF_n <-> PPF_{n+1}: same frozensets of pairs, the
    new element adjoined as isolated -- the relation set is unchanged."""
    return set(frozenset(P) for P in PPF_small)


# =======================================================================
# 3. mod-p linear algebra: echelonization + span membership
# =======================================================================
#
# A vector is a dict {row_index: coeff}.  echelonize() returns a reduced
# echelon basis as {pivot_row: vector} with each pivot normalised to 1.
# in_span() reduces a query vector against that basis.

def echelonize(cols, p):
    pivots = {}
    for col in cols:
        v = {r: c % p for r, c in col.items() if c % p}
        while v:
            r = min(v)
            if r in pivots:
                pv = pivots[r]
                factor = v[r] % p          # pv normalised so pv[r] == 1
                for rr, cc in pv.items():
                    nv = (v.get(rr, 0) - factor * cc) % p
                    if nv:
                        v[rr] = nv
                    elif rr in v:
                        del v[rr]
            else:
                inv = pow(v[r], -1, p)
                pivots[r] = {rr: (cc * inv) % p for rr, cc in v.items()}
                break
    return pivots


def in_span(pivots, vec, p):
    v = {r: c % p for r, c in vec.items() if c % p}
    while v:
        r = min(v)
        if r not in pivots:
            return False
        pv = pivots[r]
        factor = v[r] % p
        for rr, cc in pv.items():
            nv = (v.get(rr, 0) - factor * cc) % p
            if nv:
                v[rr] = nv
            elif rr in v:
                del v[rr]
    return True


def rank_of(cols, p):
    return len(echelonize(cols, p))


PRIMES = (1_000_003, 999_983)


def rank_two_primes(cols, label):
    ranks = [rank_of(cols, p) for p in PRIMES]
    if len(set(ranks)) != 1:
        raise RuntimeError(f"rank disagreement for {label}: {ranks}")
    return ranks[0]


# =======================================================================
# 4. Coboundary operators (cochains as dicts {cell: coeff})
# =======================================================================
#
# d^0 : C^0 -> C^1 ,  (d^0 phi)((P,Q)) = phi((Q,)) - phi((P,))
# d^1 : C^1 -> C^2 ,  (d^1 psi)((P,Q,R)) = psi((Q,R)) - psi((P,R)) + psi((P,Q))
# d^2 : C^2 -> C^3 ,  alternating sum over the 3 codim-1 faces.

def d0_columns(verts_idx, edges_idx):
    """Columns of d^0 : C^0(Delta) -> C^1(Delta), indexed by vertices."""
    cols = []
    inv = {v: ((v,)) for v in verts_idx}  # not used; clarity only
    for v in verts_idx:
        col = {}
        for e, ei in edges_idx.items():
            (P, Q) = e
            s = 0
            if Q == (v,)[0]:
                s += 1
            if P == (v,)[0]:
                s -= 1
            if s:
                col[ei] = s
        cols.append(col)
    return cols


def d1_of_cochain(psi, two_cells, two_idx=None):
    """d^1 applied to a 1-cochain psi (dict {edge: coeff}); returns the
    2-cochain.  Keyed by 2-cell tuple if two_idx is None, else by the
    integer index two_idx[tau]."""
    out = {}
    for tau in two_cells:
        P, Q, R = tau
        val = psi.get((Q, R), 0) - psi.get((P, R), 0) + psi.get((P, Q), 0)
        if val:
            out[two_idx[tau] if two_idx is not None else tau] = val
    return out


def d1_columns(edges, two_cells_idx):
    """Columns of d^1 : C^1 -> C^2, indexed by edges.  Column for edge e =
    d^1(indicator of e) = { 2-cell tau : sign with which e is a face of tau }."""
    cols = []
    for e in edges:
        col = {}
        psi = {e: 1}
        for tau, ti in two_cells_idx.items():
            P, Q, R = tau
            val = psi.get((Q, R), 0) - psi.get((P, R), 0) + psi.get((P, Q), 0)
            if val:
                col[ti] = val
        cols.append(col)
    return cols


def d2_columns(two_cells, three_cells_idx):
    """Columns of d^2 : C^2 -> C^3, indexed by 2-cells."""
    cols = []
    for s in two_cells:
        col = {}
        for sigma, si in three_cells_idx.items():
            A, B, C, D = sigma
            faces = [((B, C, D), 1), ((A, C, D), -1),
                     ((A, B, D), 1), ((A, B, C), -1)]
            val = 0
            for face, sign in faces:
                if face == s:
                    val += sign
            if val:
                col[si] = val
        cols.append(col)
    return cols


def banner(title):
    print("\n" + "=" * 70)
    print("  " + title)
    print("=" * 70)


# =======================================================================
# 5. Main driver
# =======================================================================

def main():
    t_start = time.time()
    print(r"""
compat_geom_partial_squared.py  --  Compat-Geom F16  (mg-f893)
Verification harness for  partial_{n+1} o partial_n = 0  (unconditional)
and the consequent failure of route (ii)'s bounded central-stability
presentation.
""")

    # -- [A] enumerate -----------------------------------------------------
    banner("[A]  PPF_3, PPF_4, iota_3, relative cells of (Delta_4, Delta_3)")
    PPF_3 = make_PPF(3)
    PPF_4 = make_PPF(4)
    print(f"  |PPF_3| = {len(PPF_3)}   (expect 12)")
    print(f"  |PPF_4| = {len(PPF_4)}   (expect 194)")
    assert len(PPF_3) == 12 and len(PPF_4) == 194

    es3, above3 = refinement_above_map(PPF_3)
    es4, above4 = refinement_above_map(PPF_4)
    chains3 = all_chains_by_dim(es3, above3)
    chains4 = all_chains_by_dim(es4, above4)
    print(f"  f(Delta_3) = {f_vector(chains3)}   (expect [12, 12])")
    print(f"  f(Delta_4) = {f_vector(chains4)}   "
          f"(expect [194, 1872, 5232, 5664, 2112])")
    assert f_vector(chains3) == [12, 12]
    assert f_vector(chains4) == [194, 1872, 5232, 5664, 2112]

    sub_vertices = iota_image(PPF_3)          # iota_3(PPF_3) subset PPF_4
    # iota_3 is an order-ideal inclusion (a sub-relation of a 3-isolated
    # poset is 3-isolated): verify directly.
    ideal_ok = all(
        not (R != Q and R < Q and R not in sub_vertices)
        for Q in es4 if Q in sub_vertices for R in es4
    )
    print(f"  iota_3(PPF_3) is a downward-closed subposet (order ideal)? "
          f"{ideal_ok}")
    assert ideal_ok

    # cells of Delta_4, by dimension; relative cells = >=1 vertex off Delta_3
    verts4 = [c[0] for c in chains3[0]]        # the 12 vertices of Delta_3
    # (Delta_3's vertices, as elements -- needed for d^0(Delta_3))
    edges3 = chains3[1]
    edges4 = chains4[1]
    two4 = chains4[2]
    three4 = chains4[3]
    rel_edges = [c for c in edges4 if any(v not in sub_vertices for v in c)]
    rel_two = [c for c in two4 if any(v not in sub_vertices for v in c)]
    print(f"  |edges(Delta_3)|        = {len(edges3)}   (expect 12)")
    print(f"  |edges(Delta_4)|        = {len(edges4)}   (expect 1872)")
    print(f"  |2-cells(Delta_4)|      = {len(two4)}   (expect 5232)")
    print(f"  |rel 1-cells (D4,D3)|   = {len(rel_edges)}   (expect 1860)")
    print(f"  |rel 2-cells (D4,D3)|   = {len(rel_two)}   (expect 5232 "
          f"-- Delta_3 has no 2-cells, so every 2-cell is relative)")
    assert len(edges3) == 12 and len(rel_edges) == 1860
    assert len(rel_two) == 5232 == len(two4)

    # -- [B] light Betti trip-wire ----------------------------------------
    banner("[B]  mod-p ranks:  dim H~^2(Delta_4) = 1,  dim B_3 = 2")
    print("  Computing mod-p ranks (two primes) ...", flush=True)
    two_idx = {tau: i for i, tau in enumerate(two4)}
    three_idx = {sg: i for i, sg in enumerate(three4)}

    t0 = time.time()
    cols_d1 = d1_columns(edges4, two_idx)
    rk_d1 = rank_two_primes(cols_d1, "d^1(Delta_4)")
    print(f"     rank d^1(Delta_4)   = {rk_d1:>5d}   "
          f"(C^1 = {len(edges4)})   [{time.time()-t0:.1f}s]", flush=True)

    t0 = time.time()
    cols_d1_rel = d1_columns(rel_edges, two_idx)
    rk_d1_rel = rank_two_primes(cols_d1_rel, "d^1_rel")
    print(f"     rank d^1_rel        = {rk_d1_rel:>5d}   "
          f"(C^1_rel = {len(rel_edges)})   [{time.time()-t0:.1f}s]", flush=True)

    t0 = time.time()
    cols_d2 = d2_columns(two4, three_idx)
    rk_d2 = rank_two_primes(cols_d2, "d^2(Delta_4)")
    print(f"     rank d^2(Delta_4)   = {rk_d2:>5d}   "
          f"(C^2 = {len(two4)})   [{time.time()-t0:.1f}s]", flush=True)

    # d^2_rel = d^2(Delta_4): all 2-cells and 3-cells are relative.
    dimH2_D4 = len(two4) - rk_d2 - rk_d1
    dimB3 = len(two4) - rk_d2 - rk_d1_rel        # b~_2(Delta_4/Delta_3)
    print(f"\n     dim H~^2(Delta_4)      = 5232 - {rk_d2} - {rk_d1} "
          f"= {dimH2_D4}   (expect 1 = Hyp(4))")
    print(f"     dim B_3 = b~_2(D4/D3)  = 5232 - {rk_d2} - {rk_d1_rel} "
          f"= {dimB3}   (expect 2 = mg-6295)")
    assert dimH2_D4 == 1, f"dim H~^2(Delta_4) = {dimH2_D4}, expected 1"
    assert dimB3 == 2, f"dim B_3 = {dimB3}, expected 2"
    print(f"     (cross-check: dim B_3 - dim H~^2(Delta_4) = "
          f"rank d^1 - rank d^1_rel = {rk_d1 - rk_d1_rel} = 1)")
    assert dimB3 - dimH2_D4 == rk_d1 - rk_d1_rel == 1

    # echelon bases reused in [C]
    ech_d1_rel = echelonize(cols_d1_rel, PRIMES[0])   # im(d^1_rel) in C^2
    ech_d1_abs = echelonize(cols_d1, PRIMES[0])       # im(d^1(D4)) in C^2

    # -- [C] cochain-level check:  q_3 o delta_3 = 0  (with explicit reps) --
    banner("[C]  cochain-level check:  delta_3 =/= 0  and  q_3 o delta_3 = 0")
    p = PRIMES[0]
    print(f"""  Work mod p = {p}.  Recall:
    delta_3 : H~^1(Delta_3) -> B_3 = H~^2(Delta_4/Delta_3)   (pair conn. map)
    q_3     : B_3 -> H~^2(Delta_4)                            (pair-LES map)
  Recipe (F13 sec.2 / F15 sec.3):  for a 1-cocycle phi on Delta_3, pick the
  preimage psi = "extend phi by zero off Delta_3" in C^1(Delta_4); then
  d(psi) in C^2(Delta_4) vanishes on Delta_3, so it is a relative 2-cocycle
  representing delta_3[phi] in B_3.  And q_3[delta_3[phi]] = [d(psi)] viewed
  in H~^2(Delta_4) -- but d(psi) is literally a coboundary there.
""")
    # 1. a generator phi of H~^1(Delta_3) = C^1(Delta_3) / im(d^0(Delta_3)).
    edges3_idx = {e: i for i, e in enumerate(edges3)}
    cols_d0_D3 = d0_columns(verts4, edges3_idx)
    ech_d0_D3 = echelonize(cols_d0_D3, p)
    rk_d0_D3 = len(ech_d0_D3)
    print(f"  rank d^0(Delta_3) = {rk_d0_D3}  (expect 11; "
          f"dim H~^1(Delta_3) = 12 - 11 = 1)")
    assert rk_d0_D3 == 11
    phi = None
    for e in edges3:
        cand = {edges3_idx[e]: 1}
        if not in_span(ech_d0_D3, cand, p):
            phi_edge = e
            phi = {e: 1}                 # indicator of a single Delta_3-edge
            break
    assert phi is not None, "no edge-indicator outside im(d^0(Delta_3))"
    P0, Q0 = phi_edge
    print(f"  phi := indicator of the Delta_3-edge  P < Q  with")
    print(f"         P = {sorted(tuple(x) for x in P0)}  (a poset on "
          f"{{0,1,2}}, {len(P0)} relations)")
    print(f"         Q = {sorted(tuple(x) for x in Q0)}  ({len(Q0)} relations)")
    print(f"         -- a 1-cochain on Delta_3, NOT a coboundary => "
          f"a non-zero class in H~^1(Delta_3).")

    # 2. psi := extend phi by zero off Delta_3  (phi is supported on one
    #    Delta_3-edge, which is also a Delta_4-edge -- psi = phi as a dict).
    psi = dict(phi)
    # sanity: psi is supported on Delta_3-edges only
    assert all(all(v in sub_vertices for v in e) for e in psi), \
        "psi not supported on Delta_3"

    # 3. d(psi) in C^2(Delta_4) -- two views: keyed by 2-cell tuple
    #    (for the d^2 check) and by integer index (for the in_span checks).
    dpsi_tup = d1_of_cochain(psi, two4)
    dpsi = d1_of_cochain(psi, two4, two_idx)
    print(f"  d(psi) has {len(dpsi)} non-zero entries in C^2(Delta_4).")

    # 3a. d(psi) vanishes on Delta_3 -- trivial: Delta_3 has NO 2-cells.
    #     (so d(psi) lies in C^2(Delta_4,Delta_3) = C^2(Delta_4) automatically.)
    print(f"  d(psi) is a relative 2-cochain: Delta_3 has no 2-cells, so "
          f"C^2(Delta_4,Delta_3) = C^2(Delta_4).  [OK]")

    # 3b. d(psi) is a relative 2-COCYCLE: d^2(d(psi)) = 0 automatically
    #     (d^2 d^1 = 0).  Confirm numerically.
    dpsi_d2 = {}
    for sigma in three4:
        A, B, C, D = sigma
        val = (dpsi_tup.get((B, C, D), 0) - dpsi_tup.get((A, C, D), 0)
               + dpsi_tup.get((A, B, D), 0) - dpsi_tup.get((A, B, C), 0)) % p
        if val:
            dpsi_d2[sigma] = val
    print(f"  d^2(d(psi)) = 0 ?  {not dpsi_d2}   "
          f"(=> d(psi) is a relative 2-cocycle, representing delta_3[phi])")
    assert not dpsi_d2

    # 4. [d(psi)] =/= 0 in B_3  <=>  d(psi) not in im(d^1_rel)  =>  delta_3 inj.
    dpsi_in_B3_trivial = in_span(ech_d1_rel, dpsi, p)
    print(f"\n  d(psi) in im(d^1_rel) ?  {dpsi_in_B3_trivial}   "
          f"(False => [d(psi)] =/= 0 in B_3)")
    assert not dpsi_in_B3_trivial, \
        "delta_3[phi] is zero in B_3 -- would contradict (UCC.2) at n=3"
    print(f"  ==>  delta_3[phi] =/= 0 in B_3.  Since dim H~^1(Delta_3) = 1,")
    print(f"       delta_3 is INJECTIVE.  This is (UCC.2) at n=3 "
          f"(re-derives mg-59f3),")
    print(f"       exhibited with an explicit cocycle representative.")

    # 5. q_3[delta_3[phi]] = [d(psi)] in H~^2(Delta_4).  But d(psi) = d^1(psi)
    #    is a coboundary in the ABSOLUTE complex.  Confirm numerically.
    dpsi_in_imd1_abs = in_span(ech_d1_abs, dpsi, p)
    print(f"\n  d(psi) in im(d^1(Delta_4)) ?  {dpsi_in_imd1_abs}   "
          f"(True => [d(psi)] = 0 in H~^2(Delta_4))")
    assert dpsi_in_imd1_abs, "d(psi) should be an absolute coboundary"
    print(f"  ==>  q_3[delta_3[phi]] = [d(psi)] = 0 in H~^2(Delta_4).")
    print(f"""
  CONCLUSION OF [C].  The SAME cochain d(psi):
     * represents a NON-ZERO class delta_3[phi] in the cofiber B_3 ;
     * is an honest coboundary  d^1(psi)  in the absolute complex Delta_4,
       hence ZERO in H~^2(Delta_4).
  That is precisely   q_3 o delta_3 = 0   -- verified at the cochain level
  with explicit representatives.  This is the n=3 instance of the engine of
  the F16 lemma  partial^2 = 0.""")

    # -- [D] the engine one level up --------------------------------------
    banner("[D]  partial_4 o partial_3 = 0  reduces to  q_4 o delta_4 = 0")
    print(r"""  By F15 Lemma 3.1 (unconditional):  partial_n = delta_{n+1} o q_n.
  Hence
      partial_4 o partial_3 = delta_5 o ( q_4 o delta_4 ) o q_3 .
  And  q_4 o delta_4 = 0  because q_4 and delta_4 are CONSECUTIVE maps in
  the (exact) pair LES of (Delta_5, Delta_4):

    .. -> H~^2(Delta_4) --delta_4--> H~^3(Delta_5/Delta_4) = B_4
                        --q_4------> H~^3(Delta_5) -> ..

  exactness at B_4 gives  im(delta_4) = ker(q_4),  i.e.  q_4 o delta_4 = 0.
  This is the SAME homological-algebra fact verified at the cochain level
  in [C] one level down (q_3 o delta_3 = 0): the connecting map of a pair
  produces a class that becomes a coboundary in the larger complex, which
  the pair-LES map q then sends to 0.  It is a THEOREM (exactness of a long
  exact sequence) -- no Delta_5 enumeration is required.

  Therefore, for ALL n, with NO hypotheses:

      ####################################################
      #                                                  #
      #     partial_{n+1} o partial_n = 0   (for all n)   #
      #                                                  #
      ####################################################

  The diagonal tower  B_3 --partial_3--> B_4 --partial_4--> B_5 --> ...
  is a COCHAIN COMPLEX.  (F13 Prop.6.1 had left partial-composites
  "unconstrained"; F16 resolves this -- they vanish.)
""")

    # -- [E] generation-degree bookkeeping --------------------------------
    banner("[E]  generation degree is UNBOUNDED -- no bounded presentation")
    print(r"""  Assume concentration -- (UCC.1)'s concentration half, M1's
  deliverable: H^k_n = 0 for k =/= n-1, and dim B_n = 2 for all n (M1's
  "M_rel perfect", critical vector (0,...,0,2,0)).  [This is the half F16
  is instructed to combine with; the OPEN half is the representation TYPE,
  which is irrelevant to the obstruction below.]

  By F13 Cor.7.7(1), under concentration the C-module H collapses onto its
  diagonal: the only non-zero spaces are the B_n, and the only structure
  maps are the partial_n (degree-raising) and the S_n-actions (degree-
  preserving).  So partial is the ONLY degree-raising structure map.

  The "generators" object (indecomposables) of a C-module is
      H~_0(H)_n  =  B_n / ( sum of images of structure maps from degree < n ).
  Under concentration the only such map into B_n is partial_{n-1}, so
      H~_0(H)_n  =  B_n / im(partial_{n-1}).
  A bounded central-stability presentation (Putman/Patzt) requires H~_0(H)
  to be supported in BOUNDED degree -- this is presentation-independent.

  Dimension bookkeeping, using ONLY:  partial^2 = 0  [D]  and  dim B_n = 2:
""")
    # symbolic / arithmetic demonstration of the dichotomy
    print("  Claim.  For every n:  H~_0(H)_n =/= 0   OR   H~_0(H)_{n+1} = B_{n+1}.")
    print("  Proof.  If H~_0(H)_n = 0 then B_n = im(partial_{n-1}), so")
    print("    im(partial_n) = partial_n(B_n) = partial_n(im partial_{n-1})")
    print("                  = (partial_n o partial_{n-1})(B_{n-1}) = 0,")
    print("    using partial^2 = 0.  Then H~_0(H)_{n+1} = B_{n+1}/im(partial_n)")
    print("    = B_{n+1}/0 = B_{n+1} =/= 0  (dim B_{n+1} = 2).            [].")
    print()
    print("  Hence H~_0(H) is non-zero for infinitely many n -- its support")
    print("  is UNBOUNDED.  Equivalently:  H admits a bounded central-")
    print("  stability presentation  <=>  B_n = 0 for all large n  --  which")
    print("  is FALSE (dim B_n = 2, M1).  So:")
    print()
    print("    ((B_n)_n, {partial_n})  admits NO bounded central-stability")
    print("    presentation.  Generation degree is unbounded.")
    print()
    print(r"""  SHARP form, assuming (UCC.2) in addition (delta_n injective):
  then im(partial_{n-1}) = im(delta_n o q_{n-1}) = im(delta_n) (q_{n-1}
  surjective under Hyp), which is 1-dimensional (delta_n injective on the
  1-dim sgn_{S_n}).  So
       dim H~_0(H)_n = dim B_n - dim im(partial_{n-1}) = 2 - 1 = 1
  for EVERY n: exactly one genuinely new generator per level, forever.
  Moreover (pair LES of (Delta_{n+1},Delta_n), q_n surjective under Hyp):
       H~_0(H)_n = B_n/im(delta_n) = B_n/ker(q_n) ~= H~^{n-1}(Delta_{n+1}).
  The generators of the degree-shift-aware object ARE the absolute
  cohomologies H~^{n-1}(Delta_{n+1}) = (conjecturally) sgn_{S_{n+1}} -- the
  canonical NON-finitely-generated FI-module.  Route (ii) does not reduce
  (FG-Cofiber): it reproduces it.""")

    # -- [F] verdict ------------------------------------------------------
    banner("[F]  VERDICT")
    print(f"""  F16 -- route (ii) WEAKER form (bounded central-stability
  presentation for ((B_n)_n, {{partial_n}})) -- VERDICT:

      AMBER-route-ii-stalls
      (sub-case: the bounded presentation PROVABLY DOES NOT EXIST)

  Established (this script + the F16 doc):
    [D] partial_{{n+1}} o partial_n = 0 for all n, UNCONDITIONALLY -- pure
        homological algebra (F15 Lemma 3.1 + exactness of the pair LES).
        Verified at the cochain level for n=3 in [C] (q_3 o delta_3 = 0,
        with explicit representatives); the general case is the same
        theorem, needing no Delta_5 computation [D].
    [E] under concentration (M1's half), partial is the only degree-raising
        structure map, and partial^2 = 0 forces the generators object
        H~_0(H) to have unbounded support.  No bounded set of generators
        reaches B_n for large n.  Hence NO bounded central-stability
        presentation -- route (ii)'s weaker form also fails.
    [C] delta_3 injective ((UCC.2) at n=3) re-derived with explicit reps.

  (UCC.2) interaction (the load-bearing sub-question):  the obstruction in
  [E] uses partial^2 = 0 (unconditional) + concentration (M1) only -- it is
  INDEPENDENT of (UCC.2).  (UCC.2) merely SHARPENS the conclusion to
  "exactly one new generator per level".  Route (ii)'s presentation
  argument neither needs nor produces (UCC.2): it stalls, at the coarse
  level, before (UCC.2) is reached.

  Pivot: F15 sec.7.3 option 3 -- M1 equivariant cofiber-Morse computing the
  representation type of B_n directly per n.  Route (iii) (mg-b345) returns
  to a PM/Daniel decision.

  NO new axioms.  NO Lean changes.
  Total runtime: {time.time() - t_start:.1f}s
""")


if __name__ == "__main__":
    main()
