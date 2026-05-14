#!/usr/bin/env python3
r"""
compat_geom_partial_3.py
========================

Compat-Geom F15 / entry sub-problem (E2) companion script (mg-8355).

Phase 1: construct the triple connecting homomorphism

    partial_3 : B_3 = H~^2(Delta_4 / Delta_3)  -->  B_4 = H~^3(Delta_5 / Delta_4)

of the triple (Delta_3 subset Delta_4 subset Delta_5), and test it for
injectivity / isomorphism.

Setting (F1-refined / F2 / F5 / mg-6295 convention)
---------------------------------------------------
Delta_n is the order complex of PPF_n := Pos_n^sub \ {antichain} \ {totals}
(|PPF_3| = 12, |PPF_4| = 194, |PPF_5| = 4110).  iota_n : PPF_n -> PPF_{n+1}
sends a partial order on {0,..,n-1} to the same relation set viewed on
{0,..,n} (element n incomparable to all); it is an order-ideal inclusion,
so Delta_n is a subcomplex of Delta_{n+1} and the pair (Delta_{n+1}, Delta_n)
is a good pair.

  B_n := H~^{n-1}(Delta_{n+1} / Delta_n)   -- the cofiber-cohomology diagonal.

F11 (mg-b352) reduced the representation-type half of (UCC.1) to "partial_n
is an isomorphism for all n", where partial_n is the connecting map of the
triple (Delta_n, Delta_{n+1}, Delta_{n+2}).  F15/(E2) is the first concrete
test: compute partial_3 and decide whether it is an isomorphism.

The key structural fact this script establishes and exploits
------------------------------------------------------------
The triple connecting homomorphism FACTORS as a composite of two pair-LES
maps (a standard, unconditional cochain-level identity -- see the doc
docs/compatibility-geometry-F15-e2-partial-test.md, section 3):

    partial_3  =  delta_4  o  q_3

      q_3    : B_3 = H~^2(Delta_4/Delta_3)  -->  H~^2(Delta_4)
               (the pair-LES map of (Delta_4, Delta_3))
      delta_4: H~^2(Delta_4)                -->  H~^3(Delta_5/Delta_4) = B_4
               (the pair-LES connecting map of (Delta_5, Delta_4))

Hence  rank(partial_3) <= dim H~^2(Delta_4) = 1 < 2 = dim B_3 .

So partial_3 is NOT an isomorphism.  This script verifies every link in
that chain:

  [A] enumerate PPF_3, PPF_4, iota_3, the relative cells of (Delta_4,Delta_3);
      verify cardinalities and f-vectors against mg-6295.
  [B] DIRECT computation (sparse mod-p rank, two primes) of the reduced
      Betti vectors b~_*(Delta_3), b~_*(Delta_4), and the relative Betti
      vector b~_*(Delta_4/Delta_3).  Reproduces Hyp(3), Hyp(4) and the
      mg-6295 / PCR-1 cofiber Betti (0,0,2,0).
  [C] the pair LES of (Delta_4, Delta_3): exactness + the [B] Betti numbers
      pin  rank(q_3) = 1  and  delta_3 injective  (no induced-map
      computation needed -- every rank is forced by exactness).
  [D] delta_4 injective: from the pair LES of (Delta_5, Delta_4) and
      Hyp(5) [H~^2(Delta_5) = 0] -- an established input (F10; and exactly
      the LES F14 itself used, F14 doc section 3.3).  Then
      partial_3 = delta_4 o q_3 gives rank(partial_3) = rank(q_3) = 1.
  [E] independent cross-check via the triple LES of (Delta_3,Delta_4,Delta_5):
      derive H~^2(Delta_5/Delta_3), H~^3(Delta_5/Delta_3) from the pair LES
      of (Delta_5,Delta_3), and verify exactness of the triple LES forces
      rank(partial_3) = 1.
  [F] S_3-equivariant refinement: Lefschetz characters give the S_3-rep
      types; partial_3 is an S_3-map 2.sgn_{S_3} -> 2.sgn_{S_3} of rank 1.
      ker(partial_3) = im(delta_3) is the (UCC.2) sgn-line of B_3.
  [G] general-n diagnosis: the SAME factorization partial_n = delta_{n+1} o
      q_n holds for all n; partial_n iso <=> delta_n = 0 <=> NOT (UCC.2)(n).
  [H] verdict.

Established external inputs (cited; NOT recomputed here -- Delta_5 has
~3.5x10^8 relative cells, out of scope for direct enumeration):
  - Hyp(5): H~^*(Delta_5) = sgn_{S_5} concentrated in degree 3.
            F10 (mg-8216), verified n <= 6.
  - B_4 = H~^3(Delta_5/Delta_4) = 2.sgn_{S_4}, b~_*(Delta_5/Delta_4) =
            (0,0,0,2,0).  F14 (mg-3839), GREEN-cofiber-perfect.
These enter only the triple-LES cross-check [E] and the delta_4-injectivity
input [D]; the CORE result rank(partial_3)=1 needs only [B]+[C] (all in
Delta_4) plus the single cited fact H~^2(Delta_5) = 0.

Pure-Python stdlib only.  Runtime ~ 1-4 min (the sparse rank sweeps over
the ~15k-cell face poset of Delta_4 dominate).

NO new axioms; NO Lean changes.

References
----------
  - mg-b352 (F11) docs/state-F11.md sec.4.2-4.6 -- the partial_n
    identification, the "partial_n iso" reduction, entry sub-problems
    (E1)/(E2).
  - mg-ecf6 (F13, E1) docs/compatibility-geometry-F13-shift-aware-
    functoriality.md -- the degree-shift-aware functor category; the
    triple LES conventions (its sec.2).
  - mg-3839 (F14) docs/compatibility-geometry-F14-pcr-lit2prime.md --
    B_4 = 2.sgn_{S_4}, b~_*(Delta_5/Delta_4) = (0,0,0,2,0).
  - mg-6295 (PCR-Lit-2) scripts/compat_geom_cofiber_morse_n3n4.py --
    poset enumeration, chain enumeration, sparse mod-p rank, S_3
    Lefschetz machinery (transcribed / adapted below, identical
    convention); B_3 = 2.sgn_{S_3}, the two critical 2-cells.
  - mg-59f3 (PCR-2) -- delta_3 injective on the sgn isotype (UCC.2 at n=3).
  - mg-8216 (F10) -- (UCC), Hyp(n) verified n <= 6.
"""

import sys
import time
from itertools import permutations


# =======================================================================
# 1. Poset enumeration
#    (transcribed verbatim from mg-6295's compat_geom_cofiber_morse_n3n4.py,
#     itself from posn_morse_check.py / mg-7455 -- identical convention)
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


# =======================================================================
# 3. iota_3 inclusion + relative cells of (Delta_4, Delta_3)
# =======================================================================

def iota_image(PPF_small):
    """Image of iota : PPF_n <-> PPF_{n+1} (the new element incomparable to
    all).  A partial order is a frozenset of pairs; the relation set is
    literally unchanged, only the ground set grows -- so the image is just
    the same frozensets, viewed inside PPF_{n+1}."""
    return set(frozenset(P) for P in PPF_small)


def relative_cells_by_dim(chains_big_by_dim, sub_vertices):
    """rel[k] = chains of Delta_{n+1} with >= 1 vertex NOT in sub_vertices --
    the cells of the relative complex C_*(Delta_{n+1}, Delta_n)."""
    rel = {}
    for d, chains in chains_big_by_dim.items():
        rel[d] = [c for c in chains if any(v not in sub_vertices for v in c)]
    return rel


# =======================================================================
# 4. Sparse mod-p rank
#    (transcribed from mg-6295; column = list of (row, coeff) pairs)
# =======================================================================

def matrix_rank_mod_p(cols, p):
    cols_d = []
    for col in cols:
        d = {}
        for (r, c) in col:
            v = c % p
            if v:
                d[r] = (d.get(r, 0) + v) % p
        cols_d.append({r: v for r, v in d.items() if v % p})
    rank = 0
    pivot_row_to_col = {}
    for j, col in enumerate(cols_d):
        while col:
            r = min(col.keys())
            v = col[r]
            if v % p == 0:
                del col[r]
                continue
            if r in pivot_row_to_col:
                pcol = cols_d[pivot_row_to_col[r]]
                pv = pcol[r]
                pv_inv = pow(pv % p, -1, p)
                factor = (v * pv_inv) % p
                for rr, vv in pcol.items():
                    nv = (col.get(rr, 0) - factor * vv) % p
                    if nv:
                        col[rr] = nv
                    elif rr in col:
                        del col[rr]
            else:
                pivot_row_to_col[r] = j
                rank += 1
                break
    return rank


def matrix_rank(cols, primes=(1_000_003, 999_983)):
    ranks = [matrix_rank_mod_p([list(c) for c in cols], p) for p in primes]
    if len(set(ranks)) > 1:
        raise RuntimeError(f"rank disagreement across primes: {ranks}")
    return ranks[0]


# =======================================================================
# 5. Reduced + relative Betti vectors
# =======================================================================

def boundary_columns(chains_by_dim, k, lower_index):
    """Columns of the boundary map d_k : C_k -> C_{k-1}, sparse format.
    A k-chain c = (P_0 < ... < P_k); d_k(c) = sum_i (-1)^i (c without P_i).
    lower_index maps a (k-1)-chain to its row index."""
    cols = []
    for c in chains_by_dim[k]:
        col = []
        for i in range(len(c)):
            face = c[:i] + c[i + 1:]
            if face in lower_index:
                col.append((lower_index[face], (-1) ** i))
        cols.append(col)
    return cols


def reduced_betti(chains_by_dim):
    """Reduced Betti vector of the order complex.  Augmentation: the empty
    chain () is the unique (-1)-cell, d_0((P,)) = ().  Returns (betti, ranks)
    with betti[k] = dim H~_k for k = 0..maxdim."""
    maxd = max(chains_by_dim)
    # row index for each dimension; dim -1 is the single empty cell.
    idx = {-1: {(): 0}}
    for d in range(0, maxd + 1):
        idx[d] = {c: i for i, c in enumerate(chains_by_dim[d])}
    ranks = {}
    # d_0 : C_0 -> C_{-1}, every 0-cell maps to () with coeff +1.
    ranks[0] = 1 if chains_by_dim.get(0) else 0
    for k in range(1, maxd + 1):
        cols = boundary_columns(chains_by_dim, k, idx[k - 1])
        ranks[k] = matrix_rank(cols)
        print(f"        rank d_{k} = {ranks[k]:>6d}   "
              f"(C_{k} has {len(chains_by_dim[k])} cells)", flush=True)
    betti = {}
    for k in range(0, maxd + 1):
        dim_ck = len(chains_by_dim[k])
        betti[k] = dim_ck - ranks.get(k, 0) - ranks.get(k + 1, 0)
    return tuple(betti[k] for k in range(0, maxd + 1)), ranks


def relative_betti(rel):
    """Reduced Betti vector of the relative complex C_*(Delta_{n+1},Delta_n)
    over Q.  No augmentation cell -- the empty chain lives in Delta_n, so it
    is not a relative cell; relative homology = reduced cofiber homology for
    a good pair."""
    idx = {d: {c: i for i, c in enumerate(rel[d])} for d in rel}
    maxd = max(rel)
    ranks = {0: 0}
    for k in range(1, maxd + 1):
        lower = idx[k - 1]
        cols = []
        for c in rel[k]:
            col = []
            for i in range(len(c)):
                face = c[:i] + c[i + 1:]
                if face in lower:
                    col.append((lower[face], (-1) ** i))
            cols.append(col)
        ranks[k] = matrix_rank(cols)
        print(f"        rank d_{k}(rel) = {ranks[k]:>6d}   "
              f"(C_{k}(rel) has {len(rel[k])} cells)", flush=True)
    betti = {}
    for k in range(maxd + 1):
        betti[k] = len(rel[k]) - ranks.get(k, 0) - ranks.get(k + 1, 0)
    return tuple(betti[k] for k in range(maxd + 1)), ranks


# =======================================================================
# 6. S_3 / S_4 actions + Lefschetz characters
#    (S_3 part transcribed from mg-6295; S_4 part added)
# =======================================================================

def apply_perm(P, perm):
    return frozenset((perm[a], perm[b]) for (a, b) in P)


# ---- S_3 character table; classes keyed by cycle type --------------------
S3_CLASSES = [(1, 1, 1), (2, 1), (3,)]
S3_CLASS_SIZE = {(1, 1, 1): 1, (2, 1): 3, (3,): 2}
S3_IRREPS = {
    "triv": {(1, 1, 1): 1, (2, 1): 1,  (3,): 1},
    "sgn":  {(1, 1, 1): 1, (2, 1): -1, (3,): 1},
    "std":  {(1, 1, 1): 2, (2, 1): 0,  (3,): -1},
}


def cycle_type(perm, m):
    """Cycle type of a permutation of {0,...,m-1} given as a tuple `perm`
    (we only look at the first m entries)."""
    seen = [False] * m
    ct = []
    for i in range(m):
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


def decompose_S3(char_by_class):
    out = {}
    for name, irr in S3_IRREPS.items():
        s = 0
        for ct in S3_CLASSES:
            s += S3_CLASS_SIZE[ct] * char_by_class[ct] * irr[ct]
        m, rem = divmod(s, 6)
        if rem != 0:
            raise RuntimeError(f"non-integer multiplicity for {name}: {s}/6")
        out[name] = m
    return out


def lefschetz_reduced_absolute(perm, chains_by_dim, m):
    """Reduced Lefschetz number of g = perm acting on an order complex
    Delta(elements):  L~(g) = sum_{k>=0} (-1)^k #{g-fixed k-cells}  - 1
    (the -1 is the augmentation / (-1)-cell, always g-fixed).  When the
    reduced homology is concentrated in a single degree d,
    L~(g) = (-1)^d trace(g | H~_d)."""
    L = -1  # the empty (-1)-cell
    for d, chains in chains_by_dim.items():
        cnt = 0
        for c in chains:
            if all(apply_perm(P, perm) == P for P in c):
                cnt += 1
        L += ((-1) ** d) * cnt
    return L


def lefschetz_cofiber(perm, chains_big_by_dim, sub_vertices):
    """Reduced Lefschetz number of g on the cofiber Delta_{n+1}/Delta_n:
    L(g) = sum_k (-1)^k #{g-fixed relative k-cells}.  No augmentation term
    (the empty cell is in Delta_n).  Concentrated homology => L(g) =
    (-1)^d trace(g | H~_d(cofiber))."""
    L = 0
    for d, chains in chains_big_by_dim.items():
        cnt = 0
        for c in chains:
            if all(apply_perm(P, perm) == P for P in c):
                if any(v not in sub_vertices for v in c):
                    cnt += 1
        L += ((-1) ** d) * cnt
    return L


# =======================================================================
# 7. Established external inputs (cited; not recomputed -- Delta_5 is huge)
# =======================================================================

# Hyp(n): H~^*(Delta_n) = sgn_{S_n}, concentrated in degree n-2.
#   Verified n = 3,4,5,6 (F10 / mg-8216).  [B] below re-derives n = 3,4
#   from scratch; n = 5 is the cited input.
HYP5_betti = (0, 0, 0, 1, 0)            # b~_*(Delta_5): sgn_{S_5} in deg 3
HYP5_cite = "F10 (mg-8216), Hyp(5) verified n<=6"

# F14 (mg-3839), GREEN-cofiber-perfect: the n=4->5 cofiber cohomology.
B4_betti = (0, 0, 0, 2, 0)              # b~_*(Delta_5/Delta_4)
B4_rep = "2.sgn_{S_4}"                  # B_4 = H~^3(Delta_5/Delta_4)
F14_cite = "F14 (mg-3839), docs/compatibility-geometry-F14-pcr-lit2prime.md"


# =======================================================================
# 8. Main driver
# =======================================================================

def banner(title):
    print("\n" + "=" * 70)
    print("  " + title)
    print("=" * 70)


def main():
    t_start = time.time()
    print(r"""
compat_geom_partial_3.py  --  F15 / entry sub-problem (E2)  (mg-8355)
Construct  partial_3 : B_3 -> B_4  (triple connecting hom of
Delta_3 c Delta_4 c Delta_5) and test it for isomorphism.
""")

    # -- [A] enumerate -----------------------------------------------------
    banner("[A]  PPF_3, PPF_4, iota_3, the relative cells of (Delta_4,Delta_3)")
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

    sub_vertices = iota_image(PPF_3)
    # iota_3 is an order-ideal (downward-closed) inclusion: a sub-relation of
    # a 3-isolated poset is 3-isolated.  Verify directly.
    ideal_ok = True
    for Q in es4:
        if Q in sub_vertices:
            for R in es4:
                if R != Q and R < Q and R not in sub_vertices:
                    ideal_ok = False
    print(f"  iota_3(PPF_3) is a downward-closed subposet (order ideal)? "
          f"{ideal_ok}")
    assert ideal_ok, "iota_3 image is not an order ideal"

    rel = relative_cells_by_dim(chains4, sub_vertices)
    f_rel = [len(rel[d]) for d in sorted(rel)]
    print(f"  f(C_*(Delta_4,Delta_3)) = {f_rel}   "
          f"(expect [182, 1860, 5232, 5664, 2112])")
    assert f_rel == [182, 1860, 5232, 5664, 2112]
    chi_rel = sum((-1) ** d * f_rel[d] for d in range(len(f_rel)))
    print(f"  chi~(Delta_4/Delta_3) = {chi_rel}   (expect +2)")
    assert chi_rel == 2

    # -- [B] direct Betti --------------------------------------------------
    banner("[B]  DIRECT reduced/relative Betti  (sparse mod-p rank, 2 primes)")
    print("  b~_*(Delta_3):")
    t0 = time.time()
    betti3, _ = reduced_betti(chains3)
    print(f"     b~_*(Delta_3) = {betti3}   "
          f"(expect (0,1): Delta_3 ~ S^1)   [{time.time()-t0:.1f}s]")
    assert betti3 == (0, 1)

    print("  b~_*(Delta_4):")
    t0 = time.time()
    betti4, _ = reduced_betti(chains4)
    print(f"     b~_*(Delta_4) = {betti4}   "
          f"(expect (0,0,1,0,0): Delta_4 ~ S^2 = Hyp(4))   "
          f"[{time.time()-t0:.1f}s]")
    assert betti4 == (0, 0, 1, 0, 0)

    print("  b~_*(Delta_4/Delta_3)   [= B_3 in degree 2]:")
    t0 = time.time()
    betti_rel, _ = relative_betti(rel)
    print(f"     b~_*(Delta_4/Delta_3) = {betti_rel}   "
          f"(expect (0,0,2,0,0): mg-6295 / PCR-1)   [{time.time()-t0:.1f}s]")
    assert betti_rel == (0, 0, 2, 0, 0)

    # The numbers the pair / triple LES needs:
    dimH = {
        ("D3", 1): betti3[1],                 # H~^1(Delta_3)        = 1
        ("D3", 2): 0,                          # H~^2(Delta_3)        = 0
        ("D4", 1): betti4[1],                 # H~^1(Delta_4)        = 0
        ("D4", 2): betti4[2],                 # H~^2(Delta_4)        = 1
        ("D4", 3): betti4[3],                 # H~^3(Delta_4)        = 0
        ("D4/D3", 2): betti_rel[2],           # B_3 = H~^2(D4/D3)    = 2
        ("D4/D3", 3): betti_rel[3],           # H~^3(D4/D3)          = 0
        # Delta_5 inputs -- cited, see section 7:
        ("D5", 1): HYP5_betti[1],             # H~^1(Delta_5)        = 0
        ("D5", 2): HYP5_betti[2],             # H~^2(Delta_5)        = 0
        ("D5", 3): HYP5_betti[3],             # H~^3(Delta_5)        = 1
        ("D5/D4", 2): B4_betti[2],            # H~^2(D5/D4)          = 0
        ("D5/D4", 3): B4_betti[3],            # B_4 = H~^3(D5/D4)    = 2
    }
    print(f"\n  Betti dictionary (computed [B] + cited):")
    print(f"     H~^1(Delta_3)      = {dimH[('D3',1)]}   (computed)")
    print(f"     H~^2(Delta_3)      = {dimH[('D3',2)]}   (computed)")
    print(f"     H~^1(Delta_4)      = {dimH[('D4',1)]}   (computed)")
    print(f"     H~^2(Delta_4)      = {dimH[('D4',2)]}   (computed)")
    print(f"     B_3 = H~^2(D4/D3)  = {dimH[('D4/D3',2)]}   (computed)")
    print(f"     H~^3(D4/D3)        = {dimH[('D4/D3',3)]}   (computed)")
    print(f"     H~^1(Delta_5)      = {dimH[('D5',1)]}   (cited: {HYP5_cite})")
    print(f"     H~^2(Delta_5)      = {dimH[('D5',2)]}   (cited: {HYP5_cite})")
    print(f"     H~^3(Delta_5)      = {dimH[('D5',3)]}   (cited: {HYP5_cite})")
    print(f"     H~^2(D5/D4)        = {dimH[('D5/D4',2)]}   (cited: {F14_cite})")
    print(f"     B_4 = H~^3(D5/D4)  = {dimH[('D5/D4',3)]}   (cited: {F14_cite})")

    # -- [C] pair LES of (Delta_4, Delta_3): pin rank(q_3) -----------------
    banner("[C]  pair LES of (Delta_4, Delta_3):  rank(q_3) and delta_3")
    print("""  The cohomology pair LES of (Delta_4, Delta_3):

    .. -> H~^1(D4) -> H~^1(D3) --d3--> H~^2(D4/D3) --q3--> H~^2(D4)
                                              --i3*--> H~^2(D3) -> ..

  with dims     0  ->   1   --d3-->     2     --q3-->   1   --i3*-->  0 .
  q_3 is the pair-LES map B_3 = H~^2(D4/D3) -> H~^2(D4) (induced by the
  cochain inclusion C^*(D4,D3) <-> C^*(D4)); delta_3 the connecting map.
  Exactness forces every rank from the [B] Betti numbers alone:""")
    a, b, c, d, e = (dimH[("D4", 1)], dimH[("D3", 1)], dimH[("D4/D3", 2)],
                     dimH[("D4", 2)], dimH[("D3", 2)])
    # exactness at H~^1(D3): ker(delta_3) = im(H~^1(D4) -> H~^1(D3))
    rank_d3 = b - a            # a = dim im into H~^1(D3) = rank of H~^1(D4)->..
    # but H~^1(D4) = 0 so that map is 0; ker(delta_3) = 0:
    delta3_injective = (a == 0)
    rank_delta3 = b if delta3_injective else None
    # exactness at H~^2(D4/D3): ker(q_3) = im(delta_3)
    rank_q3 = c - rank_delta3
    # exactness at H~^2(D4): ker(i3*) = im(q_3); rank(i3*) <= dim H~^2(D3) = 0
    rank_i3star = d - rank_q3
    print(f"     H~^1(Delta_4) = {a}  =>  delta_3 is injective: "
          f"{delta3_injective}")
    print(f"     rank(delta_3) = {rank_delta3}   "
          f"(delta_3 : H~^1(D3)=1  >->  B_3=2)")
    print(f"     ker(q_3) = im(delta_3),  dim = {rank_delta3}")
    print(f"     rank(q_3)     = dim B_3 - dim ker(q_3) = {c} - "
          f"{rank_delta3} = {rank_q3}")
    print(f"     rank(i3*)     = {rank_i3star}   (consistent: "
          f"dim H~^2(D3) = {e})")
    assert delta3_injective and rank_delta3 == 1
    assert rank_q3 == 1, f"expected rank(q_3) = 1, got {rank_q3}"
    assert rank_i3star == 0
    print(f"\n  ==>  q_3 : B_3 = 2-dim  -->>  H~^2(Delta_4) = 1-dim   is")
    print(f"       SURJECTIVE with 1-dimensional kernel ker(q_3) = im(delta_3).")

    # -- [D] delta_4 injective; partial_3 = delta_4 o q_3 ------------------
    banner("[D]  delta_4 injective;  partial_3 = delta_4 o q_3  =>  rank 1")
    print(f"""  pair LES of (Delta_5, Delta_4), around degree 2:

    .. -> H~^2(D5) --i4*--> H~^2(D4) --delta_4--> H~^3(D5/D4) = B_4 -> ..

  H~^2(Delta_5) = {dimH[('D5',2)]}  (cited: {HYP5_cite})
  => ker(delta_4) = im(i4*) = 0  =>  delta_4 is INJECTIVE.
     rank(delta_4) = dim H~^2(Delta_4) = {dimH[('D4',2)]} .
  (This is exactly the LES F14 itself used -- F14 doc sec.3.3:
   "0 -> sgn_{{S_5}} -> B_4 -> sgn_{{S_4}} -> 0".)

  CHAIN-LEVEL FACTORISATION (standard; doc sec.3):
     partial_3 = delta_4 o q_3 : B_3 --q3-->> H~^2(D4) >--delta_4--> B_4 .
  Both q_3 and delta_4 use the SAME cochain recipe ("extend a relative
  2-cocycle by zero, apply d"), so the composite IS the triple connecting
  map.  Therefore:""")
    delta4_injective = (dimH[("D5", 2)] == 0)
    rank_delta4 = dimH[("D4", 2)] if delta4_injective else None
    rank_partial3 = rank_q3 if delta4_injective else None     # delta_4 inj.
    print(f"     delta_4 injective: {delta4_injective},  "
          f"rank(delta_4) = {rank_delta4}")
    print(f"     rank(partial_3) = rank(delta_4 o q_3) = rank(q_3) = "
          f"{rank_partial3}   (delta_4 injective)")
    assert delta4_injective and rank_partial3 == 1
    dim_B3, dim_B4 = dimH[("D4/D3", 2)], dimH[("D5/D4", 3)]
    print(f"\n  partial_3 : B_3 ({dim_B3}-dim)  -->  B_4 ({dim_B4}-dim)   has "
          f"RANK {rank_partial3}.")
    print(f"  ==>  partial_3 is NOT injective (1-dim kernel),")
    print(f"       NOT surjective (1-dim cokernel),  NOT an isomorphism.")
    print(f"       As a 2x2 matrix:  det(partial_3) = 0,  rank = 1.")

    # -- [E] triple LES cross-check ---------------------------------------
    banner("[E]  cross-check: the triple LES of (Delta_3, Delta_4, Delta_5)")
    print("""  First derive the double-cofiber cohomology from the pair LES
  of (Delta_5, Delta_3):

    H~^1(D5) -> H~^1(D3) -> H~^2(D5/D3) -> H~^2(D5)   [for H~^2(D5/D3)]
    H~^2(D3) -> H~^3(D5/D3) -> H~^3(D5) -> H~^3(D3)   [for H~^3(D5/D3)]""")
    # H~^2(D5/D3): 0 -> H~^1(D3) -> H~^2(D5/D3) -> H~^2(D5)=0
    dimH[("D5/D3", 2)] = dimH[("D3", 1)] - dimH[("D5", 1)]   # = 1 - 0
    # H~^3(D5/D3): H~^2(D3)=0 -> H~^3(D5/D3) -> H~^3(D5) -> H~^3(D3)=0
    dimH[("D5/D3", 3)] = dimH[("D5", 3)] - dimH[("D3", 2)]   # = 1 - 0
    print(f"     H~^2(Delta_5/Delta_3) = {dimH[('D5/D3',2)]}   "
          f"(= H~^1(D3), 1-dim -- NOT zero)")
    print(f"     H~^3(Delta_5/Delta_3) = {dimH[('D5/D3',3)]}   "
          f"(= H~^3(D5), 1-dim)")
    print("""
  The triple LES of (Delta_3 c Delta_4 c Delta_5), around degree 2
  (F13 doc eq. 2.2; C/B = D5/D4, C/A = D5/D3, B/A = D4/D3):

    H~^2(D5/D4) -j*-> H~^2(D5/D3) -r*-> H~^2(D4/D3) -partial_3->
        H~^3(D5/D4) -j*-> H~^3(D5/D3) -r*-> H~^3(D4/D3)

  with dims:""")
    seq = [
        ("H~^2(D5/D4)", dimH[("D5/D4", 2)]),
        ("H~^2(D5/D3)", dimH[("D5/D3", 2)]),
        ("H~^2(D4/D3)=B_3", dimH[("D4/D3", 2)]),
        ("H~^3(D5/D4)=B_4", dimH[("D5/D4", 3)]),
        ("H~^3(D5/D3)", dimH[("D5/D3", 3)]),
        ("H~^3(D4/D3)", dimH[("D4/D3", 3)]),
    ]
    print("     " + "  ->  ".join(f"{nm}={dm}" for nm, dm in seq))
    dims = [dm for _, dm in seq]
    # An exact sequence V0 -> V1 -> ... with maps f_i : V_i -> V_{i+1}.
    # rank(f_i) + rank(f_{i+1}) = dim V_{i+1} (exactness at V_{i+1}), with
    # f_{-1} = 0 into V_0.  Solve the recursion for all ranks.
    rk = [0] * (len(dims))   # rk[i] = rank(f_i : V_i -> V_{i+1})
    prev = 0                 # rank of the map INTO V_0 is 0 (sequence starts)
    for i in range(len(dims) - 1):
        # exactness at V_i: rank(into V_i) + rank(out of V_i) = dim V_i
        rk[i] = dims[i] - prev
        prev = rk[i]
    rk[-1] = 0
    names = ["j*(deg2)", "r*(deg2)", "partial_3", "j*(deg3)", "r*(deg3)"]
    print("  ranks forced by exactness:")
    for i in range(len(names)):
        print(f"     rank({names[i]:>10s}) = {rk[i]}")
    triple_rank_partial3 = rk[2]
    print(f"\n  triple-LES exactness  =>  rank(partial_3) = "
          f"{triple_rank_partial3}")
    assert triple_rank_partial3 == rank_partial3 == 1, \
        "triple-LES rank disagrees with the factorisation rank"
    print(f"  AGREES with [D]: rank(partial_3) = 1.   Two independent")
    print(f"  derivations (factorisation; triple-LES exactness) concur.")

    # -- [F] S_3-equivariant refinement -----------------------------------
    banner("[F]  S_3-equivariant refinement  (Lefschetz characters)")
    # S_3 < S_4 permuting {0,1,2}, fixing 3.
    chars_D3 = {}     # char of H~^1(Delta_3)
    chars_D4 = {}     # char of H~^2(Delta_4)  (as S_3-rep, S_3 < S_4)
    chars_B3 = {}     # char of B_3 = H~^2(Delta_4/Delta_3)
    for g3 in permutations(range(3)):
        perm4 = tuple(g3) + (3,)
        ct = cycle_type(perm4, 3)
        # Delta_3: g acts on PPF_3 (= relations on {0,1,2}).
        L3 = lefschetz_reduced_absolute(perm4, chains3, 3)
        # H~_*(Delta_3) concentrated in degree 1 => L~ = (-1)^1 tr(g|H~_1)
        chars_D3[ct] = -L3
        # Delta_4: g acts on PPF_4.  H~_*(Delta_4) concentrated in degree 2.
        L4 = lefschetz_reduced_absolute(perm4, chains4, 4)
        chars_D4[ct] = L4          # (-1)^2 = +1
        # cofiber Delta_4/Delta_3: H~_* concentrated in degree 2.
        Lc = lefschetz_cofiber(perm4, chains4, sub_vertices)
        chars_B3[ct] = Lc
    dec_D3 = decompose_S3(chars_D3)
    dec_D4 = decompose_S3(chars_D4)
    dec_B3 = decompose_S3(chars_B3)
    print(f"  H~^1(Delta_3)         char {dict(chars_D3)}  =>  {dec_D3}")
    print(f"  H~^2(Delta_4)|_{{S_3}}   char {dict(chars_D4)}  =>  {dec_D4}")
    print(f"  B_3 = H~^2(D4/D3)     char {dict(chars_B3)}  =>  {dec_B3}")
    assert dec_D3 == {"triv": 0, "sgn": 1, "std": 0}, dec_D3
    assert dec_D4 == {"triv": 0, "sgn": 1, "std": 0}, dec_D4
    assert dec_B3 == {"triv": 0, "sgn": 2, "std": 0}, dec_B3
    print(f"""
  So  H~^1(Delta_3) = sgn_{{S_3}},  H~^2(Delta_4) = sgn_{{S_4}}  (its
  restriction to S_3 is sgn_{{S_3}}),  B_3 = 2.sgn_{{S_3}}  -- as expected
  (Hyp(3), Hyp(4), mg-6295).  B_4 = {B4_rep} (cited: {F14_cite}); its
  restriction to S_3 along S_3 < S_4 < S_5 is 2.sgn_{{S_3}} as well.

  partial_3 : B_3 -> B_4 is S_3-equivariant (S_3 fixes 3,4 and acts on the
  whole triple).  As a map  2.sgn_{{S_3}} -> 2.sgn_{{S_3}}  it is a 2x2
  matrix over End_{{S_3}}(sgn_{{S_3}}) = Q.  [C]-[E] give rank 1, so:
     det(partial_3) = 0,  rank(partial_3) = 1.
  ker(partial_3) = im(delta_3) is the sgn_{{S_3}}-line of B_3 that is the
  image of the pair connecting map delta_3 : H~^1(Delta_3) -> B_3 -- i.e.
  exactly the (UCC.2) line.  im(partial_3) = im(delta_4) = ker(iota_4*),
  a sgn-line in B_4.  partial_3 annihilates precisely the "inherited from
  Delta_3" part of B_3 and is injective on the complementary line.""")

    # -- [G] general-n diagnosis ------------------------------------------
    banner("[G]  general-n diagnosis:  partial_n = delta_{n+1} o q_n")
    print(r"""  The factorisation is n-uniform.  For the triple
  (Delta_n, Delta_{n+1}, Delta_{n+2}) the SAME cochain identity gives

     partial_n  =  delta_{n+1}  o  q_n

       q_n      : B_n = H~^{n-1}(Delta_{n+1}/Delta_n) -> H~^{n-1}(Delta_{n+1})
       delta_{n+1}: H~^{n-1}(Delta_{n+1}) -> H~^n(Delta_{n+2}/Delta_{n+1}) = B_{n+1}

  Pair LES of (Delta_{n+1}, Delta_n):  Hyp(n) [H~^{n-1}(Delta_n)=0] makes
  q_n SURJECTIVE with ker(q_n) = im(delta_n).
  Pair LES of (Delta_{n+2}, Delta_{n+1}):  Hyp(n+2) [H~^{n-1}(Delta_{n+2})=0]
  makes delta_{n+1} INJECTIVE.
  Hence  rank(partial_n) = rank(q_n) = dim H~^{n-1}(Delta_{n+1}).

  Therefore:
     partial_n is an isomorphism
       <=>  rank(partial_n) = 2
       <=>  q_n injective              (delta_{n+1} already injective)
       <=>  ker(q_n) = im(delta_n) = 0
       <=>  delta_n = 0 .

  But (UCC.2) at level n asserts delta_n : H~^{n-2}(Delta_n) = sgn_{S_n}
  >-> B_n is INJECTIVE, hence delta_n =/= 0.  So:

     (UCC.2)(n)   ==>   partial_n is NOT an isomorphism.

  Equivalently, under the program's own target Hyp(n+1) [H~^{n-1}(Delta_{n+1})
  = sgn_{S_{n+1}} is 1-dimensional], rank(partial_n) <= 1 < 2 for ALL n.

  The F11 sec.4.4 reduction "partial_n iso for all n" is thus not merely
  unproven -- it is INCOMPATIBLE with (UCC.2), a part of the very (UCC)
  the program is establishing.  partial_n factors through the cohomology
  of the single complex Delta_{n+1}, which (UCC) forces to be 1-dimensional.
""")

    # -- [H] verdict ------------------------------------------------------
    banner("[H]  VERDICT")
    print(f"""  Phase 1 (compute partial_3, test isomorphism) -- COMPLETE.

  RESULT:  partial_3 : B_3 -> B_4 has RANK EXACTLY 1.
           It is NOT an isomorphism (not injective, not surjective).

  Established by two independent rigorous routes:
    [D] the factorisation partial_3 = delta_4 o q_3 with q_3 rank 1
        (computed in Delta_4, [B]+[C]) and delta_4 injective (Hyp(5));
    [E] exactness of the triple LES of (Delta_3,Delta_4,Delta_5) with the
        computed [B] Betti numbers and the cited F14 / Hyp(5) inputs.
  Both give rank(partial_3) = 1.

  PRECISE STRUCTURE:
    ker(partial_3) = im(delta_3)            -- the (UCC.2) sgn_{{S_3}}-line of B_3
    im(partial_3)  = im(delta_4) = ker(iota_4*)  -- a sgn-line in B_4
    partial_3 factors through H~^2(Delta_4) = sgn_{{S_4}}, which is 1-dim.

  GENERAL-n [G]:  partial_n = delta_{{n+1}} o q_n for all n;
    partial_n iso  <=>  delta_n = 0  <=>  NOT (UCC.2)(n).
  Route (ii)'s simplest form -- "(B_n)_n is the free object M(0)^+2,
  equivalently every partial_n iso" -- FAILS, uniformly and for a precise
  structural reason.  (The WEAKER form -- a bounded central-stability
  presentation -- is NOT killed by this; see the doc, section 6.)

  VERDICT TAG:  AMBER-partial3-not-iso.
  Phase 2 (the iso-based general-n argument) is moot and not executed,
  per the ticket.  The general-n DIAGNOSIS [G] is delivered instead:
  it pinpoints precisely where the degree-shift-aware object is not free.

  NO new axioms.  NO Lean changes.
  Total runtime: {time.time() - t_start:.1f}s
""")


if __name__ == "__main__":
    main()
