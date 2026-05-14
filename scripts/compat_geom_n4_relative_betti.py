#!/usr/bin/env python3
r"""
compat_geom_n4_relative_betti.py
================================

Compat-Geom F8''' companion script (mg-f91f).  Computes the full rational
Betti vector of the relative simplicial complex (Delta_4, Delta_3), where
Delta_n is the order complex of PPF_n := Pos_n^sub \ {antichain} \ {totals}
(the F1-refined / F2 / F5 convention).

The inclusion iota_3 : PPF_3 -> PPF_4 sends a partial order P on {0,1,2} to
the partial order on {0,1,2,3} with the same relations (so element 3 is
incomparable to all of {0,1,2}).  This induces Delta_3 ↪ Delta_4 as a
sub-complex.

Outputs:
  - |PPF_3|, |PPF_4|, f-vectors of Delta_3 and Delta_4.
  - chi-tilde of Delta_3 and Delta_4 (trip-wire against F8'' §4.2 baseline).
  - Relative f-vector of (Delta_4, Delta_3).
  - chi-tilde of relative complex (cross-check: should equal +2).
  - Full Betti vector b_0, b_1, b_2, b_3 of the relative complex over Q.
  - Verdict tag: GREEN-wedge / GREEN-layer / AMBER-other / RED-foil.

Pure-Python stdlib only; rank computation uses mod-p Gauss followed by an
independent re-check at a second prime to catch any large-prime accidents.

Method follows F8'' §6.1 PCR-1 spec.  See also:
  - docs/compatibility-geometry-F8pp-quillen-fiber.md §4-§5
  - scripts/posn_morse_check.py (F2 / mg-7455) for enumeration scaffolding
  - scripts/posn_wedge_check_n5.py (F1-refined / mg-3a61) ditto
"""

import sys
import time
from itertools import combinations


# -----------------------------------------------------------------------
# 1. Poset enumeration (incremental cover-addition; copy of F1/F2 pattern)
# -----------------------------------------------------------------------

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
                    new_rel = P | {(a, b)}
                    closed = transitive_closure(new_rel)
                    if any((j, i) in closed for (i, j) in closed):
                        continue
                    if closed not in seen:
                        seen.add(closed)
                        new_frontier.add(closed)
        frontier = new_frontier
    return list(seen)


def is_total(P, n):
    """A total order has all n(n-1)/2 ordered pairs of distinct elements."""
    return len(P) == n * (n - 1) // 2


def make_PPF(n):
    r"""PPF_n := Pos_n^sub \ {antichain} \ {total orders}."""
    return [P for P in enumerate_posets(n)
            if P != frozenset() and not is_total(P, n)]


# -----------------------------------------------------------------------
# 2. Order-complex chains
# -----------------------------------------------------------------------

def above_map(elements):
    """Strict refinement P < Q (Q has more relations)."""
    es = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    above = {P: [] for P in es}
    for P in es:
        for Q in es:
            if P != Q and P < Q:
                above[P].append(Q)
    return es, above


def all_chains_by_dim(elements, above):
    """Strict chains in (elements, <).  by_dim[k] = list of (k+1)-element
    chains, each represented as a tuple of frozensets in ascending order."""
    by_dim = {0: [(P,) for P in elements]}
    cur = by_dim[0]
    dim = 0
    while cur:
        nxt = []
        for c in cur:
            top = c[-1]
            for Q in above[top]:
                nxt.append(c + (Q,))
        if not nxt:
            break
        dim += 1
        by_dim[dim] = nxt
        cur = nxt
    return by_dim


def f_vector(chains_by_dim):
    dims = sorted(chains_by_dim.keys())
    return [len(chains_by_dim[d]) for d in dims]


def reduced_euler(fvec):
    """chi-tilde = -1 + sum_k (-1)^k f_k (augmented; includes ∅ in dim -1)."""
    return -1 + sum(((-1) ** k) * fvec[k] for k in range(len(fvec)))


# -----------------------------------------------------------------------
# 3. Inclusion iota_3 : PPF_3 -> PPF_4
# -----------------------------------------------------------------------

def iota_3_image(PPF_3):
    """Image of iota_3 : PPF_3 ↪ PPF_4 (element 3 incomparable to all)."""
    # iota_3 maps a partial order on {0,1,2} to the same frozenset of pairs,
    # interpreted as a partial order on {0,1,2,3}.  No new relations needed.
    return [frozenset(P) for P in PPF_3]


# -----------------------------------------------------------------------
# 4. Relative chain complex C_*(Delta_4, Delta_3) and its boundary maps
# -----------------------------------------------------------------------

def relative_chains(chains4_by_dim, subcomplex_vertices):
    """Return rel_by_dim[k] = chains of Delta_4 with at least one vertex NOT
    in subcomplex_vertices.  These represent C_k(Delta_4, Delta_3).
    Also return idx[k] = {chain -> column index}."""
    rel_by_dim = {}
    idx = {}
    for d, chains in chains4_by_dim.items():
        rel = [c for c in chains if any(v not in subcomplex_vertices for v in c)]
        rel_by_dim[d] = rel
        idx[d] = {c: i for i, c in enumerate(rel)}
    return rel_by_dim, idx


def boundary_matrix(rel_by_dim, idx, k):
    """Sparse boundary partial_k : C_k -> C_{k-1} in relative complex.
    Returns list of columns, each column = list of (row, +-1) entries.
    Convention: partial(v_0 < v_1 < ... < v_k) = sum_i (-1)^i (omit v_i).
    Any face whose chain is entirely in Delta_3 (i.e., not in rel_by_dim[k-1])
    is zero in the quotient, so we skip it."""
    if k == 0:
        # In reduced relative complex, every 0-chain has zero boundary
        # (augmentation cell is identified with the basepoint Delta_3).
        return [[] for _ in rel_by_dim[0]]
    cols = []
    lower_idx = idx[k - 1]
    for c in rel_by_dim[k]:
        col = []
        for i in range(len(c)):
            face = c[:i] + c[i + 1:]
            if face in lower_idx:
                col.append((lower_idx[face], (-1) ** i))
        cols.append(col)
    return cols


# -----------------------------------------------------------------------
# 5. Rank over a prime field (sparse Gauss)
# -----------------------------------------------------------------------

def matrix_rank_mod_p(cols, n_rows, p):
    """cols: list of columns, each column = list of (row, coeff) tuples,
    coeffs are integers.  Returns rank mod p."""
    # Convert to dict-of-rows columns
    cols_d = []
    for col in cols:
        d = {}
        for (r, c) in col:
            v = (c % p)
            if v:
                d[r] = (d.get(r, 0) + v) % p
        cols_d.append({r: v for r, v in d.items() if v % p})
    rank = 0
    pivot_row_to_col = {}
    for j, col in enumerate(cols_d):
        # Reduce against existing pivots
        while col:
            r = min(col.keys())
            v = col[r]
            if v % p == 0:
                del col[r]
                continue
            if r in pivot_row_to_col:
                pcol = cols_d[pivot_row_to_col[r]]
                pv = pcol[r]
                # eliminate: col := col - (v * pv^{-1}) * pcol
                pv_inv = pow(pv % p, -1, p)
                factor = (v * pv_inv) % p
                for rr, vv in pcol.items():
                    nv = (col.get(rr, 0) - factor * vv) % p
                    if nv:
                        col[rr] = nv
                    elif rr in col:
                        del col[rr]
            else:
                # New pivot
                # Scale to leading 1 (not required for rank, but tidy)
                pivot_row_to_col[r] = j
                rank += 1
                break
    return rank


def matrix_rank_check(cols, n_rows, primes=(1_000_003, 999_983, 100_003)):
    """Rank via two independent primes; abort if they disagree."""
    ranks = [matrix_rank_mod_p(cols, n_rows, p) for p in primes]
    if len(set(ranks)) > 1:
        raise RuntimeError(f"Rank disagreement across primes {primes}: {ranks}")
    return ranks[0]


# -----------------------------------------------------------------------
# 6. Main
# -----------------------------------------------------------------------

def main():
    t0 = time.time()

    # ---------- enumerate PPF_3 and PPF_4 ------------------------------
    print("[1] Enumerating partial orders on {0,1,2} and {0,1,2,3} ...")
    Pos3 = enumerate_posets(3)
    Pos4 = enumerate_posets(4)
    print(f"    |Pos_3^sub| = {len(Pos3)} (expect 19)")
    print(f"    |Pos_4^sub| = {len(Pos4)} (expect 219)")
    assert len(Pos3) == 19
    assert len(Pos4) == 219

    PPF_3 = make_PPF(3)
    PPF_4 = make_PPF(4)
    print(f"    |PPF_3| = |Pos_3^sub| - 1 (antichain) - 6 (totals) = {len(PPF_3)} (expect 12)")
    print(f"    |PPF_4| = |Pos_4^sub| - 1 (antichain) - 24 (totals) = {len(PPF_4)} (expect 194)")
    assert len(PPF_3) == 12
    assert len(PPF_4) == 194

    # ---------- inclusion image ----------------------------------------
    print(f"[2] Building iota_3 : PPF_3 ↪ PPF_4 ...")
    iota_image = set(iota_3_image(PPF_3))
    assert iota_image.issubset(set(PPF_4)), \
        "iota_3(PPF_3) must be a subset of PPF_4."
    assert len(iota_image) == len(PPF_3), \
        "iota_3 must be injective."
    print(f"    iota_3 injective: |image| = {len(iota_image)}")

    # ---------- build order complexes ---------------------------------
    print("[3] Building order complex chains ...")
    es3, above3 = above_map(PPF_3)
    es4, above4 = above_map(PPF_4)

    chains3 = all_chains_by_dim(es3, above3)
    chains4 = all_chains_by_dim(es4, above4)

    f3 = f_vector(chains3)
    f4 = f_vector(chains4)
    print(f"    f-vector(Delta_3) = {f3}")
    print(f"    f-vector(Delta_4) = {f4}")

    chi3 = reduced_euler(f3)
    chi4 = reduced_euler(f4)
    print(f"    chi-tilde(Delta_3) = {chi3}")
    print(f"    chi-tilde(Delta_4) = {chi4}")

    # ---------- TRIP-WIRE ----------------------------------------------
    # The ticket as written states "chi-tilde(Delta_3) = -2" and
    # "chi-tilde(Delta_4) = +2".  This is INCONSISTENT with the F8'' §4.2
    # table which gives chi-tilde(Delta_n) = (-1)^{n-2}, i.e. -1 at n=3
    # and +1 at n=4.  The +2/-2 figures in the ticket appear to be a
    # transcription of the *Delta(X_n)* Euler chars (cofiber values),
    # NOT the Delta_n values.  We verify against the F8'' §4.2 baseline,
    # which is the canonical source.
    print("\n[4] Trip-wire vs F8'' §4.2 baseline ...")
    expected_chi3 = -1   # F8'' §4.2 row "n=3"
    expected_chi4 = +1   # F8'' §4.2 row "n=4"
    tripwire_pass = (chi3 == expected_chi3 and chi4 == expected_chi4)
    if not tripwire_pass:
        print(f"    *** TRIP-WIRE FAILED ***")
        print(f"    Expected (F8'' §4.2): chi-tilde(Delta_3) = {expected_chi3}, "
              f"chi-tilde(Delta_4) = {expected_chi4}")
        print(f"    Computed:             chi-tilde(Delta_3) = {chi3}, "
              f"chi-tilde(Delta_4) = {chi4}")
        print(f"    Would refute F8'' §4 baseline.  Aborting.")
        sys.exit(2)
    print(f"    Pass: chi-tilde(Delta_3) = {chi3} matches F8'' §4.2 row n=3.")
    print(f"    Pass: chi-tilde(Delta_4) = {chi4} matches F8'' §4.2 row n=4.")

    # Sanity: cofiber Euler chi-tilde(Delta_4/Delta_3) = chi(Delta_4) - chi(Delta_3)
    chi_cofiber_expected = chi4 - chi3
    print(f"    Expected chi-tilde(Delta_4/Delta_3) via additivity = {chi_cofiber_expected} (must be +2).")
    assert chi_cofiber_expected == 2, \
        "Cofiber chi mismatch even before computing Betti — F8'' §4.2 baseline broken."

    # ---------- absolute Betti cross-check (validates rank algorithm) --
    # Compute b_tilde_*(Delta_3) and b_tilde_*(Delta_4) by the same
    # Gauss-rank path used below, and confirm against the F8'' / F1-refined
    # / F2 predictions Delta_3 ≃ S^1 and Delta_4 ≃ S^2.
    print("\n[4b] Absolute Betti cross-check (rank-algorithm validation) ...")
    for label, chains_X in [("Delta_3", chains3), ("Delta_4", chains4)]:
        all_verts = set(v for chain in chains_X[0] for v in chain)
        # Use the same machinery but with empty subcomplex -> absolute complex.
        rel_X, idx_X = relative_chains(chains_X, set())  # nothing in subcomplex
        # For augmented absolute Betti, we need an augmentation map
        # partial_0 : C_0 -> Z sending each vertex to 1.
        max_d = max(rel_X.keys())
        ranks_X = {}
        # partial_0 (augmented) has rank 1 if there are any vertices.
        ranks_X[0] = 1 if rel_X[0] else 0
        for k in range(1, max_d + 1):
            cols = boundary_matrix(rel_X, idx_X, k)
            ranks_X[k] = matrix_rank_check(cols, len(rel_X[k - 1]))
        bettis_X = {}
        # b_tilde_0 = dim C_0 - rank partial_0^aug - rank partial_1
        bettis_X[0] = len(rel_X[0]) - ranks_X[0] - ranks_X.get(1, 0)
        for k in range(1, max_d + 1):
            bettis_X[k] = len(rel_X[k]) - ranks_X[k] - ranks_X.get(k + 1, 0)
        b_tuple = tuple(bettis_X.get(k, 0) for k in range(max_d + 1))
        print(f"    b_tilde_*({label}) = {b_tuple}")
        if label == "Delta_3":
            assert b_tuple[:2] == (0, 1) and all(b == 0 for b in b_tuple[2:]), \
                f"Delta_3 should be ≃ S^1; got {b_tuple}"
            print(f"      OK: matches Delta_3 ≃ S^1.")
        if label == "Delta_4":
            assert b_tuple[:3] == (0, 0, 1) and all(b == 0 for b in b_tuple[3:]), \
                f"Delta_4 should be ≃ S^2; got {b_tuple}"
            print(f"      OK: matches Delta_4 ≃ S^2.")

    # ---------- relative chain complex ---------------------------------
    print("\n[5] Building relative chain complex C_*(Delta_4, Delta_3) ...")
    rel_chains, idx = relative_chains(chains4, iota_image)
    rel_fvec = [len(rel_chains[d]) for d in sorted(rel_chains.keys())]
    print(f"    relative f-vector = {rel_fvec}")

    # Cross-check: f(rel) = f(Delta_4) - f(Delta_3)
    fvec_diff = [f4[d] - (f3[d] if d < len(f3) else 0)
                 for d in range(len(f4))]
    print(f"    expected (f4 - f3) = {fvec_diff}")
    assert rel_fvec == fvec_diff, \
        f"Relative f-vector mismatch: {rel_fvec} vs {fvec_diff}"

    chi_rel = sum((-1) ** k * rel_fvec[k] for k in range(len(rel_fvec)))
    # Note: chi-tilde for the relative complex (= reduced of the cofiber) is
    # the non-augmented alternating sum of the relative f-vector — there is
    # no -1 augmentation in the relative complex because the augmentation
    # cell ∅ is in Delta_3 (and collapses to the basepoint).
    print(f"    chi-tilde(Delta_4/Delta_3) = sum (-1)^k f_k^rel = {chi_rel}")
    assert chi_rel == 2, \
        f"Cofiber chi-tilde = {chi_rel}, expected +2.  Cofiber LES inconsistency."

    # ---------- compute boundary maps and ranks ------------------------
    print("\n[6] Computing boundary maps and ranks (mod-p, two primes) ...")
    max_dim = max(rel_chains.keys())
    print(f"    max relative dim = {max_dim}")

    # boundary_k : C_k -> C_{k-1}
    boundaries = {}
    for k in range(max_dim + 1):
        if k == 0:
            # In reduced/relative complex, partial_0 = 0 (vertices in
            # Delta_4 \ Delta_3 do not augment).
            boundaries[k] = [[] for _ in rel_chains[0]]
        else:
            boundaries[k] = boundary_matrix(rel_chains, idx, k)

    ranks = {}
    for k in range(max_dim + 1):
        n_rows = len(rel_chains[k - 1]) if k > 0 else 1  # k=0: into Z augmentation? but we set it 0
        cols = boundaries[k]
        n_cols = len(cols)
        r = matrix_rank_check(cols, n_rows)
        ranks[k] = r
        print(f"    rank(partial_{k}) = {r}  (C_{k} dim = {n_cols})")

    # b_k = dim C_k - rank partial_k - rank partial_{k+1}
    print("\n[7] Reduced Betti numbers of relative complex:")
    bettis = {}
    for k in range(max_dim + 1):
        ck = len(rel_chains[k])
        rk = ranks[k]
        rkp1 = ranks.get(k + 1, 0)
        bettis[k] = ck - rk - rkp1
        print(f"    b_{k} = {ck} - {rk} - {rkp1} = {bettis[k]}")

    # Augmented vs reduced: b_0 here is the *unreduced* H_0 of the
    # relative complex, which is already the reduced H_0 of the cofiber
    # (since the basepoint Delta_3 → pt lives outside the C_0 dimension
    # of the quotient).  No further shift.

    # ---------- Euler cross-check -------------------------------------
    chi_from_bettis = sum((-1) ** k * bettis[k] for k in range(max_dim + 1))
    print(f"\n    chi check: sum (-1)^k b_k = {chi_from_bettis} (must equal {chi_rel})")
    assert chi_from_bettis == chi_rel, \
        "Betti numbers do not match Euler characteristic — RANK CALCULATION BUG."

    # ---------- Verdict ------------------------------------------------
    print("\n[8] Verdict:")
    b_vec = tuple(bettis.get(k, 0) for k in range(4))
    print(f"    (b_0, b_1, b_2, b_3) = {b_vec}")
    print(f"    b_tilde_0 = {b_vec[0]}  -- the F8''' discriminating signal")
    print()
    if b_vec == (0, 0, 2, 0):
        verdict = "GREEN-wedge"
        meaning = ("Delta(X_4) ≃ ∨₂ S^2 (F8''-1 wedge conjecture). "
                   "X_n is path-connected; the two spheres come from a "
                   "single wedge point.")
    elif b_vec == (1, 0, 1, 0):
        verdict = "GREEN-layer"
        meaning = ("X_4 = X_4^↓ ⊔ X_4^↑ (F8''-2 layer conjecture). "
                   "X_n is disconnected into two pieces, each "
                   "contributing one S^2 component.")
    elif sum((-1) ** k * b_vec[k] for k in range(4)) == 2:
        verdict = "AMBER-other"
        meaning = ("Cofiber chi-tilde matches +2 but Betti vector "
                   "does not match either F8''-1 (wedge) or F8''-2 (layer) "
                   "minimal-complexity shape.  F8'' §5 conjecture set "
                   "incomplete; a third homotopy type fits the +2 "
                   "constraint and must be added.")
    else:
        verdict = "RED-foil"
        meaning = ("Cofiber chi-tilde = " + str(chi_from_bettis) +
                   " ≠ +2.  REFUTES F8'' §4.2 cofiber LES; "
                   "F8'' re-audit warranted.")
    print(f"    Verdict tag: {verdict}")
    print(f"    Meaning: {meaning}")

    print(f"\n[done] runtime: {time.time()-t0:.2f} s")

    # ---------- Machine-readable summary -------------------------------
    print("\n----- MACHINE SUMMARY -----")
    print(f"PPF_3_size={len(PPF_3)}")
    print(f"PPF_4_size={len(PPF_4)}")
    print(f"f_Delta_3={f3}")
    print(f"f_Delta_4={f4}")
    print(f"chi_Delta_3={chi3}")
    print(f"chi_Delta_4={chi4}")
    print(f"f_rel={rel_fvec}")
    print(f"chi_rel={chi_rel}")
    print(f"betti_rel={list(b_vec)}")
    print(f"verdict={verdict}")
    print("----- END SUMMARY -----")


if __name__ == "__main__":
    main()
