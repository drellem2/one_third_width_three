#!/usr/bin/env python3
r"""
posn_wedge_check.py
===================

Computes the homotopy/homology type of the order complex of the
refinement lattice Pos_n^sub on [n], under several site refinements
proposed in `docs/compatibility-geometry-site-refinement-scoping.md`:

  V0  baseline:        Pos_n^sub \ {antichain}            (mg-d60d "proper part")
  V1  inversion:       same simplicial complex            (order complex of P^op = order complex of P)
  V2  LE removal:      Pos_n^sub \ {antichain, totals}
  V3  inversion + LE:  same simplicial complex as V2

Output for each variant:
  - |Pos|, f-vector (count of nonempty strict chains by length), reduced
    Euler chi (from f-vector and cross-checked via the Mobius function of
    the augmented lattice; Philip Hall's theorem)
  - For small enough cases: Betti numbers over GF(p) (a "generic"
    surrogate for rational Betti) via sparse mod-p Gaussian elimination
  - A wedge-of-spheres reading when Betti vector permits it.

The pure-Python implementation runs on stdlib only (no SageMath
required). For n=4 the homology computation is at the edge of
tractability and may be omitted by default; pass --betti to attempt it.
The equivalent SageMath one-liner is:

    sage: L = Poset((labelled_partial_orders(n), lambda P, Q: P <= Q))
    sage: L.order_complex().homology()   # bounded lattices auto-strip 0/1

References:
- mg-5ee2 §3.2 (Euler = -1 for n=3, refutes single S^2)
- mg-d60d §3.3 (proper-part removal of cone points)
- mg-296d §1.1 (Pos_n^sub category setup)
- Bjorner-Wachs, "Poset topology" survey 2007
- OEIS A001035: 1, 1, 3, 19, 219, 4231, ...
- OEIS A006455 (refinement lattice maximal-chain counts)

Usage:
    python3 posn_wedge_check.py [n] [--betti] [--prime PRIME]
"""

import sys


# --------------------------------------------------------------------------
# 1. Enumerate labeled partial orders on [n].
# --------------------------------------------------------------------------

def transitive_closure(rel, n):
    """Floyd-Warshall-style closure of a strict relation."""
    closed = set(rel)
    changed = True
    while changed:
        changed = False
        new_pairs = []
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    new_pairs.append((i, l))
        if new_pairs:
            closed.update(new_pairs)
            changed = True
    return frozenset(closed)


def enumerate_partial_orders(n):
    """All labeled strict partial orders on [n], as frozensets of (i,j) with i<_P j.

    Brute force; only feasible up to n<=5. For n=4: ~100ms, returns 219 posets.
    """
    pairs = [(i, j) for i in range(n) for j in range(n) if i != j]
    m = len(pairs)
    results = []
    for bits in range(1 << m):
        rel = frozenset(pairs[k] for k in range(m) if (bits >> k) & 1)
        closed = transitive_closure(rel, n)
        if closed != rel:
            continue
        if any((j, i) in closed for (i, j) in closed):
            continue
        results.append(rel)
    return results


def is_chain_poset(rel, n):
    """True iff rel is a total order on [n]."""
    return len(rel) == n * (n - 1) // 2


# --------------------------------------------------------------------------
# 2. Refinement-order infrastructure: covers and chain counts via DP.
# --------------------------------------------------------------------------

def build_refinement_order(elements):
    """Return dict elem -> sorted list of all strictly-greater elements."""
    es = list(elements)
    es.sort(key=lambda P: (len(P), tuple(sorted(P))))
    strictly_above = {P: [] for P in es}
    for P in es:
        for Q in es:
            if P != Q and P < Q:    # frozenset subset
                strictly_above[P].append(Q)
    return es, strictly_above


def count_chains_by_length(elements, strictly_above, max_len=None):
    """Return f-vector f_0, f_1, ... where f_k = # chains of length k+1.

    Uses DP: cnt[k][P] = number of chains of length k+1 starting at P
    going strictly upward. Then f_k = sum over P of cnt[k][P].
    """
    # Process elements in reverse rank so that "strictly_above" entries are
    # already populated in cnt.
    by_rank = sorted(elements, key=lambda P: -len(P))
    cnt = {P: 1 for P in elements}     # cnt[0] for all P
    f_vec = [len(elements)]
    k = 0
    while True:
        new_cnt = {P: 0 for P in elements}
        for P in by_rank:
            total = 0
            for Q in strictly_above[P]:
                total += cnt[Q]
            new_cnt[P] = total
        s = sum(new_cnt.values())
        if s == 0:
            break
        f_vec.append(s)
        cnt = new_cnt
        k += 1
        if max_len is not None and k >= max_len:
            break
    return f_vec


def reduced_euler_from_fvector(f_vec):
    """chi~ = -1 + f_0 - f_1 + f_2 - ..."""
    return -1 + sum((-1) ** k * f_vec[k] for k in range(len(f_vec)))


# --------------------------------------------------------------------------
# 3. Mobius function of the augmented refinement lattice (Philip Hall cross-check).
# --------------------------------------------------------------------------

def mobius_value_augmented(elements, n):
    r"""Return mu_{hat P}(hat 0, hat 1) where:
      hat 0 = antichain (frozenset()) -- assumed to be in `elements`
      hat 1 = formal top above all elements

    By Philip Hall, this equals chi~(Delta(P \ {0,1})) for the proper part
    of the bounded lattice.
    """
    antichain = frozenset()
    # If antichain is not in elements, mu is computed on a different lattice; abort.
    if antichain not in elements:
        return None
    mu = {antichain: 1}
    # Process in order of increasing rank.
    by_rank = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    # mu(0, P) for P > 0:
    for P in by_rank:
        if P == antichain:
            continue
        s = 0
        for Q in by_rank:
            if Q == P:
                break
            if Q < P:
                s += mu[Q]
        mu[P] = -s
    # mu(0, hat 1) = - sum over P != hat 1 of mu(0, P)
    total = sum(mu.values())
    return -total


# --------------------------------------------------------------------------
# 4. Betti numbers via mod-p Gauss on the augmented chain complex.
# --------------------------------------------------------------------------

def chains_generator(elements, strictly_above, k):
    """Yield k-chains (P_0, ..., P_{k-1}) of length k as tuples."""
    if k == 0:
        yield ()
        return
    if k == 1:
        for P in elements:
            yield (P,)
        return
    # Use DFS to generate chains of length k.
    stack = [(P,) for P in elements]
    while stack:
        c = stack.pop()
        if len(c) == k:
            yield c
            continue
        for Q in strictly_above[c[-1]]:
            stack.append(c + (Q,))


def mod_p_rank_streaming(col_iter, p):
    """Rank mod p of a sparse matrix presented as an iterator of columns.

    Each column is a dict {row: val mod p}. Only the pivot columns are kept
    in memory; non-pivot columns are reduced to zero and discarded.
    """
    pivots = {}     # pivot_row -> column dict {row: val} (with leading pivot at `pivot_row`)
    rank = 0
    for col in col_iter:
        col = {r: v % p for r, v in col.items() if v % p != 0}
        # Reduce by all existing pivots.
        # Loop: find a row in col that is already a pivot row, eliminate.
        # We do this until no shared rows remain.
        while col:
            shared = None
            for r in col:
                if r in pivots:
                    shared = r
                    break
            if shared is None:
                break
            pc = pivots[shared]
            coef = (col[shared] * pow(pc[shared], -1, p)) % p
            for rr, vv in pc.items():
                nv = (col.get(rr, 0) - coef * vv) % p
                if nv:
                    col[rr] = nv
                else:
                    col.pop(rr, None)
        if col:
            r = next(iter(col))
            pivots[r] = col
            rank += 1
    return rank


def betti_mod_p(by_chains_per_k, n_minus_1_chain_count, p, max_k):
    """Compute Betti numbers via mod-p rank of boundary maps on the augmented complex.

    by_chains_per_k[k] : list of chains of length k+1 (the k-simplices).
    Augmentation: C_{-1} = GF(p), with d_0(P) = 1 for any vertex P.
    """
    sizes = {-1: 1}
    for k in range(max_k + 1):
        sizes[k] = len(by_chains_per_k.get(k, []))

    ranks = {}
    for k in range(0, max_k + 1):
        cur = by_chains_per_k.get(k, [])
        if not cur or sizes[k - 1] == 0:
            ranks[k] = 0
            continue
        if k == 0:
            ranks[0] = 1
            continue
        prev_idx = {tuple(s): i for i, s in enumerate(by_chains_per_k[k - 1])}

        def cols_iter():
            for simplex in cur:
                col = {}
                for i in range(len(simplex)):
                    face = simplex[:i] + simplex[i + 1:]
                    ri = prev_idx[tuple(face)]
                    col[ri] = ((-1) ** i) % p
                yield col
        rk = mod_p_rank_streaming(cols_iter(), p)
        ranks[k] = rk

    bettis = {}
    for k in range(-1, max_k + 1):
        rk = ranks.get(k, 0)
        rkp1 = ranks.get(k + 1, 0)
        bettis[k] = sizes.get(k, 0) - rk - rkp1
    # Convert reduced (augmented) Betti to actual reduced Betti:
    # the augmented complex has b~_k = dim H~_k.
    return bettis, ranks, sizes


# --------------------------------------------------------------------------
# 5. Variants and reporting.
# --------------------------------------------------------------------------

def variant_V0(orders, n):
    return [P for P in orders if P != frozenset()]


def variant_V2(orders, n):
    return [P for P in orders if P != frozenset() and not is_chain_poset(P, n)]


def run_variant(name, elements, n, do_betti, prime):
    print(f"\n{name}")
    print(f"  underlying set size: {len(elements)}")
    if not elements:
        print("  empty -- nothing to compute.")
        return
    elems_list, strictly_above = build_refinement_order(elements)
    f_vec = count_chains_by_length(elems_list, strictly_above)
    print(f"  dim Delta            = {len(f_vec) - 1}")
    print(f"  f-vector             = {f_vec}")
    chi_tilde = reduced_euler_from_fvector(f_vec)
    print(f"  reduced Euler chi~   = {chi_tilde}")

    mu = mobius_value_augmented(set(elements) | {frozenset()}, n)
    if mu is not None:
        # Add antichain back and recompute mu in the same lattice
        all_orders = set(elements)
        all_orders.add(frozenset())
        mu_aug = mobius_value_augmented(all_orders, n)
        print(f"  Mobius mu(0_hat, 1_hat) = {mu_aug}  (Philip Hall: must equal chi~)")
        if mu_aug != chi_tilde:
            print(f"    *** Mobius/Euler disagree! Investigate. ***")

    if do_betti:
        max_k = len(f_vec) - 1
        # Generate chains
        print(f"  enumerating chains for Betti...")
        by_k = {}
        for k in range(max_k + 1):
            by_k[k] = list(chains_generator(elems_list, strictly_above, k + 1))
            print(f"    f_{k} chains enumerated: {len(by_k[k])}")
        bettis, ranks, sizes = betti_mod_p(by_k, None, prime, max_k)
        b_str = ", ".join(f"b~_{k}={bettis[k]}" for k in range(max_k + 1))
        print(f"  reduced Betti mod {prime}: {b_str}")

        # Wedge reading
        nonzero = [(k, bettis[k]) for k in range(max_k + 1) if bettis[k] != 0]
        if len(nonzero) == 1:
            (k, b) = nonzero[0]
            print(f"  ==>  Delta ~ wedge of {b} copies of S^{k}"
                  if b > 1 else f"  ==>  Delta ~ S^{k}")
        elif not nonzero:
            print("  ==>  Delta is acyclic over GF(p)")
        else:
            ds = ", ".join(f"{b} x S^{k}" for (k, b) in nonzero)
            print(f"  ==>  Delta ~ mixed wedge: {ds}")


def site_table(n, do_betti, prime):
    print(f"\n========== n = {n}  ==========")
    print("Enumerating partial orders...")
    orders = enumerate_partial_orders(n)
    print(f"|Pos_{n}^sub| = {len(orders)}  (OEIS A001035)")
    run_variant("V0 baseline (proper part of augmented)", variant_V0(orders, n), n, do_betti, prime)
    run_variant("V2 LE removal (no antichain, no totals)",
                variant_V2(orders, n), n, do_betti, prime)


def verify_inversion_topological_identity(orders):
    """Sanity: order complex of P and P^op are equal as simplicial complexes."""
    elem = [P for P in orders if P != frozenset()]
    _, sup_above = build_refinement_order(elem)
    _, sup_below = build_refinement_order(elem)
    # For "Pos^op" we flip the order: strictly_above(P, op) = strictly_below(P, normal)
    for P in elem:
        sup_below[P] = [Q for Q in elem if Q != P and Q < P]
    fwd = count_chains_by_length(elem, sup_above, max_len=5)
    rev = count_chains_by_length(elem, sup_below, max_len=5)
    if fwd != rev:
        print(f"  fwd = {fwd}")
        print(f"  rev = {rev}")
        raise AssertionError("inversion check failed")
    print(f"\nInversion check: f-vectors match between Pos and Pos^op at low n.  OK.")


if __name__ == "__main__":
    args = sys.argv[1:]
    n = 4
    do_betti = False
    prime = 1000003
    if args and args[0].isdigit():
        n = int(args[0])
        args = args[1:]
    while args:
        a = args.pop(0)
        if a == "--betti":
            do_betti = True
        elif a == "--prime":
            prime = int(args.pop(0))
        else:
            print(f"Unknown arg {a}", file=sys.stderr)
            sys.exit(2)

    for small in [2, 3]:
        if small < n:
            site_table(small, do_betti, prime)
    site_table(n, do_betti, prime)
    orders3 = enumerate_partial_orders(3)
    verify_inversion_topological_identity(orders3)
    print("\nDone.")
