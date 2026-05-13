#!/usr/bin/env python3
r"""
posn_wedge_check_n5.py
======================

Extends mg-bbf7's posn_wedge_check.py to n=5 with three additions
(per cat-mg-3a61, Daniel program 2026-05-13):

  1. n=5 enumeration via incremental cover-addition (faster than 2^20
     brute force; reproduces the n<=4 numbers from mg-bbf7).
  2. CL-labeling by added cover relation: assigns each cover P -> P'
     in PPF_n the unique pair (a,b) added; counts maximal chains by
     descent count (rising / falling under lex order on labels).
  3. Falling-chain enumeration vs. mod-p Betti cross-check.

Plus optional pure-vs-nonpure analysis: prints rank distribution of
maximal elements of PPF_n and verifies all maximal chains have the
same length (purity).

Output for each n in {3, 4, 5}:
  - |PPF_n|, |Pos_n^sub|, dim Delta(PPF_n)
  - f-vector
  - reduced Euler characteristic
  - Mobius cross-check (Philip Hall)
  - mod-p Betti via streaming sparse Gauss (with --betti)
  - pure/nonpure verdict
  - CL-labeling: # rising max chains, # falling, decomposition by
    falling-prefix length
  - falling-chain count by chain length (Bjorner-Wachs spheres)

The pure-Python implementation runs on stdlib only.

Usage:
    python3 posn_wedge_check_n5.py [n] [--betti] [--prime PRIME] [--cl]

References:
- mg-bbf7 docs/compatibility-geometry-site-refinement-scoping.md
- mg-bbf7 scripts/posn_wedge_check.py (the n<=4 baseline)
- mg-d60d docs/compatibility-geometry-poset-cohomology-scoping.md
- mg-296d docs/compatibility-geometry-eigensheaves-scoping.md
- Bjorner-Wachs, "Shellable nonpure complexes I, II", Trans AMS 348/349.
- Wachs, "Poset topology" survey 2007.
- OEIS A001035: 1, 1, 3, 19, 219, 4231, 130023, ...
"""

import sys
import time


# --------------------------------------------------------------------------
# 1. Enumerate labeled partial orders on [n] by incremental cover-addition.
# --------------------------------------------------------------------------

def transitive_closure(rel, n):
    """Floyd-Warshall closure of a strict relation. Returns frozenset."""
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


def enumerate_partial_orders_incremental(n):
    """All labeled strict partial orders on [n], built by BFS over
    cover-additions from the antichain. Faster than 2^{n(n-1)} brute
    force at n=5 (4231 posets in seconds vs minutes)."""
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
                    closed = transitive_closure(new_rel, n)
                    if any((j, i) in closed for (i, j) in closed):
                        continue
                    if closed not in seen:
                        seen.add(closed)
                        new_frontier.add(closed)
        frontier = new_frontier
    return list(seen)


def is_chain_poset(rel, n):
    return len(rel) == n * (n - 1) // 2


# --------------------------------------------------------------------------
# 2. Refinement-order infrastructure: cover graph, chain DP, pure check.
# --------------------------------------------------------------------------

def build_cover_graph(elements):
    """Return (sorted elems, strictly_above, covers).

    strictly_above[P] = list of all Q with P < Q (subset, strict).
    covers[P] = list of (Q, added) where Q covers P (i.e. no R with P<R<Q)
                and added = (a,b) is the unique cover relation added.
    """
    es = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    strictly_above = {P: [] for P in es}
    es_set = set(es)
    for P in es:
        for Q in es:
            if P != Q and P < Q:
                strictly_above[P].append(Q)
    covers = {P: [] for P in es}
    for P in es:
        # Q covers P iff Q > P and no R with P<R<Q (i.e. rank(Q) = rank(P) + 1
        # in the refinement lattice; equivalently, Q is obtained from P by
        # adding exactly one cover relation modulo TC).
        for Q in strictly_above[P]:
            # Test no intermediate R in our set.
            intermediate = False
            for R in strictly_above[P]:
                if R == Q:
                    continue
                if R < Q:
                    intermediate = True
                    break
            if not intermediate:
                # Compute the added cover relation: covers in Q's Hasse minus
                # covers already implied by P.
                added = find_added_cover(P, Q)
                covers[P].append((Q, added))
    return es, strictly_above, covers


def find_added_cover(P, Q):
    """For a cover P -> Q in the refinement lattice, return the unique
    pair (a, b) such that Q = transitive closure of P union {(a,b)}.

    The pair (a, b) is the lex-smallest minimal element of (Q \\ P) that
    is a cover relation in Q's Hasse diagram and is NOT implied by P."""
    diff = Q - P
    if not diff:
        return None
    n = max(max(i, j) for (i, j) in Q | P) + 1 if (Q | P) else 0
    # Find the cover relations in Q's Hasse diagram.
    # A pair (a,b) in Q is a cover iff no c with (a,c) in Q and (c,b) in Q.
    Q_set = set(Q)
    for (a, b) in sorted(diff):
        is_cover_in_Q = True
        for c in range(n):
            if c == a or c == b:
                continue
            if (a, c) in Q_set and (c, b) in Q_set:
                is_cover_in_Q = False
                break
        if not is_cover_in_Q:
            continue
        # And (a,b) should not be in P (already guaranteed by diff).
        # Verify Q = TC(P ∪ {(a,b)}).
        if transitive_closure(P | {(a, b)}, n) == Q:
            return (a, b)
    # Fallback: lex-smallest pair in diff (shouldn't happen if cover
    # graph is correct).
    return min(diff)


def count_chains_by_length(elements, strictly_above, max_len=None):
    """f-vector: f_k = # strict chains of length k+1."""
    by_rank = sorted(elements, key=lambda P: -len(P))
    cnt = {P: 1 for P in elements}
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
    return -1 + sum((-1) ** k * f_vec[k] for k in range(len(f_vec)))


def maximal_chain_lengths(elements, covers):
    """Return dict P -> length of longest cover-chain from P upward.
    Use to test purity: max chain lengths from minimal elements all equal?"""
    by_rank = sorted(elements, key=lambda P: -len(P))
    longest = {}
    shortest = {}
    for P in by_rank:
        if not covers[P]:
            longest[P] = 0
            shortest[P] = 0
        else:
            longest[P] = 1 + max(longest[Q] for (Q, _) in covers[P])
            shortest[P] = 1 + min(shortest[Q] for (Q, _) in covers[P])
    minimal = [P for P in elements if all(P not in covers[Q] or True for Q in elements)]
    # Easier characterization of minimal: P is minimal iff no Q has P among its covers' targets.
    has_predecessor = set()
    for P in elements:
        for (Q, _) in covers[P]:
            has_predecessor.add(Q)
    minimal = [P for P in elements if P not in has_predecessor]
    return minimal, longest, shortest


def pure_check(elements, covers):
    """Return (pure, sample_long, sample_short, lengths_dict).

    pure iff all minimal elements P satisfy longest[P] == shortest[P]
    AND that common value is the same across all minimal elements.
    """
    minimal, longest, shortest = maximal_chain_lengths(elements, covers)
    if not minimal:
        return True, 0, 0, {}
    lens = set()
    for P in minimal:
        lens.add(longest[P])
        lens.add(shortest[P])
    pure = (len(lens) == 1)
    return pure, max(lens), min(lens), {"minimal": len(minimal),
                                          "longest_min_to_max": max(longest[P] for P in minimal),
                                          "shortest_min_to_max": min(shortest[P] for P in minimal)}


# --------------------------------------------------------------------------
# 3. Mobius function of the augmented lattice (Philip Hall cross-check).
# --------------------------------------------------------------------------

def mobius_value_augmented(elements, n):
    r"""Return mu_{hat P}(hat 0, hat 1) where:
      hat 0 = antichain (frozenset())
      hat 1 = formal top above all elements

    By Philip Hall, this equals chi~(Delta(P \ {0,1})).
    """
    antichain = frozenset()
    if antichain not in elements:
        return None
    mu = {antichain: 1}
    by_rank = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
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
    total = sum(mu.values())
    return -total


# --------------------------------------------------------------------------
# 4. Streaming sparse Gauss for Betti numbers (mod p).
# --------------------------------------------------------------------------

def chains_generator(elements, strictly_above, k):
    """Yield strict k-chains of length k as tuples."""
    if k == 0:
        yield ()
        return
    if k == 1:
        for P in elements:
            yield (P,)
        return
    stack = [(P,) for P in elements]
    while stack:
        c = stack.pop()
        if len(c) == k:
            yield c
            continue
        for Q in strictly_above[c[-1]]:
            stack.append(c + (Q,))


def chains_int_generator(elem_index, strictly_above_int, k):
    """Yield strict k-chains as tuples of int indices."""
    if k == 0:
        yield ()
        return
    if k == 1:
        for i in range(len(elem_index)):
            yield (i,)
        return
    stack = [(i,) for i in range(len(elem_index))]
    while stack:
        c = stack.pop()
        if len(c) == k:
            yield c
            continue
        for j in strictly_above_int[c[-1]]:
            stack.append(c + (j,))


def boundary_rank_streaming(elem_index, strictly_above_int, k_dim, prev_idx, p):
    """Compute rank of d_{k_dim}: C_{k_dim} -> C_{k_dim - 1} mod p.

    elem_index: list of elements (indexed 0..N-1).
    strictly_above_int[i]: list of int indices j with elem[i] < elem[j].
    prev_idx: dict mapping (k_dim)-chain tuple of ints -> row index
              (for the boundary's codomain C_{k_dim-1}; chains have length k_dim).

    Streams k_dim+1-chains as columns; uses prev_idx for face indexing.
    """
    pivots = {}
    rank = 0
    inv_cache = {}
    for simplex in chains_int_generator(elem_index, strictly_above_int, k_dim + 1):
        col = {}
        for i in range(len(simplex)):
            face = simplex[:i] + simplex[i + 1:]
            ri = prev_idx[face]
            sign = 1 if (i % 2 == 0) else (p - 1)
            col[ri] = (col.get(ri, 0) + sign) % p
        col = {r: v for r, v in col.items() if v}
        while col:
            shared = None
            for r in col:
                if r in pivots:
                    shared = r
                    break
            if shared is None:
                break
            pc = pivots[shared]
            pv = pc[shared]
            if pv not in inv_cache:
                inv_cache[pv] = pow(pv, -1, p)
            coef = (col[shared] * inv_cache[pv]) % p
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


def mod_p_rank_streaming(col_iter, p):
    """Sparse Gauss: keep only pivots in memory, reduce each col."""
    pivots = {}
    rank = 0
    for col in col_iter:
        col = {r: v % p for r, v in col.items() if v % p != 0}
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


def betti_mod_p(by_chains_per_k, p, max_k):
    """Reduced Betti numbers mod p via boundary-rank sandwich."""
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
        ranks[k] = mod_p_rank_streaming(cols_iter(), p)
    bettis = {}
    for k in range(-1, max_k + 1):
        bettis[k] = sizes.get(k, 0) - ranks.get(k, 0) - ranks.get(k + 1, 0)
    return bettis, ranks, sizes


# --------------------------------------------------------------------------
# 5. CL-labeling: enumerate maximal cover-chains and label by added pair.
# --------------------------------------------------------------------------

def enumerate_max_cover_chains(elements, covers):
    """Yield maximal cover-chains as lists of (P, added) tuples.

    Maximal = starts at a minimal element of the cover graph, ends at a
    maximal element. Each step is a cover (rank +1)."""
    has_predecessor = set()
    for P in elements:
        for (Q, _) in covers[P]:
            has_predecessor.add(Q)
    minimal = [P for P in elements if P not in has_predecessor]
    for start in minimal:
        # DFS from start
        stack = [(start, [], 0)]
        while stack:
            P, label_seq, depth = stack.pop()
            if not covers[P]:
                yield (start, label_seq)
                continue
            for (Q, added) in covers[P]:
                stack.append((Q, label_seq + [added], depth + 1))


def label_descents(label_seq):
    """Count descents in lex order: # i with label_seq[i] > label_seq[i+1]."""
    count = 0
    for i in range(len(label_seq) - 1):
        if label_seq[i] > label_seq[i + 1]:
            count += 1
    return count


def is_falling(label_seq):
    """A 'falling chain' (Bjorner-Wachs sense): at least one descent."""
    return label_descents(label_seq) > 0


def falling_chains_by_length(elements, covers):
    """Enumerate ALL strict chains in the lattice (not just maximal ones)
    that are 'falling' under the lex CL-labeling on covers used along
    the chain. For purposes of falling-chain count vs Bjorner-Wachs
    sphere count.

    Returns a dict {length k -> # falling chains of cover-length k}.
    Counts INCLUDE all chains, not just maximal."""
    by_length = {}
    # DFS over all cover-chains.
    for P in elements:
        stack = [(P, [], [])]   # (current node, label sequence, chain_nodes)
        while stack:
            Q, labels, _nodes = stack.pop()
            if labels and is_falling(labels):
                by_length[len(labels)] = by_length.get(len(labels), 0) + 1
            for (R, added) in covers[Q]:
                stack.append((R, labels + [added], _nodes + [R]))
    return by_length


# --------------------------------------------------------------------------
# 6. Variants: PPF_n = Pos_n^sub \ {antichain, totals}
# --------------------------------------------------------------------------

def variant_PPF(orders, n):
    return [P for P in orders
            if P != frozenset() and not is_chain_poset(P, n)]


# --------------------------------------------------------------------------
# 7. Reporting.
# --------------------------------------------------------------------------

def run_PPF(name, elements, n, do_betti, prime, do_cl, betti_cap=None):
    print(f"\n=== {name} ===")
    print(f"  underlying set size: {len(elements)}")
    if not elements:
        print("  empty -- nothing to compute.")
        return
    t0 = time.time()
    elems_list, strictly_above, covers = build_cover_graph(elements)
    print(f"  cover graph built in {time.time()-t0:.1f}s")

    f_vec = count_chains_by_length(elems_list, strictly_above)
    print(f"  dim Delta            = {len(f_vec) - 1}")
    print(f"  f-vector             = {f_vec}")
    chi_tilde = reduced_euler_from_fvector(f_vec)
    print(f"  reduced Euler chi~   = {chi_tilde}")

    # Mobius cross-check on the augmented lattice (re-add antichain)
    all_orders = set(elements)
    all_orders.add(frozenset())
    mu_aug = mobius_value_augmented(all_orders, n)
    if mu_aug is not None:
        print(f"  Mobius mu(0_hat, 1_hat) = {mu_aug}  (Philip Hall: must equal chi~)")
        if mu_aug != chi_tilde:
            print(f"    *** Mobius/Euler disagree! Investigate. ***")

    # Pure / nonpure
    pure, longest_max, shortest_min, info = pure_check(elements, covers)
    print(f"  pure (all max cover-chains same length)? {pure}")
    print(f"    minimal elements: {info.get('minimal', '?')}")
    print(f"    longest min->max: {info.get('longest_min_to_max', '?')}")
    print(f"    shortest min->max: {info.get('shortest_min_to_max', '?')}")

    if do_cl:
        # CL-labeling: enumerate max cover-chains and report descent stats.
        t0 = time.time()
        all_maxchains = list(enumerate_max_cover_chains(elements, covers))
        print(f"  enumerated {len(all_maxchains)} max cover-chains in {time.time()-t0:.1f}s")
        # Descent histogram
        hist = {}
        for (_, lbls) in all_maxchains:
            d = label_descents(lbls)
            hist[d] = hist.get(d, 0) + 1
        print(f"  descent histogram (# max chains with d descents):")
        for d in sorted(hist):
            print(f"    d={d}: {hist[d]}")
        rising = hist.get(0, 0)
        print(f"  # rising (d=0) max chains: {rising}")
        falling = sum(v for d, v in hist.items() if d > 0)
        print(f"  # falling (d>=1) max chains: {falling}")

        # Falling-chain count by length (Bjorner-Wachs sphere proxy).
        t0 = time.time()
        fall_by_len = falling_chains_by_length(elements, covers)
        print(f"  falling subchains by length (in {time.time()-t0:.1f}s):")
        for k in sorted(fall_by_len):
            print(f"    length {k}: {fall_by_len[k]}")

    if do_betti:
        # Use int-encoded chains for memory efficiency at n=5.
        elem_to_int = {P: i for i, P in enumerate(elems_list)}
        strictly_above_int = [[elem_to_int[Q] for Q in strictly_above[P]]
                              for P in elems_list]
        # Determine max_k we attempt; can be capped via --max-betti-dim
        max_k = len(f_vec) - 1
        if betti_cap is not None and betti_cap < max_k:
            max_k = betti_cap
        print(f"  computing Betti up to dim {max_k}...")
        # Compute boundary ranks rank_k = rank(d_k: C_k -> C_{k-1}) for k = 1..max_k+1
        # Need indexing of (k)-chains as we compute rank(d_{k+1}).
        # Sizes from f_vec.
        sizes = {-1: 1}
        for k in range(len(f_vec)):
            sizes[k] = f_vec[k]
        ranks = {0: 1 if sizes[0] > 0 else 0}
        for k in range(1, max_k + 2):
            if k > len(f_vec):
                ranks[k] = 0
                continue
            # rank(d_k): C_k -> C_{k-1}.  k-chains have length k+1 in our convention
            # Wait: f_k counts chains of LENGTH k+1 (k+1 nodes), so f_k corresponds to
            # k-simplices.  Boundary d_k goes from k-simplices (chains of length k+1)
            # to (k-1)-simplices (chains of length k).
            # We need prev_idx: chains of length k -> int index.
            if k - 1 == 0:
                # vertices: chains of length 1
                prev_idx = {(i,): i for i in range(len(elems_list))}
            else:
                t1 = time.time()
                prev_idx = {}
                idx = 0
                for c in chains_int_generator(elems_list, strictly_above_int, k):
                    prev_idx[c] = idx
                    idx += 1
                print(f"    enumerated {idx} (k-1={k-1})-simplices for d_{k} indexing in {time.time()-t1:.1f}s")
            t1 = time.time()
            r = boundary_rank_streaming(elems_list, strictly_above_int, k, prev_idx, prime)
            ranks[k] = r
            print(f"    rank(d_{k}) = {r}  (in {time.time()-t1:.1f}s)")
            del prev_idx
        # Compute reduced Betti.
        print(f"  ranks: {ranks}")
        bettis = {}
        for k in range(0, max_k + 1):
            bettis[k] = sizes.get(k, 0) - ranks.get(k, 0) - ranks.get(k + 1, 0)
        b_str = ", ".join(f"b~_{k}={bettis[k]}" for k in range(max_k + 1))
        print(f"  reduced Betti mod {prime} (k=0..{max_k}): {b_str}")
        # Euler-constraint check for higher Betti.
        partial_chi = sum((-1) ** k * bettis[k] for k in range(max_k + 1))
        if max_k < len(f_vec) - 1:
            remainder = chi_tilde - partial_chi
            print(f"  Euler residue for unknown b~_{max_k+1}..b~_{len(f_vec)-1}: "
                  f"sum (-1)^k b~_k = {remainder}")
        nonzero = [(k, bettis[k]) for k in range(max_k + 1) if bettis[k] != 0]
        if len(nonzero) == 1 and max_k == len(f_vec) - 1:
            (k, b) = nonzero[0]
            print(f"  ==>  Delta ~ {'wedge of '+str(b)+' copies of S^'+str(k) if b > 1 else 'S^'+str(k)}")
        elif not nonzero and max_k == len(f_vec) - 1:
            print("  ==>  Delta is acyclic over GF(p)")
        elif nonzero:
            ds = ", ".join(f"{b} x S^{k}" for (k, b) in nonzero)
            print(f"  ==>  Delta has at least: {ds}")


def site_table(n, do_betti, prime, do_cl, betti_cap):
    print(f"\n========== n = {n}  ==========")
    print("Enumerating partial orders (incremental BFS)...")
    t0 = time.time()
    orders = enumerate_partial_orders_incremental(n)
    print(f"|Pos_{n}^sub| = {len(orders)}  (OEIS A001035)  in {time.time()-t0:.1f}s")
    run_PPF(f"PPF_{n} (LE-removed proper part)", variant_PPF(orders, n),
            n, do_betti, prime, do_cl, betti_cap)


if __name__ == "__main__":
    args = sys.argv[1:]
    n = 5
    do_betti = False
    do_cl = False
    prime = 1000003
    betti_cap = None
    if args and args[0].isdigit():
        n = int(args[0])
        args = args[1:]
    while args:
        a = args.pop(0)
        if a == "--betti":
            do_betti = True
        elif a == "--cl":
            do_cl = True
        elif a == "--prime":
            prime = int(args.pop(0))
        elif a == "--max-betti-dim":
            betti_cap = int(args.pop(0))
        else:
            print(f"Unknown arg {a}", file=sys.stderr)
            sys.exit(2)
    for small in [3, 4]:
        if small <= n:
            site_table(small, do_betti, prime, do_cl, betti_cap)
    if n >= 5:
        site_table(n, do_betti, prime, do_cl, betti_cap)
    print("\nDone.")
