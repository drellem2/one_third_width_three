#!/usr/bin/env python3
r"""
compat_geom_F18_ucc2_delta_injective.py
=======================================

Compat-Geom F18 companion script (mg-d039).  Verification harness for the
proof of (UCC.2): the connecting map

    delta_n : H~^{n-2}(Delta_n) -> H~^{n-1}(Delta_{n+1}/Delta_n)

is injective, for every n >= 3, n-uniformly and *unconditionally*.

The proof (docs/compatibility-geometry-F18-ucc2-delta-injective.md)
-------------------------------------------------------------------
By exactness of the cofiber long exact sequence of the pair (Delta_{n+1},
Delta_n),  ker(delta_n) = im(iota_n^*),  so (UCC.2)(n) is equivalent to
iota_n^* = 0 on H~^{n-2}.  F18 proves the strictly stronger statement:

    THE INCLUSION  iota_n : Delta_n  ->  Delta_{n+1}  IS NULL-HOMOTOPIC,

via an explicit poset zig-zag.  Let omega_n := {(n,b) : b in [n]} be the
partial order on [n+1] in which the new element n lies below all of [n]
(and [n] is an internal antichain).  Define

    kappa_n : PPF_n -> PPF_{n+1},   kappa_n(x) = x  u  omega_n

("cone the new element n below everything").  Then, pointwise in PPF_{n+1},

        iota_n(x)  <=  kappa_n(x)  >=  omega_n          (*)

so the order-homotopy lemma gives  |iota_n| ~ |kappa_n| ~ const_{omega_n},
i.e. iota_n is null-homotopic.  Hence iota_n^* = 0 in *all* degrees, hence
delta_n is injective in all degrees -- in particular (UCC.2)(n).  The
argument uses NO hypothesis whatsoever (no Hyp(m), no (UCC), no F17): it is
unconditional, so a fortiori it does not assume Hyp(n+1) (the circularity
guard is satisfied vacuously).

What this script checks (n = 3, 4, 5)
-------------------------------------
  [A] Build PPF_n for n = 3,4,5; assert |PPF_n| = 12, 194, 4110
      (the F1-refined / F14 / F17 convention: nonempty, non-total partial
      orders on [n], ordered by relation-set inclusion).
  [B] omega_n is a proper partial order on [n+1]  (a vertex of Delta_{n+1}).
  [C] kappa_n is well-defined: kappa_n(x) = x u omega_n lies in PPF_{n+1}
      for every x in PPF_n  -- the one combinatorial obligation.
  [D] kappa_n is order-preserving  (x <= x'  =>  kappa_n(x) <= kappa_n(x')).
  [E] the two comparabilities (*): iota_n(x) <= kappa_n(x) and
      omega_n <= kappa_n(x), for every x.
  [F] the explicit homotopy: the prism poset maps
          H  : PPF_n x {0<1} -> PPF_{n+1},  (x,0)|->iota_n(x), (x,1)|->kappa_n(x)
          H' : PPF_n x {0<1} -> PPF_{n+1},  (x,0)|->omega_n,    (x,1)|->kappa_n(x)
      are order-preserving.  Order-preservation of H (resp. H') *is* the
      homotopy iota_n ~ kappa_n (resp. const ~ kappa_n) at that n.
  [G] S_n-equivariance: kappa_n, omega_n and the prism maps H, H' commute
      with the S_n-action (S_n permutes [n], fixes n).  So the whole
      zig-zag, hence the null-homotopy, is S_n-equivariant.
  [H] the chain-level null-homotopy.  D := P' - P is the explicit chain
      null-homotopy of iota_n built from the two prisms; verify the
      identity   dD + Dd = (iota_n)_# - (const)_#   on EVERY simplex of
      Delta_n (exact integer arithmetic).  This certifies that iota_n is
      chain-null-homotopic: for every (n-2)-cycle z, d(Dz) = (iota_n)_#(z),
      so (iota_n)_* = 0 on H~_{n-2}, hence delta_n is injective.  Done at
      n = 3 (reproduces mg-59f3's (UCC.2)@n=3 by the non-circular route)
      and n = 4 (new).
  [I] homology anchor (sanity, not load-bearing): reduced Betti vectors of
      Delta_3, Delta_4 via mod-p boundary ranks; assert (0,1) and (0,0,1)
      -- i.e. Hyp(3), Hyp(4).  Pins that the iota_n we null-homotope is the
      inclusion of the right complexes.
  [J] verdict.

Pure-Python stdlib; runtime a few seconds.  No new axioms; no Lean changes;
no HPC.
"""

import itertools
import sys
import time

sys.setrecursionlimit(1 << 20)

P = 2147483647  # a large prime, for the mod-p homology *anchor* only ([I])


# --------------------------------------------------------------------------
# Partial orders and PPF_n
# --------------------------------------------------------------------------
def _transitively_closed(rel):
    """rel: set of ordered pairs.  Return True iff transitively closed."""
    for (a, b) in rel:
        for (c, d) in rel:
            if b == c and a != d and (a, d) not in rel:
                return False
    return True


def is_proper_partial_order(rel, n):
    """rel a set of ordered pairs on [n]: irreflexive, antisymmetric,
    transitively closed, nonempty, and *non-total* (= proper)."""
    if not rel:
        return False
    for (a, b) in rel:
        if a == b or (b, a) in rel:
            return False
        if not (0 <= a < n and 0 <= b < n):
            return False
    if not _transitively_closed(rel):
        return False
    # non-total: a total order on [n] has exactly C(n,2) related pairs
    if len(rel) >= n * (n - 1) // 2:
        return False
    return True


def all_partial_orders(n):
    """Every partial order on [n], as frozensets of ordered pairs.  Enumerated
    by choosing, for each unordered pair {a<b}, one of {a<b, b<a, incomparable}
    -- 3^C(n,2) candidates -- and keeping the transitively closed ones."""
    pairs = [(a, b) for a in range(n) for b in range(n) if a < b]
    out = []
    for choice in itertools.product((0, 1, 2), repeat=len(pairs)):
        rel = set()
        for c, (a, b) in zip(choice, pairs):
            if c == 1:
                rel.add((a, b))
            elif c == 2:
                rel.add((b, a))
        if _transitively_closed(rel):
            out.append(frozenset(rel))
    return out


def ppf(n):
    """PPF_n: nonempty, non-total partial orders on [n], sorted canonically."""
    tot = n * (n - 1) // 2
    return sorted(
        (p for p in all_partial_orders(n) if 0 < len(p) < tot),
        key=lambda s: (len(s), sorted(s)),
    )


# --------------------------------------------------------------------------
# The F18 maps:  iota_n,  omega_n,  kappa_n
# --------------------------------------------------------------------------
def omega_of(n):
    """omega_n = {(n,b) : b in [n]}: the new element n below all of [n]."""
    return frozenset((n, b) for b in range(n))


def iota(x):
    """iota_n(x): the same relation set, viewed on [n+1] (element n isolated)."""
    return x


def kappa(x, omega):
    """kappa_n(x) = x u omega_n."""
    return frozenset(set(x) | set(omega))


def act(g, rel):
    """Apply a permutation g (a list) to a relation set."""
    return frozenset((g[a], g[b]) for (a, b) in rel)


# --------------------------------------------------------------------------
# Tiny exact-integer simplicial chain arithmetic in Delta_{n+1}
# --------------------------------------------------------------------------
def add_simplex(verts, coeff, chain):
    """Add coeff * [verts] to the chain dict.  verts: list of vertex indices
    (need not be sorted).  Repeated vertex => degenerate => 0.  Stored as a
    sorted tuple with the permutation sign folded into the coefficient."""
    vs = list(verts)
    if len(set(vs)) != len(vs):
        return
    arr = vs[:]
    sign = 1
    for i in range(len(arr)):
        for j in range(len(arr) - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                sign = -sign
    t = tuple(arr)
    chain[t] = chain.get(t, 0) + coeff * sign
    if chain[t] == 0:
        del chain[t]


def chain_add(a, b, sgn=1):
    out = dict(a)
    for s, c in b.items():
        out[s] = out.get(s, 0) + sgn * c
        if out[s] == 0:
            del out[s]
    return out


def boundary(chain):
    """Unreduced simplicial boundary: d on 0-simplices is 0."""
    out = {}
    for s, c in chain.items():
        if len(s) <= 1:
            continue
        for i in range(len(s)):
            add_simplex(s[:i] + s[i + 1:], c * ((-1) ** i), out)
    return out


# --------------------------------------------------------------------------
# Homology anchor [I]: reduced Betti via mod-p boundary ranks
# --------------------------------------------------------------------------
def rank_mod_p(ncols, get_col):
    """Rank mod P of a matrix given column-by-column.  get_col(j) -> dict
    {row: value}.  Sparse column reduction."""
    pivots = {}  # row -> (column dict, pivot value)
    r = 0
    for j in range(ncols):
        col = {k: v % P for k, v in get_col(j).items() if v % P}
        while col:
            lr = max(col)
            if lr in pivots:
                pv, pval = pivots[lr]
                f = (col[lr] * pow(pval, P - 2, P)) % P
                for rr, vv in pv.items():
                    nv = (col.get(rr, 0) - f * vv) % P
                    if nv:
                        col[rr] = nv
                    elif rr in col:
                        del col[rr]
            else:
                pivots[lr] = (col, col[lr])
                r += 1
                break
    return r


def reduced_betti(simplices_by_dim):
    """Reduced Betti vector b~_0, b~_1, ... over GF(P)."""
    dims = sorted(simplices_by_dim)
    index = {d: {s: i for i, s in enumerate(simplices_by_dim[d])} for d in dims}
    maxd = dims[-1]

    def bdry_col(d, j):
        s = simplices_by_dim[d][j]
        col = {}
        for i in range(len(s)):
            face = s[:i] + s[i + 1:]
            col[index[d - 1][face]] = col.get(index[d - 1][face], 0) + (-1) ** i
        return col

    rank = {0: 0}
    for d in range(1, maxd + 1):
        rank[d] = rank_mod_p(len(simplices_by_dim[d]),
                             lambda j, d=d: bdry_col(d, j))
    rank[maxd + 1] = 0
    betti = []
    for d in range(0, maxd + 1):
        nd = len(simplices_by_dim[d])
        betti.append(nd - rank[d] - rank.get(d + 1, 0))
    betti[0] -= 1  # reduce
    return betti


# --------------------------------------------------------------------------
# Per-n verification
# --------------------------------------------------------------------------
def verify_n(n, Pn, Pn1, full):
    """Run all F18 checks at level n.  Pn = PPF_n, Pn1 = PPF_{n+1} (or None
    when n = 5: we do not materialise PPF_6, checking kappa_n's image by the
    proper-partial-order property directly).  `full`: do exhaustive pairwise
    checks (n = 3,4) vs. formula + sample (n = 5)."""
    checks = 0
    omega = omega_of(n)
    tot1 = (n + 1) * n // 2

    # [B] omega_n is a vertex of Delta_{n+1}
    assert is_proper_partial_order(set(omega), n + 1)
    if Pn1 is not None:
        assert omega in set(Pn1)
    checks += 1

    # [C] kappa_n well-defined
    idx1 = {p: i for i, p in enumerate(Pn1)} if Pn1 is not None else None
    for x in Pn:
        kx = kappa(x, omega)
        if idx1 is not None:
            assert kx in idx1, (n, x)
        else:
            assert is_proper_partial_order(set(kx), n + 1), (n, x)
        # kappa_n(x) = x u omega_n exactly, and the union is disjoint
        assert set(kx) == set(x) | set(omega)
        assert not (set(x) & set(omega))  # x has no (.,n)/(n,.) pairs
        checks += 1

    # [E] the two comparabilities (*)
    for x in Pn:
        kx = kappa(x, omega)
        assert set(iota(x)) <= set(kx)      # iota_n(x) <= kappa_n(x)
        assert set(omega) <= set(kx)        # omega_n   <= kappa_n(x)
        # both strict (so the prism simplices are non-degenerate)
        assert set(iota(x)) != set(kx) and set(omega) != set(kx)
        checks += 1

    # [D] kappa_n order-preserving  &  [F] prism poset maps order-preserving
    def le(a, b):
        return set(a) <= set(b)

    if full:
        pairs = [(x, y) for x in Pn for y in Pn if le(x, y)]
    else:
        import random
        random.seed(1)
        pairs = [(x, y) for x in random.sample(Pn, 250) for y in Pn
                 if le(x, y)]
    for x, y in pairs:
        # [D]
        assert le(kappa(x, omega), kappa(y, omega))
        # [F] H : (x,i) <= (y,j) => H(x,i) <= H(y,j).  Nontrivial slices:
        #     i=j=0: iota(x) <= iota(y);  i=j=1: kappa(x) <= kappa(y);
        #     i=0,j=1: iota(x) <= kappa(y).
        assert le(iota(x), iota(y))
        assert le(iota(x), kappa(y, omega))
        # H' : i=j=1 as above; i=0,j=1: omega <= kappa(y); i=j=0: omega<=omega
        assert le(omega, kappa(y, omega))
        checks += 1

    # [G] S_n-equivariance of kappa_n, omega_n and the prism maps
    if full:
        group = list(itertools.permutations(range(n)))
    else:
        # generators of S_n: transposition (0 1) and the n-cycle
        group = [[1, 0] + list(range(2, n)),
                 list(range(1, n)) + [0]]
    for g in group:
        g1 = list(g) + [n]  # extend by fixing the new element n
        # omega_n is S_n-fixed
        assert act(g1, omega) == omega
        for x in (Pn if full else Pn[:: max(1, len(Pn) // 200)]):
            # kappa_n equivariant: g . kappa_n(x) = kappa_n(g . x)
            assert act(g1, kappa(x, omega)) == kappa(act(g, x), omega)
            # iota_n equivariant
            assert act(g1, iota(x)) == iota(act(g, x))
        checks += 1

    return checks


def chain_null_homotopy(n, Pn, Pn1):
    """[H] Build the explicit chain null-homotopy D = P' - P of iota_n and
    verify  dD + Dd = (iota_n)_# - (const)_#  on every simplex of Delta_n
    (exact integers).  Returns (#simplices checked, simplices-by-dim dict)."""
    omega = omega_of(n)
    idx1 = {p: i for i, p in enumerate(Pn1)}
    om = idx1[omega]

    # Delta_n: enumerate chains of PPF_n (the order complex)
    above = {i: [] for i in range(len(Pn))}
    for i, x in enumerate(Pn):
        for j, y in enumerate(Pn):
            if i != j and set(x) <= set(y):
                above[i].append(j)
    simp = {}

    def dfs(ch):
        simp.setdefault(len(ch) - 1, []).append(tuple(ch))
        for j in above[ch[-1]]:
            dfs(ch + [j])

    for i in range(len(Pn)):
        dfs([i])

    iidx = [idx1[iota(x)] for x in Pn]   # iota_n on vertices -> PPF_{n+1} index
    kidx = [idx1[kappa(x, omega)] for x in Pn]  # kappa_n on vertices

    # the two prism operators on a simplex sigma (tuple of PPF_n indices)
    def P_iota_kappa(sigma):
        out = {}
        k = len(sigma) - 1
        for i in range(k + 1):
            verts = [iidx[sigma[a]] for a in range(0, i + 1)] + \
                    [kidx[sigma[a]] for a in range(i, k + 1)]
            add_simplex(verts, (-1) ** i, out)
        return out

    def P_const_kappa(sigma):
        # only the i = 0 term survives (omega repeats => degenerate for i>=1)
        out = {}
        verts = [om] + [kidx[sigma[a]] for a in range(len(sigma))]
        add_simplex(verts, 1, out)
        return out

    def D(sigma):
        return chain_add(P_const_kappa(sigma), P_iota_kappa(sigma), -1)

    def iota_push(sigma):
        out = {}
        add_simplex([iidx[i] for i in sigma], 1, out)
        return out

    def const_push(sigma):
        out = {}
        add_simplex([om] * len(sigma), 1, out)
        return out

    def kappa_push(sigma):
        out = {}
        add_simplex([kidx[i] for i in sigma], 1, out)
        return out

    nchk = 0
    for d in sorted(simp):
        for sigma in simp[d]:
            # prism identity for P (sanity on the convention):
            #   dP + Pd = kappa_# - iota_#
            lhs = boundary(P_iota_kappa(sigma))
            for i in range(len(sigma)):
                if len(sigma) <= 1:
                    continue
                face = sigma[:i] + sigma[i + 1:]
                lhs = chain_add(lhs, P_iota_kappa(face), (-1) ** i)
            rhs = chain_add(kappa_push(sigma), iota_push(sigma), -1)
            assert lhs == rhs, ("prism P", n, d, sigma)

            # the load-bearing identity:  dD + Dd = iota_# - const_#
            lhs = boundary(D(sigma))
            for i in range(len(sigma)):
                if len(sigma) <= 1:
                    continue
                face = sigma[:i] + sigma[i + 1:]
                lhs = chain_add(lhs, D(face), (-1) ** i)
            rhs = chain_add(iota_push(sigma), const_push(sigma), -1)
            assert lhs == rhs, ("chain null-homotopy", n, d, sigma)
            nchk += 1
    return nchk, simp


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------
def main():
    t0 = time.time()
    total = 0
    print("=" * 72)
    print("F18 (mg-d039): (UCC.2) -- delta_n injective, n-uniformly,")
    print("               via the explicit null-homotopy of iota_n.")
    print("=" * 72)

    # [A] build PPF_n
    PPF = {}
    for n in (3, 4, 5):
        PPF[n] = ppf(n)
    expected = {3: 12, 4: 194, 5: 4110}
    for n in (3, 4, 5):
        assert len(PPF[n]) == expected[n], (n, len(PPF[n]))
    print(f"[A] PPF_n built: |PPF_3|={len(PPF[3])}, |PPF_4|={len(PPF[4])}, "
          f"|PPF_5|={len(PPF[5])}  (F14/F17 convention) -- OK")
    total += 3

    # [B]-[G] structural verification, n = 3,4,5
    for n in (3, 4, 5):
        Pn = PPF[n]
        Pn1 = PPF.get(n + 1)            # PPF_6 not built; n=5 uses direct check
        full = (n in (3, 4))
        c = verify_n(n, Pn, Pn1, full)
        total += c
        mode = "exhaustive" if full else "formula + sample"
        print(f"[B-G] n={n}: omega_n a vertex of Delta_{{{n+1}}}; "
              f"kappa_n well-defined PPF_{n}->PPF_{{{n+1}}}; order-preserving; "
              f"iota_n <= kappa_n >= omega_n; prism poset maps H,H' "
              f"order-preserving; S_{n}-equivariant ({mode}) -- {c} checks OK")

    # [H] chain-level null-homotopy, n = 3,4
    for n in (3, 4):
        nchk, simp = chain_null_homotopy(n, PPF[n], PPF[n + 1])
        total += nchk
        sdesc = ", ".join(f"dim{d}:{len(simp[d])}" for d in sorted(simp))
        print(f"[H] n={n}: Delta_{n} order complex ({sdesc}); explicit chain "
              f"null-homotopy D = P'-P verified: dD+Dd = iota_#-const_# on "
              f"all {nchk} simplices (exact integers).")
        print(f"        => iota_{n} is chain-null-homotopic "
              f"=> (iota_{n})_* = 0 on H~_k, all k>=1 "
              f"=> delta_{n} injective.  (UCC.2)@n={n} "
              f"{'[reproduces mg-59f3, non-circular route]' if n==3 else '[new]'}")

    # [I] homology anchor: reduced Betti of Delta_3, Delta_4
    for n in (3, 4):
        Pn = PPF[n]
        above = {i: [] for i in range(len(Pn))}
        for i, x in enumerate(Pn):
            for j, y in enumerate(Pn):
                if i != j and set(x) <= set(y):
                    above[i].append(j)
        simp = {}

        def dfs(ch, simp=simp, above=above):
            simp.setdefault(len(ch) - 1, []).append(tuple(ch))
            for j in above[ch[-1]]:
                dfs(ch + [j])

        for i in range(len(Pn)):
            dfs([i])
        betti = reduced_betti(simp)
        expect = {3: [0, 1], 4: [0, 0, 1, 0, 0]}[n]
        assert betti == expect, (n, betti)
        total += 1
        print(f"[I] n={n}: reduced Betti(Delta_{n}) = {betti}  "
              f"= Hyp({n})  (H~^{{{n-2}}} 1-dim, else 0) -- consistency anchor OK")

    print("-" * 72)
    print(f"ALL {total} CHECKS PASS  ({time.time() - t0:.1f}s)")
    print()
    print("[J] VERDICT: GREEN-ucc2-proven.")
    print("    iota_n : Delta_n -> Delta_{n+1} is null-homotopic for every")
    print("    n >= 3, by the explicit S_n-equivariant poset zig-zag")
    print("    iota_n <= kappa_n >= const_{omega_n}.  The construction uses")
    print("    NO hypothesis (no Hyp(m), no (UCC), no F17): unconditional,")
    print("    hence a fortiori non-circular (Hyp(n+1) is never invoked).")
    print("    Therefore iota_n^* = 0 in all degrees, and by exactness of")
    print("    the cofiber LES  ker(delta_n) = im(iota_n^*) = 0, so delta_n")
    print("    is injective: (UCC.2) holds for all n >= 3.  With F17")
    print("    ((UCC.1) <=> Hyp(n)), (UCC) is COMPLETE and the F10")
    print("    cohomological core is UNCONDITIONAL.")
    print("=" * 72)


if __name__ == "__main__":
    main()
