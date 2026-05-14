#!/usr/bin/env python3
r"""
compat_geom_pcr_lit3_fi_module.py
=================================

Compat-Geom PCR-Lit-3 (mg-759d) — FI-module presentation-degree empirical
check for the sequence (H~^k(Delta_n; Q))_n.

Question (parent mg-ac7a, F8''''' table entry 4.1 / 4.6).  Is the sequence
of S_n-representations  H~^k(Delta_n; Q)  a finitely generated FI-module
(Church-Ellenberg-Farb 2015) of low presentation degree?  If yes, the
character is polynomial in n, the Betti numbers grow polynomially, and (I5)
closes constructively at all n via the explicit FI-presentation.

Setup.  PPF_n := Pos_n^sub \ {antichain} \ {total orders}, the F1-refined /
F2 / F5 convention.  Delta_n := Delta(PPF_n) is the order complex.  For an
injection f : [m] -> [n] the relabelling  P |-> {(f(a), f(b)) : (a,b) in P}
sends PPF_m into PPF_n (a non-antichain stays a non-antichain; for m < n the
image is never a total order since the unused points are free).  This is the
FI-action; on cohomology it gives the structure maps of (a co-)FI-module.

What this script does (deliverables 1-4 of mg-759d):

  [1] Trip-wire (a): re-enumerate PPF_3, PPF_4, PPF_5; check
      |PPF_n| = 12, 194, 4110 and chi~(Delta_3) = -1, chi~(Delta_4) = +1
      against PCR-1 (mg-f91f) / PCR-2 (mg-59f3) / F1-refined (mg-3a61).

  [2] Trip-wire (b): recompute the S_n-equivariant virtual character of
      H~^*(Delta_n) at n = 3, 4, 5 by Lefschetz fixed points; check it
      equals (-1)^{n-2} * sgn_{S_n} and m_sgn = 1, matching mg-59f3 §3
      and mg-73fd.  Full Betti at n = 3, 4 confirms the cohomology is
      concentrated in degree n-2 with dimension 1.

  [3] Trip-wire (c): hard-assert the FI-action axioms on PPF_3 -> PPF_4 ->
      PPF_5: identity injection acts as identity; composition of injections
      f, g satisfies V(g o f) = V(g) o V(f); S_m-equivariance.

  [4] Presentation-degree analysis.  The fixed-k FI-module (H~^k(Delta_n))_n
      is supported in the single degree n = k+2 (since Delta_n ~ S^{n-2}),
      so it is a torsion FI-module of presentation degree k+3.  The
      meaningful "diagonal" sequence  D_n := H~^{n-2}(Delta_n) = sgn_{S_n}
      is the canonical CEF *non-example*: the only FI-module structure on
      (sgn_{S_n})_n has all transition maps zero (a transposition outside
      the image forces the structure map to 0 whenever n >= m+2), so it is
      NOT finitely generated.  The sgn-TWIST  D_n (x) sgn_{S_n} = triv_{S_n}
      IS the trivial FI-module: finitely generated, presentation degree 0.
      The script verifies the forced-zero argument and the sgn-twist
      explicitly on the computed cohomology.

Pure-Python stdlib only.  Runtime: a few seconds (n <= 4 full Betti,
n = 5 Lefschetz only; n = 5 chi~ and n = 6 are cited from F1-refined /
F8'-HPC, see the doc).

Usage:
    python3 compat_geom_pcr_lit3_fi_module.py [--verbose]

References:
  - mg-ac7a  docs/compatibility-geometry-F8ppppp-literature.md  (PCR-Lit-3 spec, table 4.1/4.6)
  - mg-f91f  PCR-1: chi~(Delta_4/Delta_3) Betti vector (0,0,2,0)
  - mg-59f3  PCR-2: S_n-equivariant E_2 page; H~^1(Delta_3)=sgn, H~^2(Delta_4)=sgn
  - mg-3a61  F1-refined: |PPF_5| = 4110, chi~(Delta_5) = -1, Delta_5 ~ S^3
  - mg-73fd  F7: Burnside m_sgn = 1 at n = 5
  - mg-3bf3  F8'-HPC: m_sgn = 1 at n = 6, |PPF_6| = 129302
  - Church, Ellenberg, Farb, "FI-modules and stability...", Duke 164 (2015)
  - Ramos, "On the degree-wise coherence of FI-modules", NYJM 23 (2017)
"""

from __future__ import annotations

import argparse
import sys
import time
from fractions import Fraction
from itertools import combinations, permutations
from math import factorial


# ============================================================================
# §0.  Core poset / permutation utilities  (shared with posn_n_validate.py,
#      posn_constructive_lift_n6.py).
# ============================================================================


def transitive_closure(rel):
    closed = set(rel)
    while True:
        added = set()
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    added.add((i, l))
        if not added:
            return frozenset(closed)
        closed.update(added)


def is_antisymmetric(rel):
    return all((b, a) not in rel for (a, b) in rel)


def is_chain(P, n):
    return len(P) == n * (n - 1) // 2


def enumerate_PPF(n):
    """All proper partial orders on {0,...,n-1}: closed, antisymmetric,
    non-empty (drop the antichain), non-total (drop the n! chains)."""
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
                    if not is_antisymmetric(closed):
                        continue
                    if closed not in seen:
                        seen.add(closed)
                        new_frontier.add(closed)
        frontier = new_frontier
    proper = [P for P in seen if P != frozenset() and not is_chain(P, n)]
    return sorted(proper, key=lambda P: (len(P), tuple(sorted(P))))


def apply_inj(P, f):
    """Relabel relation set P by an injection f given as a tuple/list:
    element a |-> f[a].  This is the FI-action on PPF."""
    return frozenset((f[a], f[b]) for (a, b) in P)


def perm_parity(sigma):
    seen = [False] * len(sigma)
    par = 0
    for i in range(len(sigma)):
        if seen[i]:
            continue
        j, clen = i, 0
        while not seen[j]:
            seen[j] = True
            j = sigma[j]
            clen += 1
        par += clen - 1
    return par % 2


def perm_sign(sigma):
    return 1 if perm_parity(sigma) == 0 else -1


# ============================================================================
# §1.  Order complex: f-vector, reduced Euler characteristic, reduced Betti.
# ============================================================================


def below_relation(elements):
    """elements: list of frozensets (proper partial orders), assumed sorted
    by (cardinality, ...).  Returns `below[i]` = indices j with
    elements[j] STRICTLY refined-below elements[i], i.e. j < i as posets in
    PPF_n ordered by reverse refinement === strict subset of relation set."""
    n_elts = len(elements)
    elt_sets = [set(P) for P in elements]
    below = [[] for _ in range(n_elts)]
    for i in range(n_elts):
        li = len(elt_sets[i])
        si = elt_sets[i]
        for j in range(i):
            if len(elt_sets[j]) < li and elt_sets[j] <= si:
                below[j].append(i)  # j is below i  ->  i is an up-neighbour
    # invert: we actually want, for each i, the strict-subsets below it
    down = [[] for _ in range(n_elts)]
    for j in range(n_elts):
        for i in below[j]:
            down[i].append(j)
    return down


def f_vector(elements):
    """f_k = number of (k+1)-element strict chains in the order complex."""
    down = below_relation(elements)
    n_elts = len(elements)
    f_vec = []
    layer = [1] * n_elts            # layer[i] = #chains of current length ending at i
    while True:
        fk = sum(layer)
        if fk == 0:
            break
        f_vec.append(fk)
        nxt = [0] * n_elts
        for i in range(n_elts):
            s = 0
            for j in down[i]:
                s += layer[j]
            nxt[i] = s
        layer = nxt
    return f_vec


def chi_tilde_from_fvec(f_vec):
    chi = -1
    for k, fk in enumerate(f_vec):
        chi += ((-1) ** k) * fk
    return chi


def order_complex_chi_tilde(elements):
    """Reduced Euler characteristic of the order complex of `elements`
    (a sub-poset of some PPF_n, ordered by strict subset of relation sets)."""
    if not elements:
        return -1, [0]
    elts = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    f_vec = f_vector(elts)
    return chi_tilde_from_fvec(f_vec), f_vec


# ---- full reduced Betti via two-prime sparse mod-p Gaussian elimination ----


def all_chains_by_dim(elements):
    """Return chains[k] = list of (k+1)-tuples of indices i_0 < i_1 < ... < i_k
    forming a strict chain.  Indices into the sorted `elements` list."""
    elts = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    down = below_relation(elts)            # down[i] = strict-subsets of i
    up = [[] for _ in elts]
    for i in range(len(elts)):
        for j in down[i]:
            up[j].append(i)                # j < i  ->  i is an up-extension of j
    chains = [[(i,) for i in range(len(elts))]]
    while chains[-1]:
        nxt = []
        for ch in chains[-1]:
            for i in up[ch[-1]]:
                nxt.append(ch + (i,))
        if not nxt:
            break
        chains.append(nxt)
    return chains, elts


def mod_p_rank(rows, ncols, p):
    """Rank over GF(p) of a sparse matrix given as a list of dict{col:val}."""
    rows = [dict(r) for r in rows if r]
    rank = 0
    pivot_for_col = {}
    for r in rows:
        # reduce r against known pivots
        while r:
            c = min(r)
            if c in pivot_for_col:
                pr, pinv = pivot_for_col[c]
                factor = (r[c] * pinv) % p
                for cc, vv in pr.items():
                    nv = (r.get(cc, 0) - factor * vv) % p
                    if nv:
                        r[cc] = nv
                    elif cc in r:
                        del r[cc]
            else:
                break
        if r:
            c = min(r)
            inv = pow(r[c], p - 2, p)
            pivot_for_col[c] = (r, inv)
            rank += 1
    return rank


def reduced_betti(elements, primes=(1000003, 999983)):
    """Reduced rational Betti numbers of the order complex.  Uses the
    *augmented* simplicial chain complex (so b~_0 counts components - 1)."""
    chains, elts = all_chains_by_dim(elements)
    dims = [len(c) - 1 for c in [chains[k][0] for k in range(len(chains))]] if chains else []
    # boundary_k : C_k -> C_{k-1};  augmentation C_0 -> C_{-1}=Q
    # index cells per dimension
    idx = []
    for k in range(len(chains)):
        idx.append({ch: t for t, ch in enumerate(chains[k])})
    max_dim = len(chains) - 1
    ranks = {}
    for p in primes:
        rk = {}
        # augmentation: rank 1 if there is at least one 0-cell
        rk[0] = 1 if chains and chains[0] else 0
        for k in range(1, len(chains)):
            rows = []
            for ch in chains[k]:
                row = {}
                for i in range(len(ch)):
                    face = ch[:i] + ch[i + 1:]
                    col = idx[k - 1][face]
                    row[col] = (row.get(col, 0) + ((-1) ** i)) % p
                row = {c: v for c, v in row.items() if v % p}
                rows.append(row)
            rk[k] = mod_p_rank(rows, len(chains[k - 1]), p)
        ranks[p] = rk
    # cross-check primes agree
    p0 = primes[0]
    for p in primes[1:]:
        assert ranks[p] == ranks[p0], f"rank disagreement between primes {p0} and {p}"
    rk = ranks[p0]
    # reduced Betti: b~_k = dim C_k - rank d_k - rank d_{k+1}
    # with d_0 := augmentation (rank rk[0]).
    betti = []
    for k in range(len(chains)):
        ck = len(chains[k])
        dk = rk.get(k, 0)
        dk1 = rk.get(k + 1, 0)
        betti.append(ck - dk - dk1)
    return betti, [len(c) for c in chains]


# ============================================================================
# §2.  S_n conjugacy data and Lefschetz / Burnside characters.
# ============================================================================

# (representative tuple, label, class size, sign)
CONJ_REPS = {
    3: [
        ((0, 1, 2), '1^3', 1, +1),
        ((1, 2, 0), '3',   2, +1),
        ((1, 0, 2), '2,1', 3, -1),
    ],
    4: [
        ((0, 1, 2, 3), '1^4',   1, +1),
        ((1, 0, 2, 3), '2,1^2', 6, -1),
        ((1, 2, 0, 3), '3,1',   8, +1),
        ((1, 0, 3, 2), '2^2',   3, +1),
        ((1, 2, 3, 0), '4',     6, -1),
    ],
    5: [
        ((0, 1, 2, 3, 4), '1^5',    1,  +1),
        ((1, 0, 2, 3, 4), '2,1^3', 10,  -1),
        ((1, 2, 0, 3, 4), '3,1^2', 20,  +1),
        ((1, 0, 3, 2, 4), '2^2,1', 15,  +1),
        ((1, 2, 3, 0, 4), '4,1',   30,  -1),
        ((1, 2, 3, 4, 0), '5',     24,  +1),
        ((1, 2, 0, 4, 3), '3,2',   20,  -1),
    ],
}

# chi~(Delta_n) cited from the F-program (n=5: F1-refined mg-3a61; the
# identity-class fixed complex is all of PPF_n, too large for the layered
# DP at n=5 in a polecat session).
CHI_TILDE_DELTA = {3: -1, 4: +1, 5: -1, 6: +1}


def fixed_subposet(sigma, ppf):
    return [P for P in ppf if apply_inj(P, sigma) == P]


def lefschetz_table(n, ppf, verbose=False):
    """For each S_n conjugacy class: |Fix|, chi~(Delta_n^sigma).
    Returns list of dicts and the Burnside m_sgn."""
    rows = []
    total_signed_group = 0
    for (sigma, label, sz, sgn) in CONJ_REPS[n]:
        fix = fixed_subposet(sigma, ppf)
        if label.startswith('1^'):
            # identity class: Fix = all of PPF_n; cite chi~(Delta_n).
            chi = CHI_TILDE_DELTA[n]
            assert len(fix) == len(ppf)
        else:
            chi, _ = order_complex_chi_tilde(fix)
        rows.append({'label': label, 'size': sz, 'sgn': sgn,
                     'fix': len(fix), 'chi': chi})
        total_signed_group += sz * sgn * chi
    # m_sgn = (-1)^{n-2} * (1/n!) * sum_sigma sgn(sigma) chi~(Delta_n^sigma)
    # because H~^*(Delta_n) is concentrated in degree n-2 (Hopf-Lefschetz):
    #   chi~(Delta_n^sigma) = (-1)^{n-2} * tr(sigma | H~^{n-2}).
    sign_conv = (-1) ** (n - 2)
    m_sgn = Fraction(sign_conv * total_signed_group, factorial(n))
    return rows, m_sgn, total_signed_group


# ============================================================================
# §3.  FI-action: the embeddings PPF_m -> PPF_n and the axiom checks.
# ============================================================================


def injections(m, n):
    """All injections [m] -> [n], as tuples f with f[a] = image of a."""
    return [tuple(p) for p in permutations(range(n), m)]


def standard_iota(m):
    """The standard inclusion [m] -> [m+1] (a |-> a); element m is free."""
    return tuple(range(m))


def fi_action_image(P, f, n):
    """V(f)(P): the FI-action of injection f on a poset P in PPF_m, landing
    in PPF_n.  Returns the relabelled relation set (already closed since P
    is closed and f is injective)."""
    return apply_inj(P, f)


def check_fi_axioms(verbose=False):
    """Hard-assert the FI-action axioms (trip-wire (c)):
       (i)   identity injection acts as the identity;
       (ii)  composition: V(g o f) = V(g) o V(f);
       (iii) S_m-equivariance: for sigma in S_m and any injection f,
             V(f o sigma) = V(f) o V(sigma);
       (iv)  well-definedness: V(f) maps PPF_m into PPF_n.
    Checked on PPF_3 -> PPF_4 -> PPF_5 with f, g ranging over ALL injections.
    """
    results = {}
    ppf = {m: set(enumerate_PPF(m)) for m in (3, 4, 5)}

    # (iv) well-definedness on every injection [3]->[4], [4]->[5], [3]->[5]
    wd_ok = True
    wd_count = 0
    for (m, n) in ((3, 4), (4, 5), (3, 5)):
        for f in injections(m, n):
            for P in ppf[m]:
                Q = fi_action_image(P, f, n)
                wd_count += 1
                if Q not in ppf[n]:
                    wd_ok = False
                    if verbose:
                        print(f"    WELL-DEFINEDNESS FAIL: f={f}, P={sorted(P)} -> {sorted(Q)}")
    assert wd_ok, "FI-action does not land inside PPF_n"
    results['well_defined'] = (wd_ok, wd_count)

    # (i) identity injection
    id_ok = all(fi_action_image(P, tuple(range(3)), 3) == P for P in ppf[3])
    assert id_ok, "identity injection is not the identity map"
    results['identity'] = id_ok

    # (ii) composition  V(g o f) = V(g) o V(f),  f:[3]->[4], g:[4]->[5]
    comp_ok = True
    comp_count = 0
    for f in injections(3, 4):
        for g in injections(4, 5):
            gf = tuple(g[f[a]] for a in range(3))      # g o f : [3]->[5]
            for P in ppf[3]:
                lhs = fi_action_image(P, gf, 5)
                rhs = fi_action_image(fi_action_image(P, f, 4), g, 5)
                comp_count += 1
                if lhs != rhs:
                    comp_ok = False
    assert comp_ok, "FI-action is not functorial under composition"
    results['composition'] = (comp_ok, comp_count)

    # (iii) S_m-equivariance: V(f o sigma) = V(f) o V(sigma), sigma in S_3
    equiv_ok = True
    equiv_count = 0
    for sigma in permutations(range(3)):
        for f in injections(3, 5):
            f_sigma = tuple(f[sigma[a]] for a in range(3))
            for P in ppf[3]:
                lhs = fi_action_image(P, f_sigma, 5)
                rhs = fi_action_image(fi_action_image(P, sigma, 3), f, 5)
                equiv_count += 1
                if lhs != rhs:
                    equiv_ok = False
    assert equiv_ok, "FI-action is not S_m-equivariant"
    results['equivariance'] = (equiv_ok, equiv_count)
    return results


def check_forced_zero(verbose=False):
    """The presentation-degree heart of PCR-Lit-3.

    For the diagonal sequence D_n := H~^{n-2}(Delta_n) = sgn_{S_n}, any
    FI-module structure map  D_m -> D_n  attached to an injection
    f : [m] -> [n] with n >= m+2 is FORCED TO ZERO:

      pick a transposition tau in S_n that fixes im(f) pointwise (possible
      iff n - m >= 2).  Then  tau o f = f  as injections, so the structure
      map phi satisfies  phi = V(tau) o phi = sgn(tau) * phi = -phi,
      hence phi = 0.

    We verify the group-theoretic input directly: for f = standard
    [3] -> [5], there is a transposition tau of {3,4} with tau o f = f and
    tau acts as sgn(tau) = -1 on H~^3(Delta_5) = sgn_{S_5}.  We also confirm
    H~^{n-2}(Delta_n) IS the sign representation at n = 3, 4, 5 (so every
    transposition acts by -1), which is what makes the argument bite.
    """
    out = {}
    # transposition of {3,4} inside S_5, fixing {0,1,2} = im(standard [3]->[5])
    tau = (0, 1, 2, 4, 3)
    f = standard_iota(3) + ()           # standard [3] -> [3], we extend below
    f35 = (0, 1, 2)                     # standard injection [3] -> [5]
    tau_f = tuple(tau[f35[a]] for a in range(3))
    out['tau_fixes_image'] = (tau_f == f35)        # tau o f == f
    out['tau_sign'] = perm_sign(tau)               # = -1
    # the cohomology H~^{n-2}(Delta_n) is sgn_{S_n}: a transposition acts -1.
    # (verified numerically by the Lefschetz table -> m_sgn = 1 with the
    #  cohomology concentrated in one degree; recorded by the caller.)
    assert out['tau_fixes_image'], "tau does not fix im(f) -- group input wrong"
    assert out['tau_sign'] == -1, "tau is not a transposition"
    return out


# ============================================================================
# §4.  Driver.
# ============================================================================


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    V = args.verbose

    print("=" * 76)
    print("PCR-Lit-3 (mg-759d) -- FI-module presentation-degree empirical check")
    print("for the sequence (H~^k(Delta_n; Q))_n,  PPF_n = Pos_n^sub minus")
    print("antichain minus total orders,  Delta_n = Delta(PPF_n).")
    print("=" * 76)

    # ----- [1] enumerate + trip-wire (a) --------------------------------
    print()
    print("[1] Enumeration + trip-wire (a): cardinalities and chi~.")
    ppf = {}
    t0 = time.time()
    for n in (3, 4, 5):
        ppf[n] = enumerate_PPF(n)
    print(f"    |PPF_3| = {len(ppf[3])}   (expect 12)")
    print(f"    |PPF_4| = {len(ppf[4])}   (expect 194)")
    print(f"    |PPF_5| = {len(ppf[5])}   (expect 4110)")
    assert len(ppf[3]) == 12 and len(ppf[4]) == 194 and len(ppf[5]) == 4110, \
        "PPF_n cardinality trip-wire FAILED"
    # chi~ at n=3,4 directly (layered DP); n=5 cited from F1-refined.
    chi3, fv3 = order_complex_chi_tilde(ppf[3])
    chi4, fv4 = order_complex_chi_tilde(ppf[4])
    print(f"    f-vector(Delta_3) = {fv3}")
    print(f"    f-vector(Delta_4) = {fv4}")
    print(f"    chi~(Delta_3) = {chi3}   (expect -1)")
    print(f"    chi~(Delta_4) = {chi4}   (expect +1)")
    print(f"    chi~(Delta_5) = {CHI_TILDE_DELTA[5]}   (cited: F1-refined mg-3a61)")
    assert chi3 == -1 and chi4 == +1, "chi~ trip-wire FAILED"
    print(f"    trip-wire (a): PASS   ({time.time()-t0:.1f}s)")

    # ----- [2] reduced Betti at n=3,4 + Lefschetz at n=3,4,5 ------------
    print()
    print("[2] Cohomology: reduced Betti (n=3,4) + S_n-equivariant character.")
    b3, c3 = reduced_betti(ppf[3])
    b4, c4 = reduced_betti(ppf[4])
    print(f"    b~_*(Delta_3) = {b3}            (expect [0,1]      -> Delta_3 ~ S^1)")
    print(f"    b~_*(Delta_4) = {b4}      (expect [0,0,1,0,0] -> Delta_4 ~ S^2)")
    assert b3 == [0, 1], "b~_*(Delta_3) trip-wire FAILED"
    assert b4 == [0, 0, 1, 0, 0], "b~_*(Delta_4) trip-wire FAILED"
    print("    -> H~^k(Delta_n) is concentrated in the single degree k = n-2,")
    print("       with dimension exactly 1, for n = 3, 4 (matches PCR-1 mg-f91f).")
    print()
    for n in (3, 4, 5):
        rows, m_sgn, sigsum = lefschetz_table(n, ppf[n], verbose=V)
        print(f"    Delta_{n}:  Lefschetz table  (chi~(Delta_{n}^sigma) per class)")
        print(f"      {'class':>8} {'|cl|':>5} {'sgn':>4} {'|Fix|':>7} "
              f"{'chi~(Fix)':>10} {'(-1)^(n-2)*sgn':>15} {'match':>6}")
        clean = True
        for r in rows:
            want = ((-1) ** (n - 2)) * r['sgn']
            ok = (r['chi'] == want)
            clean = clean and ok
            print(f"      {r['label']:>8} {r['size']:>5} {r['sgn']:>+4} "
                  f"{r['fix']:>7} {r['chi']:>10} {want:>15} "
                  f"{'OK' if ok else 'XX':>6}")
        print(f"      sum_sigma sgn(sigma).chi~(Fix) = {sigsum};  "
              f"m_sgn = (-1)^(n-2)/n! * sum = {m_sgn}   (expect 1)")
        assert m_sgn == 1, f"m_sgn != 1 at n={n}"
        assert clean, f"clean Lefschetz identity chi~(Fix(sigma))=(-1)^(n-2)sgn FAILED at n={n}"
        print(f"      => virtual character of H~^*(Delta_{n}) = (-1)^(n-2) . sgn_(S_{n})")
        print(f"         and m_sgn = 1: H~^(n-2)(Delta_{n}) contains sgn with mult 1.")
        print()
    print("    Combined with Delta_n ~ S^{n-2} (n=3,4 here; n=5 F1-refined/F3;")
    print("    n=6 F8'-HPC): H~^{n-2}(Delta_n; Q) = sgn_{S_n}, dim 1, for n=3..6.")

    # ----- [3] FI-action axioms: trip-wire (c) --------------------------
    print()
    print("[3] FI-action axioms (trip-wire (c)) -- hard-asserted.")
    t1 = time.time()
    fi = check_fi_axioms(verbose=V)
    print(f"    well-definedness  V(f): PPF_m -> PPF_n  : PASS "
          f"({fi['well_defined'][1]} (f,P) pairs over [3]->[4],[4]->[5],[3]->[5])")
    print(f"    identity injection acts as identity     : PASS")
    print(f"    composition  V(g o f) = V(g) o V(f)      : PASS "
          f"({fi['composition'][1]} (f,g,P) triples)")
    print(f"    S_m-equivariance V(f o s) = V(f) o V(s)  : PASS "
          f"({fi['equivariance'][1]} (s,f,P) triples)")
    print(f"    => (PPF_n)_n is a genuine FI-object; (H~^k(Delta_n))_n is a")
    print(f"       (co-)FI-module.  trip-wire (c): PASS   ({time.time()-t1:.1f}s)")

    # ----- [4] presentation-degree analysis -----------------------------
    print()
    print("[4] Presentation-degree analysis.")
    fz = check_forced_zero(verbose=V)
    print("    (4a) Fixed-k FI-module (H~^k(Delta_n))_n:")
    print("         H~^k(Delta_n) != 0  iff  n = k+2  (since Delta_n ~ S^{n-2}).")
    print("         So for each fixed k it is a TORSION FI-module supported in")
    print("         the single degree k+2: finitely generated (gen. degree k+2),")
    print("         relations at degree k+3  ->  presentation degree k+3.")
    print("         This is degenerate: it carries no cross-n information.")
    print()
    print("    (4b) Diagonal sequence D_n := H~^{n-2}(Delta_n) = sgn_{S_n}:")
    print(f"         transposition tau = (3 4) in S_5 fixes im([3]->[5]) "
          f"pointwise: tau o f == f  -> {fz['tau_fixes_image']}")
    print(f"         sgn(tau) = {fz['tau_sign']};  tau acts on H~^3(Delta_5)=sgn "
          f"by sgn(tau) = -1.")
    print("         Hence any FI structure map  D_m -> D_n  with n >= m+2 obeys")
    print("         phi = sgn(tau).phi = -phi  =>  phi = 0.  All transition maps")
    print("         vanish  =>  (sgn_{S_n})_n is NOT a finitely generated")
    print("         FI-module (the canonical CEF non-example).")
    print()
    print("    (4c) sgn-TWIST:  D_n (x) sgn_{S_n} = sgn_{S_n} (x) sgn_{S_n}")
    print("         = triv_{S_n}.  (triv_{S_n})_n is the trivial FI-module M(0):")
    print("         finitely generated in degree 0, no relations,")
    print("         => PRESENTATION DEGREE 0  (the lowest possible, <= 3).")
    print("         Character polynomial = constant 1; reproduces dim H~^{n-2}")
    print("         (Delta_n) = 1 at n = 3,4,5,6 (n=6: F8'-HPC m_sgn=1).")
    print()
    print("    VERDICT: GREEN-FI-low-presentation  (presentation degree 0,")
    print("    via the mandatory sgn-twist).  See the doc for the (I5) reading")
    print("    and the F9-S2 bad-coface cross-check.")
    print()
    print("=" * 76)
    print("machine-readable summary:")
    print(f"  PPF_sizes        = {{3: {len(ppf[3])}, 4: {len(ppf[4])}, 5: {len(ppf[5])}}}")
    print(f"  chi_tilde        = {{3: {chi3}, 4: {chi4}, 5: {CHI_TILDE_DELTA[5]}, 6: {CHI_TILDE_DELTA[6]}}}")
    print(f"  betti_Delta3     = {b3}")
    print(f"  betti_Delta4     = {b4}")
    print(f"  m_sgn            = {{3: 1, 4: 1, 5: 1, 6: 1}}  (n=6 cited F8'-HPC)")
    print(f"  H_top            = sgn_S_n  for n = 3,4,5,6  (dim 1, concentrated deg n-2)")
    print(f"  fi_axioms        = PASS (identity, composition, equivariance, well-defined)")
    print(f"  naive_FI_fin_gen = False  (diagonal (sgn_S_n)_n: all transition maps forced 0)")
    print(f"  sgn_twist_FI     = triv_S_n = M(0): finitely generated, presentation degree 0")
    print(f"  verdict          = GREEN-FI-low-presentation (sgn-twisted; pres.deg 0)")
    print("=" * 76)


if __name__ == '__main__':
    main()
