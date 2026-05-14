#!/usr/bin/env python3
r"""
posn_n6_out_s6_audit.py
=======================

Compat-Geom mg-3219 — Out(S_6) audit at n=6.

Deepens the first-pass Out(S_6) outer-twin check delivered by F8'-HPC
(mg-3bf3, `scripts/posn_n6_hpc.py --phase=burnside`).  Where mg-3bf3
*cited* the folklore fact "Out(S_6) swaps these three conjugacy-class
pairs", this script **constructs an explicit outer automorphism of
S_6** and verifies the class-swap data from first principles, then runs
four audit checks:

  A. Explicit Out(S_6).  Search for triple-transposition images of the
     Coxeter generators s_0..s_4 satisfying the braid relations; the
     resulting automorphism α is outer (it does not preserve cycle
     type).  Build α as a full map S_6 -> S_6 by Cayley-graph BFS and
     hard-check it is a bijective homomorphism.

  B. Class-swap verification.  Confirm α swaps exactly the three
     outer-twin pairs {(2,1^4)<->(2^3), (3,1^3)<->(3^2), (6)<->(3,2,1)}
     and fixes the other five classes.  This is the data mg-3bf3 took
     on faith.

  C. χ̃(Fix) Out-invariance.  Using the per-class χ̃(Fix_PPF_6(σ)) data
     (re-derived from posn_n6_hpc), check that χ̃(Fix(·)) — a class
     function on S_6 — is invariant under α.  Equivalent to mg-3bf3 §4
     but phrased as "the class function is Out-fixed", not just "the
     three twin pairs agree".

  D. Sign-convention reconciliation.  The mg-3219 ticket states the
     n=5 clean identity as  χ̃(Fix(σ)) = -sgn(σ);  the mg-3bf3 doc
     states the n=6 identity as  χ̃(Fix(σ)) = +sgn(σ).  Both are
     correct: the Hopf-Lefschetz trace formula gives

         χ̃(Fix_PPF_n(σ)) = (-1)^{n-2} · m_sgn · sgn(σ)

     when H̃_*(Δ_n) is concentrated in degree n-2 and is m_sgn copies
     of the sign rep.  The flip is the degree-parity factor (-1)^{n-2},
     a property of *every* n, not an Out(S_6) effect.  This script
     verifies the n=6 instance (-1)^{6-2} = +1 against the per-class
     table, and flags that mg-3bf3's stated "+sgn for n in {4,5}" and
     its universal "+(1/|S_n|)·Σ" Burnside formula are only valid for
     even n (n=4, n=6 — both on mg-3bf3's compute path; the n=5 line
     is a documentation slip that did not touch the n=6 result).

  E. Stab(c*_6) ⊆ A_6 and the Pr-profile.  The per-step Pr-profile
     (7/15, 4/7, 1/2, 1/2) lives on the single S_6-orbit of c*_6.
     Out(S_6) has *no action on PPF_6 at all* (it does not act on the
     ground set {0..5}), so the Pr-profile cannot "split into Out(S_6)
     orbits" — the question is vacuous, and BFT-sharpness is trivially
     Out(S_6)-stable.  What Out(S_6) *can* be asked about is the chain
     stabiliser: we compute Stab(c*_6) ⊆ S_6 and confirm it lies in
     A_6 (needed for the signed-orbit cocycle to be well defined).

Usage:
    python3 posn_n6_out_s6_audit.py [--verbose]

Requires `scripts/_n6_cache/ppf6.pkl` (run `posn_n6_hpc.py --phase=enum`
first).  Pure-Python stdlib; runs in seconds.

References
----------
  - mg-3bf3 (F8'-HPC):  posn_n6_hpc.py, docs/compatibility-geometry-F8prime-HPC.md
  - mg-7b3b (F8'):      posn_n6_icop_empirical.py
  - mg-3219 (this):     docs/compatibility-geometry-out-s6-audit-n6.md
  - Janusz-Rotman, "Outer automorphisms of S_6", Amer. Math. Monthly (1982).
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from itertools import combinations, permutations

import posn_n6_hpc as hpc

N = 6
_PERMS = hpc._PERMS  # all 720 permutations of range(6), as tuples


# ============================================================================
# §A.  Permutation arithmetic + explicit Out(S_6) construction.
# ============================================================================

IDENTITY = tuple(range(N))


def compose(p, q):
    """(p∘q)(i) = p[q[i]] — apply q then p."""
    return tuple(p[q[i]] for i in range(N))


def inverse(p):
    inv = [0] * N
    for i in range(N):
        inv[p[i]] = i
    return tuple(inv)


def transposition(a, b):
    t = list(range(N))
    t[a], t[b] = b, a
    return tuple(t)


def cycle_type(p):
    """Sorted partition of N giving the cycle lengths of p."""
    seen = [False] * N
    parts = []
    for i in range(N):
        if seen[i]:
            continue
        ln = 0
        j = i
        while not seen[j]:
            seen[j] = True
            j = p[j]
            ln += 1
        parts.append(ln)
    return tuple(sorted(parts, reverse=True))


# Cycle-type -> mg-3bf3 class label, for the 11 conjugacy classes of S_6.
CYCLE_TYPE_LABEL = {
    (1, 1, 1, 1, 1, 1): '1^6',
    (2, 1, 1, 1, 1): '2,1^4',
    (3, 1, 1, 1): '3,1^3',
    (2, 2, 1, 1): '2^2,1^2',
    (4, 1, 1): '4,1^2',
    (5, 1): '5,1',
    (6,): '6',
    (2, 2, 2): '2^3',
    (3, 2, 1): '3,2,1',
    (3, 3): '3^2',
    (4, 2): '4,2',
}

# Adjacent-transposition Coxeter generators s_0..s_4 of S_6.
COXETER_GENS = [transposition(i, i + 1) for i in range(N - 1)]


def all_triple_transpositions():
    """The 15 fixed-point-free involutions of S_6 (products of 3
    disjoint transpositions)."""
    out = []
    for parts in _set_partitions_into_pairs(list(range(N))):
        p = list(range(N))
        for (a, b) in parts:
            p[a], p[b] = b, a
        out.append(tuple(p))
    return out


def _set_partitions_into_pairs(elts):
    if not elts:
        yield []
        return
    first = elts[0]
    for i in range(1, len(elts)):
        pair = (first, elts[i])
        rest = elts[1:i] + elts[i + 1:]
        for sub in _set_partitions_into_pairs(rest):
            yield [pair] + sub


def braid_relations_hold(gens):
    """Check the type-A_5 Coxeter relations for an ordered 5-tuple
    `gens` = (g_0..g_4):  g_i^2 = e;  (g_i g_{i+1})^3 = e;
    (g_i g_j)^2 = e for |i-j| >= 2."""
    for i in range(len(gens)):
        if compose(gens[i], gens[i]) != IDENTITY:
            return False
    for i in range(len(gens) - 1):
        g = compose(gens[i], gens[i + 1])
        if compose(compose(g, g), g) != IDENTITY:
            return False
    for i in range(len(gens)):
        for j in range(i + 2, len(gens)):
            g = compose(gens[i], gens[j])
            if compose(g, g) != IDENTITY:
                return False
    return True


def generated_subgroup(gens):
    """Closure of `gens` under composition (BFS over the Cayley graph)."""
    seen = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        g = frontier.pop()
        for s in gens:
            h = compose(g, s)
            if h not in seen:
                seen.add(h)
                frontier.append(h)
    return seen


def find_outer_automorphism(verbose=False):
    """Search for triple-transposition images t_0..t_4 of the Coxeter
    generators s_0..s_4 satisfying the braid relations and generating
    all of S_6.  Returns the image tuple (t_0..t_4).

    Such a map s_i ↦ t_i extends to an automorphism α of S_6 (the
    braid relations are a presentation of S_6), and α is *outer*: an
    inner automorphism preserves cycle type, but α sends the
    transposition s_i to the triple-transposition t_i.
    """
    triples = all_triple_transpositions()
    assert len(triples) == 15, f"expected 15 triple-transpositions, got {len(triples)}"

    # Backtracking search: place t_0..t_4 one at a time, pruning on the
    # braid relations as soon as enough generators are fixed.
    chosen = []

    def backtrack():
        idx = len(chosen)
        if idx == N - 1:
            if not braid_relations_hold(chosen):
                return None
            if generated_subgroup(chosen) == set(_PERMS):
                return tuple(chosen)
            return None
        for t in triples:
            chosen.append(t)
            # partial braid check on the prefix
            ok = True
            for i in range(idx):
                if compose(chosen[i], chosen[i]) != IDENTITY:
                    ok = False
                    break
            if ok and idx >= 1:
                # check relation between chosen[idx-1] and chosen[idx]
                g = compose(chosen[idx - 1], chosen[idx])
                if compose(compose(g, g), g) != IDENTITY:
                    ok = False
            if ok and idx >= 2:
                for i in range(idx - 1):
                    g = compose(chosen[i], chosen[idx])
                    if compose(g, g) != IDENTITY:
                        ok = False
                        break
            if ok:
                res = backtrack()
                if res is not None:
                    return res
            chosen.pop()
        return None

    images = backtrack()
    if images is None:
        raise RuntimeError("no outer-automorphism generator image found "
                           "(should be impossible for S_6)")
    if verbose:
        print("  §A. Explicit Out(S_6) construction")
        print(f"      Coxeter generators s_0..s_4 (adjacent transpositions):")
        for i, s in enumerate(COXETER_GENS):
            print(f"        s_{i} = {s}   cycle type {cycle_type(s)}")
        print(f"      outer-automorphism images t_i = α(s_i) "
              f"(triple-transpositions):")
        for i, t in enumerate(images):
            print(f"        t_{i} = {t}   cycle type {cycle_type(t)}")
        print(f"      braid relations hold: {braid_relations_hold(images)}")
        print(f"      ⟨t_0..t_4⟩ = S_6:    "
              f"{generated_subgroup(images) == set(_PERMS)}")
    return images


def build_automorphism(images, verbose=False):
    """Extend s_i ↦ images[i] to a full map α: S_6 -> S_6 by BFS over
    the Cayley graph (right multiplication by generators).  Hard-checks
    that α is a well-defined bijective homomorphism."""
    alpha = {IDENTITY: IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        g = frontier.pop()
        ag = alpha[g]
        for i, s in enumerate(COXETER_GENS):
            h = compose(g, s)
            ah = compose(ag, images[i])
            if h in alpha:
                # consistency = the braid relations really do hold
                assert alpha[h] == ah, f"α inconsistent at {h}"
            else:
                alpha[h] = ah
                frontier.append(h)
    assert len(alpha) == 720, f"α defined on {len(alpha)} elements, want 720"
    assert len(set(alpha.values())) == 720, "α not injective"
    # full homomorphism check
    for g in _PERMS:
        for h in _PERMS:
            assert alpha[compose(g, h)] == compose(alpha[g], alpha[h]), \
                f"α not a homomorphism at ({g},{h})"
    # outer: α moves a transposition off its cycle type
    s0 = COXETER_GENS[0]
    assert cycle_type(alpha[s0]) != cycle_type(s0), \
        "α preserves cycle type of a transposition — would be inner"
    if verbose:
        print(f"      α extended to all 720 elements: "
              f"bijective homomorphism ✓, outer ✓")
    return alpha


# ============================================================================
# §B.  Class-swap verification.
# ============================================================================

# mg-3bf3's asserted outer-twin pairs + Out-fixed classes.
MG3BF3_TWIN_PAIRS = [('2,1^4', '2^3'), ('3,1^3', '3^2'), ('6', '3,2,1')]
MG3BF3_OUT_FIXED = ['1^6', '2^2,1^2', '4,1^2', '5,1', '4,2']


def verify_class_swaps(alpha, verbose=False):
    """For each S_6 conjugacy class rep σ, compute the class of α(σ) and
    confirm the swap pattern matches mg-3bf3's OUTER_TWIN_PAIRS."""
    reps = hpc.CONJ_REPS_S6
    label_of = {}
    for (sigma, label, sz, sgn) in reps:
        label_of[label] = sigma
    observed = {}  # label -> label of α(rep)
    for (sigma, label, sz, sgn) in reps:
        a_sigma = alpha[tuple(sigma)]
        observed[label] = CYCLE_TYPE_LABEL[cycle_type(a_sigma)]

    # Build the expected permutation of class labels.
    expected = {}
    for (a, b) in MG3BF3_TWIN_PAIRS:
        expected[a] = b
        expected[b] = a
    for c in MG3BF3_OUT_FIXED:
        expected[c] = c

    all_ok = (observed == expected)
    if verbose:
        print()
        print("  §B. Class-swap verification (explicit α vs mg-3bf3 folklore)")
        print(f"      {'class C':>10}  {'sgn':>4}  {'α(C)':>10}  "
              f"{'mg-3bf3 says':>13}  {'match':>6}")
        print(f"      {'-'*56}")
        for (sigma, label, sz, sgn) in reps:
            obs = observed[label]
            exp = expected[label]
            mark = '✓' if obs == exp else '✗ MISMATCH'
            kind = 'fixed' if exp == label else f'twin'
            print(f"      {label:>10}  {sgn:>+4}  {obs:>10}  "
                  f"{exp:>13}  {mark:>6}")
        print(f"      {'-'*56}")
        # sign + class-size preservation (must hold for ANY automorphism)
        sgn_of = {label: sgn for (_, label, _, sgn) in reps}
        sz_of = {label: sz for (_, label, sz, _) in reps}
        sgn_ok = all(sgn_of[c] == sgn_of[observed[c]] for c in observed)
        sz_ok = all(sz_of[c] == sz_of[observed[c]] for c in observed)
        print(f"      α preserves sgn on every class:        {sgn_ok}")
        print(f"      α preserves class size on every class: {sz_ok}")
        print(f"      class-swap pattern matches mg-3bf3:    {all_ok}")
    return all_ok, observed, expected


# ============================================================================
# §C.  χ̃(Fix) Out-invariance + §D. sign-convention reconciliation.
# ============================================================================


def burnside_per_class(ppf, verbose=False):
    """Re-derive χ̃(Fix_PPF_6(σ)) per conjugacy class (skips identity,
    as in mg-3bf3 — |Fix(id)| = |PPF_6| is the deferred HPC piece)."""
    ppf_set = frozenset(ppf)
    res = hpc.compute_burnside_msgn(ppf_set, verbose=False)
    by_label = {d['label']: d for d in res['per_class']}
    return res, by_label


def audit_chi_invariance(by_label, observed, verbose=False):
    """Check χ̃(Fix(·)) is invariant under α (i.e. χ̃ is Out-fixed as a
    class function), and reconcile the sign convention."""
    all_inv = True
    if verbose:
        print()
        print("  §C. χ̃(Fix_PPF_6(σ)) Out(S_6)-invariance")
        print(f"      {'class C':>10}  {'χ̃(Fix C)':>10}  {'α(C)':>10}  "
              f"{'χ̃(Fix αC)':>11}  {'inv?':>5}")
        print(f"      {'-'*52}")
    for label, d in sorted(by_label.items()):
        chi = d['chi_tilde']
        a_label = observed[label]
        chi_a = by_label[a_label]['chi_tilde']
        # identity class is skipped (chi None); treat as "n/a but invariant"
        if chi is None or chi_a is None:
            inv = (a_label == label)  # id is Out-fixed -> trivially invariant
            chi_disp, chi_a_disp = 'SKIP', 'SKIP'
        else:
            inv = (chi == chi_a)
            chi_disp, chi_a_disp = str(chi), str(chi_a)
        if not inv:
            all_inv = False
        if verbose:
            print(f"      {label:>10}  {chi_disp:>10}  {a_label:>10}  "
                  f"{chi_a_disp:>11}  {'✓' if inv else '✗':>5}")
    if verbose:
        print(f"      {'-'*52}")
        print(f"      χ̃(Fix(·)) is Out(S_6)-invariant: {all_inv}")

    # §D. Sign-convention reconciliation.
    if verbose:
        print()
        print("  §D. Sign-convention reconciliation")
        print("      Hopf-Lefschetz (H̃_* concentrated in degree n-2,")
        print("      = m_sgn copies of sign rep):")
        print("          χ̃(Fix_PPF_n(σ)) = (-1)^(n-2) · m_sgn · sgn(σ)")
    parity = (-1) ** (N - 2)
    m_sgn = 1  # mg-3bf3 value (extrapolated; identity-class χ̃ deferred)
    # check the per-class table against (-1)^(n-2)·m_sgn·sgn
    table_ok = True
    for label, d in sorted(by_label.items()):
        if d['chi_tilde'] is None:
            continue
        predicted = parity * m_sgn * d['sgn']
        if d['chi_tilde'] != predicted:
            table_ok = False
    if verbose:
        print(f"      n=6:  (-1)^(6-2) = {parity:+d},  so the n=6 identity is")
        print(f"            χ̃(Fix_PPF_6(σ)) = {parity:+d}·sgn(σ)   "
              f"[matches mg-3bf3 '+sgn']")
        print(f"      n=5:  (-1)^(5-2) = -1,  so the n=5 identity is")
        print(f"            χ̃(Fix_PPF_5(σ)) = -sgn(σ)   "
              f"[matches the mg-3219 ticket]")
        print(f"      => the ticket's '-sgn' (n=5) and mg-3bf3's '+sgn' (n=6)")
        print(f"         are the SAME identity; the flip is the degree-parity")
        print(f"         factor (-1)^(n-2), NOT an Out(S_6) effect.")
        print(f"      n=6 per-class table matches (-1)^(n-2)·m_sgn·sgn: "
              f"{table_ok}")
        print(f"      NOTE: mg-3bf3's doc line \"χ̃(Fix(σ)) = +sgn(σ) for "
              f"n in {{4,5}}\" and its")
        print(f"      universal \"+(1/|S_n|)·Σ sgn·χ̃\" Burnside formula are "
              f"correct only for")
        print(f"      EVEN n.  Both of mg-3bf3's compute points (n=4 calib, "
              f"n=6 result) are")
        print(f"      even, so the n=6 verdict m_sgn=1 is unaffected — the "
              f"n=5 line is a")
        print(f"      documentation slip, flagged here, not a computational "
              f"error.")
    return all_inv, table_ok


# ============================================================================
# §E.  Stab(c*_6) ⊆ A_6 and the Pr-profile under Out(S_6).
# ============================================================================


def audit_stabilizer_and_pr(verbose=False):
    """Compute Stab(c*_6) ⊆ S_6 and confirm it lies in A_6; restate the
    Pr-profile under the (absent) Out(S_6) action."""
    chain = hpc.c_star_6_chain()
    stab = []
    for sigma in _PERMS:
        if all(hpc.apply_perm(P, sigma) == P for P in chain):
            stab.append(sigma)
    in_A6 = all(hpc.perm_sign(s) == 1 for s in stab)

    # Pr-profile (recomputed, cheap) for the orbit-by-orbit restatement.
    Ls = []
    for P in chain:
        cnt = 0
        for perm in _PERMS:
            pos = {perm[k]: k for k in range(N)}
            if all(pos[a] < pos[b] for (a, b) in P):
                cnt += 1
        Ls.append(cnt)
    prs = [Fraction(Ls[k + 1], Ls[k]) for k in range(len(Ls) - 1)]
    bft_lo, bft_hi = Fraction(3, 11), Fraction(8, 11)
    bft = [bft_lo <= p <= bft_hi for p in prs]

    if verbose:
        print()
        print("  §E. Stab(c*_6) ⊆ A_6  and  Pr-profile under Out(S_6)")
        print(f"      |Stab(c*_6)| = {len(stab)}   "
              f"(stabiliser of the ordered 4-cell c*_6 in S_6)")
        print(f"      Stab(c*_6) ⊆ A_6 (all elements even): {in_A6}")
        print(f"      => the signed S_6-orbit sum of c*_6 is well defined "
              f"(F7-style).")
        print()
        print(f"      Pr-profile on the single S_6-orbit of c*_6:")
        print(f"        |L|-profile  = {Ls}")
        print(f"        per-step Pr  = {[str(p) for p in prs]}")
        print(f"        BFT-sharp    = {sum(bft)}/{len(prs)}  "
              f"(each Pr in [3/11, 8/11])")
        print()
        print(f"      Out(S_6) acts on the abstract group S_6, NOT on the")
        print(f"      ground set {{0..5}} — so it has NO action on PPF_6, on")
        print(f"      chains of PPF_6, or on c*_6.  The Pr-profile therefore")
        print(f"      cannot 'split into Out(S_6) orbits': the question is")
        print(f"      vacuous and BFT-sharpness is trivially Out(S_6)-stable.")
        print(f"      Out(S_6) enters ONLY through conjugacy-class data of the")
        print(f"      acting group (§B–§C), where §C shows χ̃(Fix) is Out-fixed.")
    return len(stab), in_A6, Ls, prs, all(bft)


# ============================================================================
# §F.  Out(S_6) and the inductive-lift subgroup (point-stabiliser S_5).
# ============================================================================


def audit_lift_subgroup(alpha, verbose=False):
    """The n -> n+1 inductive lift ι_n: PPF_n -> PPF_{n+1} adds a fresh
    element with no relations; it is equivariant for the POINT-STABILISER
    S_{n} ⊂ S_{n+1}.  At the n=6 base this means ι_5 is equivariant for a
    point-stabiliser S_5 ⊂ S_6.

    Out(S_6) swaps the two conjugacy classes of S_5 ⊂ S_6: the six point
    stabilisers and the six 'exotic' transitive S_5's.  We verify this by
    pushing a point stabiliser through the explicit α and checking the
    image fixes no ground-set point — i.e. α carries the lift's
    equivariance subgroup OUT of the point-stabiliser class.
    """
    H = tuple(sigma for sigma in _PERMS if sigma[5] == 5)        # Stab(5)
    assert len(H) == 120, f"|Stab(5)| = {len(H)}, want 120"
    aH = set(alpha[sigma] for sigma in H)
    assert len(aH) == 120
    # is aH a point stabiliser?  (does it fix some i in 0..5 pointwise?)
    fixed_pts = [i for i in range(N)
                 if all(sigma[i] == i for sigma in aH)]
    is_point_stab = len(fixed_pts) > 0
    if verbose:
        print()
        print("  §F. Out(S_6) and the inductive-lift subgroup")
        print(f"      ι_5: PPF_5 -> PPF_6 is equivariant for the point-")
        print(f"      stabiliser S_5 = Stab(5) ⊂ S_6 (|H| = {len(H)}).")
        print(f"      α(Stab(5)) is an order-{len(aH)} S_5 subgroup; the points")
        print(f"      it fixes pointwise: {fixed_pts or 'NONE — transitive S_5'}")
        print(f"      => α maps the point-stabiliser S_5 to an EXOTIC "
              f"transitive S_5: {not is_point_stab}")
        print(f"      Reading: Out(S_6) IS detectable in the *combinatorial")
        print(f"      presentation* of the lift (it moves ι_5's equivariance")
        print(f"      subgroup off the point-stabiliser class — there is no")
        print(f"      add-an-element lift map equivariant for the exotic S_5).")
        print(f"      But this is a presentation artifact, NOT a cohomological")
        print(f"      obstruction: the transported class ω_bal^(6) lives in the")
        print(f"      sign-rep summand H̃^4(Δ_6)^sgn, and sgn is Out(S_6)-fixed")
        print(f"      (A_6 is the unique index-2 subgroup, hence characteristic).")
        print(f"      n=7 end: Out(S_7) is trivial — no outer twin downstream.")
    return (not is_point_stab)


# ============================================================================
# Main.
# ============================================================================


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--verbose', '-v', action='store_true', default=True)
    args = ap.parse_args()

    print("posn_n6_out_s6_audit.py — Out(S_6) audit at n=6 (mg-3219)")
    print()

    ppf = hpc.load_cache('ppf6')
    if ppf is None:
        print("ERROR: missing _n6_cache/ppf6.pkl — run "
              "`python3 posn_n6_hpc.py --phase=enum` first.")
        sys.exit(1)
    print(f"  loaded PPF_6: {len(ppf)} elements")
    print()

    # §A — explicit Out(S_6).
    images = find_outer_automorphism(verbose=args.verbose)
    alpha = build_automorphism(images, verbose=args.verbose)

    # §B — class swaps.
    swaps_ok, observed, expected = verify_class_swaps(alpha, verbose=args.verbose)

    # §C/§D — χ̃(Fix) Out-invariance + sign reconciliation.
    res, by_label = burnside_per_class(ppf, verbose=args.verbose)
    chi_inv, table_ok = audit_chi_invariance(by_label, observed,
                                             verbose=args.verbose)

    # §E — stabiliser + Pr-profile.
    stab_size, in_A6, Ls, prs, bft_all = audit_stabilizer_and_pr(
        verbose=args.verbose)

    # §F — inductive-lift subgroup.
    lift_detectable = audit_lift_subgroup(alpha, verbose=args.verbose)

    # Verdict.
    print()
    print("  " + "=" * 64)
    print("  VERDICT")
    print("  " + "=" * 64)
    checks = [
        ("§A  explicit outer automorphism α constructed + verified", True),
        ("§B  α swaps exactly mg-3bf3's 3 twin pairs, fixes 5 classes",
         swaps_ok),
        ("§C  χ̃(Fix_PPF_6(·)) is Out(S_6)-invariant (all 11 classes)",
         chi_inv),
        ("§D  n=6 per-class table matches (-1)^(n-2)·m_sgn·sgn", table_ok),
        ("§E  Stab(c*_6) ⊆ A_6", in_A6),
        ("§E  c*_6 Pr-profile 4/4 BFT-sharp", bft_all),
        ("§F  α maps point-stabiliser S_5 to exotic S_5 (detectable, "
         "not obstructive)", lift_detectable),
    ]
    for desc, ok in checks:
        print(f"    [{'PASS' if ok else 'FAIL'}]  {desc}")
    all_pass = all(ok for _, ok in checks)
    print()
    if all_pass:
        print("  GREEN-Out-robust  —  Out(S_6) introduces no deviation in the")
        print("  n=6 Burnside/Lefschetz data: χ̃(Fix) is Out-fixed, m_sgn=1 is")
        print("  Out-invariant, the sign-rep is Out-stable, and Out(S_6) has")
        print("  no action on PPF_6 to perturb the Pr-profile or the lift.")
        print("  Residual: χ̃(Δ_6) for the identity class is the one piece")
        print("  inherited AMBER from mg-3bf3 — an HPC-budget item, NOT an")
        print("  Out(S_6) obstruction.")
    else:
        print("  NON-GREEN — see FAIL lines above.")
    print()
    sys.exit(0 if all_pass else 1)


if __name__ == '__main__':
    main()
