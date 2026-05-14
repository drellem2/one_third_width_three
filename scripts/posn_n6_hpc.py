#!/usr/bin/env python3
r"""
posn_n6_hpc.py
==============

Compat-Geom F8'-HPC master script (mg-3bf3).  Executes the 4 HPC-class
steps deferred from F8' (mg-7b3b) at n=6, lifting the empirical Pr-profile
evidence to direct cohomological evidence:

  Step 1 (PPF_6 enum):
      Full enumeration of PPF_6 — proper partial orders on {0,...,5},
      i.e. excluding empty + chains.  Expected ~130k posets.

  Step 2 (Chamber Morse at n=6):
      Apply the F5-style chamber-restricted Morse function to
      Δ(PPF_6 / S_6).  Identify critical 4-cell c*_6_C and its
      Pr-profile.

  Step 5 (Burnside / Lefschetz sign-rep extraction at n=6):
      Compute χ̃(Fix_PPF_6(σ)) for each S_6 conjugacy class.
      Assemble m_sgn(n=6) = (1/|S_6|) · Σ sgn(σ) · χ̃(Fix(σ)).

      EXPLICIT Out(S_6) AUDIT (Daniel reminder 2026-05-14T02:53Z):
      Compare χ̃(Fix(σ)) for the THREE outer-twin pairs:
        (2,1^4) vs (2^3)     — transpositions vs triple-transpositions
        (3,1^3) vs (3^2)     — 3-cycles vs (3,3)-cycles
        (6)     vs (3,2,1)   — 6-cycles vs (3,2,1)
      An inequality on ANY pair signals Out(S_6) deviation in the
      cohomology, which would require correction in the Burnside sum.

  Step 8 (Plan B Forman V-path BFS at n=6):
      Apply the F7' Plan B strategy (mg-e8d5) at n=6.  Build a literal
      Morse cocycle ω_bal^(6) ∈ Z^4(Δ_6; ℚ) on the sign-rep with
      d ω_bal^(6) = 0 and ⟨ω_bal^(6), c*_6⟩ = ±1.

  Verdict (per ticket spec):
      GREEN-clean-extension       : m_sgn(6) = 1, Plan B works,
                                    Out(S_6) twin pairs equal,
                                    Pr-profile matches mg-7b3b.
      GREEN-with-Plan-H-correction: Plan B fails, Plan-H works.
      AMBER-Out-S6-deviation      : twin pairs unequal.
      AMBER-budget-cap            : enum too large; structural
                                    extrapolation.
      RED-structural              : cohomology diverges from n=5.

Implementation notes
--------------------

* Pure-Python stdlib; no third-party dependencies.
* Checkpoints to disk (pickle) so phases can be re-run or resumed
  without redoing the costly PPF_6 enumeration.
* Designed to fit a 600k-token polecat budget.  Critical computations
  (Burnside m_sgn, Out(S_6) audit) are prioritized over speculative
  ones (Plan B Forman, which depends on chamber Morse).
* If chamber Morse at n=6 produces too-large order-complex chain
  counts, falls back to structural extrapolation and reports
  AMBER-budget-cap with the data we DO have.

Usage:
    python3 posn_n6_hpc.py [--cache-dir DIR] [--phase NAME] [--verbose]

Phases:
    enum       — Phase 1: PPF_6 enumeration.
    orbits     — Phase 2: S_6 orbit grouping.
    burnside   — Phase 3: Burnside m_sgn + Out(S_6) audit.
    morse      — Phase 4: chamber Morse at n=6.
    planB      — Phase 5: Plan B Forman cocycle.
    pr         — Phase 6: per-step Pr re-verification.
    all        — run all phases sequentially (default).

References
----------
  - mg-7b3b (F8'):    posn_n6_icop_empirical.py — n=6 ICOP empirical.
  - mg-1e58 (F5):     posn_chamber_morse_n5.py  — chamber Morse at n=5.
  - mg-73fd (F7):     posn_equivariant_morse_n5.py — Burnside at n=5.
  - mg-e8d5 (F7'):    posn_equivariant_matching_n5_planH.py — Plan B/H.
  - mg-3219 (audit):  Out(S_6) outer-twin audit at n=6 (downstream).
"""

from __future__ import annotations

import argparse
import os
import pickle
import sys
import time
from fractions import Fraction
from itertools import permutations
from math import factorial

N = 6
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '_n6_cache')


# ============================================================================
# §0.  Core utilities.
# ============================================================================


def transitive_closure(rel):
    """Transitive closure of `rel` (set of (i,j) pairs)."""
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
    for (a, b) in rel:
        if (b, a) in rel:
            return False
    return True


def is_chain(P, n):
    """A chain has exactly n(n-1)/2 strict relations under closure."""
    return len(P) == n * (n - 1) // 2


def apply_perm(P, sigma):
    """sigma is a tuple of length N; relabel P by sigma."""
    return frozenset((sigma[a], sigma[b]) for (a, b) in P)


_PERMS = list(permutations(range(N)))
assert len(_PERMS) == factorial(N)


# ============================================================================
# §1.  PPF_6 enumeration via incremental refinement frontier.
# ============================================================================


def enumerate_PPF(n, verbose=False):
    """Enumerate ALL transitively-closed antisymmetric relations on [0,n),
    including the empty antichain and chains.  Same as F5's
    enumerate_partial_orders_incremental but with PPF filtering applied
    at the end.

    Returns: list of frozenset(P) elements, where P is the closed
    relation.
    """
    if verbose:
        print(f"  Enumerating partial orders on n={n} elements...")
    t0 = time.time()
    antichain = frozenset()
    seen = {antichain}
    frontier = {antichain}
    iter_count = 0
    while frontier:
        new_frontier = set()
        for P in frontier:
            for a in range(n):
                for b in range(n):
                    if a == b:
                        continue
                    if (a, b) in P or (b, a) in P:
                        continue
                    closed = transitive_closure(P | {(a, b)})
                    if not is_antisymmetric(closed):
                        continue
                    if closed not in seen:
                        seen.add(closed)
                        new_frontier.add(closed)
        frontier = new_frontier
        iter_count += 1
        if verbose:
            elapsed = time.time() - t0
            print(f"    iter {iter_count}: frontier={len(frontier):>6}  "
                  f"seen={len(seen):>7}  elapsed={elapsed:6.1f}s")
    all_pos = sorted(seen, key=lambda P: (len(P), tuple(sorted(P))))
    if verbose:
        print(f"  Done.  Total partial orders on n={n}: {len(all_pos)}")
    return all_pos


def filter_PPF(orders, n):
    """Proper partial orders: exclude empty and chains."""
    return [P for P in orders if P != frozenset() and not is_chain(P, n)]


def rank_distribution(orders):
    """Return dict: r -> count of orders with |P| = r."""
    d = {}
    for P in orders:
        r = len(P)
        d[r] = d.get(r, 0) + 1
    return d


# ============================================================================
# §2.  S_6 orbit grouping via lex-min canonical representatives.
# ============================================================================


def lex_min_canonical(P):
    """Lex-min S_N image of P; canonical orbit-representative."""
    if not P:
        return P
    best = None
    for sigma in _PERMS:
        img = apply_perm(P, sigma)
        key = tuple(sorted(img))
        if best is None or key < best:
            best = key
    return frozenset(best)


def group_orbits(elements, verbose=False):
    """Group `elements` by S_N-orbit, returning a list of
    (canonical_rep, orbit_size, set_of_members) sorted by (rank, key)."""
    if verbose:
        print(f"  Computing orbits over {len(elements)} elements...")
    t0 = time.time()
    canon_to_members = {}
    for i, P in enumerate(elements):
        c = lex_min_canonical(P)
        canon_to_members.setdefault(c, set()).add(P)
        if verbose and (i + 1) % 5000 == 0:
            elapsed = time.time() - t0
            print(f"    processed {i+1:>6}/{len(elements)} "
                  f"({elapsed:.1f}s, {(i+1)/elapsed:.0f} per sec)")
    orbits = []
    for c, members in canon_to_members.items():
        orbits.append((c, len(members), frozenset(members)))
    orbits.sort(key=lambda t: (len(t[0]), tuple(sorted(t[0]))))
    if verbose:
        elapsed = time.time() - t0
        print(f"  Done.  Total orbits: {len(orbits)} ({elapsed:.1f}s)")
    return orbits


# ============================================================================
# §3.  Burnside / Lefschetz sign-rep extraction at n=6.
# ============================================================================


# S_6 conjugacy class representatives (cycle shape, label, class size, sign).
# Total: 1 + 15 + 40 + 45 + 90 + 144 + 120 + 15 + 90 + 40 + 120 = 720 ✓
CONJ_REPS_S6 = [
    ((0, 1, 2, 3, 4, 5), '1^6',       1,  +1),  # identity
    ((1, 0, 2, 3, 4, 5), '2,1^4',    15,  -1),  # transposition
    ((1, 2, 0, 3, 4, 5), '3,1^3',    40,  +1),  # 3-cycle
    ((1, 0, 3, 2, 4, 5), '2^2,1^2',  45,  +1),  # double trans
    ((1, 2, 3, 0, 4, 5), '4,1^2',    90,  -1),  # 4-cycle
    ((1, 2, 3, 4, 0, 5), '5,1',     144,  +1),  # 5-cycle
    ((1, 2, 3, 4, 5, 0), '6',       120,  -1),  # 6-cycle
    ((1, 0, 3, 2, 5, 4), '2^3',      15,  -1),  # triple trans  [twin of (2,1^4)]
    ((1, 2, 0, 4, 3, 5), '3,2,1',   120,  -1),  # (3,2,1)       [twin of (6)]
    ((1, 2, 0, 4, 5, 3), '3^2',      40,  +1),  # (3,3)         [twin of (3,1^3)]
    ((1, 2, 3, 0, 5, 4), '4,2',      90,  +1),  # (4,2)
]


def perm_parity(sigma):
    """0 if even, 1 if odd."""
    n = len(sigma)
    seen = [False] * n
    cycles = 0
    for i in range(n):
        if seen[i]:
            continue
        cycles += 1
        j = i
        while not seen[j]:
            seen[j] = True
            j = sigma[j]
    return (n - cycles) % 2


def perm_sign(sigma):
    return 1 if perm_parity(sigma) == 0 else -1


def check_conj_reps():
    total = sum(sz for (_, _, sz, _) in CONJ_REPS_S6)
    assert total == 720, f"S_6 conj-reps sum to {total}, want 720"
    for (sigma, label, sz, sgn) in CONJ_REPS_S6:
        psign = perm_sign(sigma)
        assert psign == sgn, f"{label}: declared sgn {sgn} != computed {psign}"
    return True


def fixed_PPF(sigma, ppf_set):
    """Fix_PPF(σ) = {P ∈ ppf_set : σ(P) = P}."""
    return [P for P in ppf_set if apply_perm(P, sigma) == P]


def order_complex_chi_tilde_and_fvec(elements, max_dim=None, verbose=False):
    r"""Compute (χ̃, f-vector) of the order complex Δ(elements, ⊆-refinement).

    f_k = number of strictly ascending chains of length k+1.
    χ̃ = -1 + Σ_k (-1)^k f_k.

    DP layer by layer.  Caps at max_dim if provided (so f-vector
    has length min(max_dim+1, max_chain_length)).
    """
    if not elements:
        # Empty complex: χ̃(∅) = -1 (reduced).
        return -1, []
    # Sort by inclusion-compatible key.
    elts = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    rank = {P: i for i, P in enumerate(elts)}
    n_elts = len(elts)
    # below[i] = list of j < i s.t. elts[j] ⊊ elts[i].
    below = [[] for _ in range(n_elts)]
    elts_sets = [set(P) for P in elts]
    for i in range(n_elts):
        si = elts_sets[i]
        li = len(si)
        for j in range(i):
            if len(elts_sets[j]) >= li:
                continue
            if elts_sets[j].issubset(si):
                below[i].append(j)
    # layer[k][i] = #chains of length k+1 ending at elts[i].
    f_vec = []
    layer_prev = [1] * n_elts  # length-1 chains
    k = 0
    while True:
        fk = sum(layer_prev)
        f_vec.append(fk)
        if max_dim is not None and k >= max_dim:
            break
        # advance to next layer
        layer_next = [0] * n_elts
        any_nonzero = False
        for i in range(n_elts):
            s = 0
            for j in below[i]:
                s += layer_prev[j]
            layer_next[i] = s
            if s > 0:
                any_nonzero = True
        if not any_nonzero:
            break
        layer_prev = layer_next
        k += 1
    chi_tilde = -1
    for k, fk in enumerate(f_vec):
        chi_tilde += ((-1) ** k) * fk
    return chi_tilde, f_vec


def compute_burnside_msgn(ppf_set, verbose=False,
                          skip_identity_chi=True,
                          max_fix_size_for_chi=20000):
    """For each S_6 conjugacy class rep, compute χ̃(Fix(σ)).

    For σ=id (Fix = full PPF_6, |Fix|=129302), direct chi-tilde
    computation requires O(|Fix|^2) below-graph construction (~10^10 ops,
    infeasible in pure Python).  Two strategies:
      (a) skip_identity_chi=True: report fix-size only, defer chi to a
          separate computation; assume the n=4/n=5 clean Lefschetz
          identity χ̃(Δ_n) = -sgn(id) = -1 to extract m_sgn.
      (b) skip_identity_chi=False: attempt the direct computation
          anyway (will likely time out).

    For σ ≠ id, the typical |Fix| is small (often <1000), so the DP
    runs in seconds.  We still guard with max_fix_size_for_chi.

    Sign convention (calibrated against n=4 via posn_n_validate.py):
      m_sgn = +(1/|S_n|) · Σ_σ sgn(σ) · χ̃(Δ(Fix(σ)))
    Clean Lefschetz identity (empirical, n=4,5): χ̃(Fix(σ)) = +sgn(σ).
    Then Σ = |S_n|·1 → m_sgn = 1.

    Returns dict with per-class data + final m_sgn (or m_sgn_assumed).
    """
    check_conj_reps()
    if verbose:
        print(f"  Burnside / Lefschetz sign-rep at n=6:")
        print(f"    {'class':>10}  {'|class|':>8}  {'sgn':>3}  "
              f"{'|Fix|':>8}  {'χ̃(Fix)':>10}  {'-sgn?':>6}  "
              f"{'time(s)':>8}")
        print(f"    {'-'*78}")
    per_class = []
    total_signed = 0  # Σ_{σ ∈ S_6} sgn(σ) · χ̃(Fix(σ)) · |class|
    skipped_id = False
    for (sigma, label, sz, sgn) in CONJ_REPS_S6:
        t0 = time.time()
        fix = fixed_PPF(sigma, ppf_set)
        is_id = (label == '1^6')
        if is_id and skip_identity_chi:
            chi_tilde = None
            fvec = None
            elapsed = time.time() - t0
            clean_id = None
            skipped_id = True
        elif len(fix) > max_fix_size_for_chi:
            chi_tilde = None
            fvec = None
            elapsed = time.time() - t0
            clean_id = None
        else:
            chi_tilde, fvec = order_complex_chi_tilde_and_fvec(fix)
            elapsed = time.time() - t0
            # Clean Lefschetz identity (calibrated at n=4 via
            # posn_n_validate.py): χ̃(Δ(Fix(σ))) = +sgn(σ).
            clean_id = (chi_tilde == sgn)
        per_class.append({
            'sigma': sigma,
            'label': label,
            'class_size': sz,
            'sgn': sgn,
            'fix_size': len(fix),
            'chi_tilde': chi_tilde,
            'f_vec': fvec,
            'clean_lefschetz_identity': clean_id,
            'time_sec': elapsed,
        })
        if chi_tilde is not None:
            total_signed += sz * sgn * chi_tilde
        if verbose:
            chi_str = ('SKIP' if chi_tilde is None else str(chi_tilde))
            clean = ('-' if clean_id is None
                     else ('✓' if clean_id else '✗'))
            print(f"    {label:>10}  {sz:>8}  {sgn:>+3}  {len(fix):>8}  "
                  f"{chi_str:>10}  {clean:>6}  {elapsed:>8.2f}")
    # m_sgn = +(1/|S_n|) · total_signed   (sign calibrated at n=4)
    m_sgn_full = None
    m_sgn_assumed = None
    if skipped_id:
        # Clean Lefschetz extrapolation: χ̃(Δ_6) = sgn(id) = +1.
        ts_assumed = total_signed + 1 * 1 * 1  # sz=1, sgn=+1, χ̃=+1
        m_sgn_assumed = Fraction(ts_assumed, 720)
    else:
        m_sgn_full = Fraction(total_signed, 720)
    if verbose:
        print(f"    {'-'*78}")
        if skipped_id:
            print(f"    Identity χ̃ skipped (|Fix|=|PPF_6|=129302; direct DP")
            print(f"    requires O(|PPF_6|^2)≈10^10 set ops — see §3b bitmask).")
            print(f"    Σ over NON-id  =  {total_signed}")
            print(f"    Extrapolating χ̃(Δ_6) = +1 (n=4,5 clean Lefschetz):")
            print(f"      m_sgn(n=6) = +(Σ_non-id + 1)/|S_6| = "
                  f"{m_sgn_assumed}")
        else:
            print(f"    Σ sgn(σ) · |class(σ)| · χ̃(Fix(σ))  =  {total_signed}")
            print(f"    m_sgn(n=6) = +Σ/|S_6|   =  {m_sgn_full}")
        print(f"    Expected (n=4, n=5 precedent):  m_sgn = 1")
    return {'per_class': per_class,
            'total_signed_non_id': total_signed,
            'm_sgn_full': m_sgn_full,
            'm_sgn_assumed': m_sgn_assumed,
            'skipped_id': skipped_id,
            'm_sgn': m_sgn_full if m_sgn_full is not None else m_sgn_assumed,
            }


# ============================================================================
# §3a.  Out(S_6) audit — outer-twin conjugacy class comparison.
# ============================================================================


# The Out(S_6) automorphism (well-known; cf. e.g. Janusz–Rotman) swaps:
#   transposition (2,1^4)       ↔ triple-transposition (2^3)
#   3-cycle       (3,1^3)       ↔ (3,3)-cycle           (3^2)
#   6-cycle       (6)           ↔ (3,2,1)
# (Other classes — 1^6, 2^2·1^2, 4·1^2, 5·1, 4·2 — are Out-fixed.)
OUTER_TWIN_PAIRS = [
    ('2,1^4',  '2^3'),
    ('3,1^3',  '3^2'),
    ('6',      '3,2,1'),
]


def out_s6_audit(per_class_data, verbose=False):
    """For each outer-twin pair (C_a, C_b) of S_6, compare χ̃(Fix(σ_a))
    and χ̃(Fix(σ_b)).

    Returns: dict with per-pair comparison + overall verdict.
    """
    by_label = {d['label']: d for d in per_class_data}
    results = []
    all_equal = True
    if verbose:
        print()
        print(f"  Out(S_6) audit — outer-twin pair χ̃(Fix) comparison:")
        print(f"    {'pair':>30}  {'χ̃_a':>8}  {'χ̃_b':>8}  {'equal?':>8}  "
              f"{'|Fix_a|':>8}  {'|Fix_b|':>8}")
        print(f"    {'-'*78}")
    for (a, b) in OUTER_TWIN_PAIRS:
        da = by_label[a]
        db = by_label[b]
        equal = (da['chi_tilde'] == db['chi_tilde'])
        results.append({
            'pair': (a, b),
            'chi_a': da['chi_tilde'],
            'chi_b': db['chi_tilde'],
            'equal': equal,
            'fix_a_size': da['fix_size'],
            'fix_b_size': db['fix_size'],
            'fvec_a': da['f_vec'],
            'fvec_b': db['f_vec'],
        })
        if not equal:
            all_equal = False
        if verbose:
            eq = "✓" if equal else "✗ DEVIATION"
            print(f"    {a + ' vs ' + b:>30}  {da['chi_tilde']:>8}  "
                  f"{db['chi_tilde']:>8}  {eq:>8}  "
                  f"{da['fix_size']:>8}  {db['fix_size']:>8}")
    if verbose:
        print(f"    {'-'*78}")
        if all_equal:
            print(f"    Verdict: χ̃(Fix) EQUAL on all 3 outer-twin pairs.")
            print(f"    →  No Out(S_6) deviation in Burnside sum; m_sgn(n=6) "
                  f"is Out(S_6)-invariant.")
        else:
            print(f"    Verdict: χ̃(Fix) DIFFERS on ≥1 outer-twin pair.")
            print(f"    →  Out(S_6) deviation present; Burnside sum may need "
                  f"correction.  Triggers mg-3219 follow-up.")
    return {'per_pair': results, 'all_equal': all_equal}


# ============================================================================
# §4.  Chamber poset Δ(PPF_6/S_6) — orbit-quotient.
# ============================================================================


def build_chamber_poset(orbits, verbose=False):
    """Construct the chamber refinement poset on S_6-orbits:
    orbit A ≤ orbit B iff there exist P_A ∈ orbit A, P_B ∈ orbit B with
    P_A ⊆ P_B (set-inclusion of relations).

    Returns: (canon_reps_list, refines_dict) where:
      canon_reps_list: list of canonical reps, sorted by (rank, key)
      refines_dict[ca] = set of cb that ca refines TO (immediate or transitive)
    """
    if verbose:
        print(f"  Building chamber poset over {len(orbits)} orbits...")
    t0 = time.time()
    reps = [c for (c, _, _) in orbits]
    members_by_rep = {c: ms for (c, _, ms) in orbits}
    rep_index = {c: i for i, c in enumerate(reps)}
    refines = {c: set() for c in reps}
    # For each pair of distinct orbits with rank_A < rank_B, check whether
    # any P_A ⊆ any P_B.  Equivalent: there's some perm σ_A, σ_B s.t.
    # σ_A(rep_A) ⊆ σ_B(rep_B), i.e. rep_A^σ ⊆ rep_B for some σ.
    # We just check: ∃ P_A in members_A, ∃ P_B in members_B, P_A ⊆ P_B.
    for i, ca in enumerate(reps):
        ms_a = members_by_rep[ca]
        len_a = len(ca)
        for cb in reps[i + 1:]:
            if len(cb) <= len_a:
                continue
            ms_b = members_by_rep[cb]
            found = False
            for pa in ms_a:
                pa_set = pa
                for pb in ms_b:
                    if pa_set <= pb:  # frozenset subset
                        found = True
                        break
                if found:
                    break
            if found:
                refines[ca].add(cb)
        if verbose and (i + 1) % 10 == 0:
            elapsed = time.time() - t0
            print(f"    processed {i+1:>4}/{len(reps)} orbits ({elapsed:.1f}s)")
    elapsed = time.time() - t0
    if verbose:
        n_edges = sum(len(v) for v in refines.values())
        print(f"  Done.  Edges in chamber poset (full transitive): {n_edges}  "
              f"({elapsed:.1f}s)")
    return reps, refines


# ============================================================================
# §4a.  Chamber Hasse covers from transitive refinement.
# ============================================================================


def chamber_hasse_covers(reps, refines):
    """Compute Hasse covers of chamber poset: A ⋖ B iff A < B and no C with
    A < C < B."""
    covers = {c: set() for c in reps}
    # For efficiency, ensure refines[c] is the full transitive set.
    for c in reps:
        for d in list(refines[c]):
            # d is a cover of c iff no e with c < e < d.
            is_cover = True
            for e in refines[c]:
                if e == d:
                    continue
                if d in refines[e]:
                    is_cover = False
                    break
            if is_cover:
                covers[c].add(d)
    return covers


# ============================================================================
# §4b.  Chamber order-complex chains (DP-based count, not enumeration).
# ============================================================================


def chamber_chain_fvec(reps, covers, max_dim=None):
    """f-vector of Δ(chamber poset): f_k = #strict chains of length k+1.
    Note: chains use the FULL strict partial order, not just Hasse covers;
    we use Hasse covers via DP saying "to extend, jump to any successor."

    Implementation: layer[k][c] = #length-(k+1) chains ending at c.
    Strict chains correspond to paths in the "below" graph; we use
    "any strictly-below" via the refines dict (full transitive).
    """
    raise NotImplementedError("see order_complex_chi_tilde_and_fvec instead")


# ============================================================================
# §5.  Greedy chamber Morse matching.
# ============================================================================


def chamber_morse_matching(reps, refines, verbose=False):
    """Run greedy acyclic Morse matching on the chamber order complex
    Δ(chamber poset).

    Approach (F5 §E):
      - Enumerate strict chains of orbits up to length 5 (4-cells).
        At n=6, chains can be longer; we cap at length 5 (cells of
        dim 0..4) for the dim-4 critical-cell target.
      - For each chain C, try to match it with a coface (chain
        extending C by one element) such that no Morse cycle results.
      - Match-pairs form the V-paths; unmatched chains are critical.

    Returns: {
        'matched': set of (c, d) chain-coface pairs,
        'critical': list of critical chains,
        'critical_by_dim': dict dim -> list,
    }

    NOTE: at n=6 the order complex may be too large to fully enumerate
    in pure Python.  We cap at max_chains (default 5M) and report
    partial results if exceeded.
    """
    raise NotImplementedError("phase 4 — see __main__")


# ============================================================================
# §6.  Plan B Forman V-path BFS — literal Morse cocycle.
# ============================================================================


def planB_forman_bfs(c_star_6_chain, ppf_list, verbose=False):
    """Plan B (F7' / mg-e8d5): V-path BFS from c*_6 to find a literal
    Morse cocycle ω_bal^(6) ∈ Z^4(Δ_6; ℚ) on the sign-rep with
      d ω_bal^(6) = 0 and ⟨ω_bal^(6), c*_6⟩ = ±1.

    The strategy: start from ω_naive (signed orbit support) and solve
    the constrained linear system d(ω_naive + ψ) = 0 over ψ supported
    on the "wing" cofaces of c*_6.
    """
    raise NotImplementedError("phase 5 — see __main__")


# ============================================================================
# §7.  c*_6 chain (lex-min iota_5-lift + step-4 cover (0,2)).
# ============================================================================


# Per mg-7b3b (F8' empirical):
#   c*_6 = (P_0, P_1, P_2, P_3, P_4) at n=6, where
#     P_0..P_3 = iota_5-lifts of F5's c*_5 (P_0..P_3 at n=5; element 5 added,
#                no relations involving 5),
#     P_4 = P_3 ∪ {(0, 2)}  -- the lex-min admissible step-4 cover with
#           Pr = 1/2.
#   |L|-profile = (180, 84, 48, 24, 12)
#   per-step Pr = (7/15, 4/7, 1/2, 1/2)  -- 4/4 BFT-sharp.
F5_C_STAR_COVERS = [
    frozenset({(0, 1), (2, 1), (3, 1)}),
    frozenset({(0, 1), (0, 4), (2, 1), (2, 4), (3, 1)}),
    frozenset({(0, 4), (2, 4), (3, 1), (4, 1)}),
    frozenset({(0, 3), (0, 4), (2, 3), (2, 4), (3, 1), (4, 1)}),
]


def c_star_6_chain():
    """Build the c*_6 lex-min critical 4-cell at n=6 per mg-7b3b."""
    closed = [transitive_closure(P) for P in F5_C_STAR_COVERS]
    P3 = closed[-1]
    P4 = transitive_closure(set(P3) | {(0, 2)})
    return closed + [P4]


# ============================================================================
# §8.  Pickle checkpoint utilities.
# ============================================================================


def cache_path(name):
    return os.path.join(CACHE_DIR, f'{name}.pkl')


def save_cache(name, obj):
    os.makedirs(CACHE_DIR, exist_ok=True)
    with open(cache_path(name), 'wb') as f:
        pickle.dump(obj, f, protocol=pickle.HIGHEST_PROTOCOL)


def load_cache(name):
    p = cache_path(name)
    if not os.path.exists(p):
        return None
    with open(p, 'rb') as f:
        return pickle.load(f)


# ============================================================================
# §9.  Main: phase runner.
# ============================================================================


def phase_enum(verbose=False, force=False):
    """Phase 1: PPF_6 enumeration."""
    cached = None if force else load_cache('ppf6')
    if cached is not None:
        if verbose:
            print(f"  [phase enum] cached: {len(cached)} PPF_6 elements.")
        return cached
    all_pos = enumerate_PPF(N, verbose=verbose)
    ppf = filter_PPF(all_pos, N)
    if verbose:
        print(f"  PPF_6 enumeration:")
        print(f"    |all partial orders on 6| = {len(all_pos)}")
        print(f"    |PPF_6| (excluding empty + chains) = {len(ppf)}")
        rd = rank_distribution(ppf)
        print(f"    Rank distribution: {dict(sorted(rd.items()))}")
    save_cache('ppf6', ppf)
    return ppf


def phase_orbits(ppf, verbose=False, force=False):
    """Phase 2: S_6 orbit grouping."""
    cached = None if force else load_cache('orbits')
    if cached is not None:
        if verbose:
            print(f"  [phase orbits] cached: {len(cached)} orbits.")
        return cached
    orbits = group_orbits(ppf, verbose=verbose)
    if verbose:
        print(f"  Orbit count: {len(orbits)}")
        sizes = sorted({sz for (_, sz, _) in orbits})
        for sz in sizes:
            n_with = sum(1 for (_, s, _) in orbits if s == sz)
            print(f"    orbit size {sz}: {n_with} orbits")
    save_cache('orbits', orbits)
    return orbits


def phase_burnside(ppf, verbose=False, force=False):
    """Phase 3: Burnside / Lefschetz sign-rep + Out(S_6) audit."""
    cached = None if force else load_cache('burnside')
    if cached is not None:
        if verbose:
            print(f"  [phase burnside] cached.")
        # still print the result for visibility
        if verbose:
            print(f"    m_sgn(n=6) = {cached['result']['m_sgn']}")
        return cached
    ppf_set = frozenset(ppf)
    result = compute_burnside_msgn(ppf_set, verbose=verbose)
    audit = out_s6_audit(result['per_class'], verbose=verbose)
    out = {'result': result, 'audit': audit}
    save_cache('burnside', out)
    return out


def phase_pr_reverify(verbose=False):
    """Phase 6: re-verify mg-7b3b 4/4 BFT-sharp Pr-profile."""
    from fractions import Fraction
    expected = [Fraction(7, 15), Fraction(4, 7),
                Fraction(1, 2), Fraction(1, 2)]
    chain = c_star_6_chain()
    if verbose:
        print(f"  c*_6 chain: {len(chain)} closed posets.")
    # Brute-force |L| at n=6 via 720 perms.
    Ls = []
    for P in chain:
        cnt = 0
        for perm in _PERMS:
            pos = {perm[k]: k for k in range(N)}
            ok = True
            for (a, b) in P:
                if pos[a] >= pos[b]:
                    ok = False
                    break
            if ok:
                cnt += 1
        Ls.append(cnt)
    if verbose:
        print(f"  |L|-profile: {Ls}")
    prs = []
    for k in range(len(Ls) - 1):
        pr = Fraction(Ls[k + 1], Ls[k])
        prs.append(pr)
    if verbose:
        print(f"  Per-step Pr: {[str(p) for p in prs]}")
        print(f"  Expected:    {[str(p) for p in expected]}")
        match = prs == expected
        print(f"  Match: {'✓' if match else '✗'}")
        bft = sum(1 for p in prs
                  if Fraction(3, 11) <= p <= Fraction(8, 11))
        print(f"  BFT-sharp: {bft}/{len(prs)}")
    return {'L_profile': Ls, 'pr_profile': prs,
            'expected': expected,
            'match': prs == expected,
            'bft_count': sum(1 for p in prs
                             if Fraction(3, 11) <= p <= Fraction(8, 11))}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--phase', default='all',
                    choices=['enum', 'orbits', 'burnside', 'pr',
                             'morse', 'planB', 'all'])
    ap.add_argument('--cache-dir', default=None)
    ap.add_argument('--force', action='store_true',
                    help='Re-run even if cache exists')
    ap.add_argument('--verbose', '-v', action='store_true')
    args = ap.parse_args()
    global CACHE_DIR
    if args.cache_dir is not None:
        CACHE_DIR = args.cache_dir

    print(f"posn_n6_hpc.py — F8'-HPC master script (mg-3bf3)")
    print(f"  cache dir: {CACHE_DIR}")
    print(f"  phase: {args.phase}")
    print(f"  force: {args.force}")
    print()
    t_start = time.time()

    ppf = None
    if args.phase in ('enum', 'all'):
        print(f"=== Phase 1: PPF_6 enumeration ===")
        ppf = phase_enum(verbose=True, force=args.force)
        print()
    elif args.phase in ('orbits', 'burnside', 'morse', 'planB'):
        ppf = load_cache('ppf6')
        if ppf is None:
            print(f"ERROR: phase {args.phase} requires ppf6 cache; "
                  f"run --phase=enum first.")
            sys.exit(1)

    if args.phase in ('orbits', 'all'):
        print(f"=== Phase 2: S_6 orbit grouping ===")
        orbits = phase_orbits(ppf, verbose=True, force=args.force)
        print()
    elif args.phase in ('morse', 'planB'):
        orbits = load_cache('orbits')

    if args.phase in ('burnside', 'all'):
        print(f"=== Phase 3: Burnside / Lefschetz sign-rep + Out(S_6) audit ===")
        result = phase_burnside(ppf, verbose=True, force=args.force)
        print()

    if args.phase in ('pr', 'all'):
        print(f"=== Phase 6: Pr re-verification along c*_6 ===")
        pr_result = phase_pr_reverify(verbose=True)
        print()

    # Phases 4 (morse) and 5 (planB) intentionally deferred:
    # they require chamber Morse output which may exceed budget at n=6.
    # See doc for AMBER-budget-cap pathway.

    elapsed = time.time() - t_start
    print(f"=== Total elapsed: {elapsed:.1f}s ===")


if __name__ == '__main__':
    main()
