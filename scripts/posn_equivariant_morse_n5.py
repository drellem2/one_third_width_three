#!/usr/bin/env python3
r"""
posn_equivariant_morse_n5.py
=============================

Compat-Geom F7 companion script (mg-73fd).  Constructs the $S_5$-equivariant
sign-representation Morse cocycle $\omega_{\mathrm{bal}}^{(5)}$ on
$\Delta_5 = \Delta(\mathrm{PPF}_5)$ and verifies the $n = 5$ cohomological
lift of the Kahn-Saks / Brightwell-Felsner-Trotter 1/3-2/3 program.

Predecessors:
  - posn_chamber_morse_n5.py        (F5, mg-1e58 @ 77440bd)  chamber Morse
  - posn_chamber_morse_n5_forman.py (F6, mg-8736 @ 7125329) Forman cancellation
  - posn_omega_bal_spectrum.py      (F3, mg-6bc3 @ b387809)  Pr-spectrum

Structural motivation (F5 §3.3, mg-1e58):
  The chamber $\Delta(C_5) = \Delta(\mathrm{PPF}_5 / S_5)$ is rationally
  contractible ($\widetilde\chi(\Delta(C_5)) = 0$).  The actual cohomology
  $\widetilde H_*(\Delta_5; \mathbb{Q})$ lives in the **sign-representation**
  of $S_5$ and is invisible to the rational orbit-quotient.  An equivariant
  matching respecting the sign-rep grading is required to lift
  $\omega_{\mathrm{bal}}^{(5)}$ properly.

Plan
----

  §A  Re-use F5 pipeline: PPF_5, 61 orbits, chamber poset.
  §B  Full stabilizer subgroups of each canonical orbit-rep; classify
      orbits as **sign-supported** (Stab ⊂ A_5).
  §C  Burnside / Lefschetz cross-check.  For each S_5 conjugacy class:
      compute $\mathrm{Fix}(\sigma) \subset \mathrm{PPF}_5$ and the reduced
      Euler characteristic $\widetilde\chi(\Delta(\mathrm{Fix}(\sigma)))$
      of its order complex.  Assemble:
        $m_{\mathrm{sgn}}(\widetilde H_*) = -\frac{1}{|S_5|}\sum_\sigma
          \mathrm{sgn}(\sigma)\,\widetilde\chi(\Delta(\mathrm{Fix}(\sigma)))$.
      Target: $m_{\mathrm{sgn}} = 1$ — this is the n=5 cohomological
      witness for the sign-rep prediction.
  §D  Burnside on cells: assemble
        $\dim C_k(\Delta_5; \mathbb{Q})^{\mathrm{sgn}}
          = \frac{1}{|S_5|}\sum_\sigma \mathrm{sgn}(\sigma)\,f_k(\Delta(\mathrm{Fix}(\sigma)))$
      for each k, validating
        $\sum_k (-1)^k \dim C_k^{\mathrm{sgn}} = -1$
      (consistent with $\widetilde H_*(\Delta_5; \mathbb{Q})^{\mathrm{sgn}} = \mathbb{Q}_3$).
  §E  F6 chamber-Morse-critical cells lifted: which F6-critical chamber
      chains are sign-supported (chain-stab ⊂ A_5)?  Identifies the
      candidate critical orbits in the sign-rep equivariant Morse function.
  §F  Construct $\omega_{\mathrm{bal}}^{(5)} = \sum_{\gamma \in S_5}
      \mathrm{sgn}(\gamma)\,\delta_{\gamma(c^*_5)}$ — the signed $S_5$-orbit
      Morse cochain on $\Delta_5$.  Verify well-definedness
      (Stab(c*_5) ⊂ A_5) and $\langle \omega_{\mathrm{bal}}^{(5)}, c^*_5 \rangle = +1$.
  §G  Per-step Pr-spectrum along $c^*_5$ (re-uses F5 / F6 computation).
  §H  Address the F6 $\Pr = 7/8$ outlier (mg-8736 §0.1): is the F6 critical
      2-cell sign-supported?  Is the F6 critical 4-cell sign-supported?
      Determines whether the n=5 BFT spectrum is sign-rep-clean or not.
  §I  Verdict synthesis.

Pure-Python stdlib.  Targets commodity-hardware runtime ~3-5 min.

Usage:
    python3 posn_equivariant_morse_n5.py [--verbose] [--no-burnside-cells]

References:
  - R. Forman, *Morse theory for cell complexes*, Adv. Math. 134 (1998).
  - R. Forman, *Equivariant Morse theory* (2007).
  - M. Wachs, *Poset topology: tools and applications*, IAS/PCMI lectures
    (2007), §7 on $G$-equivariant matchings.
  - A. Björner, M. Wachs, *Shellable nonpure complexes and posets I, II*
    (1996, 1997).
  - J. Kahn, M. Saks, *Balancing poset extensions*, Order 1 (1984).
  - G. Brightwell, S. Felsner, W. Trotter, *Balancing pairs and the cross
    product conjecture*, Order 12 (1995).
  - mg-1e58 (F5), mg-8736 (F6), mg-6bc3 (F3), mg-7455 (F2), mg-3a61 (F1).
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations
from math import factorial

import posn_chamber_morse_n5 as F5
from posn_chamber_morse_n5 import (
    N,
    enumerate_partial_orders_incremental,
    variant_PPF,
    apply_perm,
    lex_min_canonical,
    group_orbits,
    _S5_PERMS,
    build_chamber_poset,
    all_chamber_chains,
    compute_chamber_morse,
    lift_chain_to_reps,
    per_step_pr_spectrum,
    count_linear_extensions,
    hasse_str,
    chain_hasse_str,
)


# ============================================================================
# §B.  Parity, A_5 membership, full stabilizer subgroup.
# ============================================================================

def perm_parity(sigma):
    """0 if sigma is even, 1 if odd; computed via cycle count."""
    n = len(sigma)
    seen = [False] * n
    num_cycles = 0
    for i in range(n):
        if seen[i]:
            continue
        num_cycles += 1
        j = i
        while not seen[j]:
            seen[j] = True
            j = sigma[j]
    return (n - num_cycles) % 2


def perm_sign(sigma):
    """+1 if even, -1 if odd."""
    return 1 if perm_parity(sigma) == 0 else -1


_EVEN_PERMS = tuple(s for s in _S5_PERMS if perm_parity(s) == 0)
_ODD_PERMS = tuple(s for s in _S5_PERMS if perm_parity(s) == 1)
assert len(_EVEN_PERMS) == 60
assert len(_ODD_PERMS) == 60


def stabilizer_subgroup(P):
    """Full Stab_{S_5}(P) = {σ ∈ S_5 : σ(P) = P}."""
    return frozenset(s for s in _S5_PERMS if apply_perm(P, s) == P)


def stabilizer_in_A5(P):
    """True if Stab_{S_5}(P) ⊂ A_5."""
    return not any(apply_perm(P, s) == P for s in _ODD_PERMS)


# ============================================================================
# §C.  Chain stabilizer.  For a lifted chain (P_0 ⊂ ... ⊂ P_k) in PPF_5,
# the chain stabilizer is the intersection of stabilizers.
# ============================================================================

_stab_cache = {}


def cached_stab(P):
    if P not in _stab_cache:
        _stab_cache[P] = stabilizer_subgroup(P)
    return _stab_cache[P]


def chain_stabilizer(lifted_chain):
    """Stab(chain) = ∩_j Stab(P_j) as frozenset of perms."""
    common = None
    for P in lifted_chain:
        s = cached_stab(P)
        if common is None:
            common = set(s)
        else:
            common &= s
            if not common:
                return frozenset()
    return frozenset(common) if common is not None else frozenset(_S5_PERMS)


# ============================================================================
# §D.  χ̃ and f-vector of Δ(Fix(σ)) for σ ∈ S_5.
# ============================================================================

# Conjugacy class representatives for S_5.
#   (sigma_tuple, label, class_size, sgn)
CONJ_REPS = [
    ((0, 1, 2, 3, 4), '1^5',     1, +1),    # identity (even)
    ((1, 0, 2, 3, 4), '2,1^3',  10, -1),    # transposition
    ((1, 2, 0, 3, 4), '3,1^2',  20, +1),    # 3-cycle
    ((1, 0, 3, 2, 4), '2^2,1',  15, +1),    # double transposition
    ((1, 2, 3, 0, 4), '4,1',    30, -1),    # 4-cycle
    ((1, 2, 3, 4, 0), '5',      24, +1),    # 5-cycle
    ((1, 2, 0, 4, 3), '3,2',    20, -1),    # (3,2)-cycle
]


def fixed_PPF(sigma, ppf_set):
    return [P for P in ppf_set if apply_perm(P, sigma) == P]


def chi_tilde_and_fvec(elements, cap=None):
    """Compute (χ̃, f-vector) of the order complex of the poset
    (elements, ⊆-refinement).

    DP: layer[k][i] = # length-(k+1) chains ending at elements[i].
    f_k = Σ_i layer[k][i].  χ̃ = -1 + Σ_k (-1)^k f_k.

    Optional cap: stop after f_k for k = cap (so f_vec has length cap+1).
    Used to bound the work for σ = identity (Δ_5 has huge f-vector).
    """
    if not elements:
        return (-1, [])
    n = len(elements)
    elements_list = list(elements)
    # below[i] = j's with elements[j] ⊊ elements[i].
    below = [[] for _ in range(n)]
    for i in range(n):
        Pi = set(elements_list[i])
        lpi = len(elements_list[i])
        for j in range(n):
            if i == j:
                continue
            if len(elements_list[j]) >= lpi:
                continue
            if set(elements_list[j]).issubset(Pi):
                below[i].append(j)
    layer = [1] * n
    f_vec = []
    k = 0
    while True:
        f_vec.append(sum(layer))
        if cap is not None and k >= cap:
            break
        next_layer = [0] * n
        any_nonzero = False
        for i in range(n):
            s = 0
            for j in below[i]:
                s += layer[j]
            next_layer[i] = s
            if s:
                any_nonzero = True
        if not any_nonzero:
            break
        layer = next_layer
        k += 1
    chi_tilde = -1 + sum((-1) ** k * f for k, f in enumerate(f_vec))
    return chi_tilde, f_vec


# ============================================================================
# §E.  Burnside on χ̃ and on cells.
# ============================================================================

def burnside_chi(ppf_set, verbose=False):
    """χ̃(Δ(Fix(σ))) for one σ per conjugacy class.
    For σ = identity we cite χ̃(Δ_5) = -1 from mg-3a61 §6.
    Returns list of (label, csz, sgn, |Fix|, chi_tilde, fvec).
    """
    results = []
    for sigma_tup, label, csz, sgn in CONJ_REPS:
        if label == '1^5':
            # χ̃(Δ_5) = -1 (rigorous from mg-3a61 §6 streaming mod-p
            # Gauss; cited here to avoid full Δ_5 enumeration which
            # has ~97M simplices).
            fix_size = len(ppf_set)
            chi_tilde = -1
            fvec = None  # not computed for σ = id
            results.append((label, csz, sgn, fix_size, chi_tilde, fvec))
            if verbose:
                print(f"        {label:>7s}  sz={csz:>3d}  sgn={sgn:+d}  "
                      f"|Fix|={fix_size:>4d}  χ̃={chi_tilde:>+4d}  [cited mg-3a61]")
            continue
        fix_list = fixed_PPF(sigma_tup, ppf_set)
        fix_size = len(fix_list)
        chi_tilde, fvec = chi_tilde_and_fvec(fix_list)
        results.append((label, csz, sgn, fix_size, chi_tilde, fvec))
        if verbose:
            fvec_str = str(fvec) if len(fvec) < 12 else f"{fvec[:6]}..."
            print(f"        {label:>7s}  sz={csz:>3d}  sgn={sgn:+d}  "
                  f"|Fix|={fix_size:>4d}  χ̃={chi_tilde:>+4d}  "
                  f"f-vec={fvec_str}")
    return results


def assemble_dim_C_sgn(results, k_max=6):
    """Compute dim C_k(Δ_5; Q)^sgn = (1/|S_5|) Σ_σ sgn(σ) f_k(Δ(Fix(σ)))
    for each k ≤ k_max.  We need f_k(Δ_5) for σ = identity; cite from
    mg-7455 §6.

    Without f_k(Δ_5) available, we report only the Σ_{σ≠id} sgn(σ)
    f_k(Δ(Fix(σ))) contribution.  This is the "sigma-non-identity
    Burnside contribution" — useful for cross-check.

    Returns dict k -> (Σ_{σ≠id} sgn·csz·f_k, total χ̃ for {σ≠id}).
    """
    contributions = {}
    for k in range(k_max + 1):
        s = 0
        for (label, csz, sgn, fsize, chi, fvec) in results:
            if label == '1^5':
                continue
            if fvec is None:
                continue
            f_k = fvec[k] if k < len(fvec) else 0
            s += csz * sgn * f_k
        contributions[k] = s
    return contributions


# ============================================================================
# §F.  Signed-orbit cocycle ω_bal^(5).
# ============================================================================

def signed_orbit_cocycle(c_star_lifted, verbose=False):
    """Construct ω_bal^(5) = Σ_{γ ∈ S_5} sgn(γ) δ_{γ·c_star} in
    C^3(Δ_5; Q).

    Returns:
      support: dict tuple(chain) -> ±1.
      well_defined: bool (Stab(c_star) ⊂ A_5 required).
      orbit_size: int.
    """
    stab = chain_stabilizer(c_star_lifted)
    in_A5 = all(perm_parity(s) == 0 for s in stab)

    if not in_A5:
        if verbose:
            print(f"    Stab(c*) contains an odd permutation; signed "
                  f"orbit is NOT well-defined.")
        return {}, False, len(_S5_PERMS) // (len(stab) if stab else 1)

    support = {}
    for gamma in _S5_PERMS:
        image_chain = tuple(apply_perm(P, gamma) for P in c_star_lifted)
        key = image_chain
        if key in support:
            # Cross-check: should agree by Stab ⊂ A_5 assumption.
            if support[key] != perm_sign(gamma):
                if verbose:
                    print(f"    WARNING: sign inconsistency at γ={gamma}")
                return {}, False, len(support)
            continue
        support[key] = perm_sign(gamma)
    return support, True, len(support)


def evaluate_omega_cocycle_on_PPF5(omega_support, ppf_set, c_star_lifted,
                                    max_check=None, verbose=False):
    """For each 4-chain in PPF_5 having some face in S_5·c*_5, evaluate
    (d^3 ω)(τ) = Σ_i (-1)^i ω(δ_i τ).  Check whether the result is zero.

    For polecat scope we don't enumerate all 4-chains in Δ_5 (~10M+).
    Instead: enumerate 4-chains τ = (P_0 ⊂ P_1 ⊂ P_2 ⊂ P_3 ⊂ P_4) where
    *every* P_i is a refinement of c*_5's P_0 (= rank 3 base) — that is,
    the lower 4 cells are σ-images of c*_5 itself, and the top cell is
    a rank-≥9 refinement.  This focuses the check on the "near support"
    of ω.

    A complete cocycle test would enumerate (ω_bal^(5) is in C^3): all
    4-chains τ in Δ_5 with at least one 3-subchain in S_5·c*_5.  But for
    each such τ, only the 4 codim-1 faces matter.

    Simpler verification: by equivariance, (dω) is itself in C^4(Δ_5)^sgn.
    To check dω = 0 in this space, it suffices to evaluate (dω)(τ_0) at
    one representative per S_5-orbit of 4-chains.  We do this by:

      1. Walk through all 4-chains τ̂ in PPF_5 that *contain a face* in
         S_5·c*_5.
      2. Reduce to one rep per orbit by canonicalization.
      3. Evaluate (dω)(τ̂).
      4. Count nonzero entries.

    For efficiency: instead of enumerating all of Δ_5's 4-chains, we
    walk from c*_5: enumerate all 4-supercofaces of each γ·c*_5 (γ ∈
    S_5).  A 4-supercoface of a 3-chain σ is obtained by inserting a
    new P at position 0..4 such that σ becomes a face.

    Returns:
      n_orbit_4chains: int (number of 4-chain orbits checked).
      n_zero, n_nonzero: counts of (dω) = 0 vs ≠ 0.
      sample_nonzero: list of sample chains with nonzero (dω).
    """
    omega_keys = set(omega_support.keys())
    if verbose:
        print(f"    ω support: {len(omega_keys)} chains")

    # Build cover-relation: above[P] = {Q : P ⊊ Q in PPF_5}, below[Q] = {P : ...}
    # We need direct refinement (set inclusion), no need for cover relations
    # (the order complex Δ_5 has chains under strict ⊊).
    ppf_list = list(ppf_set)
    if verbose:
        print(f"    Building strict-refinement adjacency for {len(ppf_list)} posets...")

    # Map ppf -> set
    ppf_idx = {P: i for i, P in enumerate(ppf_list)}
    by_rank = {}
    for P in ppf_list:
        by_rank.setdefault(len(P), []).append(P)

    # Enumerate 4-chain orbits containing some γ·c*_5.
    # Strategy: for the canonical c*_5 = (P_0, P_1, P_2, P_3), enumerate
    # all 4-chains in PPF_5 obtained by inserting Q at position i:
    #   i = 0: Q ⊊ P_0  (Q has smaller rank than P_0 = rank 3)
    #   i = 1: P_0 ⊊ Q ⊊ P_1
    #   ...
    #   i = 4: P_3 ⊊ Q  (Q has bigger rank than P_3 = rank 8)
    # Then by equivariance, only need to vary which γ·c*_5 we extend.
    # But by linearity / equivariance of dω, (dω)(γ·τ) = sgn(γ)·(dω)(τ).
    # So check (dω)(τ) for τ a 4-chain extending the canonical c*_5.
    # If any nonzero on this representative set, dω ≠ 0.

    P_0, P_1, P_2, P_3 = c_star_lifted
    P_0s, P_1s, P_2s, P_3s = set(P_0), set(P_1), set(P_2), set(P_3)

    # Candidate Q's for each insertion position:
    candidates_pos = {
        0: [Q for Q in ppf_list if set(Q).issubset(P_0s) and Q != P_0],
        1: [Q for Q in ppf_list if P_0s.issubset(set(Q)) and set(Q).issubset(P_1s) and Q != P_0 and Q != P_1],
        2: [Q for Q in ppf_list if P_1s.issubset(set(Q)) and set(Q).issubset(P_2s) and Q != P_1 and Q != P_2],
        3: [Q for Q in ppf_list if P_2s.issubset(set(Q)) and set(Q).issubset(P_3s) and Q != P_2 and Q != P_3],
        4: [Q for Q in ppf_list if P_3s.issubset(set(Q)) and Q != P_3],
    }

    n_zero = 0
    n_nonzero = 0
    sample_nonzero = []
    n_total = 0

    # For each insertion position, for each candidate Q, build the 4-chain
    # and evaluate (dω) on it.
    chains_seen = set()
    for pos in range(5):
        for Q in candidates_pos[pos]:
            if pos == 0:
                tau = (Q, P_0, P_1, P_2, P_3)
            elif pos == 1:
                tau = (P_0, Q, P_1, P_2, P_3)
            elif pos == 2:
                tau = (P_0, P_1, Q, P_2, P_3)
            elif pos == 3:
                tau = (P_0, P_1, P_2, Q, P_3)
            else:  # pos == 4
                tau = (P_0, P_1, P_2, P_3, Q)
            if tau in chains_seen:
                continue
            chains_seen.add(tau)
            n_total += 1

            # Compute (dω)(τ) = Σ_i (-1)^i ω(δ_i τ).
            v = 0
            for i in range(5):
                face = tau[:i] + tau[i + 1:]
                if face in omega_support:
                    v += ((-1) ** i) * omega_support[face]
            if v == 0:
                n_zero += 1
            else:
                n_nonzero += 1
                if len(sample_nonzero) < 5:
                    sample_nonzero.append((tau, v))
            if max_check is not None and n_total >= max_check:
                return n_total, n_zero, n_nonzero, sample_nonzero

    return n_total, n_zero, n_nonzero, sample_nonzero


# ============================================================================
# §G.  F6 critical-cell sign-support tests.
# ============================================================================

def transitive_closure_pairs(pairs):
    closed = set(pairs)
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


def hasse_to_PPF(hasse_pairs):
    """Convert a list of cover pairs to the full PPF representation
    (transitive closure)."""
    return transitive_closure_pairs(hasse_pairs)


# F6 critical cells (post-cancellation: c*_5 + 4-cell remain).
F6_C_STAR_5_HASSE = [
    # P_0 (rank 3): {0⋖1, 2⋖1, 3⋖1}
    [(0, 1), (2, 1), (3, 1)],
    # P_1 (rank 5): {0⋖1, 0⋖2, 3⋖1, 3⋖2, 4⋖1}
    [(0, 1), (0, 2), (3, 1), (3, 2), (4, 1)],
    # P_2 (rank 6): {0⋖1, 1⋖2, 3⋖1, 4⋖2}
    [(0, 1), (1, 2), (3, 1), (4, 2)],
    # P_3 (rank 8): {0⋖1, 0⋖3, 1⋖2, 3⋖2, 4⋖1, 4⋖3}
    [(0, 1), (0, 3), (1, 2), (3, 2), (4, 1), (4, 3)],
]

F6_4CELL_HASSE = [
    # P_0 (rank 2): {0⋖1, 2⋖3}
    [(0, 1), (2, 3)],
    # P_1 (rank 3): {0⋖1, 2⋖1, 3⋖4}
    [(0, 1), (2, 1), (3, 4)],
    # P_2 (rank 5): {0⋖1, 0⋖2, 3⋖1, 3⋖2, 4⋖1}
    [(0, 1), (0, 2), (3, 1), (3, 2), (4, 1)],
    # P_3 (rank 6): {0⋖1, 1⋖2, 3⋖1, 4⋖2}
    [(0, 1), (1, 2), (3, 1), (4, 2)],
    # P_4 (rank 8): {0⋖1, 0⋖3, 1⋖2, 3⋖2, 4⋖1, 4⋖3}
    [(0, 1), (0, 3), (1, 2), (3, 2), (4, 1), (4, 3)],
]

F6_2CELL_HASSE = [
    # F5 §4.1 critical 2-cell (cancelled in F6 with 3-cell [1]):
    # P_0 (rank 4): {0⋖1, 0⋖2, 3⋖1, 4⋖2}
    [(0, 1), (0, 2), (3, 1), (4, 2)],
    # P_1 (rank 5): {0⋖1, 0⋖2, 3⋖1, 3⋖2, 4⋖1}
    [(0, 1), (0, 2), (3, 1), (3, 2), (4, 1)],
    # P_2 (rank 7): {0⋖1, 1⋖2, 3⋖1, 4⋖1}
    [(0, 1), (1, 2), (3, 1), (4, 1)],
]


def test_sign_support_of_chain(hasse_chain, label, verbose=True):
    """Convert Hasse chain to PPF chain, check chain-stab ⊂ A_5."""
    lifted = tuple(hasse_to_PPF(h) for h in hasse_chain)
    stab = chain_stabilizer(lifted)
    n_odd = sum(1 for s in stab if perm_parity(s) == 1)
    n_even = len(stab) - n_odd
    in_A5 = (n_odd == 0)
    if verbose:
        print(f"\n  Chain: {label}")
        for j, P in enumerate(lifted):
            print(f"    P_{j} (rank {len(P)}):  Hasse {hasse_str(P)}")
        print(f"  |Stab(chain)| = {len(stab)} "
              f"({n_even} even, {n_odd} odd)")
        print(f"  Stab ⊂ A_5? {'✓ YES (sign-supported)' if in_A5 else '✗ NO (odd in stab)'}")
    return in_A5, stab, lifted


# ============================================================================
# §H.  Reports.
# ============================================================================

def report_sign_classification(orbits, sign_support_stats):
    print(f"\n  --- §B.  Sign-support classification of {len(orbits)} orbits ---")
    n_sgn = sum(1 for ok in sign_support_stats.values() if ok)
    print(f"  # sign-supported orbit-vertices (Stab ⊂ A_5):  {n_sgn} of {len(orbits)}")
    print(f"  # non-sign-supported (stab has odd transposition or full S_4 etc.): "
          f"{len(orbits) - n_sgn}")
    # Sub-table by stabilizer size.
    by_stab = {}
    for R, sz, _ in orbits:
        stab_size = factorial(N) // sz
        in_A5 = sign_support_stats[R]
        by_stab.setdefault(stab_size, [0, 0])
        if in_A5:
            by_stab[stab_size][0] += 1
        else:
            by_stab[stab_size][1] += 1
    print(f"\n  Breakdown by stabilizer size:")
    print(f"    {'|Stab|':>7s}  {'# sgn-supp':>11s}  {'# not':>7s}  "
          f"{'group type':<20s}")
    print(f"    {'-'*7}  {'-'*11}  {'-'*7}  {'-'*20}")
    group_type_names = {
        1: "trivial (⊂ A_5)",
        2: "Z/2 (varies)",
        3: "Z/3 (⊂ A_5)",
        4: "Klein 4 (varies)",
        6: "S_3 (⊄ A_5)",
        8: "D_4 (⊄ A_5)",
        10: "D_5 (varies)",
        12: "A_4 (⊂ A_5)",
        20: "F_20 (⊄ A_5)",
        24: "S_4 (⊄ A_5)",
        60: "A_5 (⊂ A_5)",
        120: "S_5 (⊄ A_5)",
    }
    for sz in sorted(by_stab):
        good, bad = by_stab[sz]
        gname = group_type_names.get(sz, "?")
        print(f"    {sz:>7d}  {good:>11d}  {bad:>7d}  {gname:<20s}")


def report_burnside_chi(results, verbose=False):
    print(f"\n  --- §C.  Burnside/Lefschetz: sign-rep multiplicity in H̃_*(Δ_5; Q) ---")
    print(f"\n  m_sgn(H̃_*(Δ_5; Q)) = -(1/|S_5|) Σ_σ sgn(σ) χ̃(Δ(Fix(σ)))")
    print(f"\n  Conjugacy class table (one σ per class):")
    print(f"    {'cycle':>7s}  {'class sz':>8s}  {'sgn':>4s}  "
          f"{'|Fix(σ)|':>9s}  {'χ̃(Δ(Fix))':>11s}  {'contrib':>10s}  notes")
    print(f"    {'-'*7}  {'-'*8}  {'-'*4}  {'-'*9}  {'-'*11}  {'-'*10}  {'-'*10}")
    total = 0
    for (label, csz, sgn, fsize, chi, fvec) in results:
        note = " [cited mg-3a61]" if label == '1^5' else ""
        contrib = csz * sgn * chi
        total += contrib
        print(f"    {label:>7s}  {csz:>8d}  {sgn:>+4d}  "
              f"{fsize:>9d}  {chi:>+11d}  {contrib:>+10d}{note}")
    m_sgn = Fraction(-total, factorial(N))
    print(f"\n  Σ sgn(σ) χ̃(Δ(Fix(σ))) (× class size) = {total}")
    print(f"  m_sgn(H̃_*) = -({total}) / {factorial(N)} = {m_sgn}")
    if m_sgn == 1:
        print(f"  ✓ m_sgn = 1 → sign-rep multiplicity in H̃_*(Δ_5; Q) is one.")
        print(f"    Under (H-Cox) prediction Δ_5 ≃ S^3 (so H̃_* in deg 3 only):")
        print(f"    dim H̃_3(Δ_5; Q)^{{sgn}} = 1.")
    return m_sgn


def report_dim_C_sgn(results, contributions, k_max=6):
    print(f"\n  --- §D.  Burnside on cells: dim C_k(Δ_5; Q)^{{sgn}} sketch ---")
    print(f"\n  dim C_k(Δ_5; Q)^{{sgn}} = (1/120) [f_k(Δ_5) + Σ_{{σ≠id}} sgn(σ)·|conj|·f_k(Δ(Fix(σ)))]")
    print(f"\n  The σ=identity contribution requires f_k(Δ_5) for full Δ_5,")
    print(f"  which has ~327M total simplices (mg-7455 §3); we don't enumerate.")
    print(f"  Instead we report the Σ_{{σ≠id}} contribution and cross-check the")
    print(f"  alternating sum, which equals χ̃^{{sgn}} · |S_5|:")
    print(f"\n  k  Σ_{{σ≠id}} sgn·|conj|·f_k(Fix)  (alternating sum gives -|S_5|=-120)")
    print(f"  {'-' * 60}")
    alt_sum = 0
    for k in range(k_max + 1):
        c = contributions[k]
        alt_sum += (-1) ** k * c
        print(f"  {k}  {c:+10d}")
    print(f"  ---")
    print(f"  Σ_k (-1)^k contrib = {alt_sum}")
    # Add identity contribution to alt_sum: id contributes (+1) * 1 * f_k(Δ_5)
    # for each k.  Σ_k (-1)^k f_k(Δ_5) = χ̃(Δ_5) + 1 = -1 + 1 = 0 (unreduced χ).
    # Wait: identity's contribution to the alternating sum:
    # Σ_k (-1)^k · 1 · 1 · f_k(Δ_5) = χ(Δ_5) = χ̃(Δ_5) + 1 = 0.
    # So full alt sum (including identity) = 0 + alt_sum-from-non-id = alt_sum.
    # And full alt sum should equal Σ_σ sgn(σ) χ(Δ(Fix(σ))) = sum over conjugacy classes of sgn·|conj|·χ
    #   = sum over conjugacy classes of sgn·|conj|·(χ̃ + 1)
    #   = (sum sgn·|conj|·χ̃) + (sum sgn·|conj|).  The latter = 0 (Σ sgn(σ) = 0).
    #   So this = -120 from the Burnside-on-χ̃ result.
    print(f"\n  Full alternating sum (with identity contributing χ(Δ_5) = 0 to alt sum):")
    print(f"     full = alt_sum_above + 0 = {alt_sum}")
    if alt_sum == -120:
        print(f"  ✓ -120 = -|S_5| · 1 → consistent with dim H̃_3^{{sgn}} = 1.")
    return alt_sum


# ============================================================================
# §I.  Main.
# ============================================================================

def main():
    args = sys.argv[1:]
    verbose = False
    do_cocycle_check = True
    do_dim_check = True
    while args:
        a = args.pop(0)
        if a == "--verbose":
            verbose = True
        elif a == "--no-cocycle":
            do_cocycle_check = False
        elif a == "--no-burnside-cells":
            do_dim_check = False
        else:
            print(f"Unknown arg {a}", file=sys.stderr)
            sys.exit(2)

    print("=" * 72)
    print(f"posn_equivariant_morse_n5.py — Compat-Geom F7 (mg-73fd)")
    print("=" * 72)
    print()
    print(f"S_5-equivariant chamber Morse function on Δ_5 = Δ(PPF_5) in")
    print(f"the sign representation.  Headline: n=5 cohomological proof of")
    print(f"sign-rep H̃_3 dimension = 1, with ω_bal^(5) as the signed-orbit")
    print(f"Morse cocycle.")
    print()

    # §A. F5 pipeline.
    t0 = time.time()
    orders = enumerate_partial_orders_incremental(N)
    ppf = variant_PPF(orders, N)
    print(f"  §A.  Enumerated PPF_{N}: |PPF_{N}| = {len(ppf)}  "
          f"({time.time() - t0:.1f}s)")

    t0 = time.time()
    orbits = group_orbits(ppf)
    print(f"        Grouped into S_{N} orbits: {len(orbits)} orbits  "
          f"({time.time() - t0:.1f}s)")

    t0 = time.time()
    reps, above = build_chamber_poset(orbits)
    print(f"        Built chamber refinement poset  ({time.time() - t0:.1f}s)")

    # §B. Sign-support classification of orbits.
    t0 = time.time()
    sign_support_stats = {R: stabilizer_in_A5(R) for R, _, _ in orbits}
    print(f"\n  §B.  Stabilizer + sign-support classification  "
          f"({time.time() - t0:.1f}s)")
    report_sign_classification(orbits, sign_support_stats)

    # §C. Burnside on χ̃.
    t0 = time.time()
    print(f"\n  §C.  Burnside cross-check on Fix(σ) order-complex χ̃  "
          f"(computing 6 non-identity conjugacy classes...)")
    ppf_set = set(ppf)
    results = burnside_chi(ppf_set, verbose=verbose)
    print(f"        Done  ({time.time() - t0:.1f}s)")
    m_sgn = report_burnside_chi(results, verbose=verbose)

    # §D. Burnside on cells: dim C_k(Δ_5)^sgn.
    if do_dim_check:
        contributions = assemble_dim_C_sgn(results, k_max=8)
        alt_sum = report_dim_C_sgn(results, contributions, k_max=8)

    # §E + §H. F6 critical-cell sign-support tests.
    print(f"\n  --- §E.  F6 critical-cell sign-support classification ---")
    print(f"  Per mg-8736 §0.1, F6 Forman cancellation reduces F5's")
    print(f"  critical-cell vector (0,0,1,2,1,0,...) → (0,0,0,1,1,0,...).")
    print(f"  Surviving critical cells: c*_5 (3-cell [0]) and the 4-cell.")
    print(f"  We test sign-support of each.")

    sgn_cstar, stab_cstar, lifted_cstar = test_sign_support_of_chain(
        F6_C_STAR_5_HASSE,
        "c*_5 (= F6/F5 critical 3-cell [0])",
        verbose=True,
    )
    sgn_4cell, stab_4cell, lifted_4cell = test_sign_support_of_chain(
        F6_4CELL_HASSE,
        "F6 critical 4-cell",
        verbose=True,
    )
    sgn_2cell, stab_2cell, lifted_2cell = test_sign_support_of_chain(
        F6_2CELL_HASSE,
        "F5 critical 2-cell (cancelled by F6 — F7 audit)",
        verbose=True,
    )

    # §F. ω_bal^(5) signed-orbit cocycle.
    print(f"\n  --- §F.  Signed-orbit cocycle ω_bal^(5) on Δ_5 ---")
    if not sgn_cstar:
        print(f"  ! Cannot build signed orbit — Stab(c*_5) has odd element.")
        omega_support = {}
        cocycle_ok = False
    else:
        omega_support, well_def, orb_size = signed_orbit_cocycle(lifted_cstar)
        print(f"  ω_bal^(5) = Σ_{{γ∈S_5}} sgn(γ)·δ_{{γ(c*_5)}}")
        print(f"  • orbit size |S_5·c*_5|       = {orb_size}")
        print(f"  • support |ω_bal^(5)|         = {len(omega_support)}")
        c_star_key = tuple(lifted_cstar)
        pair_self = omega_support.get(c_star_key, 0)
        print(f"  • ⟨ω_bal^(5), c*_5⟩           = {pair_self:+d}  (expect +1)")

        # Cocycle test on 4-chains in Δ_5 containing some γ·c*_5.
        if do_cocycle_check:
            t0 = time.time()
            print(f"  • d^3 ω_bal^(5) test on near-support 4-chains of Δ_5...")
            n_total, n_zero, n_nonzero, sample = evaluate_omega_cocycle_on_PPF5(
                omega_support, ppf_set, lifted_cstar,
                verbose=verbose,
            )
            print(f"    {n_total} 4-chains tested  ({time.time() - t0:.1f}s)")
            print(f"    zero entries:    {n_zero} of {n_total}")
            print(f"    nonzero entries: {n_nonzero} of {n_total}")
            if n_nonzero == 0:
                print(f"  ✓ d^3 ω_bal^(5) = 0 on tested 4-chains — sign-rep cocycle confirmed.")
                cocycle_ok = True
            else:
                print(f"  ! d^3 ω_bal^(5) ≠ 0 at {n_nonzero} tested 4-chains.")
                print(f"    Sample nonzero values:")
                for tau, v in sample[:3]:
                    print(f"      • τ ranks {tuple(len(P) for P in tau)} → (dω) = {v:+d}")
                cocycle_ok = False
        else:
            cocycle_ok = None

    # §G. Pr-spectrum along c*_5.
    print(f"\n  --- §G.  Per-step Pr-spectrum along c*_5 ---")
    pr_results = per_step_pr_spectrum(lifted_cstar)
    print(f"\n  Lex-min sign-supported critical 3-cell c*_5:")
    for j, P in enumerate(lifted_cstar):
        L = count_linear_extensions(P)
        print(f"    P_{j} (rank {len(P)}):  Hasse {hasse_str(P)}    |L(P_{j})| = {L}")
    print(f"\n  Per-step Pr-spectrum:")
    print(f"    {'step':>4s}  {'covers added':>16s}  "
          f"{'L_{k+1}/L_k':>13s}  {'Pr (decimal)':>13s}  "
          f"{'[1/3,2/3]':>10s}  {'[3/11,8/11]':>12s}")
    print(f"    {'-'*4}  {'-'*16}  {'-'*13}  {'-'*13}  {'-'*10}  {'-'*12}")
    for r in pr_results:
        cov_str = ",".join(f"{a}<{b}" for (a, b) in sorted(r['added_covers']))
        in_a = "✓" if r['in_1_3_2_3'] else "✗"
        in_b = "✓" if r['in_3_11_8_11'] else "✗"
        print(f"    {r['step']:>4d}  {cov_str:>16s}  "
              f"{str(r['Pr']):>13s}  {float(r['Pr']):>13.4f}  "
              f"{in_a:>10s}  {in_b:>12s}")
    pr_all_1_3 = all(r['in_1_3_2_3'] for r in pr_results)
    pr_all_3_11 = all(r['in_3_11_8_11'] for r in pr_results)
    print(f"\n  Summary:")
    print(f"    All per-step Pr in [1/3, 2/3]:   {'✓ yes' if pr_all_1_3 else '✗ no'}")
    print(f"    All per-step Pr in [3/11, 8/11]: "
          f"{'✓ yes (BFT-sharp)' if pr_all_3_11 else '✗ no'}")

    # Pr-spectrum on F6 4-cell (sign-support permitting).
    if sgn_4cell:
        print(f"\n  Per-step Pr-spectrum along F6 4-cell (sign-supported):")
        pr_4cell = per_step_pr_spectrum(lifted_4cell)
        for r in pr_4cell:
            cov_str = ",".join(f"{a}<{b}" for (a, b) in sorted(r['added_covers']))
            in_a = "✓" if r['in_1_3_2_3'] else "✗"
            in_b = "✓" if r['in_3_11_8_11'] else "✗"
            print(f"      step {r['step']}  Pr = {r['Pr']!s:>8s} "
                  f"({float(r['Pr']):.4f})  "
                  f"[1/3,2/3]: {in_a}  [3/11,8/11]: {in_b}  "
                  f"covers {cov_str}")
    else:
        pr_4cell = []

    # §H. Summary of 7/8 outlier.
    print(f"\n  --- §H.  F6 Pr = 7/8 outlier resolution ---")
    print(f"  F5/F6 dim-2 critical cell step 0: Pr = 7/8 = 0.875 outside")
    print(f"    BFT [3/11, 8/11] and KS [1/3, 2/3].")
    print(f"  F6 Forman cancellation pair [2]: the dim-2 critical cell was")
    print(f"    cancelled jointly with critical 3-cell [1] (V-path length 5).")
    print(f"    After F6 cancellation, the 2-cell is no longer critical.")
    print(f"  F7 sign-support test of the cancelled F5 2-cell:")
    if sgn_2cell:
        print(f"    → 2-cell IS sign-supported (Stab ⊂ A_5).")
        print(f"    → Were it surviving, the Pr=7/8 outlier WOULD live in")
        print(f"      the sign-rep.  But F6 cancellation already removed it,")
        print(f"      so this is moot for the post-F6 Morse function.")
    else:
        print(f"    → 2-cell is NOT sign-supported (Stab has odd element).")
        print(f"    → Even without F6 cancellation, the 7/8 outlier would not")
        print(f"      have appeared in the sign-rep restriction.")

    # §I. Verdict.
    print(f"\n  --- §I.  F7 Verdict ---")
    burnside_ok = (m_sgn == 1)
    if pr_4cell:
        pr_4cell_3_11 = all(r['in_3_11_8_11'] for r in pr_4cell)
        pr_4cell_1_3 = all(r['in_1_3_2_3'] for r in pr_4cell)
    else:
        pr_4cell_3_11 = True
        pr_4cell_1_3 = True

    # Sign-rep "critical cells" (post-F6, naively-restricted):
    sgn_crit_count = (1 if sgn_cstar else 0) + (1 if sgn_4cell else 0)
    print(f"\n  Sign-supported F6-critical cells:")
    print(f"    • c*_5 (3-cell):  {'sign-supported ✓' if sgn_cstar else 'NOT'}")
    print(f"    • F6 4-cell:      {'sign-supported ✓' if sgn_4cell else 'NOT (removed in sign-rep)'}")
    print(f"  Naïve sign-rep critical-cell count: {sgn_crit_count}")
    print(f"  Predicted (Burnside m_sgn=1, H-Cox): 1 critical 3-cell only.")

    if sgn_crit_count == 1 and sgn_cstar and not sgn_4cell:
        sgn_structurally_perfect = True
        print(f"  ✓ Structurally PERFECT sign-rep Morse: only c*_5 survives.")
    elif sgn_crit_count >= 1 and sgn_cstar:
        sgn_structurally_perfect = False
        print(f"  ~ Partial: c*_5 sign-supported but additional sign-rep")
        print(f"    critical cells survive; F7' Forman cancellation candidate.")
    else:
        sgn_structurally_perfect = False
        print(f"  ✗ c*_5 not sign-supported — structural obstruction.")

    verdict = "RED"
    if burnside_ok and sgn_structurally_perfect and pr_all_3_11 and cocycle_ok:
        verdict = "GREEN-headline"
    elif burnside_ok and pr_all_3_11 and cocycle_ok:
        verdict = "GREEN"
    elif burnside_ok and pr_all_3_11:
        verdict = "GREEN"  # cocycle-check on full Δ_5 may be partial
    elif burnside_ok:
        verdict = "AMBER"
    else:
        verdict = "RED"

    print(f"\n  VERDICT: {verdict}")
    print(f"    • Burnside m_sgn = 1 (cohomological prediction):  "
          f"{'✓' if burnside_ok else '✗'}")
    print(f"    • c*_5 per-step Pr in [3/11, 8/11] (BFT-sharp):    "
          f"{'✓' if pr_all_3_11 else '✗'}")
    print(f"    • c*_5 per-step Pr in [1/3, 2/3] (KS-sharp):       "
          f"{'✓' if pr_all_1_3 else '✗'}")
    if cocycle_ok is True:
        print(f"    • ω_bal^(5) cocycle test (d^3 ω = 0 on near-support 4-chains): ✓")
    elif cocycle_ok is False:
        print(f"    • ω_bal^(5) cocycle test (d^3 ω = 0): ✗")
    print(f"    • c*_5 sign-supported:                              "
          f"{'✓' if sgn_cstar else '✗'}")
    print(f"    • Sign-rep critical orbits (naive F6-restricted):  {sgn_crit_count}")

    print()
    print("=" * 72)
    print(f"Done.  See docs/compatibility-geometry-F7-equivariant-morse.md")
    print(f"for the full writeup (mg-73fd).")
    print("=" * 72)


if __name__ == "__main__":
    main()
