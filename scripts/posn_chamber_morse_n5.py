#!/usr/bin/env python3
r"""
posn_chamber_morse_n5.py
========================

Compat-Geom F5 companion script (mg-1e58).  Implements (I2)-n5 of the
inductive-lift survey (mg-0e68 / `69fd8c9`): the chamber-restricted
discrete Morse function on $\Delta(\mathrm{PPF}_5 / S_5)$.

Predecessors:
  - posn_morse_check.py     (F2 / mg-7455 / d250cd3)   discrete Morse + ω_bal at n=4
  - posn_omega_bal_spectrum.py (F3 / mg-6bc3 / b387809)  per-step Pr-spectrum
  - compatibility-geometry-F4-inductive-survey.md (mg-0e68 / 69fd8c9) §2.2 + §5

Setup
-----
The poset $\mathrm{PPF}_5$ (= "proper partial orders" on $\{0,1,2,3,4\}$,
i.e. non-empty, non-chain) carries a natural $S_5$ action by relabeling.
Per the F4 survey §2.2, the fundamental chamber $C_5 = \mathrm{PPF}_5 / S_5$
has approximately 34 cells (predicted from $|\mathrm{PPF}_5| / |S_5|
= 4110/120 \approx 34.25$, with corrections from non-trivial stabilizers).

The order complex of the chamber, $\Delta(C_5)$, is the simplicial complex of
strict ascending chains of $S_5$-orbits of partial orders.  An equivariant
discrete Morse matching on $\Delta(\mathrm{PPF}_5)$ corresponds bijectively
to a matching on $\Delta(C_5)$.

This script:

  §A  Enumerates $\mathrm{PPF}_5$ via incremental refinement (transcribed
      from `posn_morse_check.py`).
  §B  Computes the lex-min canonical form under the $S_5$-action and
      groups elements into orbits.  Verifies the orbit count is ~34.
  §C  Constructs the chamber refinement poset (orbit-quotient of PPF_5
      under refinement).
  §D  Builds the chamber's order complex $\Delta(C_5)$ — all strict
      chains of orbits.
  §E  Runs a greedy acyclic Morse matching aimed at the critical-cell
      vector $(0, 0, 0, 1, 0, 0, 0, 0, 0)$ (one critical 3-cell,
      consistent with $\Delta_5 \simeq S^3$).
  §F  Classifies the critical cell(s) — lex-min representative chosen
      from the canonical lex-min orbit reps.
  §G  Computes per-step Pr-spectrum along the critical 3-cell c*_5 =
      (P_0 ⊂ P_1 ⊂ P_2 ⊂ P_3): values $\Pr_{P_k}[(a_k, b_k)]$ for
      $k = 0, 1, 2$, with $[1/3, 2/3]$ and $[3/11, 8/11]$ checks.
  §H  Constructs the Morse-cocycle $\omega_{\mathrm{bal}}$ via inverse
      V-path BFS from $c^*_5$, verifies $d^3 \omega_{\mathrm{bal}} = 0$,
      $\langle \omega_{\mathrm{bal}}, c^*_5 \rangle = \pm 1$.
  §I  Verdict.

Pure-Python stdlib only.  Targets commodity-hardware runtime:
  - PPF_5 enumeration   < 1 min  (4110 elements)
  - Canonical-form grouping  ≈ 1 min  (493k orbit applications, cached)
  - Chamber order-complex   < 1 min  (~ few thousand chains)
  - Greedy matching + verification  < 1 min
  - Pr-spectrum + ω_bal       < 10 s
  - Total                     ≈ 3-5 min on commodity hw

Usage:
    python3 posn_chamber_morse_n5.py [--no-prspectrum] [--no-omega]
                                     [--verbose] [--report-only]

References:
  - Forman 1998, Adv. Math. 134, Theorems 3.4, 8.2, 11.1.
  - Chari 2000, Discrete Math. 217.
  - Kahn–Saks 1984, Order 1, 113-126.
  - Brightwell–Felsner–Trotter 1995, Order 12, 327-349.
  - mg-7455 (F2): docs/compatibility-geometry-F2-scoping.md
  - mg-6bc3 (F3): docs/compatibility-geometry-F3-scoping.md
  - mg-0e68 (F4): docs/compatibility-geometry-F4-inductive-survey.md
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations
from math import factorial


# ============================================================================
# §A.  PPF_5 enumeration (re-used from posn_morse_check.py / posn_omega_bal_spectrum).
# ============================================================================

N = 5


def transitive_closure(rel):
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


def is_partial_order(rel):
    closed = set(rel)
    for (a, b) in closed:
        if a == b:
            return False
        if (b, a) in closed:
            return False
    return frozenset(closed) == transitive_closure(closed)


def is_chain_poset(P, n):
    """A chain has exactly n(n-1)/2 strict relations under transitive closure."""
    return len(P) == n * (n - 1) // 2


def enumerate_partial_orders_incremental(n):
    """Enumerate ALL transitively-closed antisymmetric relations on [0, n).
    Returns: list of frozensets.  Includes the empty relation (antichain)
    and the n! chains.
    """
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


def variant_PPF(orders, n):
    """Filter to proper partial orders: not empty, not chain."""
    return [P for P in orders
            if P != frozenset() and not is_chain_poset(P, n)]


# ============================================================================
# §B.  S_5 canonical form & orbit grouping.
# ============================================================================

# Pre-compute all 120 permutations of {0, 1, 2, 3, 4}.
_S5_PERMS = list(permutations(range(N)))


def apply_perm(P, sigma):
    """Apply permutation sigma (as tuple of length N) to poset P:
    (a, b) -> (sigma[a], sigma[b]).
    """
    return frozenset((sigma[a], sigma[b]) for (a, b) in P)


def lex_min_canonical(P):
    """Compute the lex-min S_N image of P.  Used as canonical
    representative of P's S_N-orbit.

    The "lex" ordering is on the sorted tuple of pairs of P.
    """
    if not P:
        return P
    best_key = None
    best_image = None
    for sigma in _S5_PERMS:
        img = apply_perm(P, sigma)
        key = tuple(sorted(img))
        if best_key is None or key < best_key:
            best_key = key
            best_image = img
    return best_image


def group_orbits(elements):
    """Group `elements` (list of posets) by S_N orbit.  Returns:
      orbits: list of (canonical_rep, orbit_size, full_orbit_set)
    sorted by (rank = number of relations, canonical key).
    """
    canon_to_members = {}
    for P in elements:
        c = lex_min_canonical(P)
        canon_to_members.setdefault(c, set()).add(P)
    orbits = []
    for c, members in canon_to_members.items():
        orbits.append((c, len(members), frozenset(members)))
    orbits.sort(key=lambda t: (len(t[0]), tuple(sorted(t[0]))))
    return orbits


def stabilizer_size(P):
    """Number of σ ∈ S_N with σ(P) = P."""
    count = 0
    for sigma in _S5_PERMS:
        if apply_perm(P, sigma) == P:
            count += 1
    return count


# ============================================================================
# §C.  Chamber refinement poset (orbit-quotient of PPF_5).
# ============================================================================

def orbits_strictly_above(R, all_canonical_reps):
    """For a canonical rep R, find all canonical reps R' such that some
    σ(R') ⊋ R in PPF_5, equivalently some σ'(R) ⊊ R'.

    Strict above means: there exists σ ∈ S_N with R ⊊ σ(R').
    """
    out = []
    R_set = set(R)
    for Rp in all_canonical_reps:
        if Rp == R:
            continue
        # Need |R'| > |R| for strict refinement (more relations).
        if len(Rp) <= len(R):
            continue
        # Search for σ ∈ S_N with R ⊊ σ(R').
        found = False
        for sigma in _S5_PERMS:
            img = apply_perm(Rp, sigma)
            if R_set.issubset(img) and R != img:
                found = True
                break
        if found:
            out.append(Rp)
    return out


def build_chamber_poset(orbits):
    """Build the strict refinement relation on canonical orbit reps.

    Returns:
      reps: list of canonical reps, sorted by (rank, lex).
      above: dict canonical_rep -> list of canonical reps strictly above.
    """
    reps = [c for (c, _, _) in orbits]
    above = {}
    for R in reps:
        above[R] = orbits_strictly_above(R, reps)
    return reps, above


# ============================================================================
# §D.  Order complex of the chamber: enumerate all strict chains.
# ============================================================================

def all_chamber_chains(reps, above):
    """Enumerate all strict chains in the chamber order poset.
    Returns: dict dim -> list of chains (as tuples of canonical reps).
    """
    by_dim = {0: [(R,) for R in reps]}
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


# ============================================================================
# §E.  Greedy acyclic Morse matching on the chamber face poset.
# ============================================================================

def compute_chamber_morse(reps, above, target_dim, verbose=False):
    """Greedy acyclic matching on the face poset of Δ(chamber).
    Aim: minimize critical cells, ideally achieve critical-cell vector
    (0, 0, …, 0, 1, 0, …, 0) (one critical cell at dim `target_dim`).

    Algorithm (Joswig-Pfetsch style; same as F2 compute_morse_matching but
    operating on chamber chains rather than full PPF chains):
      1. Enumerate cover pairs (σ ⊂ τ, |τ| = |σ| + 1), incl. augmentation
         pair (∅ ⊂ {v}) for each vertex v.
      2. Sort top-down by (|τ| descending, lex(τ), lex(σ)) — top-down gives
         priority to high-dim pairs, which tends to minimize critical cells
         in low dimensions.
      3. Greedy: add each pair to M if doing so leaves the modified Hasse
         (with edge reversed) acyclic.

    Returns:
      matching: dict frozenset(chain) -> ('add'/'remove', frozenset(partner), pair_idx)
      critical: dict dim -> list of critical chains
      by_dim: full dim -> chain list (incl. augmentation cell ())
      accepted_pairs: list of (sigma_tuple, tau_tuple) accepted
    """
    by_dim = all_chamber_chains(reps, above)
    if verbose:
        print(f"    chamber order complex:")
        for d in sorted(by_dim):
            print(f"      dim {d}: {len(by_dim[d])} chains")

    # Augmentation cell ().
    EMPTY = ()

    # Build cover_pairs.  Include (∅, v) for each vertex v.
    cover_pairs = []
    for v in by_dim.get(0, []):
        cover_pairs.append((EMPTY, v))
    for d in sorted(by_dim):
        if d + 1 not in by_dim:
            continue
        for tau in by_dim[d + 1]:
            for i in range(len(tau)):
                sigma = tau[:i] + tau[i + 1:]
                cover_pairs.append((sigma, tau))

    def pair_key(p):
        s, t = p
        return (-len(t), t, s)
    cover_pairs.sort(key=pair_key)

    # Adjacency: cofaces / faces.
    all_cells = [EMPTY]
    for d in sorted(by_dim):
        all_cells.extend(by_dim[d])
    cofaces = {c: [] for c in all_cells}
    faces = {c: [] for c in all_cells}
    for sigma, tau in cover_pairs:
        cofaces[sigma].append(tau)
        faces[tau].append(sigma)

    matched = {c: None for c in all_cells}

    def adj_from(c):
        for tau in cofaces[c]:
            if matched[c] != tau:
                yield tau
        if matched[c] is not None and matched[c] in faces[c]:
            yield matched[c]

    def reachable_path(src, dst):
        if src == dst:
            return True
        stack = [src]
        seen = {src}
        while stack:
            u = stack.pop()
            for v in adj_from(u):
                if v == dst:
                    return True
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return False

    accepted_pairs = []
    for sigma, tau in cover_pairs:
        if matched[sigma] is not None or matched[tau] is not None:
            continue
        matched[sigma] = tau
        matched[tau] = sigma
        if reachable_path(sigma, tau):
            matched[sigma] = None
            matched[tau] = None
        else:
            accepted_pairs.append((sigma, tau))

    matching = {}
    for i, (sigma, tau) in enumerate(accepted_pairs):
        matching[frozenset(sigma)] = ('add', frozenset(tau), i)
        matching[frozenset(tau)] = ('remove', frozenset(sigma), i)

    critical = {}
    for d in sorted(by_dim):
        critical[d] = []
        for c in by_dim[d]:
            if frozenset(c) not in matching:
                critical[d].append(c)
    # Augmentation cell: include if unmatched.
    crit_aug = (frozenset() not in matching)

    return matching, critical, by_dim, accepted_pairs, crit_aug


def verify_acyclic_modified_hasse(matching, by_dim):
    """Verify the modified Hasse digraph (with matched edges reversed) is
    acyclic.  Builds adjacency directly and runs iterative DFS.
    Returns (acyclic_bool, num_arrows, sample_cycle_or_None).
    """
    chain_to_set = {c: frozenset(c) for d in by_dim for c in by_dim[d]}
    adj = {c: [] for d in by_dim for c in by_dim[d]}
    for d in by_dim:
        if d + 1 not in by_dim:
            continue
        for tau in by_dim[d + 1]:
            tau_set = chain_to_set[tau]
            for i in range(len(tau)):
                sigma = tau[:i] + tau[i + 1:]
                sigma_set = chain_to_set[sigma]
                if matching.get(sigma_set, (None, None, None))[1] == tau_set:
                    adj[sigma].append(tau)        # matched: σ → τ
                else:
                    adj[tau].append(sigma)        # unmatched: τ → σ

    WHITE, GRAY, BLACK = 0, 1, 2
    state = {c: WHITE for c in adj}
    cycle = [None]

    def dfs_iter(start):
        stack = [(start, iter(adj[start]))]
        state[start] = GRAY
        while stack:
            u, it = stack[-1]
            try:
                v = next(it)
            except StopIteration:
                state[u] = BLACK
                stack.pop()
                continue
            if state[v] == GRAY:
                cycle[0] = (u, v)
                return
            elif state[v] == WHITE:
                state[v] = GRAY
                stack.append((v, iter(adj[v])))

    for c in list(adj):
        if state[c] == WHITE:
            dfs_iter(c)
            if cycle[0] is not None:
                break

    num_arrows = sum(len(v) for v in adj.values())
    return (cycle[0] is None, num_arrows, cycle[0])


# ============================================================================
# §F.  Linear extensions: count |L(P)| via cached recursion.
# ============================================================================

_le_cache = {}


def count_linear_extensions(P, universe_size=N):
    """|L(P)| where P is a partial order on [0, universe_size).  Elements
    absent from P are treated as isolated.
    """
    if not P:
        return factorial(universe_size)
    key = (universe_size, frozenset(P))
    if key in _le_cache:
        return _le_cache[key]
    elts = frozenset(range(universe_size))
    val = _le_recursive(frozenset(P), elts)
    _le_cache[key] = val
    return val


def _le_recursive(P, remaining):
    if not remaining:
        return 1
    key = ('rec', P, remaining)
    if key in _le_cache:
        return _le_cache[key]
    has_pred = set()
    for (a, b) in P:
        if a in remaining and b in remaining:
            has_pred.add(b)
    minima = [x for x in remaining if x not in has_pred]
    if not minima:
        return 0
    total = 0
    for x in minima:
        Px = frozenset((a, b) for (a, b) in P if a != x and b != x)
        rem_minus = frozenset(remaining - {x})
        sub_key = ('rec', Px, rem_minus)
        if sub_key in _le_cache:
            total += _le_cache[sub_key]
        else:
            v = _le_recursive(Px, rem_minus)
            _le_cache[sub_key] = v
            total += v
    _le_cache[key] = total
    return total


def covers_of(P):
    """Cover relations (Hasse) of P."""
    Pset = set(P)
    elts = set()
    for (a, b) in Pset:
        elts.add(a)
        elts.add(b)
    covers = []
    for (a, b) in Pset:
        is_cov = True
        for c in elts:
            if c in (a, b):
                continue
            if (a, c) in Pset and (c, b) in Pset:
                is_cov = False
                break
        if is_cov:
            covers.append((a, b))
    return frozenset(covers)


def newly_added_cover(P_lo, P_hi):
    """Returns the set of cover-pairs newly added going P_lo → P_hi.
    Honest cover-edge in P_hi that's NOT in P_lo's transitive closure.
    """
    cov_hi = covers_of(P_hi)
    truly_added = frozenset((a, b) for (a, b) in cov_hi if (a, b) not in P_lo)
    return truly_added


# ============================================================================
# §G.  Pretty-printing.
# ============================================================================

def poset_str(P):
    if not P:
        return "antichain"
    pairs = sorted(P)
    return "{" + ",".join(f"{a}<{b}" for (a, b) in pairs) + "}"


def hasse_str(P):
    if not P:
        return "antichain"
    covs = sorted(covers_of(P))
    return "{" + ",".join(f"{a}⋖{b}" for (a, b) in covs) + "}"


def chain_str(c):
    return " ⊂ ".join(poset_str(P) for P in c)


def chain_hasse_str(c):
    return " ⊂ ".join(hasse_str(P) for P in c)


# ============================================================================
# §H.  Pr-spectrum along critical chain (lifts via reps in PPF_5).
# ============================================================================

def lift_chain_to_reps(chain_canonical):
    """Given a chain of canonical reps (R_0, R_1, …, R_k) with R_i ⊊ ... (in
    orbit poset, not necessarily as set inclusion), find a chain of actual
    posets (P_0 ⊊ P_1 ⊊ … ⊊ P_k) where P_i ∈ S_N · R_i, P_i ⊊ P_{i+1} (as
    set of relations).

    Strategy: greedy.  Fix P_0 = R_0.  At each step pick σ_i ∈ S_N such
    that P_i ⊊ σ_i(R_{i+1}); set P_{i+1} = σ_i(R_{i+1}).  Backtrack if
    no valid σ_i.

    Returns: tuple (P_0, P_1, …, P_k) or None if no lift exists.
    """
    if len(chain_canonical) == 0:
        return ()
    # Start with P_0 = R_0 (the canonical rep itself).
    return _lift_chain_dfs(chain_canonical, 0, (chain_canonical[0],))


def _lift_chain_dfs(chain_canonical, depth, current_lift):
    if depth == len(chain_canonical) - 1:
        return current_lift
    P_curr = current_lift[-1]
    R_next = chain_canonical[depth + 1]
    P_curr_set = set(P_curr)
    seen_images = set()
    for sigma in _S5_PERMS:
        img = apply_perm(R_next, sigma)
        if img in seen_images:
            continue
        seen_images.add(img)
        if P_curr_set.issubset(img) and img != P_curr:
            result = _lift_chain_dfs(chain_canonical, depth + 1, current_lift + (img,))
            if result is not None:
                return result
    return None


def per_step_pr_spectrum(lifted_chain):
    """Compute Pr_{P_k}[(a_k, b_k)] for each step k in lifted_chain.
    Returns: list of dicts with keys 'P_k', 'P_kp1', 'L_k', 'L_kp1', 'Pr',
                                       'added_covers', 'in_1_3_2_3', 'in_3_11_8_11'.
    """
    out = []
    third = Fraction(1, 3)
    two_thirds = Fraction(2, 3)
    three_eleven = Fraction(3, 11)
    eight_eleven = Fraction(8, 11)
    for k in range(len(lifted_chain) - 1):
        P_k = lifted_chain[k]
        P_kp1 = lifted_chain[k + 1]
        L_k = count_linear_extensions(P_k)
        L_kp1 = count_linear_extensions(P_kp1)
        if L_k == 0:
            pr = Fraction(0, 1)
        else:
            pr = Fraction(L_kp1, L_k)
        added = newly_added_cover(P_k, P_kp1)
        out.append({
            'step': k,
            'P_k': P_k,
            'P_kp1': P_kp1,
            'L_k': L_k,
            'L_kp1': L_kp1,
            'Pr': pr,
            'added_covers': added,
            'in_1_3_2_3': third <= pr <= two_thirds,
            'in_3_11_8_11': three_eleven <= pr <= eight_eleven,
        })
    return out


def ks_telescoped(lifted_chain):
    """Telescoped KS product = |L(P_top)| / |L(P_bot)|."""
    if len(lifted_chain) < 2:
        return Fraction(1, 1)
    L_top = count_linear_extensions(lifted_chain[-1])
    L_bot = count_linear_extensions(lifted_chain[0])
    return Fraction(L_top, L_bot)


# ============================================================================
# §I.  ω_bal cocycle via inverse-V-path BFS (from F2/F3).
# ============================================================================

def morse_cocycle_from_critical(c_star, matching, by_dim):
    """Inverse-V-path BFS to construct the Morse-cocycle representative
    of the class [δ_{c*}] in the Morse-collapsed complex.

    Same algorithm as in `posn_morse_check.py:morse_cocycle_from_critical`,
    adapted for the chamber complex.

    Returns: dict tuple-chain -> Z coefficient.
    """
    k = len(c_star) - 1
    cofaces_of = {tuple(c): [] for d in by_dim for c in by_dim[d]}
    for d in by_dim:
        if d + 1 not in by_dim:
            continue
        for tau in by_dim[d + 1]:
            for i in range(len(tau)):
                sigma = tau[:i] + tau[i + 1:]
                if sigma in cofaces_of:
                    cofaces_of[sigma].append((i, tau))

    omega = {tuple(c_star): 1}
    frontier = [(tuple(c_star), 1)]
    while frontier:
        new_frontier = []
        for sigma_end, sign in frontier:
            for (i_end, tau) in cofaces_of.get(sigma_end, []):
                tau_fs = frozenset(tau)
                m = matching.get(tau_fs)
                if m is None:
                    continue
                kind, partner_fs, _ = m
                if kind != 'remove':
                    continue
                sigma_1 = None
                i_1 = None
                for j in range(len(tau)):
                    face_j = tau[:j] + tau[j + 1:]
                    if frozenset(face_j) == partner_fs:
                        sigma_1 = face_j
                        i_1 = j
                        break
                if sigma_1 is None or sigma_1 == sigma_end:
                    continue
                step_sign = ((-1) ** i_1) * ((-1) ** i_end)
                new_val = -sign * step_sign
                if sigma_1 not in omega:
                    omega[sigma_1] = new_val
                    new_frontier.append((sigma_1, new_val))
                else:
                    omega[sigma_1] += new_val
        frontier = new_frontier

    return {sigma: v for sigma, v in omega.items() if v != 0}


def coboundary_action(omega, chains_kp1):
    """d^k(ω)(τ) = Σ_i (-1)^i ω(d_i τ)."""
    out = {}
    for tau in chains_kp1:
        v = 0
        for i in range(len(tau)):
            sigma = tau[:i] + tau[i + 1:]
            v += ((-1) ** i) * omega.get(sigma, 0)
        if v:
            out[tau] = v
    return out


# ============================================================================
# §J.  Verdict logic.
# ============================================================================

def verdict_from_results(critical_counts, pr_results, ks_value, omega_pair_self,
                         omega_acoboundary_zero):
    """Determine the F5 verdict (RED / AMBER / GREEN / GREEN-headline)
    based on F4 §5.5 verdict matrix.
    """
    # GREEN-headline: chamber-Morse perfect (1 critical (n-2)-cell) +
    #                 all per-step Pr in [3/11, 8/11] (BFT-sharp).
    # GREEN: chamber-Morse perfect + all per-step Pr in [1/3, 2/3].
    # AMBER: chamber-Morse partial (matching non-perfect).
    # RED: chamber-Morse approach structurally obstructed.

    target = 3  # critical 3-cell at n=5

    # Check critical-cell vector.
    crit_at_target = critical_counts.get(target, 0)
    total_crit = sum(critical_counts.values())

    # Perfect = exactly 1 critical cell at dim target + 0 elsewhere.
    perfect = (crit_at_target == 1 and total_crit == 1)
    near_perfect = (crit_at_target == 1 and total_crit <= 2)

    # Check Pr-spectrum.
    pr_all_in_1_3_2_3 = all(r['in_1_3_2_3'] for r in pr_results)
    pr_all_in_3_11_8_11 = all(r['in_3_11_8_11'] for r in pr_results)

    # Check ω_bal soundness.
    omega_sound = (abs(omega_pair_self) >= 1 and omega_acoboundary_zero)

    if perfect and pr_all_in_3_11_8_11 and omega_sound:
        return "GREEN-headline"
    if perfect and pr_all_in_1_3_2_3 and omega_sound:
        return "GREEN"
    if (perfect or near_perfect) and pr_all_in_1_3_2_3:
        return "GREEN"
    if crit_at_target >= 1 and pr_results:
        return "AMBER"
    return "RED"


# ============================================================================
# §K.  Top-level driver.
# ============================================================================

def report_orbits(orbits, ppf_n):
    print(f"\n  --- §B.  S_{N} orbit enumeration of PPF_{N} ---")
    print(f"  |PPF_{N}|     = {len(ppf_n)}")
    print(f"  # orbits    = {len(orbits)}  (predicted ~34; F3 §4.2)")
    print(f"\n  Orbit table (canonical rep, orbit size, stabilizer):")
    print(f"    {'rank':>4s}  {'orbit size':>10s}  {'stab':>5s}  {'representative (Hasse)':s}")
    print(f"    {'-'*4}  {'-'*10}  {'-'*5}  {'-'*60}")
    total_check = 0
    for (R, sz, _) in orbits:
        stab = factorial(N) // sz
        total_check += sz
        print(f"    {len(R):>4d}  {sz:>10d}  {stab:>5d}  {hasse_str(R)}")
    print(f"    {'-'*4}  {'-'*10}  {'-'*5}  {'-'*60}")
    print(f"    Σ orbit sizes = {total_check}   (should equal |PPF_{N}| = {len(ppf_n)})")
    if total_check != len(ppf_n):
        print(f"    ! MISMATCH in orbit-size sum — investigate canonical-form code.")
    else:
        print(f"    ✓ orbit-stabilizer accounting verified.")


def report_chamber_poset(reps, above):
    print(f"\n  --- §C.  Chamber refinement poset ---")
    print(f"  # canonical reps (= chamber vertices) = {len(reps)}")
    total_above = sum(len(above[R]) for R in reps)
    print(f"  total above-edges in orbit poset       = {total_above}")
    rank_dist = {}
    for R in reps:
        r = len(R)
        rank_dist[r] = rank_dist.get(r, 0) + 1
    print(f"  rank distribution:")
    for r in sorted(rank_dist):
        print(f"    rank {r}: {rank_dist[r]} orbits")


def report_chamber_complex(by_dim):
    print(f"\n  --- §D.  Chamber order complex Δ(C_{N}) ---")
    f_vec = []
    for d in sorted(by_dim):
        f_vec.append(len(by_dim[d]))
    print(f"  f-vector: {f_vec}")
    # Reduced Euler characteristic.
    chi = -1 + sum((-1) ** k * f_vec[k] for k in range(len(f_vec)))
    print(f"  reduced Euler χ̃(Δ(C_{N})) = {chi}")
    print(f"  (Note: this is χ̃ of the chamber order complex, not of Δ(PPF_{N}).")
    print(f"   Δ(PPF_{N}) has χ̃ = -1 conjecturally per (H-Cox) + F2 data.)")


def report_morse_matching(matching, critical, by_dim, accepted_pairs,
                          crit_aug, acyclic, num_arrows):
    print(f"\n  --- §E.  Greedy Morse matching on Δ(C_{N}) ---")
    crit_vec = tuple(len(critical[d]) for d in sorted(critical))
    n_pairs = len(accepted_pairs)
    print(f"  total pairs accepted = {n_pairs}")
    print(f"  acyclicity check     : arrows={num_arrows}, acyclic={acyclic}")
    print(f"  critical-cell vector (by dim 0,1,…):")
    print(f"    {crit_vec}")
    print(f"  augmentation cell (∅) critical?  {crit_aug}")
    target_perfect = (sum(crit_vec) == 1 and len(crit_vec) > 3 and crit_vec[3] == 1)
    near_perfect = (sum(crit_vec) <= 2 and len(crit_vec) > 3 and crit_vec[3] >= 1)
    if target_perfect:
        print(f"  ✓ PERFECT chamber-Morse matching achieved.")
    elif near_perfect:
        print(f"  ~ near-perfect (extras: {sum(crit_vec) - crit_vec[3]} non-target critical cells)")
    else:
        print(f"  ! non-perfect chamber matching; critical-cell vector ≠ (·,·,·,1,0,…)")


def report_critical_cells(critical):
    print(f"\n  --- §F.  Critical-cell classification (chamber-representatives) ---")
    for d in sorted(critical):
        cells = critical[d]
        if not cells:
            continue
        print(f"\n  Critical dim-{d} cells: {len(cells)}")
        # Pick lex-min by chain content (tuple of pair-sorted posets).
        sorted_cells = sorted(cells, key=lambda c: tuple(tuple(sorted(P)) for P in c))
        for i, c in enumerate(sorted_cells[:5]):
            print(f"    [{i}]  ranks {tuple(len(P) for P in c)}")
            for j, P in enumerate(c):
                print(f"          P_{j}  Hasse: {hasse_str(P)}")
        if len(sorted_cells) > 5:
            print(f"    ... ({len(sorted_cells) - 5} more)")


def report_pr_spectrum(critical, target_dim=3):
    print(f"\n  --- §G.  Per-step Pr-spectrum along critical {target_dim}-cell c*_{N} ---")
    cells = critical.get(target_dim, [])
    if not cells:
        print(f"  ! No critical {target_dim}-cell — Pr-spectrum N/A.")
        return None, None, None

    sorted_cells = sorted(cells, key=lambda c: tuple(tuple(sorted(P)) for P in c))
    c_star = sorted_cells[0]
    print(f"\n  Lex-min critical {target_dim}-cell c*_{N}:")
    print(f"    canonical reps:  {chain_hasse_str(c_star)}")
    print(f"    ranks:           {tuple(len(P) for P in c_star)}")

    lifted = lift_chain_to_reps(c_star)
    if lifted is None:
        print(f"  ! Cannot lift orbit-chain to a chain of actual posets.")
        print(f"    (this means the chosen orbit-quotient chain has no representative")
        print(f"     chain in PPF_{N}; the chamber order-complex differs from the")
        print(f"     orbit-cell quotient.  See F4 §2.2.2 for the construction.)")
        return c_star, None, None
    print(f"\n  Lifted chain of representatives in PPF_{N}:")
    for j, P in enumerate(lifted):
        L = count_linear_extensions(P)
        print(f"    P_{j} (rank {len(P)}):  Hasse {hasse_str(P)}    |L(P_{j})| = {L}")

    pr_results = per_step_pr_spectrum(lifted)
    print(f"\n  Per-step Pr-spectrum:")
    print(f"    {'step':>4s}  {'covers added':>14s}  {'L_{k+1}/L_k':>13s}  "
          f"{'Pr (decimal)':>13s}  {'[1/3,2/3]':>10s}  {'[3/11,8/11]':>12s}")
    print(f"    {'-'*4}  {'-'*14}  {'-'*13}  {'-'*13}  {'-'*10}  {'-'*12}")
    for r in pr_results:
        cov_str = ",".join(f"{a}<{b}" for (a, b) in sorted(r['added_covers']))
        in_a = "✓" if r['in_1_3_2_3'] else "✗"
        in_b = "✓" if r['in_3_11_8_11'] else "✗"
        print(f"    {r['step']:>4d}  {cov_str:>14s}  "
              f"{str(r['Pr']):>13s}  {float(r['Pr']):>13.4f}  "
              f"{in_a:>10s}  {in_b:>12s}")

    ks = ks_telescoped(lifted)
    third = Fraction(1, 3)
    two_thirds = Fraction(2, 3)
    print(f"\n  Kahn–Saks telescoped product = |L(P_{len(lifted)-1})| / |L(P_0)| = {ks} ≈ {float(ks):.4f}")
    print(f"    {'IN' if third <= ks <= two_thirds else 'OUT-OF'} [1/3, 2/3]")

    pr_all_1_3 = all(r['in_1_3_2_3'] for r in pr_results)
    pr_all_3_11 = all(r['in_3_11_8_11'] for r in pr_results)
    print(f"\n  Summary:")
    print(f"    All per-step Pr in [1/3, 2/3]:    {'✓ yes' if pr_all_1_3 else '✗ no'}")
    print(f"    All per-step Pr in [3/11, 8/11]:  {'✓ yes (BFT-sharp)' if pr_all_3_11 else '✗ no'}")

    return c_star, lifted, pr_results


def report_omega_bal(c_star, matching, by_dim, target_dim=3):
    print(f"\n  --- §H.  Morse-cocycle ω_bal ---")
    if c_star is None:
        print(f"  ! No critical {target_dim}-cell — ω_bal N/A.")
        return None, None, None

    omega = morse_cocycle_from_critical(c_star, matching, by_dim)
    pair_self = omega.get(tuple(c_star), 0)
    print(f"  ω_bal supported on {len(omega)} {target_dim}-chains")
    print(f"  ⟨ω_bal, c*⟩ = {pair_self}  (expect ±1 ≠ 0)")

    chains_kp1 = by_dim.get(target_dim + 1, [])
    d_omega = coboundary_action(omega, chains_kp1)
    print(f"  # ({target_dim+1})-chains: {len(chains_kp1)}")
    print(f"  # nonzero entries of d^{target_dim} ω_bal: {len(d_omega)}")
    if not d_omega:
        print(f"  ✓ d^{target_dim} ω_bal = 0 — genuine cocycle.")
    else:
        print(f"  ! d^{target_dim} ω_bal ≠ 0 in {len(d_omega)} positions; investigate.")
    return omega, pair_self, (len(d_omega) == 0)


# ============================================================================
# §L.  Main.
# ============================================================================

def main():
    args = sys.argv[1:]
    do_prspectrum = True
    do_omega = True
    verbose = False
    report_only = False
    while args:
        a = args.pop(0)
        if a == "--no-prspectrum":
            do_prspectrum = False
        elif a == "--no-omega":
            do_omega = False
        elif a == "--verbose":
            verbose = True
        elif a == "--report-only":
            report_only = True
        else:
            print(f"Unknown arg {a}", file=sys.stderr)
            sys.exit(2)

    print("=" * 72)
    print("posn_chamber_morse_n5.py — Compat-Geom F5 (mg-1e58)")
    print("=" * 72)
    print()
    print(f"This script computes the chamber-restricted discrete Morse function")
    print(f"on Δ(PPF_{N}/S_{N}) per the F4 inductive-lift survey (mg-0e68 §2.2).")
    print()
    print(f"Target: critical-cell vector (0, 0, 0, 1, 0, 0, 0, 0, 0) on chamber")
    print(f"      = single critical 3-cell c*_{N};  Δ_{N} ≃ S^3 cohomologically.")
    print()

    t0 = time.time()
    orders = enumerate_partial_orders_incremental(N)
    ppf = variant_PPF(orders, N)
    print(f"  §A.  Enumerated PPF_{N}:  |PPF_{N}| = {len(ppf)}  "
          f"({time.time()-t0:.1f}s)")

    t0 = time.time()
    orbits = group_orbits(ppf)
    print(f"        Grouped into S_{N} orbits:  {len(orbits)} orbits  "
          f"({time.time()-t0:.1f}s)")

    report_orbits(orbits, ppf)

    t0 = time.time()
    reps, above = build_chamber_poset(orbits)
    print(f"\n        Built chamber refinement poset  ({time.time()-t0:.1f}s)")
    report_chamber_poset(reps, above)

    t0 = time.time()
    matching, critical, by_dim, accepted_pairs, crit_aug = compute_chamber_morse(
        reps, above, target_dim=3, verbose=verbose
    )
    print(f"\n        Computed greedy Morse matching  ({time.time()-t0:.1f}s)")
    report_chamber_complex(by_dim)

    t0 = time.time()
    acyc, num_arrows, sample = verify_acyclic_modified_hasse(matching, by_dim)
    print(f"\n        Verified acyclicity  ({time.time()-t0:.1f}s)")

    report_morse_matching(matching, critical, by_dim, accepted_pairs,
                          crit_aug, acyc, num_arrows)
    report_critical_cells(critical)

    c_star = None
    pr_results = []
    omega = None
    pair_self = 0
    omega_dboundary_zero = False

    if do_prspectrum:
        c_star, lifted, pr_results = report_pr_spectrum(critical, target_dim=3)
        if pr_results is None:
            pr_results = []

    if do_omega and c_star is not None:
        omega, pair_self, omega_dboundary_zero = report_omega_bal(
            c_star, matching, by_dim, target_dim=3
        )

    # ----- §I.  Verdict -----
    print(f"\n  --- §I.  F5 Verdict ---")
    crit_counts = {d: len(critical[d]) for d in critical}
    # Adjust crit_counts to include augmentation cell if needed.
    verdict = verdict_from_results(
        crit_counts, pr_results,
        ks_telescoped(lifted) if c_star and lifted else None,
        pair_self, omega_dboundary_zero
    )
    print(f"\n  VERDICT: {verdict}")
    print(f"\n  Critical-cell vector (chamber): "
          f"{tuple(len(critical[d]) for d in sorted(critical))}")
    if pr_results:
        print(f"  All per-step Pr in [1/3, 2/3]:    "
              f"{'✓' if all(r['in_1_3_2_3'] for r in pr_results) else '✗'}")
        print(f"  All per-step Pr in [3/11, 8/11]:  "
              f"{'✓' if all(r['in_3_11_8_11'] for r in pr_results) else '✗'}")
    if c_star is not None:
        print(f"  ω_bal pair ⟨ω_bal, c*⟩: {pair_self}  (expect ±1)")
        print(f"  ω_bal cocycle (d ω = 0): {'✓' if omega_dboundary_zero else '✗'}")

    print("\n" + "=" * 72)
    print(f"Done.  See docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md")
    print(f"for the full writeup (mg-1e58).")
    print("=" * 72)


if __name__ == "__main__":
    main()
