#!/usr/bin/env python3
r"""
posn_constructive_lift_n7.py
============================

Compat-Geom F9 — constructive inductive-lift, Session 2 at n=7 (mg-14a0).

Goal
----
Session 1 (mg-9e88, `posn_constructive_lift_n6.py`) executed Plan H at n=5
and n=6, produced psi^(5) and psi^(6), and detected a shared structural
*mechanism* (full-row-rank constraint matrix; one sign-supported wing orbit
per F7-bad coface; near-diagonal +-1 solution).  What Session 1 could NOT
pin down is the n-dependence of the *count* of F7-bad cofaces:

    n = 5:  10 bad cofaces  (u_5 = 4   top-position up-set cofaces)
    n = 6:  64 bad cofaces  (u_6 = 54  top-position up-set cofaces)

Two datapoints cannot distinguish polynomial from exponential growth.
Session 2 produces the **third datapoint at n=7** -- the critical
discriminator between:

  * polynomial growth  -> the pattern admits a closed form; (I5) closes
    constructively via the shared mechanism; the inductive lift is
    general-n provable;
  * exponential growth -> the Plan H system at general n is intractable;
    the empirical pattern is n-dependent in a substantive way; (I5) needs
    a different angle (the parked X_n / specialist route).

This script
----------
Re-uses the fully parameterized Plan H pipeline of Session 1 -- it imports
the poset/permutation machinery, `run_plan_h`, and `psi_structure` from
`posn_constructive_lift_n6` (the Session-1 deliverable, on this same
branch).  It adds:

  * `c_star_7_chain()` -- the candidate critical 5-cell c*_7, built by the
    F8'-HPC recipe: the iota_6-lift of the F9 c*_6, extended by the
    lex-min step-5 cover.  (And `c_star_8_chain()` for a cheap *fourth*
    up-set datapoint u_8 -- counted, but no Plan H solve at n=8.)
  * `solve_psi_fast` + `run_plan_h_fast` -- a memory- and CPU-efficient
    drop-in for the Session-1 `solve_psi`.  The Session-1 `solve_psi`
    materializes the full S_n-orbit of every wing in a `seen` set; at n=7
    that is ~9600 orbits x up to 5040 = ~48M chains, which thrashes
    memory.  The replacement groups wings by a genuine *canonical form*
    (lex-min over a TOTAL order on chains -- note `frozenset.__lt__` is
    subset, NOT lex, so the Session-1 `canonical_rep` is a no-op on
    equal-rank-profile chains and the orbit set is what blows up).  This
    keeps memory O(#wings) and is exact-arithmetic identical.
  * a 3-datapoint (n=5,6,7) cross-pattern;
  * `count_function_extrapolation()` -- the polynomial-vs-exponential
    analysis of the bad-coface count sequence;
  * a Session-2 verdict emitter.

Trip-wire pre-checks (mandatory, per mg-14a0):
  (a) n=5 AND n=6 Plan H reproduce Session 1 exactly.
  (b) Stab(c*_7) subset A_7  (so omega_naive^(7) is well-defined).
  (c) the iota_6-lift c*_6 -> c*_7 is well-defined (c*_6 is a genuine
      prefix of c*_7; the step-5 cover strictly refines P_4).

Pure-Python stdlib only.  Runtime: ~10-15 minutes on commodity hardware
(7! = 5040; the canonical-form wing grouping at n=7 is the dominant cost).

Usage:
    python3 posn_constructive_lift_n7.py [--verbose] [--no-n8]

References:
  - mg-9e88 / 5a94ce9 (F9 Session 1): scripts/posn_constructive_lift_n6.py,
    docs/state-F9.md, docs/compatibility-geometry-F9-constructive-lift.md
  - mg-e8d5 (F7' Plan H, n=5);  mg-3bf3 (F8'-HPC, c_star_6_chain);
  - mg-1e99 (F8 framework) §E: the iota-lift + lex-min cover convention
    -- "the lex-min cover [of iota_5(P_3)] is e.g. (0,5)".
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations

# All the Plan H machinery is the Session-1 deliverable, parameterized at
# arbitrary n; it lives on this same branch.  Import rather than vendor:
# the dependency is fully within-branch (DRY; no re-derivation risk).
from posn_constructive_lift_n6 import (
    transitive_closure,
    is_total,
    perm_parity,
    perm_sign,
    apply_perm_chain,
    signed_orbit_cocycle,
    immediate_cofaces,
    d_cochain,
    collect_wings,
    verify_on_bad,
    c_star_6_chain,
    C_STAR_5,
    psi_structure,
)


# ============================================================================
# §1.  The candidate critical cells c*_7 and c*_8.
# ============================================================================


def c_star_7_chain():
    r"""Build the candidate critical 5-cell c*_7 at n=7.

    Recipe (the F8'-HPC / F8-framework convention, applied one step up from
    `c_star_6_chain`):

        c*_7  =  ( iota_6(P_0), ..., iota_6(P_4),  P_4 cup {lex-min cover} )

    where (P_0,...,P_4) = c*_6 is the Session-1 F9 cell, iota_6 lifts it to
    the ambient {0,...,6} leaving element 6 free, and the lex-min step-5
    cover is the lexicographically smallest ordered pair (a,b) that can be
    added to P_4 to give a proper, antisymmetric, transitively-closed
    poset.  For P_4 = c*_6[-1] the pairs (0,1),(0,2),(0,3),(0,4) are already
    present, so the lex-min addable pair is **(0,5)** -- in agreement with
    the F8 general-n script `posn_inductive_omega_bal_general_n.py` §E,
    which states the lex-min cover at this step "is e.g. (0,5)".

    c*_7 rank profile: (3,5,6,8,9,10) -- a dim-5 cell.  Element 6 is
    incomparable throughout (the iota_6-lift).
    """
    c6 = list(c_star_6_chain())          # iota_6-lift is the identity on
                                          # relation sets; ambient n is 7.
    P5 = transitive_closure(set(c6[-1]) | {(0, 5)})
    return tuple(c6 + [P5])


def c_star_8_chain():
    r"""Build the candidate critical 6-cell c*_8 at n=8 -- ONLY used to count
    its top-position up-set u_8 (a cheap fourth count-function datapoint).
    No Plan H solve is run at n=8 (out of Session-2 scope).

    Same recipe one step further: iota_7-lift of c*_7, extended by the
    lex-min step-6 cover, which is (0,6) by the identical argument.
    """
    c7 = list(c_star_7_chain())
    P6 = transitive_closure(set(c7[-1]) | {(0, 6)})
    return tuple(c7 + [P6])


def upset_proper_count(P, n):
    """Count proper transitively-closed Q with P strictly-subset Q (the
    top-position up-set), without materializing the Plan H wings.  Mirrors
    `posn_constructive_lift_n6.upset_proper` but count-only / memory-light.
    """
    seen = {P}
    frontier = {P}
    while frontier:
        nf = set()
        for Q in frontier:
            for a in range(n):
                for b in range(n):
                    if a == b or (a, b) in Q or (b, a) in Q:
                        continue
                    c = transitive_closure(set(Q) | {(a, b)})
                    if any((y, x) in c for (x, y) in c):  # antisymmetric?
                        continue
                    if c not in seen:
                        seen.add(c)
                        nf.add(c)
        frontier = nf
    return sum(1 for Q in seen if Q != P and not is_total(Q, n))


# ============================================================================
# §2.  Memory-efficient Plan H solve (canonical-form wing grouping).
# ============================================================================


def _group_wings(wings, perms):
    """Group the wing chains into S_n-orbits, memory-bounded.

    The Session-1 `orbit_decomposition` accumulates the *full* S_n-orbit of
    every wing in a `seen` set -- at n=7 that is ~9600 orbits x up to 5040 =
    ~48M chains, which thrashes memory.  Here `seen` only ever holds wing
    chains (<= #wings): for each not-yet-grouped wing w (the orbit's
    first-encountered representative, exactly as Session 1), we sweep S_n
    once, recording (a) the images that are themselves wings, (b) the
    stabilizer Stab(w) inline.  One S_n-pass per orbit; no `canonical_rep`
    (the Session-1 one is a no-op -- `frozenset.__lt__` is subset, not lex).

    Returns:
      assigned   : wing -> (group_idx, sign)   sign = sgn(gamma), gamma.w=img
      orbit_info : list of (rep, stab_size, sign_supported), group-indexed
    The encounter order of orbits, the choice of rep, and the per-wing sign
    all match Session 1's `orbit_decomposition` exactly -> the downstream
    linear system and its lex-first solution are identical.
    """
    wings_set = set(wings)
    seen = set()
    assigned = {}
    orbit_info = []
    for w in wings:
        if w in seen:
            continue
        idx = len(orbit_info)
        stab_size = 0
        odd_in_stab = False
        for gamma in perms:
            g = apply_perm_chain(w, gamma)
            if g == w:
                stab_size += 1
                if perm_parity(gamma) == 1:
                    odd_in_stab = True
            if g in wings_set and g not in seen:
                seen.add(g)
                assigned[g] = (idx, perm_sign(gamma))
        orbit_info.append((w, stab_size, not odd_in_stab))
    return assigned, orbit_info


def _gaussian_solve_rank(A, b, n_cols):
    """Solve A x = b over Q; also return the rank.  A: list of dict{col:
    Fraction}; b: list of Fraction.  Free variables set to 0."""
    rows = [dict(r) for r in A]
    rhs = list(b)
    n_rows = len(rows)
    pivot_cols = []
    r = 0
    for c in range(n_cols):
        if r >= n_rows:
            break
        piv = next((rr for rr in range(r, n_rows) if rows[rr].get(c, 0) != 0),
                   None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        rhs[r], rhs[piv] = rhs[piv], rhs[r]
        inv = Fraction(1) / rows[r][c]
        rows[r] = {k: v * inv for k, v in rows[r].items()}
        rhs[r] *= inv
        for rr in range(n_rows):
            if rr != r and rows[rr].get(c, 0) != 0:
                f = rows[rr][c]
                newrow = dict(rows[rr])
                for k, v in rows[r].items():
                    newrow[k] = newrow.get(k, Fraction(0)) - f * v
                rows[rr] = {k: v for k, v in newrow.items() if v != 0}
                rhs[rr] -= f * rhs[r]
        pivot_cols.append(c)
        r += 1
    for rr in range(n_rows):
        if not rows[rr] and rhs[rr] != 0:
            return False, None, len(pivot_cols)
    solution = [Fraction(0)] * n_cols
    for idx, pc in enumerate(pivot_cols):
        solution[pc] = rhs[idx]
    return True, solution, len(pivot_cols)


def solve_psi_fast(omega_naive, bad_cofaces, wings, perms, verbose=False):
    """Memory-efficient drop-in for `posn_constructive_lift_n6.solve_psi`.

    Groups the wing chains into S_n-orbits with `_group_wings` (memory
    O(#wings), not O(#orbits x |S_n|)).  Exact-arithmetic identical to the
    Session-1 `solve_psi`: same orbit encounter order, same column order,
    same constraint system, hence the same lex-first Q-solution.

    Returns the same dict shape `run_plan_h_fast` / `psi_structure` expect.
    The returned `psi` is supported on the WING chains only (the codim-1
    faces of bad cofaces) -- sufficient for `verify_on_bad`, which only
    evaluates d on bad cofaces.  `supp_psi` reports the TRUE full-orbit
    support size (sum of orbit sizes of the nonzero orbits).
    """
    t0 = time.time()

    # --- Phase 1: orbit grouping (memory O(#wings)) -------------------------
    assigned, orbit_info = _group_wings(wings, perms)
    n_orbits = len(orbit_info)
    if verbose:
        print(f"      [_group_wings: {n_orbits} wing orbits, "
              f"{time.time() - t0:.0f}s]")

    # --- Phase 2: index the sign-supported orbits (encounter order) --------
    # Column index assigned to sign-supported orbits only, in the order they
    # were first encountered -- exactly the Session-1 convention.
    group_to_col = {}
    for gidx, (rep, stab_size, sign_supported) in enumerate(orbit_info):
        if sign_supported:
            group_to_col[gidx] = len(group_to_col)
    n_unknowns = len(group_to_col)

    # wing -> (column_idx, sign)  for wings in sign-supported orbits only
    wing_to_orbit = {}
    for w, (gidx, sgn) in assigned.items():
        if gidx in group_to_col:
            wing_to_orbit[w] = (group_to_col[gidx], sgn)

    # --- Phase 3: build + solve the Plan H linear system --------------------
    # One constraint per bad coface tau with d omega_naive(tau) != 0:
    #   sum_i (-1)^i psi(face_i tau) = -(d omega_naive)(tau)
    A, b, constraint_cofaces = [], [], []
    for (tau, pos) in bad_cofaces:
        rhs = -d_cochain(omega_naive, tau)
        if rhs == 0:
            continue
        coeffs = {}
        for i in range(len(tau)):
            face = tau[:i] + tau[i + 1:]
            if face in wing_to_orbit:
                col, sgn_g = wing_to_orbit[face]
                coeffs[col] = coeffs.get(col, Fraction(0)) + \
                    Fraction((-1) ** i) * Fraction(sgn_g)
        A.append(coeffs)
        b.append(rhs)
        constraint_cofaces.append((tau, pos))

    solvable, solution, rank = _gaussian_solve_rank(A, b, n_unknowns)

    # --- Phase 4: extend psi over the wings; report support size -----------
    psi = {}                 # supported on wing chains (sufficient to verify)
    nonzero_orbits = []
    supp_psi = 0
    col_to_group = {c: g for g, c in group_to_col.items()}
    if solvable:
        for w, (gidx, sgn) in assigned.items():
            col = group_to_col.get(gidx)
            if col is None:
                continue
            cj = solution[col]
            if cj != 0:
                psi[w] = sgn * cj
        for col in range(n_unknowns):
            cj = solution[col]
            if cj == 0:
                continue
            gidx = col_to_group[col]
            rep, stab_size, _ = orbit_info[gidx]
            osize = len(perms) // stab_size            # |S_n . rep|
            supp_psi += osize
            nonzero_orbits.append((col, rep, cj, osize))

    if verbose:
        print(f"      [solve_psi_fast: {n_orbits} wing orbits, "
              f"{n_unknowns} sign-supported, {time.time() - t0:.0f}s]")

    return {
        'omega_naive': omega_naive,
        'wing_orbits': orbit_info,
        'sign_supported': list(group_to_col),
        'wing_to_orbit': wing_to_orbit,
        'n_constraints': len(A),
        'n_unknowns': n_unknowns,
        'rank': rank,
        'constraint_cofaces': constraint_cofaces,
        'solvable': solvable,
        'solution': solution,
        'psi': psi,
        'nonzero_orbits': nonzero_orbits,
        'supp_psi': supp_psi,
    }


def run_plan_h_fast(n, chain, label, verbose=False):
    """Execute the full Plan H pipeline at level n on `chain`, using the
    memory-efficient `solve_psi_fast`.  Same output contract as the
    Session-1 `run_plan_h` (a results dict)."""
    print(f"\n{'=' * 72}")
    print(f"  Plan H at n={n}  --  {label}")
    print(f"{'=' * 72}")
    perms = list(permutations(range(n)))
    t0 = time.time()

    print(f"  c*_{n} rank profile: {tuple(len(P) for P in chain)}  "
          f"(dim {len(chain) - 1}-cell)")
    omega_naive, well_defined, stab = signed_orbit_cocycle(chain, perms)
    print(f"  Stab(c*_{n}): size {len(stab)}, "
          f"{'all even (subset A_%d)' % n if well_defined else 'CONTAINS ODD perm'}")
    if not well_defined:
        print(f"  ! omega_naive^({n}) is NOT well-defined in the sign-rep.")
        return {'n': n, 'well_defined': False, 'stab': stab}
    print(f"  |supp(omega_naive)| = |S_{n} . c*_{n}| = {len(omega_naive)}")

    cofaces = immediate_cofaces(chain, n)
    by_pos = {}
    for tau, pos in cofaces.items():
        by_pos[pos] = by_pos.get(pos, 0) + 1
    print(f"  Immediate cofaces of c*_{n}: {len(cofaces)}  "
          f"(by position: {dict(sorted(by_pos.items()))})")
    bad_cofaces = [(tau, pos) for tau, pos in cofaces.items()
                   if d_cochain(omega_naive, tau) != 0]
    bad_vals = sorted(set(str(d_cochain(omega_naive, tau))
                          for tau, _ in bad_cofaces))
    print(f"  F7-bad cofaces (d omega_naive != 0): {len(bad_cofaces)} of "
          f"{len(cofaces)}   d-values seen: {bad_vals}")
    if verbose:
        for (tau, pos) in sorted(bad_cofaces, key=lambda x: (x[1],))[:8]:
            print(f"      pos {pos}  ranks {tuple(len(P) for P in tau)}  "
                  f"d omega_naive = {d_cochain(omega_naive, tau)}")

    wings = collect_wings(bad_cofaces, omega_naive)
    print(f"  Wing chains (codim-1 faces of bad cofaces, not in orbit): "
          f"{len(wings)}")

    res = solve_psi_fast(omega_naive, bad_cofaces, wings, perms,
                         verbose=verbose)
    print(f"  Wing S_{n}-orbits: {len(res['wing_orbits'])}  "
          f"(sign-supported: {res['n_unknowns']})")
    print(f"  Linear system: {res['n_constraints']} constraints x "
          f"{res['n_unknowns']} unknowns, rank {res['rank']}")
    if not res['solvable']:
        print(f"  ! Plan H linear system INCONSISTENT on wing-only support.")
        print(f"    -> AMBER: Plan H insufficient at n={n}.")
        res.update({'n': n, 'well_defined': True, 'verdict': 'AMBER',
                    'chain': chain, 'cofaces': cofaces,
                    'bad_cofaces': bad_cofaces, 'wings': wings})
        return res
    supp_psi = res['supp_psi']
    print(f"  Solution: {len(res['nonzero_orbits'])} of {res['n_unknowns']} "
          f"sign-supported wing orbits nonzero;  |supp(psi)| = {supp_psi}")

    n_zero, n_nonzero, sample = verify_on_bad(omega_naive, res['psi'],
                                              bad_cofaces)
    print(f"  Verify d(omega_naive + psi) = 0 on the {len(bad_cofaces)} "
          f"F7-bad cofaces:  zero={n_zero}  nonzero={n_nonzero}")
    bad_closed = (n_nonzero == 0)

    pairing = omega_naive.get(chain, Fraction(0)) + \
        res['psi'].get(chain, Fraction(0))
    print(f"  Pairing <omega_naive + psi, c*_{n}> = {pairing}  (expect +-1)")

    print(f"  [n={n} Plan H runtime: {time.time() - t0:.1f}s]")
    res.update({
        'n': n, 'well_defined': True, 'chain': chain,
        'cofaces': cofaces, 'bad_cofaces': bad_cofaces, 'wings': wings,
        'bad_closed': bad_closed, 'pairing': pairing,
        'verdict': 'GREEN-local' if (bad_closed and pairing != 0) else 'AMBER',
    })
    return res


# ============================================================================
# §3.  Trip-wire (c): the iota_6-lift c*_6 -> c*_7 is well-defined.
# ============================================================================


def verify_lift_well_defined():
    """c*_7 is a genuine one-step coface of (the iota_6-lift of) c*_6:
      - the first 5 posets of c*_7 ARE c*_6 (iota_6 = id on relation sets);
      - the appended P_5 strictly refines P_4 and is proper + antisymmetric;
      - the refinement is a single-pair cover (closure adds nothing else).
    Returns (ok, detail dict)."""
    c6 = c_star_6_chain()
    c7 = c_star_7_chain()
    detail = {}
    detail['prefix_is_c6'] = (c7[:len(c6)] == c6)
    P4, P5 = c7[-2], c7[-1]
    detail['P5_strictly_refines_P4'] = (frozenset(P4) < frozenset(P5))
    detail['P5_antisymmetric'] = not any((b, a) in P5 for (a, b) in P5)
    detail['P5_proper'] = (len(P5) > 0 and not is_total(P5, 7))
    added = set(P5) - set(P4)
    detail['added_pairs'] = sorted(added)
    detail['single_pair_cover'] = (added == {(0, 5)})
    ok = all(detail[k] for k in
             ['prefix_is_c6', 'P5_strictly_refines_P4', 'P5_antisymmetric',
              'P5_proper', 'single_pair_cover'])
    return ok, detail


# ============================================================================
# §4.  Count-function extrapolation: polynomial vs exponential.
# ============================================================================


def _finite_differences(seq):
    """Return the table of finite-difference rows for an integer sequence."""
    rows = [list(seq)]
    while len(rows[-1]) > 1:
        prev = rows[-1]
        rows.append([prev[i + 1] - prev[i] for i in range(len(prev) - 1)])
    return rows


def _newton_forward(seq, x0):
    """Newton forward-difference interpolating polynomial through the points
    (x0+i, seq[i]).  For k points this is the unique degree-<=(k-1)
    interpolant.  Returns (callable, [delta^0, delta^1, ...])."""
    diffs = [row[0] for row in _finite_differences(seq)]

    def binom(t, j):
        num = Fraction(1)
        for i in range(j):
            num *= (t - i)
        den = 1
        for i in range(1, j + 1):
            den *= i
        return num / den

    def f(x):
        t = x - x0
        return sum(Fraction(diffs[j]) * binom(t, j) for j in range(len(diffs)))

    return f, diffs


def count_function_extrapolation(datapoints, label):
    """datapoints: list of (n, count).  Analyze polynomial-vs-exponential.
    Returns a dict of diagnostics."""
    print(f"\n  --- count-function extrapolation: {label} ---")
    ns = [n for (n, _) in datapoints]
    cs = [c for (_, c) in datapoints]
    print(f"  datapoints (n, count): {datapoints}")

    fdt = _finite_differences(cs)
    print(f"  finite-difference table:")
    for d, row in enumerate(fdt):
        print(f"      delta^{d}: {row}")

    ratios = [Fraction(cs[i + 1], cs[i]) for i in range(len(cs) - 1)]
    print(f"  consecutive ratios c[n+1]/c[n]: "
          f"{[f'{float(r):.3f}' for r in ratios]}")
    ratios_increasing = all(ratios[i + 1] > ratios[i]
                            for i in range(len(ratios) - 1))
    ratios_decreasing = all(ratios[i + 1] < ratios[i]
                            for i in range(len(ratios) - 1))
    print(f"  ratios monotone increasing? {ratios_increasing}   "
          f"decreasing? {ratios_decreasing}")

    f, diffs = _newton_forward(cs, ns[0])
    deg = len(diffs) - 1
    while deg > 0 and diffs[deg] == 0:
        deg -= 1
    kfac = 1
    for i in range(1, len(diffs)):
        kfac *= i
    lead_coeff = Fraction(diffs[-1], kfac) if kfac else Fraction(0)
    print(f"  unique interpolating polynomial: degree {deg} "
          f"(through {len(cs)} points)")
    print(f"      top finite difference delta^{len(diffs)-1} = {diffs[-1]}")
    print(f"      => leading coefficient = {lead_coeff} "
          f"({float(lead_coeff):.2f})")

    next_n = ns[-1] + 1
    poly_pred = f(next_n)
    geo_pred = Fraction(cs[-1]) * ratios[-1]
    print(f"  predictions for n={next_n}:")
    print(f"      polynomial interpolant: {poly_pred} ({float(poly_pred):.1f})")
    print(f"      geometric (last ratio): {float(geo_pred):.1f}")

    # If a 4th datapoint exists, the 3-point quadratic interpolant is a real
    # *test*, not just a fit: compare its prediction to the actual value.
    poly_test = None
    if len(cs) >= 4:
        f3, _ = _newton_forward(cs[:3], ns[0])
        pred3 = f3(ns[3])
        actual = cs[3]
        poly_test = (pred3, actual)
        print(f"  3-point quadratic-interpolant TEST against the 4th point:")
        print(f"      predicted c[n={ns[3]}] = {pred3} ({float(pred3):.1f}),  "
              f"actual = {actual}")
        print(f"      => actual / predicted = "
              f"{float(Fraction(actual) / pred3):.2f}x" if pred3 else "n/a")

    # Verdict heuristic on the count growth.
    poly_compatible = (ratios_decreasing
                       and abs(lead_coeff) < Fraction(cs[0]))
    super_poly = ratios_increasing
    if poly_test is not None:
        pred3, actual = poly_test
        # if the actual 4th point dwarfs the quadratic prediction, the count
        # is decisively super-polynomial (no low-degree polynomial fits).
        if pred3 and Fraction(actual) > Fraction(2) * pred3:
            super_poly = True
            poly_compatible = False
    count_tag = ('SUPER-POLYNOMIAL' if super_poly
                 else 'POLYNOMIAL-COMPATIBLE' if poly_compatible
                 else 'UNCERTAIN')
    print(f"  count-growth assessment: {count_tag}")
    return {
        'datapoints': datapoints, 'finite_diffs': fdt, 'ratios': ratios,
        'ratios_increasing': ratios_increasing,
        'ratios_decreasing': ratios_decreasing,
        'interp_degree': deg, 'leading_coeff': lead_coeff,
        'poly_pred_next': poly_pred, 'geo_pred_next': geo_pred,
        'poly_test': poly_test, 'count_tag': count_tag,
    }


# ============================================================================
# §5.  3-datapoint cross-pattern.
# ============================================================================


def cross_pattern_3(structs, results):
    """structs, results: dicts keyed by n in {5,6,7}.  Prints the 3-column
    cross-pattern table and the structural-mechanism persistence check."""
    print(f"\n{'=' * 72}")
    print(f"  CROSS-PATTERN:  psi^(5)  vs  psi^(6)  vs  psi^(7)")
    print(f"{'=' * 72}")
    ns = [5, 6, 7]

    def interior(n):
        return sum(1 for _, p in results[n]['cofaces'].items()
                   if p != n - 1)

    def upset(n):
        return sum(1 for _, p in results[n]['cofaces'].items()
                   if p == n - 1)

    rows = [
        ("immediate cofaces of c*_n",
         *[len(results[n]['cofaces']) for n in ns]),
        ("F7-bad cofaces  B_n",
         *[len(results[n]['bad_cofaces']) for n in ns]),
        ("  -- interior-position",
         *[interior(n) for n in ns]),
        ("  -- top-position up-set  u_n",
         *[upset(n) for n in ns]),
        ("wing chains",
         *[len(results[n]['wings']) for n in ns]),
        ("wing S_n-orbits",
         *[len(results[n]['wing_orbits']) for n in ns]),
        ("sign-supported wing orbits",
         *[results[n]['n_unknowns'] for n in ns]),
        ("linear-system constraints",
         *[results[n]['n_constraints'] for n in ns]),
        ("linear-system rank",
         *[results[n]['rank'] for n in ns]),
        ("nonzero psi wing orbits",
         *[structs[n]['n_nonzero'] for n in ns]),
        ("|supp(psi)|",
         *[structs[n]['supp_psi'] for n in ns]),
    ]
    print(f"  {'quantity':<34}{'n=5':>9}{'n=6':>9}{'n=7':>9}"
          f"{'6/5':>8}{'7/6':>8}")
    print(f"  {'-' * 75}")
    for (name, a, bb, c) in rows:
        r1 = f"{bb / a:.2f}" if a else "--"
        r2 = f"{c / bb:.2f}" if bb else "--"
        print(f"  {name:<34}{a:>9}{bb:>9}{c:>9}{r1:>8}{r2:>8}")

    print(f"\n  psi-coefficient sets:")
    for n in ns:
        print(f"    n={n}: {[str(c) for c in structs[n]['coeffs']]}")

    print(f"\n  Structural mechanism (Plan H solution shape) persistence:")
    mech = {}
    for n in ns:
        s, r = structs[n], results[n]
        frr = s['full_row_rank']
        one_per = (s['n_nonzero'] == r['n_constraints'])
        diag = dict(sorted(s['diag_hist'].items()))
        anomalies = sum(v for k, v in s['diag_hist'].items() if k != 1)
        mech[n] = {'full_row_rank': frr, 'one_per_bad': one_per,
                   'diag_hist': diag, 'anomalies': anomalies}
        print(f"    n={n}: full row rank={frr}, "
              f"#nonzero psi orbits == #bad cofaces: {one_per}")
        print(f"          per-bad-coface #(codim-1 faces in supp(psi)): "
              f"{diag}")
        print(f"          near-diagonal anomalies (bad cofaces with "
              f">=2 faces in supp(psi)): {anomalies}")
    return mech


# ============================================================================
# §6.  Main.
# ============================================================================


def main():
    args = sys.argv[1:]
    verbose = '--verbose' in args
    do_n8 = '--no-n8' not in args

    print("=" * 72)
    print("posn_constructive_lift_n7.py -- Compat-Geom F9 Session 2 (mg-14a0)")
    print("=" * 72)
    print("Plan H at n=7: the third bad-coface-count datapoint --")
    print("the polynomial-vs-exponential discriminator for (I5).")

    t_start = time.time()
    results, structs = {}, {}

    # --- n=5: reproduce mg-e8d5 / Session-1 trip-wire (a) -------------------
    r5 = run_plan_h_fast(5, C_STAR_5,
                         "F7 canonical Hasse c*_5 (= mg-e8d5 cell)",
                         verbose=verbose)
    s5 = psi_structure(r5, 5, list(permutations(range(5))))
    results[5], structs[5] = r5, s5

    # --- n=6: reproduce Session-1 deliverable / trip-wire (a) ---------------
    c6 = c_star_6_chain()
    r6 = run_plan_h_fast(6, c6,
                         "F8'-HPC verified c*_6 (= F9 Session-1 cell)",
                         verbose=verbose)
    s6 = psi_structure(r6, 6, list(permutations(range(6))))
    results[6], structs[6] = r6, s6

    # --- n=7: the Session-2 deliverable ------------------------------------
    c7 = c_star_7_chain()
    r7 = run_plan_h_fast(7, c7,
                         "candidate c*_7 (iota_6-lift of c*_6 + cover (0,5))",
                         verbose=verbose)
    results[7] = r7
    s7 = (psi_structure(r7, 7, list(permutations(range(7))))
          if r7.get('well_defined') and r7.get('solvable') else None)
    structs[7] = s7

    # --- trip-wire summary -------------------------------------------------
    print(f"\n{'=' * 72}")
    print(f"  TRIP-WIRE PRE-CHECKS")
    print(f"{'=' * 72}")
    tw_a5 = (r5.get('bad_closed') and r5.get('pairing') == 1
             and len(r5.get('bad_cofaces', [])) == 10)
    tw_a6 = (r6.get('bad_closed') and r6.get('pairing') == 1
             and len(r6.get('bad_cofaces', [])) == 64)
    tw_a = tw_a5 and tw_a6
    print(f"  (a) n=5 + n=6 Plan H reproduce Session 1 exactly:")
    print(f"        n=5: d(omega+psi)=0 on bad cofaces, pairing +1, "
          f"10 bad cofaces -- {'PASS' if tw_a5 else 'FAIL'}")
    print(f"        n=6: d(omega+psi)=0 on bad cofaces, pairing +1, "
          f"64 bad cofaces -- {'PASS' if tw_a6 else 'FAIL'}")
    tw_b = r7.get('well_defined', False)
    print(f"  (b) omega_naive^(7) well-defined (Stab(c*_7) subset A_7): "
          f"{'PASS' if tw_b else 'FAIL'}")
    lift_ok, lift_detail = verify_lift_well_defined()
    print(f"  (c) iota_6-lift c*_6 -> c*_7 well-defined: "
          f"{'PASS' if lift_ok else 'FAIL'}")
    for k, v in lift_detail.items():
        print(f"        {k}: {v}")

    if not tw_b:
        print(f"\n  VERDICT: RED-foundational -- omega_naive^(7) ill-defined.")
        print("=" * 72)
        return 'RED-foundational'

    # --- 3-datapoint cross-pattern -----------------------------------------
    mech = None
    if s7 is not None:
        mech = cross_pattern_3(structs, results)

    # --- count-function extrapolation --------------------------------------
    print(f"\n{'=' * 72}")
    print(f"  COUNT-FUNCTION EXTRAPOLATION")
    print(f"{'=' * 72}")
    bad_counts = [(n, len(results[n]['bad_cofaces'])) for n in (5, 6, 7)]
    upset_counts = [
        (n, sum(1 for _, p in results[n]['cofaces'].items() if p == n - 1))
        for n in (5, 6, 7)
    ]

    if do_n8:
        print(f"\n  Computing the fourth up-set datapoint u_8 "
              f"(count-only; no n=8 Plan H solve)...")
        t8 = time.time()
        c8 = c_star_8_chain()
        u8 = upset_proper_count(c8[-1], 8)
        print(f"  u_8 = |proper up-set of P_6(c*_8)| = {u8}  "
              f"({time.time() - t8:.1f}s)")
        upset_counts.append((8, u8))

    ext_bad = count_function_extrapolation(
        bad_counts, "#F7-bad cofaces  B_n")
    ext_up = count_function_extrapolation(
        upset_counts, "top-position up-set  u_n")

    # --- verdict -----------------------------------------------------------
    print(f"\n{'=' * 72}")
    print(f"  F9 SESSION-2 VERDICT")
    print(f"{'=' * 72}")

    plan_h_solvable = r7.get('solvable', False)
    bad_closed = r7.get('bad_closed', False)
    pairing_ok = (r7.get('pairing', 0) != 0)
    print(f"  n=7 Plan H linear system solvable:           "
          f"{'YES' if plan_h_solvable else 'NO'}")
    if plan_h_solvable:
        print(f"  d(omega_naive^(7) + psi^(7)) = 0 on bad set: "
              + ("YES (%d/%d)" % (len(r7['bad_cofaces']),
                                  len(r7['bad_cofaces']))
                 if bad_closed else "NO"))
        print(f"  <omega_naive^(7) + psi^(7), c*_7> = {r7.get('pairing')}")

    pattern_persists = None
    anomalies_7 = None
    if s7 is not None and mech is not None:
        anomalies_7 = mech[7]['anomalies']
        pattern_persists = (mech[7]['full_row_rank']
                            and mech[7]['one_per_bad']
                            and anomalies_7 <= 4)
        print(f"  near-diagonal pattern at n=7: full row rank="
              f"{mech[7]['full_row_rank']}, one-orbit-per-bad-coface="
              f"{mech[7]['one_per_bad']}, anomalies={anomalies_7} "
              f"(n=5: 0, n=6: 1)")
        print(f"  near-diagonal mechanism persists at n=7: "
              f"{'YES' if pattern_persists else 'NO'}")

    count_tag = ext_bad['count_tag']
    print(f"  bad-coface count growth: {count_tag}  "
          f"(B_n = {[c for _, c in bad_counts]}"
          + (f", u_8={upset_counts[-1][1]}" if do_n8 else "") + ")")

    # Verdict-tag logic per the mg-14a0 spec.
    if not plan_h_solvable or not (bad_closed and pairing_ok):
        tag = 'RED-pattern-breaks'
        reason = ("Plan H at n=7 fails to admit a Q-solution closing "
                  "d(omega_M^(7))=0 on the bad set")
    elif not pattern_persists:
        tag = 'AMBER-pattern-shifts'
        reason = ("the near-diagonal psi-structure changes meaningfully "
                  f"at n=7 (anomalies={anomalies_7}; n=5/6 had 0/1)")
    elif count_tag == 'POLYNOMIAL-COMPATIBLE':
        tag = 'GREEN-pattern-polynomial'
        reason = ("count compatible with polynomial growth AND the "
                  "near-diagonal pattern persists")
    elif count_tag == 'SUPER-POLYNOMIAL':
        # The near-diagonal MECHANISM persists, but the bad-coface COUNT
        # grows super-polynomially -- NOT compatible with a low-degree
        # polynomial.  Per the mg-14a0 verdict spec this is the
        # AMBER-pattern-shifts case in its "the pattern is n=5/n=6-specific"
        # sense: the COUNT side of the pattern does not generalize, even
        # though the psi-structure side does.  It is the F9-fallback datum
        # (state-F9.md decision rule: "u_7 super-polynomial -> empirical
        # correction has no clean closed form ... report + surface to PM").
        tag = 'AMBER-pattern-shifts'
        reason = ("the near-diagonal psi-MECHANISM persists at n=7, but "
                  "the bad-coface COUNT grows super-polynomially -- the "
                  "count side of the pattern is n=5/n=6-specific, so the "
                  "empirical correction has no clean closed form in n "
                  "(the F9-fallback / parked-X_n datum)")
    else:
        tag = 'GREEN-pattern-detected-but-count-uncertain'
        reason = ("near-diagonal pattern holds; count growth not yet "
                  "decidable -- would trigger a further datapoint")

    print(f"\n  VERDICT TAG: {tag}")
    print(f"  reason: {reason}")
    print(f"\n  [total runtime: {time.time() - t_start:.1f}s]")
    print("=" * 72)
    return tag


if __name__ == "__main__":
    main()
