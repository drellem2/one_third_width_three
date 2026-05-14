#!/usr/bin/env python3
r"""
posn_chamber_morse_n5_forman.py
================================

Compat-Geom F6 companion script (mg-8736).  Implements Forman cancellation
(Forman 1998 Adv. Math. 134, Thm 11.1) on top of the F5 (mg-1e58 @ `77440bd`)
greedy chamber matching, plus an extension of the BFT [3/11, 8/11] per-step
Pr-spectrum check from $c^*_5$ to all 4 critical cells of the F5 matching.

Predecessor: scripts/posn_chamber_morse_n5.py (F5, mg-1e58, 1025 LoC).
This script imports + reuses F5's pipeline up to the `(matching, critical,
by_dim)` triple, then layers Forman cancellation and the BFT extension on top.

§A.  Re-run F5 pipeline (delegated to posn_chamber_morse_n5 module).
§B.  Build the modified Hasse digraph H_M from F5's matching.
§C.  Enumerate gradient V-paths between each (critical (k+1)-cell,
     critical k-cell) pair; if unique, reverse the path to cancel.
§D.  Iterate cancellation until no further unique-path pair is found.
§E.  Verify the resulting matching is acyclic.
§F.  Extended BFT check: for each F5 critical cell (the 1 critical 2-cell,
     2 critical 3-cells, 1 critical 4-cell), lift to a chain in PPF_5 and
     report per-step Pr-values; check membership in [3/11, 8/11] for each
     of the 12 per-step values aggregated.
§G.  Verdict + summary.

Pure-Python stdlib only.  Targets commodity-hardware runtime ~10-15 min
(dominated by re-running the F5 pipeline; cancellation + BFT extension
add < 30 s).

Usage:
    python3 posn_chamber_morse_n5_forman.py [--verbose] [--skip-bft]

References:
  - Forman 1998, Adv. Math. 134, Theorem 11.1 (cancellation theorem).
  - Forman 2002, *A user's guide to discrete Morse theory*, §4.
  - Hersh, Welker, *Combinatorial structure of the discrete Morse complex*, 2017.
  - mg-1e58 (F5): scripts/posn_chamber_morse_n5.py.
  - mg-0e68 (F4): docs/compatibility-geometry-F4-inductive-survey.md.
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction

# Re-use F5's pipeline.
import posn_chamber_morse_n5 as F5
from posn_chamber_morse_n5 import (
    N,
    enumerate_partial_orders_incremental,
    variant_PPF,
    group_orbits,
    build_chamber_poset,
    compute_chamber_morse,
    verify_acyclic_modified_hasse,
    lift_chain_to_reps,
    per_step_pr_spectrum,
    ks_telescoped,
    count_linear_extensions,
    hasse_str,
    chain_hasse_str,
    poset_str,
)


# ============================================================================
# §B.  Modified Hasse digraph H_M from F5's matching.
# ============================================================================

def build_modified_hasse(matching, by_dim):
    """Build the modified Hasse digraph H_M.

    For each codim-1 pair (σ ⊂ τ):
      - If (σ, τ) is matched (M(σ) = τ):   add edge σ → τ.
      - Otherwise:                          add edge τ → σ.

    Returns:
      out_edges: dict chain (tuple) -> list of chain (tuple) targets.
      in_edges:  dict chain -> list of sources (inverse adjacency).
    """
    out_edges = {c: [] for d in by_dim for c in by_dim[d]}
    in_edges = {c: [] for d in by_dim for c in by_dim[d]}
    for d in sorted(by_dim):
        if d + 1 not in by_dim:
            continue
        for tau in by_dim[d + 1]:
            tau_fs = frozenset(tau)
            for i in range(len(tau)):
                sigma = tau[:i] + tau[i + 1:]
                sigma_fs = frozenset(sigma)
                m = matching.get(sigma_fs)
                # m = ('add', tau', idx) means M(sigma) = tau'.
                if m is not None and m[0] == 'add' and m[1] == tau_fs:
                    # Matched: σ → τ.
                    out_edges[sigma].append(tau)
                    in_edges[tau].append(sigma)
                else:
                    # Unmatched (between this σ and τ): τ → σ.
                    out_edges[tau].append(sigma)
                    in_edges[sigma].append(tau)
    return out_edges, in_edges


# ============================================================================
# §C.  Gradient V-path enumeration.
# ============================================================================

def enumerate_v_paths(start, target, out_edges, max_paths=10000,
                       max_nodes_per_path=50000):
    """Enumerate directed paths from `start` to `target` in H_M.

    Since H_M is acyclic (verified post-F5), DFS terminates.  We use an
    iterative DFS with explicit path stack.  Early-exits if more than
    `max_paths` are found (returns the bound + a flag).

    Returns:
      paths: list of paths (each a list of chains start → … → target).
      truncated: bool (True if hit max_paths).
    """
    paths = []
    truncated = False

    # Iterative DFS.  Stack holds (node, idx_into_out_edges, path_so_far).
    stack = [(start, 0, [start])]
    while stack:
        node, idx, path = stack[-1]
        if node == target:
            paths.append(list(path))
            if len(paths) >= max_paths:
                truncated = True
                break
            stack.pop()
            if len(path) > 1:
                # backtrack: pop popped node from caller's path.
                pass
            continue
        succ = out_edges.get(node, [])
        if idx >= len(succ):
            stack.pop()
            continue
        # Advance the iterator for this frame.
        stack[-1] = (node, idx + 1, path)
        nxt = succ[idx]
        if nxt in path:
            # Should not happen for acyclic H_M; defensive guard.
            continue
        if len(path) >= max_nodes_per_path:
            continue
        stack.append((nxt, 0, path + [nxt]))

    return paths, truncated


def count_v_paths_dp(start, target, out_edges, by_dim):
    """Count V-paths from `start` to `target` via DP on the acyclic H_M
    restricted to cells in some bounded region.

    Faster than enumeration when path counts are large; safer for verifying
    uniqueness (= 1).

    Strategy: compute N(c) := number of paths from c to target.
      N(target) = 1.
      N(c)      = Σ_{c' ∈ out_edges[c]} N(c').

    Bottom-up via reverse topological order; computed only on nodes
    reachable from start (forward) AND that can reach target (backward).
    """
    # Forward reachability from start.
    fwd = set()
    stack = [start]
    while stack:
        u = stack.pop()
        if u in fwd:
            continue
        fwd.add(u)
        for v in out_edges.get(u, []):
            if v not in fwd:
                stack.append(v)

    # Backward reachability to target (over reverse edges from target,
    # restricted to fwd).
    bwd = set()
    # Build reverse out-edges restricted to fwd.
    rev = {c: [] for c in fwd}
    for c in fwd:
        for d in out_edges.get(c, []):
            if d in fwd:
                rev[d].append(c)
    if target not in fwd:
        return 0
    stack = [target]
    while stack:
        u = stack.pop()
        if u in bwd:
            continue
        bwd.add(u)
        for v in rev[u]:
            if v not in bwd:
                stack.append(v)

    # Restrict to fwd ∩ bwd.  Topo-sort over out_edges (restricted).
    relevant = fwd & bwd
    if start not in relevant:
        return 0

    # Kahn's algorithm.
    in_deg = {c: 0 for c in relevant}
    for c in relevant:
        for d in out_edges.get(c, []):
            if d in relevant:
                in_deg[d] += 1
    queue = [c for c in relevant if in_deg[c] == 0]
    order = []
    while queue:
        u = queue.pop()
        order.append(u)
        for v in out_edges.get(u, []):
            if v in relevant:
                in_deg[v] -= 1
                if in_deg[v] == 0:
                    queue.append(v)

    # Reverse-order DP.
    N = {c: 0 for c in relevant}
    N[target] = 1
    for c in reversed(order):
        if c == target:
            continue
        total = 0
        for d in out_edges.get(c, []):
            if d in relevant:
                total += N[d]
        N[c] = total
    return N.get(start, 0)


# ============================================================================
# §D.  Forman cancellation: reverse V-path between critical (k+1, k) pair.
# ============================================================================

def find_unique_v_path(start, target, out_edges):
    """Find the unique V-path from start to target if one exists.

    Returns (path, count) where count is the total number of V-paths and
    path is the unique path (list of chains) iff count == 1 (else None).
    """
    n_paths = count_v_paths_dp(start, target, out_edges, None)
    if n_paths != 1:
        return None, n_paths
    paths, _ = enumerate_v_paths(start, target, out_edges, max_paths=2)
    if len(paths) != 1:
        # Defensive: DP says 1 but enumeration disagrees → caller can re-check.
        return None, len(paths)
    return paths[0], 1


def reverse_v_path_in_matching(matching, path):
    """Reverse the matching along the given V-path.

    The V-path alternates: τ_0=τ → σ_0 → τ_1 → σ_1 → … → τ_r → σ_r=σ.
    - τ → σ steps (fall): currently unmatched; AFTER cancellation, σ ↔ τ
      should be matched.
    - σ → τ steps (rise): currently matched (σ matched up to τ); AFTER
      cancellation, that pair is broken.

    Specifically:
      - For each (τ_i, σ_i) fall in the original path: add pair (σ_i, τ_i).
      - For each (σ_i, τ_{i+1}) rise: remove pair (σ_i, τ_{i+1}).

    Net effect on the critical set:
      - σ_r = σ (originally critical) gets matched with τ_r.
      - τ_0 = τ (originally critical) gets matched with σ_0.
      - All intermediate σ_i, τ_i remain matched, just to different partners.
    """
    # Path: [c_0, c_1, c_2, …, c_L] with L+1 chains, L edges.
    # Each consecutive pair (c_j, c_{j+1}) is either a fall or rise.
    new_matching = dict(matching)
    edges = list(zip(path[:-1], path[1:]))
    for (a, b) in edges:
        if len(a) > len(b):
            # Fall: a is (k+1)-cell, b is k-cell.  In M, (b, a) was NOT
            # matched.  AFTER reversal: match (b, a).
            sigma_fs = frozenset(b)
            tau_fs = frozenset(a)
            # Find next available idx; we'll re-index later.
            new_matching[sigma_fs] = ('add', tau_fs, -1)
            new_matching[tau_fs] = ('remove', sigma_fs, -1)
        else:
            # Rise: a is k-cell, b is (k+1)-cell.  In M, (a, b) WAS matched.
            # AFTER reversal: unmatch this specific pair.  Note we'll
            # re-match a and b along the fall edges flanking this rise.
            sigma_fs = frozenset(a)
            tau_fs = frozenset(b)
            # Only delete if this is currently the matched pair.
            if (new_matching.get(sigma_fs, (None, None, None))[0] == 'add'
                    and new_matching[sigma_fs][1] == tau_fs):
                del new_matching[sigma_fs]
            if (new_matching.get(tau_fs, (None, None, None))[0] == 'remove'
                    and new_matching[tau_fs][1] == sigma_fs):
                del new_matching[tau_fs]
    # Re-index sequentially.
    return new_matching


def recompute_critical(matching, by_dim):
    """Recompute the critical-cell dict from a matching."""
    critical = {}
    for d in sorted(by_dim):
        critical[d] = []
        for c in by_dim[d]:
            if frozenset(c) not in matching:
                critical[d].append(c)
    return critical


# ============================================================================
# §E.  Cancellation driver.
# ============================================================================

def attempt_cancellation_pass(matching, by_dim, verbose=False):
    """Run one pass of Forman cancellation: for each (critical (k+1)-cell,
    critical k-cell) pair, attempt to find a unique V-path.  If found,
    reverse it.  Return updated matching + records of cancellations.

    Note: we attempt pairs in order (highest k first), since cancelling
    a high-dim pair may free up a lower-dim pair.

    Returns (new_matching, cancellations_done, attempts_log).
    """
    critical = recompute_critical(matching, by_dim)
    out_edges, _ = build_modified_hasse(matching, by_dim)

    dims = sorted(critical)
    pairs = []
    for k in dims:
        if k + 1 not in critical:
            continue
        for tau in critical[k + 1]:
            for sigma in critical[k]:
                pairs.append((k, sigma, tau))
    # Prefer highest-dim pair first.
    pairs.sort(key=lambda p: (-p[0],))

    cancellations = []
    log = []
    cancelled_cells = set()

    for (k, sigma, tau) in pairs:
        if frozenset(sigma) in cancelled_cells or frozenset(tau) in cancelled_cells:
            continue
        if verbose:
            print(f"    examining pair: τ ({k+1}-cell) → σ ({k}-cell) ...")
        path, count = find_unique_v_path(tau, sigma, out_edges)
        log.append({
            'k': k,
            'sigma': sigma,
            'tau': tau,
            'v_path_count': count,
            'unique': (count == 1),
            'path_length_edges': (len(path) - 1) if path else None,
        })
        if path is not None and count == 1:
            if verbose:
                print(f"    ✓ unique V-path of length {len(path)-1} edges; cancelling.")
            matching = reverse_v_path_in_matching(matching, path)
            cancelled_cells.add(frozenset(sigma))
            cancelled_cells.add(frozenset(tau))
            cancellations.append({
                'k': k,
                'sigma': sigma,
                'tau': tau,
                'path': path,
                'path_length_edges': len(path) - 1,
            })
            # Rebuild H_M after each successful cancellation since the
            # matching changed.
            out_edges, _ = build_modified_hasse(matching, by_dim)
        else:
            if verbose:
                print(f"    ✗ V-path count = {count} (not unique); skipping.")
    return matching, cancellations, log


def iterate_cancellations(matching, by_dim, max_passes=5, verbose=False):
    """Iterate cancellation passes until no progress."""
    all_cancellations = []
    all_logs = []
    for pass_i in range(max_passes):
        critical = recompute_critical(matching, by_dim)
        total_crit = sum(len(v) for v in critical.values())
        if verbose:
            crit_vec = tuple(len(critical[d]) for d in sorted(critical))
            print(f"\n  --- Cancellation pass {pass_i+1}: critical-cell vector {crit_vec} ---")
        if total_crit <= 1:
            if verbose:
                print(f"    Reached singleton/empty critical set; stopping.")
            break
        matching, cancellations, log = attempt_cancellation_pass(
            matching, by_dim, verbose=verbose
        )
        all_cancellations.extend(cancellations)
        all_logs.append((pass_i + 1, log))
        if not cancellations:
            if verbose:
                print(f"    No cancellable pair found; stopping.")
            break
    return matching, all_cancellations, all_logs


# ============================================================================
# §F.  Extended BFT check across all 4 critical cells.
# ============================================================================

def bft_extension(critical, verbose=False):
    """For each critical cell of dim ≥ 2 in F5's greedy matching, lift the
    chain to PPF_5 and compute per-step Pr-values, checking BFT-sharp
    membership in [3/11, 8/11].

    Returns: list of dict per critical cell:
      {
        'dim': int,
        'cell_idx': int,
        'cell': chain,
        'lifted': lifted chain or None,
        'L_profile': tuple of |L| values,
        'pr_results': list of dicts (per-step),
        'bft_sharp_count': int,  # how many per-step Pr in [3/11, 8/11]
        'bft_total_steps': int,
      }
    """
    out = []
    three_eleven = Fraction(3, 11)
    eight_eleven = Fraction(8, 11)
    third = Fraction(1, 3)
    two_thirds = Fraction(2, 3)
    for d in sorted(critical):
        if d < 2:
            continue
        cells = critical[d]
        sorted_cells = sorted(
            cells, key=lambda c: tuple(tuple(sorted(P)) for P in c)
        )
        for idx, c in enumerate(sorted_cells):
            lifted = lift_chain_to_reps(c)
            if lifted is None:
                out.append({
                    'dim': d,
                    'cell_idx': idx,
                    'cell': c,
                    'lifted': None,
                    'L_profile': None,
                    'pr_results': None,
                    'bft_sharp_count': 0,
                    'bft_total_steps': 0,
                    'in_third_count': 0,
                })
                continue
            pr_results = per_step_pr_spectrum(lifted)
            L_profile = tuple(count_linear_extensions(P) for P in lifted)
            bft_count = sum(1 for r in pr_results if r['in_3_11_8_11'])
            in_third_count = sum(1 for r in pr_results if r['in_1_3_2_3'])
            out.append({
                'dim': d,
                'cell_idx': idx,
                'cell': c,
                'lifted': lifted,
                'L_profile': L_profile,
                'pr_results': pr_results,
                'bft_sharp_count': bft_count,
                'bft_total_steps': len(pr_results),
                'in_third_count': in_third_count,
            })
    return out


def report_bft_extension(rows):
    """Print the BFT extension table."""
    print(f"\n  --- §F.  Extended BFT [3/11, 8/11] check over all 4 critical cells ---\n")
    print(f"  {'dim':>4s}  {'idx':>4s}  {'|L|-profile':>26s}  {'#steps':>7s}  "
          f"{'#in [3/11,8/11]':>16s}  {'#in [1/3,2/3]':>15s}")
    print(f"  {'-'*4}  {'-'*4}  {'-'*26}  {'-'*7}  {'-'*16}  {'-'*15}")
    total_steps = 0
    total_bft = 0
    total_third = 0
    for r in rows:
        if r['lifted'] is None:
            print(f"  {r['dim']:>4d}  {r['cell_idx']:>4d}  "
                  f"{'(no lift available)':>26s}  {'-':>7s}  {'-':>16s}  {'-':>15s}")
            continue
        L_str = str(r['L_profile'])
        total_steps += r['bft_total_steps']
        total_bft += r['bft_sharp_count']
        total_third += r['in_third_count']
        print(f"  {r['dim']:>4d}  {r['cell_idx']:>4d}  {L_str:>26s}  "
              f"{r['bft_total_steps']:>7d}  "
              f"{r['bft_sharp_count']:>3d}/{r['bft_total_steps']:<3d}{'   ':>10s}  "
              f"{r['in_third_count']:>3d}/{r['bft_total_steps']:<3d}{'   ':>9s}")
    print(f"  {'-'*4}  {'-'*4}  {'-'*26}  {'-'*7}  {'-'*16}  {'-'*15}")
    print(f"  {'TOTAL':>4s}  {'':>4s}  {'':>26s}  {total_steps:>7d}  "
          f"{total_bft:>3d}/{total_steps:<3d}{'   ':>10s}  "
          f"{total_third:>3d}/{total_steps:<3d}{'   ':>9s}")
    print(f"\n  Per-step detail (each row below = 1 per-step value):")
    for r in rows:
        if r['lifted'] is None:
            continue
        for step_i, ps in enumerate(r['pr_results']):
            cov_str = ",".join(f"{a}<{b}" for (a, b) in sorted(ps['added_covers']))
            in_a = "✓" if ps['in_1_3_2_3'] else "✗"
            in_b = "✓" if ps['in_3_11_8_11'] else "✗"
            print(f"    dim {r['dim']} cell[{r['cell_idx']}] step {step_i}: "
                  f"Pr = {str(ps['Pr']):>6s} = {float(ps['Pr']):.4f}  "
                  f"[1/3,2/3]={in_a}  [3/11,8/11]={in_b}  covers={cov_str}")
    return total_steps, total_bft, total_third


# ============================================================================
# §G.  Main driver.
# ============================================================================

def main():
    args = sys.argv[1:]
    verbose = False
    skip_bft = False
    while args:
        a = args.pop(0)
        if a == "--verbose":
            verbose = True
        elif a == "--skip-bft":
            skip_bft = True
        else:
            print(f"Unknown arg {a}", file=sys.stderr)
            sys.exit(2)

    print("=" * 72)
    print("posn_chamber_morse_n5_forman.py — Compat-Geom F6 (mg-8736)")
    print("=" * 72)
    print()
    print(f"This script applies Forman cancellation (Forman 1998, Thm 11.1) to")
    print(f"F5's non-perfect greedy chamber matching on Δ(PPF_5/S_5), and")
    print(f"extends the BFT [3/11, 8/11] per-step Pr-spectrum check from")
    print(f"c*_5 (3 per-step values) to all 4 F5-critical cells.")
    print()

    # ----- §A.  Re-run F5 pipeline. -----
    t0 = time.time()
    orders = enumerate_partial_orders_incremental(N)
    ppf = variant_PPF(orders, N)
    print(f"  §A.1  Enumerated PPF_{N}:  |PPF_{N}| = {len(ppf)}  "
          f"({time.time()-t0:.1f}s)")

    t0 = time.time()
    orbits = group_orbits(ppf)
    print(f"  §A.2  Grouped into S_{N} orbits:  {len(orbits)} orbits  "
          f"({time.time()-t0:.1f}s)")

    t0 = time.time()
    reps, above = build_chamber_poset(orbits)
    print(f"  §A.3  Built chamber refinement poset  ({time.time()-t0:.1f}s)")

    t0 = time.time()
    matching, critical, by_dim, accepted_pairs, crit_aug = compute_chamber_morse(
        reps, above, target_dim=3, verbose=verbose
    )
    print(f"  §A.4  Greedy Morse matching computed  ({time.time()-t0:.1f}s)")

    t0 = time.time()
    acyc, num_arrows, sample = verify_acyclic_modified_hasse(matching, by_dim)
    print(f"  §A.5  Acyclicity verified: acyclic={acyc}, arrows={num_arrows}  "
          f"({time.time()-t0:.1f}s)")

    crit_vec_initial = tuple(len(critical[d]) for d in sorted(critical))
    print(f"\n  Initial critical-cell vector (F5 greedy):  {crit_vec_initial}")
    print(f"  Initial # critical cells:  {sum(crit_vec_initial)}")

    # ----- §B.  Build H_M. -----
    t0 = time.time()
    out_edges, in_edges = build_modified_hasse(matching, by_dim)
    n_edges = sum(len(v) for v in out_edges.values())
    print(f"\n  §B.   Built modified Hasse H_M: {n_edges} arrows  "
          f"({time.time()-t0:.1f}s)")

    # ----- §C-E.  V-path counts + Forman cancellation. -----
    print(f"\n  §C.   V-path enumeration between F5-critical pairs:\n")
    print(f"        Pair    |  dim(σ)  dim(τ)  |  # V-paths   |  unique?")
    print(f"        {'-'*8}-+-{'-'*8}-{'-'*8}-+-{'-'*12}-+-{'-'*8}")
    pre_canc_log = []
    pair_idx = 0
    for k in sorted(critical):
        if k + 1 not in critical:
            continue
        for tau in critical[k + 1]:
            for sigma in critical[k]:
                pair_idx += 1
                t0 = time.time()
                count = count_v_paths_dp(tau, sigma, out_edges, by_dim)
                dt = time.time() - t0
                pre_canc_log.append({
                    'pair_idx': pair_idx, 'k': k, 'sigma': sigma, 'tau': tau,
                    'count': count, 'time_s': dt,
                })
                print(f"        [{pair_idx}]      |  {k:>6d}  {k+1:>6d}  |  "
                      f"{count:>10d}  |  {'YES' if count == 1 else 'no':>5s}  "
                      f"({dt:.2f}s)")

    print(f"\n  §D.   Running iterative Forman cancellation passes...")
    matching_after, cancellations, all_logs = iterate_cancellations(
        matching, by_dim, max_passes=5, verbose=True
    )

    critical_after = recompute_critical(matching_after, by_dim)
    crit_vec_after = tuple(len(critical_after[d]) for d in sorted(critical_after))
    print(f"\n  Critical-cell vector after Forman cancellation:  {crit_vec_after}")
    print(f"  # cancellations performed:  {len(cancellations)}")
    for ci, c in enumerate(cancellations):
        print(f"    [{ci+1}]  dim {c['k']} ↔ dim {c['k']+1}; V-path length "
              f"{c['path_length_edges']} edges")
        print(f"         σ canonical reps: {chain_hasse_str(c['sigma'])}")
        print(f"         τ canonical reps: {chain_hasse_str(c['tau'])}")

    # ----- §E.  Verify the post-cancellation matching is acyclic. -----
    t0 = time.time()
    acyc2, num_arrows2, sample2 = verify_acyclic_modified_hasse(
        matching_after, by_dim
    )
    print(f"\n  §E.   Post-cancellation acyclicity: acyclic={acyc2}, "
          f"arrows={num_arrows2}  ({time.time()-t0:.1f}s)")
    if not acyc2:
        print(f"  ! Post-cancellation matching is NOT acyclic: cycle hint = {sample2}")
        print(f"  ! This is a bug; the V-path reversal should preserve acyclicity.")

    # ----- §F.  Extended BFT check. -----
    if not skip_bft:
        rows = bft_extension(critical, verbose=verbose)
        total_steps, total_bft, total_third = report_bft_extension(rows)
    else:
        total_steps = total_bft = total_third = 0
        rows = []

    # ----- §G.  Verdict. -----
    print(f"\n  --- §G.  F6 Verdict ---\n")
    total_crit_after = sum(crit_vec_after)
    print(f"  Initial critical-cell vector:   {crit_vec_initial}  (# = {sum(crit_vec_initial)})")
    print(f"  Final   critical-cell vector:   {crit_vec_after}  (# = {total_crit_after})")
    print(f"  Cancellations:                  {len(cancellations)}")
    print(f"  Acyclicity preserved:           {'YES' if acyc2 else 'NO'}")

    if not skip_bft:
        print(f"\n  Extended BFT check (per-step Pr in [3/11, 8/11]):")
        print(f"    Total per-step values evaluated: {total_steps}")
        print(f"    Number in [3/11, 8/11]:          {total_bft}")
        print(f"    Number in [1/3, 2/3]:            {total_third}")
        if total_steps > 0:
            print(f"    BFT-sharp fraction:              "
                  f"{total_bft}/{total_steps} = {total_bft/total_steps:.4f}")

    # Verdict logic.
    if total_crit_after == 0 and acyc2:
        verdict = "GREEN"
        verdict_msg = (
            "Forman cancellation succeeded.  Chamber is constructively "
            "contractible (zero critical cells)."
        )
    elif total_crit_after < sum(crit_vec_initial) and acyc2:
        verdict = "AMBER"
        verdict_msg = (
            f"Forman cancellation partial: {sum(crit_vec_initial)} → "
            f"{total_crit_after} critical cells."
        )
    elif not acyc2:
        verdict = "RED-bug"
        verdict_msg = (
            "Post-cancellation matching not acyclic — implementation bug."
        )
    else:
        verdict = "RED"
        verdict_msg = (
            "No V-path between any (k+1, k) critical pair; structural obstruction."
        )

    print(f"\n  VERDICT: {verdict}")
    print(f"           {verdict_msg}")
    print("\n" + "=" * 72)
    print(f"Done.  See docs/compatibility-geometry-F6-forman-cancellation.md")
    print(f"for the F6 scoping writeup (mg-8736).")
    print("=" * 72)


if __name__ == "__main__":
    main()
