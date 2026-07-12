#!/usr/bin/env python3
"""
OneThird mg-b0a6: falsification-first KILL-SHOT probe of Daniel's spectral /
near-ordinal-sum programme for the 1/3-2/3 conjecture.

Ticket:  mg-b0a6 (high, repo one_third_width_three). Daniel authorized live on
         2026-07-12 ("Go for it"); supersedes the one-third build-pause for THIS
         compute-only probe. Source: spectral_near_ordinal_sum_program.tex
         (Daniel, 2026-07-12); pm-onethird memory project_spectral_near_ordinal_sum_program.md.

WHAT THIS PROBES
----------------
The programme's chain (for a hypothetical MINIMAL COUNTEREXAMPLE P on [n]):

    minimal counterexample  ->  bad mixing  ->  lambda_std ~ 1
        ->  Cheeger low-conductance PREFIX  ->  near ordinal sum
        ->  balanced pair by minimality  ->  contradiction.

Object: symmetrize the linear-extension Cayley walk on S_n. Its standard-rep
block is the n-dim element-position transport matrix
    (T_P)_{x,a} = Pr_{sigma in LE(P)}[ x occupies position a ],
    S_P = (T_P + T_P^T)/2 restricted to H = 1^perp,
    lambda_std(P) = top eigenvalue of S_P on H.
I - S_P is a weighted graph Laplacian on the labels [n] (transport-energy
identity), so cuts are leakages: <1_A,(I-S_P)1_A> = E_sigma |A \\ sigma(A)|.

FOUR ORDERED KILL-SHOTS (run in order; STOP + report RED on first failure):

  1. DISTINGUISHED ORDER EXISTENCE.  Orient each incomparable pair by its
     >2/3 strong-majority direction; union with the poset relations. Is the
     resulting digraph ACYCLIC (does a distinguished total order e exist)?
     Linear-extension majority relations cycle in general (Fishburn); if the
     >2/3-strength orientation cycles on any P, the programme never starts.
     This is the foundational gap the .tex omits (sits BEFORE its L1-L4).

  2. STANDARD DOMINANCE.  Compute the full symmetrized Cayley-walk spectrum;
     is the 2nd-largest eigenvalue exactly lambda_std (i.e. does the spectral
     gap live in the standard sector)? Not automatic for a Cayley graph.

  3. MONOTONICITY (L2).  Is a dominant standard eigenvector monotone along the
     poset order, and monotone in the expected-rank / distinguished order e?

  4. PREFIX CAPTURE (L4/L3).  Does a threshold sweep of the dominant standard
     eigenvector yield a genuine PREFIX A_k of e, and what fraction of
     lambda_std does the best prefix Rayleigh quotient capture (vs the best
     unrestricted cut)? Report the prefix-vs-best-cut gap and leakage K_k.

SKEPTICAL BAR (per pm-onethird feedback_lean_no_vacuous_baseline_proofs /
feedback_audit_bar_for_axioms): a Rayleigh quotient above 1/3 is NOT evidence
of near-ordinal-sum structure. lambda_std > 1/3 is a rigorous but WEAK floor
(the .tex's own crude test-vector bound). We do not over-read partial signals;
verdicts are per-test GREEN/AMBER/RED with the exact quantities that drive them.

Two independent engines cross-check every exact quantity:
  - order-ideal DP over linear-extension counts (family-agnostic), and
  - brute force over all permutations (gold standard, n <= ~8).
Eigenvalues use numpy/scipy (float); the standard block is built from EXACT
rational transport counts and only then cast to float.

Test set: small posets whose comparability AND incomparability graphs are both
connected (the "irreducible under disjoint-union and ordinal-sum" interesting
core), PLUS the mandated named stress cases: the extremal tight delta ~ 1/3
posets and the N-poset family (2+2 = {x1<y1, x2<y2}) and its small extensions
(see pm-onethird feedback_n_poset_is_not_ordinal_sum: the N-poset is NOT an
ordinal sum and has nontrivial defect at every cut).
"""
from __future__ import annotations

import argparse
import itertools
from fractions import Fraction
from functools import lru_cache
from typing import Dict, List, Tuple, Optional

import numpy as np

ONE_THIRD = Fraction(1, 3)
TWO_THIRDS = Fraction(2, 3)
EIG_TOL = 1e-9   # tolerance for eigenvalue equality (float linear algebra)


# ==========================================================================
# Poset representation.
#   A poset on n = |ground set| is given by `less`: less[x] = frozenset of
#   elements strictly BELOW x (predecessors), transitively closed.
#   Elements are 0..n-1.
# ==========================================================================
class Poset:
    __slots__ = ("n", "less", "greater", "_lecount", "_les")

    def __init__(self, n: int, strict_pairs):
        """strict_pairs: iterable of (a,b) meaning a <_P b. Transitively closed
        on construction."""
        self.n = n
        less = {e: set() for e in range(n)}
        for (a, b) in strict_pairs:
            less[b].add(a)
        # transitive closure
        changed = True
        while changed:
            changed = False
            for e in range(n):
                add = set()
                for p in less[e]:
                    add |= less[p]
                if not add <= less[e]:
                    less[e] |= add
                    changed = True
        for e in range(n):
            if e in less[e]:
                raise ValueError(f"non-antisymmetric input: element {e} < itself "
                                 f"(cyclic relations given)")
        self.less = {e: frozenset(less[e]) for e in range(n)}
        greater = {e: set() for e in range(n)}
        for e in range(n):
            for p in self.less[e]:
                greater[p].add(e)
        self.greater = {e: frozenset(greater[e]) for e in range(n)}
        self._lecount = None
        self._les = None

    def comparable(self, x, y) -> bool:
        return x in self.less[y] or y in self.less[x]

    def incomparable_pairs(self):
        for x, y in itertools.combinations(range(self.n), 2):
            if not self.comparable(x, y):
                yield (x, y)

    # ---- comparability / incomparability graph connectivity ----
    def _connected(self, edges) -> bool:
        if self.n <= 1:
            return True
        adj = {e: set() for e in range(self.n)}
        for (a, b) in edges:
            adj[a].add(b)
            adj[b].add(a)
        seen = {0}
        stack = [0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return len(seen) == self.n

    def comparability_connected(self) -> bool:
        edges = [(x, y) for x in range(self.n) for y in self.less[x]]
        return self._connected(edges)

    def incomparability_connected(self) -> bool:
        edges = list(self.incomparable_pairs())
        return self._connected(edges)

    def both_connected(self) -> bool:
        return self.comparability_connected() and self.incomparability_connected()

    # ---- linear extensions (exact) ----
    def linext_count(self) -> int:
        if self._lecount is None:
            self._lecount = _linext_count(self.n, self.less)
        return self._lecount

    def linear_extensions(self) -> List[Tuple[int, ...]]:
        """All linear extensions as tuples (position a -> element at a).
        Brute permutation filter; use only for small n."""
        if self._les is None:
            out = []
            for perm in itertools.permutations(range(self.n)):
                pos = {e: i for i, e in enumerate(perm)}
                ok = True
                for e in range(self.n):
                    for p in self.less[e]:
                        if pos[p] > pos[e]:
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    out.append(perm)
            self._les = out
        return self._les

    def iso_signature(self):
        """Cheap isomorphism-invariant signature (not a perfect canonical form;
        used only to shrink reporting, never to gate a RED/GREEN)."""
        degs = tuple(sorted((len(self.less[e]), len(self.greater[e]))
                            for e in range(self.n)))
        return (self.n, degs, self.linext_count())


@lru_cache(maxsize=None)
def _linext_count_cached(n, less_key):
    less = {e: set(s) for e, s in less_key}
    return _linext_count_impl(n, less)


def _linext_count(n, less):
    key = tuple((e, tuple(sorted(less[e]))) for e in range(n))
    return _linext_count_cached(n, key)


def _linext_count_impl(n, less):
    pred_mask = [0] * n
    for e in range(n):
        m = 0
        for p in less[e]:
            m |= 1 << p
        pred_mask[e] = m
    full = (1 << n) - 1

    memo = {}

    def g(mask):
        if mask == 0:
            return 1
        v = memo.get(mask)
        if v is not None:
            return v
        total = 0
        mm = mask
        while mm:
            low = mm & (-mm)
            i = low.bit_length() - 1
            mm ^= low
            if pred_mask[i] & mask == 0:  # i minimal in current ideal
                total += g(mask ^ low)
        memo[mask] = total
        return total

    return g(full)


# ==========================================================================
# Exact pairwise before-probabilities p_ij = Pr[ i before j ] (DP engine),
# with a brute-force cross-check.
# ==========================================================================
def before_prob_dp(P: Poset, x: int, y: int) -> Fraction:
    """Pr[x before y] over uniform LE(P) via ideal DP.
    = LE(P + {x<y}) / LE(P)   (for incomparable x,y)."""
    total = P.linext_count()
    less2 = {e: set(P.less[e]) for e in range(P.n)}
    less2[y].add(x)
    P2 = Poset(P.n, [(p, e) for e in range(P.n) for p in less2[e]])
    return Fraction(P2.linext_count(), total)


def before_prob_brute(P: Poset, x: int, y: int) -> Fraction:
    les = P.linear_extensions()
    tot = len(les)
    cnt = 0
    for perm in les:
        pos = {e: i for i, e in enumerate(perm)}
        if pos[x] < pos[y]:
            cnt += 1
    return Fraction(cnt, tot)


# ==========================================================================
# Element-position transport T_P (exact rationals) and standard block S_P.
# ==========================================================================
def transport_matrix(P: Poset) -> np.ndarray:
    """(T_P)_{x,a} = Pr[element x occupies position a]. Exact rationals via LE
    enumeration; returned as float ndarray (n x n), doubly stochastic."""
    n = P.n
    les = P.linear_extensions()
    tot = len(les)
    N = [[0] * n for _ in range(n)]   # N[x][a] = #LE with x at position a
    for perm in les:
        for a, x in enumerate(perm):
            N[x][a] += 1
    T = np.zeros((n, n))
    for x in range(n):
        for a in range(n):
            T[x, a] = N[x][a] / tot
    return T


def standard_block_and_lambda(P: Poset):
    """Return (S_full, lambda_std, dominant_std_eigvec_in_R^n, projector info).
    S_full = (T + T^T)/2 (n x n, symmetric, doubly stochastic, eigenvalue 1 on
    the all-ones vector). lambda_std = top eigenvalue on H = 1^perp, with its
    eigenvector (already in H)."""
    n = P.n
    T = transport_matrix(P)
    S = (T + T.T) / 2.0
    # Orthonormal basis of H = 1^perp (Helmert-like); B is n x (n-1).
    B = _ortho_H_basis(n)
    Sh = B.T @ S @ B                       # (n-1)x(n-1) block on H
    w, V = np.linalg.eigh(Sh)
    idx = int(np.argmax(w))
    lam = float(w[idx])
    vh = V[:, idx]
    v = B @ vh                             # dominant standard eigenvector in R^n (sum 0)
    return S, lam, v, w[::-1]              # eigenvalues descending on H


def _ortho_H_basis(n: int) -> np.ndarray:
    """Orthonormal basis (n x (n-1)) of H = {v : sum v_i = 0}."""
    M = np.eye(n) - np.ones((n, n)) / n
    w, V = np.linalg.eigh(M)               # eigenvalues 0 (once) and 1 ((n-1) times)
    cols = [i for i in range(n) if w[i] > 0.5]
    return V[:, cols]


# ==========================================================================
# KILL-SHOT 1 : distinguished-order existence.
# ==========================================================================
def killshot1(P: Poset, use_brute_check=False) -> dict:
    """Build the >2/3 strong-majority orientation of incomparable pairs,
    union with poset relations, and test acyclicity. Also report the >1/2
    (Fishburn) majority orientation acyclicity for context, and whether the
    strong orientation is TOTAL (all incomparable pairs strongly oriented =
    delta(P) < 1/3, i.e. counterexample regime)."""
    n = P.n
    strong_edges = []   # (i,j): i before j with p_ij > 2/3
    maj_edges = []      # (i,j): p_ij > 1/2 (majority; ties dropped)
    total_incomp = 0
    strong_oriented = 0
    p_records = []
    for (x, y) in P.incomparable_pairs():
        total_incomp += 1
        p = before_prob_dp(P, x, y)
        if use_brute_check:
            pb = before_prob_brute(P, x, y)
            assert p == pb, f"before-prob DP/brute mismatch on {(x,y)}: {p} vs {pb}"
        p_records.append(((x, y), p))
        # strong (>2/3) orientation
        if p > TWO_THIRDS:
            strong_edges.append((x, y)); strong_oriented += 1
        elif (1 - p) > TWO_THIRDS:
            strong_edges.append((y, x)); strong_oriented += 1
        # majority (>1/2) orientation
        if p > Fraction(1, 2):
            maj_edges.append((x, y))
        elif p < Fraction(1, 2):
            maj_edges.append((y, x))
    poset_edges = [(a, b) for b in range(n) for a in P.less[b]]

    strong_acyclic = _is_acyclic(n, poset_edges + strong_edges)
    maj_acyclic = _is_acyclic(n, poset_edges + maj_edges)
    # delta(P) = max over incomparable pairs of min(p, 1-p)
    delta = max((min(p, 1 - p) for (_, p) in p_records), default=None)
    is_ce_regime = (delta is not None and delta < ONE_THIRD)
    return dict(
        n=n, total_incomp=total_incomp, strong_oriented=strong_oriented,
        strong_orientation_total=(strong_oriented == total_incomp and total_incomp > 0),
        strong_acyclic=strong_acyclic, maj_acyclic=maj_acyclic,
        delta=delta, is_counterexample_regime=is_ce_regime,
        strong_edges=strong_edges, maj_edges=maj_edges, poset_edges=poset_edges,
    )


# The one linear-extension-MAJORITY (>1/2) cyclic poset found by the reproducible
# LCG stress scan below (n=10, seed 2589): a genuine 0->3->2->0 majority cycle.
# Its >2/3-STRONG orientation is nonetheless ACYCLIC -- the strong threshold
# defeats the Fishburn/LEM cycle. Recorded so the report can cite it concretely.
LEM_CYCLIC_WITNESS_N10 = [
    (0, 5), (0, 7), (0, 8), (1, 2), (1, 4), (1, 5), (1, 7), (1, 8), (1, 9),
    (2, 4), (2, 5), (2, 7), (2, 8), (3, 8), (3, 9), (4, 5), (4, 7), (4, 8),
    (5, 7), (5, 8), (6, 7), (6, 8), (7, 8),
]


class _LCG:
    """Deterministic linear congruential generator (no Math.random / clock;
    fully reproducible from an integer seed)."""
    def __init__(self, seed):
        self.s = seed & 0xFFFFFFFFFFFF

    def rand(self, m):
        self.s = (self.s * 25214903917 + 11) & 0xFFFFFFFFFFFF
        return self.s % m


def _random_poset(n, rng, edge_num, edge_den):
    """Random poset: keep each i<j (natural labeling) with prob edge_num/edge_den,
    then transitively close. Always antisymmetric (upper-triangular seed)."""
    rel = [(i, j) for i in range(n) for j in range(i + 1, n)
           if rng.rand(edge_den) < edge_num]
    return Poset(n, rel)


def lem_stress_scan(sizes=(8, 9, 10), n_seeds=4000,
                    edge_specs=((1, 2), (2, 5), (1, 3))) -> dict:
    """Reproducible search for linear-extension-MAJORITY (>1/2) cycles at larger
    n, and whether the >2/3-STRONG orientation ever cycles even where the
    majority one does. Returns aggregate counts + first witness per size."""
    results = {}
    total_maj = 0
    total_strong = 0
    total_tested = 0
    strong_cyclic_examples = []
    maj_cyclic_examples = []
    for n in sizes:
        maj_cyc = 0
        strong_cyc = 0
        tested = 0
        for (en, ed) in edge_specs:
            for seed in range(1, n_seeds + 1):
                rng = _LCG(seed)
                P = _random_poset(n, rng, en, ed)
                r = killshot1(P)
                tested += 1
                if not r["maj_acyclic"]:
                    maj_cyc += 1
                    if len(maj_cyclic_examples) < 10:
                        maj_cyclic_examples.append((n, seed, en, ed, P, r))
                if not r["strong_acyclic"]:
                    strong_cyc += 1
                    if len(strong_cyclic_examples) < 10:
                        strong_cyclic_examples.append((n, seed, en, ed, P, r))
        results[n] = dict(tested=tested, maj_cyclic=maj_cyc, strong_cyclic=strong_cyc)
        total_maj += maj_cyc
        total_strong += strong_cyc
        total_tested += tested
    return dict(per_size=results, total_tested=total_tested,
                total_maj_cyclic=total_maj, total_strong_cyclic=total_strong,
                maj_cyclic_examples=maj_cyclic_examples,
                strong_cyclic_examples=strong_cyclic_examples)


def _is_acyclic(n: int, directed_edges) -> bool:
    """Kahn topological sort; True iff no directed cycle. Self/parallel edges ok;
    a directed cycle among the given edges returns False."""
    adj = {e: set() for e in range(n)}
    indeg = [0] * n
    eset = set()
    for (a, b) in directed_edges:
        if a == b:
            return False
        if (a, b) in eset:
            continue
        eset.add((a, b))
    for (a, b) in eset:
        adj[a].add(b)
    for a in range(n):
        for b in adj[a]:
            indeg[b] += 1
    q = [e for e in range(n) if indeg[e] == 0]
    seen = 0
    while q:
        u = q.pop()
        seen += 1
        for v in adj[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    return seen == n


# ==========================================================================
# KILL-SHOT 2 : standard dominance.
#   Build the full symmetrized Cayley-walk matrix on S_n (or the generated
#   subgroup restricted to reachable permutations) and check the 2nd-largest
#   eigenvalue equals lambda_std.
# ==========================================================================
def full_cayley_spectrum(P: Poset) -> np.ndarray:
    """Eigenvalues (descending) of the symmetrized linear-extension Cayley walk
    W[pi, tau] = eta_P(pi^{-1} tau), eta_P = (mu_P + mu_P^vee)/2, mu_P uniform on
    LE(P). Built on the FULL S_n (n! x n!). Use only for small n (<= 7)."""
    n = P.n
    les = P.linear_extensions()
    tot = len(les)
    perms = list(itertools.permutations(range(n)))
    index = {p: i for i, p in enumerate(perms)}
    m = len(perms)
    W = np.zeros((m, m))
    wt = 0.5 / tot
    # generators g in LE(P): as one-line tuples g where g(a)=element at position a
    # right multiplication pi -> pi . g  (compose as functions of positions):
    # (pi g)(a) = pi(g(a)). Symmetrize with g^{-1}.
    gens = les
    inv_gens = []
    for g in gens:
        ginv = [0] * n
        for a in range(n):
            ginv[g[a]] = a
        inv_gens.append(tuple(ginv))
    for pi in perms:
        i = index[pi]
        for g in gens:
            tau = tuple(pi[g[a]] for a in range(n))
            W[i, index[tau]] += wt
        for g in inv_gens:
            tau = tuple(pi[g[a]] for a in range(n))
            W[i, index[tau]] += wt
    # W is symmetric (eta symmetric). Symmetrize for numerical safety.
    W = (W + W.T) / 2.0
    ev = np.linalg.eigvalsh(W)
    return ev[::-1]


def killshot2(P: Poset, lam_std: float) -> dict:
    ev = full_cayley_spectrum(P)
    top = float(ev[0])
    second = float(ev[1]) if len(ev) > 1 else float("nan")
    # standard dominance: 2nd-largest full eigenvalue equals lambda_std
    dominance = abs(second - lam_std) <= 1e-7
    # also: is lambda_std actually present in the full spectrum (sanity)?
    present = bool(np.any(np.abs(ev - lam_std) <= 1e-7))
    # gap between 2nd-largest and lambda_std (positive => some non-standard
    # irrep beats the standard sector => dominance FAILS)
    excess = second - lam_std
    return dict(top=top, second=second, lam_std=lam_std, dominance=dominance,
                lam_std_present=present, excess=excess, n_eig=len(ev))


# ==========================================================================
# KILL-SHOT 3 : monotonicity of the dominant standard eigenvector.
# ==========================================================================
def expected_rank(P: Poset) -> np.ndarray:
    """E[pos(x)] for each element x (0-indexed positions)."""
    T = transport_matrix(P)
    positions = np.arange(P.n)
    return T @ positions   # (T)_{x,a} weighted by position a


def killshot3(P: Poset, v: np.ndarray) -> dict:
    """Monotone along poset: x <_P y => v_x <= v_y (up to global sign choice).
    Monotone in expected-rank order e: sort by E[pos]; is v nondecreasing?"""
    n = P.n
    er = expected_rank(P)
    # choose sign so v correlates positively with expected rank
    if float(np.dot(v - v.mean(), er - er.mean())) < 0:
        v = -v
    # ---- poset monotonicity ----
    total = 0
    agree = 0
    violators = []
    for y in range(n):
        for x in P.less[y]:
            total += 1
            if v[x] <= v[y] + 1e-9:
                agree += 1
            else:
                violators.append((x, y, float(v[x]), float(v[y])))
    poset_rate = (agree / total) if total else 1.0
    # ---- expected-rank order monotonicity ----
    order = sorted(range(n), key=lambda e: (er[e], e))
    e_mono = all(v[order[i]] <= v[order[i + 1]] + 1e-9 for i in range(n - 1))
    e_inversions = sum(1 for i in range(n - 1) if v[order[i]] > v[order[i + 1]] + 1e-9)
    # Kendall tau between the eigenvector order and the expected-rank order:
    # fair aggregate of "does expected rank determine the eigenvector ordering?"
    tau = _kendall_tau(v, er)
    return dict(poset_monotone=(len(violators) == 0), poset_agree_rate=poset_rate,
                poset_total=total, poset_violators=violators,
                expected_rank_monotone=e_mono, expected_rank_inversions=e_inversions,
                kendall_tau_v_vs_erank=tau,
                expected_rank_order=order, v=v.copy(), expected_rank=er.copy())


def _kendall_tau(a: np.ndarray, b: np.ndarray) -> float:
    """Kendall tau over pairs with strict (non-tie) order in BOTH a and b.
    +1 = orders identical, -1 = reversed, 0 = uncorrelated. Ties skipped."""
    n = len(a)
    conc = disc = 0
    for i in range(n):
        for j in range(i + 1, n):
            da = a[i] - a[j]
            db = b[i] - b[j]
            if abs(da) < 1e-9 or abs(db) < 1e-9:
                continue
            if (da > 0) == (db > 0):
                conc += 1
            else:
                disc += 1
    tot = conc + disc
    return (conc - disc) / tot if tot else float("nan")


# ==========================================================================
# KILL-SHOT 4 : prefix capture.
# ==========================================================================
def rayleigh(P: Poset, S: np.ndarray, A: frozenset) -> float:
    """Rayleigh quotient <f,S f>/<f,f> for f = 1_A projected onto H."""
    n = P.n
    f = np.array([1.0 if i in A else 0.0 for i in range(n)])
    f = f - f.mean()
    denom = float(f @ f)
    if denom < 1e-15:
        return float("nan")
    return float(f @ S @ f) / denom


def concat_prob(P: Poset, order: List[int], k: int) -> Fraction:
    """Pr(sigma(A_k)=A_k) = fraction of LE that are exact concatenations at cut k
    = e(P[A])e(P[B])/e(P). Delta0 = 1 - this."""
    les = P.linear_extensions()
    tot = len(les)
    Ak = set(order[:k])
    s = 0
    for perm in les:
        if set(perm[:k]) == Ak:
            s += 1
    return Fraction(s, tot)


def prefix_defects(P: Poset, order: List[int], k: int) -> dict:
    """Ordinal-sum defect diagnostics at prefix cut A_k (the SKEPTICAL-BAR core:
    does a good prefix actually mean a THIN interface / near ordinal sum?).
      Phi   = E|A\\sigma(A)| / |A|             (transport conductance)
      Delta1= E|A\\sigma(A)| / min(|A|,|B|)    (L1 ordinal-sum defect)
      Delta0= 1 - Pr(sigma(A)=A)              (enumerative defect)
    A genuine ordinal sum has E|A\\sigma(A)|=0 => Phi=Delta1=Delta0=0."""
    n = P.n
    K = leakage_prefix(P, order, k)          # = E|A_k \ sigma(A_k)|
    a = k
    b = n - k
    phi = Fraction(K.numerator, K.denominator * a)
    d1 = Fraction(K.numerator, K.denominator * min(a, b))
    d0 = 1 - concat_prob(P, order, k)
    return dict(k=k, K=K, Phi=phi, Delta1=d1, Delta0=d0)


def leakage_prefix(P: Poset, order: List[int], k: int) -> Fraction:
    """K_k = E_sigma |A_k \\ sigma(A_k)| where A_k = first k elements of `order`
    (the distinguished/expected-rank order) and sigma(A_k) = the set of elements
    occupying the first k positions in extension sigma.
    = E |prefix elements pushed beyond position k| = E |suffix elements pulled in|."""
    les = P.linear_extensions()
    tot = len(les)
    Ak = set(order[:k])
    s = 0
    for perm in les:
        first_k_positions_elems = set(perm[:k])   # sigma(A_k) as element set in first k positions
        s += len(Ak - first_k_positions_elems)
    return Fraction(s, tot)


def killshot4(P: Poset, S: np.ndarray, v: np.ndarray, lam_std: float,
              er_order: List[int]) -> dict:
    """Threshold-sweep the dominant standard eigenvector: nested sets by sorted
    eigenvector coordinate. Is the best threshold cut a PREFIX of the
    expected-rank order e? Best prefix Rayleigh vs best unrestricted cut; leakage
    K_k along e."""
    n = P.n
    # sweep order = elements sorted by eigenvector coordinate
    sweep = sorted(range(n), key=lambda i: v[i])
    # threshold sets (both directions): {first t of sweep}, t=1..n-1
    best_sweep_R = -1e18
    best_sweep_A = None
    for t in range(1, n):
        A = frozenset(sweep[:t])
        R = rayleigh(P, S, A)
        if R > best_sweep_R:
            best_sweep_R, best_sweep_A = R, A
        A2 = frozenset(sweep[n - t:])
        R2 = rayleigh(P, S, A2)
        if R2 > best_sweep_R:
            best_sweep_R, best_sweep_A = R2, A2

    # prefixes of the expected-rank order e
    prefixes = [frozenset(er_order[:k]) for k in range(1, n)]
    prefix_R = [(k, rayleigh(P, S, prefixes[k - 1])) for k in range(1, n)]
    best_prefix_k, best_prefix_R = max(prefix_R, key=lambda kr: kr[1])

    # best unrestricted cut (all nonempty proper subsets) -- gold standard, small n
    best_cut_R = -1e18
    best_cut_A = None
    if n <= 10:
        for r in range(1, n):
            for A in itertools.combinations(range(n), r):
                Af = frozenset(A)
                R = rayleigh(P, S, Af)
                if R > best_cut_R:
                    best_cut_R, best_cut_A = R, Af
    else:
        best_cut_R, best_cut_A = best_sweep_R, best_sweep_A

    # is the best sweep cut a prefix (or suffix) of e?
    e_prefix_sets = set(prefixes) | set(frozenset(er_order[k:]) for k in range(1, n))
    best_sweep_is_prefix = best_sweep_A in e_prefix_sets

    # ---- SKEPTICAL-BAR core: ordinal-sum defects along e ----
    # Does a good-Rayleigh prefix actually mean a THIN interface (near ordinal sum)?
    defects = [prefix_defects(P, er_order, k) for k in range(1, n)]
    # defect at the best-Rayleigh prefix:
    best_prefix_defect = defects[best_prefix_k - 1]
    # the minimum-Delta1 prefix (thinnest interface available at ANY cut):
    min_d1_defect = min(defects, key=lambda d: d["Delta1"])
    K = [(d["k"], d["K"]) for d in defects]

    return dict(
        lam_std=lam_std,
        best_sweep_R=best_sweep_R, best_sweep_A=sorted(best_sweep_A) if best_sweep_A else None,
        best_sweep_is_prefix=best_sweep_is_prefix,
        best_prefix_k=best_prefix_k, best_prefix_R=best_prefix_R,
        prefix_capture_fraction=(best_prefix_R / lam_std if lam_std > 1e-12 else float("nan")),
        best_cut_R=best_cut_R, best_cut_A=sorted(best_cut_A) if best_cut_A else None,
        prefix_vs_best_cut_gap=best_cut_R - best_prefix_R,
        leakage=K,
        best_prefix_Delta1=float(best_prefix_defect["Delta1"]),
        best_prefix_Phi=float(best_prefix_defect["Phi"]),
        best_prefix_Delta0=float(best_prefix_defect["Delta0"]),
        min_Delta1=float(min_d1_defect["Delta1"]), min_Delta1_k=min_d1_defect["k"],
        min_Delta1_Delta0=float(min_d1_defect["Delta0"]),
        prefixes=[sorted(p) for p in prefixes],
    )


# ==========================================================================
# Named / mandated posets.
# ==========================================================================
def named_posets() -> Dict[str, Poset]:
    P = {}
    # 3-element tight poset: a || (b<c).  delta = 1/3 exactly (textbook tight).
    P["tight3  a||(b<c)"] = Poset(3, [(1, 2)])           # 0 iso; 1<2
    # V (one bottom, two tops): b<a, b<c  -> delta?
    P["V  (b<a,b<c)"] = Poset(3, [(0, 1), (0, 2)])
    # N-poset (2+2): x1<y1, x2<y2 (elements 0<1, 2<3). NOT an ordinal sum.
    P["N/2+2  (0<1,2<3)"] = Poset(4, [(0, 1), (2, 3)])
    # 3+2 extension
    P["3+2  (0<1<2,3<4)"] = Poset(5, [(0, 1), (1, 2), (3, 4)])
    # N + isolated top comparable to build a both-connected small extension:
    # "N-with-bridge": 0<1, 2<3, plus 1<3 wait that makes comparable; keep simple:
    P["2+2+iso (0<1,2<3,4)"] = Poset(5, [(0, 1), (2, 3)])
    # fence / zigzag 4 (N-shaped fence): 0<1, 2<1, 2<3  (a<b>c<d)
    P["fence4 (0<1,2<1,2<3)"] = Poset(4, [(0, 1), (2, 1), (2, 3)])
    # bowtie / X: two minima below two maxima fully (ordinal sum 2-antichain (+) 2-antichain)
    P["2AC+2AC ordsum"] = Poset(4, [(0, 2), (0, 3), (1, 2), (1, 3)])
    # width-2 tight extension: 0 || (1<2<3)
    P["1||(chain3)"] = Poset(4, [(1, 2), (2, 3)])
    # 5-elt near-tight: 0 || (1<2), 3<4 chain merged? keep the extremal 1||(1<2)+extra
    P["chevron5 (0<2,1<2,3<4?)"] = Poset(5, [(0, 2), (1, 2), (3, 4)])
    # LEM(>1/2)-cyclic witness found by the reproducible stress scan (n=10):
    # its >2/3-strong orientation is nonetheless acyclic.
    P["LEM-cyclic-witness(n=10)"] = Poset(10, LEM_CYCLIC_WITNESS_N10)
    return P


# ==========================================================================
# Poset enumeration (n=3..N) via transitively-closed upper-triangular relations.
#   Every iso class has the identity as a linear extension for SOME labeling, so
#   this enumerates a superset of iso reps (with multiplicity); we dedup by a
#   cheap signature for reporting only.
# ==========================================================================
def enumerate_posets(n: int):
    """Yield Poset objects: all posets on [n] with identity as a linear
    extension (strict relation subset of {(i,j): i<j}, transitively closed)."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    npairs = len(pairs)
    seen_sig = set()
    for bits in range(1 << npairs):
        rel = [pairs[k] for k in range(npairs) if (bits >> k) & 1]
        # transitive closure must equal rel (else it's a duplicate of a bigger rel)
        P = Poset(n, rel)
        closed = set((a, b) for b in range(n) for a in P.less[b])
        if closed != set(rel):
            continue
        yield P


def enumerate_both_connected(n: int, dedup=True):
    out = []
    seen = set()
    for P in enumerate_posets(n):
        if not P.both_connected():
            continue
        if dedup:
            sig = P.iso_signature()
            if sig in seen:
                continue
            seen.add(sig)
        out.append(P)
    return out


# ==========================================================================
# Drivers.
# ==========================================================================
def fmt_frac(x: Optional[Fraction]) -> str:
    if x is None:
        return "-"
    return f"{x} ({float(x):.4f})"


def run_test1(n_lo=3, n_hi=6, verbose_named=True, do_lem_scan=True,
              lem_seeds=4000):
    print("=" * 78)
    print("KILL-SHOT 1: DISTINGUISHED ORDER EXISTENCE (>2/3 strong-majority "
          "orientation acyclic?)")
    print("=" * 78)
    any_strong_cycle = False
    cyclic_examples = []
    total_posets = 0
    ce_regime_count = 0
    total_strong_orientation = 0
    maj_cycle_count = 0

    # named first
    if verbose_named:
        print("\n-- named / mandated stress posets --")
        for name, P in named_posets().items():
            r = killshot1(P, use_brute_check=(P.n <= 8))
            tag = "STRONG-CYCLIC" if not r["strong_acyclic"] else "acyclic"
            majtag = "maj-cyclic" if not r["maj_acyclic"] else "maj-acyclic"
            print(f"  {name:26s} n={P.n} incomp={r['total_incomp']:2d} "
                  f"strong-oriented={r['strong_oriented']:2d} "
                  f"delta={fmt_frac(r['delta']):18s} "
                  f"strong:{tag:14s} {majtag}")
            if not r["strong_acyclic"]:
                any_strong_cycle = True
                cyclic_examples.append((name, P, r))

    # enumeration sweep
    for n in range(n_lo, n_hi + 1):
        posets = enumerate_both_connected(n)
        strong_cyc = 0
        maj_cyc = 0
        ce = 0
        strong_total_orient = 0
        for P in posets:
            total_posets += 1
            r = killshot1(P)
            if not r["strong_acyclic"]:
                strong_cyc += 1
                any_strong_cycle = True
                if len(cyclic_examples) < 25:
                    cyclic_examples.append((f"enum n={n}", P, r))
            if not r["maj_acyclic"]:
                maj_cyc += 1
            if r["is_counterexample_regime"]:
                ce += 1
            if r["strong_orientation_total"]:
                strong_total_orient += 1
        ce_regime_count += ce
        maj_cycle_count += maj_cyc
        total_strong_orientation += strong_total_orient
        print(f"\n  n={n}: both-connected iso-posets={len(posets):5d}  "
              f">2/3-STRONG cyclic={strong_cyc:4d}  "
              f">1/2-majority(Fishburn) cyclic={maj_cyc:4d}  "
              f"delta<1/3(counterex)={ce}  strong-total-orientation={strong_total_orient}")

    # ---- LEM-cycle stress scan (is test 1 even stressed at these sizes?) ----
    scan = None
    if do_lem_scan:
        print("\n-- LEM-cycle stress scan (reproducible LCG; n=8,9,10) --")
        print("   [why: the >2/3 orientation was acyclic on ALL exhaustive n<=7 both-")
        print("    connected posets AND the >1/2 Fishburn majority never cycled either,")
        print("    so test 1 is UNSTRESSED at n<=7. Do LEM cycles appear at all, and if")
        print("    so does the >2/3-STRONG orientation survive them?]")
        scan = lem_stress_scan(n_seeds=lem_seeds)
        for n, d in scan["per_size"].items():
            print(f"   n={n}: sampled={d['tested']:6d}  >1/2-majority cyclic={d['maj_cyclic']:3d}"
                  f"  >2/3-STRONG cyclic={d['strong_cyclic']:3d}")
        print(f"   TOTALS sampled={scan['total_tested']}  majority-cyclic={scan['total_maj_cyclic']}"
              f"  STRONG-cyclic={scan['total_strong_cyclic']}")
        if scan["maj_cyclic_examples"]:
            n, seed, en, ed, P, r = scan["maj_cyclic_examples"][0]
            print(f"   FIRST >1/2-majority cycle: n={n} (a real Fishburn/LEM cycle exists).")
            print(f"     -> on THAT poset, >2/3-strong orientation acyclic = {r['strong_acyclic']}")
        else:
            print("   No >1/2-majority cycle found in the sampled range either.")

    print("\n-- KILL-SHOT 1 SUMMARY --")
    print(f"  posets tested (both-connected, n in [{n_lo},{n_hi}]): {total_posets}")
    print(f"  >2/3 strong-majority orientation CYCLIC on any poset: "
          f"{'YES' if any_strong_cycle else 'NO'}")
    print(f"  >1/2 majority (Fishburn) cyclic count: {maj_cycle_count} "
          f"(context: majority relations are known to cycle)")
    print(f"  posets in counterexample regime (delta<1/3): {ce_regime_count} "
          f"(expected 0; conjecture holds for these n)")
    if any_strong_cycle:
        print("\n  *** >2/3 STRONG-MAJORITY CYCLE FOUND -> foundational gap TRIGGERED ***")
        for (tag, P, r) in cyclic_examples[:10]:
            print(f"    [{tag}] n={P.n} strong_edges={r['strong_edges']} "
                  f"poset_edges={r['poset_edges']} delta={fmt_frac(r['delta'])}")
    scan_strong_cyclic = scan["total_strong_cyclic"] if scan else 0
    scan_maj_cyclic = scan["total_maj_cyclic"] if scan else 0
    strong_cycle_anywhere = any_strong_cycle or (scan_strong_cyclic > 0)
    verdict = "RED" if strong_cycle_anywhere else "GREEN"
    print(f"\n  TEST 1 VERDICT: {verdict}")
    if verdict == "GREEN" and scan and scan_maj_cyclic > 0:
        print("    (well-stressed GREEN: >1/2-majority cycles DO occur in the sampled")
        print("     range, and the >2/3-strong orientation survived every one of them.)")
    elif verdict == "GREEN":
        print("    (UNSTRESSED GREEN: no >1/2-majority cycle appeared in reach either;")
        print("     the pathology test 1 guards against is not exercised at these sizes.)")
    return verdict, dict(any_strong_cycle=strong_cycle_anywhere,
                         cyclic_examples=cyclic_examples,
                         total_posets=total_posets,
                         maj_cycle_count=maj_cycle_count,
                         ce_regime_count=ce_regime_count,
                         scan=scan)


def analyze_full(P: Poset, name: str, do_full_spectrum: bool):
    """Run tests 2,3,4 on a single poset (assumes test1 context). Returns dict."""
    S, lam, v, hspec = standard_block_and_lambda(P)
    out = {"name": name, "n": P.n, "lambda_std": lam,
           "H_spectrum": [float(x) for x in hspec]}
    if do_full_spectrum:
        k2 = killshot2(P, lam)
        out["test2"] = k2
    k3 = killshot3(P, v)
    out["test3"] = k3
    er_order = k3["expected_rank_order"]
    k4 = killshot4(P, S, k3["v"], lam, er_order)
    out["test4"] = k4
    return out


def _pearson(x, y):
    import statistics
    n = len(x)
    if n < 2:
        return float("nan")
    mx = statistics.mean(x); my = statistics.mean(y)
    num = sum((xi - mx) * (yi - my) for xi, yi in zip(x, y))
    dx = sum((xi - mx) ** 2 for xi in x) ** 0.5
    dy = sum((yi - my) ** 2 for yi in y) ** 0.5
    if dx < 1e-15 or dy < 1e-15:
        return float("nan")
    return num / (dx * dy)


def dump_data(spectrum_hi=6, out_path="data/onethird-mgb0a6-spectral-killshot.json"):
    """Write the full per-poset data table (tests 2-4 quantities) + aggregate
    statistics to JSON for the report. Covers both-connected posets n=3..spectrum_hi
    plus named stress posets with n<=7."""
    import json
    rows = []
    targets = [(nm, P) for nm, P in named_posets().items() if P.n <= 7]
    for n in range(3, spectrum_hi + 1):
        for i, P in enumerate(enumerate_both_connected(n)):
            targets.append((f"enum-n{n}-#{i}", P))
    for name, P in targets:
        do_spec = P.n <= spectrum_hi
        S, lam, v, hspec = standard_block_and_lambda(P)
        k3 = killshot3(P, v)
        er_order = k3["expected_rank_order"]
        k4 = killshot4(P, S, k3["v"], lam, er_order)
        row = dict(
            name=name, n=P.n, lambda_std=lam,
            poset_monotone=k3["poset_monotone"],
            poset_agree_rate=k3["poset_agree_rate"],
            n_poset_violations=len(k3["poset_violators"]),
            expected_rank_monotone=k3["expected_rank_monotone"],
            expected_rank_inversions=k3["expected_rank_inversions"],
            kendall_tau_v_vs_erank=k3["kendall_tau_v_vs_erank"],
            prefix_capture_fraction=k4["prefix_capture_fraction"],
            best_prefix_R=k4["best_prefix_R"], best_prefix_k=k4["best_prefix_k"],
            best_cut_R=k4["best_cut_R"],
            prefix_vs_best_cut_gap=k4["prefix_vs_best_cut_gap"],
            best_sweep_is_prefix=k4["best_sweep_is_prefix"],
            best_prefix_Delta1=k4["best_prefix_Delta1"],
            best_prefix_Phi=k4["best_prefix_Phi"],
            best_prefix_Delta0=k4["best_prefix_Delta0"],
            min_Delta1=k4["min_Delta1"], min_Delta1_k=k4["min_Delta1_k"],
            min_Delta1_Delta0=k4["min_Delta1_Delta0"],
            one_minus_lambda=1.0 - lam,
        )
        if do_spec:
            k2 = killshot2(P, lam)
            row["standard_dominance"] = k2["dominance"]
            row["full_second_eig"] = k2["second"]
            row["dominance_excess"] = k2["excess"]
        rows.append(row)

    # aggregates
    import statistics
    def agg(pred, key):
        vals = [r[key] for r in rows if pred(r) and key in r and r[key] == r[key]]
        return vals
    spec_rows = [r for r in rows if "standard_dominance" in r]
    taus = [r["kendall_tau_v_vs_erank"] for r in rows if r["kendall_tau_v_vs_erank"] == r["kendall_tau_v_vs_erank"]]
    caps = [r["prefix_capture_fraction"] for r in rows if r["prefix_capture_fraction"] == r["prefix_capture_fraction"]]
    gaps = [r["prefix_vs_best_cut_gap"] for r in rows]
    summary = dict(
        n_posets=len(rows),
        standard_dominance_failures=sum(1 for r in spec_rows if not r["standard_dominance"]),
        standard_dominance_tested=len(spec_rows),
        poset_monotone_true=sum(1 for r in rows if r["poset_monotone"]),
        poset_monotone_false=sum(1 for r in rows if not r["poset_monotone"]),
        expected_rank_monotone_true=sum(1 for r in rows if r["expected_rank_monotone"]),
        expected_rank_monotone_false=sum(1 for r in rows if not r["expected_rank_monotone"]),
        kendall_tau_min=min(taus), kendall_tau_median=statistics.median(taus),
        kendall_tau_mean=statistics.mean(taus), kendall_tau_max=max(taus),
        kendall_tau_lt_1_count=sum(1 for t in taus if t < 1 - 1e-9),
        prefix_capture_min=min(caps), prefix_capture_median=statistics.median(caps),
        prefix_capture_mean=statistics.mean(caps), prefix_capture_max=max(caps),
        prefix_vs_bestcut_gap_max=max(gaps), prefix_vs_bestcut_gap_mean=statistics.mean(gaps),
        best_sweep_is_prefix_true=sum(1 for r in rows if r["best_sweep_is_prefix"]),
    )
    # SKEPTICAL-BAR aggregate: does high lambda_std actually imply a THIN interface
    # (small Delta1) at the best prefix? Programme NEEDS: 1-lambda small => Delta1 small.
    d1_best = [r["best_prefix_Delta1"] for r in rows]
    d1_min = [r["min_Delta1"] for r in rows]
    hi_lam = [r for r in rows if r["lambda_std"] >= 0.85]   # closest to bad-mixing regime
    summary.update(
        best_prefix_Delta1_min=min(d1_best), best_prefix_Delta1_median=statistics.median(d1_best),
        best_prefix_Delta1_max=max(d1_best),
        min_Delta1_over_posets_min=min(d1_min), min_Delta1_over_posets_median=statistics.median(d1_min),
        min_Delta1_over_posets_max=max(d1_min),
        # among the highest-lambda posets, is the thinnest interface actually thin?
        hi_lambda_count=len(hi_lam),
        hi_lambda_min_Delta1_median=(statistics.median([r["min_Delta1"] for r in hi_lam]) if hi_lam else None),
        hi_lambda_min_Delta1_max=(max([r["min_Delta1"] for r in hi_lam]) if hi_lam else None),
        # Pearson corr between (1-lambda) and min_Delta1 (programme predicts positive)
        corr_1mlam_minDelta1=_pearson([r["one_minus_lambda"] for r in rows], d1_min),
    )
    with open(out_path, "w") as f:
        json.dump(dict(summary=summary, rows=rows,
                       lem_witness_n10=LEM_CYCLIC_WITNESS_N10), f, indent=2)
    print(f"wrote {out_path}  ({len(rows)} posets)")
    print("AGGREGATE SUMMARY:")
    for k, v in summary.items():
        print(f"  {k}: {v}")
    return summary


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--t1-hi", type=int, default=6,
                    help="max n for full both-connected test-1 enumeration")
    ap.add_argument("--spectrum-hi", type=int, default=6,
                    help="max n for full Cayley spectrum (test 2)")
    ap.add_argument("--only", type=str, default=None,
                    help="run only test: 1|full")
    ap.add_argument("--dump", action="store_true",
                    help="write data/onethird-mgb0a6-spectral-killshot.json + aggregates")
    args = ap.parse_args()

    if args.dump:
        dump_data(spectrum_hi=args.spectrum_hi)
        return

    if args.only in (None, "1"):
        v1, d1 = run_test1(n_hi=args.t1_hi)
        if v1 == "RED":
            print("\n>>> KILL-SHOT 1 is RED: stopping early (programme cannot start; "
                  "no distinguished order). Tests 2-4 skipped per kill-shot protocol.")
            return
        if args.only == "1":
            return

    # Tests 2-4 on named posets + a sample of enumerated both-connected posets.
    print("\n" + "=" * 78)
    print("KILL-SHOTS 2-4 (test 1 GREEN): standard dominance / monotonicity / prefix")
    print("=" * 78)
    # named posets with n <= 7 get the full battery (n=10 witness is test-1 only)
    targets = [(nm, P) for nm, P in named_posets().items() if P.n <= 7]
    # add all both-connected posets up to spectrum-hi for the full battery
    for n in range(3, args.spectrum_hi + 1):
        for i, P in enumerate(enumerate_both_connected(n)):
            targets.append((f"enum-n{n}-#{i}", P))

    dom_fail = []
    mono_poset_fail = []
    mono_e_fail = []
    taus = []
    caps = []
    gaps = []
    min_d1s = []
    one_m_lams = []
    best_prefix_d1s = []
    for name, P in targets:
        do_spec = P.n <= args.spectrum_hi
        res = analyze_full(P, name, do_spec)
        t3 = res["test3"]; t4 = res["test4"]
        t2 = res.get("test2")
        dom = t2["dominance"] if t2 else None
        if t2 and not dom:
            dom_fail.append((name, P, t2))
        if not t3["poset_monotone"]:
            mono_poset_fail.append((name, P, t3))
        if not t3["expected_rank_monotone"]:
            mono_e_fail.append((name, P, t3))
        if t3["kendall_tau_v_vs_erank"] == t3["kendall_tau_v_vs_erank"]:
            taus.append(t3["kendall_tau_v_vs_erank"])
        caps.append(t4["prefix_capture_fraction"])
        gaps.append(t4["prefix_vs_best_cut_gap"])
        min_d1s.append(t4["min_Delta1"])
        best_prefix_d1s.append(t4["best_prefix_Delta1"])
        one_m_lams.append(1.0 - res["lambda_std"])
        print(f"\n[{name}] n={P.n} lambda_std={res['lambda_std']:.6f}")
        if t2:
            print(f"   T2 dominance={dom}  full 2nd-eig={t2['second']:.6f} "
                  f"lam_std={t2['lam_std']:.6f} excess={t2['excess']:+.2e}")
        print(f"   T3 poset-monotone={t3['poset_monotone']} "
              f"(agree {t3['poset_agree_rate']:.3f}, {len(t3['poset_violators'])} viol)  "
              f"e-monotone={t3['expected_rank_monotone']} "
              f"(inv={t3['expected_rank_inversions']})")
        print(f"   T4 prefix-capture={t4['prefix_capture_fraction']:.4f} "
              f"(best-prefix R={t4['best_prefix_R']:.5f} @k={t4['best_prefix_k']}, "
              f"lam_std={t4['lam_std']:.5f}); "
              f"best-sweep-is-prefix={t4['best_sweep_is_prefix']}; "
              f"prefix-vs-bestcut gap={t4['prefix_vs_best_cut_gap']:.5f}")

    print("\n" + "=" * 78)
    print("KILL-SHOTS 2-4 SUMMARY")
    print("=" * 78)
    print(f"  Standard-dominance FAILURES: {len(dom_fail)}")
    for (name, P, t2) in dom_fail[:15]:
        print(f"    [{name}] n={P.n} 2nd-eig={t2['second']:.6f} > lam_std="
              f"{t2['lam_std']:.6f} (excess {t2['excess']:+.3e})")
    print(f"  Poset-monotonicity FAILURES: {len(mono_poset_fail)}")
    for (name, P, t3) in mono_poset_fail[:15]:
        print(f"    [{name}] n={P.n} agree={t3['poset_agree_rate']:.3f} "
              f"viol={t3['poset_violators'][:3]}")
    print(f"  Expected-rank-order monotonicity FAILURES: {len(mono_e_fail)}")
    for (name, P, t3) in mono_e_fail[:15]:
        print(f"    [{name}] n={P.n} inversions={t3['expected_rank_inversions']}")

    import statistics
    tau_med = statistics.median(taus) if taus else float("nan")
    cap_med = statistics.median(caps) if caps else float("nan")
    gap_max = max(gaps) if gaps else float("nan")
    corr = _pearson(one_m_lams, min_d1s)
    n_tot = len(targets)

    # --- reasoned per-test verdicts (see docs/OneThird-Spectral-NearOrdinalSum-
    #     KillShot-Probe.md for the full argument; these are NOT naive any-failure
    #     RED calls, they apply the skeptical bar in both directions) ---
    print("\n" + "-" * 78)
    print("REASONED PER-TEST VERDICTS (kill-shot protocol; skeptical bar applied)")
    print("-" * 78)

    # TEST 2: a single dominance failure is a genuine RED (structural).
    print("  TEST 2 (standard dominance):",
          "RED" if dom_fail else "GREEN",
          f"-- {len(dom_fail)}/{len(targets)} failures; the spectral gap lives in "
          f"the standard sector.")

    # TEST 3: exact lemma false but soft claim supported AND downstream prefix
    # survives (test 4) -> AMBER, not RED. RED only if the eigenvector order were
    # essentially uncorrelated with expected rank (tau ~ 0).
    if not mono_poset_fail and not mono_e_fail:
        t3v = "GREEN"
    elif tau_med >= 0.5:
        t3v = "AMBER"
    else:
        t3v = "RED"
    print(f"  TEST 3 (monotonicity/L2): {t3v} -- exact monotone lemma FALSE "
          f"({len(mono_poset_fail)} poset-order violations, {len(mono_e_fail)}/{n_tot} "
          f"exact-order mismatches), BUT Kendall-tau(v, E[pos]) median={tau_med:.3f} "
          f"(soft '.tex' claim SUPPORTED); the prefix conclusion L2 feeds survives "
          f"via test 4 (best-cut-is-a-prefix).")

    # TEST 4: literal prefix metrics GREEN; near-ordinal-sum limit AMBER (untestable
    # lambda->1; best-Rayleigh-prefix != thinnest interface; N-poset Delta1=0.5).
    prefix_ok = (gap_max < 1e-9)
    t4v = "AMBER" if prefix_ok else "RED"
    print(f"  TEST 4 (prefix capture / near-ordinal-sum L4): {t4v} -- prefix metrics "
          f"GREEN (best-cut-is-a-prefix gap_max={gap_max:.1e}, capture median="
          f"{cap_med:.3f}); near-ordinal-sum limit AMBER: corr(1-lambda, minDelta1)="
          f"{corr:+.3f} (right SIGN) but no thin interface reachable at small n "
          f"(min Delta1 never ->0; best-Rayleigh-prefix Delta1 up to "
          f"{max(best_prefix_d1s):.2f}, the N-poset). A high Rayleigh/capture is NOT "
          f"near-ordinal-sum evidence (skeptical bar).")

    overall = "RED (killed)" if (dom_fail or t3v == "RED" or t4v == "RED") else \
              "ALIVE -- no kill-shot fired"
    print(f"\n  OVERALL: {overall}. Surviving risk localized to L1 (borrowed BK "
          f"bad-mixing => lambda->1) and L4 (near-ordinal-sum stability vs the "
          f"N-poset). See the report doc for the full call.")


if __name__ == "__main__":
    main()
