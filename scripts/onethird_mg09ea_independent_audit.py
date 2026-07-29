#!/usr/bin/env python3
"""
mg-09ea -- INDEPENDENT AUDIT INSTRUMENT for the mg-2c34 n=7 overlap test.

This file deliberately imports NOTHING from the corpus.  Every quantity is
rebuilt from its definition by a route chosen to share as little as possible
with `scripts/onethird_mg2c34_n7_overlap_test.py` and its dependency chain
(`onethird_mgb0a6_spectral_killshot_probe`, `onethird_mg4a86_*`,
`onethird_mg8b64_*`).  The point is NOT to check their arithmetic -- it is to
re-derive it.

Where the two routes differ, on purpose:

  target                mg-2c34                          here
  --------------------  -------------------------------  --------------------------
  poset identity        index into enumerate_both_        relation set hard-coded
                        connected(7) (their enumerator)   from the merge commit, then
                                                          re-verified by |L|/lam_std/delta
  poset representation  dict of frozensets `less`         bitmask up/down sets
  linear extensions     their Poset.linear_extensions     own iterative DFS; DIFFERENT
                        (fixes an index order)            index order, so any answer that
                                                          depends on the ordering breaks
  BK operator           W built entry-wise, diagonal      W = I - step * L_G, L_G the
                        by row-sum complement             graph Laplacian D - A of the
                                                          BK swap graph
  lambda_2              eigh(W), 2nd largest              smallest NONZERO eigenvalue of
                                                          L_G; lam2 = 1 - step*mu_2
  slow eigenvector      eigh(W) column                    shifted INVERSE iteration on
                                                          L_G with the constant deflated
                                                          (no eigh call in the path)
  P_U                   SVD of the n^2 indicator          least squares: P_U f =
                        matrix, then Q Q^T                M @ lstsq(M, f) (LAPACK gelsd,
                                                          not gesdd); different column
                                                          layout (a*n+x, not x*n+a)
  dim U                 SVD singular values > tol         eigenvalue count of the Gram
                                                          matrix M^T M
  p_xy, delta           before_prob_dp (DP over subsets)  exact integer count over the
                                                          enumerated linear extensions
  lambda_std            transport matrix, Helmert basis   transport matrix built from the
                                                          enumerated LEs; restriction to
                                                          1^perp by explicit deflation
                                                          S - (1/n) J on the symmetrized S
  population            their deduped list (946)          own enumeration of naturally
                                                          labelled posets + own canonical
                                                          form (invariant-restricted min)

Run:  /usr/bin/python3 scripts/onethird_mg09ea_independent_audit.py [--quick]
      (--quick skips the 956-poset population sweep)

Writes data/onethird-mg09ea-independent-audit.json.
Exits non-zero if any re-derivation disagrees with the mg-2c34 deliverable
beyond the stated tolerance.
"""

import os
import sys
import json
import math
import argparse
import itertools
from fractions import Fraction

import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

N = 7
TOL_C = 5e-7          # the deliverable prints c to 6 dp; this is the rounding tolerance
FAILURES = []


def fail(msg):
    FAILURES.append(msg)
    print("  ** DISAGREEMENT: " + msg)


# ===========================================================================
# 1.  Poset, from scratch, on bitmasks.
# ===========================================================================
class BitPoset:
    """Strict order on range(n) stored as up/down bitmasks."""

    def __init__(self, n, pairs):
        self.n = n
        up = [0] * n
        for (a, b) in pairs:
            up[a] |= 1 << b
        # transitive closure (Floyd-Warshall style on masks)
        changed = True
        while changed:
            changed = False
            for a in range(n):
                m = up[a]
                add = 0
                b = m
                while b:
                    lb = b & -b
                    j = lb.bit_length() - 1
                    add |= up[j]
                    b ^= lb
                if add & ~m:
                    up[a] = m | add
                    changed = True
        for a in range(n):
            if up[a] >> a & 1:
                raise ValueError("cyclic")
        self.up = up
        dn = [0] * n
        for a in range(n):
            m = up[a]
            while m:
                lb = m & -m
                j = lb.bit_length() - 1
                dn[j] |= 1 << a
                m ^= lb
        self.dn = dn
        self._les = None

    def comparable(self, x, y):
        return bool(self.up[x] >> y & 1 or self.up[y] >> x & 1)

    def incomparable_pairs(self):
        return [(x, y) for x in range(self.n) for y in range(x + 1, self.n)
                if not self.comparable(x, y)]

    def linear_extensions(self):
        """Own iterative DFS.  Deliberately a different index order from
        the corpus's recursive generator."""
        if self._les is not None:
            return self._les
        n = self.n
        full = (1 << n) - 1
        out = []
        stack = [(0, ())]
        while stack:
            mask, seq = stack.pop()
            if mask == full:
                out.append(seq)
                continue
            # push in reverse so the traversal order differs from a plain
            # ascending recursion
            for e in range(n - 1, -1, -1):
                if mask >> e & 1:
                    continue
                if self.dn[e] & ~mask:
                    continue
                stack.append((mask | 1 << e, seq + (e,)))
        self._les = out
        return out

    def comp_connected(self):
        return self._conn(lambda x, y: self.comparable(x, y))

    def incomp_connected(self):
        return self._conn(lambda x, y: not self.comparable(x, y))

    def _conn(self, rel):
        n = self.n
        seen = {0}
        stack = [0]
        while stack:
            v = stack.pop()
            for w in range(n):
                if w not in seen and w != v and rel(v, w):
                    seen.add(w)
                    stack.append(w)
        return len(seen) == n

    def rel_mask(self):
        m = 0
        for a in range(self.n):
            m |= self.up[a] << (a * self.n)
        return m


# ===========================================================================
# 2.  The operators, each from its definition.
# ===========================================================================
def bk_laplacian(P):
    """Graph Laplacian D - A of the BK adjacent-transposition graph on L(P).

    The repo convention (step8.tex, and both corpus builders) is: from sigma,
    each of the n-1 adjacent position slots fires at rate 1/(2(n-1)); a slot
    holding an INCOMPARABLE pair swaps, a comparable one is a self-loop.  So
    W = I - step * (D - A) with step = 1/(2(n-1)).  Building L_G and W this
    way, rather than filling W entry-wise and taking the diagonal as a row-sum
    complement, is a different assembly of the same operator.
    """
    les = P.linear_extensions()
    m = len(les)
    idx = {s: i for i, s in enumerate(les)}
    A = np.zeros((m, m))
    deg = np.zeros(m)
    n = P.n
    for s, i in idx.items():
        for k in range(n - 1):
            a, b = s[k], s[k + 1]
            if not P.comparable(a, b):
                t = s[:k] + (b, a) + s[k + 2:]
                A[i, idx[t]] += 1.0
                deg[i] += 1.0
    L = np.diag(deg) - A
    L = (L + L.T) / 2.0
    return L, 1.0 / (2 * (n - 1))


def one_particle_matrix(P):
    """M[r, a*n + x] = 1[sigma_r(a) = x].  Column layout a*n+x, the transpose
    of the corpus's x*n+a -- same span, different matrix."""
    les = P.linear_extensions()
    m, n = len(les), P.n
    M = np.zeros((m, n * n))
    for r, s in enumerate(les):
        for a, x in enumerate(s):
            M[r, a * n + x] = 1.0
    return M


def dim_U_via_gram(M, tol=1e-9):
    G = M.T @ M
    w = np.linalg.eigvalsh(G)
    return int(np.sum(w > tol * max(1.0, w.max())))


def proj_onto_U(M, f):
    """P_U f by least squares (LAPACK gelsd), not by an explicit projector."""
    coef, *_ = np.linalg.lstsq(M, f, rcond=None)
    return M @ coef


def slow_mode_inverse_iteration(L, step, tol=1e-12, iters=200):
    """mu_2 = smallest nonzero eigenvalue of L_G, and its eigenvector, by
    shifted inverse iteration with the constant mode deflated.  No call to
    eigh on the walk operator anywhere in this path.

    Returns (lam2, v, gap_to_next, dim_at_1e-9).
    """
    m = L.shape[0]
    ones = np.ones(m) / math.sqrt(m)
    # deflate the constant mode up to a large value so it cannot be selected
    big = 4.0 * (abs(L).sum(axis=1).max() + 1.0)
    Ld = L + big * np.outer(ones, ones)
    # A cheap upper bracket for mu_2: Rayleigh quotient of any 1-orthogonal
    # vector.  Then inverse-iterate with a shift just below 0.
    shift = -1e-6
    Msolve = Ld - shift * np.eye(m)
    lu = np.linalg.inv(Msolve)          # m is small (<= ~1000)
    rng = np.random.default_rng(2026_09_14)
    v = rng.standard_normal(m)
    v -= (v @ ones) * ones
    v /= np.linalg.norm(v)
    prev = None
    for _ in range(iters):
        v = lu @ v
        v -= (v @ ones) * ones
        nv = np.linalg.norm(v)
        if nv == 0:
            break
        v /= nv
        mu = float(v @ (L @ v))
        if prev is not None and abs(mu - prev) < tol * max(1.0, abs(mu)):
            prev = mu
            break
        prev = mu
    mu2 = float(v @ (L @ v))
    resid = float(np.linalg.norm(L @ v - mu2 * v))
    return 1.0 - step * mu2, v, mu2, resid


def spectrum_lam2(L, step):
    """Independent second opinion on lambda_2 only (eigvalsh of the LAPLACIAN,
    not of W): mu ascending, mu_1 = 0 for the constant."""
    w = np.sort(np.linalg.eigvalsh(L))
    mu2 = w[1]
    dimE = int(np.sum(np.abs(w - mu2) < 1e-9))
    dimE_near = int(np.sum(np.abs(w - mu2) < 1e-6))
    return 1.0 - step * mu2, dimE, dimE_near, w


def overlap_c(P, adversarial=True):
    """c = ||P_U f||^2 / ||f||^2 over the lambda_2 eigenspace.

    Computed two ways:
      c_inv  -- from the inverse-iteration eigenvector, projected by lstsq
      c_eig  -- from the Laplacian eigenbasis, min and max over the eigenspace
    """
    L, step = bk_laplacian(P)
    m = L.shape[0]
    M = one_particle_matrix(P)
    dimU = dim_U_via_gram(M)

    lam2_inv, v, mu2, resid = slow_mode_inverse_iteration(L, step)
    pv = proj_onto_U(M, v)
    c_inv = float(pv @ pv) / float(v @ v)

    lam2_e, dimE, dimE_near, w = spectrum_lam2(L, step)
    ev, V = np.linalg.eigh(L)
    order = np.argsort(ev)
    ev, V = ev[order], V[:, order]
    mu2e = ev[1]
    idx = [j for j in range(1, m) if abs(ev[j] - mu2e) < 1e-9]
    Vs = V[:, idx]
    PV = np.column_stack([proj_onto_U(M, Vs[:, j]) for j in range(Vs.shape[1])])
    Mat = Vs.T @ PV
    Mat = (Mat + Mat.T) / 2.0
    wq = np.linalg.eigvalsh(Mat)
    c_max, c_min = float(wq.max()), float(wq.min())

    return dict(num_LE=m, dim_U=dimU, lam2_inverse_iter=lam2_inv,
                lam2_eig=lam2_e, eig_residual=resid,
                c_inverse_iter=c_inv, c_max=c_max, c_min=c_min,
                dim_eigenspace=dimE, dim_eigenspace_near=dimE_near,
                null_dimU_over_m=dimU / m,
                null_orth_to_const=(dimU - 1) / (m - 1))


def transport_and_lambda_std(P):
    """T[x][a] = Pr[sigma(a) = x] from the enumerated LEs; lambda_std = largest
    eigenvalue of S = (T+T^T)/2 on 1^perp, obtained by explicit deflation
    (S - (1/n) J has the same spectrum on 1^perp and 0 on the constant)."""
    les = P.linear_extensions()
    n, m = P.n, len(les)
    T = np.zeros((n, n))
    for s in les:
        for a, x in enumerate(s):
            T[x, a] += 1.0
    T /= m
    S = (T + T.T) / 2.0
    J = np.ones((n, n)) / n
    w = np.linalg.eigvalsh(S - J)
    return float(np.max(w)), T


def exact_pair_stats(P):
    """Exact rational p_xy by integer counting over the enumerated LEs, plus
    delta, the Theorem-E frozen pair (argmin E/Var) and the max-bias pair."""
    les = P.linear_extensions()
    tot = len(les)
    n = P.n
    rows = []
    for (x, y) in P.incomparable_pairs():
        cnt = 0
        adj = 0
        for s in les:
            px = s.index(x)
            py = s.index(y)
            if px < py:
                cnt += 1
            if abs(px - py) == 1:
                adj += 1
        p = Fraction(cnt, tot)
        var = p * (1 - p)
        energy = Fraction(adj, 2 * (n - 1) * tot)
        ratio = energy / var if var != 0 else None
        rows.append(dict(x=x, y=y, p=p, var=var, adj=adj, energy=energy,
                         ratio=ratio))
    delta = max(min(r["p"], 1 - r["p"]) for r in rows)
    frozen = min((r for r in rows if r["ratio"] is not None),
                 key=lambda r: r["ratio"])
    maxbias = max(rows, key=lambda r: max(r["p"], 1 - r["p"]))
    return delta, frozen, maxbias, rows


def pair_indicator_overlap(P, x, y):
    """||P_U f||^2/||f||^2 for the CENTRED pair indicator f = 1[x <_sigma y],
    and the Lemma 3.1 threshold hypothesis check:
        exists k with  (x <_sigma y)  <=>  pos_sigma(x) <= k   for all sigma.
    """
    les = P.linear_extensions()
    m = len(les)
    M = one_particle_matrix(P)
    f = np.zeros(m)
    posx = np.zeros(m, dtype=int)
    for r, s in enumerate(les):
        px, py = s.index(x), s.index(y)
        posx[r] = px
        f[r] = 1.0 if px < py else 0.0
    lab = f.copy()
    f = f - f.mean()
    nrm = np.linalg.norm(f)
    if nrm == 0:
        return None, None
    f /= nrm
    pf = proj_onto_U(M, f)
    ov = float(pf @ pf)
    # threshold hypothesis: is {sigma: x<y} exactly {sigma: pos(x) <= k}?
    thresh_k = None
    for k in range(P.n):
        if np.array_equal(lab.astype(bool), posx <= k):
            thresh_k = k
            break
    return ov, thresh_k


# ===========================================================================
# 3.  Own enumeration + own canonical form.
# ===========================================================================
def enumerate_natural_posets(n):
    """All posets on [n] admitting the identity as a linear extension, as
    up-set masks, by DFS from the top element down.  (The corpus loops over
    2^C(n,2) bitmasks and filters; this constructs only valid ones.)"""
    out = []
    up = [0] * n

    def rec(i):
        if i < 0:
            out.append(tuple(up))
            return
        tail = [j for j in range(i + 1, n)]
        for r in range(len(tail) + 1):
            for S in itertools.combinations(tail, r):
                mask = 0
                for j in S:
                    mask |= 1 << j
                ok = True
                for j in S:
                    if up[j] & ~mask:
                        ok = False
                        break
                if ok:
                    up[i] = mask
                    rec(i - 1)
        up[i] = 0

    rec(n - 1)
    return out


def _elem_invariant(P, e):
    dn, up = P.dn[e], P.up[e]

    def prof(mask):
        out = []
        m = mask
        while m:
            lb = m & -m
            j = lb.bit_length() - 1
            out.append((bin(P.dn[j]).count("1"), bin(P.up[j]).count("1")))
            m ^= lb
        return tuple(sorted(out))
    return (bin(dn).count("1"), bin(up).count("1"), prof(dn), prof(up))


def canonical_mask(P):
    """Exact canonical form: minimum relation mask over all invariant-
    preserving relabelings.  Isomorphisms must preserve the invariant, so
    restricting to those loses nothing."""
    n = P.n
    inv = [_elem_invariant(P, e) for e in range(n)]
    groups = {}
    for e in range(n):
        groups.setdefault(inv[e], []).append(e)
    keys = sorted(groups.keys())
    slots = []
    base = 0
    for k in keys:
        g = groups[k]
        slots.append((g, list(range(base, base + len(g)))))
        base += len(g)
    best = None
    for choice in itertools.product(*[itertools.permutations(t) for _, t in slots]):
        pi = [0] * n
        for (g, _), tgt in zip(slots, choice):
            for e, t in zip(g, tgt):
                pi[e] = t
        m = 0
        for a in range(n):
            ua = P.up[a]
            while ua:
                lb = ua & -ua
                b = lb.bit_length() - 1
                m |= 1 << (pi[a] * n + pi[b])
                ua ^= lb
        if best is None or m < best:
            best = m
    return best


def both_connected_classes(n):
    reps = {}
    natural = 0
    for upmask in enumerate_natural_posets(n):
        pairs = []
        for a in range(n):
            m = upmask[a]
            while m:
                lb = m & -m
                b = lb.bit_length() - 1
                pairs.append((a, b))
                m ^= lb
        P = BitPoset(n, pairs)
        if not (P.comp_connected() and P.incomp_connected()):
            continue
        natural += 1
        cm = canonical_mask(P)
        if cm not in reps:
            reps[cm] = P
    return natural, reps


# ===========================================================================
# 4.  The five named posets, hard-coded from the merge commit.
# ===========================================================================
NAMED = {
    "enum-n7-#3":   [(0, 2), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4)],
    "enum-n7-#20":  [(0, 3), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (2, 3)],
    "enum-n7-#600": [(0, 1), (0, 3), (0, 5), (0, 6), (1, 6), (2, 6), (3, 5),
                     (4, 5)],
    "enum-n7-#945": [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4),
                     (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6),
                     (4, 5)],
    "enum-n7-#809": [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 5),
                     (1, 6), (2, 5), (2, 6), (3, 4), (3, 5), (4, 5)],
    "enum-n7-#86":  [(0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4),
                     (1, 5), (2, 3), (2, 4), (2, 5)],
    "enum-n7-#94":  [(0, 4), (0, 5), (0, 6), (1, 4), (2, 4), (3, 4)],
}

# The deliverable's published table (docs/OneThird-mg2c34-n7-Overlap-Test.md
# sec 4), transcribed here so the audit can DISAGREE with it.
PUBLISHED = {
    "enum-n7-#3":   dict(num_LE=360, dim_U=24, delta=0.5000, lam2=0.980923,
                         lam_std=0.785048, c=0.995552, null=0.0667),
    "enum-n7-#20":  dict(num_LE=198, dim_U=22, delta=0.5000, lam2=0.981202,
                         lam_std=0.767529, c=0.996857, null=0.1111),
    "enum-n7-#600": dict(num_LE=132, dim_U=20, delta=0.5000, lam2=0.979921,
                         lam_std=0.773911, c=0.996549, null=0.1515),
    "enum-n7-#945": dict(num_LE=21, dim_U=7, delta=0.3810, lam2=0.943488,
                         lam_std=0.943926, c=0.987947, null=0.3333),
    "enum-n7-#809": dict(num_LE=25, dim_U=9, delta=0.3600, lam2=0.969495,
                         lam_std=0.902015, c=0.995256, null=0.3600),
}


def audit_named():
    print("=" * 78)
    print("PART 1 -- the five named posets, re-derived from definitions")
    print("=" * 78)
    print(f"{'poset':16s} {'|L|':>5} {'dimU':>5} {'delta':>8} {'lam2^BK':>11} "
          f"{'lam_std':>10} {'c(invit)':>10} {'c(eigh)':>10} {'c_min':>10}")
    rows = {}
    for name, rel in NAMED.items():
        P = BitPoset(N, rel)
        st = overlap_c(P)
        ls, _ = transport_and_lambda_std(P)
        delta, frozen, maxbias, _ = exact_pair_stats(P)
        st["lambda_std"] = ls
        st["delta"] = float(delta)
        st["delta_exact"] = str(delta)
        st["frozen_pair"] = [frozen["x"], frozen["y"]]
        st["frozen_p"] = float(frozen["p"])
        st["maxbias_pair"] = [maxbias["x"], maxbias["y"]]
        st["maxbias_p"] = float(maxbias["p"])
        ov, k = pair_indicator_overlap(P, frozen["x"], frozen["y"])
        st["frozen_pair_overlap_with_U"] = ov
        st["lemma31_threshold_k"] = k
        rows[name] = st
        print(f"{name:16s} {st['num_LE']:>5d} {st['dim_U']:>5d} "
              f"{float(delta):>8.4f} {st['lam2_eig']:>11.6f} {ls:>10.6f} "
              f"{st['c_inverse_iter']:>10.6f} {st['c_max']:>10.6f} "
              f"{st['c_min']:>10.6f}")

        pub = PUBLISHED.get(name)
        if pub:
            if st["num_LE"] != pub["num_LE"]:
                fail(f"{name}: |L| {st['num_LE']} != published {pub['num_LE']}")
            if st["dim_U"] != pub["dim_U"]:
                fail(f"{name}: dim U {st['dim_U']} != published {pub['dim_U']}")
            if abs(st["c_max"] - pub["c"]) > TOL_C:
                fail(f"{name}: c {st['c_max']:.9f} != published {pub['c']}")
            if abs(st["c_inverse_iter"] - pub["c"]) > 1e-5:
                fail(f"{name}: c(inverse iteration) {st['c_inverse_iter']:.9f} "
                     f"!= published {pub['c']}")
            if abs(st["lam2_eig"] - pub["lam2"]) > 1e-6:
                fail(f"{name}: lam2 {st['lam2_eig']:.9f} != published "
                     f"{pub['lam2']}")
            if abs(st["lambda_std"] - pub["lam_std"]) > 1e-6:
                fail(f"{name}: lam_std {st['lambda_std']:.9f} != published "
                     f"{pub['lam_std']}")
            if abs(float(delta) - pub["delta"]) > 1e-4:
                fail(f"{name}: delta {float(delta):.6f} != published "
                     f"{pub['delta']}")
    print()
    print("  cross-check of the two independent numeric routes for c:")
    for name, st in rows.items():
        d = abs(st["c_inverse_iter"] - st["c_max"])
        print(f"    {name:16s} |c_invit - c_eigh| = {d:.2e}   "
              f"eig residual {st['eig_residual']:.1e}")
    print()
    print("  Lemma 3.1 / mechanism, at the Theorem-E frozen pair:")
    for name, st in rows.items():
        print(f"    {name:16s} frozen pair {tuple(st['frozen_pair'])} "
              f"p={st['frozen_p']:.4f}  ||P_U f||^2 = "
              f"{st['frozen_pair_overlap_with_U']:.6f}  threshold k = "
              f"{st['lemma31_threshold_k']}")
    return rows


# ===========================================================================
# 5.  Population sweep on an INDEPENDENTLY enumerated population.
# ===========================================================================
def audit_population():
    print()
    print("=" * 78)
    print("PART 2 -- own enumeration, own canonical form, own sweep")
    print("=" * 78)
    natural, reps = both_connected_classes(N)
    print(f"  naturally-labelled both-connected n=7 : {natural}")
    print(f"  isomorphism classes (own canonical)   : {len(reps)}")
    if natural != 52810:
        fail(f"naturally-labelled count {natural} != published 52810")
    if len(reps) != 956:
        fail(f"isomorphism class count {len(reps)} != published 956")

    recs = []
    for i, (cm, P) in enumerate(sorted(reps.items())):
        st = overlap_c(P)
        ls, _ = transport_and_lambda_std(P)
        delta, frozen, maxbias, _ = exact_pair_stats(P)
        ov, k = pair_indicator_overlap(P, frozen["x"], frozen["y"])
        recs.append(dict(canon=str(cm), num_LE=st["num_LE"],
                         dim_U=st["dim_U"], c_max=st["c_max"],
                         c_min=st["c_min"], lam2=st["lam2_eig"],
                         lambda_std=ls, delta=float(delta),
                         dim_eigenspace=st["dim_eigenspace"],
                         dim_eigenspace_near=st["dim_eigenspace_near"],
                         null=st["null_dimU_over_m"],
                         frozen_overlap=ov, lemma31_k=k))
        if (i + 1) % 200 == 0:
            print(f"    ... {i+1}/{len(reps)}")

    c = np.array([r["c_max"] for r in recs])
    cmin = np.array([r["c_min"] for r in recs])
    d = np.array([r["delta"] for r in recs])
    lam2 = np.array([r["lam2"] for r in recs])
    lstd = np.array([r["lambda_std"] for r in recs])
    R = (1 - lstd) / (1 - lam2)
    fo = np.array([r["frozen_overlap"] for r in recs if r["frozen_overlap"] is not None])
    simple = sum(1 for r in recs if r["dim_eigenspace"] == 1)

    summary = dict(
        n_classes=len(recs),
        naturally_labelled=natural,
        c_min=float(c.min()), c_max=float(c.max()),
        c_median=float(np.median(c)),
        c_min_over_cmin=float(cmin.min()),
        c_equals_cmin_count=int(np.sum(np.abs(c - cmin) < 1e-9)),
        lam2_simple_count=simple,
        lam2_simple_frac=simple / len(recs),
        delta_min=float(d.min()), delta_max=float(d.max()),
        delta_below_third=int(np.sum(d < 1 / 3 - 1e-12)),
        corr_c_delta=float(np.corrcoef(c, d)[0, 1]),
        R_min=float(R.min()), R_median=float(np.median(R)),
        R_max=float(R.max()),
        corr_c_R=float(np.corrcoef(c, R)[0, 1]),
        corr_c_logR=float(np.corrcoef(c, np.log(R))[0, 1]),
        frozen_overlap_min=float(fo.min()),
        frozen_overlap_median=float(np.median(fo)),
        frozen_overlap_exact_count=int(np.sum(fo > 1 - 1e-9)),
        lemma31_holds_at_exact=int(sum(
            1 for r in recs
            if r["frozen_overlap"] is not None and r["frozen_overlap"] > 1 - 1e-9
            and r["lemma31_k"] is not None)),
        max_LE=int(max(r["num_LE"] for r in recs)),
    )
    print()
    for k, v in summary.items():
        print(f"    {k:28s} {v}")
    return summary, recs


# ===========================================================================
# 6.  The committed mg-8b64 dataset: is delta < 1/3 really empty?
# ===========================================================================
def audit_dataset():
    print()
    print("=" * 78)
    print("PART 3 -- the committed mg-8b64 dataset (delta < 1/3 claim)")
    print("=" * 78)
    path = os.path.join(REPO, "data",
                        "data/onethird-mg8b64-L1b-bk-transport-transfer.json"
                        .split("/")[-1])
    with open(path) as fh:
        blob = json.load(fh)

    # `rows` is the row list; the `summary` block re-quotes a few of them, so
    # counting every nested "delta" key double-counts.  Only /rows/[] is a row.
    deltas = [float(r["delta"]) for r in blob["rows"]
              if isinstance(r.get("delta"), (int, float))]
    arr = np.array(deltas)
    below = int(np.sum(arr < 1 / 3 - 1e-12))
    print(f"    rows carrying a delta          : {len(arr)}")
    print(f"    min delta                      : {arr.min():.12f}")
    print(f"    |min delta - 1/3|              : {abs(arr.min()-1/3):.2e}")
    print(f"    rows with delta < 1/3          : {below}")
    if len(arr) != 1091:
        print(f"    NOTE: published row count is 1091, found {len(arr)}")
    if below != 0:
        fail(f"found {below} rows with delta < 1/3; deliverable claims 0")
    return dict(rows=len(arr), min_delta=float(arr.min()), below_third=below)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="skip the 956-poset population sweep")
    args = ap.parse_args()

    out = {}
    out["named"] = audit_named()
    out["dataset"] = audit_dataset()
    if not args.quick:
        summary, recs = audit_population()
        out["population"] = summary
        out["population_rows"] = recs

    # --quick must NOT overwrite the committed dataset with a sweep-less copy;
    # the audit document's sec 2.2 table would silently lose its source.  (The
    # same discipline mg-2c34's --no-sweep applies to its own artifact.)
    if args.quick:
        print()
        print("(--quick: committed dataset left untouched)")
    else:
        dst = os.path.join(REPO, "data",
                           "onethird-mg09ea-independent-audit.json")
        with open(dst, "w") as fh:
            json.dump(out, fh, indent=1, sort_keys=True, default=str)
        print()
        print(f"wrote {dst}")
    print()
    if FAILURES:
        print("=" * 78)
        print(f"AUDIT DISAGREEMENTS: {len(FAILURES)}")
        for f in FAILURES:
            print("  - " + f)
        print("=" * 78)
        return 1
    print("=" * 78)
    print("ALL RE-DERIVATIONS AGREE WITH THE DELIVERABLE.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
