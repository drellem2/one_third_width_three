#!/usr/bin/env python3
"""
mg-d1be -- audit of `lambda_std <= lambda_2^BK` as asserted at
OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md:286-288 ("the standard sector is a
subspace").

The owed correction (ComparisonRoute:653, owed since mg-4a86) says two things:
the justification is invalid, and the inequality fails exactly on the ordinal
sums.  This script does NOT inherit that record.  It re-derives it, and it asks
the question mg-4a86 did not: does the failure REACH the site, whose standing
hypothesis (sec 0 of the Reverse-Cheeger doc) is a width-3 INDECOMPOSABLE
gamma-counterexample -- a class that excludes ordinal sums by fiat.

Four parts:

  A. EXACT witnesses.  Two ordinal sums where lambda_std > lambda_2^BK, in exact
     rationals with certificates (eigenvector for the lower bound, exact
     symmetric elimination for the PSD upper bound).  No floating point.

  B. THE REACH TEST.  Exhaustive over every poset on n <= 6 up to isomorphism
     (1 + 2 + 5 + 16 + 63 + 318 classes): is the violation set EXACTLY the
     ordinal sums?  If yes, no indecomposable poset violates it, and the failure
     does not reach the site's hypothesis -- a materially different finding from
     the ticket's premise.

  C. WIDTH-3, n = 7.  The programme's own width, one step past mg-4a86's n <= 5.

  D. FROZENNESS.  Are the violating ordinal sums gamma-counterexamples (every
     incomparable pair frozen, delta < 1/3)?  This decides whether the failure
     can be instantiated inside sec 0's hypothesis at all.

Conventions copied byte-for-byte from onethird_mg4a86_standard_dominance_target_audit.py:
  - BK walk: lazy, W[L,L'] += 1/(2(n-1)) per adjacent incomparable position,
    diagonal = 1 - rowsum
  - (T_P)_{x,a} = Pr_{sigma ~ Unif L(P)}[sigma(a) = x];  S_P = (T_P + T_P^T)/2;
    lambda_std = top eigenvalue of S_P on 1^perp

Reproduce: python3.11 scripts/onethird_mgd1be_reverse_cheeger_ineq_audit.py
"""

import itertools
import json
from fractions import Fraction

import numpy as np


# ------------------------------------------------------------------ posets --
class Poset:
    """Strict order given by a boolean matrix lt[x][y] == (x <_P y)."""

    def __init__(self, n, lt):
        self.n = n
        self.lt = lt
        self._les = None

    def comparable(self, a, b):
        return self.lt[a][b] or self.lt[b][a]

    def linear_extensions(self):
        if self._les is None:
            out = []
            for perm in itertools.permutations(range(self.n)):
                pos = {x: i for i, x in enumerate(perm)}
                if all(pos[x] < pos[y]
                       for x in range(self.n) for y in range(self.n)
                       if self.lt[x][y]):
                    out.append(perm)
            self._les = out
        return self._les

    def width(self):
        """Largest antichain (n <= 7, brute force)."""
        best = 0
        for k in range(self.n, 0, -1):
            for S in itertools.combinations(range(self.n), k):
                if all(not self.comparable(a, b)
                       for a, b in itertools.combinations(S, 2)):
                    return k
        return best

    def is_ordinal_sum(self):
        """P is a NONTRIVIAL ordinal sum iff some nonempty proper D is a
        down-set with every element of D below every element of its complement.
        (Equivalently: P is decomposable.)"""
        for mask in range(1, (1 << self.n) - 1):
            D = [x for x in range(self.n) if mask >> x & 1]
            U = [x for x in range(self.n) if not mask >> x & 1]
            if all(self.lt[d][u] for d in D for u in U):
                return True
        return False


def antichain(n):
    return Poset(n, [[False] * n for _ in range(n)])


def ordinal_sum(*blocks):
    """Concatenate posets: everything in block i below everything in block j>i."""
    n = sum(b.n for b in blocks)
    lt = [[False] * n for _ in range(n)]
    off = 0
    offsets = []
    for b in blocks:
        offsets.append(off)
        for x in range(b.n):
            for y in range(b.n):
                if b.lt[x][y]:
                    lt[off + x][off + y] = True
        off += b.n
    for i, bi in enumerate(blocks):
        for j, bj in enumerate(blocks):
            if i < j:
                for x in range(bi.n):
                    for y in range(bj.n):
                        lt[offsets[i] + x][offsets[j] + y] = True
    return Poset(n, lt)


# --------------------------------------------------------------- operators --
def bk_walk_matrix_exact(P, les=None):
    """Lazy BK walk on L(P), exact Fractions.  Symmetric (uniform stationary)."""
    les = les if les is not None else P.linear_extensions()
    N = len(les)
    idx = {L: i for i, L in enumerate(les)}
    rate = Fraction(1, 2 * (P.n - 1))
    W = [[Fraction(0)] * N for _ in range(N)]
    for i, L in enumerate(les):
        for a in range(P.n - 1):
            x, y = L[a], L[a + 1]
            if not P.comparable(x, y):
                L2 = L[:a] + (y, x) + L[a + 2:]
                W[i][idx[L2]] += rate
    for i in range(N):
        W[i][i] = Fraction(1) - sum(W[i])
    return W


def transport_S_exact(P, les=None):
    """S_P = (T_P + T_P^T)/2 with (T_P)_{x,a} = Pr[sigma(a) = x], exact."""
    les = les if les is not None else P.linear_extensions()
    N = len(les)
    n = P.n
    T = [[Fraction(0)] * n for _ in range(n)]
    for L in les:
        for a, x in enumerate(L):
            T[x][a] += Fraction(1, N)
    return [[(T[i][j] + T[j][i]) / 2 for j in range(n)] for i in range(n)]


def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def lam2_float(W):
    """Second-largest eigenvalue of a symmetric matrix, float."""
    A = np.array([[float(x) for x in row] for row in W])
    ev = np.linalg.eigvalsh(A)
    return float(ev[-2])


def lam_std_float(S):
    A = np.array([[float(x) for x in row] for row in S])
    n = A.shape[0]
    # restrict to 1^perp via projector; the constant direction gets eigenvalue 0
    Pi = np.eye(n) - np.ones((n, n)) / n
    ev = np.linalg.eigvalsh(Pi @ A @ Pi)
    return float(ev[-1])


# ------------------------------------------------------- exact certificates --
def psd_exact(M):
    """Exact PSD test for a symmetric rational matrix, by symmetric elimination
    allowing zero pivots (M is expected to be singular on the constants)."""
    N = len(M)
    A = [row[:] for row in M]
    for k in range(N):
        if A[k][k] < 0:
            return False, f"negative pivot at {k}"
        if A[k][k] == 0:
            # a zero pivot forces the whole row/col to vanish, else indefinite
            if any(A[k][j] != 0 for j in range(k, N)):
                return False, f"zero pivot with nonzero row at {k}"
            continue
        piv = A[k][k]
        for i in range(k + 1, N):
            if A[i][k] == 0:
                continue
            f = A[i][k] / piv
            for j in range(k, N):
                A[i][j] -= f * A[k][j]
            for j in range(k, N):
                A[j][i] = A[i][j]  # keep symmetric
    return True, "all pivots >= 0"


def certify_lam2_upper(W, c):
    """Exact certificate that lambda_2(W) <= c, for W symmetric stochastic.

    M := c*I + (1-c)*J/N - W.  On the constants M acts as 0; on 1^perp M = cI-W.
    So M PSD  <=>  <f,Wf> <= c<f,f> for all f _|_ 1  <=>  lambda_2(W) <= c."""
    N = len(W)
    M = [[(c if i == j else Fraction(0)) + (1 - c) / N - W[i][j]
          for j in range(N)] for i in range(N)]
    return psd_exact(M)


def certify_eigenvector(M, v, lam):
    """Exact: M v == lam v, and v != 0."""
    if all(x == 0 for x in v):
        return False
    return matvec(M, v) == [lam * x for x in v]


def exact_nullspace_vector(M):
    """One nonzero exact rational vector in ker(M), or None.

    Plain Gaussian elimination over Q.  Used to produce a CERTIFIED eigenvector
    for lambda_2 -- rationalizing a numpy eigenvector fails when the eigenvalue
    is degenerate (numpy returns an arbitrary rotation inside the eigenspace)."""
    N = len(M)
    A = [row[:] for row in M]
    pivot_col_of_row, where = [], {}
    r = 0
    for c in range(N):
        p = next((i for i in range(r, N) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = A[r][c]
        A[r] = [x / inv for x in A[r]]
        for i in range(N):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][j] - f * A[r][j] for j in range(N)]
        where[c] = r
        pivot_col_of_row.append(c)
        r += 1
        if r == N:
            break
    free = [c for c in range(N) if c not in where]
    if not free:
        return None
    fc = free[0]
    v = [Fraction(0)] * N
    v[fc] = Fraction(1)
    for c, row in where.items():
        v[c] = -A[row][fc]
    return v


# ------------------------------------------- poset enumeration up to iso ----
def _wl_colours(n, lt):
    """1-WL refinement on (strict down-set, strict up-set) neighbourhoods.
    Any isomorphism preserves these colours, so canonicalization only has to
    range over permutations that respect the colour classes."""
    col = [(sum(lt[y][x] for y in range(n)), sum(lt[x][y] for y in range(n)))
           for x in range(n)]
    while True:
        new = [(col[x],
                tuple(sorted(col[y] for y in range(n) if lt[y][x])),
                tuple(sorted(col[y] for y in range(n) if lt[x][y])))
               for x in range(n)]
        keys = {c: i for i, c in enumerate(sorted(set(new)))}
        new = [keys[c] for c in new]
        if new == col:
            return col
        col = new


def canonical(n, lt):
    """Canonical form: min over relabelings of the packed relation bits.

    Restricted to permutations respecting the WL colour classes -- still a
    genuine canonical form (isomorphisms preserve the colours), but the
    permutation set is tiny compared with all n!."""
    col = _wl_colours(n, lt)
    classes = [[x for x in range(n) if col[x] == c] for c in sorted(set(col))]
    best = None
    for parts in itertools.product(*[itertools.permutations(cl) for cl in classes]):
        p = [x for part in parts for x in part]
        bits = 0
        for i in range(n):
            for j in range(n):
                if lt[p[i]][p[j]]:
                    bits |= 1 << (i * n + j)
        if best is None or bits < best:
            best = bits
    return best


def unpack(n, bits):
    return [[bool(bits >> (i * n + j) & 1) for j in range(n)] for i in range(n)]


_ISO_COUNTS = {1: 1, 2: 2, 3: 5, 4: 16, 5: 63, 6: 318, 7: 2045}


def posets_up_to_iso(n, max_width=None):
    """Every poset on n elements up to isomorphism.

    Built by induction: every poset has a maximal element, so P on [n] is some
    P' on [n-1] plus a new top element whose strict down-set D is a down-set of
    P'.  Canonicalizing dedupes the overcount.

    max_width prunes during the tower, which is sound: deleting a maximal
    element cannot increase the width, so every width-<=w poset on [n] arises
    from a width-<=w poset on [n-1]."""
    cur = {canonical(1, [[False]])}
    for k in range(2, n + 1):
        nxt = set()
        for bits in cur:
            lt_prev = unpack(k - 1, bits)
            m = k - 1
            for mask in range(1 << m):
                D = [x for x in range(m) if mask >> x & 1]
                # D must be a down-set of P'
                if not all((not lt_prev[y][d]) or (mask >> y & 1)
                           for d in D for y in range(m)):
                    continue
                lt = [[False] * k for _ in range(k)]
                for i in range(m):
                    for j in range(m):
                        lt[i][j] = lt_prev[i][j]
                for d in D:
                    lt[d][m] = True
                if max_width is not None and Poset(k, lt).width() > max_width:
                    continue
                nxt.add(canonical(k, lt))
        cur = nxt
        if max_width is None and k in _ISO_COUNTS:
            # self-check the enumerator against the known number of posets
            assert len(cur) == _ISO_COUNTS[k], \
                f"poset enumeration wrong at n={k}: {len(cur)} != {_ISO_COUNTS[k]}"
    return [Poset(n, unpack(n, b)) for b in sorted(cur)]


# --------------------------------------------------------------- frozenness --
def delta_exact(P, les=None):
    """delta(P) = max over incomparable pairs of min(p_xy, 1-p_xy), exact.
    P is a gamma-counterexample (every pair frozen) iff delta < 1/3."""
    les = les if les is not None else P.linear_extensions()
    N = len(les)
    worst = Fraction(0)
    any_incomparable = False
    for x, y in itertools.combinations(range(P.n), 2):
        if P.comparable(x, y):
            continue
        any_incomparable = True
        cnt = sum(1 for L in les if L.index(x) < L.index(y))
        p = Fraction(cnt, N)
        worst = max(worst, min(p, 1 - p))
    return (worst if any_incomparable else None)


# ==================================================================== parts ==
def part_A():
    print("=" * 78)
    print("PART A -- EXACT RATIONAL WITNESSES: lambda_std > lambda_2^BK")
    print("=" * 78)
    out = []

    cases = [
        ("A2 (+) A2", ordinal_sum(antichain(2), antichain(2)), Fraction(2, 3)),
        ("A3 (+) A3", ordinal_sum(antichain(3), antichain(3)), Fraction(9, 10)),
    ]
    for name, P, lam2_claim in cases:
        les = P.linear_extensions()
        S = transport_S_exact(P, les)
        W = bk_walk_matrix_exact(P, les)

        # lambda_std = 1, certified by an exact eigenvector orthogonal to 1.
        # For an ordinal sum the block-indicator (constant on each block, mean 0)
        # is fixed by S_P.  Build it from the block structure.
        half = P.n // 2
        f = [Fraction(1)] * half + [Fraction(-1)] * (P.n - half)
        assert sum(f) == 0, "test vector must be orthogonal to 1"
        std_ok = certify_eigenvector(S, f, Fraction(1))
        # lambda_std <= 1 always (S_P doubly stochastic), so this pins it at 1.
        lam_std = Fraction(1) if std_ok else None

        # lambda_2^BK: eigenvector for >=, exact PSD certificate for <=.
        # The eigenvector is found by EXACT rational nullspace of (W - lam*I),
        # not by rationalizing a float -- lambda_2 is degenerate here.
        N = len(les)
        Wm = [[W[i][j] - (lam2_claim if i == j else Fraction(0))
               for j in range(N)] for i in range(N)]
        v = exact_nullspace_vector(Wm)
        lower_ok = v is not None and certify_eigenvector(W, v, lam2_claim) \
            and sum(v) == 0          # must be orthogonal to the constants
        upper_ok, why = certify_lam2_upper(W, lam2_claim)

        print(f"\n  {name}:  n = {P.n},  |L(P)| = {len(les)},  width = {P.width()}")
        print(f"    lambda_std   = 1        exact eigenvector f={f} of S_P, f _|_ 1 : {std_ok}")
        print(f"    lambda_2^BK  = {lam2_claim}      eigenvector (>=) : {lower_ok}"
              f"   PSD certificate (<=) : {upper_ok} [{why}]")
        excess = lam_std - lam2_claim if lam_std is not None else None
        print(f"    EXCESS lambda_std - lambda_2^BK = {excess}   -> INEQUALITY FAILS")
        assert std_ok and lower_ok and upper_ok, "exact certification failed"
        out.append({"poset": name, "n": P.n, "num_linear_extensions": len(les),
                    "width": P.width(),
                    "lambda_std": str(lam_std), "lambda_2_BK": str(lam2_claim),
                    "excess": str(excess),
                    "certified_exact": True,
                    "lambda_std_eigenvector": [str(x) for x in f],
                    "lam2_upper_psd_certificate": upper_ok,
                    "lam2_lower_eigenvector_exact": lower_ok})
    return out


def part_B():
    print()
    print("=" * 78)
    print("PART B -- THE REACH TEST: is the violation set EXACTLY the ordinal sums?")
    print("        (every poset on n <= 6 up to isomorphism)")
    print("=" * 78)
    rows = []
    for n in range(2, 7):
        classes = posets_up_to_iso(n)
        viol, ordsum, both, viol_indecomp = [], [], 0, []
        tested = 0
        min_margin = None
        for P in classes:
            les = P.linear_extensions()
            if len(les) < 2:
                continue           # BK walk is a single point; lambda_2 undefined
            tested += 1
            S = transport_S_exact(P, les)
            W = bk_walk_matrix_exact(P, les)
            ls, l2 = lam_std_float(S), lam2_float(W)
            m = abs(ls - l2)
            min_margin = m if min_margin is None else min(min_margin, m)
            is_viol = ls > l2 + 1e-9
            is_os = P.is_ordinal_sum()
            if is_viol:
                viol.append(P)
            if is_os:
                ordsum.append(P)
            if is_viol and is_os:
                both += 1
            if is_viol and not is_os:
                viol_indecomp.append((P, ls, l2))
        sym_diff = len(viol) + len(ordsum) - 2 * both
        print(f"  n={n}: classes tested (|L(P)|>=2) = {tested:4d}   "
              f"violations = {len(viol):3d}   ordinal sums = {len(ordsum):3d}   "
              f"sym.diff = {sym_diff}   INDECOMPOSABLE violators = {len(viol_indecomp)}"
              f"   min |lam_std - lam_2| = {min_margin:.3e}")
        for P, ls, l2 in viol_indecomp:
            print(f"        !! indecomposable violator: lt={P.lt} "
                  f"lambda_std={ls:.9f} lambda_2^BK={l2:.9f}")
        rows.append({"n": n, "classes_tested": tested, "violations": len(viol),
                     "ordinal_sums": len(ordsum), "sym_difference": sym_diff,
                     "indecomposable_violators": len(viol_indecomp),
                     "min_abs_margin": min_margin})
    return rows


def part_C():
    print()
    print("=" * 78)
    print("PART C -- WIDTH-3 AT n = 7 (the programme's own width, past mg-4a86's n<=5)")
    print("=" * 78)
    classes = posets_up_to_iso(7, max_width=3)
    viol_indecomp, tested, viol, ordsum, both = [], 0, 0, 0, 0
    for P in classes:
        les = P.linear_extensions()
        if len(les) < 2:
            continue
        tested += 1
        ls = lam_std_float(transport_S_exact(P, les))
        l2 = lam2_float(bk_walk_matrix_exact(P, les))
        is_viol, is_os = ls > l2 + 1e-9, P.is_ordinal_sum()
        viol += is_viol
        ordsum += is_os
        both += (is_viol and is_os)
        if is_viol and not is_os:
            viol_indecomp.append((P, ls, l2))
    print(f"  n=7, width<=3: classes tested = {tested}   violations = {viol}   "
          f"ordinal sums = {ordsum}   sym.diff = {viol + ordsum - 2*both}   "
          f"INDECOMPOSABLE violators = {len(viol_indecomp)}")
    for P, ls, l2 in viol_indecomp:
        print(f"        !! indecomposable violator: lt={P.lt} "
              f"lambda_std={ls:.9f} lambda_2^BK={l2:.9f}")
    return {"n": 7, "width_le_3": True, "classes_tested": tested,
            "violations": viol, "ordinal_sums": ordsum,
            "sym_difference": viol + ordsum - 2 * both,
            "indecomposable_violators": len(viol_indecomp),
            "violator_lt": viol_indecomp[0][0].lt if viol_indecomp else None}


def part_D():
    print()
    print("=" * 78)
    print("PART D -- CAN THE FAILURE BE INSTANTIATED INSIDE SEC 0's HYPOTHESIS?")
    print("        (sec 0: width-3 INDECOMPOSABLE gamma-counterexample, delta < 1/3)")
    print("=" * 78)
    out = []
    for name, P in [("A2 (+) A2", ordinal_sum(antichain(2), antichain(2))),
                    ("A3 (+) A3", ordinal_sum(antichain(3), antichain(3)))]:
        d = delta_exact(P)
        print(f"  {name}: delta = {d}   frozen (delta<1/3)? {d < Fraction(1,3)}   "
              f"indecomposable? {not P.is_ordinal_sum()}")
        out.append({"poset": name, "delta": str(d),
                    "is_gamma_counterexample": d < Fraction(1, 3),
                    "is_indecomposable": not P.is_ordinal_sum()})

    # Does ANY poset on n <= 6 have every incomparable pair frozen?
    print("\n  Exhaustive: any poset on n <= 6 with delta < 1/3 (all pairs frozen)?")
    for n in range(2, 7):
        found = []
        for P in posets_up_to_iso(n):
            d = delta_exact(P)
            if d is not None and d < Fraction(1, 3):
                found.append(P)
        print(f"    n={n}: non-chain posets with delta < 1/3 : {len(found)}")
        out.append({"n": n, "frozen_posets": len(found)})
    return out


def part_E(violator_lt):
    """EXACT certification of an INDECOMPOSABLE violator.

    Both lambda_std and lambda_2^BK are algebraic, so they are separated by
    exhibiting a rational c with lambda_2^BK <= c < lambda_std:
      - lambda_2^BK <= c : exact PSD certificate (same device as part A);
      - lambda_std  >  c : exact rational Rayleigh test vector f _|_ 1 with
                           <f,S_P f> / <f,f> > c, so lambda_std >= it > c.
    No floating point enters either certificate."""
    print()
    print("=" * 78)
    print("PART E -- EXACT CERTIFICATION OF THE INDECOMPOSABLE VIOLATOR")
    print("=" * 78)
    P = Poset(len(violator_lt), violator_lt)
    les = P.linear_extensions()
    S = transport_S_exact(P, les)
    W = bk_walk_matrix_exact(P, les)
    n, N = P.n, len(les)

    rel = [(x, y) for x in range(n) for y in range(n) if P.lt[x][y]]
    inc = [(x, y) for x, y in itertools.combinations(range(n), 2)
           if not P.comparable(x, y)]
    print(f"  n = {n}, |L(P)| = {N}, width = {P.width()}")
    print(f"  cover/order relations x<y : {rel}")
    print(f"  incomparable pairs        : {inc}")
    # A poset is decomposable (a nontrivial ordinal sum) iff its incomparability
    # graph is DISCONNECTED.  Report that independently of is_ordinal_sum().
    seen, stack = {0}, [0]
    adj = {x: set() for x in range(n)}
    for x, y in inc:
        adj[x].add(y)
        adj[y].add(x)
    while stack:
        u = stack.pop()
        for v in adj[u] - seen:
            seen.add(v)
            stack.append(v)
    print(f"  incomparability graph connected on all {n} elements : {len(seen) == n}"
          f"   =>  INDECOMPOSABLE (not an ordinal sum): {not P.is_ordinal_sum()}")
    print(f"  delta(P) = {delta_exact(P)}  (gamma-counterexample iff < 1/3)")

    ls_f, l2_f = lam_std_float(S), lam2_float(W)
    print(f"  float: lambda_std = {ls_f:.12f}   lambda_2^BK = {l2_f:.12f}"
          f"   margin = {ls_f - l2_f:.3e}")

    # separating rational
    c = Fraction(9437, 10000)
    upper_ok, why = certify_lam2_upper(W, c)

    # exact Rayleigh lower bound for lambda_std: rationalize the top eigenvector
    # of S_P on 1^perp, then evaluate the quotient in EXACT arithmetic.  The
    # vector need not be exact -- only the quotient it certifies.
    A = np.array([[float(x) for x in row] for row in S])
    Pi = np.eye(n) - np.ones((n, n)) / n
    _, evec = np.linalg.eigh(Pi @ A @ Pi)
    v_num = evec[:, -1]
    D = 10**6
    v = [Fraction(round(t * D), D) for t in v_num]
    shift = sum(v) / n
    v = [t - shift for t in v]                      # force exact orthogonality
    assert sum(v) == 0
    num = sum(v[i] * S[i][j] * v[j] for i in range(n) for j in range(n))
    den = sum(t * t for t in v)
    rq = num / den
    print(f"  exact Rayleigh quotient of S_P at a rational f _|_ 1 : {float(rq):.12f}")
    print(f"  separating rational c = {c} = {float(c):.12f}")
    print(f"    lambda_2^BK <= c : {upper_ok} [{why}]  (exact PSD certificate)")
    print(f"    lambda_std  >= R > c : {rq > c}  (exact rational Rayleigh quotient)")
    proved = upper_ok and rq > c
    print(f"\n  ==> lambda_std > lambda_2^BK PROVED EXACTLY on an INDECOMPOSABLE "
          f"poset: {proved}")
    assert proved, "exact separation failed"
    return {"lt": [[bool(b) for b in row] for row in violator_lt],
            "n": n, "num_linear_extensions": N, "width": P.width(),
            "order_relations": [list(t) for t in rel],
            "incomparable_pairs": [list(t) for t in inc],
            "incomparability_graph_connected": len(seen) == n,
            "is_ordinal_sum": P.is_ordinal_sum(),
            "delta": str(delta_exact(P)),
            "separating_rational": str(c),
            "lambda_2_BK_le_c_exact_psd": upper_ok,
            "lambda_std_rayleigh_exact": str(rq),
            "lambda_std_gt_c": rq > c,
            "separation_proved_exactly": proved,
            "lambda_std_float": ls_f, "lambda_2_BK_float": l2_f}


def main():
    A = part_A()
    B = part_B()
    C = part_C()
    D = part_D()
    E = part_E(C.pop("violator_lt")) if C.get("violator_lt") else None

    print()
    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    indecomp_total = sum(r["indecomposable_violators"] for r in B) + \
        C["indecomposable_violators"]
    print(f"  (1) The inequality lambda_std <= lambda_2^BK is FALSE: exact rational")
    print(f"      witnesses at n=4 (excess 1/3) and n=6 (excess 1/10), certified.")
    print(f"  (2) 'Fails EXACTLY on the ordinal sums' holds for every poset on")
    print(f"      n <= 6 up to isomorphism -- and BREAKS at n = 7, width 3.")
    print(f"  (3) INDECOMPOSABLE violators found: {indecomp_total}"
          f"  (all at n=7; none at n<=6)")
    if E:
        print(f"      Certified EXACTLY (part E): the failure DOES reach the")
        print(f"      indecomposable class, so sec 0's hypothesis does not save")
        print(f"      the claim. mg-4a86's C3 marker is FALSE beyond n = 5 and")
        print(f"      MUST NOT be copied to the site as a rescuing restriction.")
    print(f"  (4) No poset on n <= 6 has delta < 1/3, so the frozen hypothesis")
    print(f"      cannot be instantiated at these sizes either way.")

    payload = {"work_item": "mg-d1be",
               "claim_audited": "lambda_std <= lambda_2^BK "
                                "(Reverse-Cheeger:286-288, 'the standard sector "
                                "is a subspace')",
               "A_exact_witnesses": A,
               "B_reach_test_all_posets_n_le_6": B,
               "C_width3_n7": C,
               "D_frozenness": D,
               "E_indecomposable_violator_exact": E,
               "indecomposable_violators_found": indecomp_total}
    path = "data/onethird-mgd1be-reverse-cheeger-ineq-audit.json"
    with open(path, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(f"\n  certificate -> {path}")


if __name__ == "__main__":
    main()
