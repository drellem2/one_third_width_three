#!/usr/bin/env python3
r"""
posn_n_validate.py
==================

Sanity check for posn_n6_hpc.py: re-run the Burnside / Lefschetz
calculation at n=4 (PPF_4, small) and n=5 (PPF_5) where we have
F2 / F7 published values, to pin down the SIGN CONVENTION in
   m_sgn = ±(1/|S_n|) · Σ sgn(σ) · χ̃(Fix(σ))
and verify the χ̃(Fix(σ)) = ±sgn(σ) Lefschetz identity.

Per F2 (mg-7455) at n=4 and F7 (mg-73fd) at n=5, m_sgn = 1.

Usage:
    python3 posn_n_validate.py --n=4
    python3 posn_n_validate.py --n=5
"""

from __future__ import annotations
import argparse
import time
from fractions import Fraction
from itertools import permutations
from math import factorial


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
    for (a, b) in rel:
        if (b, a) in rel:
            return False
    return True


def is_chain(P, n):
    return len(P) == n * (n - 1) // 2


def enumerate_PPF(n):
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


def apply_perm(P, sigma):
    return frozenset((sigma[a], sigma[b]) for (a, b) in P)


def perm_parity(sigma):
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


def fixed_PPF(sigma, ppf_set):
    return [P for P in ppf_set if apply_perm(P, sigma) == P]


def order_complex_chi_tilde(elements):
    if not elements:
        return -1, [0]
    elts = sorted(elements, key=lambda P: (len(P), tuple(sorted(P))))
    n_elts = len(elts)
    elts_sets = [set(P) for P in elts]
    below = [[] for _ in range(n_elts)]
    for i in range(n_elts):
        li = len(elts_sets[i])
        for j in range(i):
            if len(elts_sets[j]) < li and elts_sets[j].issubset(elts_sets[i]):
                below[i].append(j)
    f_vec = []
    layer = [1] * n_elts
    while True:
        fk = sum(layer)
        if fk == 0:
            break
        f_vec.append(fk)
        nxt = [0] * n_elts
        for i in range(n_elts):
            nxt[i] = sum(layer[j] for j in below[i])
        layer = nxt
    chi_tilde = -1
    for k, fk in enumerate(f_vec):
        chi_tilde += ((-1) ** k) * fk
    return chi_tilde, f_vec


# Conjugacy class reps for S_n (n up to 5).
CONJ_REPS_S4 = [
    ((0, 1, 2, 3), '1^4',     1,  +1),
    ((1, 0, 2, 3), '2,1^2',   6,  -1),
    ((1, 2, 0, 3), '3,1',     8,  +1),
    ((1, 0, 3, 2), '2^2',     3,  +1),
    ((1, 2, 3, 0), '4',       6,  -1),
]
CONJ_REPS_S5 = [
    ((0, 1, 2, 3, 4), '1^5',     1,  +1),
    ((1, 0, 2, 3, 4), '2,1^3',  10,  -1),
    ((1, 2, 0, 3, 4), '3,1^2',  20,  +1),
    ((1, 0, 3, 2, 4), '2^2,1',  15,  +1),
    ((1, 2, 3, 0, 4), '4,1',    30,  -1),
    ((1, 2, 3, 4, 0), '5',      24,  +1),
    ((1, 2, 0, 4, 3), '3,2',    20,  -1),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, choices=[4, 5], default=4)
    args = ap.parse_args()
    n = args.n
    factn = factorial(n)
    print(f"posn_n_validate.py at n={n}")
    print(f"  enumerating PPF_{n}...")
    t0 = time.time()
    ppf = enumerate_PPF(n)
    print(f"  |PPF_{n}| = {len(ppf)}  ({time.time()-t0:.1f}s)")
    conj_reps = CONJ_REPS_S4 if n == 4 else CONJ_REPS_S5
    total_class_sz = sum(sz for (_, _, sz, _) in conj_reps)
    assert total_class_sz == factn, f"class sizes sum to {total_class_sz}, want {factn}"
    print()
    print(f"  Burnside table:")
    print(f"  {'class':>10}  {'|class|':>8}  {'sgn':>3}  {'|Fix|':>8}  "
          f"{'χ̃(Fix)':>8}  {'χ̃ == sgn?':>11}  {'χ̃ == -sgn?':>12}")
    print(f"  {'-'*78}")
    total_signed = 0
    total_signed_with_class = 0
    for (sigma, label, sz, sgn) in conj_reps:
        fix = fixed_PPF(sigma, frozenset(ppf))
        chi, fvec = order_complex_chi_tilde(fix)
        eq_plus = (chi == sgn)
        eq_minus = (chi == -sgn)
        print(f"  {label:>10}  {sz:>8}  {sgn:>+3}  {len(fix):>8}  "
              f"{chi:>8}  {'✓' if eq_plus else '✗':>11}  "
              f"{'✓' if eq_minus else '✗':>12}")
        total_signed += sgn * chi
        total_signed_with_class += sz * sgn * chi
    print(f"  {'-'*78}")
    print()
    print(f"  Σ over class REPS:        Σ sgn(σ)·χ̃(Fix(σ))            = {total_signed}")
    print(f"  Σ over full GROUP S_{n}:   Σ_σ sgn(σ)·χ̃(Fix(σ))         = {total_signed_with_class}")
    print()
    m_pos_full = Fraction(total_signed_with_class, factn)
    m_neg_full = Fraction(-total_signed_with_class, factn)
    print(f"  m_sgn = +(1/|S_{n}|)·Σ = {m_pos_full}")
    print(f"  m_sgn = -(1/|S_{n}|)·Σ = {m_neg_full}")
    print()
    print(f"  Expected (F2/F7):  m_sgn = 1")
    if m_pos_full == 1:
        print(f"  → CORRECT SIGN: m_sgn = +(1/|S_n|)·Σ sgn(σ)·χ̃(Fix(σ))")
    elif m_neg_full == 1:
        print(f"  → CORRECT SIGN: m_sgn = -(1/|S_n|)·Σ sgn(σ)·χ̃(Fix(σ))")
    else:
        print(f"  → ??? Neither sign gives m_sgn=1: data inconsistent")


if __name__ == '__main__':
    main()
