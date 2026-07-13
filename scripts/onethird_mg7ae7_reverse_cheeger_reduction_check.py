#!/usr/bin/env python3.11
"""
mg-7ae7 — numerical re-verification of the RIGOROUS content of the L1b
Buser-type reverse-Cheeger reduction (docs/OneThird-L1b-Reverse-Cheeger-Proof-Attempt.md).

Checks, on both-connected posets (n=5,6), the three proved facts:

  [Prop.2]   1 - lambda_std  <=  n * leak(A) / (|A| |A^c|)        for every threshold cut A
  [Lem.3.2]  sum_k leak(A_k) ==  0.5 * E_sigma sum_x |sigma^{-1}(x) - rank_e(x)|   (exact)
  [Lem.3.3]  E[displacement]  <=  2 * E[inv_e]

Reuses the mg-b0a6 engine verbatim (transport_matrix, enumerate_both_connected).
Reference order e = a fixed linear extension of P (LEs[0]); leak/inv/displacement all
measured relative to that e.  Needs numpy (python3.11 on this machine).

Run:  python3.11 scripts/onethird_mg7ae7_reverse_cheeger_reduction_check.py
"""
import numpy as np
import numpy.linalg as la
from onethird_mgb0a6_spectral_killshot_probe import (
    Poset, transport_matrix, enumerate_both_connected,
)


def lambda_std(P):
    n = P.n
    T = np.array([[float(x) for x in row] for row in transport_matrix(P)])
    S = (T + T.T) / 2.0
    w, V = la.eigh(S)
    # top eigenvalue on H = 1-perp (S is doubly stochastic: 1 is an eigenvector, eig 1)
    return max(wi for wi, vi in zip(w, V.T) if abs(vi @ np.ones(n)) < 1e-6)


def check_poset(P):
    n = P.n
    LEs = list(P.linear_extensions())          # each LE: position a -> element
    N = len(LEs)
    gap = 1.0 - lambda_std(P)

    e = LEs[0]
    pos_in_e = {e[a]: a for a in range(n)}      # rank_e(x)
    invs = [{le[a]: a for a in range(n)} for le in LEs]   # sigma^{-1}: element -> position

    def leak_k(k):
        # E #{ labels x : rank_e(x) < k  AND  position(x) >= k }
        return sum(sum(1 for x in range(n) if pos_in_e[x] < k and p[x] >= k)
                   for p in invs) / N

    # [Prop.2]
    Ssum = 0.0
    for k in range(1, n):
        lk = leak_k(k); Ssum += lk
        Asz = sum(1 for x in range(n) if pos_in_e[x] < k)
        bound = n * lk / (Asz * (n - Asz))
        assert gap <= bound + 1e-9, (k, gap, bound)

    # [Lem.3.2] exact identity
    displ = sum(sum(abs(p[x] - pos_in_e[x]) for x in range(n)) for p in invs) / N
    id_err = abs(Ssum - 0.5 * displ)

    # [Lem.3.3]
    invE = 0.0
    for p in invs:
        invE += sum(1 for x in range(n) for y in range(n)
                    if pos_in_e[x] < pos_in_e[y] and p[y] < p[x])
    invE /= N
    displ_ok = displ <= 2 * invE + 1e-9
    return id_err, displ_ok


def main():
    posets = []
    for n in (5, 6):
        for i, P in enumerate(enumerate_both_connected(n)):
            posets.append(P)
            if len(posets) >= 30:
                break
        if len(posets) >= 30:
            break

    max_id_err = 0.0
    all_displ_ok = True
    cnt = 0
    for P in posets[:25]:
        id_err, displ_ok = check_poset(P)
        max_id_err = max(max_id_err, id_err)
        all_displ_ok = all_displ_ok and displ_ok
        cnt += 1

    print(f"checked {cnt} both-connected posets (n=5,6)")
    print("[Prop.2]  1 - lambda_std <= n*leak(A)/(|A||A^c|): all assertions PASSED")
    print(f"[Lem.3.2] max |sum_k leak(k) - 0.5*E[displacement]| = {max_id_err:.12g}  (exact identity, want 0)")
    print(f"[Lem.3.3] E[displ] <= 2 E[inv_e] for all: {all_displ_ok}")


if __name__ == "__main__":
    main()
