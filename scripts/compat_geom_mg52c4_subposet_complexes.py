r"""
Compat-Geom mg-52c4 -- the PER-POSET question: what is the homotopy type of the
complex of PROPER SUBPOSETS of an INDIVIDUAL poset P?

Verification harness for `docs/OneThird-mg52c4-PerPoset-Subposet-Question.md`.

Daniel (2026-08-06, mg-e768; re-asked 2026-08-13):
    "i remember that we proved the whole category pos_n is spherical, but i
     can't remember if we proved anything for individual posets, say for
     instance taking all their proper subposets"

The category-level theorem (F17+F18) is about Delta_n = Delta(PPF_n).  The
per-poset object is, for a fixed P in PPF_n, the OPEN LOWER INTERVAL

    Lbar(P) := { Q in PPF_n : Q proper-subset P }
             = { Q transitively closed : empty != Q proper-subset P }

(the second equality because every subrelation of a non-total P is non-total,
so the PPF_n side conditions are automatic below P).  Delta(Lbar(P)) is "the
complex of all proper subposets of P".

CLAIM UNDER TEST (mg-52c4 Theorem A; proof by Bjorner's crosscut theorem +
nerve lemma, see the doc S2.3).  Write Comp(P) for the set of comparable
(strictly related) pairs of P and Cov(P) for its cover relations.  Then

    height(P) >= 2  (i.e. Cov(P) != Comp(P), i.e. P has a 3-chain a<b<c)
        ==>  Delta(Lbar(P))  is CONTRACTIBLE;
    height(P) == 1  (i.e. Cov(P) == Comp(P))
        ==>  Delta(Lbar(P))  ~  S^{c-2},  c = |Comp(P)|.

F17's Lemma L1 (Q_0 a CHAIN => contractible) is the special case P = a chain
with an isolated point; it is recovered below as a labelled sub-check.

COROLLARY UNDER TEST (mg-52c4 Corollary B).  lk_{Delta_n}(P) =
Delta(Lbar(P)) * Delta(Ubar(P)) is contractible whenever height(P) >= 2 -- a
join with a contractible factor is contractible -- so the F17+F18 class
omega_bal^(n) restricts to ZERO on the link of every such P.

WHAT THIS SCRIPT CHECKS
  (T1) exhaustively, for every P in PPF_3, PPF_4, PPF_5 (and a sample of
       PPF_6): the Moebius number mu(empty, P) of the transitive-subrelation
       lattice equals the reduced Euler characteristic predicted above
       (0 if height >= 2, (-1)^c if height 1).
  (T2) for every P whose order complex is small enough to materialise: the
       full reduced Betti vector of Delta(Lbar(P)) equals the predicted one
       (all-zero, or a single 1 in degree c-2).
  (T3) directly, on n = 3, 4: the reduced Betti vector of the FULL LINK
       lk_{Delta_n}(P) = Delta({Q in PPF_n : Q comparable to P, Q != P}),
       against the Corollary-B prediction of contractibility for
       height(P) >= 2.
  (T4) F17 Lemma L1 as a labelled special case.

Reuses the poset/homology helpers of scripts/compat_geom_F17_equivariant_morse.py
(mg-4d3a) so that no second implementation of reduced_betti exists.

Pure-Python stdlib.  Runtime ~ 1-3 min.
"""

import json
import os
import sys
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from compat_geom_F17_equivariant_morse import (  # noqa: E402
    chains_by_dim,
    enumerate_posets,
    fvector_count,
    make_PPF,
    reduced_betti,
    transitive_closure,
)

# Cap on the number of simplices we are willing to materialise for a full
# Betti computation.  Above it we fall back to the Moebius number (T1 only).
BETTI_SIMPLEX_CAP = 60_000


# ---------------------------------------------------------------------------
# per-poset combinatorics
# ---------------------------------------------------------------------------

def covers(P):
    """Cover relations of the (transitively closed) strict order P."""
    return frozenset((a, b) for (a, b) in P
                     if not any((a, c) in P and (c, b) in P for c in
                                {x for pair in P for x in pair}))


def height_at_least_2(P):
    """True iff P has a 3-element chain a < b < c (equivalently Cov != Comp)."""
    return covers(P) != P


def transitive_subrelations(P):
    """All transitively closed Q with Q subset-of P (including empty and P)."""
    pairs = sorted(P)
    out = []
    for k in range(len(pairs) + 1):
        for sub in combinations(pairs, k):
            S = frozenset(sub)
            if transitive_closure(S) == S:
                out.append(S)
    return out


def moebius_bottom(P):
    """mu(empty, P) in the lattice of transitive subrelations of P.

    By Philip Hall, this is the reduced Euler characteristic of the order
    complex of the open interval (empty, P) = Lbar(P).
    """
    subs = transitive_subrelations(P)
    subs.sort(key=len)
    mu = {}
    for Q in subs:
        if not Q:
            mu[Q] = 1
            continue
        mu[Q] = -sum(mu[R] for R in subs if len(R) < len(Q) and R < Q)
    return mu[P]


def predicted(P):
    """(kind, predicted reduced Betti vector, predicted reduced Euler char)."""
    c = len(P)
    if height_at_least_2(P):
        return "contractible", [], 0
    d = c - 2
    if d < 0:                       # c == 1: Lbar(P) is empty, S^{-1}
        return "empty (S^-1)", [], -1
    betti = [0] * (d + 1)
    betti[d] = 1
    return f"S^{d}", betti, (-1) ** c


def norm_betti(b):
    b = list(b)
    while b and b[-1] == 0:
        b.pop()
    return b


# ---------------------------------------------------------------------------
# the two per-poset complexes
# ---------------------------------------------------------------------------

def lower_interval(P):
    """Lbar(P) = { Q in PPF_n : Q proper-subset P } -- proper subposets of P."""
    return [Q for Q in transitive_subrelations(P) if Q and Q != P]


def link_poset(P, ppf):
    """Elements of PPF_n strictly comparable to P: Delta of this = lk(P)."""
    return [Q for Q in ppf if Q != P and (Q < P or P < Q)]


# ---------------------------------------------------------------------------
# checks
# ---------------------------------------------------------------------------

def check_family(name, posets, do_betti=True):
    rows = []
    fails = []
    for P in posets:
        kind, pbetti, peuler = predicted(P)
        mu = moebius_bottom(P)
        ok_mu = (mu == peuler)
        betti = None
        ok_betti = None
        if do_betti:
            elems = lower_interval(P)
            if not elems:
                betti = []
                ok_betti = (norm_betti(pbetti) == [])
            else:
                nsimp = sum(fvector_count(elems))
                if nsimp <= BETTI_SIMPLEX_CAP:
                    betti = norm_betti(reduced_betti(chains_by_dim(elems)))
                    ok_betti = (betti == norm_betti(pbetti))
        row = {
            "P": sorted(map(list, P)),
            "n_rel": len(P),
            "height_ge_2": height_at_least_2(P),
            "predicted": kind,
            "mu": mu,
            "mu_ok": ok_mu,
            "betti": betti,
            "betti_ok": ok_betti,
        }
        rows.append(row)
        if not ok_mu or ok_betti is False:
            fails.append(row)
    n_betti = sum(1 for r in rows if r["betti_ok"] is not None)
    print(f"  {name}: {len(rows)} posets | mu checked {len(rows)} | "
          f"full Betti checked {n_betti} | FAILURES {len(fails)}")
    for r in fails[:5]:
        print(f"    FAIL {r}")
    return rows, fails


def check_control(name, posets):
    """NEGATIVE CONTROL -- can the mu test see anything at all?

    Re-scores every P against the SWAPPED prediction (contractible <-> sphere).
    If the harness is discriminating, this must produce failures in BOTH
    directions; a swapped run that still passes would mean the test is blind.
    """
    fail_h2 = fail_h1 = 0
    for P in posets:
        mu = moebius_bottom(P)
        if height_at_least_2(P):
            wrong = (-1) ** len(P)          # pretend it is S^{c-2}
            if mu != wrong:
                fail_h2 += 1
        else:
            wrong = 0                        # pretend it is contractible
            if mu != wrong:
                fail_h1 += 1
    print(f"  CONTROL {name}: swapped prediction fails on "
          f"{fail_h2} height>=2 posets and {fail_h1} height-1 posets "
          f"-> {'DISCRIMINATING' if fail_h2 and fail_h1 else 'BLIND (bad)'}")
    return fail_h2, fail_h1


def check_links(n):
    """T3 -- the full link lk_{Delta_n}(P), directly."""
    ppf = make_PPF(n)
    fails = []
    checked = 0
    contractible_h2 = 0
    for P in ppf:
        elems = link_poset(P, ppf)
        if not elems:
            betti = []
        else:
            nsimp = sum(fvector_count(elems))
            if nsimp > BETTI_SIMPLEX_CAP:
                continue
            betti = norm_betti(reduced_betti(chains_by_dim(elems)))
        checked += 1
        if height_at_least_2(P):
            if betti != []:
                fails.append((sorted(map(list, P)), betti))
            else:
                contractible_h2 += 1
    print(f"  links n={n}: {checked}/{len(ppf)} links computed | "
          f"height>=2 links found contractible: {contractible_h2} | "
          f"FAILURES {len(fails)}")
    for f in fails[:5]:
        print(f"    FAIL {f}")
    return checked, contractible_h2, fails


def check_L1(n):
    """T4 -- F17 Lemma L1: P a chain on [n] has contractible Lbar(P)."""
    chain = frozenset((i, j) for i in range(n) for j in range(n) if i < j)
    elems = lower_interval(chain)
    nsimp = sum(fvector_count(elems))
    if nsimp > BETTI_SIMPLEX_CAP:
        mu = moebius_bottom(chain)
        print(f"  L1 n={n}: |Lbar| = {len(elems)}, simplices {nsimp} > cap; "
              f"mu = {mu} (predicted 0) -> {'OK' if mu == 0 else 'FAIL'}")
        return mu == 0
    betti = norm_betti(reduced_betti(chains_by_dim(elems)))
    ok = (betti == [])
    print(f"  L1 n={n}: |Lbar| = {len(elems)}, reduced Betti {betti} "
          f"-> {'OK (contractible)' if ok else 'FAIL'}")
    return ok


def main():
    out = {"claim": "mg-52c4 Theorem A + Corollary B", "families": {}}
    all_fail = 0

    print("T1/T2 -- Delta(Lbar(P)) for every P in PPF_n")
    for n in (3, 4, 5):
        ppf = make_PPF(n)
        rows, fails = check_family(f"PPF_{n}", ppf, do_betti=(n <= 4))
        all_fail += len(fails)
        n_h1 = sum(1 for r in rows if not r["height_ge_2"])
        out["families"][f"PPF_{n}"] = {
            "count": len(rows),
            "height_ge_2": len(rows) - n_h1,
            "height_1": n_h1,
            "mu_failures": len(fails),
            "full_betti_checked": sum(1 for r in rows
                                      if r["betti_ok"] is not None),
        }

    print("\nT1 -- sample of PPF_6 (every 37th poset, plus all height-1 ones)")
    ppf6 = make_PPF(6)
    sample = [P for i, P in enumerate(ppf6) if i % 37 == 0]
    h1_6 = [P for P in ppf6 if not height_at_least_2(P)]
    sample = list({P for P in sample} | {P for P in h1_6})
    rows6, fails6 = check_family("PPF_6 sample", sample, do_betti=False)
    all_fail += len(fails6)
    out["families"]["PPF_6_sample"] = {
        "count": len(rows6),
        "height_1_all_included": len(h1_6),
        "mu_failures": len(fails6),
    }

    print("\nCONTROL -- swap the prediction; the harness must go RED")
    out["control"] = {}
    for n in (4, 5):
        f2, f1 = check_control(f"PPF_{n}", make_PPF(n))
        out["control"][f"PPF_{n}"] = {"swapped_fail_height_ge_2": f2,
                                      "swapped_fail_height_1": f1}
        if not (f2 and f1):
            all_fail += 1        # a blind harness is itself a failure

    print("\nT3 -- the full link lk_{Delta_n}(P) (Corollary B)")
    out["links"] = {}
    for n in (3, 4):
        checked, contr, fails = check_links(n)
        all_fail += len(fails)
        out["links"][f"n={n}"] = {
            "links_computed": checked,
            "height_ge_2_contractible": contr,
            "failures": len(fails),
        }

    print("\nT4 -- F17 Lemma L1 recovered as the chain case")
    out["L1"] = {}
    for n in (3, 4, 5):
        ok = check_L1(n)
        out["L1"][f"n={n}"] = bool(ok)
        if not ok:
            all_fail += 1

    out["ALL_PASS"] = (all_fail == 0)
    print(f"\nALL_PASS = {out['ALL_PASS']}  (total failures {all_fail})")

    dest = os.path.join(os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))), "data",
        "onethird-mg52c4-subposet-complexes.json")
    with open(dest, "w") as fh:
        json.dump(out, fh, indent=2, sort_keys=True)
    print(f"wrote {dest}")
    return 0 if all_fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
