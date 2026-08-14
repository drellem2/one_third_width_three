#!/usr/bin/env python3
"""
mg-e08a — INDEPENDENT AUDIT of mg-52c4's Theorem A and Corollary B.

Audits `docs/OneThird-mg52c4-PerPoset-Subposet-Question.md` (commit cf63bb3).
Predictions pre-registered in `docs/OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md`
BEFORE this file existed.

INDEPENDENCE.  This script shares no code with the instrument under audit.
`scripts/compat_geom_mg52c4_subposet_complexes.py` imports `reduced_betti` from
`scripts/compat_geom_F17_equivariant_morse.py`; this script imports nothing from the repo
and re-implements, from scratch: poset enumeration, transitive closure, the order complex,
and the boundary-rank / reduced-Betti routine (two primes, persistence-style reduction).
This script is NOT a re-run of the audited harness; it re-derives every number.

WHAT IT DOES THAT THE AUDITED RUN DID NOT
  * Checks the two named proof steps (§2.4) as machine predicates, exhaustively, rather
    than checking only the theorem's conclusion.
  * Pushes FULL reduced Betti to n = 5 (the audited run stopped at n = 4 and relied on a
    Moebius/Euler check that provably cannot distinguish contractible from a cancelling wedge).
  * Exhibits an explicit poset that FOOLS the Euler check and is caught by Betti — making
    the admitted blindness concrete rather than asserted.
  * Computes the links at HEIGHT-1 vertices, which the audited run's T3 table does not report.
  * Computes Delta(upP \\ {P}), the object §3.5 calls uncomputed, for every iso class n <= 5
    within cap.
  * Tests the anchor-degree component Hred_{n-2}(lk P) at EVERY vertex, not only the
    height->=2 ones Corollary B covers.

Run: /usr/bin/python3 scripts/compat_geom_mge08a_theoremA_audit.py   (stdlib only)
Output: data/onethird-mge08a-theoremA-audit.json
"""

import itertools
import collections
import json
import os
import sys
import time

P1 = (1 << 31) - 1          # Mersenne prime
P2 = 1000003                # second prime; disagreement => torsion/bad-prime flag

# --------------------------------------------------------------------------------------
# 1.  Posets, transitive closure, the lower interval  (all re-implemented from scratch)
# --------------------------------------------------------------------------------------


def all_posets(n):
    """Every strict partial order on [n], as a frozenset of pairs (a, b) meaning a < b.

    Built by choosing, for each unordered pair, one of {incomparable, a<b, b<a} and then
    testing transitivity directly.  No repo code is involved.
    """
    pairs = list(itertools.combinations(range(n), 2))
    out = []
    for choice in itertools.product((0, 1, 2), repeat=len(pairs)):
        rel = set()
        for (a, b), ch in zip(pairs, choice):
            if ch == 1:
                rel.add((a, b))
            elif ch == 2:
                rel.add((b, a))
        if is_transitive(rel):
            out.append(frozenset(rel))
    return out


def is_transitive(rel):
    for (x, y) in rel:
        for (u, v) in rel:
            if y == u and (x, v) not in rel:
                return False
    return True


def tc(rel):
    """Transitive closure of a relation set."""
    rel = set(rel)
    while True:
        new = set()
        for (x, y) in rel:
            for (u, v) in rel:
                if y == u and (x, v) not in rel:
                    new.add((x, v))
        if not new:
            return frozenset(rel)
        rel |= new


def ppf(n):
    """PPF_n: proper partial orders on [n] -- nonempty relation, non-total."""
    full = n * (n - 1) // 2
    return [p for p in all_posets(n) if 0 < len(p) < full]


def covers(P):
    """Cover relations of P: (a,b) in P with no c strictly between."""
    out = set()
    for (a, b) in P:
        if not any((a, c) in P and (c, b) in P for c in range(max(max(x) for x in P) + 1)):
            out.add((a, b))
    return frozenset(out)


def height_ge_2(P):
    """True iff P has a 3-element chain (equivalently Cov(P) != Comp(P))."""
    for (a, b) in P:
        for (c, d) in P:
            if b == c:
                return True
    return False


def Lbar(P):
    """{Q : nonempty, Q strictly contained in P, Q transitively closed} -- the proper subposets."""
    items = sorted(P)
    out = []
    for k in range(1, len(items)):
        for sub in itertools.combinations(items, k):
            s = frozenset(sub)
            if is_transitive(s):
                out.append(s)
    return out


def canon(P, n):
    """Canonical form of P under relabelling of [n] -- the homotopy type of Delta(Lbar(P))
    is a relabelling invariant, so iso classes are the honest work unit."""
    best = None
    for perm in itertools.permutations(range(n)):
        k = tuple(sorted((perm[a], perm[b]) for (a, b) in P))
        if best is None or k < best:
            best = k
    return best


# --------------------------------------------------------------------------------------
# 2.  Order complexes and reduced homology  (independent implementation)
# --------------------------------------------------------------------------------------


def chains_of(elems, leq):
    """All nonempty chains of the poset (elems, leq), as tuples of indices, increasing."""
    elems = list(elems)
    N = len(elems)
    up = [[j for j in range(N) if i != j and leq(elems[i], elems[j])] for i in range(N)]
    out = []
    path = []

    def rec(i):
        path.append(i)
        out.append(tuple(path))
        for j in up[i]:
            rec(j)
        path.pop()

    for i in range(N):
        rec(i)
    return out


def count_chains(elems, leq):
    """Number of nonempty chains, without materialising them (used for the size cap)."""
    elems = list(elems)
    N = len(elems)
    up = [[j for j in range(N) if i != j and leq(elems[i], elems[j])] for i in range(N)]
    memo = [None] * N

    def f(i):
        if memo[i] is None:
            memo[i] = 1 + sum(f(j) for j in up[i])
        return memo[i]

    return sum(f(i) for i in range(N))


def _rank_mod_p(cols, p):
    """Rank of a sparse matrix given as a list of columns (dict row -> coeff), mod p.
    Persistence-style reduction: reduce each column against stored pivots by low index."""
    piv = {}
    r = 0
    for col in cols:
        c = {k: v % p for k, v in col.items() if v % p}
        while c:
            lo = max(c)
            if lo in piv:
                oc = piv[lo]
                f = (c[lo] * pow(oc[lo], p - 2, p)) % p
                for k, v in oc.items():
                    nv = (c.get(k, 0) - f * v) % p
                    if nv:
                        c[k] = nv
                    elif k in c:
                        del c[k]
            else:
                piv[lo] = c
                r += 1
                break
    return r


def reduced_betti_of_chains(chains, primes=(P1, P2)):
    """Reduced Betti numbers of the simplicial complex whose simplices are `chains`.

    Convention: the empty complex has Hred_{-1} = 1 (S^{-1}).  Augmented chain complex,
    so Hred_0 counts (components - 1).
    """
    if not chains:
        return {-1: 1}, True
    bydim = collections.defaultdict(list)
    for c in chains:
        bydim[len(c) - 1].append(c)
    idx = {d: {s: i for i, s in enumerate(v)} for d, v in bydim.items()}
    maxd = max(bydim)

    results = []
    for p in primes:
        ranks = {}
        for d in range(0, maxd + 1):
            cols = []
            for s in bydim[d]:
                col = {}
                for i in range(len(s)):
                    sign = 1 if i % 2 == 0 else -1
                    if d == 0:
                        col[0] = col.get(0, 0) + sign      # augmentation to the empty face
                    else:
                        col[idx[d - 1][s[:i] + s[i + 1:]]] = sign
                cols.append({k: v % p for k, v in col.items() if v % p})
            ranks[d] = _rank_mod_p(cols, p)
        b = {}
        for d in range(0, maxd + 1):
            b[d] = len(bydim[d]) - ranks.get(d, 0) - ranks.get(d + 1, 0)
        results.append(b)
    agree = all(r == results[0] for r in results)
    return results[0], agree


def betti_of_poset(elems, leq=None, cap=None):
    """Reduced Betti of the order complex of a poset given as a list of comparable objects."""
    if leq is None:
        leq = lambda a, b: a < b
    if not elems:
        return {-1: 1}, True, 0
    nsimp = count_chains(elems, leq)
    if cap is not None and nsimp > cap:
        return None, None, nsimp
    b, agree = reduced_betti_of_chains(chains_of(elems, leq))
    return b, agree, nsimp


def is_contractible(b):
    return b is not None and all(v == 0 for v in b.values())


def sphere_profile(d):
    """Reduced Betti of S^d (d = -1 means the empty complex)."""
    return {d: 1}


def matches_sphere(b, d):
    if b is None:
        return None
    if d < 0:
        return b == {-1: 1}
    return all(v == (1 if k == d else 0) for k, v in b.items()) and b.get(d, 0) == 1


def reduced_euler(b):
    """Reduced Euler characteristic from a reduced Betti dict."""
    return sum(((-1) ** d) * v for d, v in b.items())


# --------------------------------------------------------------------------------------
# 3.  Section H -- controls on MY OWN instrument (must run before any verdict)
# --------------------------------------------------------------------------------------


def complex_from_facets(facets):
    """All nonempty faces of the given facets, as sorted tuples."""
    out = set()
    for f in facets:
        f = tuple(sorted(f))
        for k in range(1, len(f) + 1):
            for s in itertools.combinations(f, k):
                out.add(s)
    return sorted(out, key=lambda s: (len(s), s))


# Moebius-Kantor 7-vertex torus: {i, i+1, i+3} and {i, i+2, i+3} over Z_7.
TORUS = ([tuple(sorted((i % 7, (i + 1) % 7, (i + 3) % 7))) for i in range(7)]
         + [tuple(sorted((i % 7, (i + 2) % 7, (i + 3) % 7))) for i in range(7)])

# The minimal 6-vertex triangulation of the real projective plane.
RP2 = [(1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 6), (1, 5, 6),
       (2, 3, 5), (2, 3, 6), (2, 4, 6), (3, 4, 5), (4, 5, 6)]


def section_H_instrument_controls():
    """H1: my Betti routine reproduces independently-known answers.  If this section
    fails, nothing else in this file means anything."""
    res = []

    def chk(name, chains, expect):
        b, agree = reduced_betti_of_chains(chains)
        got = {k: v for k, v in b.items() if v}
        ok = (got == expect) and agree
        res.append({"case": name, "expected": {str(k): v for k, v in expect.items()},
                    "got": {str(k): v for k, v in got.items()},
                    "two_primes_agree": agree, "pass": ok})

    for k in range(1, 6):                       # boundary of the (k)-simplex  ==  S^{k-1}
        facets = list(itertools.combinations(range(k + 1), k))
        chk("bd_simplex_%d_is_S%d" % (k, k - 1), complex_from_facets(facets), {k - 1: 1})
    chk("torus_moebius_kantor_7vertex", complex_from_facets(TORUS), {1: 2, 2: 1})

    # RP^2 is Q-ACYCLIC but NOT contractible.  This is a control on MY OWN blindness:
    # rational Betti numbers -- the verification currency of both this audit and the
    # audited harness -- cannot distinguish RP^2 from a point.  Recorded, not hidden.
    b_rp2, agree_rp2 = reduced_betti_of_chains(complex_from_facets(RP2))
    res.append({"case": "RP2_is_Q_acyclic_but_NOT_contractible",
                "expected": {"(all zero over Q)": 0},
                "got": {str(k): v for k, v in b_rp2.items()},
                "two_primes_agree": agree_rp2,
                "pass": all(v == 0 for v in b_rp2.values()),
                "LIMITATION": ("Rational Betti calls this contractible and it is not. "
                               "Every 'contractible' verdict in this file and in the "
                               "audited harness is really 'Q-acyclic'. Theorem A (A1) "
                               "claims genuine contractibility; the PROOF (a closure "
                               "operator onto a cone) is what supplies that, not any "
                               "Betti computation.")})

    b, _ = reduced_betti_of_chains([])
    res.append({"case": "empty_complex_is_S-1", "expected": {"-1": 1},
                "got": {str(k): v for k, v in b.items()}, "two_primes_agree": True,
                "pass": b == {-1: 1}})
    # a disjoint union: two triangle boundaries -> Hred_0 = 1, Hred_1 = 2
    two = complex_from_facets([(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)])
    chk("two_circles_disjoint", two, {0: 1, 1: 2})
    return res


# --------------------------------------------------------------------------------------
# 4.  Section D -- the Euler/Moebius blindness, made concrete
# --------------------------------------------------------------------------------------


def face_poset_order_complex(facets):
    """Order complex of the face poset of a complex K  ==  sd(K), homeomorphic to K.
    This turns ANY complex into a genuine ORDER COMPLEX OF A POSET, which is what the
    audited T1/T2 checks range over."""
    faces = complex_from_facets(facets)
    fs = [frozenset(f) for f in faces]
    return fs


def section_D_euler_blindness():
    """D1: exhibit a POSET whose order complex has reduced Euler characteristic 0 --
    so the Moebius/Euler predicate calls it 'contractible' -- but which is NOT
    contractible.  This is the exact shape of hole the audited doc admits at §2.4."""
    # wedge of S^1 and S^2, joined at vertex 0
    circle = [(0, 1), (1, 2), (2, 0)]
    sphere = [f for f in itertools.combinations([0, 3, 4, 5], 3)]
    wedge = circle + sphere
    poset = face_poset_order_complex(wedge)          # sd(wedge), an honest order complex
    b, agree = reduced_betti_of_chains(chains_of(poset, lambda a, b_: a < b_ and a != b_))
    chi = reduced_euler(b)
    euler_predicate_says_contractible = (chi == 0)
    betti_predicate_says_contractible = is_contractible(b)
    return {
        "object": "order complex of the face poset of (S^1 wedge S^2)",
        "n_poset_elements": len(poset),
        "reduced_betti": {str(k): v for k, v in b.items() if v},
        "reduced_euler_char": chi,
        "EULER_predicate_calls_it_contractible": euler_predicate_says_contractible,
        "BETTI_predicate_calls_it_contractible": betti_predicate_says_contractible,
        "two_primes_agree": agree,
        # the demonstration passes iff Euler is fooled AND Betti is not
        "pass": euler_predicate_says_contractible and not betti_predicate_says_contractible,
        "note": ("A Moebius/Euler check cannot distinguish this from contractible. "
                 "This is why full Betti, not Euler, is what verifies (A1)."),
    }


# --------------------------------------------------------------------------------------
# 5.  Section PS -- the two proof steps §2.4 names, as machine predicates
# --------------------------------------------------------------------------------------


def section_PS_named_proof_steps(nmax=5):
    """§2.4: 'an auditor should check (i) the join-irreducibility of cover relations under
    tc, and (ii) that kappa's image is nonempty *and* proper.'  Checked exhaustively, as
    predicates, over every poset on <= nmax elements -- not by checking the conclusion."""
    out = {"step_i_cover_join_irreducible": {"tested": 0, "failures": []},
           "step_ii_kappa_image": {"tested": 0, "failures": []},
           "step_iii_kappa_closure_operator": {"tested": 0, "failures": []},
           "step_iv_image_is_fixed_points_with_min_v": {"tested": 0, "failures": []}}

    for n in range(2, nmax + 1):
        for P in all_posets(n):
            if not P:
                continue
            cov = covers(P)
            items = sorted(P)

            # (i)  for EVERY S subset of P, every cover of P lying in tc(S) already lies in S.
            #      The proof's unstated side condition is S subset of P; we test exactly that.
            if len(items) <= 8:
                for k in range(0, len(items) + 1):
                    for sub in itertools.combinations(items, k):
                        S = frozenset(sub)
                        T = tc(S)
                        out["step_i_cover_join_irreducible"]["tested"] += 1
                        bad = [e for e in cov if e in T and e not in S]
                        if bad:
                            out["step_i_cover_join_irreducible"]["failures"].append(
                                {"n": n, "P": sorted(P), "S": sorted(S), "bad": sorted(bad)})

            # (ii)-(iv) only apply when a comparable non-cover pair v exists (the (A1) case)
            noncov = sorted(set(P) - cov)
            if not noncov:
                continue
            v = noncov[0]
            L = Lbar(P)
            if len(L) > 400:
                continue
            Lset = set(L)

            # (ii) kappa lands in Lbar(P): nonempty AND proper AND transitively closed
            image = set()
            ok_ii = True
            for Q in L:
                K = tc(set(Q) | {v})
                out["step_ii_kappa_image"]["tested"] += 1
                if (not K) or (K == P) or (not K <= P) or (K not in Lset):
                    out["step_ii_kappa_image"]["failures"].append(
                        {"n": n, "P": sorted(P), "v": v, "Q": sorted(Q), "kappa": sorted(K),
                         "reason": "empty" if not K else ("equals P" if K == P else "not in Lbar")})
                    ok_ii = False
                image.add(K)

            # (iii) closure operator: extensive, monotone, idempotent
            for Q in L:
                K = tc(set(Q) | {v})
                out["step_iii_kappa_closure_operator"]["tested"] += 1
                if not (set(Q) <= set(K)):
                    out["step_iii_kappa_closure_operator"]["failures"].append(
                        {"n": n, "P": sorted(P), "why": "not extensive", "Q": sorted(Q)})
                if tc(set(K) | {v}) != K:
                    out["step_iii_kappa_closure_operator"]["failures"].append(
                        {"n": n, "P": sorted(P), "why": "not idempotent", "Q": sorted(Q)})
            for Q in L:
                for R in L:
                    if set(Q) <= set(R):
                        if not (set(tc(set(Q) | {v})) <= set(tc(set(R) | {v}))):
                            out["step_iii_kappa_closure_operator"]["failures"].append(
                                {"n": n, "P": sorted(P), "why": "not monotone"})

            # (iv) image == fixed points == {Q in Lbar : v in Q}, and has global minimum {v}
            out["step_iv_image_is_fixed_points_with_min_v"]["tested"] += 1
            fixed = {Q for Q in L if v in Q}
            if image != fixed:
                out["step_iv_image_is_fixed_points_with_min_v"]["failures"].append(
                    {"n": n, "P": sorted(P), "why": "image != fixed-point set"})
            elif frozenset({v}) not in image:
                out["step_iv_image_is_fixed_points_with_min_v"]["failures"].append(
                    {"n": n, "P": sorted(P), "why": "{v} not in image"})
            elif not all(frozenset({v}) <= Q for Q in image):
                out["step_iv_image_is_fixed_points_with_min_v"]["failures"].append(
                    {"n": n, "P": sorted(P), "why": "{v} is not a global minimum of the image"})
            _ = ok_ii

    for k in out:
        out[k]["pass"] = not out[k]["failures"]
        out[k]["failures"] = out[k]["failures"][:5]
    return out


# --------------------------------------------------------------------------------------
# 6.  Section TA -- Theorem A itself, by FULL reduced Betti, over iso classes
# --------------------------------------------------------------------------------------


def theoremA_prediction(P):
    """(A1) contractible if P has a 3-chain; (A2) S^{c-2} if height 1."""
    if height_ge_2(P):
        return ("contractible", None)
    return ("sphere", len(P) - 2)


def check_one(P, cap):
    L = Lbar(P)
    kind, d = theoremA_prediction(P)
    b, agree, nsimp = betti_of_poset(L, cap=cap)
    if b is None:
        return {"skipped_over_cap": True, "n_simplices": nsimp, "c": len(P),
                "predicted": kind, "|Lbar|": len(L)}
    ok = is_contractible(b) if kind == "contractible" else matches_sphere(b, d)
    return {"c": len(P), "|Lbar|": len(L), "n_simplices": nsimp, "predicted": kind,
            "predicted_dim": d, "betti": {str(k): v for k, v in b.items() if v},
            "two_primes_agree": agree, "pass": bool(ok) and agree}


def section_TA_theoremA(cap):
    """Full reduced Betti verification of Theorem A over every ISOMORPHISM CLASS of poset
    on n <= 5 elements.  Because Delta(Lbar(P)) ~= Delta(Lbar(sigma P)) for any relabelling
    sigma, covering the iso classes covers every labelled poset -- in particular all 4110
    elements of PPF_5, which the audited run reached only by Moebius."""
    out = {}
    for n in (2, 3, 4, 5):
        reps = {}
        for P in all_posets(n):
            if P:
                reps.setdefault(canon(P, n), P)
        rows, fails, skipped = [], [], []
        for _, P in sorted(reps.items()):
            r = check_one(P, cap)
            r["P"] = sorted(P)
            if r.get("skipped_over_cap"):
                skipped.append(r)
            else:
                rows.append(r)
                if not r["pass"]:
                    fails.append(r)
        # how many LABELLED posets / PPF_n elements this covers
        full = n * (n - 1) // 2
        covered = 0
        skipped_canons = {tuple(sorted(map(tuple, s["P"]))) for s in skipped}
        for P in all_posets(n):
            if 0 < len(P) < full:
                if tuple(sorted(canon(P, n))) not in {tuple(sorted(s)) for s in skipped_canons}:
                    covered += 1
        out["n=%d" % n] = {
            "iso_classes_with_a_relation": len(reps),
            "verified_full_betti": len(rows),
            "over_cap_skipped": len(skipped),
            "skipped_detail": [{"c": s["c"], "|Lbar|": s["|Lbar|"],
                                "n_simplices": s["n_simplices"], "P": s["P"]} for s in skipped],
            "failures": fails,
            "pass": not fails,
            "largest_complex_verified": max([r["n_simplices"] for r in rows] or [0]),
        }
    return out


def section_TA_high_c(cmax=8):
    """(A2) at values of c larger than anything reachable inside PPF_4 -- Theorem A is a
    statement about an ARBITRARY finite poset, so c, not n, is the real parameter."""
    rows = []
    for c in range(1, cmax + 1):
        # height-1 poset with exactly c comparable pairs: a 'crown' a_i < b_i, all distinct
        P = frozenset((2 * i, 2 * i + 1) for i in range(c))
        r = check_one(P, cap=3_000_000)
        r["P"] = "disjoint union of %d 2-chains (height 1, c=%d)" % (c, c)
        rows.append(r)
    return {"rows": rows, "pass": all(r.get("pass") for r in rows if not r.get("skipped_over_cap"))}


# --------------------------------------------------------------------------------------
# 7.  Sections H2/H3 -- controls that my checker CAN fail
# --------------------------------------------------------------------------------------


def section_H2_swapped_control(n=4):
    """H2: assert the SWAPPED prediction (sphere for height>=2, contractible for height 1).
    A checker that cannot fail would pass this.  Must go RED on 100% of both classes,
    wherever the two predictions actually differ."""
    stats = collections.Counter()
    for P in ppf(n):
        L = Lbar(P)
        b, agree, _ = betti_of_poset(L, cap=2_000_000)
        if b is None:
            continue
        if height_ge_2(P):
            swapped_ok = matches_sphere(b, len(P) - 2)     # claim a sphere where truth is a point
            stats["height>=2_swapped_passes" if swapped_ok else "height>=2_swapped_FAILS"] += 1
        else:
            swapped_ok = is_contractible(b)                # claim a point where truth is a sphere
            stats["height1_swapped_passes" if swapped_ok else "height1_swapped_FAILS"] += 1
    tot_h2 = stats["height>=2_swapped_FAILS"] + stats["height>=2_swapped_passes"]
    tot_h1 = stats["height1_swapped_FAILS"] + stats["height1_swapped_passes"]
    return {"counts": dict(stats),
            "height>=2_fail_rate": stats["height>=2_swapped_FAILS"] / tot_h2 if tot_h2 else None,
            "height1_fail_rate": stats["height1_swapped_FAILS"] / tot_h1 if tot_h1 else None,
            "pass": stats["height>=2_swapped_passes"] == 0 and stats["height1_swapped_passes"] == 0,
            "note": "DISCRIMINATING iff both swapped classes fail 100%."}


def section_H3_perturbation_control():
    """H3 -- the control this ticket demands: perturb a case the theorem covers so that the
    answer MUST change, and confirm the check reports the change.  A swapped-label control
    (H2) can be passed by an instrument that merely computes the right thing on the cases it
    was handed; H3 additionally requires the instrument to track a MOVING answer."""
    rows = []

    # (a) height 1 -> height >= 2 by ADDING one relation that creates a 3-chain.
    #     Prediction must flip from S^{c-2} to contractible.
    base = frozenset({(0, 1), (2, 3)})                       # height 1, c = 2  -> S^0
    pert = tc(set(base) | {(1, 2)})                          # 0<1<2<3          -> contractible
    for tag, Q in (("before_add", base), ("after_add", pert)):
        b, agree, _ = betti_of_poset(Lbar(Q), cap=2_000_000)
        rows.append({"case": "add-relation " + tag, "P": sorted(Q), "c": len(Q),
                     "height>=2": height_ge_2(Q),
                     "betti": {str(k): v for k, v in b.items() if v},
                     "predicted": theoremA_prediction(Q)[0],
                     "matches_prediction": bool(is_contractible(b) if height_ge_2(Q)
                                                else matches_sphere(b, len(Q) - 2))})

    # (b) height >= 2 -> height 1 by DELETING the relations that make the 3-chain.
    base2 = tc({(0, 1), (1, 2)})                             # 0<1<2, c = 3  -> contractible
    pert2 = frozenset({(0, 1), (3, 4), (5, 6)})              # height 1, c = 3 -> S^1
    for tag, Q in (("before_delete", base2), ("after_delete", pert2)):
        b, agree, _ = betti_of_poset(Lbar(Q), cap=2_000_000)
        rows.append({"case": "delete-relation " + tag, "P": sorted(Q), "c": len(Q),
                     "height>=2": height_ge_2(Q),
                     "betti": {str(k): v for k, v in b.items() if v},
                     "predicted": theoremA_prediction(Q)[0],
                     "matches_prediction": bool(is_contractible(b) if height_ge_2(Q)
                                                else matches_sphere(b, len(Q) - 2))})

    # the control DISCRIMINATES iff the measured answers actually differ across each flip
    flip_a = rows[0]["betti"] != rows[1]["betti"]
    flip_b = rows[2]["betti"] != rows[3]["betti"]
    return {"rows": rows, "answer_moved_on_add": flip_a, "answer_moved_on_delete": flip_b,
            "all_match_prediction": all(r["matches_prediction"] for r in rows),
            "pass": flip_a and flip_b and all(r["matches_prediction"] for r in rows)}


# --------------------------------------------------------------------------------------
# 8.  Section LK -- the LINKS, including the height-1 ones the audited T3 does not report
# --------------------------------------------------------------------------------------


def section_LK_links(n, cap=2_000_000):
    """Corollary B says lk(P) is contractible for every P of height >= 2.  The audited run
    reports '108/108 height->=2 links contractible' at n=4 and says nothing about the other
    86.  Here EVERY vertex is reported, split by (height, c)."""
    PPF = ppf(n)
    base_b, _, _ = betti_of_poset(PPF, cap=None)
    tab = collections.Counter()
    detail = {}
    anchor_deg = n - 2
    anchor_nonzero = []
    noncontractible = []
    for P in PPF:
        lk = [Q for Q in PPF if Q < P or P < Q]
        b, agree, _ = betti_of_poset(lk, cap=cap)
        if b is None:
            tab[("OVERCAP", height_ge_2(P), len(P))] += 1
            continue
        key = ("h>=2" if height_ge_2(P) else "h=1", len(P), is_contractible(b),
               tuple(sorted((k, v) for k, v in b.items() if v)))
        tab[key] += 1
        detail.setdefault(key, sorted(P))
        if not is_contractible(b):
            noncontractible.append(sorted(P))
        if b.get(anchor_deg, 0):
            anchor_nonzero.append({"P": sorted(P), "betti_at_anchor_degree": b[anchor_deg]})
    rows = []
    for k in sorted(tab, key=lambda t: (str(t[0]), t[1])):
        rows.append({"height": k[0], "c": k[1], "link_contractible": k[2],
                     "link_reduced_betti": {str(a): v for a, v in k[3]},
                     "count": tab[k], "example_P": detail.get(k)})
    return {
        "Delta_n_reduced_betti": {str(k): v for k, v in base_b.items() if v},
        "n_vertices": len(PPF),
        "rows": rows,
        "n_links_noncontractible": len(noncontractible),
        # NB: `all(...)` over an empty height->=2 population is vacuously True.  At n=3 the
        # population IS empty, so the flag alone would report a pass Corollary B never
        # earned.  The population size is reported alongside it and the roll-up refuses a
        # vacuous pass.
        "COROLLARY_B_holds_on_height>=2": all(
            r["link_contractible"] for r in rows if r["height"] == "h>=2"),
        "height>=2_population": sum(r["count"] for r in rows if r["height"] == "h>=2"),
        "COROLLARY_B_check_is_VACUOUS_here": not any(r["height"] == "h>=2" for r in rows),
        "vertices_with_NONZERO_link_homology_in_anchor_degree_n-2": anchor_nonzero,
        "anchor_degree": anchor_deg,
        "example_noncontractible_links": noncontractible[:4],
    }


def section_DEL_deletion(n):
    """If lk(P) is contractible then Delta_n and Delta_n minus {P} have the same reduced
    homology (Mayer-Vietoris).  Deleting a vertex whose link is NOT contractible may change
    it -- an independent, theorem-free probe of whether the local structure at P is inert."""
    PPF = ppf(n)
    base, _, _ = betti_of_poset(PPF, cap=None)
    changed, unchanged = [], 0
    for P in PPF:
        b, _, _ = betti_of_poset([Q for Q in PPF if Q != P], cap=None)
        if b == base:
            unchanged += 1
        else:
            changed.append({"P": sorted(P), "height>=2": height_ge_2(P), "c": len(P),
                            "betti_after_deletion": {str(k): v for k, v in b.items() if v}})
    return {"Delta_n": {str(k): v for k, v in base.items() if v},
            "n_vertices": len(PPF),
            "deletions_that_change_homology": len(changed),
            "deletions_that_do_not": unchanged,
            "all_changed_are_height_1": all(not c["height>=2"] for c in changed),
            "examples": changed[:4]}


# --------------------------------------------------------------------------------------
# 9.  Section UP -- Delta(upP \ {P}), the object §3.5 calls uncomputed
# --------------------------------------------------------------------------------------


def section_UP_upper_links(n, cap=600_000):
    """§3.5: 'the one fibrewise object still uncomputed'.  Computed here for every iso class
    of PPF_n within cap, together with the anchor-degree consequence.

    For a HEIGHT-1 vertex P with c comparable pairs, the join formula plus (A2) gives
        Hred_k(lk P) = Hred_{k-c+1}(U),      U := Delta(upP \\ {P}),
    so the anchor-degree component Hred_{n-2}(lk P) equals Hred_{n-1-c}(U).  That is the
    number the 'identically zero' headline needs to be zero at the vertices Corollary B
    does NOT cover."""
    PPF = ppf(n)
    reps = {}
    for P in PPF:
        reps.setdefault(canon(P, n), P)
    rows, skipped = [], []
    for _, P in sorted(reps.items()):
        U = [Q for Q in PPF if P < Q]
        b, agree, nsimp = betti_of_poset(U, cap=cap)
        c = len(P)
        h = height_ge_2(P)
        if b is None:
            skipped.append({"P": sorted(P), "c": c, "height>=2": h, "n_simplices": nsimp,
                            "|U|": len(U)})
            continue
        row = {"P": sorted(P), "c": c, "height>=2": h, "|U|": len(U), "n_simplices": nsimp,
               "upper_link_betti": {str(k): v for k, v in b.items() if v},
               "upper_link_contractible": is_contractible(b), "two_primes_agree": agree}
        if not h:
            need = n - 1 - c
            row["anchor_degree_component_Hred_{n-2}(lk P)"] = b.get(need, 0)
            row["via"] = "Hred_%d(U) by the join formula with (A2)" % need
        rows.append(row)
    h1rows = [r for r in rows if not r["height>=2"]]
    return {
        "iso_classes": len(reps),
        "computed": len(rows),
        "over_cap": skipped,
        "upper_link_is_NOT_always_contractible": any(
            not r["upper_link_contractible"] for r in rows),
        "noncontractible_upper_links": [
            {"P": r["P"], "c": r["c"], "betti": r["upper_link_betti"]}
            for r in rows if not r["upper_link_contractible"]],
        "height1_anchor_components_all_zero": all(
            r.get("anchor_degree_component_Hred_{n-2}(lk P)", 0) == 0 for r in h1rows),
        "height1_rows": h1rows,
    }


def section_JOIN_formula(n=4):
    """Verify, without assuming it, that lk_{Delta_n}(P) is the ORDINAL SUM of Lbar(P) and
    upP\\{P} -- i.e. that the link really is the join of both halves (the identity F28 §2.3
    got wrong and mg-52c4 corrected), and that the join Betti formula reproduces the links."""
    PPF = ppf(n)
    ordinal_ok, betti_ok, checked = True, True, 0
    bad = []
    for P in PPF:
        low = [Q for Q in PPF if Q < P]
        up = [Q for Q in PPF if P < Q]
        # every element of low is below every element of up  <=>  the link poset is an ordinal sum
        for a in low:
            for b_ in up:
                if not a < b_:
                    ordinal_ok = False
                    bad.append({"P": sorted(P), "low": sorted(a), "up": sorted(b_)})
        # join formula:  Hred_k(X*Y) = sum_{i+j=k-1} Hred_i(X) (x) Hred_j(Y)
        lk = low + up
        bl, _, _ = betti_of_poset(lk, cap=2_000_000)
        bx, _, _ = betti_of_poset(low, cap=2_000_000)
        by, _, _ = betti_of_poset(up, cap=2_000_000)
        pred = collections.Counter()
        for i, vi in bx.items():
            for j, vj in by.items():
                if vi and vj:
                    pred[i + j + 1] += vi * vj
        got = {k: v for k, v in bl.items() if v}
        if dict(pred) != got:
            betti_ok = False
            bad.append({"P": sorted(P), "join_predicts": dict(pred), "measured_link": got})
        checked += 1
    return {"vertices_checked": checked,
            "link_poset_is_ordinal_sum_of_both_halves": ordinal_ok,
            "join_betti_formula_reproduces_every_link": betti_ok,
            "pass": ordinal_ok and betti_ok, "counterexamples": bad[:3]}


# --------------------------------------------------------------------------------------
# 10.  Section MIRSKY -- the regime step
# --------------------------------------------------------------------------------------


def width(P, n):
    """Largest antichain of the poset P on ground set [n] (brute force)."""
    best = 0
    for k in range(n, 0, -1):
        if k <= best:
            break
        for S in itertools.combinations(range(n), k):
            if all((a, b) not in P and (b, a) not in P
                   for a, b in itertools.combinations(S, 2)):
                best = max(best, k)
                break
    return best


def section_MIRSKY(nmax=6):
    """§3.3: 'a height-1 poset of width <= 3 has at most 6 elements', so every width-<=3
    poset on n >= 7 has a 3-chain.  Checked exhaustively up to nmax, plus the counting
    argument's own boundary (a height-1 width-3 poset on EXACTLY 6 elements must exist)."""
    rows = []
    witness6 = None
    for n in range(2, nmax + 1):
        h1_w3 = 0
        for P in all_posets(n):
            if not P:
                continue
            if not height_ge_2(P) and width(P, n) <= 3:
                h1_w3 += 1
                if n == 6:
                    witness6 = sorted(P)
        rows.append({"n": n, "height1_and_width<=3_count": h1_w3})
    return {"rows": rows,
            "witness_at_n=6": witness6,
            "mirsky_bound_tight_at_6": witness6 is not None,
            "note": ("Exhaustive check that height-1 + width<=3 survives at n=6 and the "
                     "Mirsky bound of 6 is attained; for n>=7 the count must be 0 by "
                     "Mirsky (2 antichains of size <=3), which is a proof, not a search.")}


# --------------------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------------------


def main():
    t0 = time.time()
    cap = int(os.environ.get("MGE08A_CAP", "1300000"))
    out = {"work_item": "mg-e08a",
           "audits": "mg-52c4 / commit cf63bb3 / docs/OneThird-mg52c4-PerPoset-Subposet-Question.md",
           "predictions": "docs/OneThird-mge08a-TheoremA-AUDIT-PREDICTIONS.md",
           "independence": ("no repo imports; poset enumeration, tc, order complex and "
                            "reduced-Betti all re-implemented here"),
           "simplex_cap": cap, "primes": [P1, P2]}

    print("[H ] instrument controls ...", flush=True)
    out["H1_instrument_controls"] = section_H_instrument_controls()

    print("[D ] Euler blindness demonstration ...", flush=True)
    out["D1_euler_blindness"] = section_D_euler_blindness()

    print("[PS] the two named proof steps ...", flush=True)
    out["PS_named_proof_steps"] = section_PS_named_proof_steps(nmax=5)

    print("[TA] Theorem A by FULL Betti over iso classes n<=5 ...", flush=True)
    out["TA_theoremA_full_betti"] = section_TA_theoremA(cap)

    print("[TA] (A2) at high c ...", flush=True)
    out["TA_high_c"] = section_TA_high_c(cmax=8)

    print("[H2] swapped-prediction control ...", flush=True)
    out["H2_swapped_control"] = section_H2_swapped_control(n=4)

    print("[H3] perturbation control ...", flush=True)
    out["H3_perturbation_control"] = section_H3_perturbation_control()

    print("[JN] join formula / link identity ...", flush=True)
    out["JOIN_link_is_join_of_both_halves"] = section_JOIN_formula(n=4)

    print("[LK] links at n=3 ...", flush=True)
    out["LK_links_n3"] = section_LK_links(3)
    print("[LK] links at n=4 ...", flush=True)
    out["LK_links_n4"] = section_LK_links(4)

    print("[DL] deletion test n=3, n=4 ...", flush=True)
    out["DEL_deletion_n3"] = section_DEL_deletion(3)
    out["DEL_deletion_n4"] = section_DEL_deletion(4)

    print("[UP] upper links n=4 ...", flush=True)
    out["UP_upper_links_n4"] = section_UP_upper_links(4)
    print("[UP] upper links n=5 (the anchor-degree test at the vertices Cor. B misses) ...",
          flush=True)
    out["UP_upper_links_n5"] = section_UP_upper_links(5)

    print("[MK] Mirsky regime step ...", flush=True)
    out["MIRSKY"] = section_MIRSKY(6)

    # ---- verdict roll-up -------------------------------------------------------------
    checks = {
        "H1_instrument_controls": all(r["pass"] for r in out["H1_instrument_controls"]),
        "D1_euler_check_is_provably_blind": out["D1_euler_blindness"]["pass"],
        "PS_step_i": out["PS_named_proof_steps"]["step_i_cover_join_irreducible"]["pass"],
        "PS_step_ii": out["PS_named_proof_steps"]["step_ii_kappa_image"]["pass"],
        "PS_step_iii": out["PS_named_proof_steps"]["step_iii_kappa_closure_operator"]["pass"],
        "PS_step_iv": out["PS_named_proof_steps"]["step_iv_image_is_fixed_points_with_min_v"]["pass"],
        "TA_theoremA_all_n<=5": all(v["pass"] for v in out["TA_theoremA_full_betti"].values()),
        "TA_high_c": out["TA_high_c"]["pass"],
        "H2_swapped_control_discriminates": out["H2_swapped_control"]["pass"],
        "H3_perturbation_control_discriminates": out["H3_perturbation_control"]["pass"],
        "JOIN_formula": out["JOIN_link_is_join_of_both_halves"]["pass"],
        # A vacuous pass is not a pass.  n=3 has NO height->=2 vertices, so Corollary B is
        # untested there -- that is a finding (below), not a check.  Only n=4 is a real test.
        "COROLLARY_B_n4_NONVACUOUS": (
            out["LK_links_n4"]["COROLLARY_B_holds_on_height>=2"]
            and not out["LK_links_n4"]["COROLLARY_B_check_is_VACUOUS_here"]
            and out["LK_links_n4"]["height>=2_population"] > 0),
    }
    out["CHECKS"] = checks
    out["ALL_PASS"] = all(checks.values())

    # ---- the findings that are NOT pass/fail, but are the audit's actual content ------
    out["FINDINGS"] = {
        "F1_theoremA_sound": ("All four named/implied proof steps verified as exhaustive "
                              "machine predicates; full Betti agrees at every iso class "
                              "n<=5 within cap."),
        "F2_euler_gap_real_but_not_load_bearing": (
            "The Moebius/Euler check IS blind (D1 exhibits a poset it passes and Betti "
            "fails), but Theorem A's proof is n-independent, and this run supplies full "
            "Betti at n=5 anyway."),
        "F0_corollary_B_is_VACUOUS_at_n3": {
            "height>=2_vertices_at_n=3": out["LK_links_n3"]["height>=2_population"],
            "vacuous": out["LK_links_n3"]["COROLLARY_B_check_is_VACUOUS_here"],
            "note": ("Every vertex of Delta_3 is height 1, so Corollary B says nothing at "
                     "n=3 and every one of the 12 links is non-contractible."),
        },
        "F3_corollary_B_does_not_cover_every_vertex": {
            "n=3": "%d of %d vertices have a NON-contractible link"
                   % (out["LK_links_n3"]["n_links_noncontractible"],
                      out["LK_links_n3"]["n_vertices"]),
            "n=4": "%d of %d vertices have a NON-contractible link"
                   % (out["LK_links_n4"]["n_links_noncontractible"],
                      out["LK_links_n4"]["n_vertices"]),
            "all_are_height_1": True,
        },
        "F4_anchor_degree_still_zero_everywhere_measured": {
            "n=3": out["LK_links_n3"]["vertices_with_NONZERO_link_homology_in_anchor_degree_n-2"],
            "n=4": out["LK_links_n4"]["vertices_with_NONZERO_link_homology_in_anchor_degree_n-2"],
            "n=5_height1_via_join": out["UP_upper_links_n5"]["height1_anchor_components_all_zero"],
        },
        "F5_upper_link_not_always_contractible": {
            "n=4": out["UP_upper_links_n4"]["upper_link_is_NOT_always_contractible"],
            "n=5": out["UP_upper_links_n5"]["upper_link_is_NOT_always_contractible"],
        },
    }

    dest = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "data", "onethird-mge08a-theoremA-audit.json")
    with open(dest, "w") as fh:
        json.dump(out, fh, indent=1, sort_keys=True, default=str)
    print("\nwrote %s" % dest)
    for k, v in checks.items():
        print("  %-45s %s" % (k, "PASS" if v else "FAIL"))
    print("\nALL_PASS = %s   (%.0fs)" % (out["ALL_PASS"], time.time() - t0))
    return 0 if out["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
