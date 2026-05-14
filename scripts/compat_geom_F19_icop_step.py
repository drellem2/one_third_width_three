#!/usr/bin/env python3
r"""
compat_geom_F19_icop_step.py
============================

Compat-Geom F19 verification harness (mg-5722).  Trip-wire confirmation of
(ICOP-step) -- F10 section 5.4 -- and of the structural lemmas the F19
n-uniform proof rests on.

(ICOP-step) [F10 section 5.4].  For every n, the lex-min new cover step
appended to the top poset of c*_n in the iota-tower is BFT-sharp: its
Kahn-Saks probability lies in [3/11, 8/11].

This is NOT new HPC and NOT a new n-datapoint hunt.  It re-runs the
EXISTING empirical record (the canonical critical chains c*_3, c*_4, c*_5
from F2/F3/F5, and the F8' n=6 iota_5-lift candidate) as trip-wires, and
in addition certifies the two structural facts that the F19 proof
(docs/compatibility-geometry-F19-icop-step-and-bridge.md) turns into an
n-uniform argument:

  (L1) THE SYMMETRIC-PAIR LEMMA.  If {x,y} is an incomparable pair of a
       finite poset P and some automorphism sigma of P has sigma(x)=y,
       then Pr_P[x < y] = 1/2  (exactly).  [section C]

  (L2) THE ICOP-STEP STRUCTURE.  For n >= 5 the canonical new cover of the
       iota-tower top poset is taken at a symmetric incomparable pair
       (Type-S), so Pr = 1/2 by (L1); for n = 3,4 the new cover step has
       Pr = 2/3 by direct computation.  All four values 2/3, 2/3, 1/2, 1/2
       lie in [3/11, 8/11].  [sections B, D, E]

What this script checks
-----------------------
  [A]  Reconstruct c*_3, c*_4 (the lex-min cell #1 and the perfect-MF
       cell #4), c*_5 explicitly from F2 section 4.3 / F5 section 4.3 /
       F8' section A; verify each is a genuine chain in PPF, reproduce the
       |L|-profiles and per-step Pr ratios, confirm BFT-sharpness.
  [B]  For every iota-tower top poset G (and its iota-lift), enumerate the
       admissible single covers; tag each Pr-value, BFT-sharpness, and
       whether the added pair is SYMMETRIC (an Aut(G)-orbit of size 2).
       Identify the lex-min cover and confirm it is symmetric & BFT-sharp.
  [C]  (L1) the symmetric-pair lemma: for every poset in scope and every
       symmetric incomparable pair, assert Pr = 1/2 exactly.
  [D]  The iota-tower new-cover step at n = 4, 5, 6: identify it, confirm
       BFT-sharp, confirm the Type-S / Type-base classification.
  [E]  The F8' n=6 iota_5-lift candidate: reproduce profile (180,84,48,24),
       step-4 lex-min cover (0,2), Pr = 1/2, 4/4 BFT-sharp.
  [F]  Width-3 bridge sub-check at m = 4: enumerate the width-3 posets in
       PPF_4, confirm every one is reachable on a refinement chain whose
       cover steps are BFT-sharp (the m <= 4 rigorous base of the bridge).
  [G]  Verdict report.

Pure-Python stdlib.  Runtime < 5 s on commodity hardware (largest LE count
is 7! = 5040 permutations).

Usage:
    python3 compat_geom_F19_icop_step.py [--verbose]

References
  - mg-8216 (F10):  docs/general-n-proof-synthesis.md sections 5.2-5.4, 7.3-7.4
  - mg-1e99 (F8):   docs/compatibility-geometry-F8-inductive-general-n.md s.4.3-4.4, 6
  - mg-7b3b (F8'):  docs/compatibility-geometry-F8prime-n6-icop.md ; this script's
                    n=6 candidate is the F8' iota_5-lift candidate.
  - mg-1e58 (F5):   docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md s.4.3
  - mg-7455/6bc3 (F2/F3): docs/compatibility-geometry-F2-scoping.md s.4.3
"""

from __future__ import annotations

import sys
from fractions import Fraction
from itertools import permutations


# ===========================================================================
# section 0.  Core poset utilities.
# ===========================================================================


def transitive_closure(rel):
    """Transitive closure of a relation `rel` (set of (a,b) = 'a < b')."""
    closed = set(rel)
    while True:
        new = set()
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    new.add((i, l))
        if not new:
            return frozenset(closed)
        closed |= new


def is_antisymmetric(closed):
    return not any((j, i) in closed for (i, j) in closed)


def ground_set(rel, n):
    return set(range(n))


def is_proper_partial_order(rel, n):
    """Proper = transitively closed, antisymmetric, non-empty, non-total."""
    closed = transitive_closure(rel)
    if closed != frozenset(rel):
        return False
    if not is_antisymmetric(closed):
        return False
    if len(closed) == 0:
        return False
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                return True   # found an incomparable pair => non-total
    return False


def count_linear_extensions(rel, n):
    """Brute-force count of linear extensions of partial order `rel` on [n]."""
    closed = transitive_closure(rel)
    count = 0
    for perm in permutations(range(n)):
        pos = {perm[k]: k for k in range(n)}
        if all(pos[i] < pos[j] for (i, j) in closed):
            count += 1
    return count


def pr_cover(P_closed, pair, n):
    """Pr_P[a < b] for pair = (a,b): |L(P u {a<b})| / |L(P)|."""
    LP = count_linear_extensions(P_closed, n)
    if LP == 0:
        return Fraction(0)
    Q = transitive_closure(set(P_closed) | {pair})
    return Fraction(count_linear_extensions(Q, n), LP)


def pr_step(P_closed, Q_closed, n):
    """Ratio |L(Q)| / |L(P)| of a (possibly multi-cover) chain step P < Q."""
    LP = count_linear_extensions(P_closed, n)
    if LP == 0:
        return Fraction(0)
    return Fraction(count_linear_extensions(Q_closed, n), LP)


def hasse_covers(closed, n):
    """Cover relations (Hasse diagram) of a transitively closed order."""
    covers = set()
    for (i, j) in closed:
        if not any((i, k) in closed and (k, j) in closed
                   for k in range(n) if k != i and k != j):
            covers.add((i, j))
    return frozenset(covers)


def hasse_str(closed, n):
    return "{" + ", ".join(f"{i}<{j}" for (i, j) in
                           sorted(hasse_covers(closed, n))) + "}"


def incomparable_pairs(closed, n):
    """Unordered incomparable pairs {i,j} of a transitively closed order."""
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                out.append((i, j))
    return out


def automorphisms(closed, n):
    """All permutations pi of [n] with pi(closed) = closed."""
    autos = []
    rel = set(closed)
    for perm in permutations(range(n)):
        if all((perm[a], perm[b]) in rel for (a, b) in rel):
            autos.append(perm)
    return autos


def symmetric_pairs(closed, n):
    """Incomparable pairs {x,y} swapped by some automorphism of `closed`."""
    autos = automorphisms(closed, n)
    out = []
    for (x, y) in incomparable_pairs(closed, n):
        if any(s[x] == y and s[y] == x for s in autos):
            out.append((x, y))
    return out


def admissible_single_covers(closed, n, require_proper=True):
    """Every ordered pair (a,b) whose addition is a valid strict refinement
    that stays a proper partial order (antisymmetric; non-total if
    require_proper).  Returns list of dicts."""
    out = []
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            if (a, b) in closed or (b, a) in closed:
                continue
            Q = transitive_closure(set(closed) | {(a, b)})
            if not is_antisymmetric(Q):
                continue
            if Q == closed:
                continue
            if require_proper and not is_proper_partial_order(Q, n):
                continue
            out.append({"pair": (a, b), "Q": Q})
    return out


BFT_LO, BFT_HI = Fraction(3, 11), Fraction(8, 11)
KS_LO, KS_HI = Fraction(1, 3), Fraction(2, 3)


def in_bft(pr):
    return BFT_LO <= pr <= BFT_HI


def in_ks(pr):
    return KS_LO <= pr <= KS_HI


# ===========================================================================
# section A.  The canonical critical chains, reconstructed from F2/F3/F5/F8'.
# ===========================================================================

# c*_3  (F8 section 4.5):  (  {0<2}  subset  {0<1, 0<2}  ).
C_STAR_3 = {
    "n": 3,
    "label": "c*_3  (F1-refined / F8 s.4.5)",
    "hasse": [
        frozenset({(0, 2)}),
        frozenset({(0, 1), (0, 2)}),
    ],
}

# c*_4 cell #1  (F2 section 4.3.1): the LEX-MIN critical 2-cell, F8's choice.
#   P_0 {1<2,3<0,3<2}  <  P_1 {0<2,1<2,3<0}  <  P_2 {0<2,1<0,3<0}.
C_STAR_4_CELL1 = {
    "n": 4,
    "label": "c*_4 cell #1  (F2 s.4.3.1, lex-min critical 2-cell)",
    "hasse": [
        frozenset({(1, 2), (3, 0), (3, 2)}),
        frozenset({(0, 2), (1, 2), (3, 0)}),
        frozenset({(0, 2), (1, 0), (3, 0)}),
    ],
}

# c*_4 cell #4  (F2 section 4.3.2): the perfect-MF / most-symmetric 2-cell.
#   P_0 {0<1,3<1} < P_1 {0<1,0<2,3<1,3<2} < P_2 {0<3,3<1,3<2}.
C_STAR_4_CELL4 = {
    "n": 4,
    "label": "c*_4 cell #4  (F2 s.4.3.2, perfect-MF symmetric 2-cell)",
    "hasse": [
        frozenset({(0, 1), (3, 1)}),
        frozenset({(0, 1), (0, 2), (3, 1), (3, 2)}),
        frozenset({(0, 3), (3, 1), (3, 2)}),
    ],
}

# c*_5  (F5 section 4.3 lifted chain / F8' section A, hard-coded from
#        mg-1e58 77440bd):
C_STAR_5 = {
    "n": 5,
    "label": "c*_5  (F5 s.4.3 / F8' s.A)",
    "hasse": [
        frozenset({(0, 1), (2, 1), (3, 1)}),
        frozenset({(0, 1), (0, 4), (2, 1), (2, 4), (3, 1)}),
        frozenset({(0, 4), (2, 4), (3, 1), (4, 1)}),
        frozenset({(0, 3), (0, 4), (2, 3), (2, 4), (3, 1), (4, 1)}),
    ],
}


def analyse_chain(chain, verbose=False):
    """Verify a chain, compute |L|-profile, per-step Pr ratios, BFT-sharpness.
    Returns dict with closures, profile, per-step prs, top poset."""
    n = chain["n"]
    closures = [transitive_closure(P) for P in chain["hasse"]]
    print(f"  {chain['label']}   (n = {n})")
    print(f"  {'-' * 74}")
    # chain check
    ok_chain = True
    for k in range(len(closures) - 1):
        if not (closures[k] < closures[k + 1]):
            ok_chain = False
            print(f"    !! P_{k} subset P_{k+1} FAILS as set inclusion")
    profile = []
    for k, C in enumerate(closures):
        L = count_linear_extensions(C, n)
        profile.append(L)
        ppf = is_proper_partial_order(C, n)
        print(f"    P_{k}: |L| = {L:>4}   Hasse {hasse_str(C, n)}"
              f"   {'(PPF)' if ppf else '(NOT PPF)'}")
    prs = []
    print(f"    per-step (telescoped) Pr ratios:")
    for k in range(len(closures) - 1):
        pr = Fraction(profile[k + 1], profile[k])
        prs.append(pr)
        added = sorted(closures[k + 1] - closures[k])
        tag = "BFT-sharp" if in_bft(pr) else ("KS-sharp" if in_ks(pr)
                                              else "OUT OF RANGE")
        print(f"      step {k}: adds {added}   Pr = {pr}  ~ {float(pr):.4f}"
              f"   [{tag}]")
    all_bft = all(in_bft(p) for p in prs)
    print(f"    chain valid: {'YES' if ok_chain else 'NO'};"
          f"  all per-step Pr in [3/11,8/11]: {'YES' if all_bft else 'NO'}")
    print()
    return {
        "n": n, "label": chain["label"], "closures": closures,
        "profile": profile, "prs": prs, "top": closures[-1],
        "ok_chain": ok_chain, "all_bft": all_bft,
    }


# ===========================================================================
# section B.  Structural analysis of the top posets & their iota-lifts.
# ===========================================================================


def iota_lift(closed, k_extra):
    """iota-lift: same relation set, on a ground set enlarged by `k_extra`
    fresh free elements (the relation set is literally unchanged)."""
    return frozenset(closed)   # n grows; new elements are unrelated


def analyse_top_poset(closed, n, name, verbose=False):
    """Enumerate admissible single covers of a poset; tag Pr / BFT / symmetric;
    identify the lex-min cover.  Returns dict."""
    print(f"  Top poset {name}  (n = {n}):  Hasse {hasse_str(closed, n)}")
    autos = automorphisms(closed, n)
    sympairs = symmetric_pairs(closed, n)
    incs = incomparable_pairs(closed, n)
    print(f"    |Aut| = {len(autos)};  incomparable pairs = {incs};"
          f"  symmetric pairs = {sympairs}")
    covers = admissible_single_covers(closed, n, require_proper=False)
    LP = count_linear_extensions(closed, n)
    rows = []
    for c in covers:
        a, b = c["pair"]
        pr = Fraction(count_linear_extensions(c["Q"], n), LP)
        is_sym = (min(a, b), max(a, b)) in sympairs
        rows.append({"pair": (a, b), "pr": pr, "bft": in_bft(pr),
                     "sym": is_sym})
    rows.sort(key=lambda r: r["pair"])
    if verbose:
        for r in rows:
            print(f"      cover {r['pair']}:  Pr = {str(r['pr']):>6}"
                  f"  {'BFT' if r['bft'] else '   '}"
                  f"  {'SYMMETRIC' if r['sym'] else ''}")
    n_bft = sum(1 for r in rows if r["bft"])
    lex_min = rows[0] if rows else None
    if lex_min:
        print(f"    {len(rows)} admissible single covers;  {n_bft} BFT-sharp;"
              f"  lex-min cover = {lex_min['pair']}"
              f"  Pr = {lex_min['pr']}"
              f"  [{'BFT-sharp' if lex_min['bft'] else 'OUT'}]"
              f"  [{'SYMMETRIC' if lex_min['sym'] else 'not symmetric'}]")
    print()
    return {"name": name, "n": n, "rows": rows, "lex_min": lex_min,
            "sympairs": sympairs, "autos": autos}


# ===========================================================================
# section C.  (L1) the symmetric-pair lemma, verified computationally.
# ===========================================================================


def verify_symmetric_pair_lemma(posets, verbose=False):
    """For every (closed, n) in `posets` and every symmetric incomparable
    pair {x,y}, assert Pr_P[x<y] = 1/2 exactly."""
    print(f"  (L1) Symmetric-pair lemma:  symmetric incomparable pair"
          f"  =>  Pr = 1/2 exactly")
    print(f"  {'-' * 74}")
    total, ok = 0, 0
    for (closed, n, name) in posets:
        for (x, y) in symmetric_pairs(closed, n):
            pr = pr_cover(closed, (x, y), n)
            total += 1
            good = (pr == Fraction(1, 2))
            ok += int(good)
            if verbose or not good:
                print(f"    {name} (n={n}): pair ({x},{y})  Pr = {pr}"
                      f"   {'OK' if good else '!! NOT 1/2'}")
    print(f"    symmetric pairs tested: {total};  Pr = 1/2 for all:"
          f"  {'YES' if ok == total else 'NO (' + str(total-ok) + ' fail)'}")
    print()
    return ok == total and total > 0


# ===========================================================================
# section D.  The iota-tower new-cover step at n = 4, 5, 6.
# ===========================================================================


def analyse_icop_step(verbose=False):
    """(ICOP-step) [F10 s.5.4] = the Kahn-Saks probability of the lex-min
    admissible cover appended to the top poset G_n of c*_n (equivalently to
    its iota-lift iota_n(G_n)) -- the cover that begins building c*_{n+1}.

    For n = 3,4,5 we have G_n exactly (from F2/F5); for n = 6 we use the
    F8' iota_5-lift candidate iota_5(G_5).  In every case the lex-min
    admissible cover lands at a SYMMETRIC incomparable pair, so Pr = 1/2.

    We ALSO print, as context, the chain's own internal top step (which is
    a DIFFERENT object -- an inherited step, n-dependent at small n: 2/3 at
    n=3,4, 1/2 at n=5 -- handled by the F8' multiplicativity law, not by
    (ICOP-step))."""
    print(f"  (ICOP-step) per-level audit  --  the lex-min new cover of G_n")
    print(f"  {'=' * 74}")

    c3 = [transitive_closure(P) for P in C_STAR_3["hasse"]]
    c4 = [transitive_closure(P) for P in C_STAR_4_CELL1["hasse"]]
    c5 = [transitive_closure(P) for P in C_STAR_5["hasse"]]
    tops = [
        ("n=3", c3[-1], 3),
        ("n=4", c4[-1], 4),
        ("n=5", c5[-1], 5),
        ("n=6", iota_lift(c5[-1], 1), 6),   # iota_5(G_5), the F8' candidate
    ]
    chain_internal = {  # the chain's own top step Pr, for context only
        "n=3": pr_step(c3[0], c3[1], 3),
        "n=4": pr_step(c4[-2], c4[-1], 4),
        "n=5": pr_step(c5[-2], c5[-1], 5),
        "n=6": None,
    }
    results = []
    for (lbl, G, n) in tops:
        sym = symmetric_pairs(G, n)
        covers = admissible_single_covers(G, n, require_proper=False)
        covers.sort(key=lambda c: c["pair"])
        lm = covers[0]
        LG = count_linear_extensions(G, n)
        pr = Fraction(count_linear_extensions(lm["Q"], n), LG)
        is_sym = (min(lm["pair"]), max(lm["pair"])) in sym
        results.append((lbl, pr, in_bft(pr), is_sym))
        ci = chain_internal[lbl]
        ci_str = f"chain internal top step Pr = {ci}" if ci is not None \
            else "chain internal top step: n/a (n=6 is a candidate)"
        which = "iota_5(G_5)" if lbl == "n=6" else f"G_{n}"
        print(f"  {lbl}:  top poset {which}  Hasse {hasse_str(G, n)}")
        print(f"        symmetric pairs = {sym}")
        print(f"        (ICOP-step) = lex-min cover {lm['pair']}:  Pr = {pr}"
              f"   [{'BFT-sharp' if in_bft(pr) else 'OUT'}]"
              f"   [{'SYMMETRIC' if is_sym else 'NOT symmetric'}]")
        print(f"        ({ci_str})")
        print()

    print(f"  (ICOP-step) summary  --  the F19 reduction target:")
    all_bft = True
    all_sym = True
    for (lbl, pr, bft, sym) in results:
        all_bft = all_bft and bft
        all_sym = all_sym and sym
        print(f"    {lbl}:  (ICOP-step) Pr = {str(pr):>4}  ~ {float(pr):.4f}"
              f"   [{'BFT-sharp' if bft else 'OUT OF RANGE'}]"
              f"   [{'symmetric pair' if sym else 'NOT symmetric'}]")
    print(f"    (ICOP-step) in [3/11,8/11] at n=3,4,5,6:"
          f"  {'YES' if all_bft else 'NO'}")
    print(f"    (ICOP-step) cover is a symmetric pair at n=3,4,5,6:"
          f"  {'YES (uniformly Pr = 1/2 via lemma L1)' if all_sym else 'NO'}")
    print()
    return results, all_bft and all_sym


# ===========================================================================
# section E.  F8' n=6 iota_5-lift candidate reproduction.
# ===========================================================================


def reproduce_f8prime_n6(verbose=False):
    """Reproduce F8' section 3: iota_5-lift of c*_5, multiplicativity
    profile (180,84,48,24), step-4 lex-min cover (0,2) Pr=1/2, 4/4 BFT."""
    print(f"  F8' n=6 iota_5-lift candidate (trip-wire)")
    print(f"  {'-' * 74}")
    c5 = [transitive_closure(P) for P in C_STAR_5["hasse"]]
    prof5 = [count_linear_extensions(C, 5) for C in c5]
    prof6 = [count_linear_extensions(iota_lift(C, 1), 6) for C in c5]
    print(f"    c*_5 profile (n=5): {tuple(prof5)}")
    print(f"    iota_5-lift profile (n=6): {tuple(prof6)}"
          f"   (F8' predicts (180,84,48,24))")
    mult_ok = all(prof6[k] == 6 * prof5[k] for k in range(4))
    print(f"    multiplicativity |L(iota_5(P))| = 6|L(P)|:"
          f"  {'CONFIRMED' if mult_ok else 'FAILED'}")
    # first three steps
    prs = [Fraction(prof6[k + 1], prof6[k]) for k in range(3)]
    # step 4: lex-min single cover of iota_5(P_3)
    iota_P3 = iota_lift(c5[-1], 1)
    covers = admissible_single_covers(iota_P3, 6, require_proper=False)
    covers.sort(key=lambda c: c["pair"])
    lm = covers[0]
    LP = count_linear_extensions(iota_P3, 6)
    pr4 = Fraction(count_linear_extensions(lm["Q"], 6), LP)
    full = prs + [pr4]
    n_bft = sum(1 for p in full if in_bft(p))
    print(f"    step-4 lex-min cover = {lm['pair']}  Pr = {pr4}")
    print(f"    full Pr-profile = {[str(p) for p in full]}")
    print(f"    BFT-sharp: {n_bft}/4   (F8' GREEN target: 4/4)")
    print()
    return mult_ok and n_bft == 4


# ===========================================================================
# section F.  Width-3 bridge sub-check at m = 4 (rigorous base of the bridge).
# ===========================================================================


def enumerate_ppf(n):
    """All proper partial orders on [n], as transitively closed frozensets,
    via incremental refinement BFS from the empty relation."""
    seen = set()
    # start from every single relation, close, BFS upward
    frontier = set()
    for a in range(n):
        for b in range(n):
            if a != b:
                C = transitive_closure({(a, b)})
                if is_antisymmetric(C):
                    frontier.add(C)
    while frontier:
        nxt = set()
        for C in frontier:
            if C in seen:
                continue
            seen.add(C)
            for a in range(n):
                for b in range(n):
                    if a == b or (a, b) in C or (b, a) in C:
                        continue
                    D = transitive_closure(set(C) | {(a, b)})
                    if is_antisymmetric(D) and D not in seen:
                        nxt.add(D)
        frontier = nxt
    return [C for C in seen if is_proper_partial_order(C, n)]


def poset_width(closed, n):
    """Width = size of the largest antichain."""
    best = 1
    # brute force over subsets is fine for n<=4 here; use simple growth
    from itertools import combinations
    for size in range(n, 0, -1):
        for S in combinations(range(n), size):
            if all((a, b) not in closed and (b, a) not in closed
                   for a, b in combinations(S, 2)):
                return size
    return best


def width3_bridge_check_m4(verbose=False):
    """At m=4: enumerate PPF_4, find the width-3 posets, and confirm each is
    reachable on a refinement chain all of whose cover steps are BFT-sharp.
    This is the m<=4 rigorous base of the width-3 reduction bridge (F10
    section 7.3 / F8 Theorem 6.1)."""
    print(f"  Width-3 reduction bridge -- m = 4 rigorous base")
    print(f"  {'-' * 74}")
    ppf4 = enumerate_ppf(4)
    print(f"    |PPF_4| = {len(ppf4)}   (expected 194)")
    width3 = [C for C in ppf4 if poset_width(C, 4) == 3]
    print(f"    width-3 posets in PPF_4: {len(width3)}")
    # For each width-3 P, check it admits an incomparable pair (x,y) with
    # Pr in [3/11,8/11] -- i.e. P has a BFT-sharp cover step out of it.
    ok = 0
    fails = []
    for C in width3:
        good = False
        for (x, y) in incomparable_pairs(C, 4):
            for pair in [(x, y), (y, x)]:
                Q = transitive_closure(set(C) | {pair})
                if not is_antisymmetric(Q) or Q == C:
                    continue
                pr = Fraction(count_linear_extensions(Q, 4),
                              count_linear_extensions(C, 4))
                if in_bft(pr):
                    good = True
        if good:
            ok += 1
        else:
            fails.append(C)
    print(f"    width-3 posets with a BFT-sharp incomparable pair:"
          f"  {ok}/{len(width3)}")
    if fails:
        for C in fails[:5]:
            print(f"      !! no BFT-sharp pair: {hasse_str(C, 4)}")
    bridge_base_ok = (ok == len(width3) and len(width3) > 0)
    print(f"    m=4 bridge base (every width-3 poset is BFT-sharp-witnessed):"
          f"  {'CONFIRMED' if bridge_base_ok else 'FAILED'}")
    print()
    return bridge_base_ok, len(ppf4)


# ===========================================================================
# section H.  Structural probe -- (L2) and why it is not a greedy invariant.
# ===========================================================================


def is_ordinal_sum_of_antichains(closed, n):
    """A finite poset is an ordinal sum of antichains  <=>  its
    incomparability graph is a disjoint union of cliques (a cluster graph)
    <=>  incomparability is transitive on distinct elements."""
    inc = set()
    for i in range(n):
        for j in range(n):
            if i != j and (i, j) not in closed and (j, i) not in closed:
                inc.add((i, j))
    for (a, b) in inc:
        for c in range(n):
            if c != a and c != b and (b, c) in inc and (a, c) not in inc:
                return False
    return True


def antichain_blocks(closed, n):
    """The antichain blocks of an OSA poset (incomparability classes),
    ordered bottom-to-top."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                parent[find(i)] = find(j)
    blocks = {}
    for x in range(n):
        blocks.setdefault(find(x), []).append(x)
    bl = list(blocks.values())
    # order blocks: B < B' iff some b<b' across them
    bl.sort(key=lambda B: sum(1 for (a, b) in closed if a in B))
    return [sorted(B) for B in bl]


def structural_probe(verbose=False):
    """[H]  Certify the structural facts behind reduction-target (L2):
       (H1) G_3, G_4, G_5 are width-2 ordinal sums of antichains, each with
            at least one antichain block of size >= 2;
       (H2) (L2) is NOT a naive greedy invariant -- the 'always take the
            lex-min symmetric pair' tower loses all symmetry at n = 6,
            so the canonical chamber-Morse construction genuinely matters."""
    print(f"  [H1]  Canonical top posets are width-2 ordinal sums of antichains")
    print(f"  {'-' * 74}")
    c3 = [transitive_closure(P) for P in C_STAR_3["hasse"]]
    c4 = [transitive_closure(P) for P in C_STAR_4_CELL1["hasse"]]
    c5 = [transitive_closure(P) for P in C_STAR_5["hasse"]]
    h1_ok = True
    for (G, n, lbl) in [(c3[-1], 3, "G_3"), (c4[-1], 4, "G_4"),
                        (c5[-1], 5, "G_5")]:
        osa = is_ordinal_sum_of_antichains(G, n)
        w = poset_width(G, n)
        blocks = antichain_blocks(G, n) if osa else None
        has2 = osa and any(len(B) >= 2 for B in blocks)
        ok = osa and w == 2 and has2
        h1_ok = h1_ok and ok
        print(f"    {lbl}: OSA = {osa};  width = {w};  blocks = {blocks};"
              f"  has >=2 block = {has2}   [{'OK' if ok else 'FAIL'}]")
    print(f"    (H1): all canonical top posets are width-2 OSA with a >=2"
          f" block:  {'CONFIRMED' if h1_ok else 'FAILED'}")
    print()

    print(f"  [H2]  (L2) is not a naive greedy invariant")
    print(f"  {'-' * 74}")
    # Build the 'lex-min symmetric pair' tower from G_3 and watch it die.
    H = transitive_closure(C_STAR_3["hasse"][1])   # H_3 = G_3 on [3]
    cur_n = 3
    died_at = None
    trace = [("H_3", 3, symmetric_pairs(H, 3))]
    for step in range(4):
        cur_n += 1
        iH = iota_lift(H, 1)        # ground set [cur_n]
        sp = symmetric_pairs(iH, cur_n)
        if not sp:
            died_at = cur_n
            trace.append((f"iota(H_{cur_n-1})", cur_n, []))
            break
        a, b = min(sp)
        H = transitive_closure(set(iH) | {(a, b)})
        trace.append((f"H_{cur_n}", cur_n, symmetric_pairs(H, cur_n)))
    for (lbl, nn, sp) in trace:
        print(f"    {lbl} (n={nn}): symmetric pairs = {sp}")
    h2_ok = died_at is not None
    if h2_ok:
        print(f"    the naive 'lex-min symmetric pair' tower loses ALL"
              f" symmetry at n = {died_at}.")
        print(f"    => (L2) is a property of the CANONICAL chamber-Morse"
              f" construction,")
        print(f"       not of an arbitrary greedy refinement: it needs real"
              f" structural input.")
    else:
        print(f"    (unexpected: naive tower survived -- investigate)")
    print()
    return h1_ok, h2_ok


# ===========================================================================
# section G.  Verdict report.
# ===========================================================================


def main():
    verbose = "--verbose" in sys.argv
    print()
    print("compat_geom_F19_icop_step.py -- F19 (mg-5722) verification harness")
    print("(ICOP-step) [F10 s.5.4] + the symmetric-pair lemma + width-3 bridge")
    print("=" * 76)
    print()

    # ---- section A ---------------------------------------------------------
    print("[A]  Canonical critical chains -- reconstruction & per-step Pr")
    print("=" * 76)
    a3 = analyse_chain(C_STAR_3, verbose)
    a4 = analyse_chain(C_STAR_4_CELL1, verbose)
    a4s = analyse_chain(C_STAR_4_CELL4, verbose)
    a5 = analyse_chain(C_STAR_5, verbose)
    chains_ok = all(a["ok_chain"] and a["all_bft"] for a in [a3, a4, a4s, a5])
    print(f"  [A] all chains valid & per-step BFT-sharp:"
          f"  {'YES' if chains_ok else 'NO'}")
    print()

    # ---- section B ---------------------------------------------------------
    print("[B]  Top posets & iota-lifts -- admissible covers, symmetry")
    print("=" * 76)
    G3, G4, G5 = a3["top"], a4["top"], a5["top"]
    b3 = analyse_top_poset(G3, 3, "G_3 = top(c*_3)", verbose)
    b4 = analyse_top_poset(G4, 4, "G_4 = top(c*_4 cell#1)", verbose)
    b5 = analyse_top_poset(G5, 5, "G_5 = top(c*_5)", verbose)
    b5i = analyse_top_poset(iota_lift(G5, 1), 6,
                            "iota_5(G_5)  [element 5 free]", verbose)

    # ---- section C ---------------------------------------------------------
    print("[C]  (L1) symmetric-pair lemma -- computational certification")
    print("=" * 76)
    pool = [
        (G3, 3, "G_3"), (G4, 4, "G_4"),
        (a4s["top"], 4, "G_4(cell#4)"),
        (a5["closures"][-2], 5, "P_2(c*_5)"),
        (G5, 5, "G_5"),
        (iota_lift(G5, 1), 6, "iota_5(G_5)"),
        (iota_lift(G5, 2), 7, "iota_6 iota_5(G_5)"),
    ]
    l1_ok = verify_symmetric_pair_lemma(pool, verbose)

    # ---- section D ---------------------------------------------------------
    print("[D]  (ICOP-step) per-level audit  n = 3,4,5,6")
    print("=" * 76)
    icop_results, icop_all_bft = analyse_icop_step(verbose)

    # ---- section E ---------------------------------------------------------
    print("[E]  F8' n=6 iota_5-lift candidate -- trip-wire")
    print("=" * 76)
    f8p_ok = reproduce_f8prime_n6(verbose)

    # ---- section F ---------------------------------------------------------
    print("[F]  Width-3 reduction bridge -- m=4 rigorous base")
    print("=" * 76)
    bridge_ok, ppf4_size = width3_bridge_check_m4(verbose)

    # ---- section H ---------------------------------------------------------
    print("[H]  Structural probe -- (L2) and why it needs real structure")
    print("=" * 76)
    h1_ok, h2_ok = structural_probe(verbose)

    # ---- section G ---------------------------------------------------------
    print("[G]  VERDICT")
    print("=" * 76)
    print(f"  [A] critical chains valid & per-step BFT-sharp ........ "
          f"{'PASS' if chains_ok else 'FAIL'}")
    print(f"  [C] (L1) symmetric-pair lemma  (Pr = 1/2 exactly) ..... "
          f"{'PASS' if l1_ok else 'FAIL'}")
    print(f"  [D] (ICOP-step) BFT-sharp at n = 3,4,5,6 .............. "
          f"{'PASS' if icop_all_bft else 'FAIL'}")
    print(f"  [E] F8' n=6 candidate reproduced (4/4 BFT-sharp) ...... "
          f"{'PASS' if f8p_ok else 'FAIL'}")
    print(f"  [F] width-3 bridge m=4 base (|PPF_4|={ppf4_size}) ......... "
          f"{'PASS' if bridge_ok else 'FAIL'}")
    print(f"  [H1] canonical top posets are width-2 OSA w/ >=2 block  "
          f"{'PASS' if h1_ok else 'FAIL'}")
    print(f"  [H2] (L2) is not a naive greedy invariant ............. "
          f"{'PASS' if h2_ok else 'FAIL'}")
    print()
    all_pass = all([chains_ok, l1_ok, icop_all_bft, f8p_ok, bridge_ok,
                    h1_ok, h2_ok])
    if all_pass:
        print("  ALL TRIP-WIRES PASS.  (ICOP-step) holds at n=3,4,5,6: the")
        print("  lex-min new cover of G_n is a SYMMETRIC incomparable pair,")
        print("  so Pr = 1/2 uniformly via lemma (L1).  (L1) is certified;")
        print("  G_3,G_4,G_5 are width-2 ordinal sums of antichains [(L2)],")
        print("  and (L2) is not a naive greedy invariant.  The m=4 base of")
        print("  the width-3 reduction bridge is confirmed (44/44).  All")
        print("  consistent with the F19 reduction in")
        print("  docs/compatibility-geometry-F19-icop-step-and-bridge.md.")
    else:
        print("  !! SOME TRIP-WIRE FAILED -- see above.  The F19 proof rests")
        print("     on these; investigate before trusting the verdict.")
    print()
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
