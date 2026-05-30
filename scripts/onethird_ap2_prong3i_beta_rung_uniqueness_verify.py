#!/usr/bin/env python3
"""
OneThird AP-2 Prong 3I-beta: Rung-Uniqueness for SD-FLOOR via gadget-identity rigidity.

Accompanies docs/OneThird-AP-2-Prong3I-beta-RungUniqueness-SD-FLOOR.md.

GOAL (rung-uniqueness): for each descent-ladder rung n in {5, 7, 10} — with per-level
floor Q = (k+1)/(3k) at k in {11, 13, 17} = {4/11, 14/39, 6/17} respectively — prove
in the EXTREME-REDUCED width-3 sub-arena that the Q-minimizer set M_n satisfies

      |M_n| = 1   (SD-UNIQ closes -> the unique minimizer is self-dual)
   OR |M_n| odd   (SD-PARITY closes -> at least one minimizer is self-dual).

Either case forces SD-FLOOR (a self-dual class sits at the floor) at that rung.

This script bundles:

  * The analytic kernel from mg-f6d3 (Prong 3I-alpha):
      - Engine E1: linear-extension counter e(P) (downset DP).
      - Engine E2: Stanley balance ratio Pr[x<y] = e(P+x<y)/e(P).
      - Engine E3: brute-force permutation cross-check (small n).
      - Stanley reversal dual involution P -> P*.
      - Q(P) = max over incomparable pairs of min(Pr[x<y], Pr[y<x]).
      - SD0 / SD1 / SD-UNIQ / SD-PARITY sanity (re-confirm n=6 dual pair Q=15/37).

  * NEW for 3I-beta:
      - Extreme-reduced (no global max, no global min) width-3 poset enumeration up
        to order-iso via canonical augmentation (add-a-maximal-element), with a
        color-refinement canonical form so n=10 is laptop-feasible.
      - For each rung n in {5, 7, 10}: exhaust the extreme-reduced width-3 sub-arena,
        find the per-level Q floor, collect the minimizer iso-classes M_n, report
        |M_n| and how many are self-dual.

  * Five-/three-engine cross-check: E1 vs E3 on e(P); E2 vs E3 on Pr; SD0 dual-invariance
    Q(P)=Q(P*) checked on every minimizer.

Monte Carlo is NEVER used; everything is exact rational arithmetic (fractions).
"""

import argparse
import itertools
import sys
import time
from fractions import Fraction
from functools import lru_cache


# ======================================================================
# Core poset primitives (n elements 0..n-1; `less` = frozenset of (a,b)
# meaning a < b strict, transitively closed).
# ======================================================================

def transitive_closure(n, relations):
    less = [[False] * n for _ in range(n)]
    for (a, b) in relations:
        less[a][b] = True
    for k in range(n):
        lk = less[k]
        for i in range(n):
            if less[i][k]:
                li = less[i]
                for j in range(n):
                    if lk[j]:
                        li[j] = True
    return frozenset((i, j) for i in range(n) for j in range(n) if less[i][j])


def covers_to_poset(n, covers):
    return transitive_closure(n, covers)


# ----- Engine E1: linear-extension count via downset DP --------------

def linear_extensions_count(n, less):
    preds = [0] * n
    for (a, b) in less:
        preds[b] |= (1 << a)
    full = (1 << n) - 1

    @lru_cache(maxsize=None)
    def count(placed):
        if placed == full:
            return 1
        total = 0
        for e in range(n):
            if not (placed & (1 << e)) and (preds[e] & placed) == preds[e]:
                total += count(placed | (1 << e))
        return total

    res = count(0)
    count.cache_clear()
    return res


def linear_extensions_delmax(n, less):
    """Engine E3': independent recursion e(P) = sum over maximal m of e(P - m).
    Top-down deletion of maximal elements vs E1's bottom-up downset front --
    a genuinely different computation, valid at any n (no n! blowup)."""
    above = [frozenset(j for j in range(n) if (i, j) in less) for i in range(n)]

    @lru_cache(maxsize=None)
    def rec(present):
        if not present:
            return 1
        pset = frozenset(present)
        total = 0
        for m in present:
            if above[m].isdisjoint(pset):  # m maximal within `present`
                total += rec(tuple(x for x in present if x != m))
        return total

    res = rec(tuple(range(n)))
    rec.cache_clear()
    return res


# ----- Engine E3: brute-force linear extensions -----------------------

def linear_extensions_bruteforce(n, less):
    cnt = 0
    rel = less
    for perm in itertools.permutations(range(n)):
        pos = [0] * n
        for i, e in enumerate(perm):
            pos[e] = i
        ok = True
        for (a, b) in rel:
            if pos[a] > pos[b]:
                ok = False
                break
        if ok:
            cnt += 1
    return cnt


# ----- Engine E2: Stanley balance ratio -------------------------------

def prob_less_given_etotal(n, less, x, y, e_total):
    less2 = transitive_closure(n, set(less) | {(x, y)})
    return Fraction(linear_extensions_count(n, less2), e_total)


def prob_less(n, less, x, y):
    e_total = linear_extensions_count(n, less)
    return prob_less_given_etotal(n, less, x, y, e_total)


def incomparable_pairs(n, less):
    return [(x, y) for x, y in itertools.combinations(range(n), 2)
            if (x, y) not in less and (y, x) not in less]


def Q_of(n, less):
    """Q(P) = max over incomparable pairs of min(Pr[x<y], Pr[y<x])."""
    e_total = linear_extensions_count(n, less)
    best = Fraction(0)
    for (x, y) in incomparable_pairs(n, less):
        p = prob_less_given_etotal(n, less, x, y, e_total)
        bal = p if p <= 1 - p else 1 - p
        if bal > best:
            best = bal
    return best


def Q_with_reject(n, less, reject_above):
    """Compute Q(P) but early-abort (return None) the moment some incomparable
    pair has balance strictly greater than `reject_above` -- such a poset cannot
    be a Q-minimizer once the running floor is `reject_above`. Returns the exact
    Fraction Q only if Q <= reject_above (i.e. P survives as a candidate)."""
    e_total = linear_extensions_count(n, less)
    best = Fraction(0)
    for (x, y) in incomparable_pairs(n, less):
        p = prob_less_given_etotal(n, less, x, y, e_total)
        bal = p if p <= 1 - p else 1 - p
        if bal > reject_above:
            return None
        if bal > best:
            best = bal
    return best


def dual(n, less):
    """Stanley reversal: P* has a <* b iff b < a."""
    return frozenset((b, a) for (a, b) in less)


# ======================================================================
# Canonical form (order-iso) via color refinement + color-respecting
# backtracking.  Returns the lexicographically minimal relation tuple.
# ======================================================================

def _refined_colors(n, less):
    # adjacency by strict-below / strict-above
    below = [[] for _ in range(n)]   # below[i] = elements j with j < i
    above = [[] for _ in range(n)]   # above[i] = elements j with i < j
    for (a, b) in less:
        above[a].append(b)
        below[b].append(a)
    # initial color: (#below, #above)
    color = [(len(below[i]), len(above[i])) for i in range(n)]
    # compress to small ints
    def compress(col):
        order = {c: r for r, c in enumerate(sorted(set(col)))}
        return [order[c] for c in col]
    color = compress(color)
    for _ in range(n):
        new = []
        for i in range(n):
            lo = tuple(sorted(color[j] for j in below[i]))
            hi = tuple(sorted(color[j] for j in above[i]))
            new.append((color[i], lo, hi))
        newc = compress(new)
        if newc == color:
            break
        color = newc
    return color


def canonical_form(n, less):
    """Lexicographically minimal sorted relation tuple over color-respecting
    relabelings.  For width-3 posets the color classes are small, so the
    backtracking is fast even at n=10."""
    color = _refined_colors(n, less)
    classes = {}
    for i in range(n):
        classes.setdefault(color[i], []).append(i)
    # process color classes in fixed order; within each class try all orderings
    class_keys = sorted(classes)
    groups = [classes[k] for k in class_keys]

    rel_pairs = list(less)

    best = [None]

    # we assign canonical labels 0..n-1 in the order: group0 elements, group1, ...
    def search(gi, assigned, perm):
        if gi == len(groups):
            relabeled = sorted((perm[a], perm[b]) for (a, b) in rel_pairs)
            t = tuple(relabeled)
            if best[0] is None or t < best[0]:
                best[0] = t
            return
        grp = groups[gi]
        base = assigned
        for ordering in itertools.permutations(grp):
            for off, elt in enumerate(ordering):
                perm[elt] = base + off
            search(gi + 1, base + len(grp), perm)

    search(0, 0, [0] * n)
    return best[0]


def is_self_dual(n, less):
    return canonical_form(n, less) == canonical_form(n, dual(n, less))


# ======================================================================
# Width / extreme-reduced structure tests
# ======================================================================

def width_le_3(n, less):
    """True iff no antichain of size 4 exists (Dilworth width <= 3)."""
    for quad in itertools.combinations(range(n), 4):
        ok = True
        for a, b in itertools.combinations(quad, 2):
            if (a, b) in less or (b, a) in less:
                ok = False
                break
        if ok:
            return False
    return True


def has_antichain_3(n, less):
    """True iff some 3 elements are pairwise incomparable (width >= 3)."""
    for tri in itertools.combinations(range(n), 3):
        ok = True
        for a, b in itertools.combinations(tri, 2):
            if (a, b) in less or (b, a) in less:
                ok = False
                break
        if ok:
            return True
    return False


def width_exactly_3(n, less):
    """Width EXACTLY 3: an antichain of size 3 exists but none of size 4.
    The whole AP-2 arc is about width-exactly-3 posets; width-2 posets (e.g. the
    textbook point-parallel-2-chain Q=1/3 gadget) are a DIFFERENT regime and must
    be excluded, else the floor collapses to the conjecture value 1/3."""
    return has_antichain_3(n, less) and width_le_3(n, less)


def maximal_elements(n, less):
    have_above = {a for (a, b) in less}
    return [i for i in range(n) if i not in have_above]


def minimal_elements(n, less):
    have_below = {b for (a, b) in less}
    return [i for i in range(n) if i not in have_below]


def is_extreme_reduced(n, less):
    """No global max, no global min  <=>  >=2 maximal AND >=2 minimal elements."""
    return len(maximal_elements(n, less)) >= 2 and len(minimal_elements(n, less)) >= 2


# ======================================================================
# Enumeration of width-<=3 posets up to iso via canonical augmentation:
# add one element at a time as a NEW MAXIMAL element whose strict-lower set
# is an order ideal (downset) of the current poset.  Dedup by canonical form.
# ======================================================================

def order_ideals(n, less):
    """Yield every downset (order ideal) as a bitmask.  A set S is a downset
    iff for every element in S, all its strict-lowers are in S."""
    preds = [0] * n
    for (a, b) in less:
        preds[b] |= (1 << a)
    ideals = []
    full = (1 << n) - 1

    # enumerate downsets via DP over elements in a linear extension order is
    # overkill; n is small here so test each subset is fine for n<=10? 2^10=1024.
    for mask in range(1 << n):
        ok = True
        m = mask
        while m:
            e = (m & -m).bit_length() - 1
            if (preds[e] & mask) != preds[e]:
                ok = False
                break
            m &= m - 1
        if ok:
            ideals.append(mask)
    return ideals


def enumerate_width3(n_target, extreme_reduced_only=True, progress=False):
    """Return a list of canonical forms (tuples) of all width-<=3 posets on
    exactly n_target elements (optionally extreme-reduced).  Built by canonical
    augmentation level by level, deduped by canonical form."""
    # level 1: single element, no relations
    level = {canonical_form(1, frozenset()): frozenset()}
    for n in range(1, n_target):
        nxt = {}
        t0 = time.time()
        for _, less in level.items():
            for S in order_ideals(n, less):
                # new element = n, above exactly the elements of S
                new_rel = set(less)
                for a in range(n):
                    if S & (1 << a):
                        new_rel.add((a, n))
                new_less = transitive_closure(n + 1, new_rel)
                if not width_le_3(n + 1, new_less):
                    continue
                cf = canonical_form(n + 1, new_less)
                if cf not in nxt:
                    nxt[cf] = frozenset(cf)
        level = nxt
        if progress:
            print(f"    level n={n+1}: {len(level)} width-<=3 iso-classes "
                  f"({time.time()-t0:.1f}s)", file=sys.stderr, flush=True)
    # Final arena: width EXACTLY 3 (exclude width-<=2), and extreme-reduced.
    # width-<=3 was kept during AUGMENTATION so width-2 parents that grow into
    # width-3 children are not pruned; the arena itself is width-exactly-3.
    out = [less for cf, less in level.items() if width_exactly_3(n_target, less)]
    if extreme_reduced_only:
        return [less for less in out if is_extreme_reduced(n_target, less)]
    return out


def find_minimizers(n, posets, progress=False):
    """Given a list of posets (as `less` frozensets on n elements), find the
    minimum Q and the iso-classes attaining it.  Uses early-rejection."""
    best_Q = Fraction(1)   # Q <= 1/2 always; start high
    minimizers = []        # list of (less, Q)
    checked = 0
    t0 = time.time()
    for less in posets:
        checked += 1
        q = Q_with_reject(n, less, best_Q)
        if q is None:
            continue
        if q < best_Q:
            best_Q = q
            minimizers = [less]
        elif q == best_Q:
            minimizers.append(less)
        if progress and checked % 5000 == 0:
            print(f"      ...{checked}/{len(posets)} scanned, "
                  f"best_Q={best_Q} ({time.time()-t0:.1f}s)",
                  file=sys.stderr, flush=True)
    # collapse minimizers to iso-classes (they should already be iso-distinct
    # since `posets` came deduped, but be safe)
    classes = {}
    for less in minimizers:
        classes[canonical_form(n, less)] = less
    return best_Q, list(classes.values())


# ======================================================================
# Sanity checks (re-confirm mg-f6d3 facts)
# ======================================================================

def sanity_n6_refutation():
    """n=6 REFUTATION witness C and its dual C*: both Q=15/37, neither self-dual,
    SD0 gives Q(C)=Q(C*)."""
    n = 6
    C_covers = [(0, 2), (0, 4), (0, 5), (1, 3), (1, 4), (2, 3)]
    C = covers_to_poset(n, C_covers)
    Cstar = dual(n, C)
    eC = linear_extensions_count(n, C)
    eC_bf = linear_extensions_bruteforce(n, C)
    QC = Q_of(n, C)
    QCs = Q_of(n, Cstar)
    sd = is_self_dual(n, C)
    same = canonical_form(n, C) == canonical_form(n, Cstar)
    print("  [sanity n=6] e(C) =", eC, "(E1)  e(C) =", eC_bf, "(E3)  match:",
          eC == eC_bf)
    print("  [sanity n=6] Q(C) =", QC, "  Q(C*) =", QCs,
          "  SD0 dual-invariance holds:", QC == QCs)
    print("  [sanity n=6] self-dual?", sd, "  C ~= C* ?", same,
          "  (expect both False = benign dual pair)")
    ok = (eC == eC_bf and QC == QCs == Fraction(15, 37)
          and not sd and not same)
    print("  [sanity n=6]", "PASS" if ok else "FAIL")
    return ok


def cross_check_engines(n, less):
    """Independent-engine cross-check on a single poset, valid at any n:
      - e(P): E1 (downset DP) vs E3' (maximal-deletion recursion);
      - for every incomparable pair, the Stanley balance e(P+x<y)/e(P) computed
        via E1 vs via E3';
      - additionally, for n<=8, the full n! permutation engine E2 on e(P).
    Returns (ok, message)."""
    e1 = linear_extensions_count(n, less)
    e3 = linear_extensions_delmax(n, less)
    if e1 != e3:
        return False, f"e(P): E1={e1} E3'={e3}"
    if n <= 8:
        e2 = linear_extensions_bruteforce(n, less)
        if e2 != e1:
            return False, f"e(P): E2(brute)={e2} E1={e1}"
    for (x, y) in incomparable_pairs(n, less):
        less2 = transitive_closure(n, set(less) | {(x, y)})
        a1 = linear_extensions_count(n, less2)
        a3 = linear_extensions_delmax(n, less2)
        if a1 != a3:
            return False, f"e(P+{x}<{y}): E1={a1} E3'={a3}"
    return True, "ok"


# ======================================================================
# Main driver
# ======================================================================

RUNGS = {5: Fraction(4, 11), 7: Fraction(14, 39), 10: Fraction(6, 17)}


def run_rung(n, progress=False, cross_check=False):
    print(f"\n=== RUNG n={n}  (expected per-level floor q = {RUNGS[n]}) ===",
          flush=True)
    t0 = time.time()
    posets = enumerate_width3(n, extreme_reduced_only=True, progress=progress)
    print(f"  extreme-reduced width-3 iso-classes at n={n}: {len(posets)}  "
          f"({time.time()-t0:.1f}s)", flush=True)
    bestQ, M = find_minimizers(n, posets, progress=progress)
    print(f"  per-level Q floor q* = {bestQ}  (= {float(bestQ):.6f})", flush=True)
    print(f"  |M_{n}| = {len(M)}  (number of extreme-reduced Q-minimizer "
          f"iso-classes)", flush=True)
    n_sd = 0
    for less in M:
        sd = is_self_dual(n, less)
        if sd:
            n_sd += 1
        e = linear_extensions_count(n, less)
        # SD0 dual-invariance check on each minimizer
        assert Q_of(n, less) == Q_of(n, dual(n, less)), "SD0 violated!"
        print(f"    minimizer: e(P)={e}  self-dual={sd}  covers~{sorted(less)[:6]}...",
              flush=True)
    # verdict per SD-UNIQ / SD-PARITY
    closes = (len(M) == 1) or (len(M) % 2 == 1)
    via = ("SD-UNIQ |M|=1" if len(M) == 1
           else ("SD-PARITY |M| odd" if len(M) % 2 == 1 else "NEITHER (|M| even)"))
    print(f"  self-dual minimizers: {n_sd}/{len(M)}", flush=True)
    print(f"  rung-uniqueness closes? {closes}  via {via}", flush=True)
    if len(M) % 2 == 0 and n_sd == 0:
        print("  *** REFUTATION-FLAG: even |M| with NO self-dual minimizer ***",
              flush=True)
    if cross_check:
        for less in M:
            ok, msg = cross_check_engines(n, less)
            print(f"    engine cross-check on minimizer: {'PASS' if ok else 'FAIL '+msg}",
                  flush=True)
    return {
        "n": n, "floor": bestQ, "M_size": len(M), "self_dual": n_sd,
        "closes": closes, "via": via,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rungs", type=str, default="5,7",
                    help="comma-separated n values to run (default 5,7; add 10 for the full run)")
    ap.add_argument("--progress", action="store_true")
    ap.add_argument("--cross-check", action="store_true",
                    help="run E1/E2/E3 engine cross-check on each minimizer (small n)")
    ap.add_argument("--benchmark", action="store_true",
                    help="just print iso-class counts per level up to max rung")
    args = ap.parse_args()

    print("OneThird AP-2 Prong 3I-beta: rung-uniqueness verification")
    print("=" * 64)
    ok = sanity_n6_refutation()
    if not ok:
        print("SANITY FAILED -- aborting.")
        sys.exit(1)

    rungs = [int(x) for x in args.rungs.split(",") if x.strip()]
    results = []
    for n in rungs:
        results.append(run_rung(n, progress=args.progress,
                                cross_check=args.cross_check))

    print("\n" + "=" * 64)
    print("SUMMARY")
    for r in results:
        print(f"  n={r['n']:2d}  floor={r['floor']}  |M_n|={r['M_size']}  "
              f"self-dual={r['self_dual']}  closes={r['closes']} ({r['via']})")
    all_close = all(r["closes"] for r in results)
    print(f"\n  rung-uniqueness closes at ALL requested rungs: {all_close}")
    if all_close:
        print("  => SD-FLOOR unconditionally proved at these ladder rungs "
              "(via SD-UNIQ / SD-PARITY).")


if __name__ == "__main__":
    main()
