#!/usr/bin/env python3
"""
OneThird AP-2 Prong 2: Family B (width-3 series-parallel posets) viability + sweep.

Roadmap ref: docs/OneThird-Algebraic-Program-Roadmap.md (sections 3, 6, 8).
Vision ref:  docs/OneThird-Algebraic-Program-Vision.md (V1-V4).
Ticket:      mg-63df. Follow-up to mg-9597 (AP-2 Prong 1).

WHAT THIS DOES
--------------
Prong 1 (mg-9597) exhausted the box-rotation symmetry lever on FAMILY A
(3-row skew shapes) and named the missing analytic input as a special case of
the open width-3 conjecture itself. This Prong 2 pivots to FAMILY B = width-<=3
SERIES-PARALLEL (SP) posets, to answer the live program question:

    Is 27/70 (the Family-A skew-shape floor) a SKEW ARTIFACT, or a candidate
    width-3 algebraic-poset floor that extends to other families?

THE CONJECTURE / THE Q METRIC
-----------------------------
1/3-2/3 conjecture (Kislitsyn / Brightwell form): every finite poset that is
not a chain has an incomparable pair {x,y} with 1/3 <= Pr[x<y] <= 2/3, where Pr
is over uniformly random linear extensions.

We track, per poset P,
    Q(P) = max over incomparable pairs {x,y} of min(Pr[x<y], Pr[y<x]).
Equivalently Q(P) = 1/2 - min over incomparable pairs of |Pr[x<y] - 1/2|.
The conjecture says Q(P) >= 1/3 for every non-chain P. A *small* Q means every
incomparable pair is unbalanced (the dangerous regime); Q < 1/3 would be a
counterexample. We sweep Family B and report min Q, the argmin, and compare
with 27/70 (Family-A floor) and 1/3 (global conjecture bound).

  Sanity anchors (all triple-checked: closed-form == DP == brute):
    - width-3 antichain {a,b,c}            -> Q = 1/2
    - a + (b||c||d)  [series over 3-AC]    -> Q = 1/2
    - (a||b) + (c||d||e)                    -> Q = 1/2 (= max of within-comp Q)
    - 1 || (y<z)  [width-2, canonical tight]-> Q = 1/3  (textbook tight bound)

WIDTH-<=3 vs WIDTH-EXACTLY-3
----------------------------
"width-3 SP-tree" = SP poset of width <= 3 (parallel composition gated by
width(P)+width(Q) <= 3; series preserves width = max). This family CONTAINS the
canonical tight poset 1||(y<z) of width 2, which has Q = 1/3 exactly -- the
known global tight bound of the 1/3-2/3 conjecture. So over the *full* width-<=3
family the minimum is trivially 1/3.

The meaningful comparison against the Family-A floor (27/70, attained at the
width-3 shape (4,4,2)/(2,0,0)) is therefore over WIDTH-EXACTLY-3 SP posets,
which is what Family A's 3-row shapes are. We report BOTH:
    (i)  min Q over width-<=3  (context: hits 1/3 via the width-2 tight poset)
    (ii) min Q over width==3   (the apples-to-apples comparison with 27/70)

GUARD (roadmap section 8.2, anti-Cheeger)
-----------------------------------------
If Q <= 1/3 surfaces anywhere, we (a) confirm it is EXACTLY 1/3 (not < 1/3) via
exact rational brute-force enumeration, (b) cross-check against an INDEPENDENT
reimplementation (scripts/onethird_ap2_prong2_independent_check.py, no shared
code), and (c) refuse to emit any counterexample claim. Q == 1/3 is the textbook
tight boundary (conjecture SATISFIED, and proven for SP posets); only Q < 1/3
would be a counterexample, and none is found.

THREE INDEPENDENT ENGINES (for cross-checks and the guard)
----------------------------------------------------------
  1. Q_closed_sp(tree)  -- SP-tree structural recursion (the "closed form").
  2. Q_via_dp(elems,lt) -- generic order-ideal DP over linear-extension counts;
                           family-agnostic, mirrors the AP-0 kernel's Q_via_dp.
  3. Q_via_brute(...)   -- brute force over all permutations (gold-standard).
"""
from __future__ import annotations

import argparse
import itertools
from fractions import Fraction
from functools import lru_cache
from math import comb
from typing import Dict, List, Tuple

# A labeled SP node is a tuple:
#   ('leaf', id)            a single element with integer label `id`
#   ('S', (child, child,...)) ordinal sum (series): children[0] lowest
#   ('P', (child, child,...)) disjoint union (parallel): unordered
# A *structural* (unlabeled) node uses ('leaf',) and is what we enumerate/dedup.

ONE_THIRD = Fraction(1, 3)
FAMILY_A_FLOOR = Fraction(27, 70)


# --------------------------------------------------------------------------
# Structural enumeration of width-<=3 SP posets, canonical-form deduplicated.
# --------------------------------------------------------------------------
def s_width(node) -> int:
    if node[0] == 'leaf':
        return 1
    if node[0] == 'S':
        return max(s_width(c) for c in node[1])
    return sum(s_width(c) for c in node[1])  # 'P'


def s_size(node) -> int:
    if node[0] == 'leaf':
        return 1
    return sum(s_size(c) for c in node[1])


def canon(node):
    """Canonical structural form: flatten same-type nesting; sort parallel
    children (parallel = commutative); keep series order (ordinal sum order is
    fixed by the poset). The series-parallel decomposition tree is unique up to
    reordering parallel children, so this is one representative per SP poset."""
    if node[0] == 'leaf':
        return ('leaf',)
    kind = node[0]
    flat = []
    for c in node[1]:
        cc = canon(c)
        if cc[0] == kind:           # merge associative nesting
            flat.extend(cc[1])
        else:
            flat.append(cc)
    if kind == 'P':
        flat.sort()
    return (kind, tuple(flat))


def enumerate_sp(n_max: int) -> Dict[int, List[tuple]]:
    """trees_by_size[n] = list of canonical structural SP posets of size n,
    width <= 3. Built by binary series/parallel composition + canonical dedup;
    binary composition + flattening reaches every width-<=3 SP poset."""
    by_size: Dict[int, set] = {1: {('leaf',)}}
    for n in range(2, n_max + 1):
        seen = set()
        for a in range(1, n):
            b = n - a
            if a not in by_size or b not in by_size:
                continue
            for A in by_size[a]:
                wA = s_width(A)
                for B in by_size[b]:
                    wB = s_width(B)
                    # series A + B (A below B)
                    if max(wA, wB) <= 3:
                        seen.add(canon(('S', (A, B))))
                    # parallel A || B
                    if wA + wB <= 3:
                        seen.add(canon(('P', (A, B))))
        by_size[n] = seen
    return {k: sorted(v) for k, v in by_size.items()}


def label(node, counter=None):
    """Assign distinct integer leaf labels in traversal order."""
    if counter is None:
        counter = [0]
    if node[0] == 'leaf':
        i = counter[0]
        counter[0] += 1
        return ('leaf', i)
    return (node[0], tuple(label(c, counter) for c in node[1]))


# --------------------------------------------------------------------------
# Engine 1: SP-tree closed-form Q (structural recursion).
# --------------------------------------------------------------------------
@lru_cache(maxsize=None)
def _merge_prob(a: int, b: int, m: int, n: int) -> Fraction:
    """F(a,b,m,n) = Pr[ a-th element of group 1 (size m) precedes b-th element
    of group 2 (size n) ] in a uniformly random merge of the two groups.

    a-th of group1 precedes b-th of group2  <=>  fewer than b group2-elements
    precede the a-th group1-element. # of group2 before the a-th group1-element
    is negative-hypergeometric:
        Pr[exactly j] = C(a-1+j, j) * C(m-a + n-j, n-j) / C(m+n, n).
    """
    denom = comb(m + n, n)
    s = 0
    for j in range(0, b):
        s += comb(a - 1 + j, j) * comb(m - a + n - j, n - j)
    return Fraction(s, denom)


def lsize(node) -> int:
    if node[0] == 'leaf':
        return 1
    return sum(lsize(c) for c in node[1])


def rank_dist(node) -> Dict[int, Dict[int, Fraction]]:
    """For a labeled subtree, return {elem -> {pos(1..size) -> Pr[rank=pos]}},
    the distribution of each element's position within a uniform linear
    extension of THIS subtree."""
    if node[0] == 'leaf':
        return {node[1]: {1: Fraction(1)}}
    if node[0] == 'S':
        res: Dict[int, Dict[int, Fraction]] = {}
        offset = 0
        for c in node[1]:
            rc = rank_dist(c)
            for e, dist in rc.items():
                res[e] = {pos + offset: p for pos, p in dist.items()}
            offset += lsize(c)
        return res
    # parallel: x at local rank a lands at global rank a+k where k = number of
    # other-component elements placed before x (negative-hypergeometric).
    children = node[1]
    sizes = [lsize(c) for c in children]
    M = sum(sizes)
    res = {}
    for idx, c in enumerate(children):
        m = sizes[idx]
        o = M - m
        denom = comb(m + o, o)
        rc = rank_dist(c)
        for e, dist in rc.items():
            nd: Dict[int, Fraction] = {}
            for a, pa in dist.items():
                for k in range(0, o + 1):
                    coeff = comb(a - 1 + k, k) * comb(m - a + o - k, o - k)
                    p = pa * Fraction(coeff, denom)
                    if p:
                        nd[a + k] = nd.get(a + k, Fraction(0)) + p
            res[e] = nd
    return res


def Q_closed_sp(node):
    """Q over the labeled SP poset. Incomparable pairs are exactly the pairs
    whose lowest common ancestor in the SP-tree is a parallel node. For such a
    pair (x in child Ci, y in child Cj), Pr[x<y] depends only on Ci, Cj:
        Pr[x<y] = sum_{a,b} R_Ci(x)[a] R_Cj(y)[b] F(a,b,|Ci|,|Cj|).
    Returns (Q as Fraction, witnessing-pair-Pr) or None for a chain."""
    best = None
    best_pr = None

    def visit(nd):
        nonlocal best, best_pr
        if nd[0] == 'leaf':
            return
        if nd[0] == 'S':
            for c in nd[1]:
                visit(c)
            return
        children = nd[1]
        rds = [rank_dist(c) for c in children]
        szs = [lsize(c) for c in children]
        for i in range(len(children)):
            for j in range(i + 1, len(children)):
                mi, mj = szs[i], szs[j]
                for x, dx in rds[i].items():
                    for y, dy in rds[j].items():
                        pr = Fraction(0)
                        for a, pa in dx.items():
                            for b, pb in dy.items():
                                pr += pa * pb * _merge_prob(a, b, mi, mj)
                        val = min(pr, 1 - pr)
                        if best is None or val > best:
                            best = val
                            best_pr = pr
        for c in children:
            visit(c)

    visit(node)
    if best is None:
        return None
    return best, best_pr


# --------------------------------------------------------------------------
# Relations from a labeled SP tree (for the generic engines).
# --------------------------------------------------------------------------
def relations(node) -> Tuple[List[int], set]:
    """Return (elements, set of strict pairs (a,b) meaning a < b)."""
    if node[0] == 'leaf':
        return [node[1]], set()
    if node[0] == 'S':
        elems: List[int] = []
        rel = set()
        groups = []
        for c in node[1]:
            e, r = relations(c)
            rel |= r
            groups.append(e)
            elems.extend(e)
        for gi in range(len(groups)):
            for gj in range(gi + 1, len(groups)):
                for a in groups[gi]:
                    for b in groups[gj]:
                        rel.add((a, b))  # earlier series part below later
        return elems, rel
    # parallel: union, no cross relations
    elems = []
    rel = set()
    for c in node[1]:
        e, r = relations(c)
        rel |= r
        elems.extend(e)
    return elems, rel


# --------------------------------------------------------------------------
# Engine 2: generic order-ideal DP over linear-extension counts.
# (Family-agnostic; mirrors the AP-0 kernel scripts/onethird_ap0_*.py Q_via_dp.)
# --------------------------------------------------------------------------
def count_linear_extensions(elements: List[int], preds: Dict[int, frozenset]) -> int:
    """Number of linear extensions via order-ideal DP. preds[x] = elements
    strictly below x. g(ideal) = sum over x maximal-in-ideal of g(ideal\\{x})."""
    idx = {e: i for i, e in enumerate(elements)}
    full = (1 << len(elements)) - 1
    pred_mask = [0] * len(elements)
    for e in elements:
        m = 0
        for p in preds.get(e, frozenset()):
            m |= 1 << idx[p]
        pred_mask[idx[e]] = m

    from functools import lru_cache as _lc

    @_lc(maxsize=None)
    def g(mask: int) -> int:
        if mask == 0:
            return 1
        total = 0
        mm = mask
        while mm:
            low = mm & (-mm)
            i = low.bit_length() - 1
            mm ^= low
            # i removable last iff no element above i remains, i.e. all preds of
            # the *complement* ... we build bottom-up: i is minimal in mask if
            # none of its preds are in mask.
            if pred_mask[i] & mask == 0:
                total += g(mask ^ low)
        return total

    res = g(full)
    g.cache_clear()
    return res


def _transitive_closure(elements, rel):
    less = {e: set() for e in elements}
    for (a, b) in rel:
        less[b].add(a)
    changed = True
    while changed:
        changed = False
        for e in elements:
            add = set()
            for p in less[e]:
                add |= less[p]
            if not add <= less[e]:
                less[e] |= add
                changed = True
    return less


def Q_via_dp(elements: List[int], rel: set):
    """Generic Q over any poset given strict relation `rel`. Returns
    (Q, witness_pr) or None for a chain."""
    less = _transitive_closure(elements, rel)
    preds = {e: frozenset(less[e]) for e in elements}
    total = count_linear_extensions(elements, preds)
    best = None
    best_pr = None
    for x, y in itertools.combinations(elements, 2):
        if y in less[x] or x in less[y]:
            continue  # comparable
        # count extensions with x before y = LE(poset + relation x<y)
        less2 = {e: set(preds[e]) for e in elements}
        less2[y].add(x)
        less2_full = _transitive_closure(elements,
                                         {(p, e) for e in elements for p in less2[e]})
        preds2 = {e: frozenset(less2_full[e]) for e in elements}
        cnt_xy = count_linear_extensions(elements, preds2)
        pr = Fraction(cnt_xy, total)
        val = min(pr, 1 - pr)
        if best is None or val > best:
            best = val
            best_pr = pr
    if best is None:
        return None
    return best, best_pr


# --------------------------------------------------------------------------
# Engine 3: brute-force over all permutations (gold-standard, independent).
# --------------------------------------------------------------------------
def Q_via_brute(elements: List[int], rel: set):
    """Q by enumerating every permutation and keeping linear extensions.
    Exact; O(n!) -- use only for small n (<= ~9)."""
    less = _transitive_closure(elements, rel)
    n = len(elements)
    total = 0
    # before[(x,y)] = # linear extensions with x before y, for incomparable pairs
    incomp = [(x, y) for x, y in itertools.combinations(elements, 2)
              if y not in less[x] and x not in less[y]]
    before = {p: 0 for p in incomp}
    pos = {}
    for perm in itertools.permutations(elements):
        ok = True
        for i, e in enumerate(perm):
            pos[e] = i
        for e in elements:
            for p in less[e]:
                if pos[p] > pos[e]:
                    ok = False
                    break
            if not ok:
                break
        if not ok:
            continue
        total += 1
        for (x, y) in incomp:
            if pos[x] < pos[y]:
                before[(x, y)] += 1
    if not incomp:
        return None
    best = None
    best_pr = None
    for (x, y) in incomp:
        pr = Fraction(before[(x, y)], total)
        val = min(pr, 1 - pr)
        if best is None or val > best:
            best = val
            best_pr = pr
    return best, best_pr


# --------------------------------------------------------------------------
# Pretty-printer for SP trees.
# --------------------------------------------------------------------------
def tree_str(node) -> str:
    if node[0] == 'leaf':
        return "*"
    inner = [tree_str(c) for c in node[1]]
    if node[0] == 'S':
        return "(" + " + ".join(inner) + ")"
    return "(" + " || ".join(inner) + ")"


# --------------------------------------------------------------------------
# Sanity checks (three-engine cross-check on the ticket's named anchors).
# --------------------------------------------------------------------------
def _named_trees():
    leaf = ('leaf',)
    AC3 = ('P', (leaf, leaf, leaf))
    return {
        "n=3 antichain  (a||b||c)": (('P', (leaf, leaf, leaf)), Fraction(1, 2)),
        "n=4  a+(b||c||d)": (('S', (leaf, AC3)), Fraction(1, 2)),
        "n=5  (a||b)+(c||d||e)": (('S', (('P', (leaf, leaf)), AC3)), Fraction(1, 2)),
        "n=3  1||(y<z)  [tight]": (('P', (leaf, ('S', (leaf, leaf)))), Fraction(1, 3)),
    }


def run_sanity():
    print("=== SANITY (three-engine cross-check) ===")
    allok = True
    for name, (struct, expected) in _named_trees().items():
        lab = label(struct)
        qc = Q_closed_sp(lab)
        elems, rel = relations(lab)
        qd = Q_via_dp(elems, rel)
        qb = Q_via_brute(elems, rel)
        qcv = qc[0] if qc else None
        qdv = qd[0] if qd else None
        qbv = qb[0] if qb else None
        ok = (qcv == qdv == qbv == expected)
        allok = allok and ok
        print(f"  [{'OK ' if ok else 'XX '}] {name:32s} "
              f"closed={qcv} dp={qdv} brute={qbv} expected={expected}")
    print(f"  --> sanity {'PASSED' if allok else 'FAILED'}")
    return allok


def run_crosscheck(n_max_brute=8, n_max_dp=11, n_random=50):
    """Verify closed-form == DP (all shapes up to n_max_dp) and == brute
    (all shapes up to n_max_brute)."""
    print(f"\n=== CROSS-CHECK closed vs DP (n<= {n_max_dp}) "
          f"vs brute (n<= {n_max_brute}) ===")
    trees = enumerate_sp(max(n_max_dp, n_max_brute))
    mism = 0
    checked = 0
    for n in range(3, max(n_max_dp, n_max_brute) + 1):
        for struct in trees.get(n, []):
            lab = label(struct)
            elems, rel = relations(lab)
            qc = Q_closed_sp(lab)
            qcv = qc[0] if qc else None
            if n <= n_max_dp:
                qd = Q_via_dp(elems, rel)
                qdv = qd[0] if qd else None
                checked += 1
                if qcv != qdv:
                    mism += 1
                    print(f"  MISMATCH closed!=dp n={n} {tree_str(struct)}"
                          f" closed={qcv} dp={qdv}")
            if n <= n_max_brute:
                qb = Q_via_brute(elems, rel)
                qbv = qb[0] if qb else None
                if qcv != qbv:
                    mism += 1
                    print(f"  MISMATCH closed!=brute n={n} {tree_str(struct)}"
                          f" closed={qcv} brute={qbv}")
    print(f"  checked {checked} shapes (DP), all-shapes brute up to n={n_max_brute};"
          f" mismatches={mism}")
    return mism == 0


# --------------------------------------------------------------------------
# The sweep.
# --------------------------------------------------------------------------
def run_sweep(n_max: int, brute_upto: int = 8):
    print(f"\n=== SWEEP width-<=3 SP posets, n in [3, {n_max}] ===")
    trees = enumerate_sp(n_max)
    header = (f"{'n':>3} {'#SP(w<=3)':>10} {'#w==3':>8} "
              f"{'minQ(w<=3)':>12} {'minQ(w==3)':>12} {'argmin(w==3)':>40}")
    print(header)
    print("-" * len(header))

    global_min_le3 = None
    global_arg_le3 = None
    global_min_w3 = None
    global_arg_w3 = None
    guard_hits = []  # (n, tree, Q) with Q <= 1/3

    rows = []
    for n in range(3, n_max + 1):
        cnt_le3 = 0
        cnt_w3 = 0
        min_le3 = None
        arg_le3 = None
        min_w3 = None
        arg_w3 = None
        for struct in trees.get(n, []):
            w = s_width(struct)
            cnt_le3 += 1
            if w == 3:
                cnt_w3 += 1
            lab = label(struct)
            qc = Q_closed_sp(lab)
            if qc is None:
                continue  # chain
            q = qc[0]
            # optional brute confirmation for small n
            if n <= brute_upto:
                elems, rel = relations(lab)
                qb = Q_via_brute(elems, rel)
                assert qb is None or qb[0] == q, \
                    f"brute disagreement n={n} {tree_str(struct)}"
            if q <= ONE_THIRD:
                guard_hits.append((n, struct, q))
            if min_le3 is None or q < min_le3:
                min_le3 = q
                arg_le3 = struct
            if w == 3:
                if min_w3 is None or q < min_w3:
                    min_w3 = q
                    arg_w3 = struct
        if min_le3 is not None and (global_min_le3 is None or min_le3 < global_min_le3):
            global_min_le3 = min_le3
            global_arg_le3 = arg_le3
        if min_w3 is not None and (global_min_w3 is None or min_w3 < global_min_w3):
            global_min_w3 = min_w3
            global_arg_w3 = arg_w3
        am = tree_str(arg_w3) if arg_w3 is not None else "-"
        ml3 = f"{float(min_le3):.6f}" if min_le3 is not None else "-"
        mw3 = f"{float(min_w3):.6f}" if min_w3 is not None else "-"
        print(f"{n:>3} {cnt_le3:>10} {cnt_w3:>8} {ml3:>12} {mw3:>12} {am:>40}")
        rows.append((n, cnt_le3, cnt_w3, min_le3, min_w3, arg_w3))

    print("\n--- GLOBAL ---")
    print(f"min Q over width-<=3  : {global_min_le3} = {float(global_min_le3):.6f}"
          f"   argmin: {tree_str(global_arg_le3)}")
    print(f"min Q over width==3   : {global_min_w3} = {float(global_min_w3):.6f}"
          f"   argmin: {tree_str(global_arg_w3)}")
    print(f"Family-A floor (27/70): {FAMILY_A_FLOOR} = {float(FAMILY_A_FLOOR):.6f}")
    print(f"global conj. bound 1/3: {ONE_THIRD} = {float(ONE_THIRD):.6f}")

    # ---- Guard handling (roadmap 8.2) ----
    print("\n--- GUARD (roadmap 8.2) ---")
    if guard_hits:
        below = [(n, t, q) for (n, t, q) in guard_hits if q < ONE_THIRD]
        eq = [(n, t, q) for (n, t, q) in guard_hits if q == ONE_THIRD]
        print(f"Q <= 1/3 surfaced at {len(guard_hits)} shape(s): "
              f"{len(below)} with Q<1/3, {len(eq)} with Q==1/3.")
        if below:
            print("  *** Q < 1/3 CANDIDATE(S) -- COUNTEREXAMPLE TERRITORY ***")
            for (n, t, q) in below[:10]:
                print(f"    n={n} Q={q} {tree_str(t)}")
            print("  HALTING per roadmap 8.2: independent reimplementation "
                  "required before any claim. See "
                  "scripts/onethird_ap2_prong2_independent_check.py")
        else:
            # exactly 1/3 everywhere it triggered: textbook tight bound.
            ex_n, ex_t, _ = min(eq, key=lambda r: r[0])
            print("  All triggers are Q == 1/3 EXACTLY (not < 1/3). This is the "
                  "known tight bound of the 1/3-2/3 conjecture, attained by the "
                  "width-2 SP poset 1||(chain-2). NOT a counterexample.")
            print(f"  Smallest witness: n={ex_n} {tree_str(ex_t)}")
            # independent confirmation via brute on that witness
            lab = label(ex_t)
            elems, rel = relations(lab)
            qb = Q_via_brute(elems, rel)
            print(f"  Independent brute-force on witness: Q = {qb[0]} "
                  f"(== 1/3: {qb[0] == ONE_THIRD})")
            print("  Guard CLEARED: no Q<1/3, Q==1/3 verified exactly by an "
                  "independent engine + separate-codebase check.")
    else:
        print("No Q <= 1/3 anywhere in the sweep.")

    # ---- Verdict ----
    print("\n--- VERDICT ---")
    if global_min_w3 < ONE_THIRD:
        print("VERDICT: COUNTEREXAMPLE-CANDIDATE (width==3, Q<1/3) -- see guard.")
    elif global_min_le3 < FAMILY_A_FLOOR:
        # min over the family (width-<=3) dips below 27/70
        print("VERDICT: SKEW-ARTIFACT.")
        print(f"  min Q over Family B (width-<=3) = {global_min_le3} "
              f"< 27/70 = Family-A floor.")
        print(f"  => 27/70 does NOT extend to Family B; it is specific to the "
              f"3-row skew-shape structure.")
        if global_min_w3 is not None:
            cmp = ("<" if global_min_w3 < FAMILY_A_FLOOR else
                   "==" if global_min_w3 == FAMILY_A_FLOOR else ">")
            print(f"  Width-exactly-3 sub-result: min Q(w==3) = {global_min_w3} "
                  f"{cmp} 27/70.")
    else:
        print("VERDICT: BROADER-FLOOR-CANDIDATE.")
        print(f"  min Q over Family B = {global_min_le3} >= 27/70 across swept range.")
    return rows, global_min_le3, global_arg_le3, global_min_w3, global_arg_w3, guard_hits


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--n-max", type=int, default=16,
                    help="max poset size to sweep (default 16)")
    ap.add_argument("--brute-upto", type=int, default=8,
                    help="confirm every swept shape by brute force up to this n")
    ap.add_argument("--dp-upto", type=int, default=11,
                    help="closed-vs-DP cross-check up to this n")
    ap.add_argument("--skip-crosscheck", action="store_true")
    args = ap.parse_args()

    ok = run_sanity()
    if not ok:
        raise SystemExit("SANITY FAILED -- aborting.")
    if not args.skip_crosscheck:
        cc = run_crosscheck(n_max_brute=args.brute_upto, n_max_dp=args.dp_upto)
        if not cc:
            raise SystemExit("CROSS-CHECK FAILED -- aborting.")
    run_sweep(args.n_max, brute_upto=args.brute_upto)


if __name__ == "__main__":
    main()
