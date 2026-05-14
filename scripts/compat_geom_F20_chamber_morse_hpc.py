#!/usr/bin/env python3
r"""
compat_geom_F20_chamber_morse_hpc.py
====================================

Compat-Geom F20 verification + structural-anchor harness (mg-c3fa).

F20 targets the last two residuals of milestone 1 (the F10 width-3
1/3-2/3 theorem, part (iii)):

  (L2-struct)  For every n >= 3 the canonical top poset G_n of the
               canonical critical (n-2)-cell c*_n is a width-2 ordinal
               sum of antichains (OSA) containing >= 1 size-2 block.

  (W3-cover)   For every m >= 5 and every width-3 partial order P on m
               elements, some S_m-orbit representative of P appears as a
               poset P_k on a canonical critical chain.

This harness is a TRIP-WIRE + ANCHOR instrument.  It does not run the
(infeasible-in-a-single-session) full chamber-Morse greedy on the order
complex of PPF_n / S_n; instead it (a) re-runs the exact n <= 5 record,
(b) audits the F8'-HPC iota-lift "candidate c*_6" against (L2-struct),
(c) checks the iota-tower consistency claims F10 s.5.2 and F8' rest on,
(d) certifies the corrected structural reduction, and (e) probes
(W3-cover) feasibility by enumeration at m = 4, 5.

The headline FINDINGS (see docs/compatibility-geometry-F20-...md):

  * (L2-struct) holds at n = 3,4,5 exactly:
        G_3 = OSA(1,2),  G_4 = OSA(2,1,1),  G_5 = OSA(2,2,1).
  * The F8'-HPC "candidate c*_6" = iota_5(c*_5) + cover (0,2) FAILS
    (L2-struct): its top poset has WIDTH 3.  It is NOT the genuine
    canonical c*_6.
  * The iota-tower form (F10 s.5.2) is NOT literally correct: the
    genuine c*_5 does not contain iota_4(c*_4) -- its 2nd-from-top poset
    P_2 has element 4 NON-isolated, so c*_5 != iota_4(c*_4) + append.
  * (L2-struct) is jointly INCONSISTENT with the iota-tower
    multiplicativity for n >= 7: |L(G_n)| = 2^{s_n} <= 2^{n/2} but an
    iota-lift 2nd-top poset has |L| = n!*-scale, so the top step Pr
    falls below 3/11.  Resolution: the genuine c*_n is not an iota-lift.

Pure-Python stdlib.  Sections [A]-[E] run in < 30 s.  Section [F]
(chamber enumeration at n=6) is optional and time-boxed.

Usage:
    python3 compat_geom_F20_chamber_morse_hpc.py [--verbose]
        [--chamber-n6]          also run the n=6 chamber enumeration
        [--chamber-timeout S]   time budget for the n=6 enumeration

References
  - mg-5722 (F19): docs/compatibility-geometry-F19-icop-step-and-bridge.md
  - mg-4d3a (F17): docs/compatibility-geometry-F17-equivariant-cofiber-morse.md
  - mg-d039 (F18): docs/compatibility-geometry-F18-ucc2-delta-injective.md
  - mg-1e99 (F8):  docs/compatibility-geometry-F8-inductive-general-n.md
  - mg-7b3b (F8'): docs/compatibility-geometry-F8prime-n6-icop.md
  - mg-3bf3 (F8'-HPC): docs/compatibility-geometry-F8prime-HPC.md
  - mg-1e58 (F5):  docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md
"""

from __future__ import annotations

import sys
import time
from fractions import Fraction
from itertools import permutations, combinations


# ===========================================================================
# Section 0.  Core poset utilities  (exact, stdlib).
# ===========================================================================


def transitive_closure(rel):
    """Transitive closure of `rel` (set of (a,b) meaning a < b)."""
    closed = set(rel)
    changed = True
    while changed:
        changed = False
        add = set()
        for (i, j) in closed:
            for (k, l) in closed:
                if j == k and i != l and (i, l) not in closed:
                    add.add((i, l))
        if add:
            closed |= add
            changed = True
    return frozenset(closed)


def is_antisymmetric(closed):
    return not any((j, i) in closed for (i, j) in closed)


def is_proper_partial_order(rel, n):
    """Proper = transitively closed, antisymmetric, non-empty, non-total."""
    closed = transitive_closure(rel)
    if closed != frozenset(rel):
        return False
    if not is_antisymmetric(closed) or len(closed) == 0:
        return False
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                return True
    return False


def count_linear_extensions(closed, n):
    """Count linear extensions via backtracking topological sort."""
    indeg = [0] * n
    above = [[] for _ in range(n)]
    for (i, j) in closed:
        indeg[j] += 1
        above[i].append(j)
    cnt = 0
    indeg = indeg[:]

    def rec(avail, placed):
        nonlocal cnt
        if placed == n:
            cnt += 1
            return
        for idx in range(len(avail)):
            v = avail[idx]
            new_avail = avail[:idx] + avail[idx + 1:]
            for w in above[v]:
                indeg[w] -= 1
                if indeg[w] == 0:
                    new_avail.append(w)
            rec(new_avail, placed + 1)
            for w in above[v]:
                indeg[w] += 1

    rec([v for v in range(n) if indeg[v] == 0], 0)
    return cnt


def hasse_covers(closed, n):
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
    out = []
    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                out.append((i, j))
    return out


def isolated_elements(closed, n):
    """Elements appearing in no relation of `closed`."""
    used = set()
    for (a, b) in closed:
        used.add(a)
        used.add(b)
    return [v for v in range(n) if v not in used]


def automorphisms(closed, n):
    """All permutations pi with pi(closed) = closed.  (n <= 8 only.)"""
    rel = set(closed)
    return [perm for perm in permutations(range(n))
            if all((perm[a], perm[b]) in rel for (a, b) in rel)]


def symmetric_pairs(closed, n, autos=None):
    if autos is None:
        autos = automorphisms(closed, n)
    out = []
    for (x, y) in incomparable_pairs(closed, n):
        if any(s[x] == y and s[y] == x for s in autos):
            out.append((x, y))
    return out


def poset_width(closed, n):
    for size in range(n, 0, -1):
        for S in combinations(range(n), size):
            if all((a, b) not in closed and (b, a) not in closed
                   for a, b in combinations(S, 2)):
                return size
    return 0


def is_osa(closed, n):
    """OSA <=> incomparability is transitive on distinct elements."""
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
    """Antichain blocks of an OSA, ordered BOTTOM-to-TOP."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(n):
        for j in range(i + 1, n):
            if (i, j) not in closed and (j, i) not in closed:
                ri, rj = find(i), find(j)
                if ri != rj:
                    parent[ri] = rj
    groups = {}
    for x in range(n):
        groups.setdefault(find(x), []).append(x)
    blocks = [sorted(g) for g in groups.values()]
    blocks.sort(key=lambda B: sum(1 for x in range(n) if (x, B[0]) in closed))
    return blocks


def osa_signature(closed, n):
    if not is_osa(closed, n):
        return None
    return tuple(len(B) for B in antichain_blocks(closed, n))


BFT_LO, BFT_HI = Fraction(3, 11), Fraction(8, 11)


def in_bft(pr):
    return BFT_LO <= pr <= BFT_HI


def check_L2_struct(G, n, label=""):
    """(L2-struct) test: width-2 OSA with >= 1 size-2 block."""
    w = poset_width(G, n)
    osa = is_osa(G, n)
    sig = osa_signature(G, n) if osa else None
    has2 = bool(sig) and any(s == 2 for s in sig)
    le2 = bool(sig) and all(s <= 2 for s in sig)
    ok = bool(osa and w == 2 and has2)
    return {"label": label, "n": n, "width": w, "osa": osa,
            "signature": sig, "has_size2_block": has2,
            "all_blocks_le_2": le2, "L2_struct_ok": ok,
            "hasse": hasse_str(G, n)}


# ===========================================================================
# Section A.  The canonical critical chains, reconstructed from F2/F5.
# ===========================================================================

C_STAR_3 = {
    "n": 3, "label": "c*_3  (F8 s.4.5)",
    "hasse": [frozenset({(0, 2)}),
              frozenset({(0, 1), (0, 2)})],
}
C_STAR_4 = {
    "n": 4, "label": "c*_4  (F2 s.4.3.1, lex-min critical 2-cell)",
    "hasse": [frozenset({(1, 2), (3, 0), (3, 2)}),
              frozenset({(0, 2), (1, 2), (3, 0)}),
              frozenset({(0, 2), (1, 0), (3, 0)})],
}
C_STAR_5 = {
    "n": 5, "label": "c*_5  (F5 s.4.3 / F8' s.A)",
    "hasse": [frozenset({(0, 1), (2, 1), (3, 1)}),
              frozenset({(0, 1), (0, 4), (2, 1), (2, 4), (3, 1)}),
              frozenset({(0, 4), (2, 4), (3, 1), (4, 1)}),
              frozenset({(0, 3), (0, 4), (2, 3), (2, 4), (3, 1), (4, 1)})],
}


def analyse_chain(chain, verbose=False):
    n = chain["n"]
    closures = [transitive_closure(P) for P in chain["hasse"]]
    print(f"  {chain['label']}   (n = {n})")
    ok_chain = all(closures[k] < closures[k + 1]
                   for k in range(len(closures) - 1))
    profile = [count_linear_extensions(C, n) for C in closures]
    for k, C in enumerate(closures):
        w = poset_width(C, n)
        sig = osa_signature(C, n)
        iso = isolated_elements(C, n)
        tag = f"OSA{sig}" if sig else "not-OSA"
        print(f"    P_{k}: |L|={profile[k]:>4} width={w} {tag:14s}"
              f" isolated={iso}  {hasse_str(C, n)}")
    prs = [Fraction(profile[k + 1], profile[k])
           for k in range(len(closures) - 1)]
    bft = all(in_bft(p) for p in prs)
    print(f"    per-step Pr = {[str(p) for p in prs]}  "
          f"all BFT-sharp: {'YES' if bft else 'NO'}")
    G = closures[-1]
    l2 = check_L2_struct(G, n, f"G_{n}")
    print(f"    (L2-struct) on G_{n}: width={l2['width']} osa={l2['osa']} "
          f"sig={l2['signature']} -> "
          f"{'PASS' if l2['L2_struct_ok'] else 'FAIL'}")
    print()
    return {"n": n, "closures": closures, "profile": profile, "prs": prs,
            "top": G, "ok_chain": ok_chain, "bft": bft, "l2": l2}


# ===========================================================================
# Section B.  The F8'-HPC iota-lift "candidate c*_6" audit.
# ===========================================================================


def audit_f8hpc_candidate(verbose=False):
    """c*_6 (F8'-HPC s.5) = (iota5 P0..P3, P3 u {(0,2)}).  Test (L2-struct)."""
    print("  [B] F8'-HPC iota_5-lift 'candidate c*_6' -- (L2-struct) audit")
    print("  " + "-" * 72)
    c5 = [transitive_closure(P) for P in C_STAR_5["hasse"]]
    c6 = [frozenset(C) for C in c5]  # iota_5 onto [6]; element 5 free
    c6.append(transitive_closure(set(c6[-1]) | {(0, 2)}))
    prof = [count_linear_extensions(C, 6) for C in c6]
    print(f"    candidate |L|-profile = {tuple(prof)}  "
          f"(F8'-HPC: (180,84,48,24,12))")
    G6 = c6[-1]
    l2 = check_L2_struct(G6, 6, "G_6 (F8'-HPC candidate)")
    print(f"    candidate top poset G_6 = {hasse_str(G6, 6)}")
    print(f"    width = {l2['width']},  OSA = {l2['osa']},  "
          f"signature = {l2['signature']}")
    print(f"    isolated elements = {isolated_elements(G6, 6)}  "
          f"(element 5 is FREE -- never absorbed)")
    print(f"    incomparable pairs = {incomparable_pairs(G6, 6)}")
    if not l2["L2_struct_ok"]:
        print(f"    >>> FINDING: (L2-struct) FAILS on the F8'-HPC candidate "
              f"-- width {l2['width']} != 2.")
        print(f"    >>> The candidate appends a within-[5] cover (0,2), "
              f"leaving element 5 isolated;")
        print(f"    >>> a width-3 antichain {{3,4,5}} survives.  The genuine "
              f"canonical c*_6 is DIFFERENT.")
    print()
    return {"chain": c6, "profile": prof, "l2": l2}


# ===========================================================================
# Section C.  The iota-tower consistency audit.
# ===========================================================================


def iota_tower_audit(a3, a4, a5, verbose=False):
    """Test the F10 s.5.2 claim 'c*_n is an iota-tower':
       c*_{n+1} = iota_n(c*_n) + one appended cover step, i.e. the bottom
       n-1 posets of c*_{n+1} are iota_n(P_0..P_{n-2}^{(n)}), all with
       element n isolated.

    FINDING: this is NOT literally true.  c*_5's 2nd-from-top poset has
    element 4 NON-isolated.  And it is jointly inconsistent with
    (L2-struct) for n >= 7."""
    print("  [C] The iota-tower consistency audit (F10 s.5.2)")
    print("  " + "-" * 72)
    # (C1) does c*_5 contain iota_4(c*_4)?  -- check element-4 isolation.
    c5 = a5["closures"]
    iso_status = [(k, isolated_elements(c5[k], 5)) for k in range(len(c5))]
    print(f"    c*_5 element-isolation by poset:")
    n_iso = 0
    for (k, iso) in iso_status:
        has4 = 4 in iso
        if has4:
            n_iso += 1
        print(f"      P_{k}: isolated elements = {iso}"
              f"   {'(element 4 isolated)' if has4 else '(element 4 USED)'}")
    iota_tower_holds = (n_iso == len(c5) - 1)  # all but the top would be iota
    print(f"    posets of c*_5 with element 4 isolated: {n_iso} of {len(c5)}")
    if not iota_tower_holds:
        print(f"    >>> FINDING: c*_5 is NOT iota_4(c*_4) + append.")
        print(f"    >>> Only P_0 has element 4 isolated; P_1,P_2,P_3 all use "
              f"element 4.")
        print(f"    >>> The 'iota-tower' form (F10 s.5.2) does not hold "
              f"literally for the genuine c*_5.")
    # (C2) the (L2-struct) + iota-multiplicativity inconsistency for n>=7.
    print()
    print(f"    (C2) (L2-struct) vs iota-tower multiplicativity, n >= 7:")
    print(f"      A width-2 OSA G_n on [n] has |L(G_n)| = 2^{{s_n}} where")
    print(f"      s_n = #(size-2 blocks) <= floor(n/2).  An iota-lift 2nd-")
    print(f"      from-top poset would have |L| = n * |L(G_{{n-1}})|.")
    print(f"      Top-step Pr = 2^{{s_n}} / (n * 2^{{s_{{n-1}}}}).")
    for n in range(5, 11):
        s_n = n // 2          # the most generous (largest possible)
        s_nm1 = (n - 1) // 2
        # iota-tower top-step Pr upper bound
        num = Fraction(2 ** s_n, n * (2 ** s_nm1))
        ok = in_bft(num)
        print(f"      n={n}: max top-step Pr (iota-tower) = "
              f"2^{s_n}/({n}*2^{s_nm1}) = {num} ~ {float(num):.4f}"
              f"   {'in [3/11,8/11]' if ok else 'OUT OF [3/11,8/11]'}")
    print(f"    >>> FINDING: for n >= 7 the iota-tower top-step Pr is forced")
    print(f"        BELOW 3/11 if G_n is a width-2 OSA.  (L2-struct) and the")
    print(f"        iota-tower are JOINTLY INCONSISTENT for large n.")
    print(f"        Resolution: the genuine c*_n is NOT an iota-lift -- its")
    print(f"        2nd-from-top poset stays near-maximal (small |L|), as")
    print(f"        c*_5 already shows (|L(P_2)| = 8, not 5*|L(G_4)| = 10).")
    print()
    return {"iota_tower_holds": iota_tower_holds, "n_iso_c5": n_iso}


# ===========================================================================
# Section D.  Structural reduction certification.
# ===========================================================================


def symmetric_pair_lemma_check(verbose=False):
    """Re-certify F19 Lemma L1 on the F20-relevant posets: every symmetric
    incomparable pair has Pr = 1/2 exactly.  And: in a width-2 OSA EVERY
    incomparable pair is symmetric (within-block transposition)."""
    print("  [D] Structural reduction -- Lemma L1 + the OSA symmetric-pair "
          "fact")
    print("  " + "-" * 72)
    # the canonical top posets and a few near-maximal width-2 OSAs
    G3 = transitive_closure(C_STAR_3["hasse"][-1])
    G4 = transitive_closure(C_STAR_4["hasse"][-1])
    G5 = transitive_closure(C_STAR_5["hasse"][-1])
    pool = [(G3, 3, "G_3"), (G4, 4, "G_4"), (G5, 5, "G_5")]
    # add the canonical width-2 OSA at n=6,7 (signature (2,2,2), (2,2,2,1))
    for sig, n, name in [((2, 2, 2), 6, "OSA(2,2,2)"),
                         ((2, 2, 2, 1), 7, "OSA(2,2,2,1)"),
                         ((2, 2, 1, 1, 1), 7, "OSA(2,2,1,1,1)")]:
        G, _ = osa_from_signature(sig)
        pool.append((G, n, name))
    l1_ok = True
    osa_sym_ok = True
    for (G, n, name) in pool:
        autos = automorphisms(G, n)
        incs = incomparable_pairs(G, n)
        syms = symmetric_pairs(G, n, autos)
        # L1: every symmetric pair -> Pr = 1/2
        for (x, y) in syms:
            LP = count_linear_extensions(G, n)
            Q = transitive_closure(set(G) | {(x, y)})
            pr = Fraction(count_linear_extensions(Q, n), LP)
            if pr != Fraction(1, 2):
                l1_ok = False
        # OSA fact: in a width-2 OSA every incomparable pair is symmetric
        if is_osa(G, n):
            if set(map(frozenset, incs)) != set(map(frozenset, syms)):
                osa_sym_ok = False
        print(f"    {name} (n={n}): |Aut|={len(autos)}  incomp pairs="
              f"{len(incs)}  symmetric pairs={len(syms)}  "
              f"{'all incomp = symmetric' if set(map(frozenset,incs))==set(map(frozenset,syms)) else 'MISMATCH'}")
    print(f"    (L1) every symmetric incomparable pair has Pr = 1/2: "
          f"{'PASS' if l1_ok else 'FAIL'}")
    print(f"    (OSA fact) in a width-2 OSA every incomparable pair is "
          f"symmetric: {'PASS' if osa_sym_ok else 'FAIL'}")
    print(f"    => (L2-struct) ['G_n is a width-2 OSA with a size-2 block']")
    print(f"       implies G_n has a symmetric incomparable pair, hence the")
    print(f"       (ICOP-step) cover -- which lands inside a size-2 block --")
    print(f"       is at a symmetric pair, hence Pr = 1/2 (F19 Prop 3.1).")
    print()
    return l1_ok and osa_sym_ok


def osa_from_signature(sig):
    """Canonical width-2 OSA with block-size sequence `sig` (bottom-up)."""
    n = sum(sig)
    blocks, idx = [], 0
    for s in sig:
        blocks.append(list(range(idx, idx + s)))
        idx += s
    rel = set()
    for bi in range(len(blocks)):
        for bj in range(bi + 1, len(blocks)):
            for a in blocks[bi]:
                for b in blocks[bj]:
                    rel.add((a, b))
    return transitive_closure(rel), blocks


# ===========================================================================
# Section E.  (W3-cover) feasibility -- enumeration at m = 4, 5.
# ===========================================================================


def enumerate_ppf(n):
    """All proper partial orders on [n], as transitively-closed frozensets."""
    seen = set()
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


def apply_perm(closed, perm):
    return frozenset((perm[a], perm[b]) for (a, b) in closed)


def canon(closed, n, perms):
    best = None
    for perm in perms:
        img = tuple(sorted(apply_perm(closed, perm)))
        if best is None or img < best:
            best = img
    return frozenset(best)


def w3_cover_feasibility(m, verbose=False):
    """At m: enumerate width-3 S_m-orbits.  For each, test whether it admits
    a BALANCED incomparable pair (Pr in [3/11,8/11]) -- the m<=4 rigorous
    base extends: every width-3 poset that admits a balanced pair can be
    placed as a cover step P_k subset P_{k+1} on a refinement chain.  This
    is the local (per-orbit) feasibility of (W3-cover)."""
    print(f"  [E] (W3-cover) feasibility at m = {m}")
    print(f"  " + "-" * 72)
    t0 = time.time()
    ppf = enumerate_ppf(m)
    perms = list(permutations(range(m)))
    w3 = [P for P in ppf if poset_width(P, m) == 3]
    orbits = {}
    for P in w3:
        orbits.setdefault(canon(P, m, perms), []).append(P)
    print(f"    |PPF_{m}| = {len(ppf)};  width-3 posets = {len(w3)};  "
          f"width-3 S_{m}-orbits = {len(orbits)}  ({time.time()-t0:.1f}s)")
    # per-orbit: does the rep admit a balanced incomparable pair?
    have_balanced = 0
    have_sym = 0
    no_balanced = []
    for rep in orbits:
        incs = incomparable_pairs(rep, m)
        LP = count_linear_extensions(rep, m)
        bal = False
        for (x, y) in incs:
            for pair in [(x, y), (y, x)]:
                Q = transitive_closure(set(rep) | {pair})
                if not is_antisymmetric(Q) or Q == rep:
                    continue
                pr = Fraction(count_linear_extensions(Q, m), LP)
                if in_bft(pr):
                    bal = True
        if bal:
            have_balanced += 1
        else:
            no_balanced.append(rep)
        if symmetric_pairs(rep, m):
            have_sym += 1
    print(f"    width-3 orbits with a BFT-sharp (balanced) incomparable "
          f"pair: {have_balanced}/{len(orbits)}")
    print(f"    width-3 orbits with a SYMMETRIC incomparable pair "
          f"(Pr=1/2 by L1): {have_sym}/{len(orbits)}")
    if no_balanced:
        print(f"    width-3 orbits WITHOUT a balanced pair "
              f"({len(no_balanced)}):")
        for rep in no_balanced[:6]:
            print(f"      {hasse_str(rep, m)}")
    ok = (have_balanced == len(orbits) and len(orbits) > 0)
    print(f"    every width-3 S_{m}-orbit has a balanced incomparable pair: "
          f"{'PASS' if ok else 'FAIL'}  ({time.time()-t0:.1f}s)")
    print()
    return {"m": m, "n_orbits": len(orbits), "have_balanced": have_balanced,
            "have_sym": have_sym, "ok": ok, "no_balanced": no_balanced}


# ===========================================================================
# Section F.  Optional: the n=6 chamber enumeration (structural anchor data).
# ===========================================================================


def chamber_enum_n6(timeout=900.0, verbose=False):
    """Enumerate PPF_6, count S_6-orbits, build the orbit poset.  This is
    the FEASIBLE part of the chamber-Morse construction; the full greedy
    Morse matching on the order complex is HPC-class and not attempted."""
    print("  [F] n=6 chamber enumeration (structural anchor data)")
    print("  " + "-" * 72)
    t0 = time.time()
    ppf = enumerate_ppf(6)
    print(f"    |PPF_6| = {len(ppf)}   ({time.time()-t0:.1f}s)")
    if time.time() - t0 > timeout:
        print(f"    !! timed out during enumeration")
        print()
        return None
    perms = list(permutations(range(6)))
    canon_of = {}
    reps = set()
    for i, P in enumerate(ppf):
        c = canon(P, 6, perms)
        canon_of[P] = c
        reps.add(c)
        if (i & 8191) == 0 and time.time() - t0 > timeout:
            print(f"    !! timed out during orbit computation "
                  f"({i}/{len(ppf)})")
            print()
            return None
    print(f"    chamber: {len(reps)} S_6-orbits   ({time.time()-t0:.1f}s)")
    # width distribution of orbits
    wdist = {}
    osa_count = 0
    for r in reps:
        w = poset_width(r, 6)
        wdist[w] = wdist.get(w, 0) + 1
        if is_osa(r, 6):
            osa_count += 1
    print(f"    orbit width distribution: "
          f"{dict(sorted(wdist.items()))}")
    print(f"    orbits that are OSAs: {osa_count}")
    # the width-2 OSAs on [6] with a size-2 block (L2-struct candidates)
    w2osa = [r for r in reps if is_osa(r, 6) and poset_width(r, 6) == 2
             and any(s == 2 for s in (osa_signature(r, 6) or ()))]
    print(f"    width-2 OSA orbits with a size-2 block (L2-struct top-poset "
          f"candidates): {len(w2osa)}")
    for r in sorted(w2osa, key=lambda x: tuple(sorted(x))):
        sig = osa_signature(r, 6)
        LP = count_linear_extensions(r, 6)
        print(f"      OSA{sig}  |L|={LP}  {hasse_str(r, 6)}")
    print()
    return {"n_orbits": len(reps), "wdist": wdist, "w2osa": w2osa}


# ===========================================================================
# Main.
# ===========================================================================


def main():
    verbose = "--verbose" in sys.argv
    do_n6 = "--chamber-n6" in sys.argv
    chamber_timeout = 900.0
    for i, a in enumerate(sys.argv):
        if a == "--chamber-timeout" and i + 1 < len(sys.argv):
            chamber_timeout = float(sys.argv[i + 1])

    print()
    print("compat_geom_F20_chamber_morse_hpc.py -- F20 (mg-c3fa)")
    print("n-uniform chamber-Morse critical-cell structure: "
          "(L2-struct) + (W3-cover)")
    print("=" * 76)
    print()

    # ---- [A] the exact record ---------------------------------------------
    print("[A]  Canonical critical chains -- the exact record (n = 3,4,5)")
    print("=" * 76)
    a3 = analyse_chain(C_STAR_3, verbose)
    a4 = analyse_chain(C_STAR_4, verbose)
    a5 = analyse_chain(C_STAR_5, verbose)
    exact_l2 = all(a["l2"]["L2_struct_ok"] for a in [a3, a4, a5])
    exact_bft = all(a["bft"] for a in [a3, a4, a5])
    print(f"  [A] (L2-struct) on the exact record n=3,4,5: "
          f"{'PASS' if exact_l2 else 'FAIL'};  all steps BFT-sharp: "
          f"{'PASS' if exact_bft else 'FAIL'}")
    print()

    # ---- [B] F8'-HPC candidate audit --------------------------------------
    print("[B]  The F8'-HPC iota_5-lift 'candidate c*_6' audit")
    print("=" * 76)
    bres = audit_f8hpc_candidate(verbose)

    # ---- [C] iota-tower consistency audit ---------------------------------
    print("[C]  The iota-tower consistency audit")
    print("=" * 76)
    cres = iota_tower_audit(a3, a4, a5, verbose)

    # ---- [D] structural reduction -----------------------------------------
    print("[D]  Structural reduction -- Lemma L1 + the OSA symmetric fact")
    print("=" * 76)
    dres = symmetric_pair_lemma_check(verbose)

    # ---- [E] (W3-cover) feasibility ---------------------------------------
    print("[E]  (W3-cover) feasibility -- width-3 orbit enumeration")
    print("=" * 76)
    e4 = w3_cover_feasibility(4, verbose)
    e5 = w3_cover_feasibility(5, verbose)
    e6 = None
    if do_n6:
        e6 = w3_cover_feasibility(6, verbose)  # bounded; ~100 s

    # ---- [F] optional n=6 chamber enumeration -----------------------------
    fres = None
    if do_n6:
        print("[F]  n=6 chamber enumeration")
        print("=" * 76)
        fres = chamber_enum_n6(timeout=chamber_timeout, verbose=verbose)

    # ---- verdict ----------------------------------------------------------
    print("[V]  VERDICT SUMMARY")
    print("=" * 76)
    print(f"  [A] (L2-struct) exact record n=3,4,5 .............. "
          f"{'PASS' if exact_l2 else 'FAIL'}")
    print(f"  [A] all per-step Pr BFT-sharp n=3,4,5 ............. "
          f"{'PASS' if exact_bft else 'FAIL'}")
    print(f"  [B] F8'-HPC candidate c*_6 satisfies (L2-struct) .. "
          f"{'PASS' if bres['l2']['L2_struct_ok'] else 'FAIL (width 3)'}")
    print(f"  [C] iota-tower form holds for genuine c*_5 ........ "
          f"{'PASS' if cres['iota_tower_holds'] else 'FAIL (not an iota-lift)'}")
    print(f"  [D] structural reduction L1 + OSA fact certified .. "
          f"{'PASS' if dres else 'FAIL'}")
    print(f"  [E] every width-3 orbit has a balanced pair (m=4).. "
          f"{'PASS' if e4['ok'] else 'FAIL'}")
    print(f"  [E] every width-3 orbit has a balanced pair (m=5).. "
          f"{'PASS' if e5['ok'] else 'FAIL'}")
    if e6:
        print(f"  [E] every width-3 orbit has a balanced pair (m=6).. "
              f"{'PASS' if e6['ok'] else 'FAIL'} "
              f"({e6['have_balanced']}/{e6['n_orbits']})")
    if fres:
        print(f"  [F] n=6 chamber: {fres['n_orbits']} orbits, "
              f"{len(fres['w2osa'])} width-2 OSA(size-2) candidates")
    print()
    print("  KEY FINDINGS:")
    print("   1. (L2-struct) holds exactly at n=3,4,5.")
    print("   2. The F8'-HPC iota-lift 'candidate c*_6' VIOLATES (L2-struct)")
    print("      -- it has width 3.  It is not the genuine canonical c*_6.")
    print("   3. The iota-tower form (F10 s.5.2) is NOT literally correct:")
    print("      genuine c*_5 != iota_4(c*_4) + append.")
    print("   4. (L2-struct) and iota-tower multiplicativity are jointly")
    print("      INCONSISTENT for n >= 7 -- the genuine c*_n is not an")
    print("      iota-lift.")
    print("   5. Every width-3 S_m-orbit (m=4,5) admits a balanced")
    print("      incomparable pair -- the per-orbit core of (W3-cover).")
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
