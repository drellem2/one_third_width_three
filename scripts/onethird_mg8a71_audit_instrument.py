#!/usr/bin/env python3
"""mg-8a71 — INDEPENDENT AUDIT instrument for the mg-fccb repair of
docs/OneThird-L1b-Spread-Locality.md §2.3 (inequality-direction error).

Built from the DEFINITIONS in §0/§2.3 of that document, not from the repair's
script (scripts/onethird_mgfccb_direction_check.py) and not from the mg-d112
audit report.  It is deliberately a *different* instrument: it re-derives the
same direction, and it additionally

  (a) re-verifies the two exact identities §2.3 rests on — (F1) Σ_x m_x =
      2E[inv_e] and (★) E[Σ disp²] = 2E[inv_e] + Cross — which the repair did
      not re-check and which, if false, would make the corrected §2.3 statement
      unsound in a way the direction check cannot see;
  (b) tests the STRUCK sentence's *operative content* as a finite statement and
      counts the population on which it fails, rather than only exhibiting the
      one witness W_m;
  (c) checks b_x = m_x at the e-MAXIMUM as well as the e-minimum (the repair
      pins only the e-min; if the e-max were also an equality point, §3.1's
      falsifier would have a second site nobody has named);
  (d) recomputes the W_m closed forms from the poset itself, by exhaustive
      enumeration of L(W_m), rather than from the closed form.

Exact rational arithmetic (fractions.Fraction).  Standard library only — no
numpy (this host has numpy only on /usr/bin/python3).  ~20 s for n <= 5.

Notation, fixed from §0/§2.3 of the target document:
    e            a reference linear extension of P; erank_e(x) its 0-indexed rank
    pos_sigma(x) 0-indexed position of x in a uniform linear extension sigma
    disp(x)      pos_sigma(x) - erank_e(x)
    A_x          #{y : erank(y) > erank(x), pos(y) < pos(x)}   (e-above, before x)
    B_x          #{y : erank(y) < erank(x), pos(y) > pos(x)}   (e-below, after x)
    m_x          E[A_x] + E[B_x]              per-element inversion DEGREE (a sum)
    b_x          |E[A_x] - E[B_x]| = |E[disp(x)]|   per-element BIAS (a difference)

Exits non-zero on any assertion failure.
"""

import itertools
import sys
from fractions import Fraction

# ----------------------------------------------------------------- posets ---


def all_posets(n):
    """Every labeled partial order on {0,...,n-1}, as a frozenset of strict pairs.

    Enumerated by assigning each unordered pair one of three states and keeping
    the transitively closed assignments.  No isomorphism reduction: the sweep is
    over LABELED posets, which is the population the direction claim quantifies
    over (it is a per-element claim, and relabeling moves elements).
    """
    pairs = list(itertools.combinations(range(n), 2))
    for choice in itertools.product((0, 1, 2), repeat=len(pairs)):
        rel = set()
        for (a, b), c in zip(pairs, choice):
            if c == 1:
                rel.add((a, b))
            elif c == 2:
                rel.add((b, a))
        # transitivity
        ok = True
        for (a, b) in rel:
            for (c, d) in rel:
                if b == c and a != d and (a, d) not in rel:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            yield frozenset(rel)


def linear_extensions(n, rel):
    """All linear extensions of `rel`, as tuples (element at position 0, 1, ...).

    Grown by repeatedly emitting a currently-minimal element, NOT by filtering
    all n! permutations: W_m needs n = m+1 up to 11, where the filtering form
    would enumerate 39 916 800 permutations to return 11 of them.
    """
    preds = {x: set() for x in range(n)}
    for (a, b) in rel:
        preds[b].add(a)
    out = []
    prefix = []
    placed = set()

    def grow():
        if len(prefix) == n:
            out.append(tuple(prefix))
            return
        for x in range(n):
            if x not in placed and preds[x] <= placed:
                placed.add(x)
                prefix.append(x)
                grow()
                prefix.pop()
                placed.discard(x)

    grow()
    return out


# ------------------------------------------------------- the §2.3 objects ---


def stats(n, exts, e):
    """Exact E[A_x], E[B_x], m_x, b_x, E[disp^2], E[inv_e], Cross for reference e.

    exts: list of all linear extensions of P (uniform law).  e: reference order.
    """
    N = len(exts)
    erank = {x: i for i, x in enumerate(e)}
    EA = [Fraction(0) for _ in range(n)]
    EB = [Fraction(0) for _ in range(n)]
    Edisp = [Fraction(0) for _ in range(n)]
    Edisp2 = [Fraction(0) for _ in range(n)]
    Einv = Fraction(0)
    # E[I_xy I_xz] accumulator for the (star) identity
    joint = {}
    for sigma in exts:
        pos = {x: i for i, x in enumerate(sigma)}
        inv_here = 0
        inverted = [set() for _ in range(n)]  # inverted[x] = partners y
        for x, y in itertools.combinations(range(n), 2):
            # {x,y} is e-inverted in sigma iff their e-order and sigma-order differ
            if (erank[x] < erank[y]) != (pos[x] < pos[y]):
                inv_here += 1
                inverted[x].add(y)
                inverted[y].add(x)
        Einv += Fraction(inv_here, N)
        for x in range(n):
            a = sum(1 for y in inverted[x] if erank[y] > erank[x])
            b = sum(1 for y in inverted[x] if erank[y] < erank[x])
            EA[x] += Fraction(a, N)
            EB[x] += Fraction(b, N)
            d = pos[x] - erank[x]
            Edisp[x] += Fraction(d, N)
            Edisp2[x] += Fraction(d * d, N)
            for y in inverted[x]:
                for z in inverted[x]:
                    if y != z:
                        key = (x, y, z)
                        joint[key] = joint.get(key, Fraction(0)) + Fraction(1, N)
    m = [EA[x] + EB[x] for x in range(n)]
    bias = [abs(EA[x] - EB[x]) for x in range(n)]
    cross = Fraction(0)
    for (x, y, z), p in joint.items():
        eps_y = 1 if erank[y] > erank[x] else -1
        eps_z = 1 if erank[z] > erank[x] else -1
        cross += eps_y * eps_z * p
    return {
        "EA": EA, "EB": EB, "m": m, "b": bias,
        "Edisp": Edisp, "Edisp2": Edisp2,
        "Einv": Einv, "Cross": cross,
        "SumEdisp2": sum(Edisp2), "erank": erank,
    }


# --------------------------------------------------------------- the sweep ---


def sweep(ns):
    tot_triples = 0          # (P, e, x)
    tot_pairs = 0            # (P, e)
    tot_posets = 0
    viol_direction = 0       # b_x > m_x                      -- must be 0
    strict = 0               # b_x < m_x                      -- the lossy cases
    equal = 0                # b_x = m_x
    emin_equal = 0
    emin_total = 0
    emax_equal = 0
    emax_total = 0
    viol_F1 = 0              # Sum_x m_x != 2 E[inv_e]        -- must be 0
    viol_star = 0            # E[Sum disp^2] != 2E[inv] + Cross -- must be 0
    viol_jensen = 0          # E[disp^2] < (E disp)^2         -- must be 0
    viol_det_upper = 0       # Sum b_x^2 > (max m)*2E[inv]    -- must be 0 (the VALID half)
    struck_fails = 0         # Sum_x b_x^2 < (max_x m_x)^2    -- the STRUCK inference's content
    struck_holds = 0
    struck_witness = None
    per_n = {}
    for n in ns:
        n_posets = n_pairs = n_triples = 0
        for rel in all_posets(n):
            exts = linear_extensions(n, rel)
            if not exts:
                continue
            n_posets += 1
            for e in exts:                      # EVERY reference linear extension
                st = stats(n, exts, e)
                n_pairs += 1
                n_triples += n
                # (F1)
                if sum(st["m"]) != 2 * st["Einv"]:
                    viol_F1 += 1
                # (star)
                if st["SumEdisp2"] != 2 * st["Einv"] + st["Cross"]:
                    viol_star += 1
                maxm = max(st["m"])
                sum_b2 = sum(bb * bb for bb in st["b"])
                if sum_b2 > maxm * 2 * st["Einv"]:
                    viol_det_upper += 1
                # the struck inference, as a finite statement
                if maxm > 0:
                    if sum_b2 < maxm * maxm:
                        struck_fails += 1
                        if struck_witness is None:
                            struck_witness = (n, sorted(rel), e,
                                              str(maxm), str(sum_b2))
                    else:
                        struck_holds += 1
                for x in range(n):
                    if st["b"][x] > st["m"][x]:
                        viol_direction += 1
                    elif st["b"][x] == st["m"][x]:
                        equal += 1
                    else:
                        strict += 1
                    if st["Edisp2"][x] < st["Edisp"][x] ** 2:
                        viol_jensen += 1
                xmin = e[0]
                xmax = e[-1]
                emin_total += 1
                emax_total += 1
                if st["b"][xmin] == st["m"][xmin]:
                    emin_equal += 1
                if st["b"][xmax] == st["m"][xmax]:
                    emax_equal += 1
        per_n[n] = (n_posets, n_pairs, n_triples)
        tot_posets += n_posets
        tot_pairs += n_pairs
        tot_triples += n_triples
    return locals()


# ------------------------------------------------------------------- W_m ----


def W(m):
    """W_m = C_m (+) C_1: chain c_0 < ... < c_{m-1} (elements 0..m-1) plus z = m."""
    rel = set()
    for i in range(m):
        for j in range(i + 1, m):
            rel.add((i, j))
    return frozenset(rel)


def wm_report(m):
    """Recompute the repair's W_m closed forms by exhaustive enumeration."""
    n = m + 1
    rel = W(m)
    exts = linear_extensions(n, rel)
    s = m // 2
    # e places z (element m) at e-rank s: c_0..c_{s-1}, z, c_s..c_{m-1}
    e = tuple(list(range(s)) + [m] + list(range(s, m)))
    assert all(e.index(a) < e.index(b) for (a, b) in rel), "e is not a linear extension"
    st = stats(n, exts, e)
    z = m
    sum_b2 = sum(bb * bb for bb in st["b"])
    var_z = st["Edisp2"][z] - st["Edisp"][z] ** 2
    return {
        "m": m, "n": n, "num_ext": len(exts),
        "m_z": st["m"][z], "b_z": st["b"][z], "Einv": st["Einv"],
        "sum_b2": sum_b2,
        "ratio_det": sum_b2 / st["Einv"] if st["Einv"] else None,
        "var_z": var_z,
        "SumEdisp2": st["SumEdisp2"],
        "ratio_B": st["SumEdisp2"] / st["Einv"] if st["Einv"] else None,
        "max_m": max(st["m"]),
    }


def main():
    ns = [3, 4, 5]
    if len(sys.argv) > 1:
        ns = [int(a) for a in sys.argv[1].split(",")]
    print("=" * 78)
    print("mg-8a71 independent audit instrument — mg-fccb §2.3 direction repair")
    print("=" * 78)

    print("\n[1] W_m = C_m (+) C_1, e placing z at e-rank m/2 — closed forms recomputed")
    print("    (the repair's witness; forms re-derived here from L(W_m) itself)")
    print(f"    {'m':>3} {'|L|':>4} {'m_z':>12} {'b_z':>4} {'E[inv_e]':>12} "
          f"{'Sum b^2':>14} {'det ratio':>9} {'Var(pos z)':>10} {'(B) ratio':>10}")
    bad_wm = 0
    for m in (2, 4, 6, 8, 10):
        r = wm_report(m)
        s = m // 2
        want_mz = Fraction(s * (s + 1), 2 * s + 1)
        want_b2 = Fraction(s * (s + 1), 3 * (2 * s + 1))
        want_var = Fraction(m * (m + 2), 12)
        ok = (r["m_z"] == want_mz and r["Einv"] == want_mz and r["b_z"] == 0
              and r["sum_b2"] == want_b2 and r["ratio_det"] == Fraction(1, 3)
              and r["var_z"] == want_var)
        bad_wm += 0 if ok else 1
        print(f"    {m:>3} {r['num_ext']:>4} {str(r['m_z']):>12} {str(r['b_z']):>4} "
              f"{str(r['Einv']):>12} {str(r['sum_b2']):>14} "
              f"{str(r['ratio_det']):>9} {str(r['var_z']):>10} "
              f"{str(r['ratio_B']):>10}  {'OK' if ok else 'MISMATCH'}")
    print(f"    closed forms m_z=s(s+1)/(2s+1), Sum b^2=s(s+1)/(3(2s+1)), "
          f"Var=m(m+2)/12, det ratio=1/3: mismatches = {bad_wm}")

    print(f"\n[2] exhaustive sweep over LABELED posets on n in {ns},")
    print("    EVERY reference linear extension, exact rational arithmetic")
    R = sweep(ns)
    for n in ns:
        p, pr, t = R["per_n"][n]
        print(f"    n={n}: {p:>5} posets, {pr:>6} (poset, reference-order) pairs, "
              f"{t:>6} (poset, order, element) triples")
    print(f"    TOTAL: {R['tot_posets']} posets, {R['tot_pairs']} pairs, "
          f"{R['tot_triples']} triples")
    # The population NAMED must be the population SWEPT (mg-069f).  This
    # instrument was written to expose exactly that gap in mg-fccb's control, so
    # it pins its own counts: 19+219+4231 = 4469 is A001035 for n = 3,4,5.
    if ns == [3, 4, 5]:
        assert (R["tot_posets"], R["tot_pairs"], R["tot_triples"]) \
            == (4469, 43842, 218166), (
                f"population changed: {(R['tot_posets'], R['tot_pairs'], R['tot_triples'])} "
                "!= (4469, 43842, 218166) — A001035 for n = 3,4,5")
        assert [R["per_n"][n][0] for n in ns] == [19, 219, 4231], \
            "per-n poset counts no longer match A001035"
    print()
    print(f"    b_x <= m_x                 : {R['tot_triples'] - R['viol_direction']}"
          f"/{R['tot_triples']}   violations = {R['viol_direction']}")
    print(f"      of which strict b_x < m_x: {R['strict']}")
    print(f"      of which equal  b_x = m_x: {R['equal']}")
    print(f"    b_x = m_x at the e-MINIMUM : {R['emin_equal']}/{R['emin_total']}")
    print(f"    b_x = m_x at the e-MAXIMUM : {R['emax_equal']}/{R['emax_total']}")
    print(f"    (F1) Sum_x m_x = 2E[inv_e] : violations = {R['viol_F1']}")
    print(f"    (star) E[Sum disp^2] = 2E[inv_e] + Cross : violations = {R['viol_star']}")
    print(f"    Jensen E[disp^2] >= E[disp]^2           : violations = {R['viol_jensen']}")
    print(f"    VALID half  Sum b_x^2 <= (max m)*2E[inv]: violations = {R['viol_det_upper']}")
    print()
    print("    STRUCK inference, as a finite statement — 'a large per-element degree")
    print("    max_x m_x forces the deterministic part Sum_x b_x^2 to be at least")
    print("    (max_x m_x)^2' (this is what '(B) fails by a factor n' rests on):")
    print(f"      FAILS on {R['struck_fails']} of "
          f"{R['struck_fails'] + R['struck_holds']} (poset, order) pairs with max_x m_x > 0")
    if R["struck_witness"]:
        n, rel, e, maxm, sb2 = R["struck_witness"]
        print(f"      first witness: n={n} rel={rel} e={e} "
              f"max_x m_x={maxm} Sum b_x^2={sb2}")

    fail = (R["viol_direction"] or R["viol_F1"] or R["viol_star"]
            or R["viol_jensen"] or R["viol_det_upper"] or bad_wm
            or R["emin_equal"] != R["emin_total"]
            # the e-MAX equality was measured and printed here but never made a
            # failure condition; §3.1's mirror falsifier now rests on it in body
            # text, so it is enforced (mg-069f, closing finding F3)
            or R["emax_equal"] != R["emax_total"]
            or R["struck_fails"] == 0)
    print("\n" + "=" * 78)
    if fail:
        print("RESULT: FAIL — an audited assertion did not hold; see above.")
        return 1
    print("RESULT: PASS — direction b_x <= m_x holds with no exception;")
    print("        equality is pinned at the e-minimum AND the e-maximum (so §3.1")
    print("        stands, and its falsifier has a mirror instantiation);")
    print("        the identities (F1) and (star) that §2.3 rests on hold;")
    print("        the struck inference fails on a named, counted population.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
