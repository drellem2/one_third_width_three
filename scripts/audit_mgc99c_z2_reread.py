#!/usr/bin/env python3
"""mg-c99c / R2: re-read the 146 over `Z/2`, so `D3`'s `>= 6` can become `= 6` -- or not.

`mg-0f24` corrected `D3` to *">= 6 of 163 classes carry homology in degree 4"* and was careful
to write `>=`.  The reason is a torsion blind spot, not a gap in the census:

  * the **146** classes with a full homotopy type were read over the instrument's two primes
    near `10^6` (`PRIMES` in `compat_geom_mg72e4_height1_anchor`),
  * the **17** without one were read over `Z/2` by `mg-9cd1`,
  * so **2-torsion in degree 4 among the 146 is invisible to both readings**.

This script closes exactly that gap and nothing else: it re-reads `beta~_4(Gamma(P))` for all
146 over `Z/2`, alongside the same degree over both instrument primes, and reports whether the
`Z/2` reading finds a class the primes could not see.

DEGREE 3 IS READ TOO, and not for decoration.  Over `F_2`, universal coefficients give

    dim_{F2} H~_d  =  rank_d + t_d(2) + t_{d-1}(2)

with `t_d(2)` the number of `Z/2^k` summands in `H~_d(-; Z)`.  So `beta~_4^{F2} = beta~_4^{p}`
(with the primes reading the free rank) forces `t_4(2) = t_3(2) = 0` -- both, because they are
non-negative and sum to zero.  Degree 3 then localises anything that does turn up.

WHAT WOULD MAKE THIS A TEST THAT CANNOT FAIL.  A `Z/2` reader that silently reduced to the same
answer as the primes would report "no disagreement" for all 146 and look like a closure.  So the
controls below include a triangulated `RP^2`, whose entire content is that mod 2 sees homology
the instrument's primes do not, and a mutation that must make that control go RED.

Run: `/usr/bin/python3 scripts/audit_mgc99c_z2_reread.py`  (stdlib only; ~1 core, ~1 minute)
Env: `MGC99C_N` (default 7), `MGC99C_ATOM_CAP` (default 20 -- the instrument's own gate).
Output: `data/onethird-mgc99c-z2-reread.json`.
"""
import json
import os
import sys
import time
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from compat_geom_mg72e4_height1_anchor import (  # noqa: E402
    PRIMES, _rank_mod_p, atoms_of_upper, gamma_faces, height1_iso_classes,
    height1_iso_classes_fast, reduced_betti_range)

Z2 = 2


def betti_over(faces_by_dim, dmax, p, _broken=False):
    """Reduced Betti numbers in degrees -1..dmax over `F_p`, from faces of dim <= dmax+1.

    Deliberately a re-implementation of `reduced_betti_range` with the prime as a PARAMETER
    rather than a module constant -- the instrument's own routine hard-codes `PRIMES` and
    raises on disagreement, which is precisely the behaviour that hides torsion.  The
    re-implementation is the risk, so control Z2 pins it against the instrument on the primes
    it does support.

    `_broken` is the mutation control's switch: it ignores `p` and reads over `PRIMES[0]`,
    which is what a `Z/2` reader that never actually left the primes would do.
    """
    if _broken:
        p = PRIMES[0]
    total = sum(len(v) for v in faces_by_dim.values())
    if total == 0:
        return {-1: 1}
    idx = {d: {f: i for i, f in enumerate(faces_by_dim.get(d, []))} for d in range(-1, dmax + 2)}
    idx[-1] = {(): 0}
    ranks = {}
    for d in range(0, dmax + 2):
        lower = idx[d - 1]
        cols = []
        for f in faces_by_dim.get(d, []):
            col = {}
            for i in range(len(f)):
                j = lower[f[:i] + f[i + 1:]]
                col[j] = col.get(j, 0) + (1 if i % 2 == 0 else -1)
            cols.append(col)
        ranks[d] = _rank_mod_p(cols, max(1, len(lower)), p)
    out = {}
    for d in range(-1, dmax + 1):
        ndim = 1 if d == -1 else len(faces_by_dim.get(d, []))
        out[d] = ndim - ranks.get(d, 0) - ranks.get(d + 1, 0)
    return out


def facets_to_faces(facets, dmax=None):
    """Every non-empty subset of every facet, grouped by dimension."""
    faces = {}
    for f in facets:
        f = tuple(sorted(f))
        top = len(f) if dmax is None else min(len(f), dmax + 1)
        for k in range(1, top + 1):
            for s in combinations(f, k):
                faces.setdefault(k - 1, set()).add(s)
    return {d: sorted(v) for d, v in faces.items()}


# The 6-vertex minimal triangulation of RP^2 (the antipodal quotient of the icosahedron).
# 6 vertices, 15 edges, 10 triangles, chi = 1.  H~_*(RP^2; Z) = (0, Z/2, 0) so it reads
# beta~ = (0, 0, 0) over any odd prime and (0, 1, 1) over Z/2.  This is the only object in the
# script whose answer is known independently of anything the programme computed.
RP2_FACETS = [(1, 2, 3), (1, 3, 4), (1, 4, 5), (1, 5, 6), (1, 2, 6),
              (2, 3, 5), (3, 4, 6), (2, 4, 5), (3, 5, 6), (2, 4, 6)]


def main():
    n = int(os.environ.get("MGC99C_N", "7"))
    atom_cap = int(os.environ.get("MGC99C_ATOM_CAP", "20"))
    report = {
        "ticket": "mg-c99c",
        "remainder": "R2 -- mg-0f24 D3's '>= 6 of 163' is not '= 6' until the 146 are read over Z/2",
        "of": "scripts/compat_geom_mg72e4_height1_anchor.py",
        "instrument_primes": list(PRIMES),
        "n": n,
        "full_betti_atom_cap": atom_cap,
        "degree_of_interest": n - 3,
    }
    failures = []

    # ------------------------------------------------------------------ CONTROLS
    # Z1.  The RP^2 control, which is the whole reason this script can conclude anything.
    #      Two halves, and BOTH must hold: the Z/2 reader must SEE the 2-torsion, and the
    #      instrument's primes must MISS it.  The second half is what makes the first half
    #      evidence rather than a coincidence.
    rp2 = facets_to_faces(RP2_FACETS)
    # precondition: it really is a closed surface -- every edge in exactly two triangles.
    edge_mult = {}
    for f in RP2_FACETS:
        for e in combinations(sorted(f), 2):
            edge_mult[e] = edge_mult.get(e, 0) + 1
    if sorted(set(edge_mult.values())) != [2] or len(edge_mult) != 15 or len(rp2[2]) != 10:
        failures.append("CONTROL Z1 precondition: RP^2 facet list is not a closed surface "
                        "(edges=%d, mults=%r, triangles=%d)"
                        % (len(edge_mult), sorted(set(edge_mult.values())), len(rp2.get(2, []))))
    b_rp2_2 = betti_over(rp2, 2, Z2)
    b_rp2_p = [betti_over(rp2, 2, p) for p in PRIMES]
    if [b_rp2_2[d] for d in (-1, 0, 1, 2)] != [0, 0, 1, 1]:
        failures.append("CONTROL Z1: RP^2 over Z/2 read %r, expected beta~ = (0,0,1,1)" % (b_rp2_2,))
    for p, b in zip(PRIMES, b_rp2_p):
        if [b[d] for d in (-1, 0, 1, 2)] != [0, 0, 0, 0]:
            failures.append("CONTROL Z1: RP^2 over %d read %r, expected all zero" % (p, b))
    if b_rp2_2 == b_rp2_p[0]:
        failures.append("CONTROL Z1: the Z/2 reading of RP^2 AGREES with the instrument prime -- "
                        "this script cannot see 2-torsion and its 146-class result is vacuous")
    report["control_Z1_rp2"] = {
        "over_Z2": {str(d): v for d, v in b_rp2_2.items()},
        "over_primes": [{str(d): v for d, v in b.items()} for b in b_rp2_p],
        "z2_sees_torsion_primes_miss": b_rp2_2 != b_rp2_p[0],
    }

    # Z2.  The re-implementation pinned against the instrument's own routine, on the primes the
    #      instrument supports.  Spheres, the empty complex, and every Gamma(P) at n <= 5.
    pinned = 0
    for k in range(1, 6):
        sph = facets_to_faces([tuple(sorted(s)) for s in combinations(range(k + 2), k + 1)])
        want = reduced_betti_range(sph, k - 1)
        for p in PRIMES:
            got = betti_over(sph, k - 1, p)
            if got != want:
                failures.append("CONTROL Z2: bd simplex_%d over %d: %r != %r" % (k, p, got, want))
            pinned += 1
    if betti_over({}, 2, Z2) != {-1: 1}:
        failures.append("CONTROL Z2: the empty complex is not reading beta~_{-1} = 1 over Z/2")
    for m in (3, 4, 5):
        for P, _ in height1_iso_classes(m):
            atoms = atoms_of_upper(P, m)
            g = gamma_faces(P, m, atoms, dmax=len(atoms))
            dm = max(g) if g else 0
            want = reduced_betti_range(g, dm) if g else {-1: 1}
            for p in PRIMES:
                got = betti_over(g, dm, p) if g else {-1: 1}
                if got != want:
                    failures.append("CONTROL Z2: Gamma n=%d c=%d over %d: %r != %r"
                                    % (m, len(P), p, got, want))
                pinned += 1
    report["control_Z2_pins_against_instrument"] = {"comparisons": pinned}

    # Z3.  MUTATION.  A Z/2 reader that never left the primes must make Z1 go RED.  Without this
    #      the "z2_sees_torsion" flag above is an assertion nobody has shown can fail.
    b_broken = betti_over(rp2, 2, Z2, _broken=True)
    mutation_caught = (b_broken != b_rp2_2) and (b_broken == b_rp2_p[0])
    if not mutation_caught:
        failures.append("CONTROL Z3: the broken Z/2 reader was NOT caught by the RP^2 control "
                        "(broken read %r)" % (b_broken,))
    report["control_Z3_mutation"] = {
        "broken_reader_over_RP2": {str(d): v for d, v in b_broken.items()},
        "control_Z1_goes_red_on_it": mutation_caught,
    }
    print("controls: RP^2 Z/2=%r primes=%r; %d pins against the instrument; mutation caught=%s"
          % ([b_rp2_2[d] for d in (-1, 0, 1, 2)], [b_rp2_p[0][d] for d in (-1, 0, 1, 2)],
             pinned, mutation_caught), flush=True)

    # ------------------------------------------------------------------ MEASUREMENT
    # R2 asks for the 146 within the atom cap.  The other 17 are read here TOO, over the same
    # three fields, because their degree-4 skeletons turn out to sit inside the instrument's own
    # ELIM_CAP (600 000 faces) -- they were excluded from the census by a gate on the FULL
    # homotopy type, not by any degree-4 cost.  That makes the `= 6` below a figure this one
    # script derives over all 163, rather than 2 measured here plus 4 quoted from mg-9cd1.
    deg = n - 3           # degree 4 at n = 7 -- the degree D3 is a claim about
    t0 = time.time()
    classes = height1_iso_classes(n) if n <= 6 else height1_iso_classes_fast(n)
    rows = []
    disagreements = []
    max_skeleton = 0
    for P, mult in classes:
        atoms = atoms_of_upper(P, n)
        within = len(atoms) <= atom_cap
        # beta~_deg needs ranks in degrees deg and deg+1, so faces of dimension <= deg+1.
        g = gamma_faces(P, n, atoms, dmax=deg + 1)
        max_skeleton = max(max_skeleton, sum(len(v) for v in g.values()))
        b2 = betti_over(g, deg, Z2) if g else {d: (1 if d == -1 else 0) for d in range(-1, deg + 1)}
        bp = [betti_over(g, deg, p) if g else {d: (1 if d == -1 else 0) for d in range(-1, deg + 1)}
              for p in PRIMES]
        row = {
            "c": len(P), "class_size": mult, "n_atoms": len(atoms),
            "within_full_betti_atom_cap": within,
            "skeleton_faces_through_deg_plus_1": sum(len(v) for v in g.values()),
            "P": sorted(tuple(e) for e in P),
            "beta_deg_Z2": b2[deg],
            "beta_deg_primes": [b[deg] for b in bp],
            "beta_degm1_Z2": b2.get(deg - 1),
            "beta_degm1_primes": [b.get(deg - 1) for b in bp],
        }
        row["primes_agree"] = len(set(row["beta_deg_primes"])) == 1
        row["z2_agrees_with_primes_at_deg"] = all(row["beta_deg_Z2"] == v
                                                  for v in row["beta_deg_primes"])
        row["z2_agrees_with_primes_at_deg_minus_1"] = all(row["beta_degm1_Z2"] == v
                                                          for v in row["beta_degm1_primes"])
        row["carries_homology_at_deg_over_Z2"] = row["beta_deg_Z2"] != 0
        row["carries_homology_at_deg_over_primes"] = any(v != 0 for v in row["beta_deg_primes"])
        if not row["primes_agree"]:
            failures.append("n=%d c=%d: the instrument's two primes DISAGREE at degree %d: %r"
                            % (n, len(P), deg, row["beta_deg_primes"]))
        if not row["z2_agrees_with_primes_at_deg"]:
            disagreements.append(row)
        rows.append(row)

    within_rows = [r for r in rows if r["within_full_betti_atom_cap"]]
    outside_rows = [r for r in rows if not r["within_full_betti_atom_cap"]]
    seen_only_by_z2 = [r for r in disagreements if not r["carries_homology_at_deg_over_primes"]]
    nonzero_z2 = [r for r in rows if r["carries_homology_at_deg_over_Z2"]]
    nonzero_p = [r for r in rows if r["carries_homology_at_deg_over_primes"]]
    within_nonzero_p = [r for r in within_rows if r["carries_homology_at_deg_over_primes"]]
    torsion_free_deg = all(r["z2_agrees_with_primes_at_deg"] for r in rows)
    torsion_free_within = all(r["z2_agrees_with_primes_at_deg"] for r in within_rows)

    report["population"] = {
        "classes": len(rows),
        "labelled": sum(r["class_size"] for r in rows),
        "R2_population_within_atom_cap": {
            "classes": len(within_rows), "labelled": sum(r["class_size"] for r in within_rows),
            "gate": "#atoms <= %d -- the instrument's own full-homotopy-type gate" % atom_cap},
        "extension_outside_atom_cap": {
            "classes": len(outside_rows), "labelled": sum(r["class_size"] for r in outside_rows),
            "note": "read here as well; mg-9cd1 read these over Z/2 first, and this is an "
                    "independent re-derivation, not a quotation"},
        "max_skeleton_faces_eliminated": max_skeleton,
        "instrument_elimination_cap": 600000,
        "every_elimination_within_instrument_cap": max_skeleton <= 600000,
        "seconds": round(time.time() - t0, 1),
    }
    report["measurement"] = {
        "degree": deg,
        "classes_nonzero_over_Z2": len(nonzero_z2),
        "classes_nonzero_over_primes": len(nonzero_p),
        "classes_nonzero_over_primes_within_atom_cap": len(within_nonzero_p),
        "classes_where_Z2_disagrees_with_primes": len(disagreements),
        "classes_seen_ONLY_by_Z2": len(seen_only_by_z2),
        "no_2_torsion_in_degrees_%d_or_%d" % (deg - 1, deg): torsion_free_deg,
        "no_2_torsion_among_the_R2_population": torsion_free_within,
        "rows_nonzero_over_Z2": [
            {k: r[k] for k in ("c", "class_size", "n_atoms", "within_full_betti_atom_cap",
                               "beta_deg_Z2", "beta_deg_primes", "P")}
            for r in nonzero_z2],
        "rows_disagreeing": [
            {k: r[k] for k in ("c", "class_size", "n_atoms", "P", "beta_deg_Z2",
                               "beta_deg_primes", "beta_degm1_Z2", "beta_degm1_primes")}
            for r in disagreements],
    }

    # The published populations and figures, REPRODUCED rather than quoted.  If the gate or the
    # census moves, this goes RED instead of quietly re-reading a different 146.
    # Recorded as a field, so an ALL_PASS from a run at some other n or cap -- where none of these
    # checks apply -- cannot be read as R2's answer (the vacuous-pass shape of mg-a471/mg-9a59).
    report["R2_measured"] = (n == 7 and atom_cap == 20)
    if not report["R2_measured"]:
        report["verdict_D3_NOT_MEASURED"] = (
            "This run is n=%d, atom cap %d.  R2 is about n = 7 at cap 20; none of the "
            "reproduction checks below applied and this ALL_PASS is not R2's answer."
            % (n, atom_cap))
    if n == 7 and atom_cap == 20:
        checks = [
            (len(rows), 163, "iso classes at n=7"),
            (sum(r["class_size"] for r in rows), 227892, "labelled at n=7"),
            (len(within_rows), 146, "classes within the atom cap"),
            (sum(r["class_size"] for r in within_rows), 225540, "labelled within the atom cap"),
            (len(outside_rows), 17, "classes outside the atom cap"),
            (sum(r["class_size"] for r in outside_rows), 2352, "labelled outside the atom cap"),
            # mg-72e4 Sec.4.3: within the cap exactly TWO classes carry beta~_4 = 1 over the
            # primes -- K_{3,4} and K_{4,3}, c = 12, 35 labelled each.
            (len(within_nonzero_p), 2, "classes non-zero at degree 4 over the primes, within cap"),
            # mg-9cd1 Sec.4.3, re-derived here: FOUR of the 17 read non-zero over Z/2.
            (len([r for r in outside_rows if r["carries_homology_at_deg_over_Z2"]]), 4,
             "classes non-zero at degree 4 over Z/2, outside cap (mg-9cd1's figure)"),
        ]
        for got, want, what in checks:
            if got != want:
                failures.append("REPRODUCTION: %s -- got %d, expected %d" % (what, got, want))
        if sorted((r["c"], r["class_size"], r["beta_deg_primes"][0]) for r in within_nonzero_p) \
                != [(12, 35, 1), (12, 35, 1)]:
            failures.append("REPRODUCTION: the two within-cap non-zero classes are not "
                            "K_{3,4}/K_{4,3}: %r"
                            % sorted((r["c"], r["class_size"]) for r in within_nonzero_p))
        # mg-9cd1's four: the two stars (c = 6, 7 labelled) and K_{2,5}/K_{5,2} (c = 10, 21).
        got4 = sorted((r["c"], r["class_size"]) for r in outside_rows
                      if r["carries_homology_at_deg_over_Z2"])
        if got4 != [(6, 7), (6, 7), (10, 21), (10, 21)]:
            failures.append("REPRODUCTION: mg-9cd1's four outside-cap classes are not the two "
                            "stars and K_{2,5}/K_{5,2}: %r" % (got4,))

    # THE CONCLUSION, stated as a field rather than left to a reader of the table.
    if torsion_free_within:
        report["verdict_D3"] = (
            "R2 CLOSED.  The %d classes within the atom cap carry NO 2-torsion in degree %d or "
            "%d: beta~_%d over Z/2 equals beta~_%d over both instrument primes for every one of "
            "them (universal coefficients then forces t_%d(2) = t_%d(2) = 0, since they are "
            "non-negative and sum to zero).  Reading all %d classes over Z/2 in degree %d gives "
            "EXACTLY %d non-zero, so D3's '>= %d of 163' becomes '= %d of 163 over Z/2'.  The "
            "inequality was carrying the 2-torsion blind spot and nothing else; the remaining "
            "blind spot is a DIFFERENT one -- see the caveat field."
            % (len(within_rows), deg - 1, deg, deg, deg, deg, deg - 1, len(rows), deg,
               len(nonzero_z2), len(nonzero_z2), len(nonzero_z2)))
    else:
        report["verdict_D3"] = (
            "The Z/2 reading DISAGREES with the primes on %d of the %d classes within the atom "
            "cap; %d of those are invisible to the primes entirely.  D3's '>= %d' STANDS and "
            "the count RISES to %d over Z/2."
            % (len([r for r in disagreements if r["within_full_betti_atom_cap"]]),
               len(within_rows), len(seen_only_by_z2), 6, len(nonzero_z2)))
    report["caveat"] = (
        "What '= %d' is and is not.  It is a count over Z/2, in degree %d, over all %d classes; "
        "beta~_Q <= beta~_{F2} always, so the %d classes reading zero over Z/2 are rationally "
        "acyclic in that degree, but a Z/2 ONE bounds beta~_Q <= 1 and does not give a rational "
        "value (mg-72e4 Sec.3), so the field label stays on the figure.  Two blind spots remain "
        "and neither is the one R2 closed: (a) ODD torsion at a prime nobody read -- the three "
        "fields here are Z/2 and the instrument's two primes near 10^6, and a class could carry "
        "q-torsion at some other q; (b) 'no 2-torsion' is read against the primes standing in "
        "for the free rank, so torsion at 1000003 or 999983 itself would be invisible to the "
        "comparison.  The two primes agreeing on every one of the %d classes is evidence for "
        "(b), not a proof."
        % (len(nonzero_z2), deg, len(rows), len(rows) - len(nonzero_z2), len(rows)))

    report["ALL_PASS"] = not failures
    report["failures"] = failures
    out = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "data", "onethird-mgc99c-z2-reread.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("n=%d: %d classes / %d labelled read at degree %d over Z/2 and both primes "
          "(%d within the atom cap = R2's population, %d outside)  (%.1fs)"
          % (n, len(rows), sum(r["class_size"] for r in rows), deg,
             len(within_rows), len(outside_rows), report["population"]["seconds"]))
    print("  non-zero over primes: %d;  non-zero over Z/2: %d;  disagreements: %d;  "
          "seen only by Z/2: %d;  largest skeleton eliminated: %d faces"
          % (len(nonzero_p), len(nonzero_z2), len(disagreements), len(seen_only_by_z2),
             max_skeleton))
    print("  " + report["verdict_D3"])
    print("ALL_PASS =", report["ALL_PASS"])
    for x in failures[:20]:
        print("  FAIL", x)
    print("wrote", out)
    return 0 if report["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
