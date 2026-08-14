#!/usr/bin/env python3
"""mg-0f24 / D7: what does `mg-72e4`'s over-cap gate actually measure, and what did it exclude?

`compat_geom_mg72e4_height1_anchor.py` declined a class when

    _binom(len(atoms), d + 3) > SKELETON_CAP        # 3 000 000

which is the size of the TOP LAYER OF THE AMBIENT SIMPLEX on the atoms -- an object the
instrument never builds.  `mg-9cd1` D7 recorded that as a defect and named the remedy: cap on
`Gamma(P)`'s REALISED face count.  This script measures the difference between the two gates so
that the remedy is landed against a measurement rather than against one known class.

For every height-1 iso class with needed degree `d = n - c - 1 >= 0` it records

  * `ambient_top_layer`  = binom(#atoms, d+3)          -- what the old gate tested
  * `realised_through_d1` = |{faces of Gamma(P) of dim <= d+1}|   -- what beta~_d needs
  * `realised_through_d2` = |{faces of Gamma(P) of dim <= d+2}|   -- what the near-miss column
                                                                     beta~_{d+1} additionally needs
  * `realised_full`      = |Gamma(P)| in full, where #atoms <= FULL_BETTI_ATOM_CAP (20) --
                           the skeleton the margin measurement materialises

All three realised counts are enumerated with early abort at the cap, so a class that is far over
costs a bounded amount of work and is reported as a lower bound (`_over` flags).

Run: `/usr/bin/python3 scripts/audit_mg0f24_cap_gap.py`  (stdlib only)
Env: `MG0F24_NMAX` (default 7), `MG0F24_CAP` (default 3000000), `MG0F24_FULL_ATOM_CAP` (default 20).
Output: `data/onethird-mg0f24-cap-gap.json`.
"""
import json
import os
import sys
import time
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from compat_geom_mg72e4_height1_anchor import (  # noqa: E402
    _binom, atoms_of_upper, gamma_faces, height1_iso_classes, height1_iso_classes_fast,
    is_total, tc)


def gamma_face_profile(P, n, atoms, dmax, cap):
    """Realised faces of Gamma(P) of dimension <= dmax, COUNTED and not stored.

    Same face rule and same pruning as `gamma_faces`: a subset A of atoms is a face iff
    tc(P u UA) is an acyclic non-total relation, and a non-face prunes its supersets.
    Returns (total, by_dim, exceeded); on `exceeded` both counts are lower bounds.
    """
    m = len(atoms)
    by_dim = defaultdict(int)
    total = 0
    if m == 0:
        return 0, {}, False
    stack = [([i], atoms[i]) for i in range(m - 1, -1, -1)]
    while stack:
        prefix, cur = stack.pop()
        d = len(prefix) - 1
        total += 1
        by_dim[d] += 1
        if total > cap:
            return total, dict(by_dim), True
        if d >= dmax:
            continue
        for j in range(m - 1, prefix[-1], -1):
            U = cur | atoms[j]
            Q = tc(U, n)
            if Q is None or is_total(Q, n):
                continue
            stack.append((prefix + [j], Q))
    return total, dict(by_dim), False


def main():
    nmax = int(os.environ.get("MG0F24_NMAX", "7"))
    cap = int(os.environ.get("MG0F24_CAP", "3000000"))
    full_atom_cap = int(os.environ.get("MG0F24_FULL_ATOM_CAP", "20"))
    report = {
        "ticket": "mg-0f24",
        "defect": "mg-9cd1 D7 -- the over-cap gate tested the ambient simplex, not Gamma(P)",
        "of": "scripts/compat_geom_mg72e4_height1_anchor.py",
        "skeleton_cap": cap,
        "full_betti_atom_cap": full_atom_cap,
        "nmax": nmax,
    }
    failures = []
    per_n = {}

    # ---------------- CONTROLS on this script's own counter, before anything is believed.
    # The counter is a re-implementation of gamma_faces()'s DFS with the storage removed, so the
    # thing that can silently go wrong is that it counts a DIFFERENT complex.  It is pinned
    # against the instrument's own builder, per dimension, on every class at n <= 5; and the
    # early abort is pinned against an un-aborted run.  Without this the script's only assertion
    # would be one that cannot fail, which is the defect this corpus keeps catching.
    ctl = {"classes_checked": 0, "dimensions_compared": 0, "abort_free_runs": 0}
    for n in (3, 4, 5):
        for P, _ in height1_iso_classes(n):
            atoms = atoms_of_upper(P, n)
            for dmax in (max(0, n - len(P)), len(atoms)):
                built = gamma_faces(P, n, atoms, dmax=dmax)
                built_by_dim = {d: len(v) for d, v in built.items()}
                total, by_dim, over = gamma_face_profile(P, n, atoms, dmax, cap)
                if over:
                    failures.append("CONTROL n=%d c=%d: small class hit the cap" % (n, len(P)))
                if by_dim != built_by_dim:
                    failures.append("CONTROL counter vs builder n=%d c=%d dmax=%d: %r != %r"
                                    % (n, len(P), dmax, by_dim, built_by_dim))
                if total != sum(built_by_dim.values()):
                    failures.append("CONTROL total n=%d c=%d dmax=%d" % (n, len(P), dmax))
                ctl["dimensions_compared"] += len(built_by_dim)
                # The early abort must not change what is counted below the cap, and must fire at
                # one below it.  PRECONDITION: there has to be a face to abort on -- Gamma(P) is
                # empty whenever U(P) is (three classes at n = 3), and an abort test over an empty
                # complex is a test that cannot fail.  Counted, not silently skipped.
                if total == 0:
                    ctl["abort_untestable_empty_gamma"] = ctl.get("abort_untestable_empty_gamma", 0) + 1
                    continue
                t_small, _, o_small = gamma_face_profile(P, n, atoms, dmax, total)
                if o_small or t_small != total:
                    failures.append("CONTROL abort boundary n=%d c=%d dmax=%d" % (n, len(P), dmax))
                t_cut, _, o_cut = gamma_face_profile(P, n, atoms, dmax, total - 1)
                if not o_cut:
                    failures.append("CONTROL abort did not fire n=%d c=%d dmax=%d"
                                    % (n, len(P), dmax))
                ctl["abort_free_runs"] += 1
            ctl["classes_checked"] += 1
    report["control_counter_vs_builder"] = ctl
    print("control: counter == gamma_faces() on %d classes / %d dimension buckets; "
          "early abort fires exactly at the cap on %d runs"
          % (ctl["classes_checked"], ctl["dimensions_compared"], ctl["abort_free_runs"]),
          flush=True)

    for n in range(3, nmax + 1):
        t0 = time.time()
        classes = height1_iso_classes(n) if n <= 6 else height1_iso_classes_fast(n)
        rows = []
        for P, mult in classes:
            c = len(P)
            d = n - c - 1
            atoms = atoms_of_upper(P, n)
            row = {"c": c, "class_size": mult, "n_atoms": len(atoms), "needed_degree": d}
            if d >= 0:
                amb = _binom(len(atoms), d + 3)
                t1, _, o1 = gamma_face_profile(P, n, atoms, d + 1, cap)
                t2, _, o2 = gamma_face_profile(P, n, atoms, d + 2, cap)
                row.update({
                    "ambient_top_layer": amb,
                    "ambient_gate_excludes": amb > cap,
                    "realised_through_d1": t1, "realised_through_d1_over": o1,
                    "realised_through_d2": t2, "realised_through_d2_over": o2,
                    "realised_gate_excludes_needed": o1 or t1 > cap,
                    "realised_gate_excludes_nearmiss": o2 or t2 > cap,
                })
                # the realised complex is contained in the ambient one, but the old gate tested
                # only the TOP ambient layer, so neither count dominates the other a priori.
                if not o1 and not o2 and t1 > t2:
                    failures.append("n=%d c=%d: through-d1 > through-d2" % (n, c))
            if len(atoms) <= full_atom_cap:
                tf, _, of = gamma_face_profile(P, n, atoms, len(atoms), cap)
                row["realised_full"] = tf
                row["realised_full_over"] = of
                row["full_homotopy_type_computed"] = True
            else:
                row["full_homotopy_type_computed"] = False
            rows.append(row)

        gated = [r for r in rows if r["needed_degree"] >= 0]
        amb_out = [r for r in gated if r["ambient_gate_excludes"]]
        real_out = [r for r in gated if r["realised_gate_excludes_needed"]]
        wrongly = [r for r in gated
                   if r["ambient_gate_excludes"] and not r["realised_gate_excludes_needed"]]
        newly = [r for r in gated
                 if not r["ambient_gate_excludes"] and r["realised_gate_excludes_needed"]]
        admitted = [r for r in gated if not r["ambient_gate_excludes"]]
        fulls = [r for r in rows if r.get("full_homotopy_type_computed") and not r.get("realised_full_over")]
        per_n[str(n)] = {
            "iso_classes": len(rows),
            "labelled": sum(r["class_size"] for r in rows),
            "gated_classes": len(gated),
            "ambient_gate_excludes": len(amb_out),
            "ambient_gate_excludes_labelled": sum(r["class_size"] for r in amb_out),
            "realised_gate_excludes_needed": len(real_out),
            "realised_gate_excludes_needed_labelled": sum(r["class_size"] for r in real_out),
            "wrongly_excluded_by_ambient_gate": len(wrongly),
            "wrongly_excluded_labelled": sum(r["class_size"] for r in wrongly),
            "newly_excluded_by_realised_gate": len(newly),
            # the demonstrated envelope: the largest skeleton the instrument actually handed to
            # its elimination routine at this n
            "max_realised_through_d2_among_admitted":
                max([r["realised_through_d2"] for r in admitted if not r["realised_through_d2_over"]] or [0]),
            "max_realised_full": max([r["realised_full"] for r in fulls] or [0]),
            "rows": rows,
            "seconds": round(time.time() - t0, 1),
        }
        print("n=%d: %d classes, ambient gate excludes %d, realised gate excludes %d, "
              "wrongly excluded %d; max realised skeleton admitted %d, max full %d  (%.1fs)"
              % (n, len(rows), len(amb_out), len(real_out), len(wrongly),
                 per_n[str(n)]["max_realised_through_d2_among_admitted"],
                 per_n[str(n)]["max_realised_full"], per_n[str(n)]["seconds"]), flush=True)
        for r in wrongly:
            print("    WRONGLY EXCLUDED  c=%d size=%d atoms=%d d=%d  ambient=%d  realised d+1=%d d+2=%d"
                  % (r["c"], r["class_size"], r["n_atoms"], r["needed_degree"],
                     r["ambient_top_layer"], r["realised_through_d1"], r["realised_through_d2"]))

    report["per_n"] = per_n

    # WHERE THE OLD GATE BITES NEXT.  n = 8 is outside everything this instrument measures, but
    # the ambient gate's verdict there is cheap -- it needs only the atom count -- and it is the
    # honest answer to "how big is this defect going forward".  Only the AMBIENT side is computed:
    # counting realised faces for 556 classes at n = 8 is a job, not a clause, so what the
    # realised gate would say about these classes is NOT measured and is not claimed.
    for n in [int(x) for x in os.environ.get("MG0F24_AMBIENT_ONLY", "8").split(",") if x.strip()]:
        t0 = time.time()
        classes = height1_iso_classes(n) if n <= 6 else height1_iso_classes_fast(n)
        excl = []
        for P, mult in classes:
            c = len(P)
            d = n - c - 1
            if d < 0:
                continue
            m = len(atoms_of_upper(P, n))
            if _binom(m, d + 3) > cap:
                excl.append({"c": c, "class_size": mult, "n_atoms": m, "needed_degree": d,
                             "ambient_top_layer": _binom(m, d + 3)})
        report.setdefault("ambient_gate_only", {})[str(n)] = {
            "iso_classes": len(classes),
            "labelled": sum(m for _, m in classes),
            "ambient_gate_excludes": len(excl),
            "ambient_gate_excludes_labelled": sum(r["class_size"] for r in excl),
            "realised_gate_verdict": "NOT MEASURED -- ambient side only at this n",
            "rows": sorted(excl, key=lambda r: (r["c"], r["class_size"])),
            "seconds": round(time.time() - t0, 1),
        }
        print("n=%d (ambient gate only): %d classes, gate excludes %d / %d labelled  (%.1fs)"
              % (n, len(classes), len(excl), sum(r["class_size"] for r in excl),
                 time.time() - t0), flush=True)

    # The finding itself, asserted rather than only reported: at n = 7 the two gates must
    # DISAGREE on the c = 1 class -- ambient excludes it, realised admits it for the needed
    # degree.  If a later edit raises the ambient cap instead of replacing the test, or changes
    # the face rule, this goes RED rather than quietly reporting "0 wrongly excluded".
    if nmax >= 7:
        c1 = [r for r in per_n["7"]["rows"] if r["c"] == 1]
        if len(c1) != 1:
            failures.append("ASSERTION: expected exactly one c=1 class at n=7, found %d" % len(c1))
        else:
            r = c1[0]
            if not r["ambient_gate_excludes"]:
                failures.append("ASSERTION: the ambient gate no longer excludes n=7 c=1")
            if r["realised_gate_excludes_needed"]:
                failures.append("ASSERTION: the realised gate excludes n=7 c=1 for the needed degree")
            if not r["realised_gate_excludes_nearmiss"]:
                failures.append("ASSERTION: the near-miss skeleton at n=7 c=1 is no longer over cap")
        report["assertion_n7_c1_gates_disagree"] = c1[0] if len(c1) == 1 else None
    report["envelope_realised_skeleton"] = max(
        [v["max_realised_through_d2_among_admitted"] for v in per_n.values()] or [0])
    report["envelope_realised_full"] = max(
        [v["max_realised_full"] for v in per_n.values()] or [0])
    report["ALL_PASS"] = not failures
    report["failures"] = failures

    out = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "data", "onethird-mg0f24-cap-gap.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    print("envelope: largest realised skeleton handed to the elimination = %d faces; "
          "largest full Gamma materialised = %d faces"
          % (report["envelope_realised_skeleton"], report["envelope_realised_full"]))
    print("ALL_PASS =", report["ALL_PASS"])
    for x in failures[:20]:
        print("  FAIL", x)
    print("wrote", out)
    return 0 if report["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
