#!/usr/bin/env /usr/bin/python3
"""mg-9cd1 -- independent replication of mg-72e4's n=7 VIOLATION CENSUS.

For every one of the 163 height-1 iso classes at n = 7, recompute the needed degree
d = n - c - 1 of Gamma(P) with this audit's own routines.  Over Z/2, beta_Q <= beta_2, so a
mod-2 zero PROVES the rational vanishing the census claims; a mod-2 non-zero would be the
first thing to escalate.

Degrees d <= -2 vanish for free; d = -1 is exactly "Gamma(P) is non-empty" (Proposition 3's
content) and is reported as such rather than as a measurement.

Run:  /usr/bin/python3 scripts/audit_mg9cd1_n7_census.py
"""

import json
import os
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit_mg9cd1_height1_independent import (  # noqa: E402
    enum_height1, orbit_classes, atoms, gamma_faces)
from audit_mg9cd1_n7_lowdegree import betti2  # noqa: E402

SKELETON_CAP = 3_000_000


def main():
    n = 7
    reps = orbit_classes(n, enum_height1(n))
    rows = []
    t0 = time.time()
    for P, mult in reps:
        c = len(P)
        d = n - c - 1
        ats = atoms(P, n)
        if d < -1:
            how, beta = "degree_arithmetic", 0
        elif d == -1:
            how, beta = "gamma_nonempty", (1 if not ats else 0)
        else:
            f = gamma_faces(P, n, ats, dmax=d + 1)
            nfaces = sum(len(v) for v in f.values())
            if nfaces > SKELETON_CAP:
                how, beta = "over_cap", None
            else:
                how, beta = "computed_mod2", betti2(f, d)[d]
        rows.append({"c": c, "class_size": mult, "n_atoms": len(ats),
                     "needed_degree": d, "route": how, "beta_needed_mod2": beta})
    viol = [r for r in rows if r["beta_needed_mod2"]]
    over = [r for r in rows if r["beta_needed_mod2"] is None]
    by_route = Counter(r["route"] for r in rows)
    lab_by_route = {}
    for r in rows:
        lab_by_route[r["route"]] = lab_by_route.get(r["route"], 0) + r["class_size"]
    res = {"audit": "mg-9cd1", "of": "mg-72e4 @ 75fb81d", "n": n,
           "iso_classes": len(rows),
           "labelled_total": sum(r["class_size"] for r in rows),
           "violations": len(viol),
           "over_cap_classes": len(over),
           "over_cap_labelled": sum(r["class_size"] for r in over),
           "classes_by_route": dict(by_route), "labelled_by_route": lab_by_route,
           "seconds": round(time.time() - t0, 1), "rows": rows}
    print("n=7: %d classes, %d labelled, %d violations, %d over cap (%d labelled)"
          % (len(rows), res["labelled_total"], len(viol), len(over),
             res["over_cap_labelled"]))
    print("  by route (classes):  ", dict(by_route))
    print("  by route (labelled): ", lab_by_route)
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "data", "onethird-mg9cd1-n7-census.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1, sort_keys=True)
    print("wrote", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
