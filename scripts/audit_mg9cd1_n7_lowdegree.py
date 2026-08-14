#!/usr/bin/env /usr/bin/python3
"""mg-9cd1 -- the measurement the target document does NOT make: low-degree homology of
Gamma(P) for the 17 n=7 height-1 classes that have NO full homotopy type in mg-72e4.

Why this is the right instrument.  Over Z/2, rank_2(d) <= rank_Q(d) for an integer matrix,
so beta_Q(k) <= beta_2(k).  A mod-2 VANISHING therefore PROVES rational vanishing, which is
the direction that matters here: the margin claim is broken by homology appearing LOW, and
mod-2 vanishing rules that out.  (The converse fails -- a non-zero mod-2 Betti number could
be 2-torsion -- so a non-zero here is reported as an upper bound, not as a rational value.)

Gamma(P) is rebuilt from scratch by this audit's own routines (audit_mg9cd1_height1_independent),
never imported from the target instrument.

Run:  /usr/bin/python3 scripts/audit_mg9cd1_n7_lowdegree.py [max_degree]
"""

import json
import os
import sys
import time
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from audit_mg9cd1_height1_independent import (  # noqa: E402
    enum_height1, orbit_classes, atoms, gamma_faces)


def betti2(faces, dmax):
    """Reduced Betti numbers over Z/2 in degrees -1..dmax, augmented chain complex.
    Columns are big-int bitmasks over row indices; reduction is xor."""
    ranks = {}
    for d in range(0, dmax + 2):
        below = {(): 0} if d == 0 else {f: i for i, f in enumerate(faces.get(d - 1, []))}
        piv = {}
        rank = 0
        for f in faces.get(d, []):
            col = 0
            for i in range(len(f)):
                col ^= 1 << below[f[:i] + f[i + 1:]]
            while col:
                low = col.bit_length() - 1
                if low not in piv:
                    piv[low] = col
                    rank += 1
                    break
                col ^= piv[low]
        ranks[d] = rank
    b = {}
    for d in range(-1, dmax + 1):
        nd = 1 if d == -1 else len(faces.get(d, []))
        b[d] = nd - ranks.get(d, 0) - ranks.get(d + 1, 0)
    return b


# How deep to go, per class.  The target of the exercise is to certify margin >= 4, i.e.
# first-nonvanishing >= d + 4; deeper c needs less depth because d = n - c - 1 is smaller.
# The depths below are what fits in memory on a shared host -- c <= 2 is where it runs out.
DEPTH_BY_C = {1: 4, 2: 4, 3: 6, 4: 5}


def main():
    default_dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    n = 7
    reps = orbit_classes(n, enum_height1(n))
    rows = []
    for P, mult in reps:
        ats = atoms(P, n)
        if len(ats) <= 20:
            continue            # these 146 already have a full homotopy type in mg-72e4
        dmax = DEPTH_BY_C.get(len(P), default_dmax)
        t0 = time.time()
        f = gamma_faces(P, n, ats, dmax=dmax + 1)
        b = betti2(f, dmax)
        c = len(P)
        d = n - c - 1
        nz = sorted(k for k, v in b.items() if v)
        rows.append({
            "P": sorted(map(list, P)), "c": c, "class_size": mult, "n_atoms": len(ats),
            "needed_degree": d,
            "faces_by_dim": {str(k): len(v) for k, v in sorted(f.items())},
            "betti_mod2": {str(k): v for k, v in b.items()},
            "first_nonzero_mod2_le_dmax": (nz[0] if nz else None),
            # beta_Q <= beta_2, so all-zero mod 2 proves rational vanishing in these degrees
            "rational_vanishes_through": dmax if not nz else (nz[0] - 1),
            "margin_lower_bound": (dmax + 1 - d) if not nz else (nz[0] - d),
            "seconds": round(time.time() - t0, 1),
        })
        print("c=%2d sz=%6d atoms=%2d d=%2d  betti2(-1..%d)=%s  margin>=%s  [%.0fs]"
              % (c, mult, len(ats), d, dmax,
                 [b[k] for k in range(-1, dmax + 1)], rows[-1]["margin_lower_bound"],
                 rows[-1]["seconds"]), flush=True)
    res = {
        "audit": "mg-9cd1", "of": "mg-72e4 @ 75fb81d", "n": 7,
        "max_degree_by_c": DEPTH_BY_C, "max_degree_default": default_dmax,
        "field": "Z/2 (beta_Q <= beta_2, so a zero here proves rational vanishing)",
        "classes": len(rows),
        "classes_with_homology_below_n_minus_3": [
            r for r in rows
            if any(int(k) < 4 and v for k, v in r["betti_mod2"].items())],
        "rows": rows,
    }
    good = [r for r in rows if r["margin_lower_bound"] >= 4]
    res["classes_margin_ge_4"] = len(good)
    res["classes_margin_unresolved"] = [
        {"c": r["c"], "class_size": r["class_size"], "margin_lower_bound":
         r["margin_lower_bound"]} for r in rows if r["margin_lower_bound"] < 4]
    res["labelled_margin_unresolved"] = sum(
        r["class_size"] for r in rows if r["margin_lower_bound"] < 4)
    print("margin >= 4 established on %d of the 17; unresolved %d classes / %d labelled"
          % (len(good), len(res["classes_margin_unresolved"]),
             res["labelled_margin_unresolved"]))
    print("classes with homology below degree n-3 = 4:",
          len(res["classes_with_homology_below_n_minus_3"]))
    path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                        "data", "onethird-mg9cd1-n7-lowdegree.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1, sort_keys=True)
    print("wrote", path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
