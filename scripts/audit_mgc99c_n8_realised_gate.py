#!/usr/bin/env python3
"""mg-c99c / R1: run mg-0f24's repaired over-cap gate at n = 8, where only the old one was read.

`mg-0f24` replaced the over-cap gate's AMBIENT-simplex test (`binom(#atoms, d+3)`) with a count
of `Gamma(P)`'s REALISED faces.  Measured consequence at `n <= 7`:

    old ambient gate  wrongly excluded EXACTLY ONE class  (n = 7, c = 1, 42 labelled)
    new realised gate excludes NONE

At `n = 8` only the ambient side was computed -- the old gate declines 6 classes / 1792 labelled
there, and mg-0f24 said plainly that what the new gate says was NOT measured, because "counting
realised faces for 556 classes at n = 8 is a job, not a clause".  This script does that job and
answers the narrow question: **are those 6 declines real, or the same artifact one `n` higher?**

HOW 556 CLASSES BECOME 10 ENUMERATIONS.  For any simplicial complex on `m` vertices the number
of faces of dimension `<= dmax` is at most

    UB(m, dmax) = sum_{k = 1}^{dmax + 1} binom(m, k)

because every face is a non-empty subset of size `<= dmax + 1`.  Where `UB <= cap`, the realised
gate PROVABLY admits the class and no enumeration is needed.  At `n = 8` that settles 203 of the
206 gated classes on the needed-degree column outright; only 3 (and 7 on the near-miss column)
have to be enumerated.  So this is a COMPLETE answer at `n = 8`, not a bounded partial -- the
bound is exact combinatorics, not a heuristic, and control K3/K4 below is what makes it evidence.

Note `UB` and the old ambient test are DIFFERENT objects.  The old test was `binom(m, d+3)` --
the size of one layer, the one just ABOVE the skeleton in question.  `UB` sums every layer up to
and including the skeleton.  Neither dominates the other, which is exactly why the realised gate
can both admit classes the ambient gate declined and decline classes it admitted.

CONTROLS.  The counter is mg-0f24's own `gamma_face_profile`, imported rather than re-typed, and
its pin against the instrument's `gamma_faces()` builder is re-run here (K1) so widening does not
leave it behind.  K2 breaks the counter deliberately and requires K1's comparison to go RED --
the mg-c99c work item records that mg-0f24 made that demonstration, but it is not in the
repository and cannot be re-run, so it is committed here.  K3 pins the
NEW ingredient, the bound, against actual enumeration; K4 breaks the bound and requires K3 to go
RED.  K5 replays mg-0f24's `n <= 7` verdicts from its committed JSON: this widening must not move
a single one of them.

Run: `/usr/bin/python3 scripts/audit_mgc99c_n8_realised_gate.py`  (stdlib only; 1 core)
Env: `MGC99C_NMAX` (default 8), `MGC99C_CAP` (default 3000000, mg-0f24's SKELETON_CAP).
Output: `data/onethird-mgc99c-n8-realised-gate.json`.
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
from audit_mg0f24_cap_gap import gamma_face_profile  # noqa: E402


def realised_upper_bound(m, dmax, _broken=False):
    """Max possible number of faces of dimension <= dmax on m vertices.

    Every face is a non-empty subset of size <= dmax + 1, so the bound is exact and is attained
    by the full skeleton.  `_broken` drops the top term -- control K4's mutation, which makes
    the bound too small and therefore unsound.
    """
    top = dmax + 1 - (1 if _broken else 0)
    return sum(_binom(m, k) for k in range(1, top + 1))


def broken_face_profile(P, n, atoms, dmax, cap):
    """Control K2's mutation: the same DFS with the `is_total` rejection dropped, so it counts
    a strictly larger complex than `Gamma(P)`.  Must be caught by the pin against the builder."""
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
            if Q is None:                       # `or is_total(Q, n)` deliberately removed
                continue
            stack.append((prefix + [j], Q))
    return total, dict(by_dim), False


def gate_verdict(P, n, atoms, dmax, cap):
    """Does the realised gate exclude this skeleton?  Returns (excludes, count_or_None, how).

    `how` is "bound" when the combinatorial bound settled it without enumeration, or
    "enumerated" when the faces were actually counted.
    """
    m = len(atoms)
    if realised_upper_bound(m, dmax) <= cap:
        return False, None, "bound"
    total, _, over = gamma_face_profile(P, n, atoms, dmax, cap)
    return (over or total > cap), total, "enumerated"


def main():
    nmax = int(os.environ.get("MGC99C_NMAX", "8"))
    cap = int(os.environ.get("MGC99C_CAP", "3000000"))
    report = {
        "ticket": "mg-c99c",
        "remainder": "R1 -- the realised-face gate is unmeasured at n = 8",
        "of": "scripts/audit_mg0f24_cap_gap.py, scripts/compat_geom_mg72e4_height1_anchor.py",
        "skeleton_cap": cap,
        "nmax": nmax,
    }
    failures = []

    # ------------------------------------------------------------------ CONTROLS
    # K1.  mg-0f24's pin, re-run: the counter must equal the instrument's own builder per
    #      dimension.  Re-run rather than assumed, because this script calls the counter on
    #      inputs an `n` larger than anything it has been pinned on.
    ctl = {"classes_checked": 0, "dimensions_compared": 0}
    small = {}
    for m in (3, 4, 5):
        small[m] = []
        for P, _ in height1_iso_classes(m):
            atoms = atoms_of_upper(P, m)
            small[m].append((P, atoms))
            for dmax in (max(0, m - len(P)), len(atoms)):
                built = gamma_faces(P, m, atoms, dmax=dmax)
                built_by_dim = {d: len(v) for d, v in built.items()}
                total, by_dim, over = gamma_face_profile(P, m, atoms, dmax, cap)
                if over or by_dim != built_by_dim or total != sum(built_by_dim.values()):
                    failures.append("CONTROL K1 counter vs builder n=%d c=%d dmax=%d"
                                    % (m, len(P), dmax))
                ctl["dimensions_compared"] += len(built_by_dim)
            ctl["classes_checked"] += 1
    report["control_K1_counter_vs_builder"] = ctl

    # K2.  MUTATION on the counter.  A counter that counts the wrong complex must be caught by
    #      K1's comparison.  This is the demonstration mg-0f24 reported and did not commit.
    k2_caught = False
    k2_first = None
    for m in (3, 4, 5):
        for P, atoms in small[m]:
            dmax = len(atoms)
            built_by_dim = {d: len(v) for d, v in gamma_faces(P, m, atoms, dmax=dmax).items()}
            _, by_dim, _ = broken_face_profile(P, m, atoms, dmax, cap)
            if by_dim != built_by_dim:
                k2_caught = True
                if k2_first is None:
                    k2_first = {"n": m, "c": len(P), "broken": by_dim, "builder": built_by_dim}
                break
        if k2_caught:
            break
    if not k2_caught:
        failures.append("CONTROL K2: the deliberately broken counter was NOT caught by K1's "
                        "comparison -- K1 is a test that cannot fail")
    report["control_K2_counter_mutation"] = {"caught": k2_caught, "first_disagreement": k2_first}

    # K3.  The NEW ingredient.  The bound must never be below the realised count.  Pinned by
    #      actual enumeration on every gated class at n <= 6, on both columns.
    k3 = {"comparisons": 0, "violations": 0}
    for m in (3, 4, 5, 6):
        for P, _ in height1_iso_classes(m):
            c = len(P)
            d = m - c - 1
            if d < 0:
                continue
            atoms = atoms_of_upper(P, m)
            for dmax in (d + 1, d + 2):
                total, _, over = gamma_face_profile(P, m, atoms, dmax, cap)
                if over:
                    continue
                if realised_upper_bound(len(atoms), dmax) < total:
                    k3["violations"] += 1
                    failures.append("CONTROL K3: bound BELOW realised count n=%d c=%d dmax=%d "
                                    "(%d < %d)" % (m, c, dmax,
                                                   realised_upper_bound(len(atoms), dmax), total))
                k3["comparisons"] += 1
    # ... and against every count mg-0f24 already recorded at n <= 7, for free.
    prev_path = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                             "data", "onethird-mg0f24-cap-gap.json")
    prev = json.load(open(prev_path))
    for nn, v in prev["per_n"].items():
        for r in v["rows"]:
            if r.get("needed_degree", -1) < 0:
                continue
            for key, dmax in (("realised_through_d1", r["needed_degree"] + 1),
                              ("realised_through_d2", r["needed_degree"] + 2)):
                if r.get(key + "_over") or key not in r:
                    continue
                if realised_upper_bound(r["n_atoms"], dmax) < r[key]:
                    k3["violations"] += 1
                    failures.append("CONTROL K3: bound below mg-0f24's recorded %s at n=%s c=%d"
                                    % (key, nn, r["c"]))
                k3["comparisons"] += 1
    report["control_K3_bound_vs_enumeration"] = k3

    # K4.  MUTATION on the bound.  A bound one term short must be caught by K3's comparison.
    k4_caught = False
    k4_first = None
    for m in (4, 5, 6):
        for P, _ in height1_iso_classes(m):
            c = len(P)
            d = m - c - 1
            if d < 0:
                continue
            atoms = atoms_of_upper(P, m)
            total, _, over = gamma_face_profile(P, m, atoms, d + 1, cap)
            if over:
                continue
            if realised_upper_bound(len(atoms), d + 1, _broken=True) < total:
                k4_caught = True
                k4_first = {"n": m, "c": c, "broken_bound":
                            realised_upper_bound(len(atoms), d + 1, _broken=True),
                            "realised": total}
                break
        if k4_caught:
            break
    if not k4_caught:
        failures.append("CONTROL K4: the deliberately broken bound was NOT caught by K3 -- K3 "
                        "is a test that cannot fail")
    report["control_K4_bound_mutation"] = {"caught": k4_caught, "first_violation": k4_first}
    print("controls: K1 counter==builder on %d classes / %d dimension buckets; K2 mutation "
          "caught=%s; K3 %d bound-vs-count comparisons, %d violations; K4 mutation caught=%s"
          % (ctl["classes_checked"], ctl["dimensions_compared"], k2_caught,
             k3["comparisons"], k3["violations"], k4_caught), flush=True)

    # ------------------------------------------------------------------ MEASUREMENT
    per_n = {}
    for n in range(3, nmax + 1):
        t0 = time.time()
        classes = height1_iso_classes(n) if n <= 6 else height1_iso_classes_fast(n)
        n_iso = len(classes)
        rows = []
        for P, mult in classes:
            c = len(P)
            d = n - c - 1
            if d < 0:
                continue
            atoms = atoms_of_upper(P, n)
            amb = _binom(len(atoms), d + 3)
            e1, t1, how1 = gate_verdict(P, n, atoms, d + 1, cap)
            e2, t2, how2 = gate_verdict(P, n, atoms, d + 2, cap)
            rows.append({
                "c": c, "class_size": mult, "n_atoms": len(atoms), "needed_degree": d,
                "ambient_top_layer": amb, "ambient_gate_excludes": amb > cap,
                "realised_gate_excludes_needed": e1, "realised_gate_excludes_nearmiss": e2,
                "settled_needed_by": how1, "settled_nearmiss_by": how2,
                "realised_through_d1": t1, "realised_through_d2": t2,
                "bound_through_d1": realised_upper_bound(len(atoms), d + 1),
                "bound_through_d2": realised_upper_bound(len(atoms), d + 2),
            })
        amb_out = [r for r in rows if r["ambient_gate_excludes"]]
        real_out = [r for r in rows if r["realised_gate_excludes_needed"]]
        wrongly = [r for r in rows if r["ambient_gate_excludes"]
                   and not r["realised_gate_excludes_needed"]]
        newly = [r for r in rows if not r["ambient_gate_excludes"]
                 and r["realised_gate_excludes_needed"]]
        newly_nm = [r for r in rows if not r["ambient_gate_excludes"]
                    and r["realised_gate_excludes_nearmiss"]]
        per_n[str(n)] = {
            "iso_classes": n_iso,
            "iso_labelled": sum(m for _, m in classes),
            "ungated_classes_c_ge_n": n_iso - len(rows),
            "gated_classes": len(rows),
            "gated_labelled": sum(r["class_size"] for r in rows),
            "ambient_gate_excludes": len(amb_out),
            "ambient_gate_excludes_labelled": sum(r["class_size"] for r in amb_out),
            "realised_gate_excludes_needed": len(real_out),
            "realised_gate_excludes_needed_labelled": sum(r["class_size"] for r in real_out),
            "wrongly_excluded_by_ambient_gate": len(wrongly),
            "wrongly_excluded_labelled": sum(r["class_size"] for r in wrongly),
            "newly_excluded_by_realised_gate": len(newly),
            "newly_excluded_on_nearmiss_column": len(newly_nm),
            "settled_by_bound_needed": sum(1 for r in rows if r["settled_needed_by"] == "bound"),
            "enumerated_needed": sum(1 for r in rows if r["settled_needed_by"] == "enumerated"),
            "settled_by_bound_nearmiss": sum(1 for r in rows if r["settled_nearmiss_by"] == "bound"),
            "enumerated_nearmiss": sum(1 for r in rows if r["settled_nearmiss_by"] == "enumerated"),
            "rows": rows,
            "seconds": round(time.time() - t0, 1),
        }
        print("n=%d: %d gated classes; ambient excludes %d, realised excludes %d, WRONGLY "
              "excluded %d (%d labelled), newly excluded %d; %d/%d needed-column verdicts "
              "settled by the bound  (%.1fs)"
              % (n, len(rows), len(amb_out), len(real_out), len(wrongly),
                 sum(r["class_size"] for r in wrongly), len(newly),
                 per_n[str(n)]["settled_by_bound_needed"], len(rows),
                 per_n[str(n)]["seconds"]), flush=True)
        for r in wrongly:
            print("    WRONGLY EXCLUDED  c=%d size=%d atoms=%d d=%d  ambient=%d  realised d+1=%s "
                  "(%s, bound %d)" % (r["c"], r["class_size"], r["n_atoms"], r["needed_degree"],
                                      r["ambient_top_layer"], r["realised_through_d1"],
                                      r["settled_needed_by"], r["bound_through_d1"]), flush=True)
    report["per_n"] = per_n

    # K5.  mg-0f24's n <= 7 verdicts, replayed.  A widening that moves one of them is a
    #      regression, not a widening.  Compared as multisets so row order cannot flatter it.
    def key(r):
        return (r["c"], r["class_size"], r["n_atoms"], r["needed_degree"],
                bool(r["ambient_gate_excludes"]), bool(r["realised_gate_excludes_needed"]),
                bool(r["realised_gate_excludes_nearmiss"]))
    k5 = {}
    for nn, v in sorted(prev["per_n"].items()):
        if int(nn) > nmax:
            continue
        want = sorted(key(r) for r in v["rows"] if r.get("needed_degree", -1) >= 0)
        got = sorted(key(r) for r in per_n[nn]["rows"])
        k5[nn] = {"rows": len(want), "identical": want == got}
        if want != got:
            diff = [x for x in got if x not in want][:3]
            failures.append("CONTROL K5: n=%s verdicts differ from mg-0f24's committed run; "
                            "first divergences %r" % (nn, diff))
    report["control_K5_replays_mg0f24_n_le_7"] = k5

    # The finding mg-0f24 asserted, re-asserted here so a later edit cannot quietly erase it.
    if nmax >= 7:
        c1 = [r for r in per_n["7"]["rows"] if r["c"] == 1]
        if len(c1) != 1:
            failures.append("ASSERTION: expected exactly one c=1 class at n=7, found %d" % len(c1))
        elif not (c1[0]["ambient_gate_excludes"]
                  and not c1[0]["realised_gate_excludes_needed"]
                  and c1[0]["realised_gate_excludes_nearmiss"]):
            failures.append("ASSERTION: the n=7 c=1 gates no longer disagree as mg-0f24 measured")

    # ------------------------------------------------------------------ THE ANSWER
    # Stated as a field so a truncated run (MGC99C_NMAX < 8) cannot be mistaken for R1's answer
    # by anything reading the JSON.  ALL_PASS over a population that never included n = 8 is the
    # vacuous-pass shape this corpus has caught twice (mg-a471, mg-9a59).
    report["R1_measured"] = nmax >= 8
    if nmax < 8:
        report["verdict_R1"] = ("NOT MEASURED -- this run stopped at n = %d.  R1 asks about "
                                "n = 8." % nmax)
    if nmax >= 8:
        v8 = per_n["8"]
        w = [r for r in v8["rows"] if r["ambient_gate_excludes"]
             and not r["realised_gate_excludes_needed"]]
        real = [r for r in v8["rows"] if r["ambient_gate_excludes"]
                and r["realised_gate_excludes_needed"]]
        if v8["iso_classes"] != 556 or v8["iso_labelled"] != 6285806:
            failures.append("REPRODUCTION: mg-0f24 recorded 556 iso classes / 6285806 labelled "
                            "at n=8; this run reads %d / %d"
                            % (v8["iso_classes"], v8["iso_labelled"]))
        if v8["ambient_gate_excludes"] != 6 or v8["ambient_gate_excludes_labelled"] != 1792:
            failures.append("REPRODUCTION: mg-0f24 recorded 6 classes / 1792 labelled declined "
                            "by the ambient gate at n=8; this run reads %d / %d"
                            % (v8["ambient_gate_excludes"], v8["ambient_gate_excludes_labelled"]))
        report["verdict_R1"] = (
            "At n = 8 the ambient gate declines %d classes / %d labelled.  The realised gate -- "
            "measured here for the first time -- declines %d of them (%d labelled) and ADMITS "
            "%d (%d labelled).  So %d of the 6 declines were the same artifact one n higher, "
            "and %d are real.  Independently, the realised gate newly excludes %d class(es) the "
            "ambient gate admitted on the needed-degree column and %d on the near-miss column; "
            "the two gates are not nested and this is where that shows."
            % (v8["ambient_gate_excludes"], v8["ambient_gate_excludes_labelled"],
               len(real), sum(r["class_size"] for r in real),
               len(w), sum(r["class_size"] for r in w), len(w), len(real),
               v8["newly_excluded_by_realised_gate"], v8["newly_excluded_on_nearmiss_column"]))
        report["completeness_R1"] = (
            "COMPLETE at n = 8, not partial: every one of the %d gated classes has a verdict on "
            "both columns.  %d needed-column and %d near-miss-column verdicts were settled by "
            "the exact bound UB(m, dmax) with no enumeration; the remaining %d and %d were "
            "enumerated against the cap.  Nothing was sampled, truncated or skipped.  The %d "
            "classes with needed_degree < 0 (c >= n) are outside the gate entirely and are not "
            "counted in either denominator (%d gated + %d ungated = %d iso classes)."
            % (v8["gated_classes"], v8["settled_by_bound_needed"],
               v8["settled_by_bound_nearmiss"], v8["enumerated_needed"],
               v8["enumerated_nearmiss"], v8["ungated_classes_c_ge_n"],
               v8["gated_classes"], v8["ungated_classes_c_ge_n"], v8["iso_classes"]))

    report["ALL_PASS"] = not failures
    report["failures"] = failures
    out = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "data", "onethird-mgc99c-n8-realised-gate.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=1, sort_keys=True)
    if "verdict_R1" in report:
        print("  " + report["verdict_R1"])
        print("  " + report["completeness_R1"])
    print("ALL_PASS =", report["ALL_PASS"])
    for x in failures[:20]:
        print("  FAIL", x)
    print("wrote", out)
    return 0 if report["ALL_PASS"] else 1


if __name__ == "__main__":
    sys.exit(main())
