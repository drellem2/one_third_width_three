#!/usr/bin/env python3
"""
mg-7db4 -- MUTATION BATTERY for the scheduled blindness check.

WHY THIS EXISTS.  mg-7db4 gave the gate-mutation demonstration a trigger and
put `scripts/onethird_mg5ad1_gate_blindspot_probe.py` into the fast gate as the
standing blindness check.  A standing check that has never been shown to FAIL
is worth nothing -- that is Appendix A's lesson, it is why mg-60d3 built its
demonstration, and repeating it here would be the fourth generation of the same
mistake in the same file tree.  So the probe's checks are each run against a
mutation that is supposed to trip them, and the exit codes are asserted.

WHAT IT ALSO DOES, and this half matters more.  It records, as executable
assertions, the mutations that NOTHING in `script-controls.yml` catches.  Those
rows expect exit 0.  They are not decoration: if a later ticket closes one of
them, this battery FAILS, with a message telling whoever did it to update this
table and the doc.  A coverage table that improves silently is a coverage table
that is wrong, and the only thing worse than a documented blind spot is one
that used to be documented.

THE ROWS.  Every mutation is one line, in the defining module, applied to an
isolated copy of `scripts/` + `data/` under a temporary directory, with an
anchor assertion (exactly one occurrence before, exactly one after) so a
silently-inapplicable mutation cannot masquerade as an uncaught one.

  CAUGHT by the probe:
    M3   the Theorem-E frozen-pair selector, min -> max.  mg-5ad1's primary
         witness.  Caught by Part C's mg-7db4 `sel. ok` column -- and NOT by
         the probe as mg-5ad1 committed it, which recomputed argmin itself and
         never read what `bk_frozen_pair` returns.  Measured, not assumed.
    N1   Bernoulli variance p(1-p) -> p in `bk_pair_cut`.  A mutation NOBODY
         built a check for: it moves the argmin non-uniformly, so Part C's
         ORIGINAL comparison fires.  This is the row that answers "can the
         scheduled check fail on something unseen?" without the answer being
         circular -- the guard predates the mutation by an author who had not
         thought of it.
    N2   the gate drops `match_bk_lambda2` from `_identity_row_ok` -- the F3
         repair, reverted.  Part B parses the conjunction out of the gate
         source, so it fires.  IT DID NOT, on the first run of this battery:
         Part B's 240-character scan window ran past the end of the assignment
         it was reading and borrowed `ref["bk_lambda2"]` from the adjacent
         line, so the census reported the field as compared while the
         conjunction no longer compared it, and the probe exited 0.  Part B's
         only assertion is that the F3 repair is present, and it could not see
         the repair removed.  Fixed by bounding the window at the next
         `rec["match_`.  This row is why the battery was worth building.

         N2 WILL STOP APPLYING when mg-75f0 lands: that ticket replaces the
         `match_*` conjunction with `all(rec["field_matches"].values())` over
         the whole committed row, so N2's anchor drops to zero occurrences and
         `apply_mutation` refuses to run rather than reporting a blind spot it
         never tested.  That refusal is the mechanism working.  Re-point the
         row at the widened predicate -- mutating an ENTRY of the exclusion
         list is the strictly stronger replacement -- rather than deleting it.
    N4   the committed reference row is edited to agree with a mutated
         instrument.  Part C fires: the census compares against the file.

  CAUGHT BY NOTHING IN THE FAST GATE, recorded as such:
    M4   `projector_U`'s rank filter dropped, so numerically-null directions
         enter U and the measurement becomes vacuous by the document's own
         criterion (c = null = 1.0000 at two posets).  The probe rebuilds its
         own basis from definitions and never imports `projector_U`; the gate's
         own controls are structurally blind (mg-5ad1 sec 3.2).  UNCOVERED.
    N3   the gate drops the `c_min` clause from `_antichain_row_ok` -- the F4
         repair, reverted.  The probe does not read that predicate.  This one
         is caught by the 11-minute mg-60d3 demonstration instead (its
         M2/repaired case stops exiting 1), which is why that demonstration is
         still wired in on the paths filter rather than deleted.  UNCOVERED BY
         THE FAST GATE, covered by the paths-filtered job.
    N5   the BK step rescaled, 1/(2(n-1)) -> 1/(n-1) -- mg-09ea's M1.  Part A
         rebuilds the interchange matrix from its definition and never imports
         `bk_walk_matrix`, so the probe cannot see it.  Also covered by the
         demonstration, not by the fast gate.

  N3 and N5 are the reason both jobs exist.  Neither instrument subsumes the
  other, and a table showing that is more useful than a claim that one of them
  is sufficient.

Run:  /usr/bin/python3 scripts/onethird_mg7db4_probe_mutation_battery.py
      (numpy required; ~6 min -- eight probe runs)
Writes `data/onethird-mg7db4-probe-mutation-battery.json`.
Exits NON-ZERO if any row does not behave as the table says.
"""

import os
import sys
import json
import shutil
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROBE = os.path.join("scripts", "onethird_mg5ad1_gate_blindspot_probe.py")

# (id, target file relative to the repo root, exact text before, exact text
#  after, expected probe exit, one-line reason)
#
# expected exit 1 = the scheduled check catches it
# expected exit 0 = nothing in the fast gate catches it, ON PURPOSE and on the
#                   record.  Flipping one of these to 1 means coverage improved
#                   and this table is now a lie; the battery says so.
ROWS = [
    ("M3", "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
     'frozen = min((pc for pc in pairs if pc["ratio"] is not None),',
     'frozen = max((pc for pc in pairs if pc["ratio"] is not None),',
     1, "Theorem-E frozen-pair selector argmin -> argmax (mg-5ad1 M3)"),

    ("N1", "scripts/onethird_mg8b64_L1b_bk_transport_transfer_probe.py",
     "    var = p * (1 - p)\n",
     "    var = p\n",
     1, "Bernoulli variance p(1-p) -> p in bk_pair_cut (unseen by any author "
        "of any check here)"),

    ("N2", "scripts/onethird_mg2c34_n7_overlap_test.py",
     '    return (rec["match_num_LE"] and rec["match_lambda_std"]\n'
     '            and rec["match_delta"] and rec["match_bk_lambda2"])\n',
     '    return (rec["match_num_LE"] and rec["match_lambda_std"]\n'
     '            and rec["match_delta"])\n',
     1, "the gate drops match_bk_lambda2 -- the mg-09ea F3 repair, reverted"),

    # Not a text anchor: `"frozen_pair": [3, 5]` occurs at 54 rows of the
    # committed dataset, so a textual replace would rewrite 54 posets and
    # nobody could say which one the probe reacted to.  Row-scoped instead.
    ("N4", "data/onethird-mg8b64-L1b-bk-transport-transfer.json",
     ("json-row", "enum-n7-#3", "frozen_pair", [3, 5]),
     ("json-row", "enum-n7-#3", "frozen_pair", [0, 1]),
     1, "the committed reference row for enum-n7-#3 edited to agree with a "
        "mutated instrument"),

    ("M4", "scripts/onethird_mg4a86_sdquant_overlap.py",
     "    Q = Uu[:, s > max(tol, 1e-10)]\n",
     "    Q = Uu[:, s > 0.0]\n",
     0, "projector_U rank filter dropped -- UNCOVERED (mg-5ad1 M4)"),

    ("N3", "scripts/onethird_mg2c34_n7_overlap_test.py",
     '    return abs(row["c_max"] - 1.0) < 1e-8 and abs(row["c_min"] - 1.0) '
     '< 1e-8\n',
     '    return abs(row["c_max"] - 1.0) < 1e-8\n',
     0, "the gate drops the c_min clause -- the F4 repair reverted; UNCOVERED "
        "by the fast gate, caught by the mg-60d3 demonstration"),

    ("N5", "scripts/onethird_mg4a86_standard_dominance_target_audit.py",
     "    step = 1.0 / (2 * (n - 1)) if n > 1 else 0.0\n",
     "    step = 1.0 / (n - 1) if n > 1 else 0.0\n",
     0, "BK step rescaled (mg-09ea M1) -- UNCOVERED by the fast gate, caught "
        "by the mg-60d3 demonstration"),
]


def run_probe(workdir):
    proc = subprocess.run([sys.executable, PROBE], cwd=workdir,
                          capture_output=True, text=True)
    return proc.returncode, proc.stdout, proc.stderr


def failures_from(stdout):
    """The probe's own failure lines, for the record."""
    out, seen = [], False
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith("PROBE FAILURES"):
            seen = True
            continue
        if seen and s.startswith("- "):
            out.append(s[2:])
    return out


def stage(tmp):
    work = os.path.join(tmp, "tree")
    os.makedirs(work)
    for d in ("scripts", "data"):
        shutil.copytree(os.path.join(REPO, d), os.path.join(work, d))
    return work


def apply_mutation(work, rel, before, after):
    """Apply the one-line mutation, asserting it is exactly one line and that
    it actually landed.  A mutation that silently fails to apply would be
    reported as an uncaught blind spot, which is the worst possible error for
    this file to make."""
    path = os.path.join(work, rel)

    if isinstance(before, tuple) and before[0] == "json-row":
        _, row_name, field, old = before
        _, _, _, new = after
        with open(path) as f:
            doc = json.load(f)
        hits = [r for r in doc["rows"] if r["name"] == row_name]
        if len(hits) != 1:
            raise SystemExit(
                "battery: %s has %d rows named %s, expected exactly 1"
                % (rel, len(hits), row_name))
        if hits[0][field] != old:
            raise SystemExit(
                "battery: %s[%s].%s is %r, expected %r -- the committed "
                "reference moved and this table is stale"
                % (rel, row_name, field, hits[0][field], old))
        hits[0][field] = new
        with open(path, "w") as f:
            json.dump(doc, f, indent=2)
        return

    with open(path) as f:
        src = f.read()
    if src.count(before) != 1:
        raise SystemExit(
            "battery: anchor for %s occurs %d times in %s, expected exactly 1 "
            "-- the corpus moved and this table is stale"
            % (rel, src.count(before), rel))
    src = src.replace(before, after)
    if src.count(after) != 1:
        raise SystemExit("battery: mutation of %s did not land cleanly" % rel)
    with open(path, "w") as f:
        f.write(src)


def main():
    results = []
    ok = True

    with tempfile.TemporaryDirectory(prefix="mg7db4-battery-") as tmp:
        print("=" * 78)
        print("BASELINE -- unmutated tree, the probe must PASS")
        print("=" * 78, flush=True)
        work = stage(tmp)
        code, out, err = run_probe(work)
        print("  --> exit %d (expected 0)  %s"
              % (code, "OK" if code == 0 else "BATTERY INVALID"))
        if code != 0:
            print(out[-3000:])
            print(err[-2000:])
            print("\nThe unmutated probe does not pass, so no row below means "
                  "anything.")
            return 1
        results.append({"id": "baseline", "mutation": "none", "target": None,
                        "expected_exit": 0, "actual_exit": code, "PASS": True,
                        "caught": False, "probe_failures": []})
        shutil.rmtree(work)

        for mid, rel, before, after, want, why in ROWS:
            print()
            print("=" * 78)
            print("ROW %-4s expect probe exit %d  (%s)"
                  % (mid, want, "CAUGHT" if want else "NOT CAUGHT"))
            print("      %s" % why)
            print("      %s" % rel)
            print("=" * 78, flush=True)
            work = stage(tmp)
            apply_mutation(work, rel, before, after)
            code, out, err = run_probe(work)
            fails = failures_from(out)
            for f in fails[:6]:
                print("  PROBE FAILURE: %s" % f)
            if len(fails) > 6:
                print("  ... and %d more" % (len(fails) - 6))
            good = code == want
            if not good:
                ok = False
                if want == 0:
                    print("  !! COVERAGE CHANGED: this row is recorded as a "
                          "blind spot and the probe now CATCHES it.")
                    print("     That is good news and a stale table.  Update "
                          "ROWS here and the catch matrix in")
                    print("     docs/OneThird-mg7db4-GateDemo-Trigger.md.")
                else:
                    print("  !! THE SCHEDULED CHECK NO LONGER FIRES on a "
                          "mutation it is supposed to catch.")
                    print(err[-2000:])
            print("  --> exit %d (expected %d)  %s"
                  % (code, want, "OK" if good else "BATTERY FAILED"),
                  flush=True)
            results.append({
                "id": mid, "mutation": why, "target": rel,
                "expected_exit": want, "actual_exit": code, "PASS": good,
                "caught": code != 0, "probe_failures": fails})
            shutil.rmtree(work)

    report = {
        "what": "mg-7db4 mutation battery for the scheduled blindness check "
                "(scripts/onethird_mg5ad1_gate_blindspot_probe.py, wired into "
                ".github/workflows/script-controls.yml)",
        "probe_command": "python3 " + PROBE,
        "reading": {
            "expected_exit_1": "the scheduled check catches this mutation",
            "expected_exit_0": "NOTHING in the fast gate catches it; recorded "
                               "as a blind spot rather than left implicit",
        },
        "rows": results,
        "ALL_PASS": ok,
    }
    out_path = os.path.join(REPO, "data",
                            "onethird-mg7db4-probe-mutation-battery.json")
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print("\nwrote %s" % os.path.relpath(out_path, REPO))

    print()
    print("-" * 78)
    print("%-6s %-9s %-8s %-7s  %s" % ("row", "expected", "actual", "result",
                                       "mutation"))
    print("-" * 78)
    for r in results:
        print("%-6s %-9s %-8s %-7s  %s"
              % (r["id"],
                 "CAUGHT" if r["expected_exit"] else "not caught",
                 "CAUGHT" if r["actual_exit"] else "not caught",
                 "PASS" if r["PASS"] else "FAIL",
                 (r["mutation"] or "")[:44]))
    print("-" * 78)
    if not ok:
        print("\nBATTERY FAILED: the coverage table above is not what the "
              "scheduled check actually does.")
        return 1
    print("\nThe scheduled blindness check fires on %d mutations and is blind "
          "to %d, exactly as recorded."
          % (sum(1 for r in ROWS if r[4] == 1), sum(1 for r in ROWS if r[4] == 0)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
