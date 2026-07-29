#!/usr/bin/env python3
"""
mg-60d3 -- MUTATION DEMONSTRATION for the two repaired controls.

The mg-09ea independent audit of mg-2c34 found that the CI gate
(`scripts/onethird_mg2c34_n7_overlap_test.py --no-sweep`, wired into
`.github/workflows/script-controls.yml`) passed on two mutations that break
numbers the deliverable asserts:

  M1  the BK step is 1/(n-1) instead of 1/(2(n-1)) -- a global rate rescaling.
      Every lambda_2^BK in sec 4's table is wrong, and every R = (1-lambda_std)
      / (1-lambda_2^BK) in sec 6 roughly halves.  NOT CAUGHT (exit 0):
        - CONTROL A never calls `bk_walk_matrix` (it synthesises its own W);
        - CONTROL B/C are eigenvector-only, and a global rescaling fixes every
          eigenvector, so c on the antichain is unchanged;
        - CHECK-0 shares the code, so both instruments carry the same bug;
        - the identity check FETCHED `ref["bk_lambda2"]` into the report and
          never compared it.                                        (audit F3)

  M2  U is genuinely shrunk: the position observables of elements 0 and 1 are
      dropped from the one-particle span.  This is invisible to CHECK-0 (both
      instruments share `projector_U`), and CONTROL B does not fire because
      c_max is a MAXIMUM over the lambda_2 eigenspace -- the favourable reading
      survives a shrink the adversarial reading does not.  `control_B_and_C`
      already computed c_min and never asserted on it.              (audit F4)

Both repairs use values the instrument already computes:

  F3  assert `match_bk_lambda2` in the identity gate  (`_identity_row_ok`)
  F4  assert `c_min` in CONTROL B alongside `c_max`   (`_antichain_row_ok`)

WHAT THIS SCRIPT DEMONSTRATES, and why it exists at all.  Appendix A's standing
lesson -- the one mg-4ad1 fixed one layer down this morning -- is that a control
asserted but never shown to FIRE is indistinguishable from no control.  So the
repairs are not merely stated here; each is run against the mutation it is
supposed to catch, under BOTH the pre-repair and the repaired gate, and the
2 x 3 exit-code matrix is asserted:

                       pre-repair gate     repaired gate
      baseline              exit 0             exit 0     (no false positive)
      M1 (BK step)          exit 0  <- bug     exit 1     (now fatal)
      M2 (shrunk U)         exit 0  <- bug     exit 1     (now fatal)

The pre-repair gate is reconstructed HERE, by substituting the two predicates'
old bodies from this file -- the deliverable's own gate has no switch that
weakens it, and must not acquire one.

This script EXITS NON-ZERO if the matrix above is not observed exactly: it is
itself a control, and it can fail.

Run:  /usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py
      (numpy required; ~12 min -- six full runs of the CI gate)

Writes `data/onethird-mg60d3-gate-mutation-demo.json`.
"""

import os
import sys
import json
import subprocess

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

GATE = os.path.join("scripts", "onethird_mg2c34_n7_overlap_test.py")

# (mutation, gate) -> required exit code.  This IS the demonstration.
EXPECTED = {
    ("none", "pre-repair"): 0,
    ("none", "repaired"): 0,
    ("M1", "pre-repair"): 0,     # the defect the audit found
    ("M1", "repaired"): 1,       # the repair, firing
    ("M2", "pre-repair"): 0,     # the defect the audit found
    ("M2", "repaired"): 1,       # the repair, firing
}

MUTATION_DESC = {
    "none": "unmutated instrument",
    "M1": "BK step 1/(n-1) instead of 1/(2(n-1)) -- global rate rescaling",
    "M2": "U shrunk: element-0 and element-1 position blocks dropped",
}


# ------------------------------------------------------------- mutations ----
def _rebind(name, fn):
    """Rebind `name` in EVERY loaded corpus module that holds a reference.

    The corpus uses `from X import f`, so patching the defining module alone
    would leave the importers on the original.  Rebinding everywhere is the
    realistic case for a coding error: both the measurement and mg-4a86's
    reference instrument see the same bug, which is exactly why CHECK-0 is
    blind to it."""
    hits = []
    for modname, mod in list(sys.modules.items()):
        if mod is None or not modname.startswith("onethird_"):
            continue
        if hasattr(mod, name):
            setattr(mod, name, fn)
            hits.append(modname)
    if not hits:
        raise SystemExit(f"mutation target {name!r} not found in any module")
    return hits


def apply_M1():
    """BK step 1/(n-1) instead of 1/(2(n-1)).  Copy of
    `onethird_mg4a86_standard_dominance_target_audit.bk_walk_matrix` with the
    one constant changed."""
    import numpy as np

    def bk_walk_matrix_MUTATED(P):
        les = P.linear_extensions()
        m = len(les)
        n = P.n
        index = {perm: i for i, perm in enumerate(les)}
        W = np.zeros((m, m))
        step = 1.0 / (n - 1) if n > 1 else 0.0        # <-- MUTATION (was 2*(n-1))
        for perm in les:
            i0 = index[perm]
            for i in range(n - 1):
                a, b = perm[i], perm[i + 1]
                if not P.comparable(a, b):
                    nb = list(perm)
                    nb[i], nb[i + 1] = nb[i + 1], nb[i]
                    W[i0, index[tuple(nb)]] += step
        for i0 in range(m):
            W[i0, i0] += 1.0 - W[i0].sum()
        return (W + W.T) / 2.0

    return _rebind("bk_walk_matrix", bk_walk_matrix_MUTATED)


def apply_M2():
    """U genuinely shrunk.  Copy of
    `onethird_mg4a86_sector_leakage_and_tempering.one_particle_span` with the
    element-0 and element-1 blocks omitted.

    NOTE this is a strictly harder mutation than the deliverable's own sec 2.6
    row 3: dropping ONE element's block is a provable no-op on U (the blocks sum
    to the constant, so any one of them is in the span of the rest), and the
    gate is right not to fire on it.  Dropping TWO genuinely shrinks U."""
    import numpy as np

    def one_particle_span_MUTATED(P):
        les = P.linear_extensions()
        m, n = len(les), P.n
        M = np.zeros((m, n * n))
        for r, perm in enumerate(les):
            for a, x in enumerate(perm):
                if x in (0, 1):                        # <-- MUTATION
                    continue
                M[r, x * n + a] = 1.0
        return M

    return _rebind("one_particle_span", one_particle_span_MUTATED)


# ---------------------------------------------------------- gate variants ---
def apply_pre_repair_gate(tmod):
    """The gate as merged at 87f0424, before the mg-09ea repairs: lambda_2^BK
    absent from the identity conjunction (F3), CONTROL B on c_max only (F4)."""

    def identity_row_ok_PRE(rec):
        return (rec["match_num_LE"] and rec["match_lambda_std"]
                and rec["match_delta"])

    def antichain_row_ok_PRE(row):
        return abs(row["c_max"] - 1.0) < 1e-8

    tmod._identity_row_ok = identity_row_ok_PRE
    tmod._antichain_row_ok = antichain_row_ok_PRE


# --------------------------------------------------------------- one case ---
def run_case(mutation, gate):
    import onethird_mg2c34_n7_overlap_test as tmod

    if mutation == "M1":
        apply_M1()
    elif mutation == "M2":
        apply_M2()
    elif mutation != "none":
        raise SystemExit(f"unknown mutation {mutation!r}")

    if gate == "pre-repair":
        apply_pre_repair_gate(tmod)
    elif gate != "repaired":
        raise SystemExit(f"unknown gate {gate!r}")

    sys.argv = [GATE, "--no-sweep"]
    return tmod.main()


# ------------------------------------------------------------------ driver --
def extract(stdout):
    """The lines that make the outcome legible: the measured lambda_2^BK and
    c_max at the named posets, the CONTROL B readings, and any failures.

    Both quantities are recorded because the two mutations damage different
    ones -- M1 moves lambda_2^BK and leaves c alone, M2 the reverse -- and each
    is quoted in sec 2.6.1 of the deliverable."""
    lam2, cmax, ctrlB, fails = {}, {}, [], []
    in_fail = False
    for line in stdout.splitlines():
        s = line.strip()
        if s.startswith("enum-n7-#") and "lam2_BK=" in s:
            # identity-check line
            lam2[s.split()[0]] = float(s.split("lam2_BK=")[1].split()[0])
        elif s.startswith("enum-n7-#") and len(s.split()) >= 12:
            # measurement-table row: name |L| dimU delta lam2 lam_std dimE
            #                        c_max c_min null frozcap froz|U
            f = s.split()
            try:
                cmax[f[0]] = float(f[7])
            except (ValueError, IndexError):
                pass
        if s.startswith("antichain-"):
            ctrlB.append(s)
        if s.startswith("CONTROL FAILURES"):
            in_fail = True
            continue
        if in_fail and s.startswith("- "):
            fails.append(s[2:])
    return lam2, cmax, ctrlB, fails


def drive():
    results = []
    ok = True
    for (mutation, gate), want in EXPECTED.items():
        print("=" * 78)
        print(f"CASE  mutation={mutation:<5} gate={gate:<11} "
              f"(expect exit {want})")
        print(f"      {MUTATION_DESC[mutation]}")
        print("=" * 78, flush=True)
        proc = subprocess.run(
            [sys.executable, os.path.abspath(__file__),
             "--case", mutation, "--gate", gate],
            cwd=REPO, capture_output=True, text=True)
        got = proc.returncode
        lam2, cmax, ctrlB, fails = extract(proc.stdout)
        for line in ctrlB:
            print("  " + line)
        for name in sorted(lam2):
            print(f"  {name:>14}  lambda_2^BK = {lam2[name]:.9f}"
                  + (f"   c_max = {cmax[name]:.6f}" if name in cmax else ""))
        for f in fails:
            print(f"  GATE FAILURE: {f}")
        verdict = "OK" if got == want else "DEMONSTRATION FAILED"
        if got != want:
            ok = False
            print(proc.stdout[-4000:])
            print(proc.stderr[-4000:])
        print(f"  --> exit {got} (expected {want})  {verdict}\n", flush=True)
        results.append({
            "mutation": mutation, "mutation_desc": MUTATION_DESC[mutation],
            "gate": gate, "expected_exit": want, "actual_exit": got,
            "PASS": got == want,
            "lambda2_BK": lam2, "c_max": cmax, "control_B_rows": ctrlB,
            "gate_failures": fails,
        })

    report = {
        "what": "mg-60d3 mutation demonstration for the mg-09ea F3/F4 repairs "
                "to scripts/onethird_mg2c34_n7_overlap_test.py",
        "gate_command": "python3 " + GATE + " --no-sweep",
        "repairs": {
            "F3": "_identity_row_ok now requires match_bk_lambda2 -- the "
                  "committed mg-8b64 bk_lambda2 was fetched and discarded",
            "F4": "_antichain_row_ok now requires c_min = 1 as well as "
                  "c_max = 1 -- CONTROL B gated on the favourable reading only",
        },
        "cases": results,
        "ALL_PASS": ok,
    }
    out = os.path.join(REPO, "data", "onethird-mg60d3-gate-mutation-demo.json")
    with open(out, "w") as f:
        json.dump(report, f, indent=2)
    print(f"wrote {os.path.relpath(out, REPO)}")

    print()
    print("-" * 78)
    print(f"{'mutation':<10} {'gate':<12} {'expected':>9} {'actual':>7}  result")
    print("-" * 78)
    for r in results:
        print(f"{r['mutation']:<10} {r['gate']:<12} {r['expected_exit']:>9} "
              f"{r['actual_exit']:>7}  {'PASS' if r['PASS'] else 'FAIL'}")
    print("-" * 78)
    if not ok:
        print("\nDEMONSTRATION FAILED: the exit-code matrix is not as asserted.")
        return 1
    print("\nDemonstration complete: both repaired controls FIRE on the "
          "mutation they cover,\nboth mutations passed the pre-repair gate, "
          "and neither repair fires on the\nunmutated instrument.")
    return 0


def main():
    if "--case" in sys.argv:
        i = sys.argv.index("--case")
        mutation = sys.argv[i + 1]
        j = sys.argv.index("--gate")
        gate = sys.argv[j + 1]
        return run_case(mutation, gate)
    return drive()


if __name__ == "__main__":
    sys.exit(main())
