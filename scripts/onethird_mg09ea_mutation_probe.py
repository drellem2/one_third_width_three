#!/usr/bin/env python3
"""
mg-09ea -- CAN THE mg-2c34 CONTROL SUITE FAIL?

The mg-2c34 ticket required a positive control: the instrument must be shown to
produce the WRONG answer on a case where the answer is known, before it is
trusted on the unknown one.  mg-2c34 supplies four controls and mutation-tests
three of them.  This probe asks the complementary question the audit is for:
which WRONG instruments does the shipped gate let through?

Method.  Each mutation is applied to the SHARED dependency module -- so both
the measurement and mg-4a86's reference instrument see the bug, which is the
realistic shape of a genuine coding error (a bug that only one of two copies
has is not how code goes wrong).  The whole scripts/ tree is copied to a temp
directory first; nothing in the repo is modified.  The CI gate mode
(--no-sweep) is then run and its exit status recorded.

Result at the time of the audit (docs/OneThird-mg2c34-n7-Overlap-Test-
IndependentAudit.md sec 3):

    M1  BK step 1/(n-1) not 1/(2(n-1))        NOT CAUGHT (exit 0)
    M2  U shrunk (drop element-0 and -1)      NOT CAUGHT (exit 0)
    M3  BK swaps COMPARABLE adjacent pairs    caught (crash)
    M4  slow mode read at lambda_3            caught (crash)
    M5  lambda_std not symmetrised            caught (identity check)

M1 is the consequential one: it changes every lambda_2^BK, hence every
R = (1-lambda_std)/(1-lambda_2^BK) in the deliverable's sec 6, and nothing
fires -- because the identity check READS ref["bk_lambda2"] out of the
committed mg-8b64 dataset and never compares it.

Run:  /usr/bin/python3 scripts/onethird_mg09ea_mutation_probe.py
      (needs numpy; ~5 min -- each mutation runs the full 40 s gate)
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (label, file to patch, exact old text, new text, what it breaks)
MUTATIONS = [
    ("M1  BK rate doubled (step 1/(n-1), not 1/(2(n-1)))",
     "onethird_mg4a86_standard_dominance_target_audit.py",
     "    step = 1.0 / (2 * (n - 1)) if n > 1 else 0.0",
     "    step = 1.0 / (1 * (n - 1)) if n > 1 else 0.0",
     "every lambda_2^BK, hence every R = (1-lam_std)/(1-lam2) in sec 6"),

    ("M2  U genuinely shrunk (drop the element-0 AND element-1 blocks)",
     "onethird_mg4a86_sector_leakage_and_tempering.py",
     "            M[r, x * n + a] = 1.0",
     "            M[r, x * n + a] = 0.0 if x < 2 else 1.0",
     "the subspace U that c is measured against"),

    ("M3  BK walk swaps COMPARABLE adjacent pairs (predicate flipped)",
     "onethird_mg4a86_standard_dominance_target_audit.py",
     "            if not P.comparable(a, b):",
     "            if P.comparable(a, b):",
     "the BK generator entirely"),

    ("M4  slow mode read at lambda_3 instead of lambda_2",
     "onethird_mg2c34_n7_overlap_test.py",
     "    lam2 = ev[1]\n    idx = [j for j in range(1, len(ev)) "
     "if abs(ev[j] - lam2) < tol]",
     "    lam2 = ev[2]\n    idx = [j for j in range(1, len(ev)) "
     "if abs(ev[j] - lam2) < tol]",
     "which mode is called 'the slow mode'"),

    ("M5  lambda_std NOT symmetrised (S = T, not (T+T^T)/2)",
     "onethird_mg4a86_standard_dominance_target_audit.py",
     "    S = (T + T.T) / 2.0\n    B = _ortho_H_basis(n)",
     "    S = T\n    B = _ortho_H_basis(n)",
     "lambda_std, the numerator of R"),
]

TARGET = "onethird_mg2c34_n7_overlap_test.py"


def run_one(sandbox, label, fname, old, new, breaks):
    """Reset the sandbox, apply one mutation, run the CI gate, report."""
    shutil.rmtree(os.path.join(sandbox, "scripts"), ignore_errors=True)
    shutil.copytree(os.path.join(REPO, "scripts"),
                    os.path.join(sandbox, "scripts"),
                    ignore=shutil.ignore_patterns("__pycache__"))
    path = os.path.join(sandbox, "scripts", fname)
    src = open(path).read()
    if src.count(old) != 1:
        return (label, "PATCH-FAILED (%d matches)" % src.count(old), breaks, "")
    open(path, "w").write(src.replace(old, new))

    proc = subprocess.run(
        ["/usr/bin/python3", os.path.join(sandbox, "scripts", TARGET),
         "--no-sweep"],
        capture_output=True, text=True, cwd=sandbox)
    out = proc.stdout + proc.stderr

    if "CONTROL FAILURES:" in out:
        lines = out.split("CONTROL FAILURES:")[1].strip().splitlines()
        detail = " | ".join(x.strip() for x in lines[:4])
    elif proc.returncode != 0:
        detail = "crashed: " + (out.strip().splitlines() or [""])[-1][:120]
    else:
        # what did the three headline rows become?
        hits = re.findall(
            r"enum-n7-#(?:3|20|600)\s+\d+\s+\d+\s+[\d.]+\s+([\d.]+)\s+"
            r"[\d.]+\s+\d+\s+([\d.]+)", out)
        detail = "gate passed; (lam2, c) now " + str(hits)
    verdict = ("CAUGHT (exit %d)" % proc.returncode if proc.returncode
               else "NOT CAUGHT (exit 0)")
    return (label, verdict, breaks, detail)


def main():
    sandbox = tempfile.mkdtemp(prefix="mg09ea-mutation-")
    os.makedirs(os.path.join(sandbox, "data"), exist_ok=True)
    shutil.copy(
        os.path.join(REPO, "data",
                     "onethird-mg8b64-L1b-bk-transport-transfer.json"),
        os.path.join(sandbox, "data"))
    try:
        results = [run_one(sandbox, *m) for m in MUTATIONS]
    finally:
        shutil.rmtree(sandbox, ignore_errors=True)

    print("=" * 78)
    print("MUTATION PROBE of the mg-2c34 control suite (CI gate, --no-sweep)")
    print("=" * 78)
    escaped = 0
    for label, verdict, breaks, detail in results:
        print(f"\n{label}")
        print(f"  breaks : {breaks}")
        print(f"  verdict: {verdict}")
        if detail:
            print(f"  detail : {detail[:400]}")
        if verdict.startswith("NOT CAUGHT"):
            escaped += 1
    print()
    print("=" * 78)
    print(f"{escaped} of {len(results)} wrong instruments passed the gate.")
    print("=" * 78)
    # This probe REPORTS on another script's gate; a mutation escaping is the
    # audit finding, not a failure of this file.  Exit 0 unless a patch could
    # not be applied at all (which would mean the target has moved).
    return 1 if any(v.startswith("PATCH-FAILED") for _, v, _, _ in results) else 0


if __name__ == "__main__":
    sys.exit(main())
