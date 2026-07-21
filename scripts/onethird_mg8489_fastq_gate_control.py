#!/usr/bin/env python3
"""mg-8489 -- NEGATIVE CONTROL for the fast_Q gate extension (audit finding F2).

Independent audit aud0eac (docs/OneThird-CounterexampleSearch-C-IndependentAudit.md,
finding F2) observed that `five_engine_check` validated Q_primary / ap0_Q_via_dp /
IndPoset / ehrhart_Q / Q_brute but never called `fast_Q` -- while `delta_of`, which
computes delta for EVERY poset in EVERY sweep, calls exactly `fast_Q`.  Corrupting
Q_primary or Q_brute was caught; corrupting `fast_Q` passed the gate untouched.

The auditor closed the gap EMPIRICALLY (fast_Q vs Q_primary over all 9 397
width-<=3 posets to n=8, and vs a from-scratch engine to n=7: 0 disagreements),
so there is NO ACTUAL BUG.  The defect was that the STATED control did not cover
the load-bearing path.  mg-8489 adds `fast_Q` to the gate as engine M0.

A control that has only ever been seen green on a new engine has not been tested
on that engine.  This script closes that loop, in the audit's own style:

  1. POSITIVE  -- the extended gate still passes on the honest engines.
  2. NEGATIVE  -- corrupt `fast_Q` three ways and confirm the gate now RAISES.
  3. REGRESSION -- confirm corrupting Q_primary is still caught (the extension
                   did not shadow the pre-existing coverage).

The corruption is applied by rebinding the module-global `fast_Q`, which is how
`five_engine_check` resolves it -- the same patching technique the audit used in
`scripts/audit_mg0eac_negative_controls.py`.

Usage:  python3 scripts/onethird_mg8489_fastq_gate_control.py
        python3 scripts/onethird_mg8489_fastq_gate_control.py --sweep [--nmax N]

Default run is the can-it-fail control (~1 second).  `--sweep` additionally
re-establishes the audit's empirical closure THROUGH THE SHIPPED GATE: it drives
every width-<=3 iso-class to n = 8 (9 398 of them, matching the audit's 9 397
plus the n=1 singleton; class counts 15, 55, 245, 1285, 7790) through the
extended `five_engine_check`.  ~60 s.  The audit compared fast_Q against
Q_primary directly; this compares them via the gate that now ships.

Exit 0 iff every row behaves as required.  Pure standard library.
"""
import argparse
import os
import sys
import time
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust as F
import onethird_mg0eac_width3_gap_search as W

# Gate inputs.  `T` is the primitive delta=1/3 attainer of sec.0; the two ladders
# are Peczarski/Olson-Sagan published pairs; the width-3 witness is the sec.9.3a
# n=10 record (delta = 6/17, the headline of the audited work).
def _cases():
    return [
        ("T",              3,  [0, 1, 0],                              Fraction(1, 3)),
        ("A3",             3,  [0, 0, 0],                              Fraction(1, 2)),
        ("L_{9;1,2,3,4}",  9,  W.ladder_L(9, (1, 2, 3, 4)),            Fraction(6, 17)),
        ("L_{10;1,5}",     10, W.ladder_L(10, (1, 5)),                 Fraction(37, 106)),
        ("sec9.3a n=10 record", 10,
         [0, 0, 1, 1, 7, 11, 43, 107, 111, 255],                       Fraction(6, 17)),
    ]


def run_gate():
    """Run the extended gate over every case.  Return (raised, detail)."""
    try:
        for name, n, below, expect in _cases():
            e, d, engines = F.five_engine_check(name, n, below)
            assert d == expect, f"{name}: delta={d} expected={expect}"
        return False, ""
    except Exception as ex:
        return True, f"{type(ex).__name__}: {ex}"


ROWS = []


def record(label, must_raise):
    raised, detail = run_gate()
    ok = (raised == must_raise)
    status = "RAISED" if raised else "passed"
    want = "must RAISE" if must_raise else "must pass"
    ROWS.append((label, status, want, ok, detail))
    print(f"  {label:<46} {status:<7} ({want})  "
          f"{'OK' if ok else '*** WRONG ***'}")
    if detail:
        print(f"      {detail[:160]}")
    return ok


def sweep_through_gate(nmax=8):
    """Drive every width-<=3 iso-class to `nmax` through the EXTENDED gate.
    Any M0-vs-M1..M4/MC disagreement raises AssertionError inside the gate."""
    print("=" * 88)
    print(f"SWEEP -- every width-<=3 iso-class to n={nmax} through the extended gate")
    print("=" * 88)
    level = {W.order_canon(1, [0]): [0]}
    F.five_engine_check("n1", 1, [0])
    tot = 1
    t0 = time.time()
    for n in range(2, nmax + 1):
        nxt = {}
        for below in level.values():
            for nb in W.children_max(n - 1, below):
                if W.width_value_bitmask(n, nb) > 3:
                    continue
                k = W.order_canon(n, nb)
                if k not in nxt:
                    nxt[k] = nb
        level = nxt
        for below in level.values():
            F.five_engine_check(f"n{n}", n, below)
        tot += len(level)
        print(f"  n={n:2d}  classes={len(level):>7,}  cumulative={tot:>7,}  "
              f"({time.time() - t0:.1f}s)", flush=True)
    print(f"  => extended gate ran on {tot:,} iso-classes to n={nmax}: "
          f"0 disagreements\n", flush=True)
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sweep", action="store_true",
                    help="also drive every width-<=3 iso-class through the gate")
    ap.add_argument("--nmax", type=int, default=8, help="sweep depth (default 8)")
    args = ap.parse_args()

    print("=" * 88)
    print("mg-8489 -- can the fast_Q-extended gate FAIL?  (audit finding F2)")
    print("=" * 88)

    allok = True

    # --- 1. positive: honest engines, gate passes -------------------------- #
    print("\n[1] POSITIVE -- extended gate on the honest engines")
    allok &= record("uncorrupted (M0 + M1..M4 + MC)", must_raise=False)

    # --- 2. negative: corrupt fast_Q, gate must now catch it --------------- #
    print("\n[2] NEGATIVE -- corrupt fast_Q (the engine every sweep runs)")
    orig_fast = F.fast_Q

    # (a) the audit's exact perturbation: delta + 1e-6.  Pre-fix this was the
    #     row recorded as *** NOT CAUGHT ***.
    def broken_add(n, below):
        e, Q, arg = orig_fast(n, below)
        return e, (Q + Fraction(1, 10**6) if Q is not None else Q), arg

    # (b) OVERSTATED delta -- the asymmetric direction the audit called out as
    #     the silent-false-negative risk: a fast_Q that inflates delta on the
    #     true minimiser hides it, and nothing downstream would ever look.
    def broken_overstate(n, below):
        e, Q, arg = orig_fast(n, below)
        return e, (Q * Fraction(1001, 1000) if Q is not None else Q), arg

    # (c) corrupt the linear-extension count instead of delta.
    def broken_e(n, below):
        e, Q, arg = orig_fast(n, below)
        return e + 1, Q, arg

    for label, fn in (("fast_Q delta + 1e-6 (audit's probe)", broken_add),
                      ("fast_Q delta OVERSTATED x1.001", broken_overstate),
                      ("fast_Q e(P) + 1", broken_e)):
        F.fast_Q = fn
        try:
            allok &= record(label, must_raise=True)
        finally:
            F.fast_Q = orig_fast

    # --- 3. regression: pre-existing coverage still live ------------------- #
    print("\n[3] REGRESSION -- pre-existing coverage not shadowed by M0")
    orig_primary = F.Q_primary

    def broken_primary(elems, bd, *a, **k):
        e, Q, arg = orig_primary(elems, bd, *a, **k)
        return e, (Q + Fraction(1, 10**6) if Q is not None else Q), arg

    F.Q_primary = broken_primary
    try:
        allok &= record("corrupt Q_primary + 1e-6", must_raise=True)
    finally:
        F.Q_primary = orig_primary

    # restored-state check: the gate must be green again after all patching
    print("\n[4] RESTORED -- engines put back, gate green again")
    allok &= record("uncorrupted (post-patch restore)", must_raise=False)

    if args.sweep:
        print()
        sweep_through_gate(args.nmax)

    print("\n" + "=" * 88)
    for label, status, want, ok, _ in ROWS:
        print(f"  {label:<46} {status:<7} {want:<12} "
              f"{'OK' if ok else '*** WRONG ***'}")
    verdict = "PASS" if allok else "FAIL"
    print("=" * 88)
    print(f"  fast_Q gate control: {verdict} "
          f"({sum(1 for r in ROWS if r[3])}/{len(ROWS)} rows as required)")
    print("=" * 88)
    if not allok:
        raise SystemExit(1)
    return 0


if __name__ == "__main__":
    main()
