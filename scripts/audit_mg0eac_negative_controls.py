#!/usr/bin/env python3
"""INDEPENDENT AUDIT of mg-0eac sec.9 -- NEGATIVE CONTROLS.

A positive control that cannot be made to FAIL on a deliberately broken input
is not a control.  This module corrupts each engine / gate in turn and checks
that the merged work's own assertions catch it.

Findings recorded in docs/OneThird-CounterexampleSearch-C-IndependentAudit.md:

  * corrupting Q_primary (M1 as the CONTROLS call it) -> CAUGHT
  * corrupting Q_brute   (M4)                          -> CAUGHT
  * forcing delta = 1/4 inside the sweep                -> CAUGHT (SubBetaHalt)
  * corrupting fast_Q (the engine the SWEEP runs)       -> NOT CAUGHT at audit
                                                           time (Finding F2);
                                                           CAUGHT since mg-8489
  * corrupting width_value_bitmask                      -> *** NOT CAUGHT ***  (Finding F3)

The last two were the audit's structural findings: the control gate did not
cover `fast_Q`, and the width-prune certification shares its width oracle with
the prune it certifies.  Both were closed EMPIRICALLY by
`audit_mg0eac_completeness.py` (0 disagreements) -- neither is an actual bug.

F2 has since been closed STRUCTURALLY too: mg-8489 added `fast_Q` to
`five_engine_check` as engine M0, so the fast_Q row below now expects CAUGHT.
See `scripts/onethird_mg8489_fastq_gate_control.py` for the dedicated
can-it-fail control on the extended gate.  F3 remains open as a structural gap.

Usage:  python3 scripts/audit_mg0eac_negative_controls.py
"""
import os
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import onethird_ap2_prong3f_beta_selfdual_n11_13_exhaust as F
import onethird_mg0eac_primitive_delta_search as M
import onethird_mg0eac_width3_gap_search as W

RESULTS = []


def record(name, caught, detail, expected_caught=True, finding=None):
    """`finding` names the audit finding this gap corresponds to (F2/F3); such
    rows are EXPECTED not to be caught, but are still reported as findings."""
    status = "CAUGHT" if caught else "NOT CAUGHT"
    if caught != expected_caught:
        verdict = "*** UNEXPECTED -- re-audit ***"
    elif finding:
        verdict = f"*** AUDIT FINDING {finding} ***"
    else:
        verdict = "control behaves correctly"
    RESULTS.append((name, status, verdict, detail, bool(finding)))
    print(f"  {name:<52} {status:<11} {verdict}")
    if detail:
        print(f"      {detail[:150]}")


def try_controls():
    """Run the gate; return (caught, detail)."""
    try:
        W.positive_controls(verbose=False)
        return False, ""
    except Exception as ex:
        return True, f"{type(ex).__name__}: {ex}"


def main():
    print("=" * 96)
    print("NEGATIVE CONTROLS -- deliberately break the engine, confirm the gate FAILS")
    print("=" * 96)

    # --- 1. corrupt Q_primary: the M1 that five_engine_check actually calls -- #
    orig = F.Q_primary
    def broken_primary(elems, bd, *a, **k):
        e, Q, arg = orig(elems, bd, *a, **k)
        return e, (Q + Fraction(1, 10**6) if Q is not None else Q), arg
    F.Q_primary = broken_primary
    record("corrupt Q_primary (M1, control path) +1e-6", *try_controls())
    F.Q_primary = orig

    # --- 2. corrupt Q_brute: the M4 brute-force cross-check ----------------- #
    orig4 = F.Q_brute
    def broken_brute(elems, bd, *a, **k):
        e, Q = orig4(elems, bd, *a, **k)
        return e, (Q + Fraction(1, 7919) if Q is not None else Q)
    F.Q_brute = broken_brute
    record("corrupt Q_brute (M4, cross-check) +1/7919", *try_controls())
    F.Q_brute = orig4

    # --- 3. corrupt fast_Q: the engine EVERY SWEEP actually runs ------------ #
    # FINDING F2 (as audited at a90f0f7): five_engine_check never called fast_Q,
    # so the gate was blind to a fault in the exact code path that produces
    # every swept delta -- this row recorded *** NOT CAUGHT ***.
    #
    # CLOSED by mg-8489, which added fast_Q to the gate as engine M0.  The row
    # now expects CAUGHT, so this script keeps working as a live control
    # instead of asserting a gap that no longer exists.  The finding itself
    # stands as audited; only its remediation state has changed.
    origf = F.fast_Q
    def broken_fast(n, below):
        e, d, arg = origf(n, below)
        return e, (d + Fraction(1, 10**6) if d is not None else d), arg
    F.fast_Q = broken_fast
    caught, detail = try_controls()
    record("corrupt fast_Q (SWEEP path) +1e-6", caught, detail,
           expected_caught=True)
    F.fast_Q = origf

    import inspect
    src = inspect.getsource(F.five_engine_check)
    engines = [s for s in ("Q_primary", "ap0_Q_via_dp", "IndPoset", "ehrhart_Q",
                           "Q_brute", "fast_Q") if s in src]
    print(f"\n      five_engine_check calls: {engines}")
    print(f"      'fast_Q' in five_engine_check: {'fast_Q' in src}")
    print(f"      fast_Q is Q_primary: {F.fast_Q is F.Q_primary}")
    print(f"      delta_of (used by every sweep) calls fast_Q: "
          f"{'fast_Q' in inspect.getsource(M.delta_of)}\n")

    # --- 4. does the SubBetaHalt guard actually fire, or pass silently? ------ #
    def sub_third(n, below):
        e, d, arg = origf(n, below)
        return e, (Fraction(1, 4) if (d is not None and n >= 5) else d), arg
    F.fast_Q = sub_third
    M.fast_Q = sub_third
    try:
        W.enumerate_width_le(3, 6, verbose=False, keep_top=2)
        record("force delta=1/4 in sweep (SubBetaHalt guard)", False, "", True)
    except M.SubBetaHalt as ex:
        record("force delta=1/4 in sweep (SubBetaHalt guard)", True, str(ex))
    F.fast_Q = origf
    M.fast_Q = origf

    # --- 5. corrupt the width oracle shared by prune AND its certification -- #
    # FINDING F3: certify_width_prune filters width2_families through the same
    # width_value_bitmask it uses for the prune, so both sides move together.
    origw = W.width_value_bitmask
    def broken_width(n, below):
        v = origw(n, below)
        return v + 1 if n >= 5 else v
    W.width_value_bitmask = broken_width
    try:
        W.certify_width_prune(nmax=7, verbose=False)
        record("corrupt width oracle (prune certification)", False, "",
               expected_caught=False, finding="F3")
    except AssertionError as ex:
        record("corrupt width oracle (prune certification)", True, str(ex))
    W.width_value_bitmask = origw

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    for name, status, verdict, _detail, _f in RESULTS:
        print(f"  {name:<52} {status:<11} {verdict}")
    findings = [r for r in RESULTS if r[4]]
    unexpected = [r for r in RESULTS if "UNEXPECTED" in r[2]]
    print(f"\n  Controls that behave correctly:     "
          f"{len(RESULTS) - len(findings) - len(unexpected)}/{len(RESULTS)}")
    print(f"  Structural audit findings still open (F3): {len(findings)}")
    print(f"  Unexpected results (would invalidate this audit): {len(unexpected)}")
    print("  => The control gate IS a real control (it fails on broken input).")
    print("     F2 (gate did not cover fast_Q) is CLOSED by mg-8489: fast_Q is")
    print("     now engine M0 in five_engine_check and corrupting it is caught.")
    print("     F3 (width-prune certification shares its width oracle) remains")
    print("     open as a structural gap; closed empirically, and the doc's")
    print("     sec.9.2 now states the certification as oracle-conditional.")


if __name__ == "__main__":
    main()
