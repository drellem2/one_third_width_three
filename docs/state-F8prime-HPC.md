# F8'-HPC cumulative state (mg-3bf3)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries.  See here for ledger of what's done vs deferred.

**Branch:** `compat-geom-F8p-hpc-n6` from `compat-geom-F8prime-n6-icop`
(parent F8' mg-7b3b @ `7a8607f`).

## Session ledger (session 1 = this polecat, mg-3bf3)

### Session 1: 2026-05-14 (this polecat)

**Goal:** Execute the 4 HPC-class steps deferred from F8' §4.1.

**Completed:**

| Phase | Status | Output |
|-------|--------|--------|
| 1. PPF_6 enumeration | ✅ GREEN | `_n6_cache/ppf6.pkl`, \|PPF_6\| = 129 302 |
| 3. Burnside Σ over non-id S_6 classes | ✅ GREEN | `_n6_cache/burnside.pkl`, clean Lefschetz at 10/11 |
| 3a. Out(S_6) outer-twin audit | ✅ GREEN | All 3 twin pairs χ̃-equal; no Out(S_6) deviation |
| 6. Pr re-verification along c*_6 | ✅ GREEN | 4/4 BFT-sharp, matches mg-7b3b |
| 7. Doc + state | ✅ | `docs/compatibility-geometry-F8prime-HPC.md` |

**Deferred / partial (recorded as AMBER-budget-cap):**

| Phase | Status | Reason | Pickup |
|-------|--------|--------|--------|
| 3b. χ̃(Δ_6) direct bitmask DP | ⏳ attempted | ~10-min/layer Python loop; ~14 layers; may exceed single-session window | session 2 — continue `posn_n6_chi_tilde_full.py`; cache `_n6_cache/chi_tilde_full.pkl` per-layer |
| 2. Chamber Morse at n=6 | ⏳ structural | Orbit grouping (~5-10 min) + chamber poset + matching — feasible but tight for session 1 budget | session 2 — extend `posn_n6_hpc.py --phase=morse` |
| 8. Plan B Forman literal cocycle | ⏳ structural | Linear system ~22 000 × 22 000 over ℚ — HPC-within-HPC | session 3 — adapt `posn_equivariant_matching_n5_planH.py` to n=6 |

### Session-1 verdict

**GREEN-clean-extension** for the core cohomological deliverable
(m_sgn = 1, no Out(S_6) deviation), with **structural extrapolation**
on the constructive Plan B Forman cocycle and on the chamber Morse
critical-cell vector at n=6.

This **resolves mg-3219** (Out(S_6) audit at n=6) — see
`docs/compatibility-geometry-F8prime-HPC.md` §4 for the per-pair
table.

> **mg-3219 follow-up (2026-05-14, branch `compat-geom-out-s6-audit-n6`).**
> The deep Out(S_6) audit is now executed: see
> `docs/compatibility-geometry-out-s6-audit-n6.md` +
> `scripts/posn_n6_out_s6_audit.py`. Verdict **GREEN-Out-robust** — it
> builds an *explicit* outer automorphism (no longer cited folklore),
> confirms χ̃(Fix) is Out-invariant on all 11 classes, and disentangles
> the n=5/n=6 sign flip as the degree-parity factor (−1)^{n−2}, NOT an
> Out effect. That audit also flags a documentation slip in this doc /
> `posn_n6_hpc.py`: the stated n=5 identity "+sgn" and the universal
> "+(1/|S_n|)·Σ" Burnside formula are even-n-only; the correct general
> form is χ̃(Fix(σ)) = (−1)^{n−2}·m_sgn·sgn(σ). The n=6 result here is
> **unaffected** (n=4 calib + n=6 result are both even n). See Q1 note
> below; one-line correction recommended as cleanup.

### How session 2 should pick this up

If session 2 (next polecat with `--depends-on=mg-3bf3`) wants to
upgrade AMBER-budget-cap → GREEN on the constructive Plan B Forman
cocycle:

1. Load `_n6_cache/ppf6.pkl`, `_n6_cache/burnside.pkl` (this session
   already produced these).
2. Run `python3 posn_n6_hpc.py --phase=orbits` to compute the
   PPF_6 / S_6 orbit decomposition (~5-10 min).  Cached to
   `_n6_cache/orbits.pkl`.
3. Build chamber poset + greedy Morse matching: extend `posn_n6_hpc.py`
   with a `phase_morse` (`build_chamber_poset` + `chamber_morse_matching`
   stubs already in place; need real implementation).
4. Implement Plan B Forman BFS: port `posn_equivariant_matching_n5_planH.py`
   to n=6 — the structural approach is the same (find ω_naive,
   identify bad cofaces, solve d(ω + ψ) = 0 over rationals).

If session 2 wants to upgrade AMBER → GREEN on the χ̃(Δ_6) direct DP:

1. Continue / restart `posn_n6_chi_tilde_full.py` from its last
   completed layer (script writes partial f-vector to cache).
2. Alternatively, port to numpy / C-extension for ~10× speedup.

## Open questions / followups

- **Q1.**  Does the n=4,5 clean Lefschetz identity χ̃(Fix(σ)) = +sgn(σ)
  hold for σ = id at n=6, i.e. χ̃(Δ_6) = +1?  Session-1 evidence: 10/11
  classes verified; identity-class deferred.  Direct DP attempted in
  §6.1 of the F8'-HPC doc.
- **Q2.**  Is the chamber Morse critical-cell vector at n=6 exactly
  `(0, 0, 0, 0, 1, 0, 0, …)` — i.e., one critical 4-cell, no
  others?  Structurally extrapolated from F2/F5/F6 pattern in §6.2;
  not verified by direct computation in session 1.
- **Q3.**  Is the F7' Plan B Gaussian elimination over ℚ tractable at
  n=6 (linear system size ~22k × 22k)?  Deferred to session 3.
