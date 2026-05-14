# F9 constructive-lift cumulative state (mg-9e88)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs deferred across the
multi-session (500k cap) F9 ticket.

**Branches:** Session 1 — `compat-geom-F9-constructive-lift` (mg-9e88);
Session 2 — `compat-geom-F9-S2-n7-pattern` (mg-14a0).
**Goal (mg-9e88):** build the inductive lift ω_bal^(n) ↦ ω_bal^(n+1)
constructively, step by step, via the Plan H empirical-correction
strategy (mg-e8d5) generalized to the step n → n+1, and track the
structure of ψ^(n) across n to find a pattern that closes (I5)
*without* X_n identification.

**Outcome (after Session 2):** the direct Plan-H route closes (I5) at
n=5,6 but **provably does not generalize** — the bad-coface count is
super-polynomial and ψ^(n)'s shape is n-specific. See the Session-2
ledger entry below and `docs/compatibility-geometry-F9-session-2.md`.

---

## Session ledger

### Session 1 — 2026-05-14 (this polecat, mg-9e88) — DONE

**Goal:** Re-execute Plan H at n=6 to produce ψ^(6); document its
structure; cross-pattern with ψ^(5) from mg-e8d5; emit a verdict.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Trip-wire (a): n=5 Plan H reproduces mg-e8d5 | ✅ PASS | 10 bad cofaces, 1200 supp(ψ⁵), d=0 on bad, pairing +1; extended check reproduces mg-e8d5 §5b (12960/1680/11280) |
| Trip-wire (b): ω_naïve^(6) well-defined | ✅ PASS | Stab(c*_6) = {id} ⊂ A_6, \|S_6·c*_6\| = 720 |
| Trip-wire (c): d ω_naïve^(6) ≠ 0 on bad set | ✅ PASS | 64/64 immediate cofaces are F7-bad |
| Plan H at n=6: construct ψ^(6) | ✅ GREEN | linear system 64×314 rank 64; solvable; 64 nonzero wing orbits; \|supp(ψ⁶)\| = 46080 |
| Verify d(ω_naïve⁶+ψ⁶)=0 on bad set | ✅ GREEN | 64/64 zero |
| Verify pairing ⟨ω_naïve⁶+ψ⁶, c*_6⟩ | ✅ GREEN | = +1 |
| Cross-pattern ψ⁵ vs ψ⁶ | ✅ | shared structural **mechanism** detected (see below) |
| Script `scripts/posn_constructive_lift_n6.py` | ✅ | parameterized Plan H, runs n=5 + n=6 |
| Doc `docs/compatibility-geometry-F9-constructive-lift.md` | ✅ | full Session-1 write-up |
| State `docs/state-F9.md` | ✅ | this file |

**Session-1 verdict: GREEN-Plan-H-at-n=6.**
ψ^(6) constructed + verified; *partial* structural pattern detected;
the n-dependence of the bad-coface count is the open quantity → needs
the n=7 datapoint. Per mg-9e88 spec, GREEN triggers Session 2 at n=7.

**Key Session-1 findings:**

- **The structural mechanism (the cross-pattern lead).** At BOTH n=5
  and n=6: (M1) the Plan H constraint matrix has full row rank
  (rank = #bad cofaces); (M2) #nonzero ψ wing orbits = #bad cofaces
  exactly (10; 64); (M3) the lex-first solution is near-diagonal —
  n=5: all 10 bad cofaces have exactly 1 codim-1 face in supp(ψ)
  (pure diagonal); n=6: 63/64 have exactly 1, one has 2 (the shared
  wing orbit, which carries the isolated ψ-coefficient −2).
  ⇒ ψ^(n) is, up to isolated low-order corrections, a sum of one
  sign-rep wing-orbit cochain per F7-bad coface, with unit coefficient.

- **The open quantity.** The mechanism determines ψ^(n) *given* the
  bad-coface set. The bad-coface *count* is not yet closed-form in n:
  10 (n=5) → 64 (n=6), dominated by the position-(n−1) up-set of
  P_{n−2}: **u_5 = 4 → u_6 = 54**. Two datapoints cannot distinguish
  polynomial from exponential growth of this up-set.

- **Constructive advance over F8'-HPC.** mg-3bf3 §6.3 estimated the
  n=6 Plan B/H linear system at ~22 000 × 22 000 ("HPC-within-HPC")
  and delivered only the cohomological *existence*. F9 shows the
  *orbit-reduced* system is just 64 × 314 — solved exactly over ℚ in
  ~4 s. The S_6-equivariance reduction is the key the F8'-HPC
  estimate did not exploit.

- **Orbit-representative subtlety (recorded for honesty).** The F5
  lex-min cover-set chain (which c*_6 ι_5-lifts from) is a *different*
  S_5-orbit than F7's Hasse c*_5: it has stabilizer {id, (0 2)} with
  (0 2) odd, so it is *not* sign-supported at n=5. The (0,2) step-4
  cover + free element 5 break this; c*_6 has trivial stabilizer and
  *is* sign-supported. F8'/F8'-HPC only used the cover-set chain for
  its (sign-agnostic) Pr-profile, so no prior result is affected. The
  Plan H *mechanism* compared is an S_n-orbit-level invariant, so the
  cross-pattern is sound. F9 uses F7's Hasse c*_5 as the n=5 anchor
  (the actual mg-e8d5 cell).

### Session 2 — n=7 — 2026-05-14 (this polecat, mg-14a0) — DONE

**Goal:** test whether the §5.2 mechanism is *predictive* at n=7 and
whether the bad-coface count fits a low-degree polynomial.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Trip-wire (a): n=5 + n=6 reproduce Session 1 | ✅ PASS | reproduced *through the new `solve_psi_fast` code path* — n=5: 10 bad, 10×36 rank 10, supp 1200; n=6: 64 bad, 64×314 rank 64, supp 46080; both pairing +1 |
| Trip-wire (b): ω_naïve^(7) well-defined | ✅ PASS | Stab(c*_7) = {id} ⊂ A_7, \|S_7·c*_7\| = 5040 |
| Trip-wire (c): ι_6-lift c*_6 → c*_7 well-defined | ✅ PASS | first 5 posets of c*_7 *are* c*_6; P_5 = P_4 ∪ {(0,5)}, single-pair cover, proper, antisymmetric |
| Build c*_7, set up Plan H at n=7 | ✅ | rank profile (3,5,6,8,9,10); 1607 immediate cofaces (by pos {0:6,1:2,3:2,6:1597}); **all 1607 F7-bad** |
| **Critical count: \|F7-bad cofaces at n=7\|** | ✅ | **B_7 = 1607**; u_7 = 1597 (10→64→1607; u: 4→54→1597) |
| S_7-equivariance reduction + solve ψ^(7) over ℚ | ✅ | 9642 wings, 9074 orbits (9016 sign-supp); system **1607×9016 rank 1607** (full row rank); 1607 nonzero orbits; \|supp(ψ⁷)\| = 8 099 280 |
| Verify d(ω_naïve⁷+ψ⁷)=0 on bad set + pairing | ✅ | **1607/1607 zero**; ⟨ω_naïve⁷+ψ⁷, c*_7⟩ = +1 |
| Pattern check (mechanism persistence) | ✅ | (M1) full row rank ✓; (M2) one orbit per bad coface ✓; **(M3) near-diagonal — DEGRADES**: anomalies 0→1→**211**; new ψ-coeff **+2** ({−2,−1,+1,+2}) |
| Count-function extrapolation (+ 4th datapoint u_8) | ✅ | u_8 = 65099 (count-only); 3-pt quadratic predicts u_8 = 4633, actual 65099 (**14×**) → **decisively super-polynomial** |
| Script `scripts/posn_constructive_lift_n7.py` | ✅ | parameterized; imports Session-1 machinery; memory-efficient `solve_psi_fast` |
| Doc `docs/compatibility-geometry-F9-session-2.md` | ✅ | full Session-2 write-up |
| State `docs/state-F9.md` | ✅ | this update |

**Session-2 verdict: AMBER-pattern-shifts.** The F9 empirical Plan-H
pattern is **n=5/n=6-specific**. Plan H at n=7 *is* solvable (ψ^(7)
constructed + verified — **not** RED-pattern-breaks), and the *skeleton*
(M1)+(M2) survives, but **two findings fix the verdict**:

- **Finding A — the count is decisively super-polynomial.** B_n = 10,
  64, 1607 and u_n = 4, 54, 1597, 65099 — strictly increasing ratios.
  The 3-point quadratic interpolant (the only low-degree polynomial
  consistent with n≤7) predicts u_8 = 4633; the actual u_8 = 65099,
  **14× larger**. Polynomial growth is ruled out.
- **Finding B — the near-diagonal structure (M3) shifts meaningfully.**
  Per-bad-coface faces-in-supp(ψ): {1:1396, **2:211**} — 211 of 1607
  (13%) off-diagonal vs 0 (n=5) and 1 (n=6); new coefficient +2. The
  Session-1 "isolated low-order corrections" qualifier fails at n=7.

Both disjuncts of the state-ledger decision rule fire → **F9-fallback
datum**: the direct constructive Plan-H route does **not** close (I5)
at general n. The parked X_n / specialist route (F8'' mg-b345) is now
*indicated, not optional*. Surfaced to PM via mg-mail.

### Session 3 — polish — SUPERSEDED by the Session-2 verdict

The originally-scoped Session 3 ("general-n proof or extrapolation
table of the Plan H lift") is **moot for the constructive direction**:
Session 2 shows there is no general-n closed form to prove — the count
is super-polynomial and ψ^(n)'s shape is n-specific. The honest next
steps (PM/roadmap decision, **not** a Session-3 continuation of this
ticket):
- un-park the X_n / Quillen-fiber specialist route (F8'' mg-b345) —
  Session 2 shows it is necessary; **or** a different non-empirical
  angle on (I5);
- write up F9 Sessions 1+2 for the methodology paper as a documented
  obstruction (direct Plan-H route closes (I5) at n=5,6 but provably
  does not generalize).

---

## Budget ledger (500k cap, multi-session)

| Session | Cap | Used (est.) | Status |
|---------|----:|------------:|--------|
| 1 | ≤200k | ~180k | DONE (GREEN-Plan-H-at-n=6) |
| 2 (n=7, this) | ≤200k | ~110k | DONE (AMBER-pattern-shifts) |
| 3 (polish) | ≤100k | — | SUPERSEDED — see Session-2 verdict |

---

## Open questions / followups — RESOLVED / updated by Session 2

- **Q1 — RESOLVED.** u_7 = 1597 (u_5 = 4, u_6 = 54). A fourth datapoint
  u_8 = 65099 was computed (count-only). The sequence is **decisively
  super-polynomial**: the 3-point quadratic interpolant predicts
  u_8 = 4633, actual = 65099 (14×). Polynomial growth is ruled out.
- **Q2 — RESOLVED (negative).** The §5.2 mechanism is **not**
  predictive at n=7. (M1) full row rank and (M2) one-orbit-per-bad-coface
  *do* survive, but (M3) near-diagonality does **not**: the off-diagonal
  "anomaly" count is 0 → 1 → 211 and a new ψ-coefficient +2 appears. The
  mechanism is descriptive at n ≤ 6, not a closed form.
- **Q3 — RESOLVED.** The off-diagonal count is **not** O(1): 0, 1, 211.
  It grows substantially with n. (Why specifically 211 — i.e. the precise
  combinatorics of bad-coface wing-orbit sharing at n=7 — is not pursued;
  the program-level question is answered.)
- **Q4.** Global cocycle (Plan B Forman tail) — still deferred,
  consistent with mg-e8d5 / F8'-HPC §6.3. No longer on any F9 critical
  path: the F9 lever (the mechanism) is shown n-specific.
- **Q5 — RESOLVED (negative).** The mechanism does **not** yield the
  inductive lift ω_bal^(n) ↦ ω_bal^(n+1): there is no closed-form
  bad-coface count (super-polynomial) and no closed-form ψ^(n) shape
  (n-specific). (I5) does **not** close constructively via the direct
  Plan-H empirical route.

## Programmatic conclusion (Sessions 1+2)

The direct constructive Plan-H route — attempted per the Daniel
2026-05-14T05:18Z directive — **closes (I5) at n=5 and n=6 but provably
does not generalize**. Next steps are a PM/roadmap decision, **not** a
Session-3 continuation of this multi-session ticket:
- un-park the X_n / Quillen-fiber specialist route (F8'' mg-b345), now
  *indicated*; or pursue a different non-empirical angle on (I5);
- write up F9 Sessions 1+2 for the methodology paper as a documented
  obstruction.
