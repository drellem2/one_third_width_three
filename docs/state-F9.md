# F9 constructive-lift cumulative state (mg-9e88)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs deferred across the
multi-session (500k cap) F9 ticket.

**Branch:** `compat-geom-F9-constructive-lift`.
**Goal (mg-9e88):** build the inductive lift ω_bal^(n) ↦ ω_bal^(n+1)
constructively, step by step, via the Plan H empirical-correction
strategy (mg-e8d5) generalized to the step n → n+1, and track the
structure of ψ^(n) across n to find a pattern that closes (I5)
*without* X_n identification.

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

### Session 2 — n=7 — PENDING (conditional on Session 1 GREEN; it is)

**Goal:** test whether the §5.2 mechanism is *predictive* at n=7 and
whether the bad-coface count fits a low-degree polynomial.

**Decisive computation (cheap — does NOT need a full n=7 Plan H solve
up front):**

1. Build candidate c*_7 = ι_6-lift of the F9 c*_6 + lex-min step-5
   cover; verify Stab(c*_7) ⊆ A_7.
2. Enumerate the immediate cofaces of c*_7 — in particular the proper
   up-set of its top poset P_5 — and **record u_7**. The sequence
   u_5 = 4, u_6 = 54, u_7 = ? is the polynomial-vs-exponential
   discriminator.
3. Predict ψ^(7) from the mechanism (one diagonal wing orbit per bad
   coface, ±1) and verify d(ω_naïve⁷ + ψ⁷) = 0 on the bad set — test
   whether the mechanism *predicts*, not merely *describes*.

**Decision rule:**
- u_7 fits a low-degree polynomial AND mechanism predicts ψ^(7)
  correctly → upgrade to **GREEN-pattern-detected**; Session 3 writes
  the general-n extrapolation.
- u_7 super-polynomial OR mechanism fails to predict → empirical
  correction has no clean closed form → that is the fallback datum
  (F9-fallback / X_n route, parked per Daniel); report + surface to PM.

**Pickup instructions:**
- `scripts/posn_constructive_lift_n6.py` already runs at arbitrary n
  (n=5 and n=6 share one code path: `run_plan_h(n, chain, label)`).
  Add a `c_star_7_chain()` and call `run_plan_h(7, c7, ...)`.
- 7! = 5040; orbit decomposition and Gaussian elimination scale as
  before — expected well within Session-2 budget (≤200k tokens).
- Consider renaming the script `posn_constructive_lift.py` if it
  becomes genuinely multi-n, or add `posn_constructive_lift_n7.py`.

### Session 3 — polish — PENDING (conditional on Session 2)

**Goal (≤100k):** general-n proof or general-n empirical extrapolation
table; methodology-paper-grade write-up of the Plan H inductive lift.

---

## Budget ledger (500k cap, multi-session)

| Session | Cap | Used (est.) | Status |
|---------|----:|------------:|--------|
| 1 (this) | ≤200k | ~180k | DONE |
| 2 (n=7) | ≤200k | — | PENDING |
| 3 (polish) | ≤100k | — | PENDING |

---

## Open questions / followups

- **Q1.** What is u_7 = \|proper up-set of P_5(c*_7)\|? (u_5 = 4,
  u_6 = 54.) This single number decides polynomial-vs-exponential.
- **Q2.** Is the §5.2 mechanism *predictive* — does "one diagonal wing
  orbit per bad coface, ±1" reconstruct ψ^(7) without solving the full
  system? Session 1 only established it is *descriptive* at n ≤ 6.
- **Q3.** Why does the single off-diagonal (the −2 at n=6) occur at the
  position-1 bad coface specifically? Is the off-diagonal count
  bounded (0 at n=5, 1 at n=6 — does it stay O(1)?) or growing?
- **Q4.** Global cocycle (Plan B Forman tail) at n=6 — still deferred,
  consistent with mg-e8d5 and F8'-HPC §6.3. Not on the F9 critical
  path; F9's lever is the *mechanism*, not the global completion.
- **Q5.** If Session 2 confirms the pattern: does the mechanism +
  bad-coface-count closed form actually *yield* the inductive lift
  ω_bal^(n) ↦ ω_bal^(n+1) (i.e. close (I5) constructively), or only
  the per-n local correction? Session 3 question.
