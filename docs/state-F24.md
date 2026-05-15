# state-F24 — cumulative state ledger for F24 (the part-(iii) route fork) (mg-a30d)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs. deferred across the
multi-session (300k-token cap) F24 ticket.

**Branch:** `polecat-cat-mg-a30d` (mg-a30d).
**Goal (mg-a30d):** scope-and-compare the two documented routes to F10
part (iii) — Route A (HPC-per-n chamber-Morse grind) vs. Route B (the
BK/Cheeger-expansion pivot) — head-to-head, **recommend one decisively**,
and **scope the execution ticket F25**. Resolve on evidence, not a blind
commit; confirm or correct the PM lean (Route B). **Paper-and-pencil; no
new axioms; no Lean; no computation; no HPC.** Cross-repo read:
`one_third_width_three` `main.tex` / `step8.tex` (Route B / Hypothesis A)
+ mg-26fc (the two-mechanisms scoping). Targets `main`.

**Outcome (after Session 1): GREEN-route-B-recommended.**
Route B (pivot F10 part (iii) to the BK/Cheeger mechanism) is the
decisively more tractable path to milestone 1. Its entire residual gap is
**Hypothesis A** (`step8.tex` `hyp:arith`) — one `n`-independent
arithmetic inequality the in-tree paper itself isolates as "the sole
external numerical input"; it is a paper-and-pencil **constants audit**,
not a deep conjecture, and the `∃T` existential collapses to `T = T_0`.
Route A is Tier-3 HPC plus an **unscoped** `n`-uniform `(CM-rel)` proof
that **F23's own evidence disfavours** — and, even fully executed, does
not reach milestone 1. PM lean (Route B) **confirmed**, reason sharpened.
F25 scoped. See `docs/compatibility-geometry-F24-route-fork-comparison.md`.

---

## §1. Session 1 — 2026-05-15 (this polecat, mg-a30d) — DONE

**Goal:** read F23 + mg-26fc + `main.tex`/`step8.tex` (+ the Steps-1–7
constant sources); scope Route B precisely (state Hypothesis A, build the
F10-part-(iii) ⟷ BK/Cheeger dictionary, assess tractability); re-scope
Route A given F23 GREEN-descent-pinned; deliver the head-to-head
comparison + a **decisive** recommendation; scope F25.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: F23 (full) + `state-F23.md`; mg-26fc (full); `state-F22-HPC` §5; F10 `general-n-proof-synthesis.md` §6.7; `roadmap.md` | ✅ | — |
| Read in-tree spine: `main.tex` (full); `step8.tex` (Theorem E, `hyp:arith`, `thm:main-step8`, `prop:G2`, `rem:G2-order`, `rem:final-constants-audit`, `lem:small-n`); `step5.tex` `prop:single-triple` + `cor:second-moment`; `step7.tex` K_0 region | ✅ | — |
| **Route B scoped** — what it proves (= the milestone-1 `[1/3,2/3]` target), conditional on Hypothesis A *alone* (Steps 1–7 unconditional; G1–G5 discharged in `step8.tex`). The F10-part-(iii) ⟷ BK/Cheeger dictionary built. | ✅ | doc §1.1 |
| **Hypothesis A stated precisely** — `hyp:arith` form `γ²·c_5(T)·c_6·δ_0(γ) ≥ 8` + explicit form `eq:arith-explicit` `c_5^⋆(T,γ)² ≥ 128/(γ²·c_6·δ_0)`; full constants inventory with origins/dependences | ✅ | doc §1.2 |
| **Hypothesis A tractability assessed — ATTACKABLE** — it is a paper-and-pencil constants audit (the in-tree paper itself: "a purely arithmetic condition," "the sole external numerical input"). **Scoping finding:** `T`'s effect is monotone-unfavourable on both sides ⟹ `∃T` collapses to `T = T_0` (absolute) ⟹ Hypothesis A is a single inequality in `γ`. The crux: `c_5^⋆(T_0,γ)` vs. `K_0(γ,w)` asymptotics as `γ → 0`. | ✅ **HEADLINE** | doc §1.3 |
| **Route A re-scoped** — cost: Tier-3 HPC at `n=5,6,7` (`Δ_5 > 2·10⁷` cells; `Δ_6` `1.29·10⁵` vertices). Load-bearing weakness: F23 **already refuted** every `n`-uniform structural discriminator on the 3-datapoint record (F23 §4–§5) — the "datapoints seed an `n`-uniform proof" bet is partially falsified. The endgame (`n`-uniform `(CM-rel)`) is **unscoped** (F23 §7.2). Even fully executed, Route A ≠ milestone 1. | ✅ FINDING | doc §2 |
| **Head-to-head comparison + recommendation** — comparison table across 8 dimensions; **recommend Route B decisively** (single finite gap vs. HPC + unscoped endgame; Route B's success *is* milestone 1, Route A's is not; Route B is paper-and-pencil; Route B's worst case dominates). | ✅ **HEADLINE** | doc §3 |
| **PM lean confirmed + sharpened** — pm-onethird leaned Route B; confirmed on evidence. Sharper reason: Route B's gap is the in-tree paper's *sole remaining hypothesis* and resolving it *is* milestone 1; Route A doesn't reach milestone 1 even if it succeeds. | ✅ | doc §3.3 |
| **F25 scoped** — the Hypothesis A constants audit; 4 ordered subtasks; 3 named outcome verdicts (GREEN-hypothesis-A-proven / AMBER-bottleneck-located / RED-hypothesis-A-false) | ✅ | doc §4 |
| Deliverable docs written | ✅ | `docs/compatibility-geometry-F24-route-fork-comparison.md` (NEW); `docs/state-F24.md` (NEW, this file) |
| Verdict | ✅ **GREEN-route-B-recommended** | doc Verdict, §3, §5 |

**Verdict: GREEN-route-B-recommended.**

Pivot F10 part (iii) to the BK/Cheeger-expansion mechanism (`main.tex` +
Steps 1–8). Forced by three findings:

1. **Route B has a single, precisely-stated, finite residual gap** —
   Hypothesis A, one `n`-independent arithmetic inequality the in-tree
   paper isolates as "the sole external numerical input." A constants
   audit, not a deep conjecture.
2. **Route A has no comparable single gap** — Tier-3 HPC *plus* an
   `n`-uniform `(CM-rel)` proof that is unscoped and that F23's own
   evidence (every structural discriminator refuted as `n`-uniform on the
   3-datapoint record) disfavours. Even fully executed, Route A does not
   reach milestone 1.
3. **Route B's gap is paper-and-pencil polecat-attackable; Route A's is
   not.** Route B's worst case (the inequality is false/hard) names the
   exact bottleneck — better-delineated than Route A's treadmill.

Not AMBER-route-B-blocked: Hypothesis A is not "a hard open problem with
no clean attack" — the attack (the constants audit) is clear and bounded.
The uncertainty is the audit's *outcome*, not its *tractability*.

**Trust-surface impact: NONE.** Paper-and-pencil scoping; no new axioms,
no Lean changes, no computation, no HPC. The in-tree Lean
`width3_one_third_two_thirds` 4-axiom artifact is untouched.

**Deliverables produced this session:**
- `docs/compatibility-geometry-F24-route-fork-comparison.md` (NEW) — the
  structural document: Verdict, §0 the fork, §1 Route B scoped (the
  dictionary + Hypothesis A + tractability), §2 Route A re-scoped, §3 the
  head-to-head comparison + recommendation, §4 F25 scoped, §5
  establishes/does-not, §6 refs.
- `docs/state-F24.md` (NEW, this file) — cumulative state ledger.

---

## §2. The result, in one screen (reproduce-on-resume)

- **The fork** [F24 §0] — milestone 1 reduces to closing F10 part (iii)
  gap-free at general `n`. F23 left the chamber-Morse route unblocked
  only HPC-per-n. Two documented continuations: Route A (HPC-per-n
  chamber-Morse grind) vs. Route B (BK/Cheeger pivot). The fork is *which
  residual gap to attack*.
- **Route B** [F24 §1] — the in-tree `main.tex` + Steps 1–8 prove width-3
  1/3–2/3 (the `[1/3,2/3]` statement = the milestone-1 target) by a
  Cheeger-expansion dichotomy on the BK graph. Steps 1–7 unconditional;
  G1–G5 discharged in `step8.tex`. **Sole residual gap: Hypothesis A.**
  Does not use the canonical chamber-Morse cell — sidesteps the F19–F23
  wall entirely.
- **Hypothesis A** [F24 §1.2] — `step8.tex` `hyp:arith`:
  `∀ γ ∈ (0, 1/3−δ_KL) ∃ T=T(γ): γ²·c_5(T)·c_6·δ_0(γ) ≥ 8`. Explicit
  form (`eq:arith-explicit`): `c_5^⋆(T,γ)² ≥ 128/(γ²·c_6·δ_0)`. The
  in-tree paper itself: "a purely arithmetic condition on the richness
  density," "the sole external numerical input."
- **Tractability** [F24 §1.3] — a paper-and-pencil constants audit.
  Scoping finding: `T`'s effect is monotone-unfavourable on both sides
  (`c_5^⋆ ≍ T^{−O(1)}`; `w(T)` grows), and `T ≥ T_0` (absolute) is the
  only forcing constraint ⟹ optimal `T = T_0` ⟹ Hypothesis A collapses to
  a single inequality in `γ`. Crux: the `γ→0` asymptotics of
  `c_5^⋆(T_0,γ)` (Step-5 `T_0`-fat-support density) vs. `K_0(γ,w)`
  (Step-7/G3 layering depth threshold) — extract from the Steps-5/7
  proofs.
- **Route A** [F24 §2] — Tier-3 HPC at `n=5,6,7` to pin `c*_6,c*_7`,
  *then* an `n`-uniform `(CM-rel)` proof. But F23 §4–§5 already refuted
  every `n`-uniform structural discriminator on the 3-datapoint record —
  the core bet is partially falsified, and the endgame is unscoped (F23
  §7.2). Even fully executed, Route A ≠ milestone 1.
- **Recommendation** [F24 §3] — Route B, decisively. Not close. Route
  B's success *is* milestone 1; Route A's is not.
- **F25** [F24 §4] — the Hypothesis A constants audit. Paper-and-pencil,
  cross-repo read of `step1/4/5/6/7/8.tex`. 4 ordered subtasks; 3 named
  verdicts (GREEN-hypothesis-A-proven / AMBER-bottleneck-located /
  RED-hypothesis-A-false).
- **Verdict:** GREEN-route-B-recommended. Not GREEN-route-A-recommended
  (Route A is HPC + an evidence-disfavoured endgame, and doesn't reach
  milestone 1). Not GREEN-both-viable (not close — Route B dominates on
  every axis). Not AMBER-route-B-blocked (Hypothesis A *is* cleanly
  attackable — a constants audit; the uncertainty is the outcome, not the
  tractability).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **The fork is not "which mechanism is correct."** mg-26fc already
  established (GREEN-distinct-complementary) that the BK/Cheeger and
  F-series cohomological mechanisms are *both* valid, distinct-but-
  resonant attacks. The fork is *which residual gap to attack to reach
  milestone 1*.
- **Route B's residual gap is Hypothesis A — and ONLY Hypothesis A.**
  Steps 1–7 are unconditional (`main.tex`: "the rest of the cascade is
  unconditional"); the Step-8 items G1–G5 are all discharged inside
  `step8.tex` (G1 = Theorem E, proved in full; G2–G5 likewise). Do NOT
  re-open G1–G5 — they are sealed.
- **Hypothesis A is `n`-independent.** It is a *single* arithmetic
  inequality in named constants — NOT a statement about all `n`, NOT an
  `n → ∞` limit. The `n`-dependence of Theorem E (`η(γ,n) = 2/(γn)`) is
  absorbed by `lem:small-n` below `n_0(γ,T)` and by Hypothesis A above
  it.
- **The `∃T` collapse is a scoping finding asserted from `step8.tex`'s
  own constants discussion, not re-derived.** F25 subtask 1 must confirm
  the two monotonicity directions (`c_5^⋆ ≍ T^{−O(1)}` decreasing; `w(T)`
  non-decreasing) from the Steps-5/7 proofs.
- **F23's evidence against Route A is the 3-datapoint refutation.** F23
  §4–§5: every *structural* (non-criticality) discriminator of the
  candidate orbits is refuted as `n`-uniform by `c*_3, c*_5`. Do NOT
  frame Route A as "just needs more datapoints" — the datapoints already
  in hand refute the pattern Route A's endgame needs.
- **Route A is not refuted as mathematics.** It is the *less tractable
  path to milestone 1*. Its HPC datapoints retain cross-check value for
  the F10 cohomological core / methodology paper.
- **F10 cohomological core (parts i–ii) is unconditional and untouched**
  (F17+F18, `(UCC)` complete). The F19–F23 chamber-Morse arc and
  `mg-b345` (route iii) stay parked. The Lean 4-axiom trust surface is
  untouched.
- **Scope boundary** — F24 is scoping only. No HPC, no Lean, no axioms,
  no computation. F25 (the execution) is also paper-and-pencil — the
  BK/Cheeger proof is paper-level structural.

---

## §4. If F24 is reopened / a follow-on is filed — in-scope continuations

F24's verdict is decisive and its follow-on is **F25** (scoped in doc
§4): the Hypothesis A constants audit. F25 is the natural next polecat
ticket — paper-and-pencil, cross-repo read of `step1/4/5/6/7/8.tex`,
~300k cap, high priority, multi-session-able.

If F24 itself is reopened (e.g. Daniel pushes back on the
recommendation):

- The comparison is in doc §3.1 (the 8-dimension table) — every row is
  sourced. The recommendation can be re-litigated row by row.
- The one place the verdict could move: if an F25 pre-scan found
  Hypothesis A's `c_5^⋆(T_0,γ)` *provably* decays faster than `1/γ` (so
  the inequality is false on the whole small-`γ` window with no
  re-proof slack), that would be RED-hypothesis-A-false — but that is
  F25's *outcome*, and even then Route B's worst case (a precisely-
  located Daniel-level finding) still dominates Route A's treadmill. The
  verdict GREEN-route-B-recommended is about *tractability of the
  investigation*, and stands regardless.
- Not in scope to reopen: the mg-26fc two-mechanisms verdict, the F23
  GREEN-descent-pinned verdict, the F10 cohomological core.

---

## §5. References

- mg-a30d — F24 (this ticket).
  `docs/compatibility-geometry-F24-route-fork-comparison.md`, this file.
- mg-531f — F23 (the canonical descent rule): **GREEN-descent-pinned
  (HPC-per-n).** **Parent.**
  `docs/compatibility-geometry-F23-canonical-descent-rule.md` §4–§5 (the
  3-datapoint `n`-uniform-pattern refutation — the evidence against
  Route A), §6 Finding 6.1 (HPC-per-n decisive), §7.2 (the `n`-uniform
  `(CM-rel)` proof "not attempted"), §8 (the two continuations — the
  fork). `docs/state-F23.md`.
- mg-26fc — the two 1/3–2/3 mechanisms:
  **GREEN-distinct-complementary.**
  `docs/compatibility-geometry-structural-analogy-scoping.md` (the
  BK/Cheeger column rigorised; the F10 ⟷ BK/Cheeger dictionary toolkit;
  Hypothesis A vs. (FG-Cofiber) as distinct gaps).
- mg-0c5d — F22-HPC Session 2 (**RED-tripwire**): `docs/state-F22-HPC.md`
  §5 (the descent wall; Route A = route 2 "accept HPC-per-n").
- mg-43fb — F22-HPC Session 1 (GREEN-partial).
- mg-a2cb — F21 (GREEN-needs-hpc-anchor): Prop F21.1; Finding 2.1; §5.3
  (chamber-Morse greedy HPC for `n ≥ 5`).
- mg-c3fa — F20 (GREEN-partial): §1.3.
- mg-4d3a — F17 (`(UCC.1)`); mg-d039 — F18 (`(UCC.2)`) — the F10
  cohomological core, unconditional.
- mg-8216 — F10 (GREEN-conditional): `docs/general-n-proof-synthesis.md`
  §6.7(iii) (part (iii)); §5.4 ((ICOP-step)); §7.3 (the width-3 bridge).
- In-tree: `main.tex` (the BK/Cheeger program; the "crude constants"
  note); `step8.tex` (`hyp:arith` = Hypothesis A; `thm:main-step8`;
  `rem:final-constants-audit` = `eq:arith-explicit` + the constants
  inventory; G1–G5 discharged; `lem:small-n`); `step5.tex`
  (`prop:single-triple`, `cor:second-moment` — `c_5^⋆`, `T_0`);
  `step4/6/7.tex` (the sources of `c_4,C_4,C_2(T)` / `c_6` / `C_7,w,K_0`
  — F25's audit targets).

---

*Cumulative state doc for mg-a30d (F24). Session 1 DONE — verdict
**GREEN-route-B-recommended**. Branch `polecat-cat-mg-a30d`. Pivot F10
part (iii) to the BK/Cheeger-expansion mechanism: its entire residual gap
is **Hypothesis A** (`step8.tex` `hyp:arith`), one `n`-independent
arithmetic inequality the in-tree paper isolates as "the sole external
numerical input" — a paper-and-pencil constants audit, with the `∃T`
existential collapsing to `T = T_0`. Route A (HPC-per-n chamber-Morse
grind) is Tier-3 HPC plus an unscoped `n`-uniform `(CM-rel)` proof that
F23's own evidence disfavours, and does not reach milestone 1 even if
executed. PM lean (Route B) confirmed and sharpened. F25 scoped — the
Hypothesis A constants audit. No new axioms; no Lean changes; no
computation; no HPC.*
