# OneThird — Algebraic Program Vision

*Canonical vision for the OneThird algebraic-objects / counterexample-search program. Authored by pm-onethird per Daniel's 2026-05-28 directive. Updates require explicit Daniel input; no silent re-interpretation. Mirrored in pm-onethird's agent memory (`project_onethird_algebraic_program_vision.md`).*

## Daniel's vision, verbatim

> inspired by the recent breakthroughs in additive combinatorics and unit distance conjecture - I would like to start a program where we explore algebraic objects that can yield posets with balance constants that are computable. Then we could look at the parameter space and find a counterexample

— Daniel, 2026-05-28T11:33Z reminder, opening a new OneThird research direction in parallel to (or in pivot from) the strategy-indicted Cheeger-proof route.

## The four load-bearing parts

1. **Algebraic objects** — families of algebraic structures (candidates worth pinning: graded rings, polynomial-method constructions like Croot–Lev–Pach / slice-rank, matroid lattices, divisor / face / chain posets of algebraic varieties, finite-geometry incidence posets, additive-combinatorics extremal constructions, et al.).
2. **Yielding posets with computable balance constants** — for each algebraic family, the poset construction must be explicit, and the balance constant Q(P) — the maximum over xy of min(p(x<y), p(y<x)) — must be computable as a function of the algebraic parameters (closed-form, or at least computable from algorithm-tractable data, not just simulable).
3. **Parameter space exploration** — sweep the algebraic parameters; track how Q(P) varies; identify regions of small Q.
4. **Find a counterexample** — a poset P with Q(P) < 1/3 in width 3 would refute the conjecture. The program targets this as a candidate finding; bounded null result also informative.

## Inspiration sources

The recent breakthroughs Daniel cites:
- **Unit-distance conjecture progress** (algebraic / polynomial method on incidence problems).
- **Additive combinatorics** (slice-rank, capset, recent improvements on Erdős-Ko-Rado-type bounds, etc.) — polynomial methods that yield exact / closed-form bounds where prior combinatorial bounds were loose.

The methodological hope: where a Cheeger / cut-and-window combinatorial route delivered area/total inputs the proof couldn't use (mg-0c39's STRATEGY-INDICTED finding), an algebraic construction whose balance constant is explicitly computable could either find a counterexample or prove the conjecture sharp on a tractable subfamily.

## Status — 2026-05-28

**The program is UNTRIED in the OneThird arc.** The existing OneThird work has been Cheeger-proof-oriented (UC1-UC14, the FULL REFACTOR Pieces 1-6, the Step 8 G4 machinery). None of it explores algebraic constructions of posets-with-computable-balance-constants. This is a genuine new direction, not a rebranding of existing work.

**Relation to the (i)/(ii)/(iii) Cheeger-route decision:** Daniel's program proposal effectively introduces a fourth option — pivot to algebraic-objects exploration. The Cheeger route remains strategy-indicted; (i) multi-month genuine fix, (ii) honest conditional write-up, (iii) abandon all remain open as separate decisions. This program is non-exclusive with (ii) (conditional ship while exploring) and could inform (iii) (if the algebraic program finds a counterexample, abandon the Cheeger framing).

## Update protocol

- Updates to this document require an explicit Daniel restatement, recorded verbatim with date.
- Prior versions are annotated as superseded, not overwritten silently.
- Every algebraic-program ticket brief references this document and states which of the four parts (or which sub-step) it realizes; tickets that cannot cleanly answer that are vision-drifted and need reshaping.
- Polecat verdict relays lead with vision-alignment (does the deliverable's central object — the algebraic family chosen, the computability claim, the parameter sweep — match the vision verbatim?), not just GREEN / RED on the math.

## Cross-references

- `OneThird-Option-A-FULL-REFACTOR-scoping.md` — the prior Cheeger-route refactor scoping; this program is parallel/alternative.
- `docs/onethird-strategic-look-area-perimeter-conflation.md` (mg-0c39) — the STRATEGY-INDICTED verdict on the Cheeger route that motivates exploring fresh directions.
- pm-onethird agent memory `project_onethird_algebraic_program_vision.md` — the mirrored canonical vision.
- pm-onethird `feedback_pm_owns_the_vision.md`, `feedback_anti_drift_protocol.md` — the disciplines this arc runs under.
