# F14 / PCR-Lit-2′ cumulative state (mg-3839)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs deferred across the
multi-session (400k cap) F14 ticket.

**Branch:** `compat-geom-F14-B4-cofiber-cohomology` (mg-3839).
**Goal (mg-3839):** compute the n=4→5 cofiber cohomology
`B_4 = H̃³(Δ_5/Δ_4)` with its S₄-representation type and an explicit
basis — the **gating computation** for the general-n route (ii)
mechanism (F11 §6.2; mg-6295 §6.3's designated follow-up). HPC-class;
**no new axioms; no Lean changes.**

**Outcome (after Session 1): GREEN-cofiber-perfect.**
`b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)` concentrated in degree 3,
`B_4 = 2·sgn_{S_4}` — exactly the M1+M2 prediction and (UCC.1) at
level 4. Explicit 2-element basis delivered. n=3→4 trip-wire reproduces
mg-6295's GREEN. **F15 / (E2) unblocked.** Nothing deferred.

---

## Session ledger

### Session 1 — 2026-05-14 (this polecat, mg-3839) — DONE

**Goal:** compute B_4 = H̃³(Δ_5/Δ_4); deliver its S₄-rep type + an
explicit basis; verify against the n=3→4 trip-wire; emit a verdict.

| Item | Status | Output |
|------|--------|--------|
| Read parents: mg-6295 (M1 / PCR-Lit-2), mg-b352 (F11), mg-8216 (F10) | ✅ | — |
| Establish that the naive greedy+Forman recipe is infeasible at n=4→5 | ✅ | `C_*(Δ_5,Δ_4)` has **326 865 586** cells (DP f-vector) |
| Memory-efficient S_n-equivariant order-ideal-filtration reduction (MoveA + MoveB + all-cone PEEL) | ✅ | `H̃_d(Δ_5/Δ_4) = 2·H̃_{d-1}(Δ(A_4))`, `\|A_4\|=1420` |
| Elementary-collapse homology engine for the terminal `Δ(A_4)` (15 166 278 cells) | ✅ | collapse → residual `(195,606,413)` → `H̃_*(Δ(A_4)) = (0,0,1)` |
| Collapse-engine self-test (collapse vs direct Gaussian, 4 medium complexes) | ✅ PASS | — |
| Trip-wire n=3→4 (full pipeline) | ✅ PASS | reproduces mg-6295 GREEN `(0,0,2,0) = 2·sgn_{S_3}` |
| **Deliverable 1** — `b̃_*(Δ_5/Δ_4)` | ✅ | **`(0,0,0,2,0)`**, concentrated in degree 3 |
| **Deliverable 2** — S₄-rep type of `B_4` | ✅ | **`2·sgn_{S_4}`** (equivariant Euler char) |
| **Deliverable 3** — explicit basis of `B_4` | ✅ | `{z_D, z_U}`, explicit 2-cycles; boundary verified zero |
| **Deliverable 4** — script + docs + state ledger | ✅ | this file + the two below |
| Cross-checks: Euler char (3 ways), `2·H̃_{*-1}(A_4)` relation, cofiber LES | ✅ | all consistent |
| Verdict | ✅ **GREEN-cofiber-perfect** | see below |

**Verdict: GREEN-cofiber-perfect.** `b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)`
concentrated in degree 3, `B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}`. (UCC.1) is
**computed** (not merely predicted) at n=4→5. The reduction collapses
the 3.3×10⁸-cell relative complex onto `2·Δ(A_4)` (1.5×10⁷ cells), is
fully run-time-verified (every fibre hypothesis asserted), and
reproduces mg-6295's GREEN at n=3→4. An explicit 2-element basis is
delivered. F15 / (E2) is unblocked.

**Trust surface impact: NONE.** No new axioms; no Lean changes; pure-
Python computation + Markdown. The in-tree Lean `width3_one_third_two_thirds`
4-axiom trust surface is untouched.

**Deliverables produced this session:**
- `scripts/compat_geom_cofiber_morse_n4n5.py` (NEW) — the computation
  (adapts mg-6295's `compat_geom_cofiber_morse_n3n4.py`).
- `docs/compatibility-geometry-F14-pcr-lit2prime.md` (NEW) — the writeup.
- `docs/state-F14.md` (NEW, this file).

**Budget used:** ≈ 1 session, well under the 400k cap.

**Nothing deferred to a Session 2.** All four ticket deliverables are
addressed in Session 1. The natural follow-on is **F15 / (E2)** — compute
`∂_3 : B_3 → B_4` (a 2×2 S₃-equivariant matrix between mg-6295's explicit
`B_3` basis and F14's explicit `B_4` basis) and test it for isomorphism —
which F14 now unblocks. F15 is a separate ticket.

---

## Invariants (reproduce-on-resume)

Load-bearing facts; re-check against the cited parent docs before extending:

- `|PPF_3| = 12`, `|PPF_4| = 194`, `|PPF_5| = 4110` (F10 §1.1).
- `C_*(Δ_5,Δ_4)` has **326 865 586** relative cells, χ̃ = −2; the naive
  mg-6295 greedy+Forman recipe is infeasible at this size.
- Reduction: `H̃_d(Δ_5/Δ_4) = 2·H̃_{d-1}(Δ(A_4))` as S₄-representations,
  where `A_4 = {x ∈ PPF_5 : Down_4(x) ≠ ∅, Up_4(x) = ∅, x|_{0123} ≠ ∅}`,
  `|A_4| = 1420`, `Δ(A_4)` has 15 166 278 cells.
- `Δ(A_4) ≃ S²`: `H̃_*(Δ(A_4)) = (0,0,1)`, `H̃_2(Δ(A_4)) = sgn_{S_4}`.
- **`b̃_*(Δ_5/Δ_4) = (0,0,0,2,0)`**, **`B_4 = H̃³(Δ_5/Δ_4) = 2·sgn_{S_4}`** —
  computed, GREEN-cofiber-perfect. (UCC.1) verified at level 4.
- n=3→4 trip-wire: the identical pipeline gives `H̃_*(Δ_4/Δ_3) = (0,0,2,0)`
  `= 2·sgn_{S_3}` — reproduces mg-6295 (PCR-Lit-2) GREEN.
- The three reduction operations (MoveA/MoveB/all-cone PEEL) are the
  cluster-lemma discrete-Morse content; each step's collapse hypothesis
  is asserted at run time, not assumed.
- The factor 2 in `2·H̃_{*-1}(Δ(A_4))` is the `Down_4`/`Up_4` duality:
  the order-reversal involution gives an S₄-equivariant iso `D_4 ≅ U_4`.
- F14 does NOT compute `∂_3` — that is F15 / (E2). F14 supplies its
  codomain `B_4` + explicit basis; the reduction §1.2 of
  `compatibility-geometry-F14-pcr-lit2prime.md` is the dictionary.
