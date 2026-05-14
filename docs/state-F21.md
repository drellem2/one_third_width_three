# state-F21 — cumulative state ledger for F21 (the genuine non-ι-lift canonical chamber-Morse critical cell: (CM-struct)) (mg-a2cb)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs. deferred across the
multi-session (500k cap) F21 ticket.

**Branch:** `polecat-cat-mg-a2cb` (mg-a2cb).
**Goal (mg-a2cb):** prove **(CM-struct)** — the genuine (non-ι-lift)
canonical chamber-Morse critical cell at general `n` — the milestone-1
residual re-founded by F20. Four goal items: (1) identify the genuine
`c*_n`; (2) prove `G_n` is a width-2 OSA ((L2-struct)); (3) prove the
inherited steps are BFT-sharp; (4) prove (W3-cover). Two scoping
constraints: do NOT re-attempt the ι-tower route (F20 proved it broken
for `n ≥ 7`); do NOT bundle an in-ticket HPC chamber-Morse run (Tier-3,
not single-polecat-feasible) — if HPC anchor data is needed, NAME a
separate Tier-3 ticket. NO new axioms, no Lean changes. Targets `main`.

**Outcome (after Session 1):** **GREEN-needs-hpc-anchor.** (CM-struct)
not closed; no goal item closed. F21's deliverable is the **re-founding
of the induction**: Proposition F21.1 — the genuine `c*_n` is a critical
`(n−2)`-cell of the perfect `S_{n−1}`-equivariant cofiber Morse matching
`M_rel^eq` (F17), the one surviving the F18/(UCC.2) cross-boundary
cancellation against `c*_{n−1}`. (CM-struct) **reduces** to **(CM-rel)**
(a statement about `M_rel^eq`'s explicit critical cells); completing it
needs the **Tier-3 HPC anchor F22-HPC** (the explicit `M_rel^eq` critical
cells at `n = 5,6,7`), named precisely. See
`docs/compatibility-geometry-F21-genuine-chamber-morse-cell.md`.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-a2cb) — DONE

**Goal:** attempt the dedicated structural theorem on the genuine
non-ι-lift canonical chamber-Morse critical cell; build a verification +
structural-probe harness; emit a verdict; if HPC is needed, name the
Tier-3 ticket.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: F20 (full), F19 (full), F17 §0–§7, F18 (LES/Morse phrasing), F10 §5.2–5.4/§6.2–6.6, F8 §2/§4.1/§6 | ✅ | — |
| **Exact record re-confirmed** `n = 3,4,5` — (L2-struct) + all-BFT-sharp PASS | ✅ | doc §2; harness [A] |
| **Finding 2.1** — the width/`|L|`/`Pr`-profiles of `c*_n` are NOT `n`-uniform (`c*_4` all width 2; `c*_5` is `4→3→3→2`); no closed form forced by `n ≤ 5` | ✅ FINDING | doc §2; harness [A] |
| **Absorption-constraint audit** — the F20 "G_{n+1} from G_n by absorption" FAILS at `n = 3→4` (`OSA(1,2)` not an induced subposet of `OSA(2,1,1)`); holds `n = 4→5` only | ✅ CORRECTION | doc §3; harness [B] |
| **Proposition F21.1** — the cofiber-Morse inductive structure: `c*_n` is a critical cell of the perfect `S_{n−1}`-equivariant `M_rel^eq` (F17), surviving the F18 cross-boundary cancellation. Grounded in unconditional F17+F18; ι-tower-free | ✅ **HEADLINE** | doc §4 |
| **Prop F21.1 necessary condition verified** — every `c*_n` (`n = 3,4,5`) is a *relative* cell of `(Δ_n, Δ_{n−1})`; explains F20 Correction 2 | ✅ | doc §4.3; harness [E] |
| **The reduction (CM-struct) ⟹ (CM-rel)** — (CM-struct) reduces to a statement about `M_rel^eq`'s explicit critical cells (an *explicitly-constructed* object) | ✅ | doc §5.1 |
| **Lower-bound argument** — bounded backward BFT-sharp chain search: ALL 12 width-2-OSA signatures on `[6]` (and ALL 20 on `[7]`) FEASIBLE with vast pools (`≥ 4800`, `≥ 8000`); (CM-struct)(i)+(ii) far from pinning `c*_n`; criticality cannot be sidestepped | ✅ FINDING | doc §5.2, §6; harness [C] |
| **L1 + OSA-symmetry fact re-certified** on the F21-relevant posets (incl. width-2 OSAs on `[6]`,`[7]`) | ✅ | doc §7; harness [D] |
| **Tier-3 HPC anchor ticket named** — F22-HPC: explicit critical cells of `M_rel^eq` at `n = 5,6,7` (cell-tracking upgrade of the F14/F17 reduction) | ✅ | doc §8 |
| Verification harness `scripts/compat_geom_F21_genuine_cell.py` (5 sections [A][B][C][D][E]) | ✅ runs clean | the harness |
| Verdict | ✅ **GREEN-needs-hpc-anchor** | doc §9.3, §10 |

**Verdict: GREEN-needs-hpc-anchor.**

The structural argument is **sound in form** — Proposition F21.1
re-founds the induction on the unconditional F17+F18 cohomological core,
and (CM-struct) reduces to (CM-rel) about the explicitly-constructed
`M_rel^eq` — and **genuinely needs the Tier-3 HPC anchor** (the explicit
`M_rel^eq` critical cells at `n = 5,6,7`) to complete. F21's backward-
search lower-bound argument *proves* the anchor is unavoidable: the
(CM-struct)(i)+(ii) constraints under-determine `c*_n` by orders of
magnitude. This is the outcome F20 §7 explicitly anticipated as valid;
it surfaces a clean PM/Daniel Tier-3 budget decision.

**Key structural findings:**

1. **Proposition F21.1 (the headline).** The ι-tower (F10 §5.2) is dead
   (F20 Corrections 2,3). Its principled replacement: `M_{n+1}` is
   assembled from `M_n ⊔ M_rel^eq` by the F18 cross-boundary Forman
   cancellation; `c*_n` (an `(n−2)`-cell) is *consumed* by the
   cancellation (forced — `δ_n` injective kills the inherited `sgn`-class);
   the surviving critical `(n−1)`-cell of `M_rel^eq` is `c*_{n+1}`. So the
   genuine `c*_n` is a critical cell of the perfect equivariant *cofiber*
   matching — it lives on the relative complex `C_∗(Δ_n, Δ_{n−1})`.
   Verified: every `c*_n` (`n = 3,4,5`) is a relative cell. Explains F20
   Correction 2.

2. **The F20 absorption constraint is provisional.** It is a
   single-instance pattern (holds `n = 4→5`, FAILS `n = 3→4`), not a
   proven `n`-uniform law. The F20 "`12 → s_6 ∈ {2,3}`" shortlist
   narrowing rests on it and is therefore provisional.

3. **The (CM-struct)(i)+(ii) constraints do not pin `c*_n`.** Backward
   search: every width-2-OSA signature on `[6]` and `[7]` admits a vast
   pool of all-BFT-sharp chains. Chamber-Morse *criticality* is
   load-bearing; constrained enumeration cannot substitute for it.

**What stands as the residual:** **(CM-rel)** — the two critical cells of
`M_rel^eq` have width-2-OSA top posets with BFT-sharp steps. F21 reduces
(CM-struct) to (CM-rel) and names the Tier-3 anchor (F22-HPC) that makes
(CM-rel) concrete. An `n`-uniform proof of (CM-rel) is a further
structural follow-on the anchor data seeds (doc §5.4) — the anchor is the
necessary *next gate*, not automatically sufficient.

**Trust-surface impact:** NONE. No new axioms; no Lean changes; no HPC
run. Elementary order-complex combinatorics + exact rational arithmetic +
a bounded backward search + the structural assembly of unconditional
F17+F18 results. The in-tree Lean `width3_one_third_two_thirds` 4-axiom
artifact is untouched. The named F22-HPC ticket is specified
axiom-/Lean-neutral.

**Deliverables produced this session:**
- `docs/compatibility-geometry-F21-genuine-chamber-morse-cell.md` (NEW) —
  the structural document: §1 setting, §2 the exact record + Finding 2.1,
  §3 the absorption-constraint correction, §4 Proposition F21.1, §5 the
  reduction to (CM-rel) + the lower-bound argument, §6 the backward
  search, §7 the L1 engine re-certified, §8 the named Tier-3 ticket
  F22-HPC, §9 establishes/does-not, §10 verdict + program, §11 refs.
- `docs/state-F21.md` (NEW, this file) — cumulative state ledger.
- `scripts/compat_geom_F21_genuine_cell.py` (NEW) — the verification +
  structural-probe harness; sections [A]–[E]; pure-Python stdlib; [A][B]
  [D][E] run in `< 20 s`, [C] (`--search-n6`/`--search-n7`) hard-capped +
  time-boxed.

---

## §2. The result, in one screen (reproduce-on-resume)

- **(CM-struct)** [F20 §4] — the genuine canonical chamber-Morse critical
  cells have (i) all-BFT-sharp steps, (ii) width-2-OSA top posets
  ((L2-struct)), (iii) cover every width-3 orbit ((W3-cover)). **NOT
  closed by F21**; no goal item closed.
- **Proposition F21.1** [F21 §4] — the genuine `c*_n` is a critical
  `(n−2)`-cell of the perfect `S_{n−1}`-equivariant cofiber Morse matching
  `M_rel^eq` (F17) on `C_∗(Δ_n, Δ_{n−1})`, the one surviving the
  F18/(UCC.2) cross-boundary Forman cancellation against `c*_{n−1}`.
  Grounded in unconditional F17+F18. Necessary condition (`c*_n` is a
  relative cell) verified `n = 3,4,5`.
- **(CM-rel)** [F21 §5.1] — the residual: the two critical cells of
  `M_rel^eq` have width-2-OSA top posets with BFT-sharp steps.
  (CM-struct) ⟹ (CM-rel) + the cancellation-survivor identification.
- **The F20 absorption constraint** [F21 §3] — provisional; FAILS
  `n = 3→4`. The F20 `s_6 ∈ {2,3}` narrowing is therefore provisional.
- **The lower-bound argument** [F21 §5.2] — backward BFT-sharp chain
  search: all 12 (n=6) / all 20 (n=7) width-2-OSA signatures FEASIBLE,
  vast pools. (CM-struct)(i)+(ii) far from pinning `c*_n`.
- **L1 + OSA-symmetry fact** — re-certified intact (F21 §7). (L2-struct)
  ⟹ top-step `Pr = 1/2`.
- **F22-HPC** [F21 §8] — the named Tier-3 anchor: explicit `M_rel^eq`
  critical cells at `n = 5,6,7`.
- **Verdict:** GREEN-needs-hpc-anchor. Not GREEN-cm-struct-proven (no
  goal item closed); not RED (nothing false — the absorption-constraint
  failure is a banked-heuristic correction, not a (L2-struct)
  refutation); not AMBER (real structural advance — Prop F21.1, the
  reduction, the lower-bound argument, the correction).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **`PPF_n` convention** — non-empty, non-total transitively-closed
  antisymmetric relation sets on `[n]`; `(a,b)` means `a ≺ b`; ordered by
  inclusion. `ι_n` adds element `n` free. Per-step `Pr` of a chain step
  `= |L(P_{k+1})|/|L(P_k)|`; BFT-sharp `[3/11,8/11]`.
- **The ι-tower (F10 §5.2) is DEAD** — F20 Corrections 2,3 + F21
  Proposition F21.1. Any continuation must NOT assume `c*_n` is an
  ι-lift. The correct inductive structure is the **cofiber-Morse
  induction** (Proposition F21.1): `c*_n` is a critical cell of
  `M_rel^eq`.
- **The F20 absorption constraint is PROVISIONAL** — it FAILS `n = 3→4`.
  Do NOT use it as a load-bearing constraint; the F20 `s_6 ∈ {2,3}`
  narrowing depends on it.
- **`G_n` is exact only `n ≤ 5`** — `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`,
  `G_5=OSA(2,2,1)`. The genuine `G_6, G_7` are UNKNOWN — the backward
  search shows all width-2-OSA signatures are *feasible*; only the
  chamber-Morse criticality picks the genuine one. Needs F22-HPC.
- **L1 + the OSA-symmetry fact are UNCONDITIONAL and intact** — never
  used the ι-tower; re-certified by F21 §7. (L2-struct) ⟹ `G_n` has a
  symmetric pair ⟹ top-step `Pr = 1/2`.
- **F17's `M_rel^eq`** — the perfect `S_n`-equivariant cofiber Morse
  matching on `C_∗(Δ_{n+1}, Δ_n)`, critical vector `(0,…,0,2,0)`, two
  critical `(n−1)`-cells carrying `2·sgn_{S_n}`. **F17 does NOT
  materialise the two cells** (F17 §7.2) — that is the F22-HPC target.
- **F18 / (UCC.2)** — `δ_n` injective; the cross-boundary Forman
  cancellation reducing `crit(M_n) ⊔ crit(M_rel^eq)` to a perfect
  `M_{n+1}` succeeds. Both F17 and F18 are unconditional and complete.
- **The HPC route is Tier-3** — the full chamber-Morse greedy / the
  cell-tracking F14 reduction at `n = 6,7` is HPC-class, NOT
  single-polecat-feasible (F20 §1.3). F21 NAMES F22-HPC; it does not run
  it.
- **Scope boundary** — F21 is strictly (CM-struct). The cohomological
  core (F17/F18, (UCC)) is unconditional/complete and untouched (F21
  *uses* it). Route (iii)/mg-b345 stays PARKED.
- Trust-surface impact: none. No new axioms, no Lean changes, no new
  (co)homology HPC datapoint.

---

## §4. If F21 is reopened / a follow-on is filed — in-scope continuations

The genuine next step is the **Tier-3 HPC anchor F22-HPC** (F21 §8):
materialise the two critical `(n−1)`-cells of `M_rel^eq` at `n = 5,6,7`
as explicit chains, via a cell-tracking upgrade of the F14 reduction
(`scripts/compat_geom_cofiber_morse_n4n5.py`,
`compat_geom_F17_equivariant_morse.py` are the homology-level base).
Deliverables: the explicit `M_rel^eq` critical cells; the identification
(Proposition F21.1) of which is `c*_{n+1}`; the (CM-rel) check on them;
the genuine `c*_6, c*_7` pinned (resolving F20's 12-candidate list).

If F22-HPC lands, the structural follow-on is the **`n`-uniform proof of
(CM-rel)** (F21 §5.4): the anchor data seeds it (e.g. by exhibiting a
stabilisation) but does not hand it over for free.

In-session (non-HPC) strengthenings, not load-bearing: extend the
width-3 end-goal enumeration to `m = 7`; investigate whether the
absorption constraint has a correct `n ≥ 4` or dual or chain-level form
(F21 §3 left this open).

The framework F21 leaves: do NOT re-attempt the ι-tower; use Proposition
F21.1 (the cofiber-Morse induction) and the reduction to (CM-rel).

---

## §5. References

- mg-a2cb — F21 (this ticket).
  `docs/compatibility-geometry-F21-genuine-chamber-morse-cell.md`, this
  file, `scripts/compat_geom_F21_genuine_cell.py`.
- mg-c3fa — F20 (the chamber-Morse critical-cell structure; (CM-struct)):
  **GREEN-partial.** **Parent.** F21 corrects its absorption constraint
  (§3), re-founds its (CM-struct) residual via Proposition F21.1 (§4).
- mg-5722 — F19 ((ICOP-step) + width-3 bridge): **GREEN-partial.** Lemma
  L1 re-certified by F21 §7.
- mg-4d3a — F17 (equivariant cofiber Morse): **GREEN-equivariant-uniform.**
  `M_rel^eq` perfect, 2 critical cells. **Load-bearing for Proposition
  F21.1.**
- mg-d039 — F18 ((UCC.2): `δ_n` injective): **GREEN-ucc2-proven.** The
  cross-boundary cancellation succeeds. **Load-bearing for Proposition
  F21.1.**
- mg-8216 — F10 (general-`n` synthesis): §5.2 (the ι-tower — dead;
  replaced by F21 Proposition F21.1), §6.4/§6.6 (the Morse-theoretic
  (UCC.2) + the perfect-matching framework).
- mg-1e99 — F8 (the chamber-Morse construction); mg-1e58 — F5 (the
  chamber-scale HPC-class evidence).
- mg-b345 — F8″ (route (iii)): PARKED — F21 does not touch it.

---

*Cumulative state doc for mg-a2cb (F21). Session 1 DONE — verdict
GREEN-needs-hpc-anchor. Branch `polecat-cat-mg-a2cb`. (CM-struct) is
**re-founded and reduced, not closed**: the ι-tower is replaced by the
cofiber-Morse induction (Proposition F21.1), (CM-struct) reduces to
(CM-rel) about the explicit critical cells of F17's `M_rel^eq`, the
backward-search lower-bound argument proves chamber-Morse criticality
cannot be sidestepped, the F20 absorption constraint is corrected to
provisional, and the Tier-3 HPC anchor F22-HPC is named precisely. No new
axioms; no Lean changes.*
