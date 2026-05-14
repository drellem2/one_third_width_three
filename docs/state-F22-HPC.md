# state-F22-HPC — cumulative state ledger for F22-HPC (the explicit critical cells of M_rel^eq) (mg-43fb)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs. deferred across the
multi-session (1M-token cap), HPC-class F22-HPC ticket.

**Branch:** `polecat-cat-mg-43fb` (mg-43fb).
**Goal (mg-43fb):** materialise the **two critical `(n−1)`-cells** of the
perfect `S_n`-equivariant cofiber Morse matching `M_rel^eq` (F17) on
`C_∗(Δ_{n+1}, Δ_n)`, as explicit chains in `PPF_{n+1}`, for `n = 5, 6`
(and `7` if the Tier-3 budget permits). The cell-tracking upgrade of
`compat_geom_cofiber_morse_n4n5.py` / `compat_geom_F17_equivariant_morse.py`.
Deliverables: (1) the two cells at `n = 5,6,7`; (2)
`scripts/compat_geom_F22_hpc_cell_tracking.py`; (3)
`docs/compatibility-geometry-F22-hpc-critical-cells.md` with a (CM-rel)
read; (4) this ledger. **NO new axioms, no Lean changes**, no (co)homology
datapoint touching the trust surface. Targets `main`.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-43fb) — DONE

**Goal:** build the cell-tracking infrastructure; materialise `M_rel^eq`'s
critical cells as far as feasible; check (CM-rel) on the anchor data;
emit a verdict; checkpoint.

**Outcome: GREEN-partial.** See
`docs/compatibility-geometry-F22-hpc-critical-cells.md`.

### Completed

- **`scripts/compat_geom_F22_hpc_cell_tracking.py`** — the cell-tracking
  upgrade. Implements the explicit F14-reduction lift maps
  `closure-operator → PEEL → MoveB → MoveA` on top of the F17 `(Q,F)`-model
  of `A_n`. Memory-efficient: the lift never materialises `Δ(A_n)`
  (`1008 / 1.5·10⁷ / 1.35·10¹³` cells at `n = 3,4,5`). Pure-Python stdlib,
  exact arithmetic, runtime ≈ 0.1 s.
- **The two critical `(n−1)`-cells of F17's `M_rel^eq` materialised**, as
  explicit chains in `PPF_{n+1}`, for **`n = 3, 4, 5`** — the F17-structural
  (closure-operator) route, seeded with the known exact `c*_3, c*_4, c*_5`
  (F21 §2). Both `c_D` (the `D_n` summand) and `c_U = order-reversal(c_D)`
  (the `U_n` summand). Verified: genuine relative cells of
  `C_∗(Δ_{n+1},Δ_n)`, `S_n`-dual. Explicit chains in
  `docs/compatibility-geometry-F22-hpc-critical-cells.md` §2.
- **(CM-rel) checked on the anchor data — CONFIRMED at `n = 3, 4, 5`.**
  Every materialised cell has a width-2 OSA top poset with a size-2 block
  (`OSA(1,1,2)`, `OSA(1,2,1,1)`, `OSA(1,2,2,1)`) and all internal per-step
  Kahn–Saks `Pr` in `[3/11, 8/11]`. `c_D@5`'s top `OSA(1,2,2,1)` is one of
  F20 §6's 12 genuine-`G_6` candidates.
- **Cross-checks.** F14 homology reduction (imported from
  `compat_geom_cofiber_morse_n4n5.py`) gives `H̃_∗(Δ_4/Δ_3) = (0,0,2)` — the
  cofiber has 2 critical `2`-cells. `Δ(A_3)` (`1008` cells, `≃ S¹`) shown to
  admit a perfect Morse matching with critical counts `(1,1,0,0)` —
  exactly one critical `1`-cell, doubled by `D/U` to `M_rel^eq`'s two
  critical `2`-cells.
- **The load-bearing finding (§5 of the doc).** F17's `M_rel^eq` critical
  cells are **NOT** in the `S_{n+1}`-orbit of the F21-recorded chamber-Morse
  `c*_{n+1}`: `c_D`'s `|L|`-profile `(6,3,2) / (24,5,3,2)` vs. `c*_4 =
  (5,3,2) / c*_5 = (30,14,8,4)`. `c_D` carries `c*_n`'s **internal**
  structure (its internal `|L|`-profile = `c*_n`'s), not `c*_{n+1}`'s.
  Structural reason: the F21-recorded `c*_{n+1}` lies in the MoveB filter
  `Sub` (every poset of `c*_4` is in `A_3 ⊂ Sub`), hence is *matched*, not
  critical, by F17's `M_rel^eq`. So F21.1's "`c*_{n+1}` is **(the descent
  of)** a critical cell of `M_rel^eq`" needs the F18 cross-boundary
  cancellation as a genuine cell-transforming step — not a survivor-pick.
- **Docs:** `docs/compatibility-geometry-F22-hpc-critical-cells.md` (full
  results + (CM-rel) read + the finding), this ledger.

### NOT done (deferred to a continuation session)

- **The genuine `c*_6, c*_7` are NOT pinned.** The materialised `c_D@5,
  c_U@5` are `M_rel^eq@5`'s critical cells, not `c*_6`. F20's 12-candidate
  short list for `G_6` is **not resolved**.
- **`n = 6, 7` cells not materialised.** The closure-operator route at
  `n = 6` needs `c*_6` as the terminal seed (the unknown); the
  intrinsic-combinatorial route needs `Δ(A_6)` (`≫ Δ(A_5)`'s `1.35·10¹³`).
- **The F18 cross-boundary cancellation not run.** It is the step that
  produces `c*_{n+1}` from `M_rel^eq`'s cells + `c*_n` — see §2 below.

### Token budget

Session 1 used a modest fraction of the 1M cap (the closure-operator route
is cheap; the analysis — not the computation — was the load). The
remaining budget is ample for the continuation.

---

## §2. The continuation plan (for the next session)

Priority order (consistent with F21 §8 — `n = 5,6` first, `n = 7` only if
budget permits):

1. **The F18 cross-boundary cancellation tracking (the deliverable-(b)
   gate).** Implement, at the cell level, the assembly
   `M_{n+1} = M_n ⊔ M_rel^eq + cross-boundary cancellation`. **Trip-wire:**
   at `n = 4`, the cancellation of `c*_4` against `{c_D@4, c_U@4}` must
   descend to the known `c*_5` — this is the validity test. Then run it at
   `n = 5` to **produce the genuine `c*_6`**. Session 1 §5 shows this step
   is genuinely needed and genuinely missing — it is *inside* the anchor's
   remaining work, not a downstream F23 structural follow-on.
2. **`n = 6`.** With `c*_6` from sub-goal 1, the closure-operator lift gives
   `M_rel^eq@6`'s critical cells immediately (§0.3 of the doc); the
   cross-boundary cancellation at `n = 6` then gives `c*_7`.
3. **`n = 7`** — only if budget permits; as sub-goal 2, one level up.

**HPC watch.** If sub-goal 1's cross-boundary cancellation proves
Tier-3-heavy (it involves `M_n` on `Δ_n`, HPC-class beyond `n = 5` per
F20/F21), the route is the non-materialising structural cell-tracking of
the assembled `M_{n+1}` — apply the F14 / F9-S2 memory-efficiency
precedents (`solve_psi_fast`, the order-ideal-filtration reduction).
Checkpoint per session here.

**Infrastructure in place.** `scripts/compat_geom_F22_hpc_cell_tracking.py`
already has: the `(Q,F)`-model of `A_n`; the explicit `closure-operator →
PEEL → MoveB → MoveA` lift maps; the F14 reduction objects
(`R, Q_∅, S↓/S↑, D_n, U_n, A_n`); relative-cell verification; the (CM-rel)
analysis; the exact record `c*_3,4,5`; the Benedetti–Lutz random discrete
Morse engine (for materialised cross-checks). A continuation session adds
the cross-boundary cancellation on top.

---

## §3. Scope boundary (unchanged from the ticket)

F22-HPC computes the cofiber matching's critical cells (the anchor) — and,
per the Session 1 §5 finding, also owns the F18 cross-boundary cancellation
tracking needed to descend them to `c*_{n+1}`. The **`n`-uniform proof of
(CM-rel)** (that `M_rel^eq` critical cells have width-2-OSA tops for *all*
`n`) remains the separate structural follow-on **F23** — NOT in F22-HPC
scope. Session 1's (CM-rel) confirmation at `n = 3,4,5` is anchor data that
seeds F23, not a proof of the `n`-uniform statement.

---

## §4. Verdict ledger

| Session | Date | Verdict | Headline |
|---|---|---|---|
| 1 | 2026-05-14 | **GREEN-partial** | `M_rel^eq` critical cells materialised `n = 3,4,5` (F17-structural route); (CM-rel) confirmed on them; the F21.1 "(the descent of)" finding pins the cross-boundary-cancellation continuation gate. Genuine `c*_6, c*_7` not pinned. |
