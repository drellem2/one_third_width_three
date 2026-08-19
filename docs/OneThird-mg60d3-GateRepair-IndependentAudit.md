# INDEPENDENT AUDIT — the mg-60d3 CI-gate repair, audited by mg-5ad1

**Target, derived from the merge commits.** `mg-60d3` merged 2026-07-29T18:02Z into two repos:
`one_third_width_three` as **`af7fc2df`** (932 insertions, 7 files) and `onethird_program` as
**`c50ce32f`** (`STATE.md`, +13/−5). It was filed as the landing ticket for the mg-2c34 / mg-09ea
consequences and was never audited. The load-bearing part is not the prose: it edits
**`.github/workflows/script-controls.yml`** (the CI gate), **repairs two controls** in
`scripts/onethird_mg2c34_n7_overlap_test.py`, and adds **309 new lines**
(`scripts/onethird_mg60d3_gate_mutation_demo.py`) whose only job is to prove those repairs can fire.
Until now the repair and its proof-of-firing were validated only by their author.

**Auditor did not author the target and did not reuse its mutation harness.** Route in §1. `STATE.md`
was not edited; no `mg` ticket state was changed. Verdict routes to pm-onethird.

**What this audit changed in the merged artifact**, following mg-60d3's own precedent for annotating a
merged doc in place (it did the same to `OneThird-L1b-BK-Transport-Transfer-Probe.md:86`): a pointer
annotation at `docs/OneThird-mg2c34-n7-Overlap-Test.md` §2.6.1 carrying the two RED findings, a scope
note on ledger claim 27, and one factual word (§7: *"three"* → *"five"*). **No claim was struck, no
measured value touched, and the gate itself is unmodified** — the coverage fix is filed separately and
is deliberately not attempted here.

---

## §0 — Verdict

| | |
|---|---|
| **Reproduction of the 2×3 exit-code matrix** | **CONFIRMED** by a disjoint route — the *actual* pre-repair gate source at `87f0424` plus source-level mutations of the defining modules. All six cells agree. |
| **Every figure in §2.6 / §2.6.1** | **CONFIRMED exactly.** `λ₂^BK` under M1, `c` under M2, the `dim U` drops, the CONTROL B table, the bit-identical `c` under M1. Not one number is wrong. |
| **F3 repair (`match_bk_lambda2`)** | **CORRECT and non-vacuous.** Fires on **5 of 5** identity rows. |
| **F4 repair (`c_min` in CONTROL B)** | **CORRECT and non-vacuous** (`dim λ₂-eigenspace = n−1 > 1`, so `c_min` is a genuinely different reading). Fires on **3 of 3** antichains. |
| **Did the repair over-correct?** | **NO.** `c_min = 1` is true to `≤ 2.7e-15` against a `1e-8` tolerance, and not knife-edge: `3.0e7–1.1e8 ×` `EIG_TOL` of margin. One **over-reaching justification**, §5.2. |
| **Committed demo artifact** | **REPRODUCES today** — exit 0, 6/6 PASS, JSON identical but for one signed-zero print (§2.4). |
| **Is the *class* of defect closed?** | **NO — RED, and this is the finding.** Two new **one-line** mutations of the same family pass the repaired gate, printing *"All controls and identity checks PASSED."* §3. |
| **Is the proof-of-firing scheduled?** | **NO — confirmed from the workflow, not the comment.** And it **would not have caught either new mutation** even if it were. §4. |
| **Cross-repo consistency** | **CONSISTENT.** `c50ce32f` is Appendix A only; `onethird_program` holds no copy of either control. Verified by enumeration. §6. |
| **Overall** | **GREEN for the repair, RED for the class it belongs to.** |

**The single finding that matters.** mg-60d3 exists because two controls were *reporting success while
blind*. Both repairs are real, and both were derived **from** the two failures mg-09ea found — so
they are guaranteed to catch exactly those two. They are **a patch on two instances, not a fix for
the class.** The class is:

> *a quantity the document asserts, computed by code the CI gate exercises, with no control that can
> fail.*

Two more members are reachable by one-line edits today, and both pass the repaired gate:

| new mutation | one-line change | repaired gate |
|---|---|---|
| **M3** | `bk_frozen_pair`'s Theorem-E selector `min(…, key=ratio)` → `max(…)` | **exit 0** |
| **M4** | `projector_U`'s rank filter `s > max(tol, 1e-10)` → `s > 0.0` | **exit 0** |

**M3 is the decisive one, because it is F3 verbatim.** `frozen_pair` sits in the *same committed
mg-8b64 reference row the gate already has open in memory*, and is never compared. The gate compares
**4 of the 22** fields in that row. M3 moves the frozen pair at **5 of 5** posets, moves
`frozen_pairmode_capture` at 5 of 5, and moves `frozen_pair_overlap_with_U` from `0.807 / 0.809 /
0.810` to **exactly `1.0000`** at the three off-regime posets — the quantity ledger claim 8
(`PROVEN[c]`) rests on, in a row that *explicitly* says *"argmin ratio, not the max-bias pair"*. The
document knows the selector is load-bearing. The gate does not check it, and nothing printed looks
wrong.

**In fairness to the target: nothing in the document claims the class is closed.** Ledger claim 27
says only that *"the CI gate **fires** on both mutations that previously passed it"*, which is exactly
and narrowly true — I confirm it. This is a **residual finding**, not a refutation of a stated claim.
It is filed as RED because the reading the arc will take from a merged mutation demonstration is
"the gate is now mutation-tested", and it is not: it is tested against the two mutations already
known to have beaten it.

---

## §1 — Route: how this was made independent of the target

The demonstration under audit reconstructs the pre-repair gate **in process**, by substituting the
two predicates' old bodies (`apply_pre_repair_gate` rebinds `tmod._identity_row_ok` and
`tmod._antichain_row_ok`), and applies its mutations by **monkeypatching every loaded
`onethird_*` module** (`_rebind`). A polecat that re-ran that file and agreed with it would have
audited nothing. So:

1. **The pre-repair gate is the real thing, not a reconstruction.**
   `git show 87f0424:scripts/onethird_mg2c34_n7_overlap_test.py` — the source as mg-2c34 merged it.
   Verified to contain **zero** occurrences of `_identity_row_ok`, `_antichain_row_ok` or
   `match_bk_lambda2`. (Note this is a *stronger* pre-repair state than the demo's: at `87f0424` the
   identity block does not even *compute* `lambda2_BK`.)
2. **The mutations are source-level, one line each, in the defining module** — not runtime rebinds.
   Each case gets its own isolated tree containing a copy of `scripts/` and the one reference dataset
   the gate reads; the edit is applied there with an anchor-count assertion so a silent no-match is
   impossible.
3. **Eight full `--no-sweep` gate runs**, one per (mutation, gate) pair, each in its own tree.
4. **The antichain half of the audit imports nothing from the corpus.** `part_A` of
   `scripts/onethird_mg5ad1_gate_blindspot_probe.py` rebuilds the BK interchange matrix and the
   one-particle span from their definitions (`itertools.permutations`, adjacent transpositions, step
   `1/(2(n−1))`, laziness on the diagonal; SVD rank filter on the position-indicator matrix).
5. **The committed demo was also run verbatim once**, to check the committed artifact still
   reproduces — but as corroboration, after the independent route had already returned its answer.

Mutations, stated so they can be re-derived:

| | site | one-line change |
|---|---|---|
| **M1** | `onethird_mg4a86_standard_dominance_target_audit.py:127` | `step = 1.0/(2*(n-1))` → `1.0/(n-1)` |
| **M2** | `onethird_mg4a86_sector_leakage_and_tempering.py:56` | skip `x in (0, 1)` when filling the position blocks |
| **M3** | `onethird_mg8b64_L1b_bk_transport_transfer_probe.py:187` | `frozen = min(…, key=ratio)` → `max(…)` |
| **M4** | `onethird_mg4a86_sdquant_overlap.py:45` | `Q = Uu[:, s > max(tol, 1e-10)]` → `Uu[:, s > 0.0]` |

---

## §2 — Target 1: reproduce, do not assess

### 2.1 The exit-code matrix

Independently obtained, eight runs:

| | pre-repair gate (**real `87f0424` source**) | repaired gate (`af7fc2df`) |
|---|---|---|
| unmutated instrument | exit **0** | exit **0** |
| **M1** — BK step rescaled | exit **0** ← the defect | exit **1** |
| **M2** — `U` shrunk by element block | exit **0** ← the defect | exit **1** |
| **M3** — frozen-pair selector flipped | *(not run: no pre-repair claim)* | **exit 0 ← NOT CAUGHT** |
| **M4** — `projector_U` rank filter dropped | *(idem)* | **exit 0 ← NOT CAUGHT** |

The top six cells match `data/onethird-mg60d3-gate-mutation-demo.json` exactly. **A side conclusion:
the demo's in-process reconstruction of the pre-repair gate is behaviourally faithful** — it produces
the same three pre-repair exit codes as the actual merged source.

### 2.2 M1 — what fires, and over what population

The population is the **five** named posets of the identity check (`OFF_REGIME` `#3/#20/#600` plus
`IN_REGIME` `#945/#809`), and **5 of 5 rows fail** `match_bk_lambda2`. My `λ₂^BK`:

| poset | committed reference | under M1 | matches |
|---|---|---|---|
| `enum-n7-#3` | `0.9809230949067392` | `0.961846190` | `num_LE ✓ λ_std ✓ δ ✓ λ₂^BK ✗` |
| `enum-n7-#20` | `0.981202325964234` | `0.962404652` | `✓ ✓ ✓ ✗` |
| `enum-n7-#600` | `0.979920568765699` | `0.959841138` | `✓ ✓ ✓ ✗` |
| `enum-n7-#945` | `0.9434881015120073` | `0.886976203` | `✓ ✓ ✓ ✗` |
| `enum-n7-#809` | `0.9694945404615061` | `0.938989081` | `✓ ✓ ✓ ✗` |

§2.6.1's quoted `0.961846 / 0.962405 / 0.959841` reproduce. **And the mechanism claim reproduces
exactly**: under M1, `c` is bit-identical at all five posets (`0.995552 / 0.996857 / 0.996549 /
0.987947 / 0.995256`) and `CHECK-0` is `0.00e+00` — confirming CONTROL A/B/C are eigenvector-only and
CHECK-0 shares the code, which is why nothing else could have caught it.

### 2.3 M2 — what fires, and over what population

The population is the **three** antichains, and **3 of 3 rows fail**. `c_max` survives at
`1.000000000` on all three; `c_min` collapses to `0`:

| antichain | `dim U` | `c_max` | `c_min` | CONTROL B | CONTROL C |
|---|---|---|---|---|---|
| `A₄` | `10 → 7` | `1.000000000` | `−0.000000000` | **FAIL** | PASS (`0.446958`) |
| `A₅` | `17 → 13` | `1.000000000` | `−0.000000000` | **FAIL** | PASS (`0.246286`) |
| `A₆` | `26 → 21` | `1.000000000` | `0.000000000` | **FAIL** | PASS (`0.104472`) |

Measured `c` at the five posets moves to `0.986571 / 0.988475 / 0.995959 / 0.966288 / 0.988713` and
`dim U` to `22/20/19/6/8` — §2.6.1's quoted `0.986571 / 0.988475 / 0.995959` and the `10/17/26 →
7/13/21` antichain drop both reproduce. **The one-element-drop no-op reproduces too**, from
definitions and with no corpus import: dropping element `0`'s block leaves `dim U` at `10/17/26` and
`c_min` at `1`. §2.6's third table row is right, and so is its correction of the general claim that
row implies.

### 2.4 The committed demo re-run verbatim

Exit **0**, six of six PASS. `data/onethird-mg60d3-gate-mutation-demo.json` re-serialises identical
to the committed file except for **one printed signed zero** — committed `c_min=-0.000000000` vs
`0.000000000` at `A₆` under M2, in a captured stdout line. No assertion, figure or exit code depends
on it; `|c_min|` is `0` to `< 1e-9` either way. Noted for completeness, not as a defect.

---

## §3 — Target 2: are the two repairs sufficient, or only sufficient against the two mutations that were caught?

**Only against those two.** Two new mutations of the same family, one line each, pass the repaired
gate and print *"All controls and identity checks PASSED."*

### 3.1 M3 — the frozen-pair selector. This is F3 verbatim, still live.

`mg8b64_bk_frozen_pair` supplies Theorem E's frozen pair (`argmin` of `E(f_xy)/Var(f_xy)`); the gate
uses it to compute `frozen_pairmode_capture` and `frozen_pair_overlap_with_U`. Flip `min` → `max`:

| poset | frozen pair | `frozen_pairmode_capture` | `frozen_pair_overlap_with_U` |
|---|---|---|---|
| `enum-n7-#3` | `[3,5] → [0,1]` | `0.3920 → 0.2325` | `0.8072 → ` **`1.0000`** |
| `enum-n7-#20` | `[4,5] → [0,1]` | `0.4303 → 0.2727` | `0.8094 → ` **`1.0000`** |
| `enum-n7-#600` | `[2,4] → [5,6]` | `0.6114 → 0.2647` | `0.8096 → ` **`1.0000`** |
| `enum-n7-#945` | `[1,2] → [0,1]` | `0.3456 → 0.1522` | `1.0000 → 1.0000` |
| `enum-n7-#809` | `[1,3] → [0,1]` | `0.4656 → 0.1526` | `1.0000 → 1.0000` |

Everything else is untouched: `|L|`, `λ_std`, `δ`, `λ₂^BK` and `c` are bit-identical, CONTROL A/B/C
pass, CHECK-0 is `0.00e+00`. **`δ` in particular survives**, because the gate computes it on a
separate path (`delta_and_frozen_pair`, the max-bias route) — so `match_delta` is no defence.

Why this is the *same* defect, not a new one:

- **The comparison is available and unused.** `frozen_pair = [3,5]` is a field of the committed
  mg-8b64 reference row the gate opens at line 550. The audit probe's Part B census: the identity
  conjunction compares **4 of 22** reference fields (`num_LE`, `lambda_std`, `delta`, `bk_lambda2`);
  **18 are not compared**, including `frozen_pair`, `frozen_ratio`, `frozen_p`, `min_phi_bk_pair`,
  `width`, `num_incomp_pairs`, `transport_gap`. Part C confirms the corpus's `argmin`-ratio selector
  reproduces the committed `frozen_pair` at **5 of 5** posets — so a one-line comparison in exactly
  F3's shape was available and was not made.
- **It damages a `PROVEN[c]` ledger claim.** Claim 8 — *"the frozen-pair indicator's own overlap with
  `U` is `≥ 0.779` over the population and exactly `1` in 137/946 posets"* — carries the scope note
  *"mg-8b64's own Theorem-E frozen pair (argmin ratio), not the max-bias pair"*. The document
  identifies the selector as load-bearing in the ledger row itself.
- **It is silent.** Unlike M4 below, no printed column looks anomalous: `froz|U = 1.0000` is a value
  the document legitimately reports at `#945` and `#809`.
- **A full-sweep run does not catch it either.** By code reading: `failures` is assembled only from
  CONTROL A, CONTROL B, CONTROL C, `CHECK-0`, `report["identity_check"]` and `report["measured"]`. The
  sweep block adds **no** failure condition, so `lemma_3_1_check` (`137 of 137`) would change silently
  as well.

### 3.2 M4 — the projector's rank filter. Green on a measurement that is vacuous by the document's own criterion.

Drop the rank filter in `projector_U` (`s > max(tol, 1e-10)` → `s > 0.0`), so numerically-null
singular directions enter `U`:

| poset | `dim U` | `null = dim U/|L|` | `c_max` | `c_min` |
|---|---|---|---|---|
| `enum-n7-#3` | `24 → 49` | `0.0667 → 0.1361` | `0.995552 → 0.995805` | idem |
| `enum-n7-#20` | `22 → 49` | `0.1111 → 0.2475` | `0.996857 → 0.997237` | idem |
| `enum-n7-#600` | `20 → 49` | `0.1515 → 0.3712` | `0.996549 → 0.997853` | idem |
| `enum-n7-#945` | `7 → 21 = |L|` | `0.3333 → ` **`1.0000`** | `0.987947 → ` **`1.000000`** | idem |
| `enum-n7-#809` | `9 → 25 = |L|` | `0.3600 → ` **`1.0000`** | `0.995256 → ` **`1.000000`** | idem |

At `#945` and `#809`, `U` becomes **the whole function space**. The instrument's own §2 defines
`null` as *"the vacuity floor — `c` near `null` is NO signal in either direction"*, and here
`c = null = 1.0000` exactly: the measurement is vacuous **by the document's own criterion**, printed
side by side in the same row, and the gate exits **0**. Each control's reason for missing it is
structural: enlarging `U` can only *increase* overlap, so CONTROL B's `c_max = c_min = 1` survives
(antichain `dim U` inflates `10/17/26 → 16/25/36 = n²`); CONTROL C builds its own coordinate subspace
and only requires `≠ 1` (`0.820 / 0.368 / 0.147`, all passing); CHECK-0 shares `projector_U`, which is
exactly what §11.1's mg-60d3-restated bullet says.

**Honest weighting.** M4 is a coarser error than M3, and its damage *is* visible to a careful reader
in the printed `null` column. The finding is that the **gate** cannot see it, not that a human
couldn't. **M3 is the primary witness** and M4 the corroborating one.

### 3.3 What this means

The repairs were derived from the two known failures, so their sufficiency against those two is not
evidence about the class. Tested against the class, the gate is still blind in at least two places,
both reachable by a single character or a single expression. **The repair is a patch on two instances
of a class rather than a fix for the class** — which is the finding target 2 asked for.

---

## §4 — Target 3: the proof-of-firing is not run by anything

**The exclusion is real, confirmed from the workflow rather than the comment.**
`.github/workflows/script-controls.yml` runs exactly three steps beyond setup: the mg-8489 fast_Q
control, the mg-8ff1 counterexample, and `onethird_mg2c34_n7_overlap_test.py --no-sweep`.
`onethird_mg60d3_gate_mutation_demo.py` is **not** invoked. The repo has exactly two workflows —
`lean.yml` (filtered on `lean/**`, whose last touch was 2026-05-21) and `script-controls.yml` — and a
whole-repo grep finds the demo named only in prose: three lines of
`docs/OneThird-mg2c34-n7-Overlap-Test.md`, one comment in the gate's own docstring, and the
workflow's own exclusion comment. **Nothing executes it.**

**What would have to be true for the demo to run again.** Four things, in sequence, all human:
someone must (a) recognise that the edit they are making is an edit to the gate; (b) know the
instruction exists at all — it lives in a workflow comment and a doc subsection, on no executable
path; (c) have ~12 minutes and the numpy interpreter (`/usr/bin/python3`; bare `python3` on this host
has no numpy); and (d) choose to spend them. **The failure is silent by construction**: a control
that has stopped being able to fire prints nothing and exits 0, which is indistinguishable from a
control that fired correctly. That is the mg-4ad1 lesson the workflow header states, relocated one
level up — from the gate to the gate's own verifier.

**And there is a second gap, which changes what a fix has to do.** Even if the demo *were* scheduled,
**it would not have caught M3 or M4.** `EXPECTED` is a hardcoded 2×3 dictionary over
`{none, M1, M2}`, and `apply_M1` / `apply_M2` are two hardcoded functions. The demo answers *"do the
two known repairs still fire?"* — a regression test on two fixed mutations. It does not and cannot
answer *"is the gate blind anywhere?"* So *"run it on demand when the gate changes"* is not merely
unowned; **obeying it perfectly would still have passed both of §3's mutations.** A scheduling fix
alone would close the ownership gap and leave the coverage gap open.

Per the ticket, the fix is filed separately and is not designed here.

---

## §5 — Target 4: did the repair over-correct?

Checked in both directions. Reproducible via
`scripts/onethird_mg5ad1_gate_blindspot_probe.py` (Part A, no corpus import).

### 5.1 The `c_min` assertion is non-vacuous, true, and not knife-edge — no over-correction

| antichain | `dim U` | `dim λ₂-eigenspace` | `1 − c_min` | nearest **excluded** eigenvalue | margin / `EIG_TOL` |
|---|---|---|---|---|---|
| `A₄` | `10 = (n−1)²+1` | **3** `= n−1` | `8.9e-16` | `1.137e-01` | `1.14e+08` |
| `A₅` | `17` | **4** | `−6.7e-16` | `5.508e-02` | `5.51e+07` |
| `A₆` | `26` | **5** | `2.7e-15` | `3.048e-02` | `3.05e+07` |

Three separate things, each of which had to hold:

- **Non-vacuous.** The λ₂ eigenspace has dimension `n−1 = 3/4/5`, so `c_min` is genuinely a different
  reading from `c_max`. Had it been simple, the F4 repair would have been decoration — and this is
  not idle: `dim_E = 1` at all five *measured* posets (ledger claim 2), so the gate's *other*
  two-sided check (`dim_eigenspace > 1 and |c_max − c_min| > 1e-9`) is vacuous today.
- **Not over-tight.** The eigenspace lies inside `U` — `‖(I − P_U)V_E‖_F ≤ 1.9e-14`, `1 − c_min ≤
  2.7e-15` — against an assertion tolerance of `1e-8`. **Seven orders of margin.** The repair forbids
  nothing the walk permits on the cases it runs on.
- **Not tolerance-sensitive.** `c_min = 1` is stable across every degeneracy tolerance from `1e-15`
  to `1e-3`; the nearest eigenvalue *excluded* from the eigenspace sits `3.0e7`–`1.1e8 ×` `EIG_TOL`
  away. There is no knife edge for a different BLAS or numpy build to fall off.

**So: asserting `c_min` as well as `c_max` is correct, and the repair will not start failing on
legitimate inputs.**

### 5.2 One over-reaching justification, and a latent (not live) hazard

The docstring justifies the assertion as follows:

> *"L(P) = S_n, the BK chain is the interchange process on the path, and by Aldous/CLR the slowest
> mode **IS** the single-particle mode, which lies in U. Required: `c_max = 1` **AND** `c_min = 1`."*

Aldous' spectral-gap conjecture, as proved by Caputo–Liggett–Richthammer, gives the **eigenvalue**:
`gap(interchange) = gap(one-particle)`. `c_min = 1` is the strictly stronger statement that the
**whole** gap eigenspace lies in the one-particle sector, which additionally requires that no other
`S_n`-irrep component of the generator attains that eigenvalue. **CLR does not supply that.** The
containment is a verified property of the specific matrices, not a consequence of the theorem cited.

Empirically it holds well past the control's scope — I checked `A₇` (`|L| = 5040`) as well:
`dim U = 37 = (n−1)²+1`, `dim_E = 6 = n−1`, `c_min = 1.000000000000`, nearest excluded eigenvalue
`1.85e-2`. **Four for four at `n = 4,5,6,7`.** So the hazard is latent, not live:

> If CONTROL B is ever extended to a larger antichain — which §5.2's larger-`n` falsification
> programme invites — `c_min = 1` is **not licensed by the theorem cited**, and a legitimate
> eigenvalue coincidence across irreps would make the repaired control fail on a *correct*
> instrument. Whoever hits that will loosen the control, and the repair will be gone.

**Recommended, docstring only, no behaviour change:** cite the eigenspace containment as a verified
property of `A₄/A₅/A₆` (now also `A₇`), and cite Aldous/CLR for the eigenvalue equality alone.

### 5.3 Scope of what F4 actually added

The `c_min` assertion's population is exactly **three synthetic antichains**. On the five measured
posets `λ₂^BK` is simple, so no two-sided reading is exercised there at all. Not a defect — the
honest scope statement: **mg-60d3 added no two-sided coverage on real data.**

---

## §6 — Target 5: the cross-repo half

**What landed in `onethird_program` as `c50ce32f`.** `STATE.md` only, `+13/−5`, Appendix A only.
Enumerated: step **4c** rewritten (*"three times now"* → *"three deliverables … and on the fourth it
fired three times inside a single document"*, with the *"diff every summary artifact against the
body"* instruction added); step **4d** rewritten four-for-four → **five-for-five**, with *"run 4d
yourself even when the deliverable ran it on itself"* and *"check every axis of scope, not only `n`"*;
a new **mg-09ea row** in the location table; the *"fourth row"* paragraph re-anchored to mg-c8c6; a
new **"FIVE for five"** paragraph; and three stale counts fixed (`n = 4` → `n = 5`, *"four out of
four"* → *"five out of five"*, the fourth-row reference now naming mg-c8c6). **No program-table row
touched.**

**Are the two repos consistent?** Yes, and there is nothing that *could* diverge — verified by
enumeration rather than by trusting the commit message:

- `onethird_program` tracks **43 files**: `README.md`, `STATE.md`, `.gitignore`, 8 docs, 1 html, and
  `code/{face_geometry,face_geometry_audit_5630,face_geometry_audit_e0ce,hodge_leverage}`.
- **No `scripts/` directory** and **no copy of the gate or its dependencies**: `git grep -l` for
  `c_min`, `bk_lambda2`, `one_particle_span`, `projector_U` across the whole repo returns **nothing**.
- **No CI at all**: `.github` does not exist, tracked or untracked.

So neither repaired control has a second, unrepaired copy. The commit message's *"Appendix A only …
the mathematical consequences … are landed in `one_third_width_three`, not here"* is **accurate**.

**One observation, same class, explicitly out of scope for mg-60d3.** `onethird_program` ships
`code/face_geometry/controls.py`, `code/hodge_leverage/controls.py` and two `run_all.sh`, and has no
CI of any kind. By the argument written at the top of `script-controls.yml` — *"a control nothing runs
is indistinguishable from a control that does not exist"* — those are unrun controls in the sibling
repo. Noted, not actioned, and not mg-60d3's to fix.

---

## §7 — One minor precision finding

**§2.6's prose understates the identity check's population, and §2.6.1 contradicts it.** §2.6 reads
*"if any of the **three** posets stops matching its committed mg-8b64 row"*. The loop runs over
`named` = `OFF_REGIME + IN_REGIME` = **five** posets; §2.6.1's own table correctly lists
`#3/#20/#600/#809/#945`; and my M1 run fails **5 of 5**. The error is in the benign direction — it
understates coverage — but it is Appendix A step **4c**'s exact shape (*body right, summary drops a
qualifier*), inside the very section mg-60d3 wrote to land an audit whose 4c finding was that
pattern. **Fix: "three" → "five" at §2.6.** Ledger claim 5 is fine as written — it is scoped to the
three posets the corpus names, which is a different statement.

---

## §8 — What lands UNCHANGED

Everything mg-60d3 asserts about its own repair. Recorded explicitly because the RED above is about a
residual, not about a wrong claim:

1. **Ledger claim 27 — CONFIRMED.** Both repairs fire on the mutation they cover; neither fires on
   the unmutated instrument. Reproduced by a disjoint route.
2. **Both repairs are correct, minimal, and use values the instrument already computed.** One line
   each, no new measurement, no switch that can weaken the gate at run time.
3. **The predicates were extracted to module level for the right reason** — the gate's conjunction is
   readable in one place, and the demonstration can substitute the pre-repair forms without the
   deliverable's gate acquiring a weakening switch. Confirmed: the shipped gate has no such switch.
4. **F3's diagnosis was right and the number was never wrong.** All five committed `bk_lambda2`
   references reproduce to `< 1e-9` on an unmutated run. Missing control, not wrong result.
5. **The demo is itself a control and can fail** — it asserts the matrix and exits non-zero
   otherwise. Verified by construction and by its passing run.
6. **§2.6's third table row and its correction are both right**: the one-element drop is a provable
   no-op on `U` and the gate is right not to fire; the general claim that row implies is false, and
   M2 is the witness.
7. **§11.1's restatement of CHECK-0 is right, and load-bearing here.** CHECK-0 verifies the wrapper,
   not the instrument. My M3 and M4 both return `CHECK-0 = 0.00e+00` — the restatement predicted its
   own blindness correctly.

---

## §9 — Reproduction

```bash
# the audit's fast, self-verifying probe (targets 4 and the §3.1 census); ~30 s
/usr/bin/python3 scripts/onethird_mg5ad1_gate_blindspot_probe.py

# the exit-code matrix, independent route.  For each case: copy scripts/ + the
# one reference dataset to an isolated tree, apply ONE source-level edit from
# §1's table, then run the gate there.  The pre-repair gate is the real source:
git show 87f0424:scripts/onethird_mg2c34_n7_overlap_test.py
/usr/bin/python3 scripts/onethird_mg2c34_n7_overlap_test.py --no-sweep   # ~2 min per case

# the target's own demonstration, verbatim (~12 min, six gate runs)
/usr/bin/python3 scripts/onethird_mg60d3_gate_mutation_demo.py
```

`data/onethird-mg5ad1-gate-blindspot-probe.json` is the probe's committed output. Interpreter matters:
bare `python3` on this host has no numpy.

---

## §10 — Findings ledger

> **[DISPOSITION, 2026-07-30 (mg-75f0) — `docs/OneThird-mg75f0-GateClassClosure.md`.]** Findings **1**,
> **3** and **4** are closed; finding **2** is closed for its cheap half only and its expensive half is
> assigned. Nothing in this audit was contradicted; the repair mg-60d3 made and ledger claim 27 both
> stand as this audit records them.
>
> | # | disposition |
> |---|---|
> | **1** | **CLOSED.** The identity check now compares the **whole** committed row — 22 of 23 fields, one exclusion (`name`) with its reason in the source — by iterating the reference row rather than a conjunction, so a field *added* to that row is compared automatically. `dim U`'s rank is the one surface that widening does not reach, so **CONTROL E** was added for it. **Acceptance was not M3/M4**: three further one-line mutations that neither mg-60d3 nor this audit used were run, and all three were invisible to the repaired gate (exit 0) and are fatal to the widened one (exit 1). |
> | **2** | **CLOSED for the ~30 s half**: this audit's own probe (`scripts/onethird_mg5ad1_gate_blindspot_probe.py`) is now a step in `script-controls.yml`, with a new part D that exercises every gate predicate for firing in milliseconds. **STILL OPEN for the expensive half** — the ~12 min mg-60d3 demo, plus mg-75f0's own ~25 min class-closure demo, are run by nothing. That trigger is **mg-7db4's**, which was in flight and unmerged; mailed. |
> | **3** | **FIXED, docstring only, no behaviour change.** `_antichain_row_ok` now cites Aldous/CLR for the gap **eigenvalue** alone and cites the eigenspace containment as a **verified property of `A₄/A₅/A₆/A₇`**, with the consequence stated: if it ever fails at larger `n`, narrow the control's *population*, do not loosen the *assertion*. |
> | **4** | **CLOSED as a coverage gap.** **CONTROL F** measures `enum-n7-#52` and `#88` — the committed sweep's only posets with `dim_E > 1` — and asserts `dim_E > 1` as well as `\|c_max − c_min\| ≤ 1e-9`, so the coverage cannot quietly evaporate. It is real, not decorative: under M2 the two readings split by `7.58e-02` and `4.30e-02` at those posets. |
> | **5, 6, 7** | Untouched. §7's *"three" → "five"* correction landed with this audit; the identity population is now **seven**. Finding 6 (the signed-zero print) and finding 7 (`onethird_program` has no CI) are out of mg-75f0's scope. |


| # | finding | severity | site |
|---|---|---|---|
| **1** | **The repair is a patch on two instances, not a fix for the class.** M3 (frozen-pair selector, one character) and M4 (`projector_U` rank filter, one expression) both pass the repaired gate with *"All controls and identity checks PASSED."* M3 is F3 verbatim: `frozen_pair` is in the same committed reference row the gate has open, and **4 of 22** fields in that row are compared | **RED** | §3 |
| **2** | **The proof-of-firing has no owner and no mechanism**, confirmed from the workflow. And it is **insufficient even when obeyed** — `EXPECTED` is a hardcoded 2×3 matrix over two fixed mutations, so it would not have caught M3 or M4 | **RED** | §4 |
| **3** | **The F4 justification over-reaches the theorem it cites.** Aldous/CLR gives the gap *eigenvalue*; `c_min = 1` asserts gap-*eigenspace* containment in the one-particle sector. True at `n = 4,5,6,7`; **not licensed** for a larger antichain, which §5.2's programme invites. Docstring fix only | **AMBER** (latent) | §5.2 |
| **4** | **`dim_eigenspace > 1` two-sided check is vacuous on real data** (`dim_E = 1` at 5/5 measured posets), so F4's coverage is exactly three synthetic antichains. Scope statement, not a defect | **note** | §5.3 |
| **5** | **§2.6 says "three" where the gate checks five**; §2.6.1 contradicts it and is right. Benign direction, but step-4c shaped | **minor** | §7 |
| **6** | Committed demo JSON reproduces up to one **signed-zero print** at `A₆`. No assertion depends on it | **note** | §2.4 |
| **7** | `onethird_program` has two `controls.py` and **no CI at all** — unrun controls in the sibling repo, by `script-controls.yml`'s own argument. Out of scope for mg-60d3 | **note** | §6 |
| — | Everything mg-60d3 claims about its repair: **CONFIRMED**, by a disjoint route | GREEN | §2, §8 |
