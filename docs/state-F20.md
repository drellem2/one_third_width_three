# state-F20 — cumulative state ledger for F20 (the n-uniform chamber-Morse critical-cell structure: (L2-struct) + (W3-cover)) (mg-c3fa)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat session
boundaries. Ledger of what is done vs. deferred across the multi-session
(500k cap) F20 ticket.

**Branch:** `polecat-cat-mg-c3fa` (mg-c3fa).
**Goal (mg-c3fa):** close the last two residuals of milestone 1 (the F10
width-3 1/3-2/3 theorem, part (iii)) — **(L2-struct)** (`G_n` is a width-2
ordinal sum of antichains) and **(W3-cover)** (the canonical critical
chains meet every width-3 `S_m`-orbit). Primary approach: the n-uniform
chamber-Morse critical-cell structural theorem. Enabling fallback: the
bounded F8‴ HPC chamber-Morse anchor run at `n = 7, 8`. NO new axioms, no
Lean changes. Targets `main`.

**Outcome (after Session 1):** **GREEN-partial.** Neither residual closed
n-uniformly. F20's deliverable is the **re-founding of both residuals on a
corrected structural understanding**: the prior ι-tower framing (F10 §5.2,
on which F19's reductions of both (ICOP-step) and the width-3 bridge rest)
is found *not literally correct*, the F8′-HPC "candidate `c*_6`" is found
to *violate (L2-struct)*, and the corrected reduction (CM-struct) is given.
(L2-struct) holds exactly `n ≤ 5`; the width-3 *end goal* is verified
directly `m ≤ 6`. See `docs/compatibility-geometry-F20-chamber-morse-structure.md`.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-c3fa) — DONE

**Goal:** read F10/F17/F18/F8/F8′/F8′-HPC/F19; attempt the n-uniform
chamber-Morse structural theorem for (L2-struct) and (W3-cover); build a
verification + anchor harness; emit a verdict.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: F19 §2–4, F17 §1–5, F18 §2–5, F10 §5.2–5.4/§6.6–6.7/§7.3, F8 §4.1–4.6/§6, F8′ §3, F8′-HPC §5–6, F5 §3–4 | ✅ | — |
| **(L2-struct) verified exactly `n = 3,4,5`** — `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`, `G_5=OSA(2,2,1)` | ✅ exact, re-confirmed | doc §2; harness [A] |
| **Correction 1** — F8′-HPC "candidate `c*_6`" violates (L2-struct) (width 3; element 5 stays isolated) | ✅ FINDING | doc §3.1; harness [B] |
| **Correction 2** — the ι-tower form (F10 §5.2) is not literally correct: genuine `c*_5 ≠ ι_4(c*_4)+append` (only `P_0` has element 4 isolated) | ✅ FINDING | doc §3.2; harness [C] |
| **Correction 3** — (L2-struct) ∧ ι-tower multiplicativity are jointly inconsistent for `n ≥ 7` (top-step Pr forced `< 3/11`); ⇒ genuine `c*_n` is not an ι-lift | ✅ FINDING | doc §3.3; harness [C2] |
| **The corrected reduction (CM-struct)** — residuals re-founded on the genuine chamber-Morse object, ι-tower-free | ✅ | doc §4 |
| **Symmetric-pair engine survives** — Lemma L1 + the OSA-symmetry fact recertified on `G_3,G_4,G_5` and the canonical `n=6,7` width-2 OSAs; (L2-struct) still ⟹ top-step BFT-sharpness | ✅ | doc §4.2; harness [D] |
| **Width-3 end goal verified `m ≤ 6`** — every width-3 `S_m`-orbit admits a balanced incomparable pair: `m=4` 5/5, `m=5` 29/29, `m=6` 170/170 | ✅ extends F8 Thm 6.1 base | doc §6.2; harness [E] |
| **n = 6 chamber anchor data** — `|PPF_6|=129302`, 316 `S_6`-orbits, width dist `{2:74,3:170,4:63,5:9}`, genuine `G_6` ∈ explicit 12-element candidate list | ✅ | doc §6.3; harness [F] |
| Verification harness `scripts/compat_geom_F20_chamber_morse_hpc.py` (6 sections) | ✅ runs clean | the harness |
| Verdict | ✅ **GREEN-partial** | see below |

**Verdict: GREEN-partial.**

Neither (L2-struct) nor (W3-cover) is proven n-uniformly. F20's headline
content is **three structural corrections** that re-found the residuals,
plus the corrected reduction, plus a genuine extension of the rigorous
base of the *end goal* (width-3 Kahn–Saks 1/3-2/3) to `m ≤ 6`.

**Key structural findings (the three corrections):**

1. **The F8′-HPC ι-lift "candidate `c*_6`" violates (L2-struct).** Its top
   poset `G_6 = ι_5(G_5) ∪ {(0,2)}` has **width 3** — the appended cover
   `(0,2)` is a relation inside `[5]`, so element 5 is never absorbed and
   `{3,4,5}` is a width-3 antichain. `|L(G_6 cand)| = 12` is not a power
   of 2. The genuine `c*_6` is a different object.

2. **The ι-tower form (F10 §5.2) is not literally correct.** The genuine
   `c*_5` does not contain `ι_4(c*_4)`: only `P_0` of `c*_5` has element 4
   isolated; `P_1,P_2,P_3` all use element 4. So `c*_5 ≠ ι_4(c*_4)+append`.
   (The F8′ multiplicativity audit "confirming the ι-tower" was an audit
   of the ι-lift *candidate* — a tautology — not of the genuine object.)

3. **(L2-struct) ∧ ι-tower multiplicativity are jointly inconsistent for
   `n ≥ 7`.** A width-2 OSA has `|L| = 2^s`, `s ≤ ⌊n/2⌋`; an ι-lift
   2nd-top poset has `|L| = n!`-scale; the top-step Pr `2^{s_n}/(n·2^{s_{n-1}})`
   is forced `< 3/11` for `n ≥ 7`. **Resolution:** the genuine `c*_n` is
   **not** an ι-lift — its 2nd-top poset stays near-maximal (small `|L|`),
   exactly as the genuine `c*_5` already shows (`|L(P_2)| = 8`, not `10`).

These three corrections mean **F19's reductions of (ICOP-step) and the
width-3 bridge — phrased on the ι-tower model — need the F20 correction.**
The *order-theoretic core* of F19 (Lemma L1, the symmetric-pair argument
of Prop 3.1) is untouched and survives intact (doc §4.2); only the
ι-tower *scaffolding* is corrected (doc §4 supplies (CM-struct)).

**What stands as the residual:** an n-uniform proof of either residual
needs the **genuine (non-ι-lift) canonical chamber-Morse critical cell**
`c*_n` for general `n`. F20 corrects the target, pins the genuine `G_6` to
a 12-element list, verifies the end goal `m ≤ 6`, and recommends a
follow-on **F21** — but does not close the residuals.

**Trust-surface impact:** NONE. No new axioms; no Lean changes; the only
computation beyond exact rational arithmetic is the bounded n = 6 chamber
*enumeration* (structural anchor data, not a (co)homology computation).
The in-tree Lean `width3_one_third_two_thirds` 4-axiom artifact is
untouched.

**Deliverables produced this session:**
- `docs/compatibility-geometry-F20-chamber-morse-structure.md` (NEW) — the
  proof/analysis document: §1 setting, §2 the exact record, §3 the three
  corrections, §4 the corrected reduction (CM-struct), §5 (L2-struct), §6
  (W3-cover), §7 the harness, §8 establishes/does-not, §9 verdict + F21
  recommendation, §10 references.
- `docs/state-F20.md` (NEW, this file) — cumulative state ledger.
- `scripts/compat_geom_F20_chamber_morse_hpc.py` (NEW) — the verification +
  structural-anchor harness; sections [A]–[F]; pure-Python stdlib; [A]–[E]
  run in < 30 s, [F] (`--chamber-n6`) in ≈ 5 min.

---

## §2. The result, in one screen (reproduce-on-resume)

- **(L2-struct)** [F19 §3.3] — `G_n` is a width-2 ordinal sum of antichains
  with a size-2 block. **Verified exactly `n = 3,4,5`** (`OSA(1,2)`,
  `OSA(2,1,1)`, `OSA(2,2,1)`). NOT proven n-uniformly.
- **(W3-cover)** [F19 §4.3] — the canonical critical chains meet every
  width-3 `S_m`-orbit. NOT proven. But the **end goal** (every width-3
  poset has a balanced incomparable pair, `Pr ∈ [3/11,8/11]`) is verified
  **exactly `m ≤ 6`** (5/5, 29/29, 170/170 orbits) — extending F8 Thm 6.1.
- **Correction 1** — F8′-HPC `c*_6` candidate `= ι_5(c*_5)+{(0,2)}` has top
  poset of **width 3**: violates (L2-struct). Not the genuine `c*_6`.
- **Correction 2** — genuine `c*_5 ≠ ι_4(c*_4)+append` (element 4
  non-isolated in `P_1,P_2,P_3`). The ι-tower form is not literally true.
- **Correction 3** — (L2-struct) ∧ ι-tower multiplicativity inconsistent
  for `n ≥ 7`; the genuine `c*_n` is not an ι-lift.
- **The corrected reduction (CM-struct)** — there is an `S_n`-equivariant
  Morse function on `Δ_n` (exists, by F17+F18) whose canonical critical
  cells have all-BFT-sharp steps (i), top posets that are width-2 OSAs
  ((L2-struct)) (ii), and collectively cover every width-3 orbit
  ((W3-cover)) (iii). The genuine object is built by genuine chamber-Morse
  descent, NOT by ι-lift-and-append.
- **Symmetric-pair engine** — Lemma L1 (symmetric incomparable pair ⇒
  Pr = 1/2) + the OSA-symmetry fact (every incomparable pair of a width-2
  OSA is symmetric) survive the corrections intact: (L2-struct) still ⟹
  the new-cover step has Pr = 1/2 (F19 Prop 3.1, order-theoretic core).
- **n = 6 chamber:** `|PPF_6| = 129302`, **316** `S_6`-orbits, genuine
  `G_6` ∈ {12 width-2-OSA-with-size-2-block orbits, `|L| ∈ {2,4,8}`}.
- **Verdict:** GREEN-partial. Not GREEN-both / GREEN-one (neither residual
  closed); not RED (nothing false — the `n ≥ 7` obstruction is to the
  *ι-tower model*, not (L2-struct)); not AMBER (real structural progress —
  three corrections, the corrected reduction, end-goal base extended).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **`PPF_n` convention** — non-empty, non-total transitively-closed
  antisymmetric relation sets on `[n]`; `(a,b)` means `a ≺ b`; ordered by
  relation-set inclusion. `|PPF_n| = 12,194,4110,129302` at `n=3,4,5,6`.
  `ι_n` adds element `n` free.
- **`Pr_P[x≺y] = |L(P∪{x<y})|/|L(P)|`**; BFT-sharp interval `[3/11,8/11]`.
- **A width-2 OSA `A_{a_1}⊕⋯⊕A_{a_r}` (`a_i∈{1,2}`) has `|L| = 2^s`**,
  `s = #(size-2 blocks)`. `|L(G_n)|` being a power of 2 is a *necessary*
  condition for (L2-struct) — the F8′-HPC candidate fails it (`|L|=12`).
- **The ι-tower form (F10 §5.2) is NOT the genuine object** — F20
  Corrections 2 + 3. Any continuation must NOT assume `c*_n` is an ι-lift,
  must NOT use the "one new cover step per level" reduction of (ICOP-step)
  as stated in F19 §3.1 (it is ι-tower-based), and must NOT trust the
  F8′-HPC `c*_6` candidate. Use the corrected reduction (CM-struct), doc §4.
- **Lemma L1 + the OSA-symmetry fact are UNCONDITIONAL and survive the
  corrections** — they never used the ι-tower. (L2-struct) ⟹ `G_n` has a
  symmetric pair ⟹ the within-block new cover has Pr = 1/2. This is the
  load-bearing order-theoretic core of F19 and it is intact.
- **`G_n` is exact only `n ≤ 5`** — `G_3=OSA(1,2)`, `G_4=OSA(2,1,1)`,
  `G_5=OSA(2,2,1)`, with `s_3=s_4=1`, `s_5=2`. The genuine `G_6` is
  unknown — one of the 12 candidates listed in doc §6.3.
- **The full chamber-Morse greedy is HPC-class beyond single-session
  budget already at `n = 6`** (F5: ~567 s for the n = 5 chamber order
  complex of 352,947 cells; n = 6 is ≥ 100× larger). The F8‴ anchor run at
  `n = 7,8` as literally specified is NOT single-polecat-feasible — the
  F20 ticket's in-ticket scoping of it was over-optimistic. F20 delivers
  the feasible anchor data (n = 6 chamber *enumeration*) instead.
- **Scope boundary** — F20 is strictly F10 part (iii)'s two residuals. The
  cohomological core (F17/F18, (UCC)) is unconditional/complete and
  untouched. Route (iii)/mg-b345 stays PARKED.
- Trust-surface impact: none. No new axioms, no Lean changes, no new
  (co)homology HPC datapoint.

---

## §4. If F20 is reopened / a follow-on F21 is filed — in-scope continuations

The genuine next step is a **follow-on F21** targeting the genuine
(non-ι-lift) canonical chamber-Morse critical cell at general `n`:

- **(a) The structural theorem.** Identify `c*_n` for general `n` —
  built by genuine `S_n`-equivariant Forman-respecting chamber-Morse
  descent (NOT ι-lift) — and prove (i) its top poset is a width-2 OSA
  ((L2-struct)) and (ii) the critical chains cover every width-3 orbit
  ((W3-cover)). Pin the genuine `G_6` among the 12 candidates of doc §6.3
  as a first checkpoint.
- **(b) The HPC chamber-Morse run.** A genuine chamber-Morse greedy at
  `n = 6` (and `n = 7` if budget permits) — this is **Tier-3 HPC budget**,
  NOT single-polecat-session-feasible (contrary to the F20 ticket's
  in-ticket scoping). It would pin `c*_6` directly.
- **In-session strengthenings** (not load-bearing): extend the width-3
  end-goal enumeration to `m = 7` (bounded but slow); search the n = 6
  chamber for valid critical-cell candidates ending at each of the 12
  `G_6`-candidate posets with all-BFT-sharp steps.

The corrected reduction (CM-struct) (doc §4) is the framework F21 should
use; do NOT re-attempt the ι-tower route.

---

## §5. References

- mg-c3fa — F20 (this ticket). `docs/compatibility-geometry-F20-chamber-morse-structure.md`, this file, `scripts/compat_geom_F20_chamber_morse_hpc.py`.
- mg-5722 — F19 ((ICOP-step) + width-3 bridge): **GREEN-partial.** `docs/compatibility-geometry-F19-icop-step-and-bridge.md`. **Parent.** F20 corrects F19's ι-tower scaffolding; confirms F19's symmetric-pair engine (L1, Prop 3.1 core) survives.
- mg-4d3a — F17 (equivariant cofiber Morse) + mg-d039 — F18 ((UCC.2)): the unconditional cohomological core. Untouched by F20.
- mg-8216 — F10 (general-`n` synthesis): `docs/general-n-proof-synthesis.md` §5.2 (**the ι-tower form — corrected by F20 §3**), §6.7 (part (iii)), §7.3 (the width-3 bridge).
- mg-1e99 — F8 (ICOP framework): §4.1 (the chamber-Morse construction), §6 (Theorem 6.1 — `m ≤ 4` rigorous base, extended to `m ≤ 6` by F20).
- mg-7b3b — F8′ / mg-3bf3 — F8′-HPC: the ι₅-lift `c*_6` candidate — **F20 §3.1 finds it violates (L2-struct)**; F8′-HPC §6.2's conjecture that it is the genuine `c*_6` is refuted.
- mg-1e58 — F5 (chamber-Morse `n=5`): the chamber order complex; the ~567 s greedy-matching cost cited in F20 §1.3.
- mg-b345 — F8″ (route (iii)): PARKED — F20 does not touch it.

---

*Cumulative state doc for mg-c3fa (F20). Session 1 DONE — verdict
GREEN-partial. Branch `polecat-cat-mg-c3fa`. The two residuals (L2-struct)
and (W3-cover) are **reduced and corrected, not closed**: the prior
ι-tower framing is found incorrect (three structural corrections), the
corrected reduction (CM-struct) is given, the symmetric-pair engine is
confirmed intact, and the width-3 end goal is verified `m ≤ 6`. Follow-on
F21 recommended. No new axioms; no Lean changes.*
