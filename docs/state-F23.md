# state-F23 — cumulative state ledger for F23 (the canonical descent rule for `c*_{n+1}`) (mg-531f)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat
session boundaries. Ledger of what is done vs. deferred across the
multi-session (500k-token cap) F23 ticket.

**Branch:** `polecat-cat-mg-531f` (mg-531f).
**Goal (mg-531f):** find the `S_{n+1}`-equivariant structure — beyond
`min-|L|-profile` + BFT-sharp — that selects THE canonical `c*_{n+1}` from
the 4-orbit candidate set F22-HPC S2 left under-specified, and answer
**decisively**: does a canonical rule **exist**? Testbed: the `n = 3 → 4`
case (cheap, materialisable). **No new axioms; no Lean changes; no
(co)homology datapoint.** Targets `main`.

**Outcome (after Session 1): GREEN-descent-pinned (HPC-per-n variant).**
A canonical `S_{n+1}`-equivariant rule **does exist** — chamber-Morse
criticality, made `S`-equivariant by the `min-|L|-profile` tie-break (F23
candidate form B) — and it decisively pins recorded `c*_4` at the
`n = 3 → 4` testbed. But it is **not** closed-form / `n`-uniform: every
*structural* (non-criticality) discriminator of the 4 orbits is refuted as
`n`-uniform by the recorded `c*_3, c*_5`, and applying the rule needs the
level-`(n+1)` chamber-Morse matching — HPC-per-n. The cofiber-Morse
induction (F21 Prop F21.1) narrows but does **not** self-close. See
`docs/compatibility-geometry-F23-canonical-descent-rule.md`.

---

## §1. Session 1 — 2026-05-15 (this polecat, mg-531f) — DONE

**Goal:** materialise the 4-orbit candidate set at `n = 3 → 4`; run the
full `S_4`-equivariant invariant battery; test the three candidate rule
forms; emit a **decisive** verdict.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: F22-HPC S1+S2 (full), F21 (full), the F22-HPC Section-10 testbed infra | ✅ | — |
| **F22-HPC S2 candidate set reproduced exactly** — `212` descent-reachable → `151` BFT-sharp → `44` of `min-|L|-profile` `(5,3,2)` → **4 `S_4`-orbits** | ✅ | script Section 1; doc §1 |
| **Full `S_4`-invariant battery on the 4 orbits** — they agree on `|L|`-profile, per-step `Pr`, width profile, bottom-poset iso, orbit size; (L2-struct) holds for ALL 4 (does not discriminate); they differ in top-poset OSA, middle-poset iso, new-element locus | ✅ FINDING | script Section 2; doc §1 |
| **Rule A (deterministic descent `V`-path) — FAILS** — 'shortest `V`-path' selects orbit 2, not recorded `c*_4` (orbit 3); the gradient flow is a wide-fan-out DAG with no distinguished `S_4`-invariant `V`-path criterion | ✅ FINDING | script Section 3; doc §2 |
| **Rule B (chamber-Morse criticality) — THE RULE** — `M^chamber_4` has 4 critical `2`-cells in 4 distinct orbits, profiles `(5,3,2),(12,5,2),(8,3,2),(8,4,2)`; the unique `min-|L|-profile` one IS recorded `c*_4` (exact, same labelling); of the 4 descent orbits, exactly one meets `crit(M^chamber_4)` | ✅ **HEADLINE** | script Section 4; doc §3 |
| **Rule C (lex-min over a structural `S_4`-invariant) — FAILS `n`-uniformity** — top-poset OSA and new-element locus each uniquely pick recorded `c*_4` at `n = 3 → 4`, but both are refuted as `n`-uniform rules by the recorded `c*_3, c*_5` | ✅ FINDING | script Section 5; doc §4 |
| **`n`-uniformity probe** — `c*_3, c*_4, c*_5`: new-element locus is HIGH / LOW / (absent→HIGH→MIXED); top OSA is `OSA(1,2) / OSA(2,1,1) / OSA(2,2,1)` — NO `n`-uniform structural pattern; sharpens F21 Finding 2.1 at the selector level | ✅ FINDING | script Section 6; doc §5 |
| **`n = 3` base + HPC-per-n confirmation** — `M^chamber_3` perfect (`c*_3` trivially unique); `M^chamber_4` not perfect (4 critical `2`-cells); `Δ_5` `> 2·10⁷` cells — `M^chamber_5` is Tier-3 HPC | ✅ | script Section 7; doc §6 |
| Testbed script `scripts/compat_geom_F23_canonical_descent.py` (8 sections; pure-Python stdlib; exact arithmetic; runs clean in ≈ 3 s; asserts the candidate set reproduces F22-HPC S2 exactly) | ✅ runs clean | the script |
| Verdict | ✅ **GREEN-descent-pinned (HPC-per-n)** | doc §0, §7, §8 |

**Verdict: GREEN-descent-pinned (HPC-per-n variant).**

A canonical `S_{n+1}`-equivariant rule selecting `c*_{n+1}` from the
4-orbit candidate set exists — **Rule B**, chamber-Morse criticality (F23
candidate form B; the structure F21 §5.2 / F22-HPC S2 finding 6 predicted
was needed), made `S`-equivariant by the `min-|L|-profile` tie-break — and
it decisively pins recorded `c*_4` at the `n = 3 → 4` testbed. But:

1. **No closed-form / `n`-uniform structural rule survives.** Every
   *structural* (non-criticality) discriminator of the 4 orbits is refuted
   as `n`-uniform by the recorded `c*_3, c*_5`. The only `n`-uniform
   selector is chamber-Morse criticality itself — the *definition* of
   `c*_n`.
2. **The rule is HPC-per-n.** Applying Rule B at level `n+1` needs
   `M^chamber_{n+1}`, HPC-class from `n = 5` on. The cofiber-Morse
   induction (Prop F21.1) narrows but does **not** self-close into a
   closed-form recursion.

This is **not** AMBER-not-canonically-pinnable: "the canonical
chamber-Morse critical cell `c*_n`" **is** a well-defined canonical
`S_{n+1}`-equivariant object (via `min-|L|-profile` chamber-Morse
criticality — an `S`-equivariant refinement of the label-dependent lex-min
definition). It does **not** need re-founding. But the structural-shortcut
hope is not realised — the descent is the **third** structural model
(after the ι-tower F19→F20 and the `M_rel^eq`-survivor F21→F22) that
narrows the inductive rule without closing it.

**Decisive consequence (surfaced to the PM/Daniel level):** the
chamber-Morse route to F10 part (iii) is unblocked **only in the
HPC-per-n sense** — route 2 of `state-F22-HPC` §5, a separate Tier-3
decision — **or** the program pivots part (iii) to the documented
BK/Cheeger-expansion mechanism (mg-26fc). A budget/strategy decision.

**Trust-surface impact: NONE.** No new axioms; no Lean changes; no
(co)homology datapoint. Elementary order-complex combinatorics + exact
rational arithmetic on the materialised `n = 3 → 4` testbed. The in-tree
Lean `width3_one_third_two_thirds` 4-axiom artifact is untouched.

**Deliverables produced this session:**
- `scripts/compat_geom_F23_canonical_descent.py` (NEW) — the candidate-rule
  testbed; 8 sections; reproduces F22-HPC S2's candidate set exactly
  (assertion-checked); runtime ≈ 3 s.
- `docs/compatibility-geometry-F23-canonical-descent-rule.md` (NEW) — the
  structural document: §0 the question, §1 the 4-orbit candidate set +
  battery, §2 Rule A, §3 Rule B (the rule), §4 Rule C, §5 the
  `n`-uniformity probe, §6 the HPC-per-n cost, §7 establishes/does-not,
  §8 the decision F23 surfaces, §9 refs.
- `docs/state-F23.md` (NEW, this file) — cumulative state ledger.

---

## §2. The result, in one screen (reproduce-on-resume)

- **The 4-orbit candidate set** [F23 §1] — at `n = 3 → 4`: `212`
  descent-reachable `2`-cells → `151` all-BFT-sharp → `44` of
  `min-|L|-profile` `(5,3,2)` → 4 `S_4`-orbits, each size `24`. All 4
  satisfy (L2-struct) (width-2-OSA top with a size-2 block) — it does NOT
  discriminate. They differ in top-poset OSA `[(1,2,1),(1,1,2),(1,2,1),
  (2,1,1)]`, middle-poset iso-type, and new-element locus.
- **Rule A — deterministic descent `V`-path** [F23 §2] — FAILS: shortest
  `V`-path selects orbit 2, not recorded `c*_4` (orbit 3).
- **Rule B — chamber-Morse criticality** [F23 §3] — **THE RULE.**
  `c*_{n+1}` = the unique `min-|L|-profile` critical `(n−1)`-cell of
  `M^chamber_{n+1}` = the unique descent orbit (of the 4) meeting
  `crit(M^chamber_{n+1})`. `S_{n+1}`-equivariant; decisive at the testbed
  (exact, same labelling). **But:** it is chamber-Morse criticality
  itself — the *definition* of `c*_n` — and is HPC-per-n.
- **Rule C — lex-min over a structural `S_4`-invariant** [F23 §4] — FAILS
  `n`-uniformity: top-poset OSA and new-element locus pick recorded `c*_4`
  at `n = 3 → 4` but are refuted as `n`-uniform by the recorded
  `c*_3, c*_5`.
- **`n`-uniformity probe** [F23 §5] — no `n`-uniform structural pattern in
  the new-element locus (HIGH/LOW/MIXED) or the top-poset OSA
  (`OSA(1,2)/OSA(2,1,1)/OSA(2,2,1)`). Sharpens F21 Finding 2.1 at the
  selector level.
- **HPC-per-n** [F23 §6] — `M^chamber_3` perfect; `M^chamber_4` not
  perfect (4 critical `2`-cells); `Δ_5` `> 2·10⁷` cells, `M^chamber_5`
  Tier-3 HPC.
- **Verdict:** GREEN-descent-pinned (HPC-per-n). Not GREEN-partial (the
  rule uniquely pins, not merely narrows). Not AMBER (a canonical
  `S_{n+1}`-equivariant rule DOES exist; `c*_n` IS canonically
  well-defined). Not RED (Rule B works at the testbed; F21.1's descent
  picture is confirmed, not refuted).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **`PPF_n` convention** — non-empty, non-total transitively-closed
  antisymmetric relation sets on `[n]`; `(a,b)` means `a ≺ b`; ordered by
  inclusion. Per-step `Pr` of a chain step `= |L(P_{k+1})|/|L(P_k)|`;
  BFT-sharp `[3/11, 8/11]`.
- **The descent (F21 Prop F21.1) is CONFIRMED, not refuted** — F23 is
  GREEN, not RED. Recorded `c*_4` IS descent-reachable from the survivor;
  F23 finds the *selector*, it does not break the descent picture.
- **Rule B is the rule — but it is chamber-Morse criticality itself.** Do
  NOT mis-read F23 as having found a *new structure* that bypasses the
  chamber-Morse matching. It has not. The rule is the program's original
  definition of `c*_n`, made `S`-equivariant by `min-|L|-profile`. Its
  content is a *compatibility theorem* (the descent set and
  `crit(M^chamber)` intersect in exactly one orbit), not a generative
  shortcut.
- **No closed-form structural rule exists** — every structural
  discriminator of the 4 orbits FAILS `n`-uniformity (F21 Finding 2.1,
  sharpened). Do NOT extrapolate "top OSA `(2,1,1)`" or "stays in `D_n`"
  to general `n` — both are `n = 4` coincidences.
- **HPC-per-n** — `M^chamber_n` is HPC-class for `n ≥ 5` (F20 §1.3,
  F21 §5.3, F23 §6). The descent does NOT bypass this.
- **Scope boundary** — F23 is the `n = 3 → 4` testbed (route 1 of
  `state-F22-HPC` §5). Route 2 (Tier-3 HPC at `n = 6, 7`) is a SEPARATE
  decision, NOT bundled. Route (iii)/mg-b345 stays PARKED. The
  cohomological core (F17/F18, (UCC)) is unconditional/complete and
  untouched.
- **Trust-surface impact: none.** No new axioms, no Lean changes, no new
  (co)homology HPC datapoint.

---

## §4. If F23 is reopened / a follow-on is filed — in-scope continuations

F23's verdict (GREEN-descent-pinned, HPC-per-n) surfaces a PM/Daniel
decision, not an obvious next polecat ticket. The documented continuations:

1. **Route 2 of `state-F22-HPC` §5 — accept HPC-per-n (a Tier-3
   decision).** Materialise `M^chamber_n` (or `M^cofiber_n` + the descent)
   at `n = 6, 7` as Tier-3 HPC, apply F23's Rule B as the per-level
   selector, pin the genuine `c*_6, c*_7`, and pursue the `n`-uniform
   proof of (CM-rel) seeded by that data. F23's Rule B is the precise
   selector this route applies.
2. **The BK/Cheeger pivot (mg-26fc) — a PM/Daniel decision.** Pivot F10
   part (iii) to the BK/Cheeger-expansion mechanism (the in-tree
   `main.tex` + `step8.tex` spine, conditional on Hypothesis A), which
   does NOT need the canonical chamber-Morse critical cell. F23 does NOT
   pivot pre-emptively; it documents the alternative.

In-session (non-HPC) strengthenings, not load-bearing: verify Rule B at
`n = 4 → 5` via the chamber-quotient `Δ(C_5)` if a feasible equivariant
chamber-Morse matching there can be made to expose the critical 3-cell
orbits (the full-`Δ_5` route is HPC — F23 §6); investigate whether the
`min-|L|-profile` tie-break is provably tie-free among chamber-Morse
critical cells for all `n` (it is at `n = 3, 4`).

The framework F23 leaves: the descent (F21 Prop F21.1) is confirmed and is
the correct inductive *characterisation*; the *selector* is chamber-Morse
criticality (Rule B), `S`-equivariant via `min-|L|-profile`, but HPC-per-n;
no closed-form structural rule exists. The three structural models
(ι-tower, `M_rel^eq`-survivor, the descent) have all narrowed without
closing the recursion.

---

## §5. References

- mg-531f — F23 (this ticket).
  `docs/compatibility-geometry-F23-canonical-descent-rule.md`, this file,
  `scripts/compat_geom_F23_canonical_descent.py`.
- mg-0c5d — F22-HPC Session 2 (RED-tripwire): **Parent.** `state-F22-HPC.md`
  §5 (finding 6 — the 4-orbit under-specification F23 resolves; the three
  continuation routes — F23 is route 1). `compat_geom_F22_hpc_cell_tracking.py`
  Section 10 (the `n = 3` materialised trip-wire — F23's testbed infra).
- mg-43fb — F22-HPC Session 1 (GREEN-partial): the closure-operator lift
  infra; the exact record `c*_3,4,5`.
- mg-a2cb — F21 (GREEN-needs-hpc-anchor): Proposition F21.1 (the
  cofiber-Morse induction — F23 tests its descent clause); §5.2 (the
  lower-bound argument — F23 §1 confirms it concretely); Finding 2.1
  (no closed form forced by `n ≤ 5` — F23 §5 sharpens at the selector
  level).
- mg-c3fa — F20 (GREEN-partial): §1.3 (the chamber-Morse greedy is HPC for
  `n ≥ 5` — F23 §6 confirms).
- mg-5722 — F19: the ι-tower model (the first structural model, broken by
  F20).
- mg-4d3a — F17 (`M_rel^eq`); mg-d039 — F18 ((UCC.2)).
- mg-26fc — the two 1/3-2/3 mechanisms (the BK/Cheeger documented
  alternative — §4 continuation 2).
- mg-8216 — F10: §6.7 part (iii).

---

*Cumulative state doc for mg-531f (F23). Session 1 DONE — verdict
**GREEN-descent-pinned (HPC-per-n)**. Branch `polecat-cat-mg-531f`. A
canonical `S_{n+1}`-equivariant rule selecting `c*_{n+1}` from the 4-orbit
descent candidate set EXISTS (Rule B — chamber-Morse criticality, made
`S`-equivariant via `min-|L|-profile`; F23 candidate form B) and decisively
pins recorded `c*_4` at the `n = 3 → 4` testbed. But it is not closed-form
/ `n`-uniform — every structural discriminator fails `n`-uniformity against
the recorded `c*_3, c*_5`, and the rule needs the level-`(n+1)`
chamber-Morse matching (HPC-per-n). The cofiber-Morse induction (Prop
F21.1) narrows but does not self-close. "The canonical chamber-Morse
critical cell `c*_n`" is a well-defined canonical object — it does NOT need
re-founding (not AMBER) — but the chamber-Morse route to F10 part (iii) is
unblocked only in the HPC-per-n sense (route 2 of `state-F22-HPC` §5) or
the program pivots to the BK/Cheeger mechanism (mg-26fc): a PM/Daniel
decision. No new axioms; no Lean changes.*
