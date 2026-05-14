# state-F19 — cumulative state ledger for F19 ((ICOP-step) + the width-3 reduction bridge) (mg-5722)

**Pattern:** `feedback_polecat_cumulative_state_doc` — survives polecat session
boundaries. Ledger of what is done vs. deferred across the multi-session
(350k cap) F19 ticket.

**Branch:** `compat-geom-F19-icop-step-and-bridge` (mg-5722).
**Goal (mg-5722):** close the last two conditional inputs of F10 part (iii)
— **(ICOP-step)** (F10 §5.4, PRIMARY) and the **width-3 reduction bridge**
(F10 §7.3, in-ticket sibling). NO new axioms; no Lean changes; no new HPC;
no new empirical n-datapoint. The cohomological core is already
unconditional (F17 + F18); F19 is strictly F10 part (iii).

**Outcome (after Session 1):** **GREEN-partial.** (ICOP-step) substantially
advanced — its probabilistic content fully discharged by a rigorous
n-uniform lemma, and reduced to a clean purely-order-theoretic
sub-statement verified `n ≤ 6`. The width-3 bridge `m ≤ 4` base re-proven,
`m ≥ 5` cleanly reduced. See the Session-1 ledger below and
`docs/compatibility-geometry-F19-icop-step-and-bridge.md`.

---

## §1. Session 1 — 2026-05-14 (this polecat, mg-5722) — DONE

**Goal:** read the F10/F17/F18/F8/F8′/F5/F2 inputs; reconstruct the
canonical critical chains; isolate the n-uniform structural argument for
(ICOP-step); reduce the width-3 bridge; build a trip-wire harness; emit a
verdict.

**Completed:**

| Item | Status | Output |
|------|--------|--------|
| Read parents: F10 §5.2–5.4/§7.3–7.4/§6.7, F18 §5.4/§7.2, F8 §4.3–4.4/§6/§11, F8′ §3, F5 §4.3, F2 §4.3 | ✅ | — |
| **Lemma (L1)** — symmetric-pair lemma: symmetric incomparable pair ⇒ `Pr = 1/2` | ✅ rigorous, n-uniform, unconditional | proof doc §2 |
| **Proposition 3.1** — reduction (ICOP-step) ⟸ (L2) ⟸ (L2-struct) | ✅ rigorous reduction | proof doc §3.1, §3.3 |
| (L2) / (L2-struct) verified `n = 3,4,5,6` | ✅ via harness | proof doc §3.2; harness [B],[D],[H] |
| Residual identified precisely: n-uniform proof of (L2-struct) | ✅ → recommended F20 | proof doc §3.4 |
| Width-3 bridge `m ≤ 4` base re-proven (44/44 in PPF₄) | ✅ | proof doc §4.2; harness [F] |
| Width-3 bridge `m ≥ 5` reduced: `bridge(m≥5) ⟸ (ICOP-step) + (W3-cover)` | ✅ | proof doc §4.3–4.4 |
| Verification harness `scripts/compat_geom_F19_icop_step.py` (8 sections) | ✅ all trip-wires PASS | the harness |
| Verdict | ✅ **GREEN-partial** | see below |

**Verdict: GREEN-partial.**

The probabilistic content of (ICOP-step) is **fully discharged**,
rigorously and n-uniformly, by **Lemma (L1)** (the symmetric-pair lemma:
a cover step at a symmetric incomparable pair has Kahn–Saks probability
exactly `1/2 ∈ [3/11, 8/11]`). (ICOP-step) is then **reduced**
(Proposition 3.1) to the purely order-theoretic **(L2-struct)**: the
canonical critical cell's top poset `G_n` is a width-2 ordinal sum of
antichains. (L2-struct) is **verified `n ≤ 6`** (re-confirmed by the F19
harness) and is the precisely-identified residual. The width-3 reduction
bridge: `m ≤ 4` base re-proven (44/44 width-3 posets in PPF₄ are
BFT-sharp-witnessed); `m ≥ 5` cleanly reduced to (ICOP-step) + **(W3-cover)**
(the ι-tower meets every width-3 `S_m`-orbit).

Key structural findings:

1. **The symmetric-pair lemma is the n-uniform engine.** If `σ ∈ Aut(P)`
   swaps an incomparable pair `{x,y}`, then `⪯ ↦ ⪯^σ` is a bijection of
   `L(P)` carrying `{x ⪯ y}` onto `{y ⪯ x}`, so `Pr_P[x≺y] = 1/2`. No
   linear-extension counting, any poset size — fully n-uniform.

2. **(ICOP-step) at `n = 3,4,5,6` is uniformly `Pr = 1/2`.** The lex-min
   new cover of `G_n` (the cover building toward `c*_{n+1}`) is taken at a
   symmetric incomparable pair in every verified case — the strongest BFT
   form. (The chain's *internal* top step is a different, inherited object:
   `2/3` at `n=3,4`, `1/2` at `n=5` — governed by F8′ multiplicativity, not
   by (ICOP-step).)

3. **`G_n` is a width-2 ordinal sum of antichains** at `n = 3,4,5`
   (`G_3 = A_2⊕A_1`, `G_4 = A_1⊕A_1⊕A_2`, `G_5 = A_1⊕A_2⊕A_2`). In an OSA
   every incomparable pair lies inside one antichain block, hence is
   symmetric; this is (L2-struct) ⇒ (L2).

4. **(L2-struct) is not a naive greedy invariant.** The harness's negative
   control — the "always refine the lex-min symmetric pair" tower — loses
   ALL symmetry already at `n = 4`. So (L2-struct) is a property of the
   *canonical chamber-Morse construction specifically*; proving it
   n-uniformly needs the chamber-Morse machinery at general `n` (F8‴ HPC
   run, or a dedicated structural theorem) — the F20 residual.

5. **Both residuals are the same flavour.** (L2-struct) and (W3-cover) are
   both n-uniform structural facts about the `S_n`-equivariant
   chamber-Morse critical cells. A single F20 ticket on that structure
   addresses both; closing them makes F10 part (iii) unconditional and —
   with F17+F18 — the full width-3 1/3-2/3 theorem proven at general `n`.

**Trust-surface impact:** NONE. No new axioms; no Lean changes; no HPC; no
new empirical n-datapoint. Elementary order-complex combinatorics + a
trip-wire harness re-running the existing `n ≤ 6` record with exact
rational arithmetic. The in-tree Lean `width3_one_third_two_thirds`
4-axiom artifact is untouched.

**Deliverables produced this session:**
- `docs/compatibility-geometry-F19-icop-step-and-bridge.md` (NEW) — the
  proof document: §1 setting, §2 Lemma (L1), §3 the reduction to
  (L2-struct), §4 the width-3 bridge, §5 the harness, §6 establishes/does
  not, §7 verdict + F20 recommendation, §8 references.
- `docs/state-F19.md` (NEW, this file) — cumulative state ledger.
- `scripts/compat_geom_F19_icop_step.py` (NEW) — the verification harness;
  all trip-wires pass; runtime < 5 s; pure-Python stdlib.

---

## §2. The result, in one screen (reproduce-on-resume)

- **(ICOP-step) [F10 §5.4].** For every `n`, the lex-min new cover step
  appended to the top poset of `c*_n` in the ι-tower is BFT-sharp.
- **Lemma (L1).** `σ ∈ Aut(P)`, `σ(x)=y`, `σ(y)=x`, `x ∥ y` ⇒
  `Pr_P[x≺y] = 1/2`. Proof: `⪯ ↦ ⪯^σ` bijects `L(P)`, maps `{x⪯y}` to
  `{y⪯x}`. Rigorous, n-uniform, unconditional.
- **Reduction (Prop 3.1).** (ICOP-step) ⟸ **(L2)** "the canonical new cover
  is at a symmetric incomparable pair" ⟸ **(L2-struct)** "`G_n` is a
  width-2 ordinal sum of antichains" (in an OSA every incomparable pair is
  inside a block ⇒ symmetric; the lex-min cover lands in a block because
  the canonical labelling puts a size-2 block at the lex-least indices,
  below the free element).
- **Verified `n ≤ 6`:** `G_3 = A_2⊕A_1`, `G_4 = A_1⊕A_1⊕A_2`,
  `G_5 = A_1⊕A_2⊕A_2`, `ι_5(G_5)` — all width-2 OSA with a size-2 block;
  lex-min new cover symmetric, `Pr = 1/2`, at `n = 3,4,5,6`.
- **Residual:** an n-uniform proof of (L2-struct). Needs the F8‴ chamber-
  Morse HPC run or a dedicated structural theorem. → **F20**.
- **Width-3 bridge:** `m ≤ 4` rigorous base re-proven (44/44 in PPF₄);
  `bridge(m≥5) ⟸ (ICOP-step) + (W3-cover)`, with **(W3-cover)** = "the
  ι-tower meets every width-3 `S_m`-orbit" → **F20 sibling**.
- **Verdict:** GREEN-partial. Not GREEN-icop-step (L2-struct not proven
  ∀n); not AMBER (no stall — the analytic content IS closed n-uniformly);
  not RED (nothing false — `Pr = 1/2` is the safest BFT value).

---

## §3. Invariants (re-check against cited parent docs before extending)

- **`PPF_n` convention** — non-empty, non-total transitively-closed
  antisymmetric relation sets on `[n]`; ordered by relation-set inclusion
  (more relations ⇒ higher ⇒ fewer linear extensions). `|PPF_3| = 12`,
  `|PPF_4| = 194`, `|PPF_5| = 4110`. `ι_n` adds element `n` free.
- **`Pr_P[x≺y] = |L(P∪{x<y})| / |L(P)|`** — the Kahn–Saks probability of
  the cover step; BFT-sharp interval `[3/11, 8/11]`, `≈ [0.2727, 0.7273]`.
- **Lemma (L1) is unconditional and n-uniform** — it uses no chamber-Morse,
  no cohomology, no computation. The one obligation: `σ` must *swap*
  `x` and `y` (`σ(x)=y` AND `σ(y)=x`), not merely map `x` to `y`. The
  harness's `symmetric_pairs` checks exactly this.
- **(ICOP-step) is the lex-min cover of `G_n` (or `ι_n(G_n)`)** — the cover
  *appended going up* to build `c*_{n+1}`. It is NOT the chain's own
  internal top step (which is inherited, n-dependent, `2/3` at `n=3,4`).
  Do not conflate the two.
- **The F8′ multiplicativity law** `|L(ι_{n-1}(P))| = n·|L(P)|` is the
  elementary "free-point insertion multiplies LE-count by `m+1`" fact —
  rigorous, n-uniform; it makes the *inherited* steps n-independent, so
  (ICOP-step) is the only genuinely-new per-step probability.
- **`G_n` exact only at `n ≤ 5`** — `c*_3` (F8 §4.5), `c*_4` cell #1 (F2
  §4.3.1), `c*_5` (F5 §4.3 / F8′ §A). `n = 6` is the F8′ ι₅-lift
  *candidate* (`ι_5(G_5)`); the genuine `c*_6` needs the F8‴ HPC run.
  F19 inherits this status — the `n = 6` line is the established record,
  not a new datapoint.
- **(L2-struct) is NOT a greedy invariant** — the canonical chamber-Morse
  construction genuinely matters; verified by the harness §H negative
  control. Any F20 attempt must engage the chamber-Morse machinery.
- **Scope boundary** — F19 is strictly F10 part (iii)'s two secondary
  inputs. The cohomological core (parts (i)–(ii)), (UCC), F17/F18 are
  unconditional/complete and untouched. Route (iii)/mg-b345 stays PARKED.
- Trust-surface impact: none. No new axioms, no Lean changes, no HPC, no
  new n-datapoint.

---

## §4. If F19 is reopened for a Session 2 — in-scope continuations

Neither is load-bearing for the Session-1 verdict, but both would
strengthen it:

- (a) Extend the harness's (L2-struct) certification with a *structural*
  (non-enumerative) check at `n = 6` if the F8‴ canonical `c*_6` becomes
  available — currently `n = 6` uses the F8′ candidate.
- (b) Make Proposition 3.1's "the canonical labelling places a size-2
  block at the lex-least indices" fully explicit as a labelling lemma
  (currently argued from F8′ §3.5–3.7 + the harness).

**The genuine next step is a new ticket — F20** — targeting the structure
of the `S_n`-equivariant chamber-Morse critical cells at general `n`:
prove **(L2-struct)** (`G_n` is a width-2 ordinal sum of antichains) and
its sibling **(W3-cover)** (the ι-tower meets every width-3 `S_m`-orbit).
Closing (L2-struct) makes **(ICOP-step) proven n-uniformly**; closing both
makes **F10 part (iii) unconditional** and — with F17+F18 — the **full
width-3 Kahn–Saks 1/3-2/3 theorem proven at general `n`**.

---

## §5. References

- mg-5722 — F19 (this ticket).
- mg-d039 — F18 ((UCC.2)): `docs/compatibility-geometry-F18-ucc2-delta-injective.md`, `docs/state-F18.md`. Parent — §7.2 recommended (ICOP-step).
- mg-4d3a — F17 (equivariant cofiber Morse). With F18, cohomological core unconditional.
- mg-8216 — F10 (general-`n` synthesis): `docs/general-n-proof-synthesis.md` §5.2–5.4, §7.3–7.4, §6.7. Parent — defines (ICOP-step) and the bridge.
- mg-1e99 — F8 (ICOP framework): `docs/compatibility-geometry-F8-inductive-general-n.md` §4.3–4.4, §6, §11.
- mg-7b3b — F8′ (`n=6` ICOP): `docs/compatibility-geometry-F8prime-n6-icop.md` §3.
- mg-1e58 — F5 (chamber-Morse `n=5`): `docs/compatibility-geometry-F5-chamber-morse-n5-scoping.md` §4.3.
- mg-7455 / mg-6bc3 — F2 / F3 (`n=4`): `docs/compatibility-geometry-F2-scoping.md` §4.3.
- Code: `scripts/compat_geom_F19_icop_step.py` (this F19).
