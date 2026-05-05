# Aggregate verdict — Option-C validation arc 1

**EXPLORATORY ONLY — NOT a live program.**

Aggregate verdict for `mg-fefe` (Option-C validation arc 1). Doc-only.

---

## §0 — Headline verdict

**AMBER** — two of three sub-deliverables land GREEN; Deliverable C
surfaces a coverage gap (K > 2w + 2 width-3 layered irreducible
leaves not covered by existing in-tree leaf-closers) that has a
clean mitigation (signature tightening, Candidate A') but
adjusts the Deliverable B picture from "no signature change" to
"minimal signature tightening". The execution arc is still in PM
scope to file (the mitigation is mechanical), but this should be
surfaced for Daniel review before commitment.

| Sub-deliverable | Verdict | Trip-wires fired? |
|---|---|---|
| **A** — F1-inactive ⇒ N-poset-core proof | **GREEN** | None. |
| **B** — Signature design + cascade analysis | **GREEN** | None. |
| **C** — K ≥ 3 lift plan | **AMBER** | None strictly; coverage gap raised but not a "new structural fact F6/F7". |

The aggregate **AMBER** reflects Deliverable C's coverage-gap
finding, not a failure. The path forward is well-defined:
Candidate A' (Candidate A from B + a 1-line def tightening of
`Case3Witness.{u}` to add `LB.K ≤ 2 * LB.w + 2 ∧ Fintype.card β ≤
6 * LB.w + 6` as hypotheses).

---

## §1 — Per-deliverable findings

### Deliverable A — F1-inactive ⇒ N-poset-core proof: GREEN

* **Theorem proven** uniformly via two structural lemmas (Lemma 1:
  F1-inactive ⇒ ∃ row pair with incomparable nbhds; Lemma 2:
  incomparable row nbhds ⇒ N-poset-core).
* **Hypotheses tight**: K = 2, w ≥ 1, width 3, layered-irreducible,
  `|α| ∈ {4, 5, 6}` (the `|α| = 3` antichain case is a degenerate
  remark per `f1-inactive-n-core-proof.md` §3 — closed by
  `bipartite_balanced_enum` directly).
* **6-class verification** explicit at every F1-inactive class
  with `|α| ≥ 4` (Class 1 = K2-N4-22-N, Class 2 = K2-N5-23-1⊄2,
  Class 3 = K2-N5-32-1⊄2, Class 4 = K2-N6-M, Class 5 =
  K2-N6-{122}-(1,2,2)a, Class 6 = K2-N6-{222}-(2,2,2)).
* **Catalog correction noted** (`f1-inactive-n-core-proof.md` §4):
  mg-e112 §A §4's enumeration of F1-inactive classes was
  partially incorrect (omitted K2-N5-23-1⊄2 and K2-N5-32-1⊄2).
  Re-derived from the matrices: total 8 F1-inactive classes
  (matching the §4 corrected count).
* **Robustness discussion** (§6) covers extension to |α| ≥ 7
  (vacuous within K=2 width-3), K ≥ 3 (deferred to Deliverable C),
  width relaxation, and w = 0 vacuity.
* **No trip-wires fire**: F4-b (no Steps 5-7 fiber/coherence),
  F6/F7 (no new structural facts), `feedback_n_poset_is_not_ordinal_sum`
  PASS, no new axioms.
* **Bounded paper-math**: ~1 page of structural argument as
  budgeted by the ticket.

**Verdict GREEN** — the implication-as-theorem holds uniformly
across the F1-inactive |α| ≥ 4 sub-family, ready for consumption
by the execution arc's K=2 closure (`option_c_K2_closure` in
Deliverable C §4.a's `hStep` sketch).

### Deliverable B — Signature design + cascade analysis: GREEN

* **Three candidates considered**:
  - **A — Discharge in place (no signature change)**: 7 ×
    MECHANICAL across all 7 operational consumers; 0 × CASCADE.
  - **B — K2RestrictedCase3Witness (audit §4a sketch)**: 1 ×
    CASCADE on `lem_layered_balanced` (full F3 rewrite); trip-wire 4
    borderline.
  - **C — Bundled ACL + trigger + certificate**: 3 × CASCADE,
    trip-wire 4 fires; bundle bakes dispatch into signature
    (anti-pattern).
* **Recommendation: Candidate A**. The audit's
  operational-load-bearing finding (universal-quantifier
  reading, `mg-e0b8` §3a) is **preserved** by Candidate A —
  rather than circumvented by tightening the universal, it is
  honored by discharging the universal in tree.
* **Mathematical content preserved exactly**: signature
  unchanged ⇒ Prop content unchanged.
* **Cascade is bounded** at 7 × MECHANICAL — the
  `feedback_signature_regressions` audit-bar PASSES.
* **The K=2 case-2-strict residual** (`mg-b666` Track 1) is
  absorbed inside the K=2 branch of `Case3Witness_proof`'s
  body via the Bool certificate over the 40-class catalog
  (per `path-c-cleanup-roadmap.md` §6b), bypassing
  `Case2FKGSubClaim` entirely.

**Verdict GREEN** — Candidate A is the audit's recommendation
in disguise; the universal scope is preserved and discharged
in place, bounded at MECHANICAL cascade.

### Deliverable C — K ≥ 3 lift plan: AMBER

* **F3 step shape laid out** (`k-ge-3-lift-plan.md` §4.a) with
  reducible-cut descent + leaf K-dispatch (K=1, K=2, K ≥ 3).
* **Leaf catalogue** at K ≥ 3 (§2): InCase3Scope ⇒
  `case3_certificate`; ¬ InCase3Scope (within F5 C2 caps) ⇒
  `case3Witness_hasBalancedPair_outOfScope`; both wired through
  `bounded_irreducible_balanced_hybrid`.
* **LoC estimate**: hStep ~130-220 LoC + Case3Witness_proof
  composition ~30-50 LoC = ~160-270 LoC. Adding K=2 closure
  (~300-500 LoC for the 40-class Bool certificate) and headline
  re-wiring (~10-20 LoC) gives a total bundle of ~470-790 LoC,
  matching `mg-e0b8` §5c's ~480-700 estimate within rounding.
* **mg-e112 §C cross-reference** (§5): every needed primitive
  for the F3 step is in tree. The single missing primitive is
  the K=2 Bool certificate over the 40-class catalog (the
  substantive new work in the execution arc).
* **Coverage gap raised** (§2.d, §3): width-3 layered
  irreducible posets with `K > 2 * w + 2` exist (§3's K=5, w=1,
  |α|=5 zigzag witness) but are uncovered by every existing
  in-tree leaf-closer. The gap is **vacuous at the operational
  headline path** (where `K = |α|, w = |α| + 1` always satisfies
  `K ≤ 2w + 2`), so the gap doesn't block the execution arc;
  but the universal `Case3Witness.{u}` def is over-strong
  relative to in-tree coverage.
* **Mitigation: Candidate A'** (§6). Tighten `Case3Witness.{u}`'s
  def to add `LB.K ≤ 2 * LB.w + 2 ∧ Fintype.card β ≤ 6 * LB.w + 6`
  as hypotheses. This is a small signature change that makes the
  in-tree coverage explicit at the type level. Cascade impact:
  unchanged from Candidate A (still 7 × MECHANICAL — the cap
  proofs at `LayeredBalanced.lean:548` are trivial given the
  headline path's `K = |α|, w = |α| + 1`).
* **Trip-wire 2** (new structural fact F6/F7): does **not**
  strictly fire (the gap is a coverage mismatch, not a new
  failure mode of an argument). Borderline reportable; surfaced
  here for visibility.
* **Trip-wires 1, 4, audit-bar, F4-b**: do **not** fire.

**Verdict AMBER** — the K ≥ 3 plan is sound and bounded for the
operational headline path; the coverage gap surfaced is a
def-vs-machinery scope mismatch that is mitigated by Candidate A'
(small signature tightening). Surfacing for Daniel review before
the execution arc commits.

---

## §2 — Recommendation for the execution arc

### §2.a — Path forward

**File the execution arc** (the implementation ticket the validation
arc is gating) **with Candidate A' as the signature shape**:

1. **K=2 substantive closure** (`option_c_K2_closure`):
   ~300-500 LoC. Combines Deliverable A's F1-inactive ⇒ N-core
   trigger with a K=2 Bool certificate over the 40-class catalog
   (mg-e112 §A). Bypasses `Case2FKGSubClaim` per
   `path-c-cleanup-roadmap.md` §6b. **The substantive new math.**
2. **F3 step proof** (`hStep`): ~130-220 LoC per Deliverable C §4.b.
   Composes reducible-cut descent + K-dispatch + existing in-tree
   leaf-closers. **Mechanical glue.**
3. **`Case3Witness_proof`**: ~30-50 LoC. Threads `hStep` through
   `hasBalancedPair_of_layered_strongInduction_width3`. **Mechanical
   glue.**
4. **`Case3Witness.{u}` def tightening to Candidate A'**: ~5-10
   LoC. Adds two cap inequalities to the universal.
5. **Consumer thread updates**: ~10-30 LoC across C2-C7. Drop
   `hC3` parameter; supply `Case3Witness_proof` instead.
   Mechanical re-typing.

**Total bundle**: ~475-810 LoC. Matches the `mg-e0b8` §5c
estimate (~480-700 LoC) within tolerance. Multi-polecat or
single-polecat Daniel-confirmed scope.

### §2.b — What the execution arc commits

* **Drops `hC3` from headline.** `width3_one_third_two_thirds`
  becomes hypothesis-free (the Option-C content is in tree).
* **No new project axioms.** All existing axioms
  (`case3Witness_hasBalancedPair_outOfScope`, `Lean.ofReduceBool`
  via `native_decide`, `brightwell_sharp_centred`) reused.
* **Closes the case-2-strict residual** (`mg-b666` Track 1)
  structurally via the K=2 Bool certificate, bypassing the
  provably-false `Case2FKGSubClaim`.
* **Tightens `Case3Witness.{u}`'s scope** to match in-tree coverage
  (Candidate A' caps).

### §2.c — What the execution arc does NOT commit

* **Does not handle K > 2w + 2 width-3 layered irreducible
  posets** (Deliverable C §3's coverage gap). These are vacuous
  at the headline path; their formal universal coverage is
  punted to a future arc if ever needed.
* **Does not promote ACL to a load-bearing role**. The
  alternating-cancellation lemma (`mg-acc8`) is invoked
  conceptually in the K=2 closure's structure but not as the
  central argument; the central argument is the Bool certificate
  + Deliverable A's F1 trigger. ACL is the framing inspiration,
  not the proof.
* **Does not change anything outside Step 8**. Steps 1-7 stay
  unchanged; Mathlib subtype API stays unchanged; Brightwell
  axiom stays unchanged.

### §2.d — Pre-commitment checklist for Daniel

Before filing the execution arc, surface to Daniel:

1. **Candidate A' mini-signature change**: the `Case3Witness.{u}`
   def adds two cap hypotheses. Is this acceptable?
   - PRO: aligns def with in-tree machinery; trivially provable
     at headline path.
   - CON: requires headline call-site to supply the cap proofs
     (~3-5 LoC; trivial via `omega`).
   - Default: yes, acceptable per `feedback_signature_regressions`
     and `feedback_audit_bar_for_axioms` (no new axioms; content
     preserved modulo cap restriction).
2. **K > 2w + 2 coverage gap**: punted to future. Acceptable?
   - PRO: vacuous at operational headline path; building new
     leaf-closer for this is paper-tier math (Option-α
     escalation).
   - CON: the universal `Case3Witness.{u}` is over-strong relative
     to what's provable in tree.
   - Default: yes, punt (Candidate A' tightens the def to match
     in-tree coverage; the punt is **explicit at the type level**).
3. **K=2 closure scope**: ~300-500 LoC for the 40-class Bool
   certificate. Multi-polecat?
   - PRO: bounded combinatorial enumeration; reuses
     `case3_certificate`'s Bool kit.
   - CON: substantive new content; needs careful audit per
     `feedback_audit_bar_for_axioms`.
   - Default: single-polecat or multi-polecat depending on
     timeline; within scope per `path-c-cleanup-roadmap.md` §6b.

If Daniel confirms 1, 2, 3, the execution arc is in PM scope to
file as a single ticket (or a 2-3 ticket sequence for K=2 closure
→ F3 step + Case3Witness_proof → headline rewrite).

---

## §3 — Trip-wire summary

| Trip-wire | Sub-D A | Sub-D B | Sub-D C | Aggregate |
|---|---|---|---|---|
| 1. Single sub-D budget overrun | NO | NO | NO | NO |
| 2. New structural obstruction (F6/F7) | NO | NO | borderline | borderline |
| 3. F4-b trap (relabelling-as-progress) | NO | NO | NO | NO |
| 4. Signature cascade unbounded | n/a | NO | NO | NO |
| 5. K ≥ 3 cataloguing surfaces new structural facts | n/a | n/a | borderline | borderline |
| 6. Token budget overrun | NO | NO | NO | NO |
| 7. Re-derivation of arc 1-4 / mg-* content | NO | NO | NO | NO |

**Trip-wires 2 and 5 are borderline reportable** because the
K > 2w + 2 coverage gap surfaces in Deliverable C — but per the
analysis in `k-ge-3-lift-plan.md` §7.a, the gap is a coverage
mismatch (existing leaf-closer caps don't span the universal
def), **not** a new structural fact about K ≥ 3 layered irreducible
posets. It's a scope alignment issue, mitigated cleanly by
Candidate A'. AMBER, not RED.

---

## §4 — Outcome class

Per `feedback_distinguish_arc_chunk_outcomes`:
**substantive validation chunk; no parallel cleanup.** The three
deliverables IS the deliverable. **Headline / axiom inventory /
hC3 / sorry-count all unchanged** (this validation arc is doc-only;
the execution arc will change the headline + hC3, with axiom
inventory unchanged).

---

## §5 — Provenance

Aggregate verdict for `mg-fefe`. Filed 2026-05-05 by polecat.
Origin: Daniel directive 2026-05-05T~15:24Z. Branch
`option-c-validation-arc-1`.

The polecat's mini-CEO scope was exercised (per arc 2.0 §6.4.4
and the in-session Daniel reminder). Verdict AMBER reflects honest
assessment of the K > 2w + 2 coverage gap; no auto-pivot to RED
or GREEN. Returns to mg-344a workspace pending Daniel review.
