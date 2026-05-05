# Proof-approaches catalog 1 — bespoke combinatorics direction

**EXPLORATORY ONLY — NOT a live program.**  This directory carries
the three sub-deliverables of `mg-e112`, the proof-approaches
catalog for the bespoke-finite combinatorics direction (mg-344a)
on the K=2 obstruction family.  Doc-only; no Lean source changes;
no signature changes; no new axioms; no fresh paper-level math.

## Index

* `obstruction-enumeration.md` — §A: every isomorphism class of
  width-3 K=2 layered-irreducible poset with `w ≥ 1` and
  `|α| ∈ {3, 4, 5, 6}` (40 classes), tabulated with structural
  data (band partition, biadjacency, |L(α)|, |Aut|, within-band
  ⪯-pair status, F1 status, sign-imbalance, trichotomy tag).
* `proof-techniques-taxonomy.md` — §B: classification of proof
  techniques (counting, coupling, structural reduction, symmetry,
  direct enumeration, order polytope, spectral, FKG / log-concavity)
  with applicability to each branch of the trichotomy
  (N-poset-core / reducible / balanced-pair).
* `in-tree-primitive-inventory.md` — §C: catalog of every Lean
  lemma / def / structure / axiom in tree relevant to the
  trichotomy's discharge, plus a "primitives that COULD exist but
  DON'T" gap list.

## Direction context

* **Daniel directive 2026-05-05T~11:30Z** (in-session, post mg-8baf
  RED + post mg-344a direction-sharpening): "do we have work that
  can be started, perhaps to categorize possible proof approaches
  in our combinatorial case."
* **Working direction (mg-344a, active).** After arcs 1.0 / 2.0 /
  3.0 / 4.0 / cnc-1 closed (no GREEN / no USABLE), Daniel's
  direction shifts from "import asymptotic machinery" to "bespoke
  finite / rigid combinatorics on the quotient-to-chain frame."
  The saturation lemma proposed there uses the trichotomy
  N-poset-core / reducible / balanced-pair.
* **This catalog is the structural prerequisite for verifying
  that trichotomy by direct enumeration.**  Per Daniel's directive
  and PM scoping, the catalog is independent of whether the
  saturation lemma proves out: useful as reference material
  regardless (audit-as-deliverable per
  `feedback_audit_as_deliverable`).

## Status

* **Headline:** unchanged.
* **Axiom inventory:** unchanged.
* **`hC3` retention:** unchanged.
* **Sorry-count:** unchanged (zero sorries in tree, modulo the
  pre-existing `hC3` Prop hypothesis).

## Cross-references

* `mg-344a` (active, human) — Daniel's workspace ticket;
  saturation lemma direction; this catalog is its supporting
  reference material.
* `mg-e112` (this work) — PM-commissioned catalog deliverable.
* `mg-8baf` (archived) — `docs/conceptual-arc-1/lit-audit.md`;
  adjacent-field literature audit.  §B's category structure
  echoes mg-8baf's §1.3 / §3.3 framing but is distinct (techniques
  to apply directly vs external lemmas to import).
* `mg-cda8` (archived) — `docs/why-hC3-is-structural.md`; F1-F3
  framing.
* `mg-0bc8` (archived) — arc 4.0 scoping (math-simp arc 4.0);
  K=2 N-poset recurring centrality.
* `mg-e0b8` (archived) — `docs/case3witness-operational-audit.md`;
  Case3Witness operational consumption audit.
* `mg-805c` (archived) — B1 size-minimality ship.
* `mg-b666` / `mg-a79e` / `mg-b0de` — Track 1 round 1 + A8-S2
  block-and-report; case-2-strict residual obstruction.

## Audit-bar discipline

* `feedback_audit_bar_for_axioms` — applies; no new axioms.
* `feedback_signature_regressions` — applies; no signature changes.
* `feedback_n_poset_is_not_ordinal_sum` — applies; N-poset
  classes correctly tagged as **N**.
* `feedback_audit_as_deliverable` — applies; the catalog IS the
  deliverable.
* `feedback_distinguish_arc_chunk_outcomes` — applies at close;
  substantive catalog chunk; no parallel cleanup; headline /
  axiom inventory / hC3 / sorry-count unchanged.

## Provenance

Filed 2026-05-05 by polecat.  Origin: Daniel directive
2026-05-05T~11:30Z (in-session, no reminder ID).  Direction
context: mg-344a (active).
