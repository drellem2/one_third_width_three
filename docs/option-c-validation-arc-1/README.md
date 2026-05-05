# Option-C validation arc 1

**EXPLORATORY ONLY — NOT a live program.**

`mg-fefe` (Option-C validation arc 1). Doc-only. No Lean source
changes; no signature changes; no new axioms. Three sub-deliverables
+ aggregate verdict.

---

## Index

| File | Sub-deliverable | Verdict |
|---|---|---|
| [`f1-inactive-n-core-proof.md`](f1-inactive-n-core-proof.md) | A. F1-inactive ⇒ N-poset-core uniform proof | GREEN |
| [`signature-design.md`](signature-design.md) | B. Signature design + cascade analysis | GREEN (Candidate A) |
| [`k-ge-3-lift-plan.md`](k-ge-3-lift-plan.md) | C. K ≥ 3 lift plan | AMBER (Candidate A' adjustment) |
| [`verdict.md`](verdict.md) | Aggregate verdict + execution arc recommendation | AMBER |

---

## Reading order

1. **`verdict.md` first** — the aggregate AMBER verdict, the
   recommendation for the execution arc, and the pre-commitment
   checklist for Daniel review. ~10 minutes to read.
2. **`f1-inactive-n-core-proof.md`** (Deliverable A) — the
   ~1-page paper-level proof that anchors Deliverable B's K=2
   discharge route and Deliverable C's K=2 leaf step. ~15 minutes
   to read.
3. **`signature-design.md`** (Deliverable B) — three candidate
   signatures + cascade analysis on the 7 operational consumers
   from `mg-e0b8` §2. Verdict: Candidate A (discharge in place,
   no signature change) wins on cascade. ~10 minutes to read.
4. **`k-ge-3-lift-plan.md`** (Deliverable C) — F3 step proof
   shape + leaf catalogue + LoC estimate + the K > 2w + 2
   coverage gap finding + the Candidate A' mitigation. ~15 minutes
   to read.

---

## Status

Filed 2026-05-05 by polecat. Branch `option-c-validation-arc-1`.

**Aggregate verdict: AMBER.** Two sub-deliverables GREEN
(A and B); Deliverable C surfaces a coverage gap (K > 2w + 2
width-3 layered irreducible leaves uncovered by existing in-tree
leaf-closers) with a clean mitigation (Candidate A' = Candidate A
+ small `Case3Witness.{u}` def tightening). The execution arc is
in PM scope to file pending Daniel review of the Candidate A'
adjustment and the K=2 closure scope.

---

## Cross-references

* `mg-344a` (active, Daniel's workspace) — Option-C proof shape
  origin.
* `mg-acc8` (archived) — `docs/alternating-cancellation-arc-1/`;
  ACL AMBER verdict.
* `mg-e112` (archived) — `docs/proof-approaches-catalog-1/`;
  40-class catalog + primitive inventory; consumed by
  Deliverables A and C.
* `mg-e0b8` (archived) — `docs/case3witness-operational-audit.md`;
  consumer inventory + bundle estimate; consumed by Deliverable B.
* `mg-cda8` (archived) — `docs/why-hC3-is-structural.md`;
  F1-F5 framing.
* `mg-805c` (archived) — B1 ship; size-minimality reductio.
