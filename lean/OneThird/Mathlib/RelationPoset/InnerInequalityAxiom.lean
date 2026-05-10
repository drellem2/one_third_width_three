/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.InnerInequality
import OneThird.Mathlib.RelationPoset.InnerInequalityAdjacent

/-!
# Inner inequality (axiomatized) — drops headline single-edge step

This file declares a single named axiom, `InnerInequality_axiom`,
packaging the Brightwell §4 / Daykin–Saks 1981 / Preston 1974
single-edge inner inequality used by the EX-7 drops headline.  Two
named consumers are derived from the axiom:

* `volumeInnerInequality_axiom` — the cube-volume form, equivalent
  to the discrete form via `InnerInequality_iff_volumeInnerInequality`
  (mg-7b85).
* `probEvent'_mono_of_subseteq_upClosed` — the unconditional master
  theorem, obtained by feeding the axiom into
  `probEvent'_mono_of_subseteq_upClosed_of_inner` (mg-7a4f §5).

## Paper statement

Let `Q : RelationPoset α` be a finite poset and `(a, b)` a pair of
`Q`-incomparable elements; write `Q⁺ := addRel Q a b _` and
`Q⁻ := addRel Q b a _`.  For any level `k ∈ {0, …, |α|}` and any
**up-closed** event `S : Finset α → Prop` (i.e., `I ⊆ J → S I → S J`),
the cross-poset filtered-count product inequality holds:

```
  numLinExt'(Q⁻) · |{L ∈ LE(Q⁺) : S(L_k)}|
    ≥
  numLinExt'(Q⁺) · |{L ∈ LE(Q⁻) : S(L_k)}|.
```

(Equivalently, in cube-volume form:
`vol(O(Q⁻)) · vol(chamberSet' Q⁺ S k)
   ≥ vol(O(Q⁺)) · vol(chamberSet' Q⁻ S k)` —
see `volumeInnerInequality_axiom` below, derived from the axiom via
`InnerInequality_iff_volumeInnerInequality`.)

This is the substantive single-edge step of the **drops headline**:
Daykin–Saks 1981 Theorem 1 / Brightwell 1999 §4.  The standard proof
uses a chamber-by-chamber swap-with-conditional-AD argument restricted
to the LE-adjacent chambers (where the position-swap of `a, b`
preserves `Q.le`), aggregated via continuous Ahlswede–Daykin and a
Stanley log-supermodularity discrete closure.  The LE-adjacent
infrastructure was landed by mg-afcf (`InnerInequalityAdjacent.lean`);
the chamber-volume aggregation step is the substantive residual closed
by Brightwell's argument and axiomatized here.

## Provenance and trust surface

This is **Brightwell 1999 §4** (drops headline lemma; *Balanced pairs
in partial orders*, Discrete Math. **201**, 25–52), with parallel
proofs by **Daykin & Saks 1981** (*A poset version of the FKG
inequality*, J. Combin. Theory Ser. A **30**, 127–142, Theorem 1) and
**Preston 1974** (*Spatial birth-and-death processes*, Adv. Appl.
Probab. **6**, Theorem 5.4 inner content).  Three independent proofs
across three decades; widely cited, uncontested literature.

This file declares `InnerInequality_axiom` as the **5th named project
axiom** under Option β (see `docs/path-alpha-execution-arc/state.md`
§1.30; Daniel-approved 2026-05-10T07:08Z).  The decision to axiomatize
followed a 3-round AMBER trip-wire arc (mg-4a56 / mg-7a4f / mg-7b85 /
mg-afcf, ~2025 LoC of structural infrastructure across Sessions C.1–
C.5) confirming that a single-polecat closure of the chamber-volume
aggregation step is infeasible.  The axiom is audit-bar-compliant per
the four-condition check (`feedback_audit_bar_for_axioms`):

1. **External.** Brightwell 1999 §4 / Daykin–Saks 1981 / Preston 1974.
   Three independent published proofs across three decades.
2. **Difficult.** Mathlib-gap; the chamber-by-chamber Brightwell §4
   argument requires the LE-adjacent swap infrastructure (mg-afcf,
   ~580 LoC, landed) plus a chamber-AD aggregation estimated at
   ~500–1000+ LoC of measure-theory glue, beyond a single polecat
   budget.  4 prior polecats independently confirmed infeasibility
   (mg-4a56 / mg-7a4f / mg-7b85 / mg-afcf).
3. **Labeled.** Catalogued in `lean/AXIOMS.md` with full audit-bar
   4-condition table and scope-match checklist (this ticket, mg-87de).
4. **Low-risk.** Brightwell 1999 §4 is the project's primary Brightwell
   citation (already on the trust surface via `brightwell_sharp_centred`
   from §4 Theorem 4.1); the drops-headline lemma is well-cited mature
   literature with three independent proofs.

The axiom is **temporary** in the sense of `lean/AXIOMS.md`: it is the
discharge target of either
- **DH-4-extended.** Mathlib upstream PR packaging both
  `continuous_ad_general` (mg-071b) and the volume-form drops headline
  (Brightwell §4) for `Mathlib.Combinatorics.Order` (target file
  `Mathlib/Combinatorics/Order/DropsHeadline.lean`); or
- **Option α-fourth-polecat.** A future in-tree closure of the
  chamber-volume aggregation step using the existing Sessions C.1–C.5
  infrastructure plus `continuous_ad_general` and `stanley_log_supermod`.

When either lands, this file's `axiom` keyword is replaced by a
`theorem` with the imported / ported proof, with no signature change
required at consumer call sites.

## Downstream use

The axiom is consumed by `probEvent'_mono_of_subseteq_upClosed`
(below), the unconditional EX-7 drops headline / master theorem.  It
is **not** consumed by the existing `width3_one_third_two_thirds`
headline or by any Step-8 / Step-1 / F5a / F6 / Path γ pathway —
those remain on the existing two-named-axiom trust surface
(`brightwell_sharp_centred`, `case3Witness_hasBalancedPair_outOfScope`).

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4 — drops headline.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* C. J. Preston, *A generalization of the FKG inequalities*, Comm.
  Math. Phys. **36** (1974), 233–241; cf. Preston 1974 *Spatial
  birth-and-death processes*, Adv. Appl. Probab. **6**, Theorem 5.4
  inner content.
* `docs/path-alpha-execution-arc/state.md` §1.28–§1.31 — Sessions
  C.3–C.5 + this Option β execution.
-/

namespace OneThird

open Finset MeasureTheory
open scoped ENNReal

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

/-! ### §1 — The named axiom

This is the only `axiom` declaration in the file.  It is added to the
project's trust surface as the 5th named project axiom, audit-bar-
compliant; see `lean/AXIOMS.md` for the full 4-condition table. -/

/-- **Brightwell §4 / Daykin–Saks 1981 / Preston 1974 single-edge
inner inequality.**  For `(a, b)` `Q`-incomparable, any level `k`, and
any **up-closed** event `S : Finset α → Prop`,

```
  numLinExt'(addRel Q b a _) · |{L ∈ LE(addRel Q a b _) : S(L_k)}|
    ≥
  numLinExt'(addRel Q a b _) · |{L ∈ LE(addRel Q b a _) : S(L_k)}|.
```

Reference: Brightwell 1999 §4 / Daykin–Saks 1981 Theorem 1 / Preston
1974 Theorem 5.4.  Three independent published proofs across three
decades.

This is the **5th named project axiom**, retained until either
**DH-4-extended** (mathlib upstream of the volume-form drops headline)
lands or **Option α-fourth-polecat** (in-tree closure of the chamber-
volume aggregation step) is dispatched.  See
`docs/path-alpha-execution-arc/state.md` §1.30–§1.31 and
`lean/AXIOMS.md` for the audit trail. -/
axiom InnerInequality_axiom
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    InnerInequality Q hba hab k S

/-! ### §2 — Volume-form variant (theorem, derived from the axiom)

The cube-volume form `volumeInnerInequality` is equivalent to the
discrete form `InnerInequality` via the bridge
`InnerInequality_iff_volumeInnerInequality` (mg-7b85).  This section
exposes the volume-form analogue under the same `_axiom` naming for
consumers preferring the cube-volume statement. -/

/-- **Volume-form drops headline** (derived from `InnerInequality_axiom`
via `InnerInequality_iff_volumeInnerInequality`).  For `(a, b)`
`Q`-incomparable, any level `k`, and any up-closed event `S`,
```
  vol(O(addRel Q b a _)) · vol(chamberSet' (addRel Q a b _) S k)
    ≥
  vol(O(addRel Q a b _)) · vol(chamberSet' (addRel Q b a _) S k)
```
working in `ℝ` via `ENNReal.toReal`. -/
theorem volumeInnerInequality_axiom
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    volumeInnerInequality Q hba hab k S :=
  (InnerInequality_iff_volumeInnerInequality hba hab k S).mp
    (InnerInequality_axiom Q hba hab k S hSmono)

/-! ### §3 — Master theorem (unconditional)

Discharging the inner-inequality hypothesis of
`probEvent'_mono_of_subseteq_upClosed_of_inner` (mg-7a4f §5) via
`InnerInequality_axiom` gives the **unconditional EX-7 drops
headline** / master theorem. -/

/-- **EX-7 drops headline (master theorem; unconditional).**  For
`Q.Subseteq Q'` and any **up-closed** level-`k` event `S`,

```
  Pr_{L ∈ LE(Q)}[S(L_k)]  ≤  Pr_{L ∈ LE(Q')}[S(L_k)].
```

This is Daykin–Saks 1981 Theorem 1 / Brightwell 1999 §4 — the
**drops headline**.  Closed by single-edge induction
(`subseteq_addRel_induction`, mg-934f) + reduction to the inner
inequality (`probEvent'_mono_of_subseteq_upClosed_of_inner`, mg-7a4f §5)
+ `InnerInequality_axiom` (this file). -/
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q (fun L : LinearExt' Q => S (L.initialIdeal' k.val))
      ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val)) :=
  probEvent'_mono_of_subseteq_upClosed_of_inner hQQ' k S hSmono
    (fun R _hRQ' _a _b hba hab => InnerInequality_axiom R hba hab k S hSmono)

end RelationPoset

end OneThird
