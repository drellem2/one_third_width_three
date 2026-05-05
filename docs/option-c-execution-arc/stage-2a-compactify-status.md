# mg-2a56 — Option-C Stage 2A status (`LayeredDecomposition.compactify`)

**Status: GREEN.** The compactification infrastructure landed cleanly,
discharging Obstruction B (empty bands at sub-poset descent) of
`mg-979e-block-and-report.md` §1.b. No new project axioms; build green;
trip-wires 1, 2, 3, 4, 5, 6, 7 all clear.

This is the **substantive infrastructure chunk** of the Option-C
Stage 2 sequence per `mg-979e` §3.d. Stage 2B (Candidate A''
tightening + headline rewrite + consumer updates) consumes this
infrastructure on top.

## Deliverable

* `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean` — new
  module, 443 LoC total (269 code + 122 doc + 52 blank).
* `lean/OneThird.lean` — root import added at the natural place
  (after `LayeredReduction`, before `LayerOrdinal`).
* `lean/scripts/PrintAxiomsCompactify.lean` — axiom-audit script.

LoC delta: **+269 code (excluding doc/blank)**, well below the
trip-wire-4 ceiling of 525 and at the centre of the estimated
250-350 range.

## Architecture

Given `L : LayeredDecomposition α` and `S : Finset α`, the
constructor `L.compactify S : LayeredDecomposition ↥S` builds a
*compacted* layered decomposition on the sub-poset whose:

* depth `K' := compactBand L S L.K` counts only the non-empty bands
  of `L.restrict S`;
* width `w' := L.w` is preserved exactly;
* band map `band z := compactBand L S (L.band z.val)` takes the
  *rank* of `L.band z.val` among non-empty band indices in
  `[1, L.band z.val]`.

Empty bands are removed and the surviving bands are densely
re-numbered. The interaction width is preserved without tightening
(no sub-poset-specific information is consumed).

The structural correctness rests on **strict monotonicity of
`compactBand` at non-empty indices**: if `a < b` and `b` is a
non-empty band index, `compactBand L S a < compactBand L S b`. Rank
preserves the linear order of underlying band indices, so each new
band coincides with the restriction of an original (non-empty) band
to `S`.

## Preservation lemma coverage

| Property                                | Lemma                                     | Status |
| --------------------------------------- | ----------------------------------------- | ------ |
| `K' ≤ K`                                | `compactify_K_le`                         | ✅     |
| `K ≤ N → K' ≤ N`                        | `compactify_K_le_of_K_le`                 | ✅     |
| `w' = w` (preserved exactly)            | `compactify_w_eq` (`@[simp]`)             | ✅     |
| `w' ≤ w`                                | `compactify_w_le`                         | ✅     |
| `band' z ≤ L.band z.val`                | `compactify_band_le_orig`                 | ✅     |
| `|α| ≤ M → |↥S| ≤ M`                    | `compactify_card_le_of_card_le`           | ✅     |
| `Function.Injective L.band` propagates  | `compactify_band_injective_of_injective`  | ✅     |
| Band-relabelling structure (eq iff)     | `compactify_band_eq_iff_band_eq`          | ✅     |
| `band_pos` (≥ 1)                        | constructor field                         | ✅     |
| `band_le` (≤ K')                        | constructor field                         | ✅     |
| `band_size` (≤ 3)                       | constructor field                         | ✅     |
| `band_antichain` (each band antichain)  | constructor field                         | ✅     |
| `forced_lt` (L2-forced)                 | constructor field                         | ✅     |
| `cross_band_lt_upward` (L2-upward)      | constructor field                         | ✅     |
| API: `(L.compactify S).K = compactBand L S L.K` | `compactify_K` (`@[simp]`)        | ✅     |
| API: `(L.compactify S).band z = compactBand L S (L.band z.val)` | `compactify_band_apply` (`@[simp]`) | ✅ |

The Candidate A''-style cap propagation (Injective + K-cap +
cardinality-cap, per `mg-979e-block-and-report.md` §1.a/§1.b) is
covered by the trio
`compactify_band_injective_of_injective`,
`compactify_K_le_of_K_le`,
`compactify_card_le_of_card_le`.

## Axiom inventory

`#print axioms` against every public symbol in `Compactify.lean`
(see `lean/scripts/PrintAxiomsCompactify.lean`):

```
'OneThird.Step8.LayeredDecomposition.compactify' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_K_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_w_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_w_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_band_le_orig' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_K_le_of_K_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_card_le_of_card_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_band_injective_of_injective' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OneThird.Step8.LayeredDecomposition.compactify_band_eq_iff_band_eq' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

**Mathlib trio only.** No new project axioms introduced; the
`brightwell_sharp_centred` and
`case3Witness_hasBalancedPair_outOfScope` inventory of
`lean/AXIOMS.md` is unchanged. The headline
`width3_one_third_two_thirds` axiom output (recorded in
`lean/PRINT_AXIOMS_OUTPUT.txt`) is unchanged at
`[propext, Classical.choice, Quot.sound, brightwell_sharp_centred]`.

## Trip-wire status

| #  | Trip-wire                                                    | Status |
| -- | ------------------------------------------------------------ | ------ |
| 1  | Token overrun > 600k (150% of 400k cap)                      | clear  |
| 2  | New structural obstruction surfaces                          | clear  |
| 3  | F4-b trap reappears (Steps 5-7 fiber/coherence/global)       | clear  |
| 4  | LoC blow-up > 525 (150% of 350 max estimate)                 | clear  |
| 5  | `#print axioms` shows new project axiom                      | clear  |
| 6  | Existing `restrict` consumers require modification           | clear  |
| 7  | A K ≥ 3 leaf case doesn't compactify cleanly                 | clear  |

Trip-wire 6 specifically: the existing `LayeredDecomposition.restrict`
operator is unchanged. Compactification is a *companion* operator,
not a replacement. Any existing `restrict` consumer continues to work
verbatim; consumers that need empty-band cleanup will explicitly call
`compactify` on top.

## What this ticket does NOT do

Per the work-item spec, Stage 2A is infrastructure-only:

* ❌ Does not modify the headline `width3_one_third_two_thirds`.
* ❌ Does not drop `hC3` from any consumer.
* ❌ Does not add Candidate A'' cap hypotheses to `Case3Witness.{u}`.
* ❌ Does not change any consumer of `Case3Witness`.

Those are Stage 2B's scope, threaded on top of this infrastructure.

## Why no parallel cleanup chunk

Per `feedback_distinguish_arc_chunk_outcomes`, this is a **substantive
infrastructure chunk**: the Lean module IS the deliverable. Headline /
axiom inventory / `hC3` count / sorry count are all unchanged, by
design — Stage 2B ships those changes.

## Cross-references

* `mg-2a56` — this work item.
* `mg-979e-block-and-report.md` §1.b — Obstruction B (the empty-bands
  bug fixed here).
* `mg-979e-block-and-report.md` §3.a — the polecat-recommended
  compactification architecture this implements.
* `mg-979e-block-and-report.md` §3.d — the Stage 1 + Stage 2 sequence
  decomposition this lives inside.
* `mg-01ec` — Option-C Stage 1 (K=2 substantive closure, landed at
  `c403216` on `option-c-execution-arc`).
* `lean/OneThird/Step8/LayeredReduction.lean` — base `LayeredDecomposition`
  + `restrict` operator; the file we compactify on top of.
* `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean` — the
  new module shipped by this ticket.
* `lean/scripts/PrintAxiomsCompactify.lean` — axiom-audit script.
* `lean/AXIOMS.md` — unchanged (no new axioms).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — unchanged (headline axiom output
  identical to `9be3dec`).

---

*Filed 2026-05-05 by polecat for `mg-2a56`.*
