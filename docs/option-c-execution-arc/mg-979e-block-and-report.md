# mg-979e — Block-and-report (trip-wires 1 + 5)

**Status: BLOCKED.** No Lean source landed. PM mail follows.

`mg-979e` (Option-C execution arc, sequence ticket 2) was scoped
at 400k tokens to glue the K=2 substantive closure (`mg-01ec`'s
`option_c_K2_closure`) with F3 + leaf closers, drop `hC3` from
the headline, and tighten `Case3Witness.{u}` to Candidate A'.

Polecat survey + a partial implementation attempt surfaced two
overlapping obstructions that fire **trip-wire 5** ("K ≥ 3
leaf-closure fails. Existing `bounded_irreducible_balanced_hybrid`
doesn't compose cleanly with `option_c_K2_closure` and the
existing axioms → STOP") and **trip-wire 1** ("Token overrun
> 600k → STOP" — would reach this if the polecat tried to build
the full set of additional infrastructure required to close the
gaps). PM mail follows; per
`feedback_polecat_stop_runaway`, no auto-extension; await PM
direction.

---

## §1 — Two overlapping structural obstructions

### §1.a — Obstruction A: K ≥ 3 + ¬InCase3Scope + Case 2

The K ≥ 3 leaf K-dispatch in `k-ge-3-lift-plan.md` §4.a routes
through `bounded_irreducible_balanced_hybrid` with `hStruct`
discharged via `case1_dispatch_balanced_or_witness`
(`Case3Dispatch.lean:271`):

```
HasBalancedPair α ∨ Case2Witness L ∨ Case3Witness L
```

* `HasBalancedPair α` — done.
* `Case3Witness L` — `case3Witness_hasBalancedPair_outOfScope`
  (existing project axiom).
* **`Case2Witness L` — gap.** Discharge requires
  `Case2FKGSubClaim L`, which is **provably false** (K=2 N-poset
  counterexample, per `docs/path-c-cleanup-roadmap.md` §5;
  `mg-8f59` / `mg-a79e` / `mg-b0de`). The same counterexample-class
  extends to K ≥ 3 width-3 layered configurations admitting
  within-band ⪯-comparable pairs.

`option_c_K2_closure` (`mg-01ec`) bypasses Case 2 at K=2 by
unified Bool-certificate enumeration over the 40-class catalog at
`w = 1`, `|β| ≤ 6`. No analogous infrastructure exists for K ≥ 3
(`mg-fefe` Deliverable C §3 — the K=5, w=1, |α|=5 zigzag is one
of many uncovered cases).

**Candidate A' (the planned tightening) does not close this gap.**
Adding `LB.K ≤ 2 * LB.w + 2` and `Fintype.card β ≤ 6 * LB.w + 6`
to `Case3Witness.{u}` (per `k-ge-3-lift-plan.md` §6) makes the
F3-step's invariants explicit but does **not** exclude
`Case2Witness L` from the universal scope. Real layered
configurations within the F5 C2 caps + ¬InCase3Scope can carry a
strict within-band ⪯-comparable pair (e.g. K=4 width-3 bipartite
with a within-band size-≥2 antichain admitting profile_le).

### §1.b — Obstruction B: empty bands at sub-poset descent (Candidate A'' attempt)

This polecat attempted to close obstruction A via **Candidate
A''** — Candidate A' plus `Function.Injective LB.band` as a
third cap. Injectivity makes `Case2Witness L` vacuous (the
predicate posits distinct `a, a'` with `band a = band a'`,
contradicting injectivity). The cap is supplied trivially at the
operational headline path (`layeredFromBridges` builds `band`
from a Szpilrajn extension, which is injective by construction).

**A second obstruction surfaced at sub-poset descent.** F3-step's
reducible-cut descent calls `OrdinalDecompOfReducible L k` and
recurses on `↥D.Lower` or `↥D.Upper` via `L.restrict`. The
restriction preserves `K = L.K` and `w = L.w` but reduces
`|↥S| < |α|`. The injectivity cap propagates via
`Subtype.val ∘ band` ✓.

But the sub-poset has **empty bands**: `(L.restrict S).bandSize k`
can be 0 for bands not represented in `S`. Empty bands break two
leaf-dispatch primitives:

1. **`bounded_irreducible_balanced_inScope`** (K=3 InCase3Scope
   leaf) requires `hNonempty : ∀ k ∈ [1, K], 1 ≤ bandSize L k`.
   Fails at sub-posets with empty bands.

2. **Reducible-cut search at sub-posets** can find only "trivial"
   reducible cuts — cuts where `D.Lower = ∅` or `D.Upper = ∅`,
   making `LayerOrdinalReducible L k` vacuously true. Trivial
   cuts produce zero progress on the IH (don't strictly shrink
   |↥S|). And the parent might satisfy
   `¬LayerOrdinalIrreducible L` (some trivial reducible)
   without admitting any non-trivial reducible — leaving the F3
   step stuck between leaf dispatch (which needs irreducibility)
   and descent (which needs a non-trivial cut).

The fix is **band-compactification**: at `restrict`, build a new
`LayeredDecomposition` on `↥S` with `K' = #{k ∈ [1, K] |
bandSize ≥ 1}` and band map shifted to enumerate `[1, K']`. This
is structural new infrastructure — comparable in scale to
`mg-01ec` (~100-200 LoC for the compactification itself plus
preservation lemmas for K, w, caps, injective, and the layered
axioms `forced_lt` / `cross_band_lt_upward`).

### §1.c — Combined assessment

The two obstructions interlock:

* Without obstruction A's mitigation (Injective cap), the F3
  step's K ≥ 3 leaf can't close Case 2.
* With obstruction A's mitigation, obstruction B emerges at
  sub-poset descent.

Closing both within Candidate A''-class cap tightening requires:

1. The Injective cap (or stronger).
2. Band-compactification infrastructure for `restrict`.
3. Cap propagation under compactification.

Combined LoC estimate: ~300-500 LoC, comparable to `mg-01ec`'s
K=2 closure scope. **Out of `mg-979e`'s 400k-token budget.**

---

## §2 — What this polecat completed

* Surveyed the F3 framework
  (`hasBalancedPair_of_layered_strongInduction_width3`,
  `LayerOrdinal.lean:472`), the 7 operational consumers of
  `Case3Witness.{u}`, the K=2 closure architecture
  (`option_c_K2_closure`, `K2Closure.lean:500`), and the leaf
  closers (`bounded_irreducible_balanced_inScope`,
  `bounded_irreducible_balanced_hybrid`,
  `case3Witness_hasBalancedPair_outOfScope`).
* Identified obstruction A (Case 2 gap at K ≥ 3 ¬InCase3Scope)
  via `case1_dispatch_balanced_or_witness` analysis.
* Identified obstruction B (empty bands at sub-poset descent)
  via partial implementation of the F3 step.
* Verified `Case2FKGSubClaim L` is provably false (K=2 N-poset
  counterexample) via `path-c-cleanup-roadmap.md` §5.

**No Lean source committed.** `Case3Witness.{u}` def is unchanged.
No new axioms introduced. No `sorry` introduced. The mail-check
schedule (step 2 of polecat protocol) is the only background
artifact.

---

## §3 — Resolution paths (PM/Daniel decision)

### §3.a — Build band-compactification infrastructure

Build a `LayeredDecomposition.compactify` constructor that, given
`L : LayeredDecomposition α` and `S : Finset α`, produces
`L' : LayeredDecomposition ↥S` with `L'.K = #{k | 1 ≤ k ≤ L.K ∧
bandSize (L.restrict S) k ≥ 1}` and band map shifted accordingly.
Plus preservation lemmas: K' ≤ K, w' = w (or w' ≤ w with care),
caps preserved, Injective preserved, `forced_lt`/
`cross_band_lt_upward` preserved.

Estimated cost: 100-200 LoC for the constructor + 50-100 LoC for
preservation lemmas + integration with the F3 step. Total ~250-350
LoC. Combined with obstruction A's Candidate A'' tightening
(20-40 LoC), the overall delta is ~270-400 LoC — at or above the
ticket's 400k-token cap.

A dedicated follow-up ticket `mg-979e-followup` (or similar)
sized at 400k-600k tokens is appropriate. Sequence: implement
compactification, then re-attempt this ticket.

### §3.b — Build a K ≥ 3 ¬InCase3Scope Bool certificate

Mirror the `option_c_K2_closure` architecture for K ≥ 3
¬InCase3Scope. Substantial new work; the catalog is much larger
than K=2's 40 classes (`k-ge-3-lift-plan.md` §3 enumerates K=4
w=1 |α|≤12, K=3 w≥2 |α|∈{8,9}, K=3 w=1 |α|∈{10,11,12}, plus
K≥5 cases).

Estimated cost: ~500-800 LoC. Out of single-polecat scope; a
multi-polecat sequence comparable to the K=2 closure arc is
appropriate.

### §3.c — Park `Case3Witness.{u}` as `def` indefinitely

Land `option_c_K2_closure` (already in tree from `mg-01ec`)
without dropping `hC3`. `Case3Witness.{u}` remains a `def`
hypothesis on the headline. The forum send (`mg-fb16`) and
Hopkins outreach (`mg-b8f9`) remain on the conditional headline.

Per `path-c-cleanup-roadmap.md` §7, this is the "option (δ) park"
position the project is currently in. mg-01ec advanced the K=2
sub-claim from "obstruction" to "closed", but the universal
discharge remains parked.

### §3.d — Compose §3.a + §3.c

Land §3.c immediately (status quo+); plan §3.a as a multi-polecat
follow-up sequence. The Option-C arc would close in two stages:
* Stage 1 (now): K=2 substantive closure (mg-01ec, landed).
* Stage 2 (later): compactification + Candidate A'' + drop hC3
  (new ticket sequence).

This preserves forward momentum without forcing this polecat to
attempt the full bundle in one session.

---

## §4 — Recommendation

**Recommend §3.d.** Land mg-01ec's K=2 closure as-is (already in
tree); file a follow-up ticket(s) for compactification +
Candidate A'' + headline rewrite. The two obstructions identified
here are mitigatable but require substantially more infrastructure
than `mg-979e`'s scope allows.

**Why not §3.a alone?** The infrastructure delta is at the
boundary of single-polecat scope. Failing to land in 400k tokens
would consume the budget without delivery.

**Why not §3.b?** A K ≥ 3 Bool certificate is more work than
compactification and doesn't obviously generalize to other
operational paths.

**Why not §3.c alone?** Leaves the project at exactly the same
"option (δ) park" position with no Option-C progress beyond
mg-01ec. The follow-up infrastructure direction (§3.a) is worth
documenting now while the analysis is fresh.

---

## §5 — Cross-references

* `mg-979e` — this work item (Option-C execution arc, sequence
  ticket 2).
* `mg-01ec` — sequence ticket 1 (K=2 substantive closure, landed
  on `option-c-execution-arc` branch as `c403216`).
* `mg-fefe` (archived) — validation arc 1.
* `docs/option-c-validation-arc-1/k-ge-3-lift-plan.md` —
  Deliverable C, the (incomplete) Candidate A' plan;
  AMBER verdict.
* `docs/option-c-validation-arc-1/signature-design.md` —
  Deliverable B; Candidate A cascade analysis.
* `docs/option-c-validation-arc-1/f1-inactive-n-core-proof.md` —
  Deliverable A; F1-inactive ⇒ N-poset-core (referenced for
  completeness; not consumed by mg-01ec or attempted here).
* `docs/option-c-execution-arc/k2-closure-status.md` — mg-01ec
  status doc.
* `docs/path-c-cleanup-roadmap.md` §5, §6, §7 — named
  obstruction (K=2 N-poset) + closure cost estimates +
  re-attempt conditions.
* `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` axiom.
* `lean/OneThird/Step8/Case3Dispatch.lean:271` —
  `case1_dispatch_balanced_or_witness` (the three-way dispatch
  surfacing the Case 2 gap).
* `lean/OneThird/Step8/Case2FKG.lean:226` —
  `case2Witness_balanced_or_strict` (Case 1 absorption).
* `lean/OneThird/Step8/Case2Rotation.lean:894` —
  `case2Witness_balanced_under_FKG` (gated on the broken
  `Case2FKGSubClaim`).
* `lean/OneThird/Step8/Case2Rotation.lean:772` —
  `Case2FKGSubClaim` (provably false structure per `mg-8f59`).
* `lean/OneThird/Step8/OptionC/K2Closure.lean:500` —
  `option_c_K2_closure` (the K=2 architecture this ticket would
  extend).
* `lean/OneThird/Step8/LayerOrdinal.lean:472` —
  `hasBalancedPair_of_layered_strongInduction_width3` (the F3
  framework analogue without caps).
* `lean/OneThird/Step8/LayerOrdinal.lean:108` —
  `OrdinalDecompOfReducible` (where the empty-band issue
  surfaces under sub-poset descent).
* `lean/OneThird/Step8/LayeredReduction.lean:203` —
  `LayeredDecomposition.restrict` (the sub-poset constructor
  that doesn't compactify K).
* `lean/OneThird/Step8/LayeredBridges.lean:181` —
  `layeredFromBridges` (the operational headline path; provides
  Injective band map but K = |α|).
* `lean/AXIOMS.md` §B —
  `case3Witness_hasBalancedPair_outOfScope` axiom audit.

---

*Filed 2026-05-05 by polecat for `mg-979e`. Trip-wires 1 + 5
fire per the polecat-instruction. PM mail follows.*
