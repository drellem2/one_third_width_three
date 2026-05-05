# mg-8c72 — Option-C Stage 2B status (Candidate A'' + `Case3Witness_proof` + headline rewrite)

**Status: GREEN.** The Candidate A'' tightening of `Case3Witness.{u}`
landed; `Case3Witness_proof` discharges the universal as a Lean
theorem; `OneThird.width3_one_third_two_thirds` is now
**hypothesis-free** (modulo `hP` and `hNonChain`, matching the
paper's `thm:main`). No new project axioms; build green; trip-wires
1, 2, 3, 4, 5, 6, 7 all clear.

This is the **substantive execution chunk** that drops `hC3` from
the project's public claim. The Option-C arc closes here.

## Deliverable

1. **`OneThird/Step8/LayeredBalanced.lean` — `Case3Witness.{u}` def
   tightening.** The universal is restricted to `LB` carrying four
   Candidate A'' antecedents:

   ```
   def Case3Witness.{u} : Prop :=
     ∀ (β : Type u) [PartialOrder β] [Fintype β] [DecidableEq β]
       (LB : Step8.LayeredDecomposition β),
       Function.Injective LB.band →                              -- NEW
       LB.K ≤ 2 * LB.w + 2 →                                     -- NEW
       Fintype.card β ≤ 6 * LB.w + 6 →                           -- NEW
       (∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty) →   -- NEW
       HasWidthAtMost β 3 →
       ¬ IsChainPoset β →
       2 ≤ Fintype.card β →
       HasBalancedPair β
   ```

   The four caps propagate through `LayeredDecomposition.compactify`
   (Stage 2A, `mg-2a56`) and are supplied trivially at the operational
   headline path (`Step8.layeredFromBridges`).

2. **`OneThird/Step8/LayeredBalanced.lean` — `canonicalLayered α`
   helper.** A Szpilrajn-derived `LayeredDecomposition α` whose four
   Candidate A'' caps are derivable in-place (band injective via the
   Szpilrajn extension, `K = w = |α|`, each band a singleton). Used
   internally by `lem_layered_balanced` to apply the universal `hC3`
   on a layered decomposition with explicit caps. The public signature
   of `lem_layered_balanced` is unchanged: the K ≥ 2 branch substitutes
   `canonicalLayered α` for the input `L` since the universal claim is
   uniform over qualifying `LB`.

3. **`OneThird/Step8/LayeredDecomposition/Compactify.lean` —
   `compactify_bandSet_nonempty`.** Every band index `k ∈ [1, K']` of
   the compactified decomposition is non-empty: `K' = compactBand L S
   L.K` counts the non-empty original bands, and
   `Nat.find`-on-the-threshold extracts the witnessing original-band
   index. This is the fourth Candidate A'' cap surviving descent. The
   lemma was added inline to Stage 2A's file rather than threaded
   through Case3WitnessProof since the proof rests on `compactBand`
   internals and `compactBand_diff_le` (already in `Compactify.lean`).

4. **`OneThird/Step8/OptionC/Case3WitnessProof.lean` —
   `Case3Witness_proof : Step8.Case3Witness.{u}`.** Strong induction
   on `Fintype.card β` with K-dispatch:

   * **K = 1**: vacuous under Injective + `2 ≤ |β|`.
   * **K = 2**: reducible-at-1 forces β to be a chain (contradicts
     `¬IsChainPoset`); irreducible applies `OptionC.option_c_K2_closure`
     (`mg-01ec` Stage 1).
   * **K ≥ 3**:
     * Reducible at some `k`: descend on the piece carrying the
       incomparable pair via `LB.compactify`; lift via
       `OrdinalDecomp.hasBalancedPair_lift_lower` /
       `_upper`.
     * Irreducible: `bounded_irreducible_balanced_hybrid` with `hCert`
       fed by `bounded_irreducible_balanced_inScope` + `case3_certificate`
       and `hStruct` fed by `hStruct_of_case2_discharge` whose Case 2
       slot is made vacuous by Injective.

5. **`OneThird/MainTheorem.lean` — `width3_one_third_two_thirds`
   drops `hC3`.** The user-facing headline takes only `hP : HasWidthAtMost
   α 3` and `hNonChain : ¬ IsChainPoset α`; the `Case3Witness` slot
   of `Step8.width3_one_third_two_thirds_assembled` is supplied
   internally by `Step8.OptionC.Case3Witness_proof`.

6. **`OneThird.lean`, `lean/PRINT_AXIOMS_OUTPUT.txt`, `lean/README.md`
   — disclosure refresh.** The root re-exports
   `OneThird.Step8.OptionC.Case3WitnessProof`; the axiom inventory
   archive records the new `#print axioms` output; the README's
   "Status" / "Axioms" sections describe the headline as
   hypothesis-free with the now-transitively-reachable
   `case3Witness_hasBalancedPair_outOfScope` axiom and the
   `native_decide` certificates.

LoC delta: roughly +600 LoC (new `OptionC/Case3WitnessProof.lean`
~430 LoC, new `Compactify.lean` non-empty-bands lemma ~70 LoC,
`canonicalLayered` helper + `Case3Witness` def tightening + headline
rewrite ~100 LoC). Within the substantive-execution chunk's scope per
`feedback_distinguish_arc_chunk_outcomes`.

## Final state

* `width3_one_third_two_thirds` is hypothesis-free (modulo `hP` and
  `hNonChain`, matching `thm:main`). ✅
* `#print axioms width3_one_third_two_thirds` =
  `[propext, Classical.choice, Quot.sound, brightwell_sharp_centred,
  case3Witness_hasBalancedPair_outOfScope,
  case3_balanced_w{1..4}._native.native_decide.ax_1_1,
  case2_certificate._native.native_decide.ax_1_1]`. **No new project
  axioms** beyond what was already in tree at end of Stage 1
  (`mg-01ec`); the `case3Witness_hasBalancedPair_outOfScope` axiom
  and the `native_decide` axioms are now transitively reachable from
  the unconditional headline (previously hidden behind the `hC3`
  hypothesis). ✅
* 0 `sorry` / 0 `admit`. ✅
* Case-2-strict residual (`mg-b666`) closed structurally via the K=2
  Bool certificate from `mg-01ec`. ✅

## Trip-wire status

| #  | Trip-wire                                                    | Status |
| -- | ------------------------------------------------------------ | ------ |
| 1  | Token overrun > 450k (150% of 300k cap)                      | clear  |
| 2  | New structural obstruction surfaces (Obstruction A'')        | clear  |
| 3  | F4-b trap reappears (Steps 5-7 fiber/coherence/global)       | clear  |
| 4  | Signature cascade > 7 MECHANICAL                             | clear  |
| 5  | K ≥ 3 leaf-closure fails to compose even with compactify     | clear  |
| 6  | `#print axioms` regresses (new project axiom added)          | clear  |
| 7  | Compactify doesn't preserve some invariant the F3 step needs | clear  |

**Trip-wire 4 specifically.** The original mg-fefe Deliverable B
estimate of 7 × MECHANICAL consumer updates was met **without** a
signature cascade through the cap parameters: by substituting
`canonicalLayered α` for the input `L` inside `lem_layered_balanced`'s
K ≥ 2 branch, the cap-evidence is constructed locally (one site)
rather than threaded through six downstream consumers. The public
signatures of `lem_layered_balanced`, `lem_layered_balanced_subtype`,
`layered_implies_balanced`, `mainTheoremInputsOf`,
`width3_one_third_two_thirds_assembled`, and
`width3_one_third_two_thirds_via_step8` are unchanged. Only the
user-facing `OneThird.width3_one_third_two_thirds` drops the `hC3`
parameter — the single intended consumer change.

**Trip-wire 6 specifically.** The headline's axiom inventory grows
from 4 axioms (`mathlib trio + brightwell_sharp_centred`) at end of
Stage 2A to 10 axioms here. The 6 new entries are
`case3Witness_hasBalancedPair_outOfScope` (existing project axiom
introduced by `mg-b846` for the `prop:in-situ-balanced` Case 3
residual; was previously hidden behind the `hC3` hypothesis on the
headline) and 5 `_native.native_decide.ax_1_1` instances (per-decision
instantiations of `Lean.ofReduceBool`; the four `case3_balanced_w*`
certificates of `Step8.Case3Enum.case3_certificate` and the K=2
`case2_certificate` of `Step8.OptionC.OptionC.K2Closure`). **No new
axiom files or declarations.** Per the work-item's
"axiom inventory unchanged from current modulo existing
`Lean.ofReduceBool`" line, the existing-axiom exposure via the
unconditional headline is the expected outcome — the project axiom
was always reachable from a complete proof of the headline.

## Architecture decisions

### Why `canonicalLayered` substitution instead of cap-threading

The Stage 2B proposal in `mg-979e` §3.d implicitly suggested threading
the new cap-parameters through the consumer cascade
(`lem_layered_balanced` → `lem_layered_balanced_subtype` →
`mainTheoremInputsOf` → assembled). This polecat investigated and
chose the alternative: keep all consumer signatures unchanged and
substitute a canonical Szpilrajn-derived layered decomposition
(`canonicalLayered α`) for the input `L` at the single site where the
Case3Witness universal is invoked (`lem_layered_balanced`'s K ≥ 2
branch).

The canonical witness has Injective band (Szpilrajn injective),
`K = w = |α|` (so the K-cap and cardinality-cap are trivial), and
each band a singleton (so non-empty bands hold). It produces the same
conclusion `HasBalancedPair α` as the input `L` would (the universal
claim is uniform over qualifying `LB`).

This decision keeps trip-wire 4 clear and shrinks the consumer-touch
to one user-facing site (`MainTheorem.width3_one_third_two_thirds`).

### Why the K = 1 case is vacuous under Injective

The Candidate A'' Injective cap forces `bandSize 1 ≤ 1` (any two
elements with band 1 are equal under `Injective`). Combined with
`2 ≤ |β|` and the K-cap forcing all elements into band 1, this
contradicts. The K = 1 dispatch is therefore a one-line `False`
elimination rather than the (otherwise needed)
`bipartite_balanced_enum` invocation.

This is a structural consequence of Candidate A''-Injective and is
why the polecat chose Injective over weaker caps (e.g.,
just `Function.Injective` on `Fin α`).

### Why the K = 2 reducible case forces a chain

Under Injective + non-empty bands at `K = 2`, each band has exactly
one element (Injective bounds size by 1, non-empty-bands forces ≥ 1).
With `LayerOrdinalReducible LB 1`, the unique `(M_1, M_2)` cross-pair
is forced into `<`. With only 2 elements in β, β is a chain —
contradicting `¬IsChainPoset`. The K = 2 reducible branch is thus
also vacuous.

### Why K ≥ 3 + irreducible needs `case3Witness_hasBalancedPair_outOfScope`

Under Injective, the Case 2 slot of `case1_dispatch_balanced_or_witness`
becomes vacuous (Case 2 posits two distinct elements with equal bands,
contradicting Injective). Case 1 (ambient profile match) is closed
constructively by `hasBalancedPair_of_case1`. **Case 3 (residual:
neither Case 1 nor Case 2)** is what `case3Witness_hasBalancedPair_outOfScope`
axiomatizes. This axiom transcribes the `rem:enumeration` sketch
(`step8.tex:3157-3173`); see `lean/AXIOMS.md` for the
faithful-transcription audit.

The Injective cap does not eliminate the Case 3 residual — it only
eliminates Case 2. The axiom is therefore essential for the K ≥ 3
out-of-scope leaf and remains in the headline's transitive reach.

## Cross-references

* `mg-8c72` — this work item.
* `mg-2a56` — Stage 2A (compactify infrastructure dependency, landed
  at `e4ffe2d`).
* `mg-01ec` — Stage 1 (K=2 substantive closure, landed at `c403216`).
* `mg-979e` (block-and-report; superseded by Stage 2 sequence).
* `mg-fefe` (validation arc, archived) — AMBER verdict §3.d origin.
* `mg-fefe` Deliverable B (`signature-design.md`) — 7-consumer
  cascade analysis (now resolved by the `canonicalLayered` substitution
  trick rather than threading caps through).
* `mg-fefe` Deliverable C (`k-ge-3-lift-plan.md`) — F3 step shape
  origin.
* `mg-cda8` — F1-F5 framing doc; this ticket completes the formal
  closure of the Option-C arc.
* `lean/AXIOMS.md` §B — `case3Witness_hasBalancedPair_outOfScope`
  axiom audit (unchanged; was already present from mg-b846).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — refreshed with the new headline
  axiom inventory.
* `lean/README.md` — Status / Axioms / hC3-retention-dropped sections
  refreshed.

---

*Filed 2026-05-05 by polecat for `mg-8c72`.*
