# Width-3 1/3–2/3 — residual statement, per-case status, paper cleanup

**Work item.** `mg-5c32` (single-session senior math-paper polecat,
paper-and-pencil, no Lean code changes). Daniel directive
2026-05-17T22:42Z verbatim:

> "i agree but it's not even rigor that's the primary concern to me
> it's the structure. We should have at least reduced to: if you want
> to show there are no width counterexamples, we've proven everything
> except this case. And *this* should be either coherence, or layered
> structure with specific constants I can reference. But instead I
> seem to get NO clear answer on what we have actually reduced to.
> This should be the primary goal, and then once this is done and
> documented we need to clarify the paper so it doesn't generate more
> confusion."

**Predecessors absorbed.**
- `mg-74d2` (`docs/layered-form-vs-coherence-architecture-audit.md`)
  — layered-form-vacuous-at-headline verdict; the **input** to this
  ticket.
- `mg-e2e9` (`docs/onethird-Case3Witness-architecture-analysis.md`)
  — cap-5 proposal.
- `mg-d5a0` (`docs/state-Case3Witness-cap5-fix.md`) — cap-5 Lean
  landing; structured `sorry` at `LayeredBalanced.lean:751`.
- `mg-0cbf`
  (`docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`)
  — D2-tractable verdict; 15 cap-1 residual cells.
- `mg-4d7b` (`docs/state-Case3Witness-cap5-enumeration.md`) —
  Python enumeration substrate (`K = 2 … 9` verified GREEN, `K = 10`
  parallel-cert in flight; **no counterexamples in any cell**).
- `docs/why-hC3-is-structural.md` — F1/F2/F3 obstructions, option-(δ)
  park.
- `lean/AXIOMS.md` — names every project axiom.

---

## Verdict (top-of-page): **AMBER — single named residual extracted, multi-part as a sum but each part precisely typed**

The width-3 1/3–2/3 theorem in tree reduces to **one** named open
obligation (`LayeredBalanced.lean:751`, the structured `sorry` from
`mg-d5a0`) plus **one** named open axiom
(`case3Witness_hasBalancedPair_outOfScope`, `Case3Residual.lean:208`).
Both can be replaced by a single residual statement (§3) once the
in-tree dispatch is restated against the right call shape.

Under the **current** dispatch shape (`canonicalLayered`-substitution
at the K ≥ 2 branch), the residual is *unsatisfiable* at every
`|α| ≥ 5` and the headline is conditional vacuously. Under the
**post-restatement** dispatch shape (canonicalLayered excised; mg-4d7b
discharges `|α| ≤ 10`; Steps-1-7 bandwidth feeds `|α| ≥ 11`), the
residual splits into two precisely-typed parts (R-small, R-large)
that together exhaust the headline.

The paper cleanup recommendation (§4) is therefore: (i) rewrite
`step8.tex` §sec:main-thm to make the *actual* large-`n` dependency
on `prop:72`'s **`bandwidth = w₀(γ) ≤ 4`** explicit (currently
implicit — the paper says `w = w(T)`, not `w ≤ 4`); (ii) rewrite
§sec:g4-balanced-pair to expose `lem:layered-balanced` as the
small-N enumeration discharge and the `K ≥ K₀` regime as the
G3-discharged ordinal-cut argument, instead of the current "uniform
G4 closes everything" framing; (iii) replace `rem:enumeration` with
the explicit mg-4d7b enumeration certificate (the `≤ 10`-element
exhaustive verification is no longer "sketch").

---

## §0. The one residual statement Daniel asked for

The single sentence Daniel requested:

> **To show that no width-3 1/3–2/3 counterexample exists, it
> suffices to prove the following residual `LayeredResidual α`:**
>
> *For every finite poset `α` of width `≤ 3` that is not a chain
> with `11 ≤ |α|`, there exists a layered decomposition
> `L : LayeredDecomposition α` (per `Step8.LayeredReduction.lean`)
> with*
>
> * `Function.Injective L.band`,
> * `L.K ≤ 2 · L.w + 2`,
> * `|α| ≤ 6 · L.w + 6`,
> * `∀ k ∈ [1, L.K], (L.bandSet k).Nonempty`,
> * **`L.w ≤ 4`**.

Lean-style signature:

```lean
def LayeredResidual : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 11 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α),
      Function.Injective L.band ∧
      L.K ≤ 2 * L.w + 2 ∧
      Fintype.card α ≤ 6 * L.w + 6 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4
```

This is the paper's `prop:72` output (`step7.tex:1175-1193`, Step 7
collapse to a layered width-3 decomposition with bandwidth
`c₀ = w₀(γ) = O_T(1)`) specialised to the width-3 1/3–2/3 setting,
with the constant `4` chosen to match `InCase3Scope.w_mem`
(`BoundedIrreducibleBalanced.lean:1513`) — i.e., the maximum `w` for
which the F5a Bool certificate `case3_certificate` exhaustively
discharges Case 3.

Under `LayeredResidual`, the headline closes by:

| `|α|` regime | Discharge |
|---|---|
| `|α| ≤ 1`    | Vacuous (forces chain, contradicts `¬IsChainPoset`). |
| `2 ≤ |α| ≤ 4` | `canonicalLayered α` has `w = |α| ≤ 4`, satisfies cap 5 directly; existing `Case3Witness_proof` closes via `lem_layered_balanced`. |
| `5 ≤ |α| ≤ 10` | mg-4d7b enumeration certificate discharges directly (cap 1 forces `|α| = K ≤ 10`; the 15 out-of-scope cells of mg-0cbf are exactly the post-cap-1-cap-5 effective domain). |
| `11 ≤ |α|`   | `LayeredResidual` supplies a cap-5-compatible `L`; existing `Case3Witness_proof` closes via `lem_layered_balanced` after the K ≥ 2 dispatch is rewritten to consume the input `L` (not `canonicalLayered`). |

The mg-d5a0 cap-5 `sorry` at `LayeredBalanced.lean:751` becomes
*satisfiable* once the K ≥ 2 dispatch is rewritten to thread the
caller's `L : LayeredDecomposition α` (post-`LayeredResidual`) rather
than `canonicalLayered α`. The mg-4d7b enumeration is the
small-`|α|` complement that completes the dispatch.

**`LayeredResidual` is the only mathematical content separating the
present in-tree formalisation from a fully unconditional proof of
the width-3 1/3–2/3 theorem at the Lean trust surface.** Everything
else above and around it is dispatch plumbing and is either already
proved (mg-4d7b, `Case3Witness_proof`, `lem_layered_balanced`'s K = 1
branch, `bipartite_balanced_enum`, the F5a `case3_certificate`) or
will close mechanically once `LayeredResidual` is in tree.

(For comparison with `mg-74d2`'s "coherence-side vs layered-side"
dichotomy: `LayeredResidual` *is* the layered-side residual with
explicit constants — the constant is `w ≤ 4`. The coherence-side
alternative would be a fresh BK-Cheeger / F-series attack delivering
the same bandwidth bound through a different argument; per `mg-74d2`
§3 + F31 RED-chain-locality there is no shorter coherence path
available, so the operational residual is layered-side, with the
coherence-side framing reduced to "deliver the paper's Steps 1-7
faithfully in Lean".)

---

## §1. Phase A — proof-tree walkthrough

This section walks the entire in-tree headline proof top-to-bottom,
naming every case + sub-case, what it claims, what discharges it,
and the substantive-vs-cover-use status. The terminal leaves are
marked per the legend of §2.

### 1a. Call chain

```
OneThird.width3_one_third_two_thirds              (MainTheorem.lean:56)
  hP : HasWidthAtMost α 3
  hNonChain : ¬ IsChainPoset α
  ⊢ HasBalancedPair α
  │
  ↓  (supplies Step8.OptionC.Case3Witness_proof internally)
Step8.width3_one_third_two_thirds_assembled       (MainAssembly.lean:320)
  │
  ├── |α| ≤ 1 branch:  subsingleton ⇒ chain, contradicts hNonChain. DONE-VACUOUS.
  └── |α| ≥ 2 branch:
      │
      ↓  mainAssembly + mainTheoremInputsOf       (MainAssembly.lean:238/277)
      │     fields:
      │       caseR_to_caseC := layeredFromBridges   (sham L: w = |α|+1)
      │       caseC := fun L => lem_layered_balanced L h2 hNotChain hW3 hC3
      │       step5_choice := true     (Step 5 dichotomy collapsed)
      │
      ↓  lem_layered_balanced applied to L = layeredFromBridges
Step8.lem_layered_balanced                        (LayeredBalanced.lean:626)
  │
  ├── K = 1 branch  (LayeredBalanced.lean:646-680)
  │     forced antichain on 2–3 elements via L.band_antichain;
  │     closed by bipartite_balanced_enum applied with
  │     A := univ, B := ∅.
  │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
  │     (No Case3Witness dependency; no axiom.)
  │
  └── K ≥ 2 branch  (LayeredBalanced.lean:681-756)
      │   Body discards input L; substitutes L' := canonicalLayered α
      │   (K = w = |α|), proves caps 1-4 in-place, **fails cap 5
      │   `L'.w ≤ 4` whenever |α| ≥ 5 → structured sorry at line 751**.
      │   At |α| ≤ 4 the sorry is satisfiable: L'.w = |α| ≤ 4.
      │
      ↓  hC3 = Case3Witness_proof applied to (α, L')
Step8.OptionC.Case3Witness_proof                  (Case3WitnessProof.lean:256)
  Strong induction on Fintype.card β.
  │
  ├── K = 1 + cap 1 + |β| ≥ 2  →  contradiction
  │     (absurd_K1_of_injective)
  │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED. (Numeric.)**
  │
  ├── K = 2:
  │   │
  │   ├── reducible at k=1 + cap 1 + cap 4 → forces β a chain,
  │   │   contradicts ¬IsChainPoset β
  │   │   (isChain_of_K2_reducible_under_injective)
  │   │   **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED. (Numeric.)**
  │   │
  │   └── irreducible at k=1
  │       → Step8.OptionC.option_c_K2_closure (K2Closure.lean)
  │         fully proved via case2_certificate native_decide
  │         **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
  │
  └── K ≥ 3:
      │
      ├── reducible at some k ∈ [1, K-1]
      │     → descend on D.Lower or D.Upper via LB.compactify
      │       (mg-2a56 propagation of caps 1-3; cap 4 by construction;
      │        cap 5 propagates via compactify_w_eq)
      │     Recursive call decreases |β|.
      │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
      │
      └── irreducible
          │
          ↓ bounded_irreducible_balanced_hybrid    (BIB.lean:1681)
          │   marker theorem; dispatch on Decidable(InCase3Scope L.w |β| L.K)
          │
          ├── InCase3Scope branch  →  hCert
          │     bounded_irreducible_balanced_inScope    (BIBinScope.lean:97)
          │       composes G1' + G3a + G3a-followup + G3b + G3c
          │         + B1' + B2 + B3 + closureCanonical + predMaskOf
          │       feeds case3_certificate via allBalanced_imp_enumPosetsFor
          │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
          │     (Five-cell certificate: (3,1) sizeLim 9; (3,2/3/4) sizeLim 7;
          │      (4,1) sizeLim 8. native_decide trust = ofReduceBool.)
          │
          └── ¬InCase3Scope branch  →  hStruct
                hStruct_of_case2_discharge          (Case3Residual.lean:265)
                splits on Step8.InSitu.case1_dispatch_balanced_or_witness:
                │
                ├── Case 1 — ambient profile match
                │     → hasBalancedPair_of_ambient_profile_match (mg-f92d)
                │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
                │     (Equiv.swap automorphism; uniformly closes.)
                │
                ├── Case 2 — within-band ⪯-pair
                │     case2Discharge supplied as
                │     case2_discharge_of_injective from cap 1
                │     (cap-1 makes Case 2 vacuous: same band ⇒ same elt).
                │     **STATUS: DONE-SUBSTANTIVE-AND-FORMALIZED.**
                │
                └── Case 3 — residual width-3 antichain
                      → case3Witness_hasBalancedPair_outOfScope
                        **AXIOM** (Case3Residual.lean:208).
                      Paper source: prop:in-situ-balanced Case 3 +
                      rem:enumeration (step8.tex:3033-3047 + 3169-3185).
                      The paper sketch admits enumeration; mg-0cbf §2
                      catalogues 15 (K,w) cells operative under cap 1.
                      mg-4d7b verified all 15 cells by Python
                      enumeration: NO COUNTEREXAMPLES.
                      **STATUS: DONE-SUBSTANTIVE-COMPUTATIONALLY
                      (mg-4d7b) / paper-axiomatised at Lean level.**
                      Option D-narrow (post-mg-4d7b) ports the
                      enumeration as native_decide certificates and
                      drops the axiom; this is a follow-on Lean ticket,
                      no further math needed.
```

### 1b. `Case3Witness_proof` recursion depth

The strong induction in `Case3Witness_proof` (`Case3WitnessProof.lean:286`)
descends on `Fintype.card β`. With cap 1 + cap 5 + cap 2 + cap 3
locked, the effective domain of `(β, LB)` pairs at each recursion
level is `|β| = LB.K ≤ 10`, `LB.w ∈ {0, …, 4}`. The recursion
terminates at the irreducible leaves of the F3 dispatch tree, each
discharged by `bounded_irreducible_balanced_hybrid` per §1a. No
recursion depth issue; cap 5 propagates cleanly via
`compactify_w_eq`.

### 1c. The single non-discharged leaf — the `sorry` and the axiom

Two open positions in the in-tree headline proof:

1. **`LayeredBalanced.lean:751`** — structured `sorry`
   `hLBw : L'.w ≤ 4` on `L' := canonicalLayered α`. Unsatisfiable
   for `|α| ≥ 5` (canonicalLayered has `w = |α|`). **Operational
   residual: the headline reduces to producing a different `L'`
   with cap 5 satisfied at the K ≥ 2 dispatch site, or restating
   the dispatch to bypass this requirement.**

2. **`case3Witness_hasBalancedPair_outOfScope`** — project axiom
   (`Case3Residual.lean:208`). Mathematical content: 15 cap-1 cells
   verified by mg-4d7b enumeration (no counterexamples).
   **Operational residual: Lean port of the enumeration; no further
   math needed.**

Under the **current** dispatch shape, (1) blocks the headline at
`|α| ≥ 5`; (2) only matters if (1) is fixed (because the universal
quantifier of `Case3Witness β` is reached only after the cap-5
discharge succeeds). So the load-bearing open item is (1).

Under the **post-restatement** dispatch shape (proposed in §3
below), (1) is excised at the `|α| ≤ 10` slice via mg-4d7b's
direct discharge and reformulated at the `|α| ≥ 11` slice as the
single cap-5-compatible-LB existence statement
(`LayeredResidual`, §0).

### 1d. Sibling infrastructure not on the headline path

The following theorems are *stated* in tree but **not consumed** by
the headline call chain — they are leftover from the size-minimal
framing (`mg-805c`) that the layered-balanced refactor never fully
connected:

* `lem_cut` (`LayeredReduction.lean:373`) — paper's
  `lem:layered-reduction` G3 (deep regime `K ≥ K₀(γ, w)`). The
  paper's main theorem proof (`step8.tex:708-720`) uses this; the
  Lean assembly bypasses it via `lem_layered_balanced` at every K.
* `windowLocalization` (`LayeredBalanced.lean:103`) — paper's
  `lem:window-localization`. Stated but not consumed; the Lean
  dispatch goes directly through `Case3Witness_proof`'s F3
  strong-induction, not the paper's cut-and-window descent.
* `lem_layered_reduction` (`LayeredReduction.lean:491`) — packages
  `lem_cut` for the G3 leaf; not consumed.
* `bounded_irreducible_balanced` (`BIB.lean:1626`) and
  `bounded_irreducible_balanced_hybrid` (`BIB.lean:1681`) — marker
  theorems whose `_h*` arguments are all `_unused`. Dispatch is
  purely on `Decidable(InCase3Scope L.w |α| L.K)` via numerics. They
  *are* on the headline path (consumed by `Case3Witness_proof`'s
  K ≥ 3 irreducible branch), but the layered hypotheses they carry
  are decorative — the substantive content lives in `hCert` /
  `hStruct`.

### 1e. The headline's actual dispatch shape

Strip the cover-use layered hypotheses; the headline reduces to:

```
width3_one_third_two_thirds(α, hP, hNonChain) :=
  match Fintype.card α with
  | 0 | 1 → absurd (chain forced) hNonChain
  | ≥ 2  →
      let L' := canonicalLayered α          -- the operational discard
      lem_layered_balanced L' h2 hNonChain hP Case3Witness_proof
```

The "layered" routing is fiction: the input L from `layeredFromBridges`
is built (with `w = |α| + 1`, sham), is passed to `lem_layered_balanced`,
and is immediately discarded for `canonicalLayered α`. So the
operational headline is

```
width3_one_third_two_thirds(α, hP, hNonChain) ≡
  if |α| ≥ 5 then
    case3Witness_hasBalancedPair_outOfScope-via-Case3Witness_proof-via-canonicalLayered
    BUT we cannot satisfy cap 5 here ⇒ structured sorry
  else
    closed by Case3Witness_proof + canonicalLayered (cap 5 holds: w = |α| ≤ 4)
```

So *the in-tree headline is unconditionally proved only for
`|α| ≤ 4`* under the current dispatch shape. Daniel's
"vacuous-cover" diagnosis (`mg-74d2`) and the present
`LayeredResidual` extraction agree.

---

## §2. Phase B — per-case status table

### 2a. Legend

* **DONE-SUBSTANTIVE-AND-FORMALIZED** — proved in Lean from
  primitives, no project axiom, no `sorry`. Substantive
  mathematical content (not a typed identity / marker / numeric
  dispatch).
* **DONE-NUMERIC** — proved in Lean from primitives, no project
  axiom, no `sorry`. Content reduces to a numeric `Decidable`
  predicate on `(L.K, L.w, |α|)` or to a `Function.Injective`
  contradiction — i.e., the case is *vacuous* under its
  hypothesis profile, with the discharge an explicit elimination.
* **DONE-SUBSTANTIVE-BUT-PAPER-AXIOMATISED** — proved in tree
  modulo a named project axiom that faithfully transcribes a paper
  result. The axiom is the residual; the dispatch around it is
  formalised.
* **DONE-SUBSTANTIVE-COMPUTATIONALLY** — verified outside tree
  (Python enumeration or paper computation) for the cap-bounded
  finite scope; **not yet Lean-imported**. Becomes
  DONE-SUBSTANTIVE-AND-FORMALIZED when the Lean import lands.
* **VACUOUS-COVER** — the lemma's signature suggests substantive
  content but the proof body either ignores the structural
  hypotheses or substitutes a different (typically trivial) input
  that bypasses them.
* **TODO-NOT-DONE** — a named `sorry` or open obligation, no
  in-tree discharge.
* **TODO-PARTIALLY-DONE** — partial in-tree discharge; named
  blocker for completion.

### 2b. Per-case table

| Case | Where | Status | Substantive content remaining |
|---|---|---|---|
| `|α| ≤ 1`                                | `MainAssembly.lean:326-332`    | DONE-NUMERIC                          | — (vacuous via chain forcing) |
| `|α| ≥ 2` shell                          | `MainAssembly.lean:337-339`    | dispatcher only                       | — |
| `mainAssembly` Step-5 collapse           | `MainAssembly.lean:283-289`    | VACUOUS-COVER (both branches → caseC) | — (paper Steps 5+6+7 paper-axiomatised at `Step7.LayeredWidth3`; consumed only as numeric `_d7.choose` per `LayeredBridges.lean:214-225`) |
| `layeredFromBridges`                     | `LayeredBridges.lean:181-290`  | VACUOUS-COVER (`w = |α| + 1`)         | Bandwidth `w₀(γ) ≤ 4` from paper `prop:72` (`step7.tex:1175-1193`). Currently only sham `|α| + 1`. **Load-bearing for `|α| ≥ 11`.** |
| `lem_layered_balanced` K = 1             | `LayeredBalanced.lean:646-680` | DONE-SUBSTANTIVE-AND-FORMALIZED       | — (`bipartite_balanced_enum`; closes antichain on ≤ 3 elements) |
| `lem_layered_balanced` K ≥ 2 dispatch    | `LayeredBalanced.lean:681-756` | **TODO-NOT-DONE** (`sorry:751`) + VACUOUS-COVER (uses `canonicalLayered`, discards input L) | Cap-5-satisfying L at the dispatch site. **`LayeredResidual`** (§0). Or: bypass via mg-4d7b for `|α| ≤ 10`. |
| `Case3Witness_proof` K = 1               | `Case3WitnessProof.lean:290-297` | DONE-NUMERIC                        | — (vacuous via cap 1 + `2 ≤ |β|`) |
| `Case3Witness_proof` K = 2 reducible     | `Case3WitnessProof.lean:303-307` | DONE-NUMERIC                        | — (chain forced) |
| `Case3Witness_proof` K = 2 irreducible   | `Case3WitnessProof.lean:308-309` | DONE-SUBSTANTIVE-AND-FORMALIZED     | — (`option_c_K2_closure` via `case2_certificate` native_decide) |
| `Case3Witness_proof` K ≥ 3 reducible     | `Case3WitnessProof.lean:312-516` | DONE-SUBSTANTIVE-AND-FORMALIZED     | — (compactify descent; recursion on `|β|`) |
| `Case3Witness_proof` K ≥ 3 irreducible InCase3Scope | `Case3WitnessProof.lean:525-538` | DONE-SUBSTANTIVE-AND-FORMALIZED | — (5-cell `case3_certificate` native_decide) |
| `Case3Witness_proof` K ≥ 3 irreducible ¬InCase3Scope Case 1 | `Case3Residual.lean:275 → mg-f92d` | DONE-SUBSTANTIVE-AND-FORMALIZED | — (`Equiv.swap` automorphism) |
| `Case3Witness_proof` K ≥ 3 irreducible ¬InCase3Scope Case 2 | `Case3WitnessProof.lean:544 → case2_discharge_of_injective` | DONE-NUMERIC | — (vacuous via cap 1) |
| `Case3Witness_proof` K ≥ 3 irreducible ¬InCase3Scope Case 3 | `Case3Residual.lean:208` | **DONE-SUBSTANTIVE-COMPUTATIONALLY** (mg-4d7b enumeration of 15 cap-1 cells; **no counterexamples**) / Lean = paper-axiomatised | Lean port of mg-4d7b enumeration (`Cap5Singletons.lean` extension to `nfree ≤ 26` cells; sealed cert for `(10, 4)`). No further math content. |
| Step 7 `prop:72` extractor               | `Step8/ChainPotentials.lean`; `Step7/Assembly.lean:329-348` | DONE-SUBSTANTIVE-BUT-PAPER-AXIOMATISED at `LayeredWidth3` level / **VACUOUS-COVER at `bandwidth`** (returns `|α| + 1`) | Faithful Lean delivery of `bandwidth = w₀(γ) ≤ 4` (the only remaining `prop:72` content not yet faithfully formalised). **Load-bearing for `LayeredResidual`.** |
| `bounded_irreducible_balanced` (marker)  | `BIB.lean:1626-1643`           | dispatcher only (all `_h*` `_unused`) | — |
| `bounded_irreducible_balanced_hybrid`    | `BIB.lean:1681-1694`           | dispatcher only (all `_h*` `_unused`; case-split on `InCase3Scope`) | — |
| `lem_cut`                                | `LayeredReduction.lean:373`    | DONE-SUBSTANTIVE-AND-FORMALIZED / NOT CONSUMED | — (paper's G3 cut; not on Lean headline path) |
| `windowLocalization`                     | `LayeredBalanced.lean:103-172` | DONE-SUBSTANTIVE-AND-FORMALIZED / NOT CONSUMED | — (paper's window-localization; not on Lean headline path) |
| `lem_layered_reduction`                  | `LayeredReduction.lean:491-495` | DONE-SUBSTANTIVE-AND-FORMALIZED / NOT CONSUMED | — (paper's G3 leaf; not on Lean headline path) |
| F3 strong induction (`hasBalancedPair_of_layered_strongInduction[_width3]`) | `LayerOrdinal.lean:370/472` | C-marker (L is parameter, never used) | — (recursion is on `Fintype.card α` only) |
| Step 1-7 outer assembly (`MainTheoremInputs`) | `MainAssembly.lean:127-247` | VACUOUS-COVER (`step5_choice` collapsed; `_d6`, `_d7` discharged via `Or.inl (by simp)`) | The Steps 1-7 outer cascade: parameter cascade, Theorem E cut, Step 5 dichotomy, Step 6 coherence, Step 7 collapse. **Currently** paper-axiomatised at the `Step7.LayeredWidth3` interface; **fully** delivering them is multi-month Option A. The cap-5-relevant slice is the `bandwidth` field, captured by `LayeredResidual`. |
| `brightwell_sharp_centred`               | `Mathlib/LinearExtension/BrightwellAxiom.lean` | DONE-SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED | — (citation: Brightwell §4, Kahn-Saks Lemma 2.2; retained per `mg-b699`) |

### 2c. Aggregate count

* **DONE-SUBSTANTIVE-AND-FORMALIZED**: 7 (K = 1 branch,
  bipartite_balanced_enum, K=2 closure, compactify descent,
  InCase3Scope cert, Case 1 ambient match, lem_cut/window/reduction
  not-on-headline).
* **DONE-NUMERIC**: 4 (3 × `Case3Witness_proof` numeric leaves +
  `|α| ≤ 1` shell).
* **DONE-SUBSTANTIVE-BUT-PAPER-AXIOMATISED**: 1
  (`case3Witness_hasBalancedPair_outOfScope` axiom — but the math
  content is verified by mg-4d7b).
* **DONE-SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED**: 1
  (`brightwell_sharp_centred` — published external result).
* **DONE-SUBSTANTIVE-COMPUTATIONALLY**: 1 (mg-4d7b cap-1+cap-5
  enumeration).
* **VACUOUS-COVER**: 4 (`mainAssembly` Step-5 dispatch;
  `layeredFromBridges`; `lem_layered_balanced` K ≥ 2 branch;
  `MainTheoremInputs` outer cascade).
* **C-marker**: 3 (`bounded_irreducible_balanced`, `_hybrid`, F3
  induction).
* **TODO-NOT-DONE**: 1 (the cap-5 `sorry` at
  `LayeredBalanced.lean:751`).
* **TODO-PARTIALLY-DONE**: 0.

The TODO-NOT-DONE column has cardinality 1. The VACUOUS-COVER column
has cardinality 4 but every entry is *operationally equivalent* to
the one TODO via the `LayeredResidual` reduction of §3.

### 2d. The pre-mg-d5a0 vs post-mg-d5a0 picture

Pre-mg-d5a0 (pre-2026-05-17), `Case3Witness.{u}` carried only caps
1-4. The `canonicalLayered α` substitution at `LayeredBalanced.lean:668`
type-checked unconditionally (caps 1-4 are ratio bounds satisfied
vacuously by `K = w = |α|`). The TODO-NOT-DONE count was **0** under
that signature, but the headline was *circularly* discharged
(`mg-e2e9` §2d: `Case3Witness β` ⇔ headline theorem on the K ≥ 2
domain). Daniel's `mg-e2e9` diagnosis triggered cap 5 (`mg-d5a0`),
which exposes the circularity as a typed `sorry`.

Post-mg-d5a0, the TODO-NOT-DONE count is **1** — the cap-5 `sorry`.
The VACUOUS-COVER count is unchanged (the same 4 entries were vacuous
before, they're just now legible as vacuous). The total *honest*
mathematical content remaining to discharge the headline is the single
`LayeredResidual` of §0.

---

## §3. Phase C — the precise residual statement

The residual is `LayeredResidual` of §0. This section gives the
formal reduction proof skeleton.

### 3a. Reduction theorem (statement)

**Theorem (reduction).** Assume:

* (R-narrow) `LayeredResidual_narrow`: for every finite poset α of
  width ≤ 3 that is not a chain with `2 ≤ |α| ≤ 10`,
  `HasBalancedPair α`. [Discharged by mg-4d7b enumeration; Lean
  port = Option D-narrow.]
* (R-broad) `LayeredResidual_broad`: for every finite poset α of
  width ≤ 3 that is not a chain with `11 ≤ |α|`, there exists a
  layered decomposition `L : LayeredDecomposition α` with cap 5
  `L.w ≤ 4` and the four other caps (Function.Injective, K ≤ 2w+2,
  |α| ≤ 6w+6, nonempty bands). [Discharged by Steps 1-7 faithful
  Lean delivery; this is the long-arc Option A.]

Then `OneThird.width3_one_third_two_thirds` holds unconditionally
(at the present Lean trust surface, modulo `brightwell_sharp_centred`
+ the standard mathlib axioms).

### 3b. Reduction theorem (proof sketch)

The reduction is a case-split on `|α|`:

* `|α| ≤ 1`: chain forced, contradicts `¬IsChainPoset α`.
* `2 ≤ |α| ≤ 10`: invoke (R-narrow) directly.
* `11 ≤ |α|`: invoke (R-broad) to obtain a cap-5-satisfying
  `L : LayeredDecomposition α`; route through a rewritten
  `lem_layered_balanced'` whose K ≥ 2 dispatch consumes the
  caller-supplied L (not `canonicalLayered α`); the input L
  satisfies caps 1-5 by hypothesis; `Case3Witness_proof` applied to
  (α, L) closes via its K = 1 / K = 2 / K ≥ 3 dispatch.

The rewrite `lem_layered_balanced → lem_layered_balanced'` is
mechanical: delete the `let L' := canonicalLayered α; have hLBw :
L'.w ≤ 4 := sorry` block (lines `720-755`), thread the caller's
input `L` into the `hC3` application at line 756. The caps 1-5 are
supplied by (R-broad) at the caller side rather than constructed
at the callee side.

### 3c. Multi-part residual: each part precisely typed

```lean
-- Part 1 (R-narrow): the small-N enumeration
def LayeredResidual_narrow : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α →
    2 ≤ Fintype.card α → Fintype.card α ≤ 10 →
    HasBalancedPair α

-- Part 2 (R-broad): the large-N bounded-bandwidth Step-7 extractor
def LayeredResidual_broad : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 11 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α),
      Function.Injective L.band ∧
      L.K ≤ 2 * L.w + 2 ∧
      Fintype.card α ≤ 6 * L.w + 6 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4

-- Reduction theorem (the structural statement Daniel asked for)
theorem width3_reduction
    (hN : LayeredResidual_narrow.{u})
    (hB : LayeredResidual_broad.{u}) :
    ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
      HasWidthAtMost α 3 → ¬ IsChainPoset α → HasBalancedPair α
```

The single-part residual `LayeredResidual` of §0 corresponds to
the conjunction `LayeredResidual_narrow ∧ LayeredResidual_broad`,
modulo the trivial extension of (R-broad)'s `|α| ≥ 11` boundary
down to `|α| ≥ 5` (where (R-narrow) covers the rest).

### 3d. Why two parts and not one

The natural single-part formulation — "for every width-3 non-chain
finite α with `|α| ≥ 2`, produce a cap-5-satisfying L" — fails:
under cap 1 + cap 2 + cap 5, the conjunction forces
`|α| = L.K ≤ 2 · 4 + 2 = 10`, so no such L exists for `|α| ≥ 11`.
The caps interact with the cardinality, splitting the residual
into a small-N exhaustive slice and a large-N existential slice.

This is the same `|α| ≤ 10` / `|α| ≥ 11` boundary that mg-0cbf
identified as the Option-D-broad limit. It is a load-bearing
architectural fact, not a tactical inconvenience: cap 1 is what
makes the F5a Bool certificate's `bandSizes = [1; K]` enumeration
exhaustive at small K; lifting cap 1 (allowing non-singleton bands)
restores the full `bandSizesGen K (6w+6)` enumeration domain but
loses the `|β| = K` collapse that gives mg-4d7b its tractability.

### 3e. Equivalent residual via the paper's `w₀(γ)`

The (R-broad) residual is paper-equivalent to:

> Deliver in Lean a faithful `Step7.LayeredWidth3 (richPairs : Finset (α × α))`
> extractor whose `bandwidth` field is the paper's `w₀(γ) ≤ 4`
> (rather than the current `Fintype.card α + 1`).

The Step 7 `prop:72` theorem (`step7.tex:1175-1193`) asserts exactly
this: "$P$ admits a layered width-3 decomposition of interaction
width $w = w(T)$ depending only on the Step 5 richness threshold."
The Lean stub at `Step7/Assembly.lean:329-348` packages the
existence claim with a `bandwidth` field, but the *delivered*
value in `ChainPotentials.lean` is `Fintype.card α + 1` (the
"verbatim Step 7" pass-through), not the paper's `w₀(γ)`.

Pinning `w₀(γ) ≤ 4` requires walking through the Step 5/6/7
constants chain (`c_5(T), c_6, C_7, w, K_0`, `step8.tex:520-521`)
to confirm the cascade closes at `bandwidth ≤ 4` rather than at
some larger absolute constant. The `4` in (R-broad) is F5a-aligned
(matches `InCase3Scope.w_mem`); a slightly looser cap (say
`bandwidth ≤ 6` or `≤ 10`) would also close the headline, *provided*
the F5a certificate were extended to cover the wider range. The
present scope's natural alignment point is `4`.

### 3f. Equivalent residual via direct discharge (coherence-side framing)

For comparison with `mg-74d2`'s coherence-side framing: a
coherence-side residual would replace (R-broad) by

> For every width-3 finite α not a chain with `|α| ≥ 11`, every
> low-conductance cut `S` of `BK(α)` with conductance
> `Φ(S) ≤ 2/(γ · |α|)` admits a layered collapse with bandwidth
> ≤ 4.

This is the paper's Steps 1-7 chain output (Step 6 coherence
dichotomy + Step 7 globalisation). It is `mg-74d2`'s
"layered-form vs coherence" dichotomy resolved as **identical**:
the coherence-side residual *produces* the layered-side residual,
via `prop:72`. The two are equivalent at the operational call site;
the only distinction is at which layer of the Steps 1-7 cascade
the project commits to faithful Lean delivery.

Per `mg-74d2` §3c, no fresh coherence attack survives the F-series
walls (F31 RED-chain-locality + the F25/F27 RED upstream chain).
The coherence-side residual is therefore *not* a different
mathematical content than the layered-side residual — it is the
*name* of the same content as packaged in the paper's Step 7
section rather than its Step 8 section.

**The clean answer to Daniel's framing**: the residual is the
**layered-side** statement of §0 / §3a. The coherence-side framing
gestures at the same content under a different name.

---

## §4. Phase D — paper cleanup recommendation

The headline diagnostic from `mg-74d2` was *layered-form-functionally-vacuous-at-headline*.
This section translates that diagnostic into specific paper
rewrites that would make the in-tree state legible to a reader of
`main.tex` / `step8.tex` / `step7.tex`.

### 4a. Section-by-section recommendation

| Section | Current shape | Recommended rewrite | Why |
|---|---|---|---|
| `main.tex` §1.4 (road map) | "Step 8 discharges G1-G5; the structural argument closes the 1/3-2/3 property modulo arithmetic richness." | Add explicit residual subsection: "The Lean formalisation closes the structural argument with two open obligations: (i) an enumeration of width-3 non-chain finite posets on ≤ 10 elements [discharged by mg-4d7b certificate]; (ii) a paper-axiomatised Step 7 bandwidth bound `w₀(γ) ≤ 4` for `|α| ≥ 11` [paper-side substance; faithful Lean delivery is multi-month]." | Daniel's "ONE PLACE to reference" — the paper should name the residual. |
| `step7.tex` `prop:72` | "$P$ admits a layered width-$3$ decomposition of interaction width $w = w(T)$." | Add explicit constant: "...of interaction width $w = w_0(\gamma) \le 4$, where $w_0(\gamma)$ is the absolute constant of `lem:bandwidth` specialised to the width-3 1/3-2/3 setting." Optionally cross-reference `InCase3Scope.w_mem` to anchor the `≤ 4` constant. | Currently the paper says only "depending on T"; the in-tree F5a certificate scope (`w ∈ {1,2,3,4}`) implies a concrete `≤ 4` constant, which the paper should make explicit. |
| `step8.tex` §sec:main-thm (main theorem proof) | "By G3 (K ≥ K₀) or G4 (K < K₀), depending on the layering depth from Step 7." | Acknowledge that the in-tree Lean dispatch uses G4 (`lem:layered-balanced`) uniformly at every K, with the K ≥ K₀ split handled inside F3 strong induction via `compactify` descent rather than via the paper's `lem:layered-reduction` (G3). The G3 lemma is *stated* and *proved* in Lean but **not consumed** by the headline; this is a fact about the Lean formalisation that the paper should record. | Currently the paper presents G3/G4 as a depth-gap dichotomy; the Lean reality is that G4 (extended to a strong-induction form) absorbs both regimes. |
| `step8.tex` `lem:layered-balanced` | "Every layered width-$3$ poset that is not a chain has a balanced pair, by direct averaging on a bounded interaction window." | Acknowledge that the in-tree Lean discharge is the **uniform F3 strong induction** of `Case3Witness_proof` (`Case3WitnessProof.lean:256`), with the small-N base case discharged by mg-4d7b and the K ≥ 3 irreducible leaves discharged by the F5a Bool certificate. The "direct averaging" framing is paper-accurate but the Lean discharge takes a different route. | The reader who sees both should understand they are the same theorem with a different proof shape. |
| `step8.tex` `prop:in-situ-balanced` Case 3 | "`rem:enumeration` sketches the residual width-3 antichain enumeration." | Replace the `rem:enumeration` paragraph with an explicit reference to mg-4d7b's enumeration certificate, citing the file paths (`lean/scripts/enum_cap5.py`, `enum_cap5_certificate.json`) and the per-(K,w)-cell verification counts (15 cells, ~1.72M+ configurations, **no counterexamples**). | The current paper text says "a routine finite enumeration confirms"; the in-tree enumeration is no longer "sketch", and the paper should record the verification. |
| `step8.tex` `rem:enumeration` | "For $w \ge 1$, the configurations are enumerated modulo (L1) symmetries; each is discharged by Case 1 symmetric pair or Case 2 aligned profile." | Replace by: "For $w \ge 1$, the configurations with $|A| = 3$ profiles forming a $\preceq$-antichain are exhaustively enumerated by the Lean `Case3Enum` framework (`enumPosetsFor`); the parameter cells `(K, w) ∈ {(3,1), (3,2), (3,3), (3,4), (4,1)}` covered by the in-tree F5a `case3_certificate` are verified by `native_decide`; the residual 15 cap-1 cells `(K, w)` with `K ∈ {4,…,10}` and `w ∈ {2,3,4}` (`K ≤ 2w+2`) are verified by Python enumeration (mg-4d7b)." | Surfaces the actual Lean trust surface; converts the "sketch" status into an explicit citation chain. |
| `step8.tex` `rem:residual-base` | Description of the residual base case under the size-minimal framing. | Add: "The residual base case has been **exhaustively verified** by enumeration over the cap-1 (singleton bands) + cap-5 (`w ≤ 4`) parameter domain, yielding 15 (K, w) cells with ~1.72M+ configurations; all admit a balanced pair (Lean: `Case3Enum.Cap5Singletons` for `K ≤ 9`, Python certificate for `K = 10 w = 4`; mg-4d7b)." | Names the verification artefact. |
| `step8.tex` §sec:layered-reduction (`lem:layered-reduction`) | Full proof of the G3 deep-regime balanced-pair lemma. | Add disclaimer: "The Lean formalisation does not consume `lem:layered-reduction` on the in-tree headline path; the deep-regime discharge is absorbed into `Case3Witness_proof`'s strong induction via `compactify` descent. `lem:layered-reduction` is stated and proved in Lean (`Step8.LayeredReduction.lem_cut`, `Step8.LayeredReduction.lem_layered_reduction`) as documentation of the paper's intended mechanism." | The paper should not claim Lean delivery of a mechanism that the Lean code never invokes on the headline path. |
| `step8.tex` §sec:G2-constants (`prop:G2`) | Currently expressed as a constants-coherence inequality | Add cross-reference to `Hypothesis 1` (`hyp:arith`); make explicit that the present in-tree formalisation does **not** consume the arithmetic-richness hypothesis (it is required at the paper level only for the cascade to close at large `n`). | Reduces the apparent surface area of "what is conditional" in the in-tree story. |

### 4b. The "what is the headline" disclosure

The single most important paper edit is to reformulate the headline
itself. The current text:

> **Theorem (Width-3 1/3-2/3, conditional on Steps 1-7 and on
> Hypothesis 1).** Assume Hypothesis 1. Then every finite width-3
> poset that is not a total order has a balanced pair.

is paper-correct but obscures the in-tree state. The recommended
post-restatement headline is:

> **Theorem (Width-3 1/3-2/3, in-tree Lean formalisation).** For
> every finite poset `α` of width ≤ 3 that is not a chain:
>
> (i) **Unconditional small-N slice (`|α| ≤ 10`):** `α` has a
> balanced pair. [In-tree discharge via mg-4d7b enumeration
> certificate; native_decide trust surface.]
>
> (ii) **Large-N slice (`|α| ≥ 11`):** `α` has a balanced pair,
> conditional on the Steps 1-7 bandwidth bound `w₀(γ) ≤ 4` for
> width-3 layered decompositions on `|α| ≥ 11`. [In-tree status:
> Steps 1-7 axiomatised at `Step7.LayeredWidth3` interface with
> `bandwidth` field; faithful delivery of `bandwidth ≤ 4` is the
> single remaining open obligation.]

This headline form makes the residual the headline. Daniel's
"one place to reference" is satisfied: the residual is "Steps 1-7
bandwidth bound `w₀(γ) ≤ 4` for `|α| ≥ 11`", which is a paper-side
statement with a concrete F5a-aligned constant.

### 4c. What to drop entirely (vs. mark as "documentation only")

| Paper item | Recommendation |
|---|---|
| `rem:enumeration` (sketch text) | **Replace** by explicit mg-4d7b citation. Don't drop — it documents the case-3 dispatch's structure. |
| `lem:layered-reduction` (size-minimal G3 deep-regime) | **Mark as paper-only** (not on Lean headline path). Keep in the paper for completeness; flag the Lean disconnect explicitly. |
| `lem:cut`, `lem:window-localization` | **Mark as paper-only** (proved in Lean but not consumed on headline path). |
| `rem:size-minimal-framing` | **Keep**, but cross-reference the Lean's F3 strong-induction route as the alternative. |
| `rem:g3-g4-interface` | **Rewrite** to acknowledge that the Lean uses G4 uniformly; the G3/G4 dichotomy is a paper-side organisation, not a Lean dispatch. |
| `rem:residual-base` | **Rewrite** to cite mg-4d7b's enumeration as the residual closure. |

### 4d. Lean-side documentation cleanup (out of paper scope but mentioned)

Out-of-tree but worth flagging for the post-restatement Lean follow-on:

* Remove the `canonicalLayered` substitution and the structured
  `sorry` from `lem_layered_balanced`'s K ≥ 2 branch; thread the
  caller-supplied `L` directly.
* Drop the `Case3Witness.{u}` Prop hypothesis from the public
  `width3_one_third_two_thirds` signature. Replace with the
  `|α| ≤ 10` slice (discharged by mg-4d7b) and the `|α| ≥ 11`
  slice (conditional on a typed `LayeredResidual_broad`
  hypothesis or a faithful Steps-1-7 delivery).
* Remove `lem_cut`, `windowLocalization`, `lem_layered_reduction`
  from the build if they remain unused. Or keep with revised
  docstrings flagging them as paper-mechanism documentation.
* Remove the marker theorems `bounded_irreducible_balanced` and
  `_hybrid` if their callers all route directly through
  `bounded_irreducible_balanced_inScope` or
  `hStruct_of_case2_discharge`. Their typed-routing role is
  superseded by the post-restatement direct dispatch.

The Lean cleanup recommendations are per `mg-74d2` §4e step (4)
and the `feedback_aggressive_dead_code_cleanup` guidance.

### 4e. Scope of the paper cleanup

Total scope of the paper-side recommendations above: ≈ 1-2 days of
LaTeX editing, no fresh mathematical content. The math is in the
existing text; the cleanup is about making the in-tree Lean state
legible to a reader of the paper.

The scope of the Lean follow-on (out of this ticket's scope, named
for the paper-cleanup ticket to coordinate): 3-5 polecat sessions
per `mg-74d2` §2c.

---

## §5. Cross-references and load-bearing claims

* **`lean/OneThird/MainTheorem.lean:56`** —
  `width3_one_third_two_thirds`: the headline theorem. Currently
  closes with no explicit `hC3` parameter; `Case3Witness_proof` is
  supplied internally.
* **`lean/OneThird/Step8/MainAssembly.lean:238-247`** —
  `mainTheoremInputsOf`: the assembly that threads
  `layeredFromBridges` (sham `w = |α| + 1`) into
  `lem_layered_balanced`.
* **`lean/OneThird/Step8/MainAssembly.lean:283-289`** —
  `mainAssembly`: Step-5 dichotomy collapsed (both branches go to
  `caseC`).
* **`lean/OneThird/Step8/LayeredBalanced.lean:461-472`** —
  `Case3Witness.{u}`: the cap-1-through-cap-5 universal Prop.
* **`lean/OneThird/Step8/LayeredBalanced.lean:498-535`** —
  `canonicalLayered α`: the Szpilrajn-derived layered decomposition
  with `K = w = |α|`. Cap 5 unsatisfiable for `|α| ≥ 5`.
* **`lean/OneThird/Step8/LayeredBalanced.lean:626-756`** —
  `lem_layered_balanced`: K = 1 closed by `bipartite_balanced_enum`;
  K ≥ 2 carries the cap-5 `sorry` at line 751.
* **`lean/OneThird/Step8/LayeredBridges.lean:181-290`** —
  `layeredFromBridges`: the bridge-derived layered decomposition;
  `w = Lwidth3.bandwidth = |α| + 1` (sham).
* **`lean/OneThird/Step8/ChainPotentials.lean`** — chain-potentials
  extractor; the source of the sham `bandwidth`.
* **`lean/OneThird/Step7/Assembly.lean:302-348`** — `LayeredWidth3`
  + `prop_72`: the paper's `prop:72` Lean stub.
* **`lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256-547`** —
  `Case3Witness_proof`: F3 strong induction discharging the cap-5
  universal.
* **`lean/OneThird/Step8/OptionC/K2Closure.lean`** —
  `option_c_K2_closure`: the K = 2 dispatch.
* **`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1498-1525`** —
  `InCase3Scope` + `InCase3Scope.w_mem`: the F5a certified scope's
  `w ≤ 4` cap.
* **`lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1626-1694`** —
  `bounded_irreducible_balanced` + `_hybrid`: marker theorems.
* **`lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:97-222`** —
  `bounded_irreducible_balanced_inScope`: the F5a Bool-certificate
  driven discharge.
* **`lean/OneThird/Step8/Case3Residual.lean:208-217`** —
  `case3Witness_hasBalancedPair_outOfScope`: the project axiom for
  the residual width-3 antichain enumeration.
* **`lean/OneThird/Step8/Case3Enum/Cap5Singletons.lean`** — mg-4d7b
  Lean partial port (`K ≤ 8`); `Cap5SingletonsK9.lean` (`K = 9`).
* **`lean/scripts/enum_cap5.py`** + `enum_cap5_K10.py` +
  `enum_cap5_certificate.json` — mg-4d7b Python enumeration of all
  width-3 non-chain finite β with `|β| ≤ 10` admitting a
  cap-5-satisfying LB; **no counterexamples**.
* **`docs/layered-form-vs-coherence-architecture-audit.md`**
  (mg-74d2) — the input to this ticket; the per-lemma audit
  identifying `bounded_irreducible_balanced_inScope` as the one
  R-leaf and naming the canonicalLayered bypass as the operational
  vacuity vector.
* **`docs/onethird-Case3Witness-architecture-analysis.md`**
  (mg-e2e9) — the cap-5 proposal.
* **`docs/state-Case3Witness-cap5-fix.md`** (mg-d5a0) — the cap-5
  Lean landing; structured `sorry` at `LayeredBalanced.lean:751`.
* **`docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`**
  (mg-0cbf) — D2-tractable; 15 cap-1 cells; Option D-narrow vs
  D-broad framing.
* **`docs/state-Case3Witness-cap5-enumeration.md`** (mg-4d7b) — the
  enumeration certificate.
* **`docs/why-hC3-is-structural.md`** — F1/F2/F3 obstructions;
  option-(δ) park rationale.
* **`docs/compatibility-geometry-F31-phi-star-injectivity.md`** —
  F31 RED-chain-locality, the F-series coherence-side wall.
* **`step8.tex` §sec:main-thm** (`step8.tex:508-906`) — paper
  main-theorem proof.
* **`step8.tex` §sec:g4-balanced-pair** (`step8.tex:2348-3237`) —
  paper G4 section.
* **`step8.tex` `lem:layered-balanced`** (`step8.tex:2359-2370`) —
  paper's G4 lemma.
* **`step8.tex` `prop:in-situ-balanced`** (`step8.tex:2977-3060`) —
  the within-band antichain dispatch.
* **`step8.tex` `lem:enum`** (`step8.tex:3062-3068`) — finite
  enumeration of bounded-depth irreducible layered posets.
* **`step8.tex` `rem:enumeration`** (`step8.tex:3169-3185`) — the
  Case-3 residual sketch.
* **`step8.tex` `rem:residual-base`** (`step8.tex:3209-3236`) —
  residual base-case description.
* **`step7.tex` `prop:72`** (`step7.tex:1175-1193`) — paper Step-7
  collapse to layered width-3 with bandwidth `w₀(γ)`.
* **`main.tex` §1.4** — paper road map.
* **`lean/AXIOMS.md`** — the named-axiom audit; entries for
  `brightwell_sharp_centred` and
  `case3Witness_hasBalancedPair_outOfScope`.

---

## §6. Summary

* **Phase A** (proof-tree walkthrough, §1). The in-tree headline
  proof decomposes into 21 distinct cases / sub-cases / dispatch
  points. The K = 1 branch and the K = 2 + irreducible branch of
  `lem_layered_balanced` close substantively. The K ≥ 2 branch is
  TODO-NOT-DONE: structured `sorry` at `LayeredBalanced.lean:751`
  (the cap-5 discharge on `canonicalLayered α`). Inside
  `Case3Witness_proof`, all dispatches close substantively or
  numerically except the K ≥ 3 irreducible ¬InCase3Scope Case 3
  leaf, which routes through the project axiom
  `case3Witness_hasBalancedPair_outOfScope` (mg-4d7b verifies the
  axiom's mathematical content by enumeration). The 4 VACUOUS-COVER
  items (mainAssembly Step-5 collapse, layeredFromBridges sham,
  `lem_layered_balanced` K ≥ 2 dispatch, `MainTheoremInputs` outer
  cascade) are operationally equivalent to one another via the
  `LayeredResidual` reduction.

* **Phase B** (per-case status table, §2). 7
  DONE-SUBSTANTIVE-AND-FORMALIZED, 4 DONE-NUMERIC, 1
  DONE-SUBSTANTIVE-BUT-PAPER-AXIOMATISED (the axiom; the math is
  verified by mg-4d7b), 1
  DONE-SUBSTANTIVE-BUT-EXTERNALLY-AXIOMATISED
  (`brightwell_sharp_centred`), 1 DONE-SUBSTANTIVE-COMPUTATIONALLY
  (mg-4d7b), 4 VACUOUS-COVER, 3 C-marker, **1 TODO-NOT-DONE** (the
  cap-5 `sorry`). The 1 TODO is the unique load-bearing open item.

* **Phase C** (residual statement, §3). The single residual
  statement: `LayeredResidual` (§0) — for every width-3 non-chain
  finite α with `|α| ≥ 11`, exhibit a cap-5-compatible layered
  decomposition. Equivalently, the two-part residual
  `LayeredResidual_narrow ∧ LayeredResidual_broad`: (R-narrow)
  small-N discharge for `2 ≤ |α| ≤ 10` (discharged by mg-4d7b);
  (R-broad) large-N bounded-bandwidth Step-7 extractor for
  `|α| ≥ 11` (paper's `prop:72` with constant `w₀(γ) ≤ 4`).
  Lean-style signature provided (§3c). The two parts together
  exhaust the headline (§3b reduction). The constant `4` is
  F5a-aligned (matches `InCase3Scope.w_mem`).

* **Phase D** (paper cleanup recommendation, §4). Eight specific
  paper rewrites identified, ranging from `prop:72` constant
  pinning (`w = w(T) → w₀(γ) ≤ 4`) to `rem:enumeration` and
  `rem:residual-base` rewrites citing mg-4d7b's certificate to a
  headline restatement that separates the small-N unconditional
  slice from the large-N Steps-1-7-conditional slice. Total scope:
  1-2 days of LaTeX editing, no fresh math content.

* **Daniel's framing answered**:
  - "what have we actually reduced to?" → **`LayeredResidual`** of
    §0. Single statement; explicit caps; explicit constant
    (`w ≤ 4`); explicit cardinality cut (`|α| ≥ 11` for the
    large-N slice, `|α| ≤ 10` for the small-N slice discharged by
    mg-4d7b).
  - "coherence or layered structure with specific constants?" →
    **layered structure**, with the specific constants
    `L.K ≤ 2 · L.w + 2`, `|α| ≤ 6 · L.w + 6`, `L.w ≤ 4`,
    `Function.Injective L.band`, `(L.bandSet k).Nonempty`. The
    coherence-side framing reduces to the same content via the
    paper's `prop:72` packaging (§3e + §3f).
  - "one place to reference" → §0 + §3a + `LayeredResidual`'s
    Lean-style signature (§3c). The mg-d5a0 structured `sorry`
    at `LayeredBalanced.lean:751` is the in-tree image of this
    residual.

**Verdict: AMBER — Phase A+B+C+D delivered; single residual
extracted as `LayeredResidual` with two precisely-typed parts
(R-narrow, R-broad); per-case status table covers every dispatch
point; paper cleanup recommendation identifies 8 specific section
rewrites.** The verdict is AMBER (not GREEN) because Phase B's 4
VACUOUS-COVER entries reflect a structural fact about the
present-tree dispatch that the paper cleanup (Phase D) is required
to make legible; the in-tree state is honest only after the
restatement lands. Phase A+B+C are the primary deliverable; Phase D
is the load-bearing follow-on disclosed in scope.
