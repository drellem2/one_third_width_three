# OneThird width-3 1/3–2/3 — proof structure onboarding

**Audience:** every polecat dispatched on `one_third_width_three`.
**Read first; check every Lean line cited before recommending action.**
**Maintenance contract:** owner = whoever ships the next major
architectural audit, residual re-extraction, axiom land/drop, or
headline restatement. Touch this file in the same commit; don't open
a follow-on. If a section conflicts with current source, source wins
and this file is wrong — fix it.

---

## §0. Onboarding TL;DR (read even if you skim nothing else)

* The headline theorem is `OneThird.width3_one_third_two_thirds`
  (`lean/OneThird/MainTheorem.lean:56`). It is **AMBER**: one
  structured `sorry` and two project axioms, named below.
* The proof is **layered-decomposition based**, descending through
  `lem_layered_balanced` → (`Case3Witness_proof` ∘ `bounded_irreducible_balanced_hybrid`)
  with Bool-certificate leaves verified by `native_decide`.
* The architecture has a **real substantive backbone in the
  |α| ≤ 10 slice** (F3 strong induction inside `Case3Witness_proof`
  + mg-4d7b enumeration). The **|α| ≥ 11 slice is conditional** on
  Steps 1–7's `w₀(γ) ≤ 4` bandwidth bound, which Lean does not yet
  faithfully deliver.
* **Two known historical pitfalls** (§3) — F3 conflation (mg-74d2/mg-82fc)
  and residual over-constraint (mg-5c32). Read §3 BEFORE adding API
  surface from one place to another or restating residuals from
  Case3Witness's call shape.

---

## §1. Math story in one page

**Goal.** For every finite poset `α` with `width(α) ≤ 3` that is not a
chain, exhibit an incomparable pair `(u, v)` with
`1/3 ≤ Pr[u <_L v] ≤ 2/3` over uniform random linear extensions `L`
of `α`.

**Approach (paper Steps 1–8, `step1.tex`…`step8.tex`).**

1. **Steps 1–7 (paper).** Reduce to a *layered decomposition*
   `L : LayeredDecomposition α` with width-3 bands, bounded interaction
   width `w ≤ w₀(γ)` (paper `prop:72`, `step7.tex:1175-1193`), and the
   four other caps used in §2 below. **Status in Lean:** Steps 1–7
   are paper-axiomatised at the `Step7.LayeredWidth3` interface
   (`Step7/Assembly.lean:302-348`). The current chain-potentials
   extractor (`Step8/ChainPotentials.lean`) ships
   `bandwidth = |α| + 1` (sham); faithful delivery of `w₀(γ) ≤ 4` is
   the long-arc residual (R-broad below).
2. **Step 8 G4 (paper `lem:layered-balanced`, Lean `lem_layered_balanced`,
   `LayeredBalanced.lean:626`).** Given the layered `L`, dispatch on
   `L.K`:
   * `K = 1` — bands forced antichain ≤ 3 elts; close by
     `bipartite_balanced_enum`. **SUBSTANTIVE-AND-FORMALIZED.**
   * `K ≥ 2` — apply `Case3Witness_proof.{u}` (the K-strong-induction
     dispatcher). **CURRENTLY VACUOUS-COVER** because the in-tree body
     discards the caller's `L` and substitutes `canonicalLayered α`
     (`K = w = |α|`), failing cap 5 — the structured `sorry` at
     `LayeredBalanced.lean:755` (mg-d5a0). See §3 pitfall #3.
3. **Case3Witness_proof internal F3 strong induction**
   (`OptionC/Case3WitnessProof.lean:256`, `Nat.strong_induction_on`
   at line 286). Descends on `Fintype.card β`. Five caps on `LB`:
   (1) `Function.Injective LB.band`, (2) `LB.K ≤ 2·LB.w+2`, (3)
   `|β| ≤ 6·LB.w+6`, (4) nonempty bands, (5) `LB.w ≤ 4` (mg-d5a0).
   Caps 1+4 collapse bands to singletons (`K=|β|`); caps 2+5 force
   `|β| ≤ 10`. So the non-vacuous scope of `Case3Witness` is
   `|β| ≤ 10`.
4. **Within Case3Witness_proof's recursion** (K-dispatch, all
   substantive backbone in this slice):
   * `K = 1` + cap 1 + `2 ≤ |β|` → contradiction.
   * `K = 2` reducible → chain forced → contradicts `¬IsChainPoset`.
   * `K = 2` irreducible → `OptionC.option_c_K2_closure` via F5a K=2
     `case2_certificate` (`native_decide`).
   * `K ≥ 3` reducible → recurse on `D.Lower`/`D.Upper` via
     `compactify`; lift balanced pair via marginal-invariance from
     `OrdinalDecomp.hasBalancedPair_lift`
     (`Mathlib/LinearExtension/Subtype.lean:1152`) — this is paper
     `lem:ordinal-factorisation` (`step8.tex:2404-2418`). See §3
     pitfall #1.
   * `K ≥ 3` irreducible → `bounded_irreducible_balanced_hybrid` →
     branch on `Decidable(InCase3Scope L.w |β| L.K)`:
     - **in-scope** (K=3, w∈{1..4} per `sizeLimit`; K=4, w=1) →
       `bounded_irreducible_balanced_inScope` consumes
       `case3_certificate` (`Case3Enum/Certificate.lean:71`,
       `native_decide`). **SUBSTANTIVE-COMPUTATIONAL.**
     - **out-of-scope** (K∈{4 w≥2, 5..10} cells) →
       `case3Witness_hasBalancedPair_outOfScope` AXIOM
       (`Case3Residual.lean:208`). Math content **verified by mg-4d7b**
       (Python enumeration of ~1.72M+ configs, no counterexamples;
       partial Lean port at `Case3Enum/Cap5Singletons.lean`).
5. **External axioms.** `LinearExt.brightwell_sharp_centred`
   (Brightwell–Tetali sharp 1/3 lower bound; `AXIOMS.md:21`).

---

## §2. Proof tree (top-to-bottom) with status tags

**Tag legend.** **S** = substantive-and-formalized (real Lean proof).
**SC** = substantive-computational (`native_decide`/Bool cert).
**SP** = substantive-but-paper-axiomatised (project axiom faithful to
paper). **SE** = substantive-but-externally-axiomatised. **M** =
marker (typed-routing only; declared hypotheses unused or numeric).
**V** = vacuous-cover (signature suggests substance but body discards
inputs or hypothesis is structurally unreachable). **T** = TODO-sorry.
**NC** = present in tree but not consumed by the headline path.

| Node | File:Line | Tag |
|---|---|---|
| `OneThird.width3_one_third_two_thirds` | `MainTheorem.lean:56` | wrapper |
| `Step8.width3_one_third_two_thirds_assembled` | `MainAssembly.lean:320` | S (`|α|<2` vacuous vs `mainAssembly` `|α|≥2`) |
| `Step8.mainAssembly` (`step5_choice` collapse) | `MainAssembly.lean:277` | M (both branches → `caseC`) |
| `Step8.mainTheoremInputsOf` | `MainAssembly.lean:238` | S (bundle), but `caseR_to_caseC` = `layeredFromBridges` is **V** because `bandwidth = |α|+1` upstream |
| `Step8.lem_layered_balanced` K=1 | `LayeredBalanced.lean:626/646-680` | S (antichain ≤ 3 elts → `bipartite_balanced_enum`) |
| `Step8.lem_layered_balanced` K≥2 | `LayeredBalanced.lean:681-755` | **V + T** (`canonicalLayered` substitution, cap-5 `sorry` at line 755 — mg-d5a0) |
| `Step8.OptionC.Case3Witness_proof.{u}` | `OptionC/Case3WitnessProof.lean:256` | S (Nat.strong_induction on `\|β\|`) |
| ↳ K=1 base | `:290-297` (`absurd_K1_of_injective`) | S (numeric contradiction) |
| ↳ K=2 reducible | `:303-307` (`isChain_of_K2_reducible_under_injective`) | S (forces chain) |
| ↳ K=2 irreducible | `:308-309` (`OptionC.option_c_K2_closure`) | SC (F5a K=2 `case2_certificate`) |
| ↳ K≥3 reducible: ordinal-decomp + cross-pair eliminated | `:312-347` (`OrdinalDecompOfReducible`, `LayerOrdinal.lean:108`) | S |
| ↳ K≥3 reducible: recursive descent on `D.Lower`/`D.Upper` via `compactify`; 5 cap-propagation lemmas | `:350-516` (+ `LayeredDecomposition/Compactify.lean`) | S |
| ↳ K≥3 reducible: conclusion lift | `:438/:516` → `OrdinalDecomp.hasBalancedPair_lift` (`Subtype.lean:1152`) → `probLT_restrict_eq` (`:1065`) | S (paper `lem:ordinal-factorisation`; THE marginal-invariance lift — see §3 pitfall #1) |
| ↳ K≥3 irreducible: hybrid dispatch | `bounded_irreducible_balanced_hybrid` (`BoundedIrreducibleBalanced.lean:1681`) | M (pure `by_cases Decidable(InCase3Scope)`) |
| ↳ ↳ in-scope | `bounded_irreducible_balanced_inScope` (`BoundedIrreducibleBalancedInScope.lean:97`) ∘ `case3_certificate` (`Case3Enum/Certificate.lean:71`) | **S + SC** (G1'/G3a/G3b/G3c/B1'/B2/B3 bridges + 5-cell `native_decide`) |
| ↳ ↳ out-of-scope: Case 1 | `hasBalancedPair_of_ambient_profile_match` (mg-f92d) | S (`Equiv.swap` profile symmetry) |
| ↳ ↳ out-of-scope: Case 2 | `case2_discharge_of_injective` | V (cap 1 makes Case 2 unreachable — vacuous by design) |
| ↳ ↳ out-of-scope: Case 3 | `case3Witness_hasBalancedPair_outOfScope` (`Case3Residual.lean:208`) | **SP** (axiom faithful to `step8.tex:3033-3047` + `rem:enumeration`; math verified by mg-4d7b enumeration on 15 cells, ~1.72M+ configs, NO COUNTEREXAMPLES) |
| `LinearExt.brightwell_sharp_centred` | `Mathlib/LinearExtension/BrightwellAxiom.lean` | **SE** (Brightwell–Tetali) |
| `Step8.bounded_irreducible_balanced` (no `_inScope`) | `BIB.lean:1626` | M (pure identity; all `_h*` underscored) |
| `Step8.hasBalancedPair_of_layered_strongInduction[_width3]` | `LayerOrdinal.lean:370/472` | M (bare F3 framework; L unused; recursion on `Fintype.card α` only) — **NC** (not invoked on headline) |
| `Step8.lem_cut`, `Step8.windowLocalization`, `Step8.lem_layered_reduction` | `LayeredReduction.lean:373/491` + `LayeredBalanced.lean:103` | S + **NC** (paper's G3 cut-and-window infrastructure, not on Lean headline path) |
| `Cap5Singletons.case3_balanced_singletons_K{2,4..8}_*` | `Case3Enum/Cap5Singletons.lean:101+` | SC + **NC** (mg-4d7b ports; not wired into headline) |
| `Cap5SingletonsK9` | `Cap5SingletonsK9.lean` | SC + **NC** (not imported into `OneThird.lean`) |
| K=10 w=4 cap-5 cell | `lean/scripts/enum_cap5_K10_certificate.json` | external evidence (no Lean axiom) |

**Aggregate.** 17 S nodes on the headline path; 3 SC (`case3_certificate`,
F5a K=2 `case2_certificate`, K=4 w=1 sliver); 1 SP (load-bearing
on headline: the Case-3 out-of-scope axiom); 1 SE
(`brightwell_sharp_centred`); 4 M nodes (none currently load-bearing —
their `_h*` are decorative); 3 V (incl. cap-5 sorry call site); 1 T
(the cap-5 `sorry` at `LayeredBalanced.lean:755`); ≥3 NC nodes
(mg-4d7b enumeration, `lem_cut`/`windowLocalization`/`lem_layered_reduction`,
bare F3 framework).

**The headline reduces to two residuals.** Per mg-2970 (correcting
mg-5c32 — see §3 pitfall #2), the in-tree state factors as
`R1_paper_faithful ∧ R2_exists_bounded_bandwidth`:
* **R1** (paper-faithful uncapped `lem:layered-balanced`): Lean port
  of `step8.tex:3199-3253`, taking `(α, L)` with only `L.w ≤ 4` (no
  cap 1, no cap 2, no cap 3 — drops the call-shape caps of the
  existing `Case3Witness_proof.{u}`). Discharges
  `HasBalancedPair α` via the paper's strong induction on `|α|`. The
  current `Case3Witness_proof.{u}` is a *restriction* of R1 covering
  only the cap-1-cap-5 sub-slice (`|α| ≤ 10` AND admits singleton-band
  bandwidth-`≤ 4` L).
* **R2** (existence of bandwidth-`≤ 4` layered decomposition): for
  every width-3 non-chain finite α, `∃ L, L.w ≤ 4`. Discharged for
  `|α| ≤ 10` by direct construction (iterated ordinal-sum
  decomposition); for `|α| ≥ 11` by paper's `prop:72` + Steps 1-7
  (`w₀(γ) ≤ 4`).
* See `docs/width3-residual-statement.md` (mg-2970) for the full
  satisfiability proofs, Lean signatures, and a worked example of
  why the cardinality split lives inside R2's discharge (not inside
  the residual statement).

---

## §3. Known pitfalls — read before re-deriving

These are the two reference cases for "things polecats have got wrong"
plus the standing architectural trap that produced both.

### Pitfall #1 — "F3 strong induction" names two different things

Two constructs in tree are both called "F3 strong induction"; only
one is substantive, and they live in different files. **Do not
conflate.** (Mistake taxonomy from mg-74d2 confirmed/refined by
mg-82fc.)

| Construct | File:Line | Status | What it is |
|---|---|---|---|
| `hasBalancedPair_of_layered_strongInduction[_width3]` | `LayerOrdinal.lean:370/472` | **MARKER** — `L` declared, never used; recursion is on `Fintype.card α` only via an inline `hStep` hypothesis. NOT on the headline path. | Bare F3 framework template. Type-only dispatcher. |
| `Case3Witness_proof.{u}` | `OptionC/Case3WitnessProof.lean:256` (induction at `:286`) | **SUBSTANTIVE.** Its own `Nat.strong_induction_on` on `Fintype.card β` with explicit cap-propagation. NOT the bare framework. | The load-bearing F3 instance for the headline. |

The conclusion-lift in `Case3Witness_proof` K≥3 reducible branch is
**NOT** circular: it eliminates cross-pair incomparability via
`hRed`, recurses on `D.Lower`/`D.Upper` (strict descent on
`Fintype.card`), then lifts via `OrdinalDecomp.hasBalancedPair_lift`
which is paper `lem:ordinal-factorisation` (`step8.tex:2404-2418`)
delivered as `Pr[u<v]`-marginal-invariance from a genuine
`LinearExt α ≃ LinearExt Lower × LinearExt Mid × LinearExt Upper`
bijection (`Mathlib/LinearExtension/Subtype.lean:~700/1065/1152`).

**When auditing F3, ALWAYS state which of the two constructs you're
talking about** and verify it by reading the proof body, not just the
signature.

### Pitfall #2 — Don't transcribe Case3Witness's caps as the residual

`Case3Witness.{u}` (`LayeredBalanced.lean:461`) carries five caps
(see §1). They are an **API surface** of the universal statement
`Case3Witness_proof` discharges, **not** the right shape for the
residual the headline reduces to.

**Two historical over-claims to avoid** (mg-5c32 hit both; mg-2970
diagnosed and corrected — see `docs/width3-residual-statement.md`
§1):

1. **Stapling caps 1+4+2+5 together gives an unsatisfiable residual
   at `|α| ≥ 11`.** Cap 1 (`Function.Injective L.band`) + cap 4
   (nonempty bands) ⇒ singleton bands ⇒ `|α| = L.K`. Caps 2+5 ⇒
   `L.K ≤ 10`. Together: no L satisfying all five caps exists at
   `|α| ≥ 11`. mg-5c32's `LayeredResidual` (§0 single-part) AND
   `LayeredResidual_broad` (§3c two-part) both made this error.

2. **Claiming mg-4d7b enumeration discharges the `|α| ≤ 10` slice
   over-claims mg-4d7b's scope.** mg-4d7b enumerates the
   **cap-1-cap-5 sub-slice** only (β admitting a singleton-band L
   with bandwidth `≤ 4`). For width-3 non-chain α with `|α| ≤ 10`
   and *no* such L (canonical counterexample: `α = 3-antichain ⊕
   3-antichain`, `|α| = 6`, minimum singleton-band bandwidth = 5),
   mg-4d7b's enumeration does not cover α even though α has a
   balanced pair (here `(a₁, a₂)` are symmetric, `Pr = 1/2`). The
   `|α| ≤ 10` slice requires a *strict superset* of mg-4d7b's
   enumeration OR a paper-faithful uncapped `lem:layered-balanced`.

The **right residual is R1 + R2** (mg-2970 form):

```lean
def R1_paper_faithful.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : Step8.LayeredDecomposition α),
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    L.w ≤ 4 →
    HasBalancedPair α
    -- paper proof: step8.tex:3199-3253 strong induction on |α|
    -- (Case A K=1 trivial, Case B reducible IH-recurse, Case C
    -- irreducible window-localize → prop:in-situ-balanced).
    -- The current Case3Witness_proof.{u} is a restricted version
    -- (additionally requires caps 1, 2, 3, 4); R1 drops those.

def R2_exists_bounded_bandwidth.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4
    -- discharged by:
    --   |α| ≤ 10  : direct construction (Mirsky / iterated ordinal-sum)
    --   |α| ≥ 11  : paper's prop:72 + Steps 1-7 (currently sham)
```

The cardinality split lives inside R2's discharge, *not* inside the
residual statement. Caps 1, 2, 3, 4 from `Case3Witness.{u}` are
**dropped** because they are call-shape artefacts of the cap-1-aligned
F5a Bool certificate encoding, not paper-side requirements of the
bandwidth-bounded-to-balanced-pair derivation.

**Before stating "the residual is X", do both checks:**
1. **Satisfiability.** Is X satisfiable at the headline's full `|α|`
   range under all the caps you wrote down? If not, you've stapled
   API hypotheses to a residual that should drop some.
2. **Discharge-coverage.** If you cite an existing artefact (mg-4d7b,
   `case3_certificate`, …) as the discharge, verify that artefact's
   actual scope matches your residual's stated scope. mg-4d7b
   ≠ "all width-3 non-chain α with `|α| ≤ 10`".

### Pitfall #3 — `canonicalLayered α` substitution makes layered hypotheses fiction

`lem_layered_balanced` K≥2 branch (`LayeredBalanced.lean:681-755`)
**discards the caller's `L`** and substitutes
`canonicalLayered α := Szpilrajn linear extension with K = w = |α|`
(`LayeredBalanced.lean:498`). The caller-provided `L`'s bandwidth
`L.w ≤ 4` (if any) is never consumed there; cap 5 cannot be
discharged on `canonicalLayered α` for `|α| ≥ 5` → structured `sorry`
at `LayeredBalanced.lean:755`.

Operationally this means: anything the headline appears to "buy" by
threading an L through the layered API is **fiction at the K≥2 call
site** until that branch is rewritten to consume the caller's `L`.
Per mg-74d2 §1, the only place layered structure is genuinely
consumed downstream is the F5a Bool-certificate encoding leaf
(`bounded_irreducible_balanced_inScope` via `cross_band_lt_upward`
for `predMaskOf` upper-triangularity) — and that's an encoding
artefact, not a structural insight about α.

**Practical implication.** If a ticket says "use L's bandwidth to
discharge X at the headline," verify the K≥2 dispatch consumes L
(grep for `let L' := canonicalLayered`). Most likely it doesn't, and
the work is to rewrite `lem_layered_balanced` first (Option D-narrow
per mg-0cbf §5e).

### Pitfall #4 — Verify "not implemented" / "doesn't exist" claims

Source docs frequently say "we have not yet…" or "X is not in tree."
Some claims have since shipped (e.g., mg-4d7b's K=2..9 Lean ports).
Before assuming a doc's negative claim is current, grep for the
named symbol or `ls` the path. Example checks before action:

* `grep -rn 'case3_balanced_singletons_K9' lean/` — is K=9 cell ported?
* `ls lean/OneThird/Step8/Case3Enum/Cap5Singletons*.lean` — partial
  Lean port present?
* `grep -n 'sorry' lean/OneThird/Step8/LayeredBalanced.lean` — only
  the one cap-5 sorry should appear; if more, the tree has regressed.

---

## §4. Cross-reference index (terse)

**Lean (in this worktree, byte-current at commit time of this file):**

* Headline + assembly: `MainTheorem.lean:56`,
  `MainAssembly.lean:238/277/320`.
* `lem_layered_balanced` + `canonicalLayered`:
  `LayeredBalanced.lean:498/626/755`.
* `Case3Witness_proof`: `OptionC/Case3WitnessProof.lean:256/286`.
* Marker theorems: `LayerOrdinal.lean:370/472`,
  `BoundedIrreducibleBalanced.lean:1626/1681`.
* Substantive F5a leaf: `BoundedIrreducibleBalancedInScope.lean:97`.
* Bool certificates: `Case3Enum/Certificate.lean:71`,
  `Case3Enum/Cap5Singletons.lean`, `Case3Enum/Cap5SingletonsK9.lean`.
* `InCase3Scope`: `BoundedIrreducibleBalanced.lean:1498-1525`.
* Residual axiom: `Case3Residual.lean:208`.
* Lift (paper `lem:ordinal-factorisation`):
  `Mathlib/LinearExtension/Subtype.lean:1065/1152/1227`.
* Compactify (cap propagation): `LayeredDecomposition/Compactify.lean`.
* Axiom inventory: `lean/AXIOMS.md`.

**Paper.** `main.tex` §1.4 road map; `step7.tex:1175-1193`
(`prop:72`); `step8.tex:2404-2418` (`lem:ordinal-factorisation`);
`step8.tex:2965-2970` (`prop:in-situ-balanced`); `step8.tex:3033-3047`
(Case 3 residual sketch); `step8.tex:3071-3124` (paper's F3
`lem:layered-balanced` proof); `step8.tex:3157-3173`
(`rem:enumeration` — the sketch the residual axiom transcribes);
`step8.tex:3194-3236` (`rem:residual-base`).

**Predecessor audits and state docs (read in order of relevance):**

* `docs/onethird-proof-outline-audit.md` (mg-82fc) — per-step proof-tree
  tag table; the **most thorough** source for the §2 table here.
* `docs/width3-residual-statement.md` (mg-5c32) — the
  `LayeredResidual_{narrow,broad}` extraction. **The two-part split
  is the right shape — do not single-part it.**
* `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2) —
  the canonicalLayered-bypass diagnosis; per-lemma R-leaf/R-numeric/M
  audit.
* `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9) —
  cap-5 proposal.
* `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — cap-5 Lean
  landing; structured `sorry` placement.
* `docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`
  (mg-0cbf) — Option D-narrow / D-broad framing.
* `docs/state-Case3Witness-cap5-enumeration.md` (mg-4d7b) — Python
  enumeration certificate; per-(K,w) cell counts.
* `docs/why-hC3-is-structural.md` — F1/F2/F3 obstructions; option-(δ)
  park rationale.

---

## §5. Maintenance contract

This file is the **single-source-of-truth proof-tree summary** for
polecat onboarding (per Daniel directive 2026-05-18T09:37Z, work item
mg-6f04). Update it in the **same commit** as any change that:

* Lands or drops a project axiom (`AXIOMS.md` diff).
* Closes a `sorry` or introduces one (`grep -rn sorry lean/`).
* Restates the headline (`MainTheorem.lean`).
* Re-extracts the residual (mg-5c32-class work) — §3 pitfall #2's
  template must be edited to match the new residual shape.
* Rewires `lem_layered_balanced` or `mainTheoremInputsOf`
  (Option D-narrow / D-broad-class work).
* Refactors `Case3Witness` signature (caps changed) or
  `Case3Witness_proof` body.
* Discharges Steps 1–7's `w₀(γ)` faithfully.
* Surfaces a fresh pitfall worth adding to §3 — error patterns are
  more useful than success summaries.

If you're a polecat reading this and your task touches the proof
tree, **update §1 / §2 inline as you go** and commit the doc change
in the same patch as the Lean change. Don't open a follow-on ticket
to "update onboarding doc"; rot starts there.

If you find this doc is wrong, edit it directly. Source-of-truth is
the Lean tree and `step{1..8}.tex`; this doc is summary.
