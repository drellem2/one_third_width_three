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
  structured `sorry` (relocated to `MainAssembly.lean` integration
  point post-mg-234e) and one named project axiom (plus Brightwell
  is gone from the headline deps as of mg-8c72's Case3Witness_proof
  landing).
* The proof is **layered-decomposition based**, descending through
  `lem_layered_balanced` → (`Case3Witness_proof` ∘ `bounded_irreducible_balanced_hybrid`)
  with Bool-certificate leaves verified by `native_decide`.
* **mg-234e caller's-L rewire** (Option D-narrow per mg-0cbf §5e;
  spec mg-ac13 §5.4): `lem_layered_balanced` K ≥ 2 dispatch now
  takes the five `Case3Witness` cap-antecedents as explicit
  hypotheses on the caller's `L` (no more `canonicalLayered α`
  substitution), so the cap-5 sorry that lived at
  `LayeredBalanced.lean:755` is CLOSED at that site. The
  architectural gap (Steps 1–7's `w₀(γ) ≤ 4` paper-axiomatised
  delivery, mg-ac13 §5.4 forward action 5) is now correctly
  localised at `mainTheoremInputsOf.caseC_canonicalLayered` in
  `MainAssembly.lean` as a structured `sorry`, where the upstream
  `Step7.LayeredWidth3` interface is the intended source.
* The architecture has a **real substantive backbone in the
  |α| ≤ 10 slice** (F3 strong induction inside `Case3Witness_proof`
  + mg-4d7b enumeration). The **|α| ≥ 11 slice is conditional** on
  Steps 1–7's `w₀(γ) ≤ 4` bandwidth bound, which Lean does not yet
  faithfully deliver.
* **Two known historical pitfalls** (§3) — F3 conflation (mg-74d2/mg-82fc)
  and residual over-constraint (mg-5c32). Read §3 BEFORE adding API
  surface from one place to another or restating residuals from
  Case3Witness's call shape.
* **mg-5fbd S7-F bridge audit (RED, 7th vacuity discovery)**:
  the `MainAssembly.lean:265` sorry is **architecturally
  unclosable in-place**. See §3 pitfall #5 + `docs/state-S7-F-bridge-Session1.md`.
  The S7-A–E pilot grounded forms (mg-4584/9331/1069/d135/516f)
  remain valid Step 7 internal scaffolding; the closure of the
  sorry requires multi-month upstream Steps 1-6 cascade port
  plus architectural refactor of `width3_one_third_two_thirds_assembled`
  to proof-by-contradiction. Status-quo (retain the sorry with
  AXIOMS.md-analog disclosure) is the recommended forward
  action.
* **mg-0bd1 S7-F bridge Session 2 (RED, 8th vacuity discovery)
  → CORRECTED by mg-faf8**: mg-0bd1 found the FULL REFACTOR's
  pinned bridge signature (`MA-Sig §4.2 §E`, mg-a22b)
  **structurally unsatisfiable for large α** — its five-cap
  conclusion (transcribed from `Case3Witness`) forced
  `|α| ≤ 10 + C_exc T`. **mg-faf8 re-pinned the contract**: the
  bridge `lem_layered_from_step7` now emits only three caps
  (`Xexc.card ≤ C_exc T`, band-nonempty, `L.w ≤ 4`); the consumer
  is the new **Piece 6** (`lem_layered_balanced_full`, the full
  Step 8 G4), not the bounded `lem_layered_balanced`; and the
  corrected contract is satisfiability-verified
  (`docs/state-MA-Sig-Session1.md` §10, instantiated against the
  3-disjoint-chains counterexample class). mg-d8c7 is now a
  **6-piece** decomposition. See §3 pitfall #6.

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
   `LayeredBalanced.lean:626`).** Given the layered `L` plus the five
   Candidate A'' cap hypotheses (`hInj`, `hKw`, `hCardw`, `hNonempty`,
   `hLw : L.w ≤ 4`), dispatch on `L.K`:
   * `K = 1` — bands forced antichain ≤ 3 elts; close by
     `bipartite_balanced_enum`. **SUBSTANTIVE-AND-FORMALIZED.**
   * `K ≥ 2` — apply `Case3Witness_proof.{u}` (the K-strong-induction
     dispatcher) directly on the caller's `L`. **SUBSTANTIVE post-mg-234e**
     (was VACUOUS-COVER pre-mg-234e). The K ≥ 2 dispatch threads the
     caps to `hC3 α L hInj hKw hCardw hNonempty hLw …`; the cap-5
     sorry that lived at `LayeredBalanced.lean:755` is CLOSED at
     this site. The integration debt (Steps 1–7's `w₀(γ) ≤ 4`
     paper-axiomatised delivery) is now correctly localised at
     `mainTheoremInputsOf.caseC_canonicalLayered` in
     `MainAssembly.lean`. See §3 pitfall #3.
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
       (Python enumeration of ~1.72M+ configs in the cap-1
       singleton-band sub-slice, no counterexamples; partial Lean
       port at `Case3Enum/Cap5Singletons.lean`). **Cap-light
       extension by mg-be48** (`docs/state-Case3Witness-cap-light-enumeration.md`)
       extends Python enumeration to **non-singleton bands** (cap 1
       dropped, caps 2-5 + L1a retained) for cells with `nfree ≤ 25`
       (TIER A); the very densest cells (`nfree > 25`, e.g.
       K=4 w=1 `[3,3,3,3]`) remain in TIER B and rely on the
       structural argument that they are either ordinal-sum
       reducible (Case B lift) or admit a within-band symmetric
       pair (Pr = 1/2).
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
| `Step8.lem_layered_balanced` K≥2 | `LayeredBalanced.lean:681-720` | **S post-mg-234e** (caller's L directly threaded to `Case3Witness_proof` with five Candidate A'' cap hypotheses; cap-5 sorry CLOSED at this site — was V+T pre-mg-234e) |
| `Step8.mainTheoremInputsOf.caseC_canonicalLayered` | `MainAssembly.lean` (post-mg-234e) | **T** (relocated cap-5 sorry at integration point: `canonicalLayered α` has `w = |α|`, fails `L.w ≤ 4` cap; Steps 1–7 paper-axiomatised delivery is the intended source per mg-ac13 §5.4 forward action 5) |
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
| ↳ ↳ out-of-scope: Case 3 | `case3Witness_hasBalancedPair_outOfScope` (`Case3Residual.lean:208`) | **SP** (axiom faithful to `step8.tex:3033-3047` + `rem:enumeration`; math verified by mg-4d7b enumeration on 15 cells, ~1.72M+ configs in singleton-band sub-slice, **+ mg-be48 cap-light extension** to non-singleton bands within TIER A scope, NO COUNTEREXAMPLES across either) |
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

**The headline reduces to Step 8 in full + Steps 1-7 axiomatic
interface.** (mg-2970's `R1 + R2` framing SUPERSEDED by mg-ac13 — see
§3 pitfall #2 and `docs/coherence-collapse-case-extraction.md`.)
* **Step 8 (R1-equivalent)** = Lean port of paper's
  `lem:layered-balanced` (`step8.tex:2453, 3199-3253`), taking
  `(α, L)` with only `L.w ≤ 4` (no cap 1, no cap 2, no cap 3 —
  drops the call-shape caps of the existing `Case3Witness_proof.{u}`).
  Discharges `HasBalancedPair α` via the paper's strong induction on
  `|α|`. The current `Case3Witness_proof.{u}` is a *restriction* of
  this covering only the cap-1-cap-5 sub-slice (`|α| ≤ 10` AND admits
  singleton-band bandwidth-`≤ 4` L). **This IS the entire Step 8
  engineering target — NOT a narrow residual.**
* **Steps 1-7 (R2-equivalent, AXIOMATIC interface)** = paper's
  `prop:72` (`step7.tex:1173`) plus the upstream cascade. Delivers
  `L : LayeredDecomposition α` with `L.w ≤ w₀(γ) ≤ 4` *for α arising
  as a minimal γ-counterexample in the (R)+(coherent) regime*. The
  current Lean tree axiomatises this at `Step7.LayeredWidth3`
  (`Step7/Assembly.lean:302-348`). **NOT a free-standing existence
  claim over all width-3 non-chain α** — see pitfall #2 below for
  why mg-2970's universal-quantifier R2 is false.
* See `docs/coherence-collapse-case-extraction.md` (mg-ac13) for
  the structural extraction of the "narrower property" delivered by
  the coherence-collapse case, the 3-disjoint-chains counterexample
  refuting mg-2970 R2 in its full cap-light form, and the
  proof-technique known-ness verdict.

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

### Pitfall #2 — Don't transcribe Case3Witness's caps as the residual; don't quantify R2's `∃ L` universally over width-3 non-chain α

`Case3Witness.{u}` (`LayeredBalanced.lean:461`) carries five caps
(see §1). They are an **API surface** of the universal statement
`Case3Witness_proof` discharges, **not** the right shape for the
residual the headline reduces to.

**Three historical over-claims to avoid** (mg-5c32 hit the first
two; mg-2970 corrected those but introduced a third; mg-ac13 closes
the third — see `docs/coherence-collapse-case-extraction.md`):

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
   3-antichain`, `|α| = 6`, minimum singleton-band bandwidth = 5,
   but admits w=0 L with two size-3 bands), mg-4d7b's enumeration
   does not cover α even though α has a balanced pair (here
   `(a₁, a₂)` are symmetric, `Pr = 1/2`).

3. **Quantifying R2's `∃ L with L.w ≤ 4` universally over width-3
   non-chain α gives a FALSE statement.** Counterexample (mg-ac13
   §3): `α =` 3 disjoint chains of length 10 (|α| = 30, width 3,
   non-chain). Every layered decomposition of this α has bandwidth
   ≥ 9 (each chain spans 10 distinct band indices by (L1)+(L4),
   and cross-chain incomparable pairs force `|band(x) − band(y)|
   ≤ w` by (L3), giving `w ≥ 9`). So `∀ width-3 non-chain α, ∃ L
   with L.w ≤ 4` is FALSE. The proper Lean shape for "Steps 1-7's
   bandwidth bound" is the **axiomatic interface**
   `Step7.LayeredWidth3` (`Step7/Assembly.lean:302-348`), which
   only applies to α that arise as minimal γ-counterexamples in the
   (R)+(coherent) regime — not to all width-3 non-chain α. **Do
   not chase R2 as a free-standing universal-existence Lean lemma;
   it is false in that form.**

The **right framing is**:

* **Step 8** = Lean port of `lem:layered-balanced` (`step8.tex:2453`):
  `∀ (α, L) with HasWidthAtMost α 3 ∧ ¬IsChainPoset α ∧ 2 ≤ |α| ∧
  L.w ≤ 4, HasBalancedPair α`. This IS the entire engineering target
  (Daniel's "R1 is the entire conjecture" complaint is structurally
  correct — see mg-ac13 §5.1). Proof-technique is known
  (paper-proved strong induction + cited FKG + finite enumeration
  base case); the in-tree gap is engineering, not math.
* **Steps 1-7** = paper-axiomatised `Step7.LayeredWidth3` interface,
  delivering `L : LayeredDecomposition α` with `L.w ≤ 4` for α
  arising as a minimal γ-counterexample in the (R)+(coherent)
  regime. **Not** universally quantified over width-3 non-chain α.

**Before stating "the residual is X", do three checks:**
1. **Satisfiability under caps.** Is X satisfiable at the headline's
   full `|α|` range under all the caps you wrote down? If not,
   you've stapled API hypotheses to a residual that should drop
   some (pitfall #1).
2. **Discharge-coverage of cited artefacts.** If you cite an
   existing artefact (mg-4d7b, `case3_certificate`, …) as the
   discharge, verify that artefact's actual scope matches your
   residual's stated scope. mg-4d7b ≠ "all width-3 non-chain α
   with `|α| ≤ 10`" (pitfall #2).
3. **Universal-quantifier truthfulness.** If your residual quantifies
   universally over width-3 non-chain α with an `∃ L` conclusion,
   construct an explicit counterexample to refute it before
   accepting the form. mg-ac13 §3 builds 3-disjoint-chains-of-10
   as the refutation of mg-2970 R2 (pitfall #2.3).

### Pitfall #3 — `canonicalLayered α` substitution (CLOSED at K≥2 dispatch as of mg-234e; gap relocated to integration point)

**Status post-mg-234e:** `lem_layered_balanced` K ≥ 2 branch
(`LayeredBalanced.lean:681-720`) **now consumes the caller's `L`
directly** with the five `Case3Witness` cap-antecedents
(`hInj`, `hKw`, `hCardw`, `hNonempty`, `hLw : L.w ≤ 4`) passed as
explicit hypotheses. The cap-5 sorry that lived at
`LayeredBalanced.lean:755` is CLOSED at that site.

**The architectural gap moved up, not away.** The integration point
`mainTheoremInputsOf.caseC_canonicalLayered` in `MainAssembly.lean`
still uses `canonicalLayered α` (`K = w = |α|`) to derive caps 1–4
cleanly, and admits cap 5 (`L.w ≤ 4`) as a structured `sorry` —
the Steps 1–7 paper-axiomatised delivery gap, per mg-ac13 §5.4
forward action 5. This is the *correct* localisation: the missing
piece is "Steps 1–7's `prop:72 + rem:w0-constant` cascade
delivering an `L : LayeredDecomposition α` with `L.w ≤ 4` for α
arising as a minimal γ-counterexample". The `Step7.LayeredWidth3`
structure is the placeholder; faithful Lean port is multi-year
(per mg-ac13 §5.3 Daniel "shouldn't even go there yet").

**Pre-mg-234e history.** Prior to mg-234e, the K ≥ 2 branch
discarded the caller's `L` and substituted `canonicalLayered α`
internally, hiding the cap-5 gap inside the dispatch as a
structured `sorry` at `LayeredBalanced.lean:755`. Operationally
this meant: anything the headline appeared to "buy" by threading
an L through the layered API was **fiction at the K≥2 call site**.
Per mg-74d2 §1, the only place layered structure is genuinely
consumed downstream is the F5a Bool-certificate encoding leaf
(`bounded_irreducible_balanced_inScope` via `cross_band_lt_upward`
for `predMaskOf` upper-triangularity) — and that's an encoding
artefact, not a structural insight about α.

**Practical implication.** If a ticket says "use L's bandwidth to
discharge X at the headline," the K ≥ 2 dispatch NOW consumes L
honestly; the work is to supply an `L` with `L.w ≤ 4` at
`mainTheoremInputsOf.caseC_canonicalLayered`. The intended source
is the `Step7.LayeredWidth3` paper-axiom interface; the in-tree
`canonicalLayered α` placeholder fails cap 5 by design.

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

### Pitfall #5 — The `caseC_canonicalLayered` cap-5 sorry is not closable in-place (mg-5fbd, 7th vacuity discovery)

**Status post-mg-5fbd:** The cap-5 sorry at
`MainAssembly.lean:265` (relocated from `LayeredBalanced.lean:755`
by mg-234e per pitfall #3) is **architecturally unclosable** by any
"better `L`" choice. The S7-F bridge (mg-5fbd) audit confirms.
Reasons:

1. **Five-cap unsatisfiability for `|α| ≥ 11`.** `Case3Witness`'s
   caps 1+4 force singleton bands (`L.K = |α|`); cap 2 + cap 5
   force `L.K ≤ 2·4+2 = 10`. So `|α| ≥ 11` ⇒ no `L` satisfies
   all five caps. (Mirror of pitfall #2.1 at the integration site,
   not at residual-extraction.)
2. **Even within `|α| ≤ 10`, five-cap unsatisfiability for
   specific α.** Take `α = 3 disjoint chains of length 3`
   (`|α| = 9`, width 3, non-chain). cap 1 forces singletons
   (`L.K = 9`), cap 2 forces `L.w ≥ 4`, cap 5 forces `L.w = 4`,
   (L2) forces 10 ground-set pairs at band-distance ≥ 5 to be
   `<_P`-comparable, but `P` has only 9 comparable pairs (all
   within-chain). Contradiction; no `L` exists. (Specialisation
   of pitfall #2.3's 3-disjoint-chains-of-10 to `|α| ≤ 10`.)
3. **The paper's `lem:layered-from-step7` (`step8.tex:1913-2106`)
   does not claim coverage of arbitrary width-3 non-chain α.**
   It requires (a) Dilworth A ⊔ B ⊔ C input, (b) Step 5(C) or
   Step 7(ii) cascade-output hypotheses, (c) the conclusion lives
   on `P|_{X∖X^exc}` not `P`. These are paper-side inputs that
   hold only for **α arising as a minimal γ-counterexample in
   the (R)+(coherent) regime** — i.e., the paper's
   proof-by-contradiction setup.
4. **Current Lean `width3_one_third_two_thirds_assembled` is
   direct construction, not proof-by-contradiction.** No
   contradiction hypothesis is threaded through to
   `caseC_canonicalLayered`, so the bridge's input hypotheses
   cannot be derived at the call site.

**Practical implication.** Closing the `MainAssembly.lean:265`
sorry honestly requires *all three* of:

* the S7-F bridge construction itself (substantial, but not a
  blocker — would be the smaller half);
* Lean port of Steps 1-6 cascade outputs to supply the bridge's
  input hypotheses concretely (multi-month per mg-6ab8 Option A,
  6-9M tokens);
* architectural refactor of `MainAssembly.lean` from direct
  construction to proof-by-contradiction (so the cascade
  hypotheses can be derived from `¬ HasBalancedPair α`).

**This is the 7th vacuity discovery** (after mg-e2e9, mg-74d2,
mg-5c32, mg-82fc, mg-2970, mg-ac13). Forward options per
`docs/state-S7-F-bridge-Session1.md` §6: (C') status-quo
retain the sorry with documented disclosure, (B') narrow-locally-
close via a new project axiom in `AXIOMS.md`, (A') full multi-
month refactor + cascade port. Recommendation per Daniel
mg-ac13 §5.3 stance: **(C') status-quo**.

### Pitfall #6 — The FULL REFACTOR's pinned S7-F bridge signature is unsatisfiable for large α (mg-0bd1, 8th vacuity discovery)

**Status post-mg-faf8 — CORRECTED.** mg-faf8 re-pinned
`MA-Sig §4.2 §E/§G` per the recommendation below; the corrected
contract is satisfiability-verified in
`docs/state-MA-Sig-Session1.md` §10. P3/P4 Lean work may now be
dispatched against the corrected `MA-Sig §4.2`, and **Piece 6**
(the full Step 8 G4) is recorded in
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6. The
pitfall record below is **retained as an error pattern** — it is
the canonical example of a type-clean-but-unsatisfiable pinned
signature; future signature contracts must run the satisfiability
check (see the closing).

**The original defect (mg-0bd1).** The Option A' FULL REFACTOR
(mg-d8c7) pinned the S7-F bridge signature in
`docs/state-MA-Sig-Session1.md` §4.2 §E
(`lem_layered_from_step7`). That *original* pinned signature's
five-cap conclusion **could not be satisfied** for large minimal
γ-counterexamples. Full proof in
`docs/state-S7-F-bridge-Session2.md` §2:

1. The pinned `lem_layered_from_step7` conclusion is
   `∃ Xexc L, Xexc.card ≤ C_exc T ∧ [the five Case3Witness caps
   on L : LayeredDecomposition {a // a ∉ Xexc}]`.
2. cap 1 (`Function.Injective L.band`) + cap 4 (nonempty bands
   on `[1,K]`) ⇒ singleton bands ⇒ `card {a // a ∉ Xexc} = L.K`.
3. cap 2 (`L.K ≤ 2 L.w + 2`) + cap 5 (`L.w ≤ 4`) ⇒ `L.K ≤ 10`.
4. Hence `Fintype.card α ≤ 10 + Xexc.card ≤ 10 + C_exc T` — a
   fixed finite bound, since `C_exc T` is `O_T(1)`.
5. But the bridge's hypothesis `Step5R ∨ Step5C` (Step 5
   dichotomy) holds for minimal γ-counterexamples of **unbounded**
   size. So the pinned bridge is a **false** proposition, not a
   vacuous one, for every large minimal γ-counterexample.

This is **the same error as pitfall #2.1** (stapling caps 1+4+2+5
gives an unsatisfiable shape), recurring inside the MA-Sig
**pinned pseudo-Lean signature**. `MA-Sig §4.4`'s "no 8th vacuity"
audit checked only producer/consumer **type compatibility**
("5 caps match"), not pitfall #2's mandated **check #1 —
satisfiability under caps**.

**Root cause.** `lem_layered_balanced` / `Case3Witness`
(`LayeredBalanced.lean:461`) is — by its own docstring
(`LayeredBalanced.lean:447-450`: *"`|β| ≤ 30`, `K ≤ 10`"*) — the
**bounded `|β| ≤ 10` base sub-slice** of Step 8 G4, **not** the
full Step 8. The original `MA-Sig §4.2 §G` pinned it "UNCHANGED"
as the Step-8 endpoint and so had to pin its producer (the
bridge) to emit the same bounded-only five caps. The **full**
Step 8 G4 (paper `lem:layered-balanced`, statement
`step8.tex:2453-2464`, proof `3211-3266`: only `L.w ≤ 4`, strong
induction on `|β|`, no caps 1/2/3 — see pitfall #2's "right
framing") was **not in the tree** and **not one of mg-d8c7's
original 5 pieces**.

**The fix (mg-faf8).** The FULL REFACTOR gains a **6th piece** —
`lem_layered_balanced_full`, the full Step 8 G4 port (consuming
`lem_cut`, `windowLocalization`, `lem_layered_reduction`,
currently **NC**), recorded in
`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6. The S7-F
bridge is re-pinned (`MA-Sig §4.2 §E`) to emit only the three
satisfiable caps — `Xexc.card ≤ C_exc T`, band-nonempty,
`L.w ≤ 4` — dropping caps 1/2/3, and to feed Piece 6 rather than
the bounded `lem_layered_balanced`. The paper
`lem:layered-from-step7` and `lem:layered-balanced` are both
sound; only the original MA-Sig signature *shape* was wrong, and
it is now fixed. `MA-Sig §4.4` is also re-pinned: it now runs a
satisfiability check (check (B)), not type-compatibility alone.

**Standing lesson.** This was the **8th vacuity discovery**
(after mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13,
mg-5fbd). It recurred because an audit checked types only. When
pinning or consuming any `∃`-with-caps signature, run
pitfall #2's **check #1 — satisfiability under caps** — a
signature can type cleanly and still be a false proposition.
See `docs/state-MA-Sig-Session1.md` §4.4 check (B) + §10 for the
template (the corrected contract's satisfiability verification,
instantiated against the 3-disjoint-chains counterexample class).

---

## §4. Cross-reference index (terse)

**Lean (in this worktree, byte-current at commit time of this file):**

* Headline + assembly: `MainTheorem.lean:56`,
  `MainAssembly.lean:238/277/320`.
* `lem_layered_balanced` + `canonicalLayered`:
  `LayeredBalanced.lean:498/626`. Pre-mg-234e cap-5 sorry at
  `LayeredBalanced.lean:755` is CLOSED. Relocated cap-5 sorry
  post-mg-234e at `MainAssembly.lean`
  `caseC_canonicalLayered`.
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
* S7 grounded forms (S7-pilot scaffolding, NOT on headline path
  pre-S7-F): `Step7/SignedThreshold.lean` `§7 Grounded`,
  `Step7/SignConsistency.lean` `§6 Grounded`,
  `Step7/TripleVisibility.lean` `§4 Grounded` (mg-4584, mg-9331);
  `Step7/Cocycle.lean` `§6 Grounded` (`cocycle_grounded`,
  `cocycle_grounded_good_weight_lb`),
  `Step7/Potential.lean` `§7 Grounded` (`bfsSumPot`,
  `bfsPotentialData`, `potential_grounded`,
  `lem_potential_grounded_bundled`) (mg-1069);
  `Step7/SingleThreshold.lean` `§7 Grounded`
  (`fiberThresholdDataOfBFS`, `single_c_grounded`,
  `lem_single_c_grounded_bundled`),
  `Step7/GiantComponent.lean` (full file:
  `BipartiteRichness`, `degB_sum_split_bound`,
  `commonB_neighbour_of_rich_rows`, `endpoint_walk3`,
  `lem_giant_component_grounded`,
  `lem_giant_component_grounded_bundled`) (mg-d135);
  `Step7/Prop71_Prop72_LemBandwidth.lean` (full file:
  `prop_71_grounded`, `prop_71_grounded_good_weight_lb`,
  `prop_72_grounded`, `lem_bandwidth_le_four`,
  `lem_bandwidth_le_four_bundled`,
  `prop71_prop72_lemBandwidth_grounded`) (mg-516f). All produce
  cleared-denominator `(1 − o(1))`-fraction bounds taking
  upstream Step 2 / Step 5 / Step 6 Lean outputs as concrete
  input. The S7-E `lem_bandwidth_le_four_bundled` ships the
  **load-bearing `bandwidth ≤ 4`** for S7-F bridge consumption
  (per mg-6ab8 §7.1 spec; instantiates abstract `prop_72` at
  `c₀ := 4`, paper `rem:w0-constant`).

**Paper.** `main.tex` §1.4 road map; `step7.tex:1175-1193`
(`prop:72`); `step8.tex:2404-2418` (`lem:ordinal-factorisation`);
`step8.tex:2965-2970` (`prop:in-situ-balanced`); `step8.tex:3033-3047`
(Case 3 residual sketch); `step8.tex:3071-3124` (paper's F3
`lem:layered-balanced` proof); `step8.tex:3157-3173`
(`rem:enumeration` — the sketch the residual axiom transcribes);
`step8.tex:3194-3236` (`rem:residual-base`).

**Predecessor audits and state docs (read in order of relevance):**

* `docs/coherence-collapse-case-extraction.md` (mg-ac13) — paper-first
  extraction of the "narrower property" delivered by the coherence-collapse
  case; technique-known verdict; 3-disjoint-chains counterexample
  refuting mg-2970 R2's universal-existence form. **SUPERSEDES
  mg-2970's `R1+R2` framing.**
* `docs/onethird-proof-outline-audit.md` (mg-82fc) — per-step proof-tree
  tag table; the **most thorough** source for the §2 table here.
* `docs/width3-residual-statement.md` (mg-2970) — `R1_paper_faithful +
  R2_exists_bounded_bandwidth` re-extraction. **SUPERSEDED by mg-ac13:
  R1 IS Step 8 in full (not a narrow residual); R2 in its universal-∃
  form is FALSE (mg-ac13 §3 counterexample).** Retain for cross-reference
  to its corrections of mg-5c32, not as the headline residual statement.
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
  enumeration certificate; per-(K,w) cell counts (singleton-band
  sub-slice).
* `docs/state-Case3Witness-cap-light-enumeration.md` (mg-be48) —
  cap-light extension: non-singleton-band enumeration per
  `(K, w, band-sizes)` cell; structural argument for TIER B
  (`nfree > 25`) cells.
* `docs/state-S7-A-G1-G2-Session1.md` (mg-4584) — S7 pilot first
  execution sub-arc; `signed_threshold_grounded` (G1) and grounded
  sign-consistency (G2) wired to Step 2 staircase + Step 6
  `cor_pointwise`.
* `docs/state-S7-B-G3-Session1.md` (mg-9331) — S7 pilot second
  execution sub-arc; `triple_visibility_grounded` (G3) wired to
  Step 5 second-moment + Jensen-for-ℕ.
* `docs/state-S7-C-G4-G5-Session1.md` (mg-1069) — S7 pilot third
  execution sub-arc; `cocycle_grounded` (G4) +
  `potential_grounded` / `lem_potential_grounded_bundled` (G5)
  wired to S7-A signed-threshold + S7-B triple-visibility outputs.
  `bfsSumPot` BFS-spanning-tree potential construction is concrete
  (`pot z := ∑ e ∈ path z, signedWeight e`).
* `docs/state-S7-D-G6-G9-Session1.md` (mg-d135) — S7 pilot fourth
  execution sub-arc; `single_c_grounded` (G6) +
  `lem_giant_component_grounded` (G9) wired to S7-C
  `bfsPotentialData` and the bipartite-richness reverse-Markov
  + diameter-3 closure (`Pair := A × B` specialisation;
  `BipartiteRichness` bundle).
* `docs/state-S7-E-prop71-prop72-Session1.md` (mg-516f) — S7 pilot
  fifth execution sub-arc; `prop_71_grounded` + `prop_72_grounded`
  + `lem_bandwidth_le_four` + `lem_bandwidth_le_four_bundled`
  wired to S7-C BFS potential + S7-D giant-component walk witness
  + Step 5 parametric var-budget / `c_T`-richness. Ships the
  **load-bearing `bandwidth ≤ 4`** result, but on the `Pair`
  space as a `LayeredWidth3 richPairs` packaging — *not* a
  `LayeredDecomposition α` on the ground set.
* `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — S7 pilot
  sixth and final execution sub-arc; **RED 7th vacuity
  discovery**. Phase D Checkpoint 3 audit + bridge call-site
  architectural pitfall (cap-5 unsatisfiability at
  `caseC_canonicalLayered` per §3 pitfall #5). Recommendation:
  Option (C') RED-STAY-PUT — retain the sorry with documented
  disclosure. No Lean changes in this session.
* `docs/state-S7-F-bridge-Session2.md` (mg-0bd1) — FULL REFACTOR
  piece 3 (S7-F bridge) execution attempt; **RED 8th vacuity
  discovery**. The MA-Sig §4.2 §E pinned bridge signature's
  five-cap conclusion is unsatisfiable for large α (§3
  pitfall #6); the 5-piece mg-d8c7 decomposition is missing the
  full Step 8 G4 port (a 6th piece). Recommendation: re-scope
  (re-pin MA-Sig §4.2, add piece 6) before any P3/P4 Lean work.
  No Lean changes in that session.
* `docs/state-MA-Sig-Session1.md` (mg-a22b, re-pinned mg-faf8) —
  the Option A' FULL REFACTOR signature contract. §4.2 §E/§G,
  §4.3, §4.4 are the pinned cascade API; **§9** records the
  mg-0bd1 8th-vacuity finding; **§10** is the mg-faf8 re-pin's
  satisfiability verification (the corrected bridge is a true,
  non-vacuous proposition, instantiated against the
  3-disjoint-chains counterexample class). The re-pin mg-0bd1
  recommended is **applied** by mg-faf8.
* `docs/OneThird-Steps-1-7-Lean-port-scoping.md` (mg-6ab8) — Steps
  1-7 multi-month Lean-port scoping; Phase E option B selected.
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
* Re-extracts the residual (mg-5c32-/mg-2970-/mg-ac13-class work) —
  §3 pitfall #2's template must be edited to match the new residual
  shape. **Daniel's "vacuity-discovery" pattern has hit 6 times as of
  mg-ac13** (mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13);
  default to skeptical paper-first reading, not API-surface
  transcription.
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
