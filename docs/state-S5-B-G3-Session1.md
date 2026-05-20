# State — S5-B — Session 1: Step 5 Lean port G3 — Dilworth decomposition selection

**Ticket:** mg-f268 (OneThird-S5-B: Step 5 Lean port G3 — Dilworth
decomposition selection).
**Branch:** `polecat-mg-f268`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 / §5.2
piece 1, Wave-1.
**Depends:** mg-faf8 (corrected MA-Sig signature contract — landed
a554cbb).

**Scope.** Wave-1 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition. Delivers the **operational content of GAP G3** — paper
`lem:decomp-selection` (`step5.tex:508-619`) — grounded on the concrete
ground set of a width-3 poset: the **selection of a Dilworth
decomposition `X = A ⊔ B ⊔ C` into three chains** (the three-chain
split), with non-vacuous concrete instantiation.

---

## §0. Verdict — **GREEN-S5-B-delivered**

`lean/OneThird/Step5/GroundSet.lean` (NEW, ~430 LoC) ports the
constructive heart of paper `lem:decomp-selection` grounded on the
ground set, and ships the mg-f268-mandated **non-triviality
witnesses**. `lake build OneThird` is clean (exit 0); the only
residual warnings on the new file are the `unusedDecidableInType`
linter notice on `hasChainCover_three_of_widthAtMost` (identical to
the pre-existing `Dilworth.lean:776` pattern for `hasChainCover_width`)
and one `push_neg` deprecation (identical to `Dilworth.lean:424`).

**Non-triviality bar met — no Subsingleton-on-empty baseline.** The
port instantiates non-vacuously at **two** concrete width-3 non-chain
posets:

* `Antichain3.decomp_selection_nonvacuous` — the 3-element antichain
  (`HasWidth Antichain3 3`, genuinely `¬ IsChainPoset`) decomposes
  into **three nonempty singleton chains** that partition the ground
  set, `|A| + |B| + |C| = 3`, each chain card `= 1`.
* `Antichain3.decomp_selection_groundSet_applies` — the *general* G3
  port `decomp_selection_groundSet` itself fires at `Antichain3`,
  confirming it is non-vacuously applicable, not merely type-correct.
* `Chain2Iso2.decomp_has_genuine_two_chain` — a purpose-built
  4-element width-3 non-chain poset (`0 < 1`, two isolated points)
  whose G3 decomposition genuinely contains a chain of length `≥ 2`,
  exercising the **non-singleton-chain** case of the mechanism (the
  `Antichain3` witness alone only has singleton chains).

**No vacuity-discovery surfaced.** Skeptical re-audit against
`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks — see §3
below. The port surfaced no ill-posed target and no missing mathlib
dependency: Dilworth's theorem is already in tree
(`Mathlib/Poset/Dilworth.lean`, `hasChainCover_of_hasWidth`), so the
G3 selection is a genuine, non-vacuous use of it.

---

## §1. What landed

New file `lean/OneThird/Step5/GroundSet.lean`, registered in
`lean/OneThird.lean` (import added after `OneThird.Step5.Dichotomy`).

### §1.1. The three-chain decomposition (`namespace OneThird.Step5`)

* `DilworthDecomp α` — a decomposition of `α` into three chains,
  presented as a band function `band : α → Fin 3` whose three fibers
  are chains. This is exactly the data of
  `OneThird.Mathlib.Poset.HasChainCover α 3`, packaged so the three
  chains `D.A`, `D.B`, `D.C` are named and reusable.
* `DilworthDecomp.chain` / `.A` / `.B` / `.C` — the three chains as
  `Finset α`; `mem_chain`, `coe_chain`, `chain_isChain`,
  `chain_disjoint` — the basic API.
* `DilworthDecomp.chains_cover` — `A ∪ B ∪ C = univ`: the three
  chains cover the whole ground set (the `E = ∅` content of paper G3).
* `DilworthDecomp.card_partition` — `|A| + |B| + |C| = |α|`: a genuine
  partition, losing zero elements.
* `DilworthDecomp.comparable_of_band_eq` / `incomp_band_ne` —
  same-band ⇒ comparable; incomparable ⇒ distinct bands.
* `hasChainCover_three_of_widthAtMost` — width-≤3 ⇒ a 3-chain cover
  exists (Dilworth specialised).
* `selectDilworthDecomp` — **the G3 selection**: a width-≤3 poset gets
  a chosen three-chain decomposition.
* `decomp_selection_groundSet` — **the G3 grounded port**: every
  width-3 non-chain poset admits a Dilworth decomposition
  `X = A ⊔ B ⊔ C` partitioning the ground set, with at least two
  nonempty chains.

### §1.2. Non-triviality witnesses

* `OneThird.Antichain3.decomp` + `decomp_selection_nonvacuous` +
  `decomp_selection_groundSet_applies` — the 3-element antichain
  witness (§3 GroundSet.lean).
* `OneThird.Step5.Chain2Iso2` (NEW concrete poset: `Fin 4`, order
  `0 < 1` with two isolated points) + `card_eq`, `not_isChainPoset`,
  `hasWidthAtMost`, `hasWidth`, `decomp_has_genuine_two_chain` — the
  genuine-2-chain witness (§4 GroundSet.lean).

---

## §2. Why the grounded port is not a marker

The **abstract** `OneThird.Step5.decomp_selection` (`FiberMass.lean:69`)
is the *bookkeeping half* of G3: given three `TripleMono` records it
observes they hold simultaneously. But it **presupposes the three
chains `A, B, C` as already-given data** — it never constructs them.

`decomp_selection_groundSet` supplies the missing *constructive half*:
the actual three-chain split. Its hypotheses are load-bearing:

* `hP : HasWidthAtMost α 3` feeds `hasChainCover_three_of_widthAtMost`
  → `OneThird.Mathlib.Poset.hasChainCover_width` — without it there is
  no `Fin 3`-valued band function, so the conclusion's `DilworthDecomp`
  cannot be built.
* `hNonChain : ¬ IsChainPoset α` is consumed to deliver the
  "≥ two nonempty chains" conjunct: a non-chain poset has an
  incomparable pair, and `incomp_band_ne` shows the band function
  separates it across two distinct (hence nonempty) chains. Drop
  `hNonChain` and that conjunct is false (a chain poset can land
  every element in one chain).

The conclusion is a conjunction of *constructed facts* — partition
cover, exact cardinality sum, two nonempty chains — each proved, not
a typed-routing shell.

---

## §3. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability.** The grounded theorem's hypotheses are
   satisfiable at the headline's range — explicitly witnessed by
   `Antichain3` (`HasWidth Antichain3 3`, `¬ IsChainPoset`) and
   `Chain2Iso2` (`HasWidth Chain2Iso2 3`, `¬ IsChainPoset`). The
   conclusion is constructed directly (Dilworth's theorem +
   `card_eq_sum_card_fiberwise`); not vacuous.
2. **Discharge-coverage.** The only cited artefact is
   `OneThird.Mathlib.Poset.hasChainCover_of_hasWidth` (Dilworth's
   theorem, already in tree, fully proved by the Galvin antichain
   split) — its scope (all finite posets) strictly covers the
   width-≤3 use here. No over-claim.
3. **Universal-quantifier truthfulness.** `decomp_selection_groundSet`
   is `∀ width-3 non-chain α, ∃ D : DilworthDecomp α, …`. The `∃ D`
   is **not** a problematic existence claim: `D` is the *Dilworth
   decomposition*, which exists for **every** finite width-≤3 poset
   by Dilworth's theorem — unlike mg-2970's R2 `∃ L with L.w ≤ 4`,
   there is no bandwidth bound, no caps, nothing to fail. The
   3-disjoint-chains counterexample (pitfall #2.3) refutes "`∃ L`
   with bounded interaction width" — it does **not** refute
   "`∃` a 3-chain decomposition", which is exactly Dilworth.

---

## §4. Scope boundary (honest)

This ticket ports the **decomposition-selection** content of G3 — the
construction of the three chains `A ⊔ B ⊔ C` — which the abstract
`decomp_selection` presupposed. Out of scope, faithful to the paper's
own structure:

* The paper's `lem:decomp-selection` also mentions a *common
  refinement* `R*` of each chain into consecutive subchains so that
  G1 endpoint-monotonicity applies to all three ordered triples.
  Paper `step5.tex:520-528` states this apparatus is **vestigial**
  ("the trivial partition works and `E := ∅` suffices"): under the
  exact-monotone form of G1 (`EndpointMono.lean`, `D₁ = E₁ = 0`) no
  refinement is needed. The Lean port reflects this — a single
  `DilworthDecomp` with three named chains serves all three ordered
  triples `(A,B|C)`, `(A,C|B)`, `(B,C|A)` at once, and the `E = ∅`
  content is `chains_cover` / `card_partition` (zero elements lost).
  The abstract simultaneous-monotonicity bookkeeping remains
  `OneThird.Step5.decomp_selection` (`FiberMass.lean`), unchanged.
* G1 (endpoint monotonicity), G2 (convex overlap), G4 (fiber-mass),
  G5 (global layering) — sibling Wave-1 tickets S5-A / S5-C / S5-D /
  S5-E.

The existing `OneThird/Step5/*.lean` files are **unchanged**;
`GroundSet.lean` is purely additive.

---

## §5. Files

* `lean/OneThird/Step5/GroundSet.lean` — NEW (~430 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S5-B-G3-Session1.md` — this file.
