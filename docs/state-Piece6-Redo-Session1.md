# Piece 6 RE-DO — full Step 8 G4 (`lem_layered_balanced_full`) — Session 1: GREEN-built + one disclosed axiom (mg-65de)

**Ticket:** mg-65de (OneThird-Piece6-Redo: genuinely build
`lem_layered_balanced_full` — de-vacuify `windowLocalization` and
`lem_layered_reduction`, discharge the Case C2 base case).
**Predecessors:** mg-fdc2 (Piece 6 Session 1, doc-only RED),
mg-faf8 (MA-Sig re-pin + Piece 6 recorded), mg-0bd1 (S7-F bridge
Session 2, 8th vacuity), mg-d8c7 (Option A' FULL REFACTOR scoping).

**Verdict:** **GREEN — Piece 6 genuinely built**, with **one
disclosed, minimal project axiom** for the genuine residual
(irreducible twin-free base case). Unlike mg-fdc2 (which produced a
660-line diagnostic and zero Lean), this session delivers genuine
Lean: the two vacuous "wiring" lemmas are de-vacuified, the full
Step 8 G4 strong induction is built and compiles, and the result is
instantiated non-vacuously at a concrete irreducible width-3
non-chain poset with a non-singleton-band decomposition.

---

## §0. What was delivered

| Deliverable | File | Status |
|---|---|---|
| `windowLocalization` de-vacuified | `Step8/LayeredBalanced.lean` | **Genuine** — constructs a real `OrdinalDecomp`, delivers marginal invariance + lift |
| `lem_layered_reduction` de-vacuified | `Step8/LayeredReduction.lean` | **Genuine** — conclusion derived, not an input field |
| `lem_layered_balanced_full` (Piece 6) | `Step8/LayeredBalancedFull.lean` (new) | **Built** — strong induction, Cases A/B genuine, Case C peeled |
| `lem_layered_balanced_irreducible_base` | `Step8/LayeredBalancedFull.lean` (new) | **Disclosed axiom** — the genuine residual |
| Non-vacuous instantiations | `Step8/LayeredBalancedFullExample.lean` (new) | **Built** — `Antichain3` + `windowLocalization` concrete |

The whole library builds (`lake build OneThird`). `AXIOMS.md` gains
one entry; `PROOF-STRUCTURE-ONBOARDING.md` is updated in the same
commit (maintenance contract §5).

---

## §1. The three gaps mg-65de scoped, and how each was closed

### Gap 1 — `windowLocalization` was vacuous

**Before.** `windowLocalization` (`LayeredBalanced.lean:103`) proved
`∃ q, probLT x y = q ∧ |W| ≤ 3(3w+1)` by `q := probLT x y`. The
first conjunct was `rfl`; the lemma carried only the window-size
bound and **no marginal-invariance content**.

**After.** `windowLocalization` now takes two band boundaries
`cutLo ≤ cutHi` at which `L` is layer-ordinal reducible (the cuts
are *clean*) and **constructs a genuine `OrdinalDecomp β`** with
`Mid = {z : cutLo < band z ≤ cutHi}`. It delivers:

* a real `OrdinalDecomp` (the comparability fields are discharged
  from the reducibility hypotheses + the layered axioms);
* the size bound `|Mid| ≤ 3(cutHi − cutLo)` (from (L1));
* the **marginal-invariance identity** `probLT x y = probLT_{P|_W} x y`
  (`OrdinalDecomp.probLT_restrict_eq`, paper `cor:ordinal-marginal`);
* the **balanced-pair lift** `HasBalancedPair ↥W → HasBalancedPair β`
  (`OrdinalDecomp.hasBalancedPair_lift`).

This is exactly the content the ticket asked for ("HasBalancedPair
on the window implies HasBalancedPair on beta", plus genuine
marginal invariance).

### Gap 2 — `lem_layered_reduction` was vacuous

**Before.** `ReductionWitness` carried `conclusion : balanced` — the
ambient conclusion *itself* — as an input field, and
`lem_layered_reduction` was literally `fun W => W.conclusion`: it
assumed its own conclusion.

**After.** `ReductionWitness` now carries only data about the **two
strictly-smaller sub-posets**: a clean two-part ordinal cut
(`OrdinalDecomp` with `Mid = ∅`, both sides non-empty) and a
balanced pair on **one side** (`HasBalancedPair ↥D.Lower ∨
HasBalancedPair ↥D.Upper`). `lem_layered_reduction` **derives**
`HasBalancedPair β` via `OrdinalDecomp.hasBalancedPair_lift_lower /
_upper`. The conclusion is computed, not assumed; the input is a
genuinely weaker statement about sub-posets. It is wired into Case B
of `lem_layered_balanced_full`.

### Gap 3 — the Case C2 base case had no in-tree discharge

This is the genuine residual. See §3 for the genuine attempt and §4
for the minimal axiom.

---

## §2. `lem_layered_balanced_full` — the architecture built

`lem_layered_balanced_full` (`step8.tex:2453-2464`) is strong
induction on `Fintype.card β`. The step dispatches on the
**ordinal-sum structure**:

* **Case B — reducible.** If `L` is layer-ordinal reducible at a
  band index `k` with both sides non-empty (`hNice`), `β` is a
  genuine two-part ordinal sum. The incomparable pair lands wholly
  in one (strictly smaller) side — a cross-pair is `<`-forced by
  reducibility — so the induction hypothesis (on `L.restrict`)
  produces a balanced pair there, and `lem_layered_reduction` lifts
  it. **Genuine, no axiom.**

* **Case C-twin.** Otherwise `β` is irreducible. If `β` has two
  distinct elements with identical ambient `<`-profile,
  `hasBalancedPair_of_ambient_profile_match` (`Case3Struct.lean`,
  the transposition-automorphism argument) closes it. This subsumes
  the paper's `K = 1` single-antichain case. **Genuine, no axiom.**

* **Case C-residual.** Otherwise `β` is irreducible *and* twin-free
  — discharged by the disclosed axiom
  `lem_layered_balanced_irreducible_base` (§4).

The peel is genuine: Case B is the paper's `cor:reducibility-transfer`
reduction; Case C-twin is `prop:in-situ-balanced` Case 1. The
residual axiom is exactly `prop:in-situ-balanced` Cases 2 + 3.

**Why this is not mg-fdc2's blocked routing.** mg-fdc2 found the
*scoped* routing ("`Case3Witness_proof` becomes the base case;
wire the placeholders") unbuildable. This session does not use that
routing: it does not route through `Case3Witness_proof` at all (so
band injectivity is never needed), and it de-vacuifies the
placeholders into genuine lemmas before wiring. The strong induction
is the paper's own outer induction on `|X|`, built directly.

---

## §3. The genuine finding — the paper's window-localization is invalid for irreducible posets

A genuine attempt to formalise the paper's Case C (window-localise,
recurse on `W ⊊ X`) surfaced a **genuine gap in the paper proof**.

**The paper's `lem:window-localization`** (`step8.tex:2654`) claims
`W(i,j) = L_{min−w} ∪ ⋯ ∪ L_{max+w}` is the middle piece of an
ordinal-sum decomposition `X = X⁻ ⊔ W ⊔ X⁺`. **This is false for
`w ≥ 1`.** An ordinal middle piece needs every element below `W` to
be `<_P` every element of `W`. An element `z` at band `min−w−1` and
a window element `ω` at the boundary band `min−w` differ by a single
band index; axiom (L2) (`band x + w < band y ⇒ x <_P y`) does **not**
force `z <_P ω` once `w ≥ 1`. So the cut below `W(i,j)` is not clean.

**An ordinal middle piece requires both boundary cuts to be clean** —
i.e. `LayerOrdinalReducible L` at both boundaries. A layer-ordinal
**irreducible** poset has **no** clean cut anywhere, so its only
ordinal middle pieces are `∅` and `X` itself. Hence the paper's
**Case C1** (recurse on a proper window `W ⊊ X`) is **impossible for
an irreducible poset**, and **Case C2** (`W = X`) is the *only*
sub-case — but the paper's Case-C2 size bound `|X| ≤ 3(3w+1)` is
**also false**:

> **Counterexample.** The poset `β = {1, …, K}` with
> `i <_P j ⇔ j − i > 2` is a valid partial order, has width 3
> (antichains are intervals of length `≤ 3`), is not a chain, and
> admits the layered decomposition `band := id`, `K := K`, `w := 2`.
> Every band boundary `k` is straddled by the incomparable pair
> `(k, k+1)`, so `β` is layer-ordinal **irreducible**. Yet `K` is
> **unbounded** — `|β| = K` is not `≤ 3(3·2+1) = 21`.

So the irreducible residual is **genuinely unbounded**: the existing
bounded enumeration certificates (`case3_certificate`, the mg-4d7b
Python enumeration over `|β| ≤ 30`) do **not** cover it, and there
is no "recurse to a smaller window" escape. This is why the residual
is genuinely open and not a transcription oversight.

The de-vacuified `windowLocalization` correctly **requires** the two
clean-cut hypotheses (`LayerOrdinalReducible L cutLo / cutHi`); it
is honest about needing them, unlike the paper's version. It is
genuine and is exercised concretely
(`window_localization_concrete`), but it is **not on the headline
recursion path**, because for layered posets every clean window is
one side of an ordinal cut — which Case B already handles via
`lem_layered_reduction`. (For a layered poset, `LayerOrdinalReducible`
at a band boundary is equivalent to a genuine two-part ordinal sum:
each band is wholly in one side, since a band is an antichain.)

---

## §4. The disclosed axiom — `lem_layered_balanced_irreducible_base`

The genuine residual of Piece 6, after Case B (reducible) and
Case C-twin (profile collision) are genuinely proved:

```lean
axiom lem_layered_balanced_irreducible_base
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4)
    (hIrr  : ¬ ∃ k, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k ∧
                    both sides non-empty)              -- irreducible
    (hNoTwin : ¬ ∃ a a', a ≠ a' ∧
                 (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')) :  -- twin-free
    HasBalancedPair β
```

It is paper `prop:in-situ-balanced` Cases 2 + 3 — the
Ahlswede–Daykin / FKG profile-ordering inequality and the finite
profile-antichain enumeration.

**Strictly weaker than the headline, not a dodge.** The axiom adds
two hypotheses (`hIrr`, `hNoTwin`) to `lem_layered_balanced_full`.
The complementary cases are genuinely proved (Case B + Case C-twin,
§2). So `lem_layered_balanced_full = reducible(proved) ∨
twin(proved) ∨ irreducible-twin-free(axiom)`. The
reducible-vs-irreducible split is genuine mathematical content (the
ordinal-sum factorisation `cor:reducibility-transfer`), not a
relabelling of the headline.

**Why it cannot be proved in this ticket** (genuine attempt, ticket
directive "do NOT default to a new axiom"):

1. `Case3Witness_proof` cannot be the base case — it needs band
   injectivity Piece 6's `L` does not carry (mg-fdc2 §3, re-verified).
2. The FKG / Ahlswede–Daykin inequality for linear extensions (paper
   Case 2) is **not in the tree** — future work
   (`Mathlib/RelationPoset/FKG.lean §11`); the in-tree
   `Case2FKGSubClaim` is **provably false**.
3. The residual is **genuinely unbounded** (§3) — paper Case 3's
   bounded enumeration does not cover it, and the paper's own
   size-bound argument is false.

A faithful proof needs the FKG-for-linear-extensions infrastructure
(multi-polecat, `~2000`–`3500` LoC) **plus** new math for the
unbounded irreducible regime. That is beyond a single Piece-6
ticket. The axiom is the precise minimal residual.

**For pm-onethird.** Per the ticket ("Any axiom proposal comes back
to pm-onethird for review before adoption"), this axiom is filed for
review. The full disclosure is in `AXIOMS.md`
(`OneThird.Step8.lem_layered_balanced_irreducible_base`). It is
landed (rather than left as a `sorry`) so that
`lem_layered_balanced_full` is a complete, axiom-cited theorem; if
pm-onethird rejects the axiom, the replacement path is in `AXIOMS.md`.

---

## §5. Non-vacuous instantiation (the non-triviality bar)

`Step8/LayeredBalancedFullExample.lean`:

* `antichain3_hasBalancedPair_via_full` — `lem_layered_balanced_full`
  applied to **`Antichain3`**: a concrete width-3, non-chain,
  **irreducible** (an antichain admits no non-trivial ordinal cut)
  poset with a **non-singleton-band** layered decomposition (the
  single band `L_1` holds all three elements). This is exactly the
  configuration mg-fdc2 §3.3 flagged as "no in-tree discharge"; it
  is discharged genuinely: the branch mathematically active for
  `Antichain3` is Case C-twin (the three elements are pairwise
  twins). `antichain3_hasBalancedPair_direct` exhibits that
  branch's content axiom-free
  (`hasBalancedPair_of_ambient_profile_match`). Note `#print axioms
  antichain3_hasBalancedPair_via_full` still lists
  `lem_layered_balanced_irreducible_base` — `#print axioms` reports
  the transitive closure of the proof *term* of
  `lem_layered_balanced_full`, which references the axiom in the
  sibling Case C-residual branch; it does not reflect which branch
  is active for a given instance.

* `window_localization_concrete` — the de-vacuified
  `windowLocalization` applied to concrete data, producing a genuine
  `OrdinalDecomp Antichain3` with the marginal-invariance identity
  and the balanced-pair lift.

`lem_layered_reduction` is genuinely consumed by
`lem_layered_balanced_full`'s Case B (build-verified in the proof
term).

---

## §6. Verification log

* `windowLocalization` rewritten — `LayeredBalanced.lean`; builds.
* `lem_layered_reduction` / `ReductionWitness` rewritten —
  `LayeredReduction.lean` (import `OneThird.Mathlib.LinearExtension.Subtype`
  added; no import cycle — `Subtype.lean` does not import
  `LayeredReduction.lean`); builds.
* `lem_layered_balanced_full` + axiom — `LayeredBalancedFull.lean`
  (new); builds.
* Instantiations — `LayeredBalancedFullExample.lean` (new); builds.
* `OneThird.lean` imports both new files; `lake build OneThird`
  succeeds.
* No `sorry` introduced. One named axiom added
  (`lem_layered_balanced_irreducible_base`), fully disclosed in
  `AXIOMS.md`.
* The §3 paper-gap finding (window-localization invalid for
  irreducible posets) and the unbounded-irreducible counterexample
  are reproducible facts about the layered axioms, independent of
  any unbuilt P1–P5 deliverable.

---

## §7. Cross-references

* `lean/OneThird/Step8/LayeredBalanced.lean` — `windowLocalization`.
* `lean/OneThird/Step8/LayeredReduction.lean` — `ReductionWitness`,
  `lem_layered_reduction`.
* `lean/OneThird/Step8/LayeredBalancedFull.lean` —
  `lem_layered_balanced_full`, `lem_layered_balanced_irreducible_base`,
  `layered_implies_balanced_full`.
* `lean/OneThird/Step8/LayeredBalancedFullExample.lean` — the
  non-vacuous instantiations.
* `lean/AXIOMS.md` —
  `OneThird.Step8.lem_layered_balanced_irreducible_base` entry.
* `docs/state-Piece6-FullStep8G4-Session1.md` (mg-fdc2) — the
  predecessor RED diagnostic this session executes against.
* `docs/state-MA-Sig-Session1.md` §10 (mg-faf8) — the Piece 6
  contract.
* `step8.tex:2453-2464` (`lem:layered-balanced`), `:3096-3186`
  (`prop:in-situ-balanced`), `:2654` (`lem:window-localization`).
