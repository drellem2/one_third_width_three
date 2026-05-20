# State — S1-D — Session 1: Step 1 assembly — `thm:interface` and its corollaries

**Ticket:** mg-794c (OneThird-S1-D: Step 1 assembly — integrate
S1-A/B/C, land `thm:interface` and its corollaries).
**Branch:** `polecat-794c`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 Piece 1,
Wave-1.
**Depends:** mg-bcf2 (S1-C), mg-2e24 (S1-B), mg-30e3 (S1-A);
mg-faf8 (corrected MA-Sig signature contract).

**Scope.** Wave-1 assembly ticket of the Piece-1 (Steps 1-6 cascade
port) decomposition.  Integrates the three parallel Wave-1 ports —
S1-A (parts (i)+(ii)), S1-B (parts (iii)+(iv)), S1-C (the two
corollary cores) — into the single four-part **local interface
theorem** `thm:interface` (`step1.tex:144-195`) and its two
corollaries `cor:overlap` / `cor:triple-overlap`.

---

## §0. Verdict — **GREEN-S1-D-delivered**

`lean/OneThird/Step1/Interface.lean` (NEW, ~330 LoC) assembles the
S1-A/B/C ports into:

* `InterfaceConclusion x y` — the four-part conclusion of
  `thm:interface` as a named proposition;
* `thm_interface` — the assembled local interface theorem (headline
  Step 1 deliverable);
* `IsInterfaceMove` + `disjointPos_of_no_adjacency` — the part-(iii)
  → corollaries bridge;
* `cor_overlap`, `cor_triple_overlap` — the two corollaries assembled
  on the regular overlap / regular triple overlap;
* `thm_interface_nonvacuous` — the mg-794c acceptance witness.

`lake build OneThird.Step1.Interface` is clean (exit 0,
`✔ [993/993] Built OneThird.Step1.Interface`).  `lake build OneThird`
(full library) is clean.  The only warnings are the pre-existing
`linter.unusedDecidableInType` / `unusedSectionVars` notices in
`BadSet.lean` — unchanged from the S1-B port, not introduced here.

**No `sorry`, no new axiom.**  `#print axioms` confirms all four
assembled theorems (`thm_interface`, `cor_overlap`,
`cor_triple_overlap`, `thm_interface_nonvacuous`) depend on exactly
`[propext, Classical.choice, Quot.sound]` — the three standard
mathlib axioms, no `sorryAx`, no project axiom.

**Non-triviality bar met — no Subsingleton-on-empty baseline.**
`thm_interface_nonvacuous` instantiates the assembled `thm_interface`
at the concrete 3-element antichain `Antichain3` (`Fin 3`, discrete
order) with rich pair `(a0, a1)`.  It proves:

* `HasWidth Antichain3 3` and `¬ IsChainPoset Antichain3` — width
  **exactly 3**, genuinely non-chain;
* `IsRich 1 a0 a1` with `commonNbhdLength a0 a1 = 1` — a genuine rich
  pair, `t = 1 > 0`, so the coordinate codomain `{0,…,t}²` is the
  honest `2 × 2` grid `{0,1}²`;
* `2 ≤ numLinExt Antichain3` — the linear-extension set decomposed by
  the interface theorem is **not a subsingleton**;
* `∃ L L' : LinearExt Antichain3, BKAdj L L'` — a concrete BK edge
  exists, so part (iii)'s universal quantifier over BK moves is **not
  vacuous**;
* the assembled `thm_interface` **fires**, delivering the full
  four-part `InterfaceConclusion a0 a1`.

**No new vacuity-discovery surfaced.**  The four S1-A/B/C ports
compose cleanly; no fresh paper-side rigour gap arose during
assembly.  The one known part-(iv) imprecision (the `|I(z)| ≤ 2`
length bound) was surfaced by S1-B, not by this assembly — see §3.

---

## §1. What landed

New file `lean/OneThird/Step1/Interface.lean`, registered in
`lean/OneThird.lean` (import added after `OneThird.Step1.BadSet`).

### §1.1. The four-part interface theorem (`namespace OneThird`)

* `InterfaceConclusion x y` — the four-part conclusion as a named
  `Prop`: (i) coordinate map into the `(t+1)×(t+1)` grid + the
  common-neighbour chain; (ii) the raw-fiber decomposition
  `L(P) = F_{x,y} ⊔ Bad_{x,y}`; (iii) the BK-move classification
  trichotomy; (iv) the bad-set structural backbone (common-neighbour
  comparability + `I(z)` order-convexity + external count
  `n − t − 2` + the collinear-fiber size bound `≤ t + 1`).
* `thm_interface` — the assembled local interface theorem: for a
  width-3 poset and a rich pair `(x, y)`, `InterfaceConclusion x y`
  holds.  Proof is pure assembly:
  - part (i) ← `localInterface_coordMap_groundSet` (S1-A);
  - part (ii) ← `localInterface_rawFiber_groundSet` (S1-A);
  - part (iii) ← `bkMove_classification` (S1-B);
  - part (iv) ← `commonNbhdFinset_comparable` + `incompLocus_ordConvex`
    + `card_externalFinset` + `collinear_fiber_card_le` (S1-B).

### §1.2. The part-(iii) → corollaries bridge

* `IsInterfaceMove x y L hk` — the predicate "the BK move of `L` at
  position `k` belongs to the `(x, y)` interface": its swapped pair
  has both elements in `{x, y} ∪ C(x, y)` and at least one in
  `{x, y}`.  This is exactly the move shape part (iii) establishes for
  every coordinate-changing move (the swap of `{x,y}` / `{x,c}` /
  `{y,c}` cases of `bkSwap_signFlip` / `bkSwap_iCoord_shift` /
  `bkSwap_jCoord_shift`).
* `disjointPos_of_no_adjacency` — the bridge: from interaction-locus
  exclusion (no element of `{x, y}` is `L`-adjacent to any element of
  `{u, v} ∪ C(u, v)`), an `(x, y)`-interface move and a
  `(u, v)`-interface move have disjoint support (`DisjointPos`).
* `not_adjacency_of_regularOverlap` /
  `not_adjacency_of_regularTripleOverlap` — interaction-locus
  exclusion extracted from regular-overlap / regular-triple-overlap
  membership.

### §1.3. The two corollaries, assembled

* `cor_overlap` — `cor:overlap` (`step1.tex:429`): on the regular
  overlap `Ω°_{xy,uv}`, two interface moves span a commuting `2×2` BK
  square.  Wires `disjointPos_of_no_adjacency` into S1-C's
  `cor_overlap_commuting_square`.
* `cor_triple_overlap` — `cor:triple-overlap` (`step1.tex:516`): on
  the regular triple overlap `Ω°°°_{xyz}`, three interface moves span
  a commuting `2×2×2` BK cube.  Wires three applications of
  `disjointPos_of_no_adjacency` into S1-C's
  `cor_triple_overlap_commuting_cube`.

### §1.4. Non-vacuity witness

* `thm_interface_nonvacuous` — the mg-794c capstone (see §0).

---

## §2. Why the assembly is not a marker

`thm_interface` consumes its hypotheses honestly.  `hP :
HasWidthAtMost α 3` is load-bearing in parts (i), (iii) and (iv) — it
feeds `commonNbhd_isChain_of_width3` (part (i) common-neighbour
chain), rules out a swap of two common neighbours in
`bkMove_classification` (part (iii)), and underlies
`commonNbhdFinset_comparable` (part (iv)).  The incomparability
`hxy.1` is consumed everywhere.

The bridge `disjointPos_of_no_adjacency` is genuine content, not a
typed reroute: the `IsInterfaceMove` hypotheses are load-bearing (they
supply the `{x,y}`-element and the `{u,v}∪C(u,v)`-membership the
position argument needs), and the no-adjacency hypothesis is the
operative fact (it is the contradiction target).  The math: when the
two position intervals `{k,k+1}`, `{m,m+1}` overlap, the
`{x,y}`-element of the `(x,y)`-move is `L`-adjacent to one of the two
`{u,v}∪C(u,v)`-elements of the `(u,v)`-move — an interaction-locus
violation in every overlap case.  No element-disjointness of the rich
pairs is needed, so the bridge applies verbatim to the
element-sharing pairs `(x,y),(y,z),(x,z)` of `cor:triple-overlap`.

The corollaries `cor_overlap` / `cor_triple_overlap` consume real
`regularOverlap` / `regularTripleOverlap` membership and real
`IsInterfaceMove` data; the disjoint-support hypothesis the S1-C
commuting-square / cube verifications need is *derived* here, not
assumed.

---

## §3. Part (iv) — the `|I(z)| ≤ 2` faithfulness decision (S1-D resolution)

S1-B (mg-2e24, `docs/state-S1-B-bkmoves-badset-Session1.md`) surfaced
a paper-side imprecision: `step1.tex:308-311` claims the
incomparability locus `I(z) := {k : z ∥ c_k}` of an **external**
element `z` has **length** `≤ 2`, citing a width-`4` antichain.  A
literal width-3 argument does not support the length bound — the
common neighbours `c_k` are pairwise comparable, so a `4`-antichain
inside `{x,y,z} ∪ {c_{k_i}}` would have to be `{x,y,z,c_k}`, forcing
`z ∥ x ∧ z ∥ y`, i.e. `z ∈ commonNbhd x y`, contradicting that `z`
is external.  Width 3 yields only the **order-convexity** of `I(z)`.

S1-B ported the order-convexity (`incompLocus_ordConvex`) in full,
flagged the gap, mailed `human`, and handed the decision to S1-D
with three options: (a) supply a corrected `I(z)`-length argument,
(b) accept the weaker `O(n · t²)` bad-set bound, (c) carry
`|I(z)| ≤ 2` as a documented axiom/hypothesis.

**S1-D resolution: option (b).**  `thm_interface` part (iv) lands the
**order-convexity form** (`incompLocus_ordConvex`), *not* the
unprovable `|I(z)| ≤ 2` length bound.  Rationale:

* The order-convexity form is the genuine width-3-provable structural
  fact; it is what S1-B ported in full, with no `sorry` and no axiom.
* Per S1-B's analysis, the qualitative part-(iv) conclusion
  ("`Bad_{x,y}` is one-dimensional": collinear fibers carry `≤ t+1`
  extensions, `K = O(1)` strips, external count `n − t − 2`) is
  unaffected.  With only convexity one gets `|I(z)| ≤ t`, degrading
  the paper's `|Bad| = O(n · t)` to `O(n · t²)`.
* In the rich regime where `cor:overlap` / `cor:triple-overlap` are
  consumed (`|F_{x,y}| ≥ c·n²`, `t = Θ(n)`, `|F_{x,y}|` factorially
  large), `O(n · t²)` still gives `|Bad| = o(|F_{x,y}|)`, so every
  downstream use survives — only the sharp exponent constant is at
  stake.

This is **not a block**: the gap was surfaced by S1-B (already
reported to `human`), not by this assembly; the assembly itself
surfaces no new gap, introduces no axiom and no `sorry`.  Option (b)
keeps `thm_interface` faithful to what width-3 actually proves.  A
follow-up sharpening to `O(n·t)` (a corrected `I(z)`-length argument,
or a small documented hypothesis) can be filed separately if a
later step needs the sharp constant; no current consumer does.

---

## §4. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability.**  Every hypothesis of `thm_interface` and of the
   two corollaries is satisfiable at the headline range — explicitly
   witnessed by `thm_interface_nonvacuous` (concrete `Antichain3`,
   `IsRich 1 a0 a1`, a concrete BK edge).  The corollary hypotheses
   (`regularOverlap` membership, `IsInterfaceMove`) are satisfiable in
   principle — the regular overlap is non-empty on positive-density
   overlaps (`cor:overlap`'s setting), and `IsInterfaceMove` is the
   move shape of every genuine interface move.  No vacuous routing.
2. **Discharge-coverage.**  No external artefact is cited as a
   discharge; every clause of `thm_interface` is proved by a directly
   cited S1-A/B/C lemma, and the bridge is proved from scratch.  No
   over-claim.
3. **Universal-quantifier truthfulness.**  No `∀ … ∃ …` existence
   claim is introduced.  `thm_interface` is universally quantified
   over width-3 rich pairs with a conjunction-of-facts conclusion,
   each fact proved.  The corollaries are universally quantified over
   regular-overlap members + interface moves with a commuting-square
   / cube existence conclusion, proved constructively.  No false
   universal-existence shape (cf. pitfall #2.3).

---

## §5. Scope boundary (honest)

This ticket **assembles** the S1-A/B/C ports into `thm:interface`
plus its two corollaries.  Out of scope, faithfully so:

* The **sharp** `|Bad_{x,y}| = O(n · t)` bound — `thm_interface`
  part (iv) lands the order-convexity / collinear-fiber backbone
  (§3); the sharp exponent constant needs the `|I(z)| ≤ 2` step,
  which is not width-3-provable as stated.  No current consumer
  needs it.
* The **quantitative** `O((t_{xy}+t_{uv})^2)` interaction-locus bound
  and the `O(t·√|Ω|)` triple-overlap bad-mass bound — these remain in
  the `Corollaries.lean` set-theoretic scaffold form
  (`bounded_interaction`, `regularOverlap_density`,
  `regularTripleOverlap_density`), unchanged.  They are
  Step-4/Step-7 consumption-time concerns, not Step 1 assembly.
* `cor_overlap` / `cor_triple_overlap` deliver the **commuting-square
  / commuting-cube** content of the corollaries (the `cor:overlap`
  part (a) / `cor:triple-overlap` parts (b),(c) cores).  The
  density parts (`cor:overlap` part (b), `cor:triple-overlap`
  part (d)) are the `Corollaries.lean` scaffold, unchanged.

The S1-A/B/C files (`GroundSet.lean`, `BKMoves.lean`, `BadSet.lean`,
`Overlap.lean`, `Corollaries.lean`) and `RichPair.lean` are
**unchanged**; `Interface.lean` is purely additive and re-assembles.

---

## §6. Files

* `lean/OneThird/Step1/Interface.lean` — NEW (~330 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S1-D-Session1.md` — this file.
