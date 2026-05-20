# State — S1-A — Session 1: Step 1 Lean port part 1 — coordinate map and raw-fiber decomposition

**Ticket:** mg-30e3 (OneThird-S1-A: Step 1 Lean port part 1 —
coordinate map and raw-fiber decomposition).
**Branch:** `polecat-mg-30e3`.
**Parent:** mg-d8c7 (Option A' FULL REFACTOR scoping) §2.1 piece 1,
Wave-1.
**Depends:** mg-faf8 (corrected MA-Sig signature contract — landed
a554cbb).

**Scope.** Wave-1 ticket of the Piece-1 (Steps 1-6 cascade port)
decomposition.  Delivers the first two parts of paper `thm:interface`
(`step1.tex:144-195`) — the **coordinate map** `π_{x,y}` (part (i)) and
the **raw-fiber decomposition** `L(P) = F_{x,y} ⊔ Bad_{x,y}` (part
(ii)) — grounded on the concrete Bubley–Karzanov graph `bkGraph α`,
with a non-vacuous concrete instantiation.

---

## §0. Verdict — **GREEN-S1-A-delivered**

`lean/OneThird/Step1/GroundSet.lean` (NEW, ~410 LoC) ports paper
`thm:interface` parts (i) + (ii) grounded on the BK graph, and ships
the mg-30e3-mandated **non-triviality witness**.  `lake build` is clean
(exit 0; the only residual warnings are the `weak`
`linter.unusedDecidableInType` notices, identical to the pre-existing
`Corollaries.lean:92` pattern in the same directory).

**Non-triviality bar met — no Subsingleton-on-empty baseline.**  The
port instantiates non-vacuously at the concrete 3-element antichain
`Antichain3` (`Fin 3`, discrete order).  `Antichain3.localInterface_nonvacuous`
proves, at this concrete poset:

* it has **width exactly 3** (`HasWidth Antichain3 3`) and is genuinely
  **not a chain** (`¬ IsChainPoset Antichain3`) — the hypotheses of the
  grounded theorem are satisfiable, not vacuously quantified;
* the rich-pair hypothesis is satisfiable: `IsRich 1 a0 a1` holds, with
  common-neighbour-chain length `t(a0,a1) = 1 > 0` (proved
  `commonNbhdLength a0 a1 = 1`) — so the coordinate codomain `{0,…,t}²`
  is the honest `2 × 2` grid `{0,1}²`, not a degenerate point;
* `2 ≤ numLinExt Antichain3` — the linear-extension set that the raw
  fibers decompose is **not a subsingleton**, explicitly rebutting the
  "Subsingleton-on-empty" degenerate baseline;
* the grounded interface theorem `localInterface_groundSet` *actually
  fires* and delivers its part-(i)/(ii) conclusions concretely.

**No vacuity-discovery surfaced.**  Skeptical re-audit against
`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2's three checks — see §3
below.  The paper's parts (i)+(ii) are genuinely soft (the paper itself
says part (i) is "immediate from Definition" and the part-(ii)
partition is "by definition"); the width-3 mathematical content first
appears in parts (iii)+(iv), which are the sibling tickets S1-B/C/D.
The grounded theorem nonetheless consumes its width hypothesis honestly
— see §2.

---

## §1. What landed

New file `lean/OneThird/Step1/GroundSet.lean`, registered in
`lean/OneThird.lean` (import added after `OneThird.Step1.Corollaries`).

### §1.1. BK-graph-grounded interface theorems (`namespace OneThird`)

* `localCoord_mem_grid` — paper part (i): every linear extension (=
  every vertex of `bkGraph α`) has local coordinate
  `π_{x,y}(L) ∈ {0,…,t}²`, the `(t+1)×(t+1)` grid.
* `goodFiber_bkGraph_adj_iff` — paper Def. `def:good-fiber` clause (G3),
  grounded: inside a good fiber, the edges of `bkGraph α` are exactly
  the unit grid moves of the local coordinates (sign-preserving `±e₁`,
  `±e₂`).
* `localInterface_coordMap_groundSet` — paper part (i) bundled: the
  common-neighbour set is a chain (the width-3 content, via
  `commonNbhd_isChain_of_width3`) and the coordinate map lands in
  `{0,…,t}²`.
* `localInterface_rawFiber_groundSet` — paper part (ii): the raw fibers
  cover `V(bkGraph α)`, and `F_{x,y}` / `Bad_{x,y}` partition it.
* `localInterface_groundSet` — parts (i) + (ii) bundled; the part-1
  deliverable of the Step 1 cascade port.

### §1.2. Non-triviality witness (`namespace OneThird.Antichain3`)

* `Antichain3` — the 3-element antichain (`Fin 3`, discrete order),
  with `DecidableEq` / `Fintype` / `PartialOrder` instances.
* `hasWidth` (`HasWidth Antichain3 3`), `not_isChainPoset`,
  `incomp_iff_ne`, `commonNbhdFinset_a0_a1` (`= {a2}`),
  `commonNbhdLength_a0_a1` (`= 1`), `isRich_a0_a1` (`IsRich 1 a0 a1`),
  `two_le_numLinExt` (`2 ≤ numLinExt Antichain3`).
* `localInterface_nonvacuous` — the capstone acceptance witness (see
  §0); fires `localInterface_groundSet` at the concrete poset.

---

## §2. Why the grounded theorem is not a marker

`localInterface_groundSet` takes `hP : HasWidthAtMost α 3` and
`hxy : IsRich T x y`.  Both are **load-bearing**: clause (1) of part
(i) is `IsChain (· ≤ ·) (commonNbhd x y)`, discharged by
`commonNbhd_isChain_of_width3 hP hxy.1` — which consumes the width
hypothesis `hP` *and* the incomparability `hxy.1`.  This is paper
`lem:CNchain-width3`, the input that makes the coordinate map "encode
positions in the sorted common chain" (`step1.tex:198-201`).

The part-(ii) raw-fiber decomposition (`localInterface_rawFiber_groundSet`)
is hypothesis-free — faithfully matching the paper, where the partition
is "by definition" (the raw fibers are equivalence classes; `Bad_{x,y}`
is the complement of `F_{x,y}`).  This is *not* a vacuity: the
non-triviality witness (`two_le_numLinExt`) proves the partitioned set
is genuinely non-trivial.

---

## §3. Skeptical re-audit (`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2)

1. **Satisfiability.**  The grounded theorems' hypotheses are
   satisfiable at the headline's range — explicitly witnessed by
   `Antichain3.localInterface_nonvacuous` (`HasWidth Antichain3 3`,
   `IsRich 1 a0 a1`).  The conclusions are constructed directly (the
   coordinate bound is `Finset.card_filter_le`; the partition is the
   `badSet = univ \ goodFiberSet` complement identity).  Not vacuous.
2. **Discharge-coverage.**  No external artefact is cited as a
   discharge; every clause is proved in-file or by a directly-cited
   `LocalCoords.lean` / `CommonChain.lean` lemma.  No over-claim.
3. **Universal-quantifier truthfulness.**  No `∀ … ∃ …` existence
   claim is introduced.  `localInterface_groundSet` is universally
   quantified over width-3 rich pairs with a *conjunction-of-facts*
   conclusion, each fact proved.  The witness instantiates it
   concretely.

---

## §4. Scope boundary (honest)

This ticket ports paper `thm:interface` parts (i) + (ii) **only**.
Out of scope, tracked as sibling Wave-1 tickets:

* part (iii) — BK-move classification (internal grid move / sign flip /
  external-external swap);
* part (iv) — bad-set strip decomposition + the quantitative
  `O(n·t)` / `O(t·|F|^{1/2})` bad-set bounds;
* `cor:overlap`, `cor:triple-overlap` — the overlap corollaries
  (current scaffold in `OneThird/Step1/Corollaries.lean`).

The existing `OneThird/Step1/{LocalCoords,CommonChain,Corollaries}.lean`
and `OneThird/RichPair.lean` are **unchanged**; `GroundSet.lean` is
purely additive and re-exports / strengthens.

---

## §5. Files

* `lean/OneThird/Step1/GroundSet.lean` — NEW (~410 LoC).
* `lean/OneThird.lean` — +1 import line.
* `docs/state-S1-A-Session1.md` — this file.
