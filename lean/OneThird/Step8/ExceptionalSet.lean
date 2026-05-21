/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ChainPotentials
import OneThird.Step8.ConcreteChainLiftData
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Step 8 — S7-F bridge sub-ticket A: the exceptional set `X^exc`

This file is **FULL REFACTOR Phase-2, Piece 3 (the S7-F bridge),
sub-ticket A** (work item `mg-08d7`). It ports **item (i) of paper
`lem:layered-from-step7`** (`step8.tex:2009-2089`): construct the
exceptional set `X^exc` from a `ChainLiftData α`, and bound its
cardinality by an `O_T(1)` constant `C_exc(T)`.

## What the paper does (`step8.tex:2027-2055`, item (i))

The bridge removes a small exceptional set before it can present the
remaining ground set as an *exactly* layered decomposition. The
exceptional set is a union of three pieces:

```
  X^exc  :=  X^exc_mono  ∪  X^exc_band  ∪  X^exc_sync
```

* `X^exc_mono` — the non-monotonicity locus of the chain potential
  `a` on its Dilworth chain (`o(1)`-mass by `prop:71`, empty in the
  Step 5(C) branch).
* `X^exc_band` — the bandwidth-excess endpoints: elements that sit in
  an incomparable pair whose chain-potential gap exceeds `K_bw`
  (`O_T(1)` count by `lem:bandwidth`).
* `X^exc_sync` — the chain-tail orphans: chain elements whose
  synchronization partner in another chain is undefined (`≤ K_bw` per
  synchronization map).

Item (i): `|X^exc| ≤ C_exc(T) = O_T(1)`.

## What this file delivers

* **`Xexc_mono`, `Xexc_band`, `Xexc_sync`, `Xexc`** — the four
  `Finset α`s, each derived **only** from the bare `ChainLiftData α`
  fields (`triple`, `pot`, `K_bw`, `fAB`, `fAC`, `fBC`) and the poset
  order of `α`.
* **`Xexc_mono_eq_empty`** — the mono-exceptional set is **genuinely
  empty**, *earned* from the `ChainPotential.strictMono{A,B,C}`
  fields: the Lean `ChainPotential` is the *post-`prop:71`* potential,
  so it is strictly chain-monotone and the non-monotonicity locus has
  no inhabitant.
* **`Xexc_sync_card_le`** — `|X^exc_sync|` is bounded by the three
  synchronization-map orphan counts, hypothesis-free (subadditivity of
  `card` over `∪` and `image`).
* **`Xexc_card_le_of_budget`** — the **fully concrete** cardinality
  bound `|X^exc| ≤ B + 6` from the genuine cascade facts: a band
  budget `B`, the three per-sync-map orphan bounds (`≤ K_bw`), and
  `K_bw ≤ 2`. No abstract constant, no `opaque`, no axiom.
* **`Xexc_card_le`** — the contract-shaped corollary `|X^exc| ≤
  C_exc T` (`MA-Sig §4.1`/`§4.2 §E`), under `ExcBudget D T`.
* The **grid discharge** (`§5`): `Xexc gridChainLiftData` computes to
  `{(0,0)}` (card `1`, genuinely non-empty), `ExcBudget` holds for the
  grid for **every** `T`, and the bound closes — a concrete,
  free-hypothesis, non-degenerate verification (the sub-ticket-A
  analogue of `f7a_chainLiftData_constructible`).

## The `ExcBudget` interface — what the bridge must discharge

The **bare** `ChainLiftData α` carries no soundness invariant: it is
inhabited even for the 3-disjoint-chains family `Δ_ℓ`
(`docs/state-MA-Sig-Session1.md` §11.3), where `X^exc` is *not*
`O_T(1)` (empty sync maps make every chain element an orphan). So the
`O_T(1)` cardinality bound is **not** provable from the bare structure
alone — and a theorem claiming it would be **false** on `Δ_ℓ`.

`ExcBudget D T` pins the precise extra facts the genuine cascade
supplies. They are exactly the paper's three `O_T(1)` ingredients:
`lem:budget-var` (mono — discharged here, the set is empty),
`lem:bandwidth` (band count `≤ c₁ T`), and the per-chain orphan bound
(`≤ K_bw` per synchronization map). Wiring `ExcBudget` out of the
bridge's `hCex` (a minimal γ-counterexample) + the Steps-1-7 cascade
is **Piece-1 / sub-ticket S7-F-Z** integration work — not sub-ticket
A. `ExcBudget` is genuinely satisfiable (the grid satisfies it for
every `T`, `§5`) and genuinely *fails* for `Δ_ℓ`, so it is a real
soundness filter, not an inert hypothesis.

## Cross-references

* `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`
  (the bridge input); `:211` `SyncMap`; `:267` `ChainPotential`.
* `lean/OneThird/Step8/ConcreteChainLiftData.lean` — `gridChainLiftData`
  (the F7a witness, mg-974c) used for the `§5` discharge.
* `docs/state-MA-Sig-Session1.md` §4.1 (`C_exc`), §4.2 §E
  (`lem_layered_from_step7` — emits `Xexc.card ≤ C_exc T`), §11.3
  (the bare-structure caveat).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.3 — Piece 3,
  sub-arc `mg-S7-F-A`.
* `step8.tex:2009-2089` — `lem:layered-from-step7`; the `X^exc`
  definition at `:2034-2055`, item (i) at `:2056-2065`, the `|X^exc|`
  bookkeeping in the proof at `:2182-2196`.

No `sorry`. No new `axiom` (`AXIOMS.md` unchanged). The single
`opaque` constant `c₁` models the abstract Step-5 cascade constant
`c_1(T)` of paper `lem:endpoint-mono`; it is an opaque definition, not
an axiom, and the load-bearing content (`Xexc_card_le_of_budget`) does
not reference it.
-/

namespace OneThird
namespace Step8

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
  [DecidableLE α]

/-! ### §1 — `X^exc_mono`: the non-monotonicity locus

Paper `step8.tex:2042-2044`: `X^exc_mono` is the set of chain
elements where the potential `a` fails strict chain-monotonicity.

The Lean `ChainPotential` (`ChainPotentials.lean:267`) carries
`strictMono{A,B,C}` as **fields** — it is, by construction, the
potential *after* `prop:71`'s `o(1)`-mass cleanup. So the
non-monotonicity locus is genuinely empty. We still define it as a
real filter over the chain indices (it *is* "derived from the
`ChainLiftData` fields"), and *earn* the emptiness from the
`strictMono` fields (`Xexc_mono_eq_empty`) — rather than asserting
`∅` outright. -/

/-- The mono-exceptional **A-chain indices**: indices `i` where the
potential fails to strictly increase to some later index `j`. -/
def monoExcIdxA (D : ChainLiftData α) : Finset (Fin D.triple.A.length) :=
  univ.filter (fun i => ∃ j : Fin D.triple.A.length, i < j ∧
    ¬ D.pot.a (D.triple.A.elem i) < D.pot.a (D.triple.A.elem j))

/-- The mono-exceptional **B-chain indices**. -/
def monoExcIdxB (D : ChainLiftData α) : Finset (Fin D.triple.B.length) :=
  univ.filter (fun i => ∃ j : Fin D.triple.B.length, i < j ∧
    ¬ D.pot.a (D.triple.B.elem i) < D.pot.a (D.triple.B.elem j))

/-- The mono-exceptional **C-chain indices**. -/
def monoExcIdxC (D : ChainLiftData α) : Finset (Fin D.triple.C.length) :=
  univ.filter (fun i => ∃ j : Fin D.triple.C.length, i < j ∧
    ¬ D.pot.a (D.triple.C.elem i) < D.pot.a (D.triple.C.elem j))

/-- **`X^exc_mono`** (`step8.tex:2042-2044`) — the non-monotonicity
locus of the chain potential, as a `Finset α`. -/
def Xexc_mono (D : ChainLiftData α) : Finset α :=
  (monoExcIdxA D).image D.triple.A.elem ∪
  (monoExcIdxB D).image D.triple.B.elem ∪
  (monoExcIdxC D).image D.triple.C.elem

lemma monoExcIdxA_empty (D : ChainLiftData α) : monoExcIdxA D = ∅ := by
  unfold monoExcIdxA
  rw [Finset.filter_eq_empty_iff]
  intro i _
  push_neg
  intro j hij
  exact D.pot.strictMonoA hij

lemma monoExcIdxB_empty (D : ChainLiftData α) : monoExcIdxB D = ∅ := by
  unfold monoExcIdxB
  rw [Finset.filter_eq_empty_iff]
  intro i _
  push_neg
  intro j hij
  exact D.pot.strictMonoB hij

lemma monoExcIdxC_empty (D : ChainLiftData α) : monoExcIdxC D = ∅ := by
  unfold monoExcIdxC
  rw [Finset.filter_eq_empty_iff]
  intro i _
  push_neg
  intro j hij
  exact D.pot.strictMonoC hij

/-- **`X^exc_mono` is genuinely empty.** Earned from the
`ChainPotential.strictMono{A,B,C}` fields: the Lean `ChainPotential`
is the post-`prop:71` monotone potential, so the non-monotonicity
locus has no inhabitant (paper: `X^exc_mono` is "empty in branch
(a)", `o(1)`-mass after `prop:71` in branch (b)). -/
theorem Xexc_mono_eq_empty (D : ChainLiftData α) : Xexc_mono D = ∅ := by
  unfold Xexc_mono
  rw [monoExcIdxA_empty, monoExcIdxB_empty, monoExcIdxC_empty]
  simp

/-! ### §2 — `X^exc_sync`: the chain-tail orphans

Paper `step8.tex:2049-2055`: `X^exc_sync` collects the chain elements
whose synchronization partner in another chain is undefined
(`f_••(i) = none`). The band assembly `L_k := {a_k, b_{f_AB(k)},
c_{f_AC(k)}}` (`step8.tex:2117-2121`) cannot place such an element, so
it is absorbed into the exceptional set. The paper bounds this by
`≤ K_bw` per chain; in the Lean model there are exactly three
synchronization maps (`fAB`, `fAC`, `fBC`), each contributing
`≤ K_bw` orphans, hence `|X^exc_sync| ≤ 3·K_bw`. -/

/-- The **orphan index set** of a synchronization map — the domain
indices at which the partial map is undefined (`partner i = none`). -/
def syncOrphans {nA nB : ℕ} (f : SyncMap nA nB) : Finset (Fin nA) :=
  univ.filter (fun i => (f.partner i).isNone)

@[simp] lemma mem_syncOrphans {nA nB : ℕ} (f : SyncMap nA nB)
    (i : Fin nA) : i ∈ syncOrphans f ↔ (f.partner i).isNone := by
  simp [syncOrphans]

/-- **`X^exc_sync`** (`step8.tex:2049-2055`) — the chain-tail orphans,
as a `Finset α`: the `A`-elements with no `B`- or `C`-partner, and
the `B`-elements with no `C`-partner. -/
def Xexc_sync (D : ChainLiftData α) : Finset α :=
  (syncOrphans D.fAB).image D.triple.A.elem ∪
  (syncOrphans D.fAC).image D.triple.A.elem ∪
  (syncOrphans D.fBC).image D.triple.B.elem

/-- **Hypothesis-free orphan bound.** `|X^exc_sync|` is at most the
sum of the three synchronization-map orphan counts — subadditivity of
`Finset.card` over `∪` and `image`. -/
theorem Xexc_sync_card_le (D : ChainLiftData α) :
    (Xexc_sync D).card ≤ (syncOrphans D.fAB).card
      + (syncOrphans D.fAC).card + (syncOrphans D.fBC).card := by
  unfold Xexc_sync
  have h1 := card_union_le
    ((syncOrphans D.fAB).image D.triple.A.elem ∪
      (syncOrphans D.fAC).image D.triple.A.elem)
    ((syncOrphans D.fBC).image D.triple.B.elem)
  have h2 := card_union_le
    ((syncOrphans D.fAB).image D.triple.A.elem)
    ((syncOrphans D.fAC).image D.triple.A.elem)
  have h3 : ((syncOrphans D.fAB).image D.triple.A.elem).card
      ≤ (syncOrphans D.fAB).card := card_image_le
  have h4 : ((syncOrphans D.fAC).image D.triple.A.elem).card
      ≤ (syncOrphans D.fAC).card := card_image_le
  have h5 : ((syncOrphans D.fBC).image D.triple.B.elem).card
      ≤ (syncOrphans D.fBC).card := card_image_le
  omega

/-! ### §3 — `X^exc_band`: the bandwidth-excess endpoints

Paper `step8.tex:2045-2048`: `X^exc_band` collects the endpoints of
rich pairs whose synchronization offset exceeds `K_bw`. In the Lean
port we use the equivalent **chain-potential gap** form, which is
exactly the negation of the genuine `lem:bandwidth` content already
proved for a concrete witness (`gridChainLiftData_bandwidth_genuine`,
`ConcreteChainLiftData.lean`): an element is band-exceptional iff it
sits in an incomparable pair whose potential gap exceeds `K_bw`. This
is derivable purely from the `ChainLiftData` fields `pot` and `K_bw`
(no `Rich⋆` data is needed — dropping the "rich" qualifier only
*enlarges* the set, so the cardinality bound stays faithful). The
gap `|a x − a y| > K_bw` is written in `abs`-free disjunction form
`K_bw < a x − a y ∨ K_bw < a y − a x` to keep the filter predicate
kernel-reducible. -/

/-- **`X^exc_band`** (`step8.tex:2045-2048`) — the bandwidth-excess
endpoints, as a `Finset α`: elements `z` that sit in an incomparable
pair `(z, y)` whose chain-potential gap exceeds `K_bw`. -/
def Xexc_band (D : ChainLiftData α) : Finset α :=
  univ.filter (fun z => ∃ y : α, ¬ z ≤ y ∧ ¬ y ≤ z ∧
    ((D.K_bw : ℤ) < D.pot.a z - D.pot.a y ∨
     (D.K_bw : ℤ) < D.pot.a y - D.pot.a z))

lemma mem_Xexc_band (D : ChainLiftData α) (z : α) :
    z ∈ Xexc_band D ↔ ∃ y : α, ¬ z ≤ y ∧ ¬ y ≤ z ∧
      ((D.K_bw : ℤ) < D.pot.a z - D.pot.a y ∨
       (D.K_bw : ℤ) < D.pot.a y - D.pot.a z) := by
  simp [Xexc_band]

/-! ### §4 — `X^exc` and the cardinality bound (paper item (i)) -/

/-- **`X^exc`** (`step8.tex:2034-2055`, `eq:Xexc-def`) — the
exceptional set, the union of the three pieces. -/
def Xexc (D : ChainLiftData α) : Finset α :=
  Xexc_mono D ∪ Xexc_band D ∪ Xexc_sync D

/-- Since `X^exc_mono` is empty (`§1`), `X^exc` is the union of just
the band and sync pieces. -/
theorem Xexc_eq_band_union_sync (D : ChainLiftData α) :
    Xexc D = Xexc_band D ∪ Xexc_sync D := by
  unfold Xexc
  rw [Xexc_mono_eq_empty, empty_union]

/-- **The fully concrete cardinality bound** — paper item (i),
hypothesis-explicit and free of any abstract constant.

Given a band budget `B` (the `lem:bandwidth` ground-set count), the
three per-synchronization-map orphan bounds (`≤ K_bw`, the paper's
"`≤ K_bw` per chain"), and `K_bw ≤ 2` (`lem:bandwidth`, so the lifted
width is `K_bw + 2 ≤ 4`), the exceptional set has

```
  |X^exc| ≤ B + 6.
```

The `+6 = 3·2` absorbs the three orphan sets at `K_bw ≤ 2`; the `B`
absorbs the band piece. `X^exc_mono` contributes `0` (it is empty).
Every step — `Xexc_mono_eq_empty`, the `card`-subadditivity, the
orphan reduction — is genuine; nothing is `card_union_le` alone. -/
theorem Xexc_card_le_of_budget (D : ChainLiftData α) (B : ℕ)
    (hKbw : D.K_bw ≤ 2)
    (hband : (Xexc_band D).card ≤ B)
    (hAB : (syncOrphans D.fAB).card ≤ D.K_bw)
    (hAC : (syncOrphans D.fAC).card ≤ D.K_bw)
    (hBC : (syncOrphans D.fBC).card ≤ D.K_bw) :
    (Xexc D).card ≤ B + 6 := by
  have hsync : (Xexc_sync D).card ≤ (syncOrphans D.fAB).card
      + (syncOrphans D.fAC).card + (syncOrphans D.fBC).card :=
    Xexc_sync_card_le D
  have hunion : (Xexc D).card ≤ (Xexc_band D).card + (Xexc_sync D).card := by
    rw [Xexc_eq_band_union_sync]
    exact card_union_le _ _
  omega

/-! #### The contract-shaped corollary

`MA-Sig §4.1` pins `C_exc : ℕ → ℕ` (paper `C_exc(T) = 3 c_1(T)`) and
`§4.2 §E` pins the bridge `lem_layered_from_step7` to emit
`Xexc.card ≤ C_exc T`. The Step-5 constant `c_1(T)` of paper
`lem:endpoint-mono` is supplied by the (not-yet-ported) Steps-1-7
cascade; here it is modelled by the opaque constant `c₁` — an opaque
definition (no body), **not** an axiom: it does not appear in
`#print axioms` and `AXIOMS.md` is unchanged. The load-bearing
content lives in `Xexc_card_le_of_budget`, which does not mention it. -/

/-- The abstract Step-5 per-chain endpoint-exceptional constant
`c_1(T)` of paper `lem:endpoint-mono` (`step5.tex`). An opaque
`O_T(1)` cascade constant — the faithful Lean port will replace it
with the genuine Step-5 output once Piece 1 lands. -/
opaque c₁ : ℕ → ℕ

/-- **The exceptional-set size constant** `C_exc(T)` (`MA-Sig §4.1`,
`step8.tex:2054`). The paper writes `C_exc(T) = 3 c_1(T)`; the Lean
model uses the equal-order `c₁ T + 6`, where the `+6` is the
`3·K_bw ≤ 3·2` orphan contribution made explicit. Both are `O_T(1)`. -/
def C_exc (T : ℕ) : ℕ := c₁ T + 6

/-- **`ExcBudget D T`** — the genuine cascade facts the S7-F bridge
must discharge (from `hCex` + the Steps-1-7 cascade) to obtain the
`O_T(1)` cardinality bound. The bare `ChainLiftData` does **not**
imply these (it is inhabited for `Δ_ℓ`, where they fail); they encode
`lem:bandwidth` (band count) and the per-chain orphan bound. -/
structure ExcBudget (D : ChainLiftData α) (T : ℕ) : Prop where
  /-- `lem:bandwidth`, pushed to ground support: the band-exceptional
  set is `O_T(1)`. -/
  band_le : (Xexc_band D).card ≤ c₁ T
  /-- `A→B` chain-tail orphans: `≤ K_bw` (`step8.tex:2052`). -/
  orphan_AB : (syncOrphans D.fAB).card ≤ D.K_bw
  /-- `A→C` chain-tail orphans: `≤ K_bw`. -/
  orphan_AC : (syncOrphans D.fAC).card ≤ D.K_bw
  /-- `B→C` chain-tail orphans: `≤ K_bw`. -/
  orphan_BC : (syncOrphans D.fBC).card ≤ D.K_bw

/-- **Paper `lem:layered-from-step7`, item (i)** — the contract-shaped
bound `|X^exc| ≤ C_exc T` (`MA-Sig §4.2 §E`). Follows from the
concrete `Xexc_card_le_of_budget` with band budget `B := c₁ T`. -/
theorem Xexc_card_le (D : ChainLiftData α) (T : ℕ)
    (hKbw : D.K_bw ≤ 2) (h : ExcBudget D T) :
    (Xexc D).card ≤ C_exc T :=
  Xexc_card_le_of_budget D (c₁ T) hKbw h.band_le h.orphan_AB h.orphan_AC
    h.orphan_BC

/-! ### §5 — Grid discharge: a concrete, non-degenerate verification

The sub-ticket-A analogue of `f7a_chainLiftData_constructible`
(`ConcreteChainLiftData.lean`, mg-974c). On the genuine width-3
non-chain carrier `Fin 3 × Fin 3` with the F7a witness
`gridChainLiftData`:

* `X^exc` computes to the **non-empty** singleton `{(0,0)}` (card `1`)
  — the construction is non-vacuous;
* `X^exc_band` is empty (the grid satisfies `lem:bandwidth`:
  every incomparable pair is within `K_bw = 1`);
* `X^exc_sync` is `{(0,0)}` — the genuine `f_AC` chain-tail orphan;
* `ExcBudget gridChainLiftData T` holds for **every** `T`, with no
  free hypothesis;
* hence `|X^exc| ≤ C_exc T` closes unconditionally for the grid.

For `Δ_ℓ` (3 disjoint chains, empty sync maps) `ExcBudget` is *false*
— so this discharge genuinely exercises the soundness filter. -/

open GridChainLift

/-- On the grid F7a witness, `X^exc_mono` is empty (`§1`). -/
theorem grid_Xexc_mono : Xexc_mono gridChainLiftData = ∅ :=
  Xexc_mono_eq_empty _

/-- On the grid F7a witness, `X^exc_band` is empty — the grid
satisfies `lem:bandwidth` (`gridChainLiftData_bandwidth_genuine`):
every incomparable pair has chain-potential gap `≤ K_bw = 1`. -/
theorem grid_Xexc_band : Xexc_band gridChainLiftData = ∅ := by
  unfold Xexc_band
  rw [Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨y, hzy, hyz, hgap⟩
  have hb := gridChainLiftData_bandwidth_genuine z y hzy hyz
  rw [abs_le] at hb
  -- `gridChainLiftData.pot.a` is `potFun` definitionally.
  have hpa : gridChainLiftData.pot.a = potFun := rfl
  rw [hpa] at hgap
  rcases hgap with hg | hg <;> omega

/-- On the grid F7a witness, `X^exc_sync` is the genuine `f_AC`
chain-tail orphan `{(0,0)}` (`A`-index `0`, the
`gridChainLiftData_orphan_forced` element). -/
theorem grid_Xexc_sync :
    Xexc_sync gridChainLiftData = {((0 : Fin 3), (0 : Fin 3))} := by
  decide

/-- **`X^exc` on the grid is the non-empty singleton `{(0,0)}`.** The
construction is genuinely non-vacuous on a genuine carrier. -/
theorem grid_Xexc :
    Xexc gridChainLiftData = {((0 : Fin 3), (0 : Fin 3))} := by
  rw [Xexc_eq_band_union_sync, grid_Xexc_band, empty_union, grid_Xexc_sync]

/-- `|X^exc| = 1` on the grid — non-degenerate (not the empty set). -/
theorem grid_Xexc_card : (Xexc gridChainLiftData).card = 1 := by
  rw [grid_Xexc, Finset.card_singleton]

/-- **`ExcBudget` holds for the grid for every `T`**, with no free
hypothesis: the band piece is empty (`0 ≤ c₁ T`), and each
synchronization map has `≤ K_bw = 1` orphans (`f_AB`/`f_BC` total,
`f_AC` with exactly one orphan). For `Δ_ℓ` this would be false — the
discharge exercises a genuine soundness filter. -/
theorem grid_excBudget (T : ℕ) : ExcBudget gridChainLiftData T where
  band_le := by rw [grid_Xexc_band, card_empty]; exact Nat.zero_le _
  orphan_AB := by decide
  orphan_AC := by decide
  orphan_BC := by decide

/-- **Paper item (i), fully discharged on the grid F7a witness** —
`|X^exc| ≤ C_exc T` for every `T`, with no free hypothesis. The
sub-ticket-A acceptance certificate. -/
theorem grid_Xexc_card_le (T : ℕ) :
    (Xexc gridChainLiftData).card ≤ C_exc T :=
  Xexc_card_le gridChainLiftData T (by decide) (grid_excBudget T)

end Step8
end OneThird
