/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.Poset.Dilworth
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Chain potentials infrastructure for A5's ground-set lift

This file provides the Lean structural content consumed by
`lem:layered-from-step7` (`step8.tex:1913-2106`, GAP G2-A5). It
formalises the paper-level ingredients that `rem:layered-from-step7`
treats informally:

* **Indexed Dilworth chains** `A = (a_1, a_2, …)` etc., strictly
  monotone sequences covering the ground set (`step7.tex:1001-1003`);
* **Synchronization maps** `f_{AB}, f_{AC}, f_{BC}` — weakly
  monotone *partial* maps between chain indices
  (`step7.tex:1009-1012`);
* **Chain-monotone potential** `a : α → ℤ` — strictly increasing
  along each Dilworth chain (`step7.tex:1004-1013`), in the
  cleared-denominator integer form matching
  `Step7.PotentialData.pot` (`lean/OneThird/Step7/Potential.lean:115`);
* **Bandwidth constant** `K_bw : ℕ` from `lem:bandwidth`
  (`step7.tex:1018-1027`).

The paper's lift `rem:layered-from-step7` (`step8.tex:1913-2106`)
consumes these together with the perturbation bounds
`lem:one-elem-perturb` (F6a, `mg-1f5e`) and `lem:exc-perturb`
(F6b, `mg-7496`) to replace the vacuous `layeredFromBridges` of
`MainAssembly.lean` with a tight bounded-`w` `LayeredDecomposition`.
This file provides only the structural ingredients; the
constructive lift is F7 (`mg-f1b7`).

## Main definitions

* `IndexedChain α` — a strictly monotone `Fin n → α`.
* `ChainTriple α` — three `IndexedChain`s that cover `α`.
* `SyncMap nA nB` — a *partial* weakly monotone `Fin nA → Option (Fin nB)`.
* `ChainPotential T` — an integer potential strictly monotone on
  each chain of a `ChainTriple T`.
* `ChainLiftData α` — the bundle `(triple, pot, K_bw, fAB, fAC, fBC)`.

## Main results

* `IndexedChain.support_isChain` — the image of an indexed chain is
  a chain under `≤`.
* `ChainTriple.card_le_sum_lengths` — the three chain lengths sum
  covers `|α|`.
* `ChainTriple.exists_long_chain` — pigeonhole: some chain has
  length `≥ |α|/3`.

No new axioms or sorries are introduced.
-/

namespace OneThird
namespace Step8

/-! ### §1 — Indexed Dilworth chains -/

/-- **Indexed chain** (`step7.tex:1001-1003`).

A strictly monotone sequence `a_0, a_1, …, a_{length-1}` in a
partially ordered type. The paper writes
`(a_1 <_P a_2 <_P ⋯)` for such a sequence; here the indexing is
`0`-based (`Fin length`), matching Lean convention. -/
structure IndexedChain (α : Type*) [PartialOrder α] where
  /-- Chain length. -/
  length : ℕ
  /-- Chain elements, indexed by `Fin length`. -/
  elem : Fin length → α
  /-- Strict monotonicity: `i < j ⇒ elem i < elem j`. -/
  strictMono : StrictMono elem

namespace IndexedChain

variable {α : Type*} [PartialOrder α]

/-- The underlying set of an `IndexedChain` as a `Finset`. -/
noncomputable def support (C : IndexedChain α) : Finset α := by
  classical
  exact (Finset.univ : Finset (Fin C.length)).image C.elem

lemma elem_injective (C : IndexedChain α) : Function.Injective C.elem :=
  C.strictMono.injective

@[simp] lemma mem_support {C : IndexedChain α} {x : α} :
    x ∈ C.support ↔ ∃ i : Fin C.length, C.elem i = x := by
  classical
  simp [support]

lemma card_support (C : IndexedChain α) : C.support.card = C.length := by
  classical
  rw [support, Finset.card_image_of_injective _ C.elem_injective]
  simp

/-- The support of an `IndexedChain` is a chain under `≤`. -/
lemma support_isChain (C : IndexedChain α) :
    IsChain (· ≤ ·) (C.support : Set α) := by
  classical
  intro x hx y hy hne
  simp only [support, Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inl (C.strictMono hij).le
  · exact absurd (congrArg C.elem hij) hne
  · exact Or.inr (C.strictMono hij).le

/-- Strict monotonicity in `Fin` order is equivalent to strict
monotonicity in `≤`-order on elements. -/
lemma elem_lt_elem {C : IndexedChain α} {i j : Fin C.length} (h : i < j) :
    C.elem i < C.elem j :=
  C.strictMono h

end IndexedChain

/-! ### §2 — Chain triple covering the ground set -/

/-- **Three-chain Dilworth cover** (`step7.tex:1001`).

Three indexed chains `A`, `B`, `C` whose supports cover every
element of `α`. This matches Dilworth's theorem for width ≤ 3:
every such poset splits into three chains. Chains may be empty and
are not required to be pairwise disjoint at this data level —
`rem:layered-from-step7` (`step8.tex:1931-1950`) achieves partition
via the exceptional set `X^{exc}`, which is a separate construction. -/
structure ChainTriple (α : Type*) [PartialOrder α] [Fintype α] where
  /-- Chain `A`. -/
  A : IndexedChain α
  /-- Chain `B`. -/
  B : IndexedChain α
  /-- Chain `C`. -/
  C : IndexedChain α
  /-- Every ground-set element appears in at least one chain. -/
  cover : ∀ x : α,
    (∃ i : Fin A.length, A.elem i = x) ∨
    (∃ j : Fin B.length, B.elem j = x) ∨
    (∃ k : Fin C.length, C.elem k = x)

namespace ChainTriple

variable {α : Type*} [PartialOrder α] [Fintype α] (T : ChainTriple α)

/-- The sum of the three chain lengths is at least `|α|`. -/
lemma card_le_sum_lengths :
    Fintype.card α ≤ T.A.length + T.B.length + T.C.length := by
  classical
  set SA : Finset α := T.A.support
  set SB : Finset α := T.B.support
  set SC : Finset α := T.C.support
  have hcover : (Finset.univ : Finset α) ⊆ SA ∪ SB ∪ SC := by
    intro x _
    rcases T.cover x with hA | hB | hC
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inl (IndexedChain.mem_support.mpr hA))))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr
          (Or.inr (IndexedChain.mem_support.mpr hB))))
    · exact Finset.mem_union.mpr
        (Or.inr (IndexedChain.mem_support.mpr hC))
  have hcard : (Finset.univ : Finset α).card ≤ (SA ∪ SB ∪ SC).card :=
    Finset.card_le_card hcover
  have hU1 : (SA ∪ SB ∪ SC).card ≤ (SA ∪ SB).card + SC.card :=
    Finset.card_union_le _ _
  have hU2 : (SA ∪ SB).card ≤ SA.card + SB.card :=
    Finset.card_union_le _ _
  have hCardA : SA.card = T.A.length := IndexedChain.card_support _
  have hCardB : SB.card = T.B.length := IndexedChain.card_support _
  have hCardC : SC.card = T.C.length := IndexedChain.card_support _
  have hUniv : Fintype.card α = (Finset.univ : Finset α).card := by
    simp [Finset.card_univ]
  omega

/-- Pigeonhole: the longest of the three chains has length ≥ `⌈|α|/3⌉`.
We state this in the cleared-denominator form
`|α| ≤ 3 · max(|A|, |B|, |C|)`. -/
lemma exists_long_chain :
    Fintype.card α ≤
      3 * max (max T.A.length T.B.length) T.C.length := by
  have h := T.card_le_sum_lengths
  have h1 : T.A.length ≤ max (max T.A.length T.B.length) T.C.length :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have h2 : T.B.length ≤ max (max T.A.length T.B.length) T.C.length :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have h3 : T.C.length ≤ max (max T.A.length T.B.length) T.C.length :=
    le_max_right _ _
  omega

end ChainTriple

/-! ### §3 — Synchronization maps -/

/-- **Synchronization map** (`step7.tex:1009-1012`).

A *partial* weakly monotone function between two chain index sets
`Fin nA → Option (Fin nB)`. The paper's
`f_{AB}(i) := argmin_j |a(a_i) - a(b_j)|` is such a map: weakly
monotone when the potential is strictly increasing on each chain,
partial for chain-tail orphans (the `X^{exc}_{sync}` of
`step8.tex:1948-1950`).

* `partner i = none` records a chain-tail orphan.
* `partner i = some j` records partner index `j`, with
  `weakly_monotone` enforcing `i ≤ i' ⇒ j ≤ j'` on defined indices. -/
structure SyncMap (nA nB : ℕ) where
  /-- Partner map, partial. -/
  partner : Fin nA → Option (Fin nB)
  /-- Weak monotonicity on the defined subset of indices. -/
  weakly_monotone :
    ∀ i i' : Fin nA, i ≤ i' →
    ∀ j : Fin nB, partner i = some j →
    ∀ j' : Fin nB, partner i' = some j' →
    j ≤ j'

namespace SyncMap

variable {nA nB : ℕ}

/-- Domain of a sync map: indices with a defined partner. -/
def domain (f : SyncMap nA nB) : Finset (Fin nA) :=
  (Finset.univ : Finset (Fin nA)).filter (fun i => (f.partner i).isSome)

@[simp] lemma mem_domain {f : SyncMap nA nB} {i : Fin nA} :
    i ∈ f.domain ↔ (f.partner i).isSome := by
  simp [domain]

/-- The *trivial* sync map: everywhere undefined. Demonstrates
`SyncMap` is nonempty for every pair of lengths. The paper's
`rem:layered-from-step7` never uses this map as a witness, but it
serves as a base constructor and closes the type under "no sync
information available". -/
def empty (nA nB : ℕ) : SyncMap nA nB where
  partner _ := none
  weakly_monotone := by
    intro _ _ _ _ hij _ _
    exact absurd hij (by simp)

@[simp] lemma empty_partner (i : Fin nA) : (empty nA nB).partner i = none := rfl

@[simp] lemma empty_domain : (empty nA nB).domain = ∅ := by
  classical
  apply Finset.ext
  intro i
  simp [mem_domain]

end SyncMap

/-! ### §4 — Chain-monotone potential -/

/-- **Chain-monotone potential** (`step7.tex:1004-1013`).

A potential `a : α → ℤ` that is strictly increasing along each
chain of a `ChainTriple`. The paper's Prop. 7.1 guarantees this
after removing the `o(1)`-mass exceptional set `X^{exc}_{mono}` of
`step8.tex:1944-1946`; after this removal the chain-monotone
property holds exactly.

The integer-valued potential matches the cleared-denominator form
of `Step7.PotentialData.pot : Vertex → ℤ`
(`lean/OneThird/Step7/Potential.lean:115`). -/
structure ChainPotential {α : Type*} [PartialOrder α] [Fintype α]
    (T : ChainTriple α) where
  /-- Element potential `a : α → ℤ`. -/
  a : α → ℤ
  /-- Strict monotone along chain `A`. -/
  strictMonoA : StrictMono fun i : Fin T.A.length => a (T.A.elem i)
  /-- Strict monotone along chain `B`. -/
  strictMonoB : StrictMono fun i : Fin T.B.length => a (T.B.elem i)
  /-- Strict monotone along chain `C`. -/
  strictMonoC : StrictMono fun i : Fin T.C.length => a (T.C.elem i)

namespace ChainPotential

variable {α : Type*} [PartialOrder α] [Fintype α] {T : ChainTriple α}

/-- The potential is injective on each chain (as indexed by `Fin _`). -/
lemma injective_on_A (P : ChainPotential T) :
    Function.Injective fun i : Fin T.A.length => P.a (T.A.elem i) :=
  P.strictMonoA.injective

lemma injective_on_B (P : ChainPotential T) :
    Function.Injective fun i : Fin T.B.length => P.a (T.B.elem i) :=
  P.strictMonoB.injective

lemma injective_on_C (P : ChainPotential T) :
    Function.Injective fun i : Fin T.C.length => P.a (T.C.elem i) :=
  P.strictMonoC.injective

/-- Along chain `A`, the potential respects the poset order
(since chain elements are `≤`-comparable and the potential is
strictly monotone in the chain index). -/
lemma a_lt_of_index_lt_A (P : ChainPotential T) {i j : Fin T.A.length}
    (h : i < j) : P.a (T.A.elem i) < P.a (T.A.elem j) :=
  P.strictMonoA h

lemma a_lt_of_index_lt_B (P : ChainPotential T) {i j : Fin T.B.length}
    (h : i < j) : P.a (T.B.elem i) < P.a (T.B.elem j) :=
  P.strictMonoB h

lemma a_lt_of_index_lt_C (P : ChainPotential T) {i j : Fin T.C.length}
    (h : i < j) : P.a (T.C.elem i) < P.a (T.C.elem j) :=
  P.strictMonoC h

end ChainPotential

/-! ### §5 — Lift infrastructure bundle -/

/-- **Ground-set lift infrastructure bundle** — the data package
consumed by `rem:layered-from-step7` (`step8.tex:1913-2106`).

Consists of:

* a `ChainTriple α` — three Dilworth chains covering `α`;
* a `ChainPotential` — strictly monotone along each chain;
* a bandwidth constant `K_bw : ℕ` from `lem:bandwidth`;
* three partial sync maps `fAB, fAC, fBC` between chain indices.

The structural content here supplies the ingredients the paper's
lift uses at `step8.tex:1913-1940`. The constructive lift that
builds a tight bounded-`w` `LayeredDecomposition` from this data
and the F6a/F6b perturbation bounds is F7 (`mg-f1b7`). -/
structure ChainLiftData (α : Type*) [PartialOrder α] [Fintype α] where
  /-- Dilworth chain triple covering `α`. -/
  triple : ChainTriple α
  /-- Chain-monotone potential. -/
  pot : ChainPotential triple
  /-- Bandwidth constant `K_bw` from `lem:bandwidth`. -/
  K_bw : ℕ
  /-- Sync map from chain `A` to chain `B`. -/
  fAB : SyncMap triple.A.length triple.B.length
  /-- Sync map from chain `A` to chain `C`. -/
  fAC : SyncMap triple.A.length triple.C.length
  /-- Sync map from chain `B` to chain `C`. -/
  fBC : SyncMap triple.B.length triple.C.length

namespace ChainLiftData

variable {α : Type*} [PartialOrder α] [Fintype α] (D : ChainLiftData α)

/-- Pigeonhole inherited from the chain triple: some chain has
length ≥ `|α| / 3`. -/
lemma exists_long_chain :
    Fintype.card α ≤
      3 * max (max D.triple.A.length D.triple.B.length)
        D.triple.C.length :=
  D.triple.exists_long_chain

/-- The total length across the three chains is at least `|α|`. -/
lemma card_le_sum_lengths :
    Fintype.card α ≤
      D.triple.A.length + D.triple.B.length + D.triple.C.length :=
  D.triple.card_le_sum_lengths

end ChainLiftData

end Step8
end OneThird
