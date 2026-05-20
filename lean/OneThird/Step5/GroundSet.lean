/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Preorder.Chain
import OneThird.Mathlib.Poset.Dilworth
import OneThird.Step1.GroundSet

/-!
# Step 5 — G3: Dilworth decomposition selection (ground-set port)

FULL REFACTOR Phase 2, Wave-1 ticket of Piece 1 (Steps 1-6 cascade
port), per `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.1 / §5.2
under S5-B.

This file ports the **operational content of GAP G3** — paper
`lem:decomp-selection` (`step5.tex:508-619`) — grounded on the concrete
ground set of a width-3 poset: the **selection of a Dilworth
decomposition `X = A ⊔ B ⊔ C` into three chains**.

## The gap between this file and the abstract `decomp_selection`

`OneThird.Step5.decomp_selection` (`FiberMass.lean:69`) is the
*bookkeeping half* of G3: given three `TripleMono` records — one per
ordered triple `(A,B|C)`, `(A,C|B)`, `(B,C|A)` — it observes that they
hold *simultaneously* under the exact-monotone form of G1 (`step5.tex`
remark: *"the trivial partition works and `E := ∅` suffices for all
three ordered triples simultaneously"*). But that lemma **presupposes
the three chains `A, B, C` as already-given data** — it never
constructs them.

This file supplies the missing *constructive half*: the actual
three-chain split. For a width-≤3 finite poset `α`, Dilworth's theorem
(`OneThird.Mathlib.Poset.hasChainCover_of_hasWidth`) yields a cover of
`α` by three chains; `selectDilworthDecomp` *selects* one and packages
it as a `DilworthDecomp α`. The three chains genuinely **partition**
the ground set (`chains_cover`, `card_partition`) — losing **zero**
elements, which is the `E = ∅` content of the paper's G3 in the
exact-G1 regime made concrete. Because there are exactly three named
chains, a single decomposition serves all three ordered triples
`(A,B|C)`, `(A,C|B)`, `(B,C|A)` at once — the structural point of the
paper's "single common refinement `R*`".

## Main definitions

* `OneThird.Step5.DilworthDecomp` — a decomposition of `α` into three
  chains, presented as a band function `band : α → Fin 3` whose fibers
  are chains. The three chains are `D.A`, `D.B`, `D.C`.
* `OneThird.Step5.selectDilworthDecomp` — the G3 selection: a width-≤3
  poset gets a chosen three-chain decomposition.

## Main results

* `OneThird.Step5.DilworthDecomp.chains_cover` — `A ∪ B ∪ C = univ`:
  the three chains cover the whole ground set.
* `OneThird.Step5.DilworthDecomp.card_partition` —
  `|A| + |B| + |C| = |α|`: the cover is a genuine partition, losing
  zero elements (`E = ∅`).
* `OneThird.Step5.decomp_selection_groundSet` — **the G3 grounded
  port**: every width-3 non-chain poset admits a Dilworth
  decomposition `X = A ⊔ B ⊔ C` partitioning the ground set, with at
  least two nonempty chains (the non-chain hypothesis is load-bearing
  here).

## Non-triviality witnesses

Per the mg-f268 acceptance bar, the port instantiates non-vacuously at
two concrete width-3 non-chain posets — no Subsingleton-on-empty
baseline:

* `OneThird.Antichain3.decomp_selection_nonvacuous` — the 3-element
  antichain decomposes into three nonempty singleton chains.
* `OneThird.Step5.Chain2Iso2.decomp_has_genuine_two_chain` — a
  4-element width-3 poset (`0 < 1`, two isolated points) whose G3
  decomposition genuinely contains a chain of length `≥ 2`, exercising
  the non-singleton-chain case of the mechanism.
-/

open Finset

namespace OneThird
namespace Step5

open OneThird.Mathlib.Poset

variable {α : Type*}

/-! ### §1 — The three-chain decomposition structure -/

/-- **A Dilworth decomposition of `α` into three chains.**

The decomposition is presented as a *band function* `band : α → Fin 3`
whose three fibers `{x | band x = i}` are each chains. This is exactly
the data of `OneThird.Mathlib.Poset.HasChainCover α 3`, packaged as a
structure so the three chains `A = band⁻¹{0}`, `B = band⁻¹{1}`,
`C = band⁻¹{2}` are named and reusable.

Paper `step5.tex:511-516`: the Dilworth decomposition
`P = A ⊔ B ⊔ C`. The band function makes the partition automatic:
every element lands in exactly one fiber. -/
structure DilworthDecomp (α : Type*) [PartialOrder α] where
  /-- The chain-assignment function: which of the three chains an
  element belongs to. -/
  band : α → Fin 3
  /-- Each fiber of `band` is a chain in `α`. -/
  band_isChain : ∀ i : Fin 3, IsChain (· ≤ ·) ({x | band x = i} : Set α)

namespace DilworthDecomp

variable [PartialOrder α]

/-- Package a `HasChainCover α 3` witness as a `DilworthDecomp`. -/
noncomputable def ofHasChainCover (h : HasChainCover α 3) : DilworthDecomp α :=
  ⟨h.choose, h.choose_spec⟩

/-- If two elements share a band, they are comparable (they lie in a
common chain). Contrapositive of `incomp_band_ne`. -/
lemma comparable_of_band_eq (D : DilworthDecomp α) {x y : α}
    (hxy : x ≠ y) (hb : D.band x = D.band y) : x ≤ y ∨ y ≤ x := by
  have hchain := D.band_isChain (D.band x)
  have hx : x ∈ ({z | D.band z = D.band x} : Set α) := rfl
  have hy : y ∈ ({z | D.band z = D.band x} : Set α) := hb.symm
  exact hchain hx hy hxy

/-- **Incomparable elements get distinct bands.** An incomparable pair
cannot lie in a common chain, so the band function separates it. -/
lemma incomp_band_ne (D : DilworthDecomp α) {x y : α} (h : x ∥ y) :
    D.band x ≠ D.band y := by
  intro hb
  have hxy : x ≠ y := by rintro rfl; exact h.1 (le_refl x)
  rcases D.comparable_of_band_eq hxy hb with hle | hle
  · exact h.1 hle
  · exact h.2 hle

variable [Fintype α]

/-- The `i`-th chain of the decomposition, as a `Finset α`. -/
def chain (D : DilworthDecomp α) (i : Fin 3) : Finset α :=
  Finset.univ.filter (fun x => D.band x = i)

/-- The first chain `A` of the Dilworth decomposition `X = A ⊔ B ⊔ C`. -/
abbrev A (D : DilworthDecomp α) : Finset α := D.chain 0
/-- The second chain `B` of the Dilworth decomposition `X = A ⊔ B ⊔ C`. -/
abbrev B (D : DilworthDecomp α) : Finset α := D.chain 1
/-- The third chain `C` of the Dilworth decomposition `X = A ⊔ B ⊔ C`. -/
abbrev C (D : DilworthDecomp α) : Finset α := D.chain 2

@[simp] lemma mem_chain {D : DilworthDecomp α} {i : Fin 3} {x : α} :
    x ∈ D.chain i ↔ D.band x = i := by
  simp [DilworthDecomp.chain]

/-- The `i`-th chain, coerced to a `Set`, is the `band`-fiber. -/
lemma coe_chain (D : DilworthDecomp α) (i : Fin 3) :
    (↑(D.chain i) : Set α) = {x | D.band x = i} := by
  ext x; simp

/-- **Each chain of the decomposition is genuinely a chain.** -/
lemma chain_isChain (D : DilworthDecomp α) (i : Fin 3) :
    IsChain (· ≤ ·) (↑(D.chain i) : Set α) := by
  rw [D.coe_chain i]; exact D.band_isChain i

/-- **The three chains are pairwise disjoint** — distinct fibers of the
band function never meet. -/
lemma chain_disjoint (D : DilworthDecomp α) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (D.chain i) (D.chain j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_chain] at hxi hxj
  exact hij (hxi.symm.trans hxj)

/-- **The three chains cover the whole ground set** (`A ∪ B ∪ C = X`).

This is the `E = ∅` content of paper G3 in the exact-G1 regime: no
element is lost to an exceptional set. -/
lemma chains_cover [DecidableEq α] (D : DilworthDecomp α) :
    D.A ∪ D.B ∪ D.C = Finset.univ := by
  have hfin : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  ext x
  simp only [Finset.mem_union, Finset.mem_univ, iff_true, DilworthDecomp.A,
    DilworthDecomp.B, DilworthDecomp.C, mem_chain]
  have h3 := hfin (D.band x)
  tauto

/-- **The decomposition is a genuine partition** — the three chain
cardinalities sum to `|α|`. Together with `chain_disjoint` and
`chains_cover`, this is the exact `X = A ⊔ B ⊔ C` split, losing zero
elements. -/
lemma card_partition (D : DilworthDecomp α) :
    (D.chain 0).card + (D.chain 1).card + (D.chain 2).card =
      Fintype.card α := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset (Fin 3)))
    (f := D.band) (fun x _ => Finset.mem_univ _)
  rw [Fin.sum_univ_three] at h
  rw [Finset.card_univ] at h
  simpa [DilworthDecomp.chain] using h.symm

end DilworthDecomp

/-! ### §2 — The G3 selection -/

variable [PartialOrder α] [Fintype α] [DecidableEq α]

/-- A width-≤3 finite poset admits a chain cover of size 3 — the
existence half of Dilworth's theorem, specialised to width 3. -/
theorem hasChainCover_three_of_widthAtMost (hP : HasWidthAtMost α 3) :
    HasChainCover α 3 :=
  hasChainCover_width.mono (hasWidthAtMost_iff_width_le.mp hP)

/-- **G3 selection.** Given a width-≤3 finite poset, *select* a
Dilworth decomposition `X = A ⊔ B ⊔ C` into three chains.

This is the constructive heart of paper `lem:decomp-selection`: by
Dilworth's theorem the poset splits into three chains, and we fix one
such split "once and for all" (`step5.tex:198-202`) so that all three
ordered triples are served by the same chains. The choice is
noncomputable (it goes through `Exists.choose`). -/
noncomputable def selectDilworthDecomp (hP : HasWidthAtMost α 3) :
    DilworthDecomp α :=
  DilworthDecomp.ofHasChainCover (hasChainCover_three_of_widthAtMost hP)

/-- **GAP G3, ground-set port** (`lem:decomp-selection`, `step5.tex:508`).

Every width-3 non-chain poset `α` admits a Dilworth decomposition
`X = A ⊔ B ⊔ C` into three chains such that:

* the three chains **cover the whole ground set** (`A ∪ B ∪ C = X`);
* the cover is a genuine **partition** (`|A| + |B| + |C| = |X|`),
  losing **zero** elements — the `E = ∅` content of paper G3;
* at least **two** of the chains are nonempty.

The `¬ IsChainPoset α` hypothesis is **load-bearing**: it is exactly
what forces two of the three chains to be nonempty (a non-chain poset
has an incomparable pair, which `incomp_band_ne` splits across two
distinct chains). For a chain poset the decomposition still exists but
could place every element in a single chain. -/
theorem decomp_selection_groundSet (hP : HasWidthAtMost α 3)
    (hNonChain : ¬ IsChainPoset α) :
    ∃ D : DilworthDecomp α,
      (D.A ∪ D.B ∪ D.C = Finset.univ) ∧
      ((D.chain 0).card + (D.chain 1).card + (D.chain 2).card =
        Fintype.card α) ∧
      (∃ i j : Fin 3, i ≠ j ∧
        (D.chain i).Nonempty ∧ (D.chain j).Nonempty) := by
  refine ⟨selectDilworthDecomp hP, ?_, ?_, ?_⟩
  · exact (selectDilworthDecomp hP).chains_cover
  · exact (selectDilworthDecomp hP).card_partition
  · -- A non-chain poset has an incomparable pair; the band function
    -- separates it across two distinct (hence nonempty) chains.
    set D := selectDilworthDecomp hP with hD
    simp only [IsChainPoset, not_forall, not_or] at hNonChain
    obtain ⟨u, v, huv, hvu⟩ := hNonChain
    have hpar : u ∥ v := ⟨huv, hvu⟩
    refine ⟨D.band u, D.band v, D.incomp_band_ne hpar, ⟨u, ?_⟩, ⟨v, ?_⟩⟩
    · simp
    · simp

end Step5

/-! ### §3 — Non-triviality witness: the 3-element antichain

Per the mg-f268 acceptance bar, the G3 port must instantiate
non-vacuously at a concrete width-3 non-chain poset. The minimal such
poset is `OneThird.Antichain3` (from `Step1/GroundSet.lean`), the
3-element antichain. Its unique Dilworth decomposition is the three
singleton chains. -/

namespace Antichain3

open OneThird.Step5

/-- The explicit Dilworth decomposition of the 3-element antichain:
the identity band function, whose three fibers are the three
singletons `{a0}`, `{a1}`, `{a2}`. -/
def decomp : Step5.DilworthDecomp Antichain3 where
  band := fun x => x
  band_isChain := by
    intro i
    apply Set.Subsingleton.isChain
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    exact ha.trans hb.symm

/-- **G3 non-triviality witness at `Antichain3`.**

The 3-element antichain is a genuine width-3 non-chain poset (no
Subsingleton-on-empty degeneracy), and `decomp` partitions it into
three nonempty singleton chains, covering the whole ground set and
losing zero elements. -/
theorem decomp_selection_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    (decomp.A ∪ decomp.B ∪ decomp.C = Finset.univ) ∧
    (decomp.A.card + decomp.B.card + decomp.C.card = 3) ∧
    decomp.A.Nonempty ∧ decomp.B.Nonempty ∧ decomp.C.Nonempty ∧
    (∀ i : Fin 3, (decomp.chain i).card = 1) := by
  refine ⟨hasWidth, not_isChainPoset, decomp.chains_cover, ?_, ?_, ?_, ?_, ?_⟩
  · have h := decomp.card_partition
    rwa [card_eq] at h
  · decide
  · decide
  · decide
  · decide

/-- The general G3 port `decomp_selection_groundSet` **fires** at the
concrete width-3 non-chain poset `Antichain3` — confirming the port is
non-vacuously applicable, not merely type-correct. -/
theorem decomp_selection_groundSet_applies :
    ∃ D : Step5.DilworthDecomp Antichain3,
      (D.A ∪ D.B ∪ D.C = Finset.univ) ∧
      ((D.chain 0).card + (D.chain 1).card + (D.chain 2).card =
        Fintype.card Antichain3) ∧
      (∃ i j : Fin 3, i ≠ j ∧
        (D.chain i).Nonempty ∧ (D.chain j).Nonempty) :=
  Step5.decomp_selection_groundSet hasWidthAtMost not_isChainPoset

end Antichain3

/-! ### §4 — Non-triviality witness: a width-3 poset with a genuine
2-element chain

`Antichain3`'s decomposition has only singleton chains. To exercise
the non-singleton-chain case of the G3 mechanism, we use a 4-element
width-3 poset `Chain2Iso2`: a 2-element chain `0 < 1` together with two
isolated points `2`, `3`. Any G3 decomposition of it must place a
chain of length `≥ 2` (three chains, four elements, pigeonhole). -/

namespace Step5

/-- A 4-element width-3 poset: a 2-element chain `0 < 1` plus two
isolated points. Carrier `Fin 4`. -/
def Chain2Iso2 : Type := Fin 4

namespace Chain2Iso2

instance : DecidableEq Chain2Iso2 := inferInstanceAs (DecidableEq (Fin 4))

instance : Fintype Chain2Iso2 := inferInstanceAs (Fintype (Fin 4))

instance (n : ℕ) : OfNat Chain2Iso2 n := inferInstanceAs (OfNat (Fin 4) n)

/-- The order relation: reflexive, with the single strict relation
`0 < 1`. The elements `2` and `3` are isolated. -/
protected def le (x y : Chain2Iso2) : Prop :=
  x = y ∨ (x = (0 : Fin 4) ∧ y = (1 : Fin 4))

instance : PartialOrder Chain2Iso2 where
  le := Chain2Iso2.le
  le_refl _ := Or.inl rfl
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | ⟨hx0, hy1⟩
    · exact hyz
    · rcases hyz with rfl | ⟨hy0, _⟩
      · exact Or.inr ⟨hx0, hy1⟩
      · exact absurd (hy1.symm.trans hy0) (by decide)
  le_antisymm x y hxy hyx := by
    rcases hxy with rfl | ⟨hx0, hy1⟩
    · rfl
    · rcases hyx with rfl | ⟨hy0, _⟩
      · rfl
      · exact absurd (hy1.symm.trans hy0) (by decide)

instance (x y : Chain2Iso2) : Decidable (x ≤ y) :=
  if h : x = y ∨ (x = (0 : Fin 4) ∧ y = (1 : Fin 4)) then
    isTrue h
  else
    isFalse h

/-- `Chain2Iso2` has exactly four elements. -/
lemma card_eq : Fintype.card Chain2Iso2 = 4 := by decide

/-- `Chain2Iso2` is not a chain: the isolated points `2` and `3` are
incomparable. -/
theorem not_isChainPoset : ¬ IsChainPoset Chain2Iso2 := by
  intro h
  rcases h 2 3 with hle | hle
  · exact absurd hle (by decide)
  · exact absurd hle (by decide)

/-- `Chain2Iso2` has width at most 3: it has 4 elements but the whole
universe is not an antichain (`0 < 1`), so no antichain reaches size
4. -/
theorem hasWidthAtMost : HasWidthAtMost Chain2Iso2 3 := by
  intro s hs
  by_contra hcard
  push_neg at hcard
  have hs4 : s.card = 4 := by
    have hle := Finset.card_le_univ s
    rw [card_eq] at hle
    omega
  have huniv : s = Finset.univ :=
    Finset.eq_univ_of_card s (by rw [hs4, card_eq])
  subst huniv
  have h01 : (0 : Chain2Iso2) ≤ (1 : Chain2Iso2) := Or.inr ⟨rfl, rfl⟩
  exact hs (by simp) (by simp) (by decide) h01

/-- `Chain2Iso2` has width exactly 3: `{1, 2, 3}` is an antichain of
size 3. -/
theorem hasWidth : HasWidth Chain2Iso2 3 := by
  refine ⟨hasWidthAtMost, {1, 2, 3}, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha hb
    intro hle
    rcases hle with h | ⟨h0, _⟩
    · exact hab h
    · rcases ha with rfl | rfl | rfl <;> exact absurd h0 (by decide)
  · decide

/-- **G3 non-triviality witness at `Chain2Iso2`.**

The G3 port `decomp_selection_groundSet` fires at this 4-element
width-3 non-chain poset and produces a decomposition that genuinely
contains a chain of length `≥ 2` — exercising the non-singleton-chain
case of the mechanism. (Three chains partition four elements, so
pigeonhole forces one chain to length `≥ 2`; that chain is a genuine
`≤`-chain by `chain_isChain`.) -/
theorem decomp_has_genuine_two_chain :
    ∃ D : DilworthDecomp Chain2Iso2, ∃ i : Fin 3,
      2 ≤ (D.chain i).card ∧
      IsChain (· ≤ ·) (↑(D.chain i) : Set Chain2Iso2) := by
  obtain ⟨D, _, hcard, _⟩ :=
    decomp_selection_groundSet hasWidthAtMost not_isChainPoset
  rw [card_eq] at hcard
  have hsplit : 2 ≤ (D.chain 0).card ∨ 2 ≤ (D.chain 1).card ∨
      2 ≤ (D.chain 2).card := by omega
  rcases hsplit with h | h | h
  · exact ⟨D, 0, h, D.chain_isChain 0⟩
  · exact ⟨D, 1, h, D.chain_isChain 1⟩
  · exact ⟨D, 2, h, D.chain_isChain 2⟩

end Chain2Iso2

end Step5

end OneThird
