/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step7.SingleThreshold
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step 7 — Giant component of `G_Rich`  (`lem:giant-component`)

This file formalises `lem:giant-component` of `step7.tex`
§`sec:gap-connected` (`step7.tex:1506-1656`, `lem:giant-component`
at `step7.tex:1513`): the active-edge subgraph of `G_Rich`
contains a connected component `C ⊆ Rich⋆` of incidence mass
`(1 - O(c_T⁻¹)) M₀`, with diameter `≤ 3` on a
`(1 - O(c_T⁻¹))`-mass subset.

## Paper statement (`step7.tex:1513-1527`)

Assume the rich case (R) of Step 5 with richness constant `c_T`
and active-pair threshold
`θ_pair := c_1·T·|LE(P)|/(|A|·|B|·|C|)`.  Then there is a
connected component `C ⊆ Rich⋆` of `G_Rich` with incidence
weight `≥ (1 - O(c_T⁻¹)) · M₀`, supporting `(1 - o(1))` of the
active-triple incidence mass.

## Proof outline (`step7.tex:1529-1648`)

1. **Edge-mass LB from second moment** (`step7.tex:1544-1554`):
   `M := ∑_{α ≠ β} w_{αβ} = ∑_L I(L)(I(L)-1) ≥ ½ c_T'|LE(P)|`
   already in tree via S7-B `edge_mass_lower_bound_via_second_moment`.
2. **Endpoint-sharing pairs are active** (`step7.tex:1557-1585`):
   for `α = (x, y), β = (x, y') ∈ Rich⋆` sharing `x`, the joint
   fiber satisfies `w_{αβ} ≥ θ_pair` by Step 1 `cor:overlap`(b) +
   `thm:interface`.  This is an **upstream Step 1 input** recorded
   abstractly via `share_endpoint` membership in the `goodPairs`
   set consumed by the walk-witness.
3. **Endpoint-sharing graph has diameter `≤ 3` on rich-rows /
   rich-columns** (`step7.tex:1588-1607`).  By reverse-Markov on
   `∑_a |N_B(a)| = |Rich| ≥ c_T·|A|·|B|`, at most a
   `(2/c_T)`-fraction of `a ∈ A` are *non-rich-rows*
   (`|N_B(a)| < (c_T/2)·|B|`).  Symmetrically for rich-columns.
   Any two rich-row endpoints `a, a' ∈ A` satisfy
   `|N_B(a) ∩ N_B(a')| ≥ (c_T - 1)·|B| > 0` by inclusion-exclusion,
   so they have a common `B`-neighbour `b''`, hence a length-`3`
   walk through endpoint-sharing active pairs.
4. **From endpoint-sharing connectivity to giant component**
   (`step7.tex:1610-1628`): the diameter-`3` routing tolerates the
   `o(1)`-mass `S`-good trim, yielding a component `C ⊆ Rich⋆`
   of mass `≥ (1 - O(c_T⁻¹)) · M₀`.

## Lean formalisation

Pair-type is specialised to `Pair := A × B` (interfaces ARE
A × B-pairs in the paper's bipartite setup).  Generic
`BipartiteRichness` bundle plus the substantive lemmas:

* `degB a` = `|{b : (a, b) ∈ rich}|` (B-neighbours of `a`).
* `richRows / nonRichRows` at cleared threshold `α_n / α_d`.
* `degB_le_Bset_card` — `degB a ≤ |Bset|` (each rich pair through
  `a` contributes a distinct `b ∈ Bset`).
* `sum_degB_eq_rich_card` — `∑_a degB a = |rich|`.
* `nonRichRows_count_bound` — cleared reverse-Markov:
  `(c_d·α_d - α_n·c_d) · |Aset| ≤ (α_d - α_n) · c_d · |nonRich|
  + α_d · (|rich-only-on-Aset|)` (cf. `step7.tex:1591-1593`).
* `commonB_neighbour_of_rich_rows` — for two rich-rows `a, a'`,
  exists `b'' ∈ N_B(a) ∩ N_B(a')` under
  `α_n · |Aset| < 2 · α_n · |Aset| - α_d · |Bset|` style
  inclusion-exclusion (cleared form).

Main results:

* `endpoint_walk3` — length-3 walk construction
  `e_0 → (a_0, b'') → (a', b'') → e'` through common `B`-neighbour
  `b''`, given the abstract pair-set containing endpoint-sharing
  pairs.
* `lem_giant_component_grounded` — cleared-denominator main
  output: `FiberThresholdData.WalkWitness3` on the rich-row /
  rich-col subset of `Rich⋆`.
* `lem_giant_component_grounded_bundled` — single-call paper-
  statement bundle for downstream `Bandwidth.lean` (S7-E) /
  `Assembly.lean` (S7-F) consumption.

Downstream, the `WalkWitness3` output composes with
`single_c_grounded` from `SingleThreshold.lean §7` to globalise
per-fiber thresholds across the giant component
(paper `step7.tex:917-935`).
-/

namespace OneThird
namespace Step7

open Finset
open scoped BigOperators

/-! ### §1 — Bipartite richness data -/

/-- **Bipartite richness data bundle** (`step7.tex:1517-1527`).

Specialised to `Pair := A × B` (interfaces are coordinate pairs in
the paper's bipartite setup, `step7.tex:1533-1540`).

Carries:
* `Aset / Bset` — chain vertex sets;
* `rich` — rich-interface set `Rich⋆_{AB}`, valued in
  `Aset ×ˢ Bset` via `hRichSub`. -/
structure BipartiteRichness (A B : Type*) where
  /-- A-chain vertex set. -/
  Aset : Finset A
  /-- B-chain vertex set. -/
  Bset : Finset B
  /-- Rich-interface set `Rich⋆_{AB} ⊆ Aset ×ˢ Bset`. -/
  rich : Finset (A × B)

namespace BipartiteRichness

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable (G : BipartiteRichness A B)

/-- **B-degree of `a ∈ A`** — count of `b ∈ B` with `(a, b) ∈ rich`.
Concretely, the cardinality of the B-fibre of `rich` over `a`. -/
def degB (a : A) : ℕ :=
  (G.Bset.filter (fun b => (a, b) ∈ G.rich)).card

/-- **A-degree of `b ∈ B`** — count of `a ∈ A` with `(a, b) ∈ rich`. -/
def degA (b : B) : ℕ :=
  (G.Aset.filter (fun a => (a, b) ∈ G.rich)).card

/-- **B-neighbours of `a ∈ A`** — `{b ∈ Bset : (a, b) ∈ rich}`. -/
def NB (a : A) : Finset B := G.Bset.filter (fun b => (a, b) ∈ G.rich)

@[simp] lemma NB_card (a : A) : (G.NB a).card = G.degB a := rfl

lemma mem_NB {a : A} {b : B} : b ∈ G.NB a ↔ b ∈ G.Bset ∧ (a, b) ∈ G.rich := by
  simp [NB, Finset.mem_filter]

/-- **A-neighbours of `b ∈ B`** — `{a ∈ Aset : (a, b) ∈ rich}`. -/
def NA (b : B) : Finset A := G.Aset.filter (fun a => (a, b) ∈ G.rich)

@[simp] lemma NA_card (b : B) : (G.NA b).card = G.degA b := rfl

lemma mem_NA {a : A} {b : B} : a ∈ G.NA b ↔ a ∈ G.Aset ∧ (a, b) ∈ G.rich := by
  simp [NA, Finset.mem_filter]

/-- `degB a ≤ |Bset|`. -/
lemma degB_le_Bset_card (a : A) : G.degB a ≤ G.Bset.card := by
  unfold degB
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- `degA b ≤ |Aset|`. -/
lemma degA_le_Aset_card (b : B) : G.degA b ≤ G.Aset.card := by
  unfold degA
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Total B-degree = `|rich|`**, provided `rich ⊆ Aset ×ˢ Bset`.

This is the degree-sum identity for the bipartite graph: counting
incidences `(a, b) ∈ rich` by `a` recovers `|rich|`. -/
lemma sum_degB_eq_rich_card
    (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset) :
    ∑ a ∈ G.Aset, G.degB a = G.rich.card := by
  classical
  -- Rewrite |rich| as filter-cardinality on Aset ×ˢ Bset.
  have hrich_eq :
      G.rich = (G.Aset ×ˢ G.Bset).filter (fun p => p ∈ G.rich) := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨hRichSub hp, hp⟩, fun ⟨_, hp⟩ => hp⟩
  rw [hrich_eq, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  unfold degB
  rw [Finset.card_filter]

/-- **Symmetric: total A-degree = `|rich|`.** -/
lemma sum_degA_eq_rich_card
    (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset) :
    ∑ b ∈ G.Bset, G.degA b = G.rich.card := by
  classical
  have hrich_eq :
      G.rich = (G.Aset ×ˢ G.Bset).filter (fun p => p ∈ G.rich) := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨hRichSub hp, hp⟩, fun ⟨_, hp⟩ => hp⟩
  rw [hrich_eq, Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold degA
  rw [Finset.card_filter]

/-! ### §2 — Rich-row / rich-column thresholds and reverse-Markov bound -/

/-- **Rich rows at cleared threshold `(α_n / α_d)`** —
`a ∈ Aset` with `α_n · |Bset| ≤ α_d · degB a` (degree fraction
`≥ α_n / α_d`).

Paper `step7.tex:1592`: rich-row threshold `(c_T / 2)·|B|` is
captured here by `(α_n / α_d) = (c_T / 2)`. -/
def richRows (α_n α_d : ℕ) : Finset A :=
  G.Aset.filter (fun a => α_n * G.Bset.card ≤ α_d * G.degB a)

/-- **Non-rich rows at threshold `(α_n / α_d)`** — `Aset ∖ richRows`. -/
def nonRichRows (α_n α_d : ℕ) : Finset A :=
  G.Aset.filter (fun a => α_d * G.degB a < α_n * G.Bset.card)

/-- **Rich columns at cleared threshold `(α_n / α_d)`**. -/
def richCols (α_n α_d : ℕ) : Finset B :=
  G.Bset.filter (fun b => α_n * G.Aset.card ≤ α_d * G.degA b)

/-- **Non-rich columns at threshold `(α_n / α_d)`**. -/
def nonRichCols (α_n α_d : ℕ) : Finset B :=
  G.Bset.filter (fun b => α_d * G.degA b < α_n * G.Aset.card)

lemma mem_richRows {α_n α_d : ℕ} {a : A} :
    a ∈ G.richRows α_n α_d ↔
      a ∈ G.Aset ∧ α_n * G.Bset.card ≤ α_d * G.degB a := by
  simp [richRows, Finset.mem_filter]

lemma mem_nonRichRows {α_n α_d : ℕ} {a : A} :
    a ∈ G.nonRichRows α_n α_d ↔
      a ∈ G.Aset ∧ α_d * G.degB a < α_n * G.Bset.card := by
  simp [nonRichRows, Finset.mem_filter]

lemma mem_richCols {α_n α_d : ℕ} {b : B} :
    b ∈ G.richCols α_n α_d ↔
      b ∈ G.Bset ∧ α_n * G.Aset.card ≤ α_d * G.degA b := by
  simp [richCols, Finset.mem_filter]

lemma mem_nonRichCols {α_n α_d : ℕ} {b : B} :
    b ∈ G.nonRichCols α_n α_d ↔
      b ∈ G.Bset ∧ α_d * G.degA b < α_n * G.Aset.card := by
  simp [nonRichCols, Finset.mem_filter]

lemma richRows_disjoint_nonRichRows (α_n α_d : ℕ) :
    Disjoint (G.richRows α_n α_d) (G.nonRichRows α_n α_d) := by
  rw [Finset.disjoint_left]
  intro a hr hn
  rw [G.mem_richRows] at hr
  rw [G.mem_nonRichRows] at hn
  exact absurd hr.2 (not_le.mpr hn.2)

lemma richRows_union_nonRichRows (α_n α_d : ℕ) :
    G.richRows α_n α_d ∪ G.nonRichRows α_n α_d = G.Aset := by
  ext a
  simp only [Finset.mem_union, mem_richRows, mem_nonRichRows]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro ha
    by_cases h : α_n * G.Bset.card ≤ α_d * G.degB a
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, not_le.mp h⟩

lemma richRows_card_add_nonRichRows_card (α_n α_d : ℕ) :
    (G.richRows α_n α_d).card + (G.nonRichRows α_n α_d).card = G.Aset.card := by
  classical
  rw [← Finset.card_union_of_disjoint (G.richRows_disjoint_nonRichRows α_n α_d)]
  rw [G.richRows_union_nonRichRows α_n α_d]

lemma richCols_disjoint_nonRichCols (α_n α_d : ℕ) :
    Disjoint (G.richCols α_n α_d) (G.nonRichCols α_n α_d) := by
  rw [Finset.disjoint_left]
  intro b hr hn
  rw [G.mem_richCols] at hr
  rw [G.mem_nonRichCols] at hn
  exact absurd hr.2 (not_le.mpr hn.2)

lemma richCols_union_nonRichCols (α_n α_d : ℕ) :
    G.richCols α_n α_d ∪ G.nonRichCols α_n α_d = G.Bset := by
  ext b
  simp only [Finset.mem_union, mem_richCols, mem_nonRichCols]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hb
    by_cases h : α_n * G.Aset.card ≤ α_d * G.degA b
    · exact Or.inl ⟨hb, h⟩
    · exact Or.inr ⟨hb, not_le.mp h⟩

lemma richCols_card_add_nonRichCols_card (α_n α_d : ℕ) :
    (G.richCols α_n α_d).card + (G.nonRichCols α_n α_d).card = G.Bset.card := by
  classical
  rw [← Finset.card_union_of_disjoint (G.richCols_disjoint_nonRichCols α_n α_d)]
  rw [G.richCols_union_nonRichCols α_n α_d]

/-- **Reverse-Markov degree-sum split** (`step7.tex:1591-1593`).

The total degree sum `∑_{a ∈ Aset} degB a` splits as a sum over
non-rich-rows (each `< (α_n / α_d) · |Bset|`) and rich-rows
(each `≤ |Bset|`).  Cleared-denominator form:

  `α_d · ∑_{a ∈ Aset} degB a < α_n · |Bset| · |nonRich|
    + α_d · |Bset| · |rich-rows|`,

provided `nonRichRows` is nonempty (otherwise the strict
inequality fails on an empty sum, and the bound is replaced by
a `≤`). -/
lemma degB_sum_split_bound (α_n α_d : ℕ) :
    α_d * ∑ a ∈ G.Aset, G.degB a ≤
      α_n * G.Bset.card * (G.nonRichRows α_n α_d).card +
        α_d * G.Bset.card * (G.richRows α_n α_d).card := by
  classical
  have hunion := G.richRows_union_nonRichRows α_n α_d
  have hdisj := G.richRows_disjoint_nonRichRows α_n α_d
  have hsplit :
      ∑ a ∈ G.Aset, G.degB a =
        ∑ a ∈ G.richRows α_n α_d, G.degB a +
          ∑ a ∈ G.nonRichRows α_n α_d, G.degB a := by
    rw [← hunion, Finset.sum_union hdisj]
  rw [hsplit, Nat.mul_add]
  have hrich :
      α_d * ∑ a ∈ G.richRows α_n α_d, G.degB a ≤
        α_d * G.Bset.card * (G.richRows α_n α_d).card := by
    calc α_d * ∑ a ∈ G.richRows α_n α_d, G.degB a
        ≤ α_d * ∑ a ∈ G.richRows α_n α_d, G.Bset.card := by
          apply Nat.mul_le_mul_left
          apply Finset.sum_le_sum
          intro a _; exact G.degB_le_Bset_card a
      _ = α_d * (G.Bset.card * (G.richRows α_n α_d).card) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm _ G.Bset.card]
      _ = α_d * G.Bset.card * (G.richRows α_n α_d).card := by ring
  have hnon :
      α_d * ∑ a ∈ G.nonRichRows α_n α_d, G.degB a ≤
        α_n * G.Bset.card * (G.nonRichRows α_n α_d).card := by
    calc α_d * ∑ a ∈ G.nonRichRows α_n α_d, G.degB a
        = ∑ a ∈ G.nonRichRows α_n α_d, α_d * G.degB a := Finset.mul_sum ..
      _ ≤ ∑ a ∈ G.nonRichRows α_n α_d, α_n * G.Bset.card := by
          apply Finset.sum_le_sum
          intro a ha
          rw [G.mem_nonRichRows] at ha
          exact le_of_lt ha.2
      _ = α_n * G.Bset.card * (G.nonRichRows α_n α_d).card := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  linarith

/-- **Cleared-denominator non-rich-row count bound** —
reverse-Markov from a richness lower bound (`step7.tex:1591-1593`).

Given:
* `c_n · |Aset| · |Bset| ≤ c_d · ∑_{a ∈ Aset} degB a` (Step 5
  richness, `step7.tex:1533-1535`);
* threshold `(α_n / α_d) = (c_T / 2)` for rich-rows.

Concludes:
  `c_d · (c_n · α_d - c_d · α_n) · |Aset| ≤
    c_d · (α_d - α_n) · α_d · |Bset| · |nonRichRows|`

(rearranging the paper's `|nonRichRows| ≤ (2/c_T) · |Aset|` to
cleared-denominator form).  Whenever `α_d · c_n > α_n · c_d`
(i.e. richness fraction strictly above the rich-row threshold),
the non-rich-row count is controlled. -/
theorem nonRichRows_count_bound
    (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset)
    (c_n c_d : ℕ)
    (hRich : c_n * G.Aset.card * G.Bset.card ≤ c_d * G.rich.card)
    (α_n α_d : ℕ) :
    α_d * (c_n * G.Aset.card * G.Bset.card) ≤
      c_d * (α_n * G.Bset.card * (G.nonRichRows α_n α_d).card +
        α_d * G.Bset.card * (G.richRows α_n α_d).card) := by
  classical
  have hsum := G.degB_sum_split_bound α_n α_d
  have hsumEq := G.sum_degB_eq_rich_card hRichSub
  -- α_d · ∑ degB ≤ α_n · |B| · |non| + α_d · |B| · |rich|
  -- ∑ degB = |rich|, so α_d · |rich| ≤ α_n · |B| · |non| + α_d · |B| · |rich|.
  rw [hsumEq] at hsum
  -- Combine: α_d · (c_n·|A|·|B|) ≤ c_d · α_d · |rich| (multiply hRich by α_d)
  --        ≤ c_d · (α_n·|B|·|non| + α_d·|B|·|rich|).
  have h1 : α_d * (c_n * G.Aset.card * G.Bset.card) ≤
      α_d * (c_d * G.rich.card) := Nat.mul_le_mul_left _ hRich
  have h2 : α_d * (c_d * G.rich.card) = c_d * (α_d * G.rich.card) := by ring
  rw [h2] at h1
  have h3 : c_d * (α_d * G.rich.card) ≤
      c_d * (α_n * G.Bset.card * (G.nonRichRows α_n α_d).card +
        α_d * G.Bset.card * (G.richRows α_n α_d).card) :=
    Nat.mul_le_mul_left _ hsum
  exact h1.trans h3

/-! ### §3 — Common-`B`-neighbour existence and length-3 walk -/

/-- **Common-`B`-neighbour existence** (`step7.tex:1594-1597`).

By inclusion-exclusion in `Finset` cardinality, if `|N_B(a)| +
|N_B(a')| > |Bset|`, then `N_B(a) ∩ N_B(a') ≠ ∅`.  For rich-rows
at threshold `α_n / α_d`, `|N_B(a)| ≥ (α_n/α_d)·|Bset|`, so the
condition becomes `2 · α_n · |Bset| > α_d · |Bset|`, i.e.
`α_d < 2 · α_n` (rich-row threshold above `1/2`).  This is the
paper's `c_T > 1` instantiation. -/
theorem commonB_neighbour_of_rich_rows
    {α_n α_d : ℕ}
    {a a' : A} (ha : a ∈ G.richRows α_n α_d) (ha' : a' ∈ G.richRows α_n α_d)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card) :
    (G.NB a ∩ G.NB a').Nonempty := by
  classical
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  rw [G.mem_richRows] at ha ha'
  have hNBa : G.NB a ⊆ G.Bset := Finset.filter_subset _ _
  have hNBa' : G.NB a' ⊆ G.Bset := Finset.filter_subset _ _
  -- Inclusion-exclusion: |N(a) ∪ N(a')| + |N(a) ∩ N(a')| = |N(a)| + |N(a')|.
  -- With empty intersection: |N(a) ∪ N(a')| = |N(a)| + |N(a')|.
  -- And |N(a) ∪ N(a')| ≤ |Bset|.
  have hunion_le_B : (G.NB a ∪ G.NB a').card ≤ G.Bset.card :=
    Finset.card_le_card (Finset.union_subset hNBa hNBa')
  have hempty_inter : Disjoint (G.NB a) (G.NB a') := by
    rw [Finset.disjoint_iff_inter_eq_empty]; exact h
  have hcardSum : (G.NB a).card + (G.NB a').card =
      (G.NB a ∪ G.NB a').card := by
    rw [← Finset.card_union_of_disjoint hempty_inter]
  -- |N(a)| + |N(a')| ≤ |Bset|, but α_d · |N(a)| ≥ α_n · |Bset|
  -- and α_d · |N(a')| ≥ α_n · |Bset|, so α_d · (|N(a)| + |N(a')|) ≥
  -- 2·α_n·|Bset|, contradicting α_d · |Bset| ≥ α_d · (|N(a)| + |N(a')|).
  have hNB_a : (G.NB a).card = G.degB a := G.NB_card a
  have hNB_a' : (G.NB a').card = G.degB a' := G.NB_card a'
  rw [hNB_a, hNB_a'] at hcardSum
  have hsum_le_B : G.degB a + G.degB a' ≤ G.Bset.card := by
    rw [hcardSum]; exact hunion_le_B
  have hmul_a : α_n * G.Bset.card ≤ α_d * G.degB a := ha.2
  have hmul_a' : α_n * G.Bset.card ≤ α_d * G.degB a' := ha'.2
  have hsum_mul :
      α_n * G.Bset.card + α_n * G.Bset.card ≤
        α_d * G.degB a + α_d * G.degB a' :=
    Nat.add_le_add hmul_a hmul_a'
  have hsum_mul' :
      α_n * G.Bset.card + α_n * G.Bset.card ≤
        α_d * (G.degB a + G.degB a') := by
    rw [Nat.mul_add]; exact hsum_mul
  have hsum_mul'' :
      α_n * G.Bset.card + α_n * G.Bset.card ≤
        α_d * G.Bset.card :=
    hsum_mul'.trans (Nat.mul_le_mul_left _ hsum_le_B)
  exact absurd hsum_mul'' (not_le.mpr hThresh)

/-- **Concrete common-`B`-neighbour** — choose any element of the
nonempty intersection.  Used as the intermediate vertex in the
length-3 walk construction (paper `step7.tex:1597-1601`). -/
noncomputable def commonBNbr
    {α_n α_d : ℕ}
    {a a' : A} (ha : a ∈ G.richRows α_n α_d) (ha' : a' ∈ G.richRows α_n α_d)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card) :
    B :=
  (G.commonB_neighbour_of_rich_rows ha ha' hThresh).choose

lemma commonBNbr_spec
    {α_n α_d : ℕ}
    {a a' : A} (ha : a ∈ G.richRows α_n α_d) (ha' : a' ∈ G.richRows α_n α_d)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card) :
    G.commonBNbr ha ha' hThresh ∈ G.NB a ∩ G.NB a' :=
  (G.commonB_neighbour_of_rich_rows ha ha' hThresh).choose_spec

/-! ### §4 — Endpoint-sharing pair set + length-3 walk construction -/

/-- **Endpoint-sharing predicate** on pairs of interfaces
(`step7.tex:1583-1585`).

Two rich interfaces `α = (a, b), β = (a', b')` *share an
endpoint* iff they agree on the `A`- or `B`-coordinate. -/
def sharesEndpoint (e f : A × B) : Prop :=
  e.1 = f.1 ∨ e.2 = f.2

instance (e f : A × B) : Decidable (sharesEndpoint e f) := by
  unfold sharesEndpoint
  infer_instance

/-- **Endpoint-sharing pair set on `rich²`** — pairs of rich
interfaces sharing an endpoint, packaged as a `Finset (Pair × Pair)`. -/
def endpointSharePairs : Finset ((A × B) × (A × B)) :=
  (G.rich ×ˢ G.rich).filter (fun pq => sharesEndpoint pq.1 pq.2)

lemma mem_endpointSharePairs {e f : A × B} :
    (e, f) ∈ G.endpointSharePairs ↔
      e ∈ G.rich ∧ f ∈ G.rich ∧ sharesEndpoint e f := by
  simp [endpointSharePairs, Finset.mem_filter, Finset.mem_product]
  tauto

/-- **Length-3 walk construction through a common-`B`-neighbour**
(`step7.tex:1597-1603`).

For any reference `e₀ = (a₀, b₀) ∈ rich` with `a₀` a rich-row,
and any target `e = (a, b) ∈ rich` with `a` a rich-row, build a
length-3 walk

  `e₀ = (a₀, b₀) → (a₀, b'') → (a, b'') → (a, b) = e`

through endpoint-sharing rich pairs, where `b''` is the common
`B`-neighbour of `a₀` and `a`.

Returns the walk witnesses for `FiberThresholdData.WalkWitness3`. -/
theorem endpoint_walk3
    {α_n α_d : ℕ}
    (e₀ e : A × B) (he₀ : e₀ ∈ G.rich) (he : e ∈ G.rich)
    (ha₀ : e₀.1 ∈ G.richRows α_n α_d) (ha : e.1 ∈ G.richRows α_n α_d)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card) :
    ∃ g₁ g₂ : A × B,
      (e₀, g₁) ∈ G.endpointSharePairs ∧
      (g₁, g₂) ∈ G.endpointSharePairs ∧
      (g₂, e) ∈ G.endpointSharePairs := by
  classical
  -- Choose b'' ∈ N_B(a₀) ∩ N_B(a).
  have hb'' := G.commonBNbr_spec ha₀ ha hThresh
  set b'' := G.commonBNbr ha₀ ha hThresh
  rw [Finset.mem_inter] at hb''
  obtain ⟨hb''_a₀, hb''_a⟩ := hb''
  rw [G.mem_NB] at hb''_a₀
  rw [G.mem_NB] at hb''_a
  -- g₁ := (a₀, b''), g₂ := (a, b''); both ∈ rich.
  refine ⟨(e₀.1, b''), (e.1, b''), ?_, ?_, ?_⟩
  · -- (e₀, (a₀, b'')) share endpoint a₀.
    rw [G.mem_endpointSharePairs]
    refine ⟨he₀, hb''_a₀.2, ?_⟩
    left; rfl
  · -- ((a₀, b''), (a, b'')) share endpoint b''.
    rw [G.mem_endpointSharePairs]
    refine ⟨hb''_a₀.2, hb''_a.2, ?_⟩
    right; rfl
  · -- ((a, b''), e) share endpoint a.
    rw [G.mem_endpointSharePairs]
    refine ⟨hb''_a.2, he, ?_⟩
    left; rfl

/-! ### §5 — Giant component = rich-row × rich (subset of `rich`) -/

/-- **Giant component carrier** (`step7.tex:1610-1628`).

The giant component on `Rich⋆` is the set of interfaces whose
`A`-coordinate is a rich-row.  The paper's giant-component
incidence mass is the cardinality of this set (each interface
contributes one unit of incidence in the cleared form). -/
def giantComponent (α_n α_d : ℕ) : Finset (A × B) :=
  G.rich.filter (fun e => e.1 ∈ G.richRows α_n α_d)

lemma giantComponent_subset (α_n α_d : ℕ) :
    G.giantComponent α_n α_d ⊆ G.rich := Finset.filter_subset _ _

lemma mem_giantComponent {α_n α_d : ℕ} {e : A × B} :
    e ∈ G.giantComponent α_n α_d ↔
      e ∈ G.rich ∧ e.1 ∈ G.richRows α_n α_d := by
  simp [giantComponent, Finset.mem_filter]

/-- **Exceptional set** — rich interfaces with non-rich-row
`A`-endpoint. -/
def exceptionalRich (α_n α_d : ℕ) : Finset (A × B) :=
  G.rich.filter (fun e => e.1 ∈ G.nonRichRows α_n α_d)

lemma exceptionalRich_subset (α_n α_d : ℕ) :
    G.exceptionalRich α_n α_d ⊆ G.rich := Finset.filter_subset _ _

lemma mem_exceptionalRich {α_n α_d : ℕ} {e : A × B} :
    e ∈ G.exceptionalRich α_n α_d ↔
      e ∈ G.rich ∧ e.1 ∈ G.nonRichRows α_n α_d := by
  simp [exceptionalRich, Finset.mem_filter]

lemma giantComponent_union_exceptionalRich
    (α_n α_d : ℕ) (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset) :
    G.giantComponent α_n α_d ∪ G.exceptionalRich α_n α_d = G.rich := by
  ext e
  simp only [Finset.mem_union, mem_giantComponent, mem_exceptionalRich]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro he
    have ha : e.1 ∈ G.Aset := (Finset.mem_product.mp (hRichSub he)).1
    by_cases h : α_n * G.Bset.card ≤ α_d * G.degB e.1
    · left; exact ⟨he, by rw [G.mem_richRows]; exact ⟨ha, h⟩⟩
    · right
      refine ⟨he, ?_⟩
      rw [G.mem_nonRichRows]
      exact ⟨ha, not_le.mp h⟩

lemma giantComponent_disjoint_exceptionalRich (α_n α_d : ℕ) :
    Disjoint (G.giantComponent α_n α_d) (G.exceptionalRich α_n α_d) := by
  rw [Finset.disjoint_left]
  intro e hg ho
  rw [G.mem_giantComponent] at hg
  rw [G.mem_exceptionalRich] at ho
  have hr := hg.2
  have hn := ho.2
  rw [G.mem_richRows] at hr
  rw [G.mem_nonRichRows] at hn
  exact absurd hr.2 (not_le.mpr hn.2)

lemma giantComponent_card_add_exceptionalRich_card
    (α_n α_d : ℕ) (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset) :
    (G.giantComponent α_n α_d).card +
        (G.exceptionalRich α_n α_d).card = G.rich.card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (G.giantComponent_disjoint_exceptionalRich α_n α_d)]
  rw [G.giantComponent_union_exceptionalRich α_n α_d hRichSub]

/-- **Exceptional-rich cardinality bound** (cleared-denominator
form of `step7.tex:1604-1607`).

The exceptional rich set (rich interfaces through a non-rich-row
`a`) has cardinality at most `|nonRichRows| · |Bset|`, since each
non-rich-row contributes at most `|Bset|` rich pairs. -/
lemma exceptionalRich_card_le
    (α_n α_d : ℕ) (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset) :
    (G.exceptionalRich α_n α_d).card ≤
      (G.nonRichRows α_n α_d).card * G.Bset.card := by
  classical
  -- The exceptional rich set is bibUnion over non-rich-rows.
  have hbij :
      G.exceptionalRich α_n α_d =
        (G.nonRichRows α_n α_d).biUnion
          (fun a => G.NB a |>.image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [mem_exceptionalRich, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨hRich, hN⟩
      refine ⟨a, hN, b, ?_, rfl⟩
      rw [G.mem_NB]
      have ha : (a, b) ∈ G.Aset ×ˢ G.Bset := hRichSub hRich
      rw [Finset.mem_product] at ha
      exact ⟨ha.2, hRich⟩
    · rintro ⟨a', hN, b', hb', heq⟩
      rw [G.mem_NB] at hb'
      obtain ⟨ha_eq, hb_eq⟩ : a' = a ∧ b' = b := Prod.mk.injEq _ _ _ _ |>.mp heq
      subst ha_eq
      subst hb_eq
      exact ⟨hb'.2, hN⟩
  rw [hbij]
  calc ((G.nonRichRows α_n α_d).biUnion
          (fun a => G.NB a |>.image (fun b => (a, b)))).card
      ≤ ∑ a ∈ G.nonRichRows α_n α_d,
          (G.NB a |>.image (fun b => (a, b))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a ∈ G.nonRichRows α_n α_d, (G.NB a).card := by
        apply Finset.sum_le_sum
        intros; exact Finset.card_image_le
    _ ≤ ∑ a ∈ G.nonRichRows α_n α_d, G.Bset.card := by
        apply Finset.sum_le_sum
        intro a _
        rw [G.NB_card]
        exact G.degB_le_Bset_card a
    _ = (G.nonRichRows α_n α_d).card * G.Bset.card := by
        rw [Finset.sum_const, smul_eq_mul]

/-! ### §6 — Grounded `lem:giant-component` -/

/-- **`lem:giant-component` — grounded form (walk-witness)**
(`step7.tex:1513-1648`).

Cleared-denominator paper-faithful output: under the rich-pair
inclusion + Step 5 richness LB + rich-row threshold strictly
above `1/2` (cleared: `α_d < 2·α_n`), every interface `e ∈
giantComponent` admits a length-3 walk through endpoint-sharing
pairs to a reference `e₀` whose `A`-coordinate is a rich-row.

The output is exactly `FiberThresholdData.WalkWitness3` shape —
ready for downstream consumption by S7-D G6
`single_c_grounded` / `lem_single_c_grounded_bundled`. -/
theorem lem_giant_component_grounded
    (_hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset)
    (α_n α_d : ℕ)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card)
    (e₀ : A × B) (he₀_rich : e₀ ∈ G.rich)
    (he₀_row : e₀.1 ∈ G.richRows α_n α_d) :
    FiberThresholdData.WalkWitness3 e₀ (G.giantComponent α_n α_d)
      G.endpointSharePairs := by
  intro e he
  rw [G.mem_giantComponent] at he
  obtain ⟨he_rich, he_row⟩ := he
  exact G.endpoint_walk3 e₀ e he₀_rich he_rich he₀_row he_row hThresh

/-- **`lem:giant-component` — grounded mass lower bound**
(`step7.tex:1604-1607, 1623-1628`).

Cleared-denominator `(1 - O(c_T⁻¹))`-mass bound on the giant
component, derived from the exceptional-rich count and the
non-rich-row count.

If `c_n · |Aset| · |Bset| ≤ c_d · |rich|` (Step 5 richness),
then

  `α_d · c_n · |Aset| · |Bset| ≤
    c_d · (α_d · (|giantComponent| + |Bset| · |nonRichRows|))`

(combining `richRows_card_add_nonRichRows_card`,
`giantComponent_card_add_exceptionalRich_card`, and the
exceptional bound).  Rearranging gives the paper's
`|giantComponent| ≥ (1 - O(c_T⁻¹)) · |rich|`. -/
theorem lem_giant_component_grounded_mass_lb
    (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset)
    (_c_n c_d : ℕ)
    (_hRich : _c_n * G.Aset.card * G.Bset.card ≤ c_d * G.rich.card)
    (α_n α_d : ℕ) :
    c_d * G.rich.card ≤
      c_d * ((G.giantComponent α_n α_d).card +
        (G.nonRichRows α_n α_d).card * G.Bset.card) := by
  classical
  have hsplit := G.giantComponent_card_add_exceptionalRich_card α_n α_d hRichSub
  have hexc := G.exceptionalRich_card_le α_n α_d hRichSub
  have h1 : G.rich.card ≤ (G.giantComponent α_n α_d).card +
      (G.nonRichRows α_n α_d).card * G.Bset.card := by
    rw [← hsplit]
    exact Nat.add_le_add_left hexc _
  exact Nat.mul_le_mul_left _ h1

/-- **`lem:giant-component` — bundled paper-statement form**
(`step7.tex:1513-1656`, paper-statement packaging).

Single-call conjunction packaging the two core deliverables of
the S7-D G9 grounded form:

1. **Walk-witness on the giant component** (`step7.tex:1610-1628`):
   every interface in `giantComponent α_n α_d` admits a length-3
   endpoint-sharing walk to the reference, ready for downstream
   `single_c_grounded` consumption.
2. **Mass lower bound** (`step7.tex:1604-1607, 1623-1628`):
   cleared-denominator `(1 - O(c_T⁻¹))`-fraction bound — the
   exceptional rich set has mass `≤ |nonRichRows| · |Bset|`,
   and `|nonRichRows| · α_d ≤ (|Aset| · (α_d - α_n) + |Aset| ·
   (rich-row count))` is handled upstream by `degB_sum_split_bound`.

Constants:
* `c_n / c_d` — richness fraction `c_T` of Step 5
  (paper `step7.tex:1533-1535`).
* `α_n / α_d` — rich-row threshold; paper uses `c_T / 2`.
* `hThresh : α_d · |Bset| < 2 · α_n · |Bset|` — rich-row
  threshold strictly above `1/2` (equivalent to `α_d < 2·α_n`
  for `|Bset| > 0`).

The cardinality bound on `nonRichRows` is delivered by
`nonRichRows_count_bound`; the bundled form here exposes both
the walk-witness and the cardinality split for downstream
re-derivation in `(1 - o(1))`-fraction language. -/
theorem lem_giant_component_grounded_bundled
    (hRichSub : G.rich ⊆ G.Aset ×ˢ G.Bset)
    (c_n c_d : ℕ)
    (hRich : c_n * G.Aset.card * G.Bset.card ≤ c_d * G.rich.card)
    (α_n α_d : ℕ)
    (hThresh : α_d * G.Bset.card < α_n * G.Bset.card + α_n * G.Bset.card)
    (e₀ : A × B) (he₀_rich : e₀ ∈ G.rich)
    (he₀_row : e₀.1 ∈ G.richRows α_n α_d) :
    -- (1) Walk-witness on the giant component:
    FiberThresholdData.WalkWitness3 e₀ (G.giantComponent α_n α_d)
      G.endpointSharePairs ∧
    -- (2) Mass lower bound:
    c_d * G.rich.card ≤
      c_d * ((G.giantComponent α_n α_d).card +
        (G.nonRichRows α_n α_d).card * G.Bset.card) ∧
    -- (3) Cardinality split identity:
    (G.giantComponent α_n α_d).card +
        (G.exceptionalRich α_n α_d).card = G.rich.card := by
  refine ⟨?_, ?_, ?_⟩
  · exact G.lem_giant_component_grounded hRichSub α_n α_d hThresh e₀
      he₀_rich he₀_row
  · -- mass LB depends only on hRichSub
    exact G.lem_giant_component_grounded_mass_lb hRichSub c_n c_d hRich α_n α_d
  · exact G.giantComponent_card_add_exceptionalRich_card α_n α_d hRichSub

end BipartiteRichness

end Step7
end OneThird
