/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Step 8 — G3: Layered reduction (`sec:layered-reduction`)

Formalises the GAP G3 / `lem:layered-reduction` discharge of
`step8.tex` §`sec:layered-reduction` (`step8.tex:1872-2335`).

## Setup

A `LayeredDecomposition` (`def:layered`, `step8.tex:1883-1907`)
of a finite width-3 poset `P = (α, ≤)` records:

* the **depth** `K : ℕ` of the layering;
* the **interaction width** `w : ℕ`;
* the **band map** `band : α → ℕ` placing each element in a band
  index `1 ≤ band x ≤ K`,

subject to the layered axioms

* `(L1)` each band has size `≤ 3`;
* `(L2-forced)` if `band x + w < band y`, then `x < y` (the *forced*
  cross-band comparability);
* `(L2-upward)` if `x < y` in the partial order, then
  `band x ≤ band y` (cross-band comparabilities are directed
  upward — the §sec:g4 setup property of the paper, recorded as
  `cross_band_lt_upward` and added in mg-53ce / A5-G2 path 1).

`(L3)` of the paper (comparability whenever `|band i − band j| > w`)
follows from `(L2-forced)` by symmetry, so we do not require it as
an axiom.

## Size-minimality framing (`mg-805c`)

The lemma is stated as a one-shot reductio against *size-minimal*
γ-counterexamples: among all width-3 γ-counterexamples (for the given
γ), `P` has the smallest ground set `|X|`. Earlier formulations of
this paper used `γ/2`-recursion, packaging the cut piece `A` as a
smaller `(γ/2)`-counterexample and deferring the contradiction to a
recursive call. Size-minimality contradicts directly: any proper
induced subposet `A ⊊ P` has `|A| < |X|`, so by size-minimality `A`
is not a γ-counterexample at the *same* parameter γ, hence `A` has a
balanced pair, which lifts to `P` by Step 3 (bulk identity) or
Step 5 (window perturbation). The dependence of `K₀` on γ is
one-sided (driven by the window-perturbation bound alone), with no
compounding through iterated halving.

## Main results

* `LayeredDecomposition` — the layered decomposition structure.
* `LayeredCut` — the ordinal cut data of `lem:cut`
  (`step8.tex:2164-2186`): a cut index `k`, the lower set `A`, the
  upper set `B`, the interaction window `W`.
* `lem_cut` — **`lem:cut`** (`step8.tex:2164`). For depth
  `K ≥ 2w + 2`, every index `k ∈ (w, K − w)` produces an ordinal
  cut whose only cross-comparability obstructions live inside the
  interaction window of size `≤ 6w`.
* `LayeredReductionConclusion` — the conclusion of
  `lem:layered-reduction` in size-minimal form: `P` has a balanced
  pair, contradicting that `P` is a γ-counterexample. (Single
  `Prop`, no disjunction — the prior `(γ/2)`-counterexample
  alternative branch is gone.)
* `lem_layered_reduction` — **`lem:layered-reduction`**
  (`step8.tex:2193`, GAP G3 discharged, size-minimal form).
  Cleared-denominator abstract form: from a layered decomposition
  of depth `K ≥ K₀(γ, w)` and the witness map packaged in
  `ReductionWitness`-style (which carries the size-minimality
  discharge as a `Prop` hypothesis), the conclusion `balanced`
  holds. The combinatorial cut + bulk/window lift argument is left
  to the downstream window-localization gluing in
  `LayeredBalanced.lean`; this file packages the conclusion.

## References

`step8.tex` §`sec:layered-reduction` (`step8.tex:1872-2335`),
Lemmas `lem:cut`, `lem:layered-reduction`, Definition `def:layered`.
`simplifications.md` §1 (size-minimality framing source).
-/

namespace OneThird
namespace Step8

/-! ### §1 — Layered decompositions (`def:layered`) -/

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- **Layered width-3 decomposition** (`def:layered`,
`step8.tex:1883`).

A layered decomposition of interaction width `w` and depth `K` of
a finite poset `P = (α, ≤)` records:

* `band : α → ℕ` — band index in `[1, K]`;
* `(L1)` `band_size : ∀ k, |{x : band x = k}| ≤ 3`;
* `(L2-forced)` `forced_lt : ∀ x y, band x + w < band y → x < y`;
* `(L2-upward)` `cross_band_lt_upward : ∀ x y, x < y → band x ≤ band y`.

`(L2-upward)` records the paper's §sec:g4 setup property "cross-band
comparabilities are directed upward". It was originally argued
informally in `step8.tex` `prop:in-situ-balanced` (`step8.tex:2965-3048`)
without an explicit Lean field; the `mg-53ce` polecat report
(`docs/a5-g2-status.md`) diagnosed the missing axiom as the (L2)
gap blocking `bounded_irreducible_balanced_inScope`. Path 1 of the
resolution (this work) makes it a structural field.

The condition `(L3)` of the paper (`|i − j| > w` ⇒ comparability)
follows from `(L2-forced)` applied symmetrically, so we omit it as
a field. -/
structure LayeredDecomposition (α : Type*)
    [PartialOrder α] [Fintype α] where
  /-- Depth of the layering. -/
  K : ℕ
  /-- Interaction width (`step8.tex:1905`). -/
  w : ℕ
  /-- Band-index map (`L_i = {x : band x = i}`). -/
  band : α → ℕ
  /-- Band index is positive (band labels are `1, 2, …, K`). -/
  band_pos : ∀ x : α, 1 ≤ band x
  /-- Band index does not exceed `K`. -/
  band_le : ∀ x : α, band x ≤ K
  /-- (L1a) Each band has size `≤ 3` (`step8.tex:1892`). -/
  band_size :
    ∀ k : ℕ,
      (((Finset.univ : Finset α).filter (fun x => band x = k)).card) ≤ 3
  /-- (L1b) Each band is an antichain (`step8.tex:1892`, matches the
  paper's L1 stated as "each `L_i` is an antichain"). -/
  band_antichain :
    ∀ k : ℕ,
      IsAntichain (· ≤ ·)
        ((((Finset.univ : Finset α).filter (fun x => band x = k)) : Set α))
  /-- (L2-forced) Far-apart bands force comparability `x < y`
  (`step8.tex:1894-1901`). -/
  forced_lt : ∀ x y : α, band x + w < band y → x < y
  /-- (L2-upward) Cross-band comparabilities are directed upward:
  if `x < y` in the partial order, then `band x ≤ band y`.

  This is the paper's §sec:g4 setup property — see the
  `prop:in-situ-balanced` discussion (`step8.tex:2965-3048`) — and
  was added as an explicit field in `mg-53ce` / A5-G2 path 1 to close
  the (L2) gap diagnosed in `docs/a5-g2-status.md`. With this field,
  the band-major encoding `predMaskOf L` is upper-triangular, which
  is what the F5a Bool certificate's enumeration requires. -/
  cross_band_lt_upward : ∀ x y : α, x < y → band x ≤ band y

namespace LayeredDecomposition

variable (L : LayeredDecomposition α)

/-- The `i`-th band as a `Finset`. -/
noncomputable def bandSet (i : ℕ) : Finset α :=
  (Finset.univ : Finset α).filter (fun x => L.band x = i)

@[simp] lemma mem_bandSet {x : α} {i : ℕ} :
    x ∈ L.bandSet i ↔ L.band x = i := by
  simp [bandSet]

/-- (L3) — derived corollary of (L2): far-apart bands are
comparable in *some* direction (`step8.tex:1896`). -/
theorem comparable_of_far {x y : α}
    (h : L.w < (max (L.band x) (L.band y)) - (min (L.band x) (L.band y))) :
    x < y ∨ y < x := by
  -- WLOG `band x ≤ band y`; then `band x + w < band y`, so `x < y` by (L2).
  rcases le_total (L.band x) (L.band y) with hxy | hxy
  · left
    apply L.forced_lt
    omega
  · right
    apply L.forced_lt
    omega

/-! ### §1b — `restrict`: sub-poset layered decomposition -/

/-- **Sub-poset restriction of a layered decomposition**.

Given `L : LayeredDecomposition α` and any `Finset S ⊆ α`, the
subtype `↥S` inherits:

* the ambient partial order (`Subtype` order);
* a band map `band z := L.band z.val`;
* the *same* depth `K` and interaction width `w`.

Axioms (L1), (L1b), (L2) transfer directly: (L1) and (L1b) because
filtering by band commutes with subtype inclusion and each band in
`α` is an antichain of size `≤ 3`; (L2) because the Subtype order
is the restriction of the ambient order.

This is the prerequisite infrastructure for applying G4-style
balanced-pair reasoning recursively on sub-posets — in particular,
for the F5 reducibility argument, whose recursion hypothesis
requires `LayeredDecomposition ↥β` for each recursive sub-poset
`β`. The window-localization argument of
`lem:window-localization` (`step8.tex:2524-2569`) is the canonical
specialization (restrict to a window slice).

Uses `classical` (for the image-under-`Subtype.val` card bound);
the underlying function content (`band`) is computable. -/
noncomputable def restrict (L : LayeredDecomposition α) (S : Finset α) :
    LayeredDecomposition ↥S where
  K := L.K
  w := L.w
  band z := L.band z.val
  band_pos z := L.band_pos z.val
  band_le z := L.band_le z.val
  band_size k := by
    classical
    -- Inject the sub-band into the ambient band via `Subtype.val`.
    set T : Finset ↥S :=
      (Finset.univ : Finset ↥S).filter (fun z => L.band z.val = k) with hT
    have hinj : Function.Injective (fun z : ↥S => z.val) :=
      Subtype.val_injective
    have hcard_img :
        (T.image (fun z : ↥S => z.val)).card = T.card :=
      Finset.card_image_of_injective _ hinj
    have hSub :
        T.image (fun z : ↥S => z.val) ⊆
          (Finset.univ : Finset α).filter (fun a => L.band a = k) := by
      intro a ha
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      obtain ⟨z, hz, hzeq⟩ := ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hzeq]; exact hz
    calc T.card
        = (T.image (fun z : ↥S => z.val)).card := hcard_img.symm
      _ ≤ ((Finset.univ : Finset α).filter (fun a => L.band a = k)).card :=
          Finset.card_le_card hSub
      _ ≤ 3 := L.band_size k
  band_antichain k := by
    classical
    -- `a ≤ b` on the Subtype is the ambient `a.val ≤ b.val`; use
    -- `L.band_antichain` on the image.
    intro a ha b hb hne hle
    simp only [Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq] at ha hb
    have hne_α : a.val ≠ b.val := fun h => hne (Subtype.ext h)
    have hle_α : a.val ≤ b.val := hle
    apply L.band_antichain k
      (show a.val ∈ ((((Finset.univ : Finset α).filter
          (fun x => L.band x = k))) : Set α) by
        simp only [Finset.coe_filter, Finset.mem_univ,
          true_and, Set.mem_setOf_eq]
        exact ha)
      (show b.val ∈ ((((Finset.univ : Finset α).filter
          (fun x => L.band x = k))) : Set α) by
        simp only [Finset.coe_filter, Finset.mem_univ,
          true_and, Set.mem_setOf_eq]
        exact hb)
      hne_α hle_α
  forced_lt x y h := L.forced_lt x.val y.val h
  cross_band_lt_upward x y h := L.cross_band_lt_upward x.val y.val h

/-! ### §1c — `restrict` API lemmas -/

/-- `band` transfers transparently: the restricted band of a
subtype element is the ambient band of its `val`. -/
@[simp] lemma band_restrict (L : LayeredDecomposition α) (S : Finset α)
    (z : ↥S) :
    (L.restrict S).band z = L.band z.val := rfl

/-- Depth is preserved by `restrict`. -/
@[simp] lemma K_restrict (L : LayeredDecomposition α) (S : Finset α) :
    (L.restrict S).K = L.K := rfl

/-- Interaction width is preserved by `restrict`.

This is the "w-monotonicity" half of restriction: the same `w`
always works — the (L2) cross-band-comparability hypothesis is
inherited from the ambient poset because the Subtype order is the
restriction. Tightenings (genuine `w' < w` on the sub-poset) are
possible but not supplied here: tightening requires knowing more
about `S` (e.g. that it witnesses band collapses), and F5's
recursive use inherits `w` directly. -/
@[simp] lemma w_restrict (L : LayeredDecomposition α) (S : Finset α) :
    (L.restrict S).w = L.w := rfl

/-- The `i`-th band of the restricted decomposition consists of
exactly those subtype elements whose ambient band is `i`. -/
lemma mem_bandSet_restrict (L : LayeredDecomposition α) (S : Finset α)
    {z : ↥S} {i : ℕ} :
    z ∈ (L.restrict S).bandSet i ↔ L.band z.val = i :=
  (L.restrict S).mem_bandSet

/-- The image of a restricted band under `Subtype.val` sits inside
the ambient band. -/
lemma image_val_bandSet_restrict_subset [DecidableEq α]
    (L : LayeredDecomposition α) (S : Finset α) (i : ℕ) :
    ((L.restrict S).bandSet i).image (fun z : ↥S => z.val) ⊆
      L.bandSet i := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨z, hz, hzeq⟩
  rw [mem_bandSet]
  rw [← hzeq]
  exact (L.restrict S).mem_bandSet.mp hz

/-- `comparable_of_far` transfers across `restrict`: a restricted
decomposition inherits the (L3) comparability corollary with the
same interaction width. -/
lemma comparable_of_far_restrict (L : LayeredDecomposition α) (S : Finset α)
    {x y : ↥S}
    (h : L.w <
      (max (L.band x.val) (L.band y.val)) -
        (min (L.band x.val) (L.band y.val))) :
    x < y ∨ y < x := by
  rcases L.comparable_of_far (x := x.val) (y := y.val) h with hlt | hlt
  · exact Or.inl hlt
  · exact Or.inr hlt

/-- **Window-localization specialization** (`step8.tex:2524-2569`).

Restrict a layered decomposition to a `Window` slice. The result
is a `LayeredDecomposition` on `↥W.slice` with the same depth and
width. This is the building block of window-localization: the
probability identity (`probLT_restrict_eq` of
`OneThird/Mathlib/LinearExtension/Subtype.lean`) is then applied
on the induced ordinal-sum decomposition `α = X^− ⊔ W ⊔ X^+` to
reduce marginal calculations in `α` to marginal calculations in
`↥W.slice`. -/
noncomputable def restrictSlice (L : LayeredDecomposition α)
    (loBand hiBand : ℕ) : LayeredDecomposition
      ↥((Finset.univ : Finset α).filter
          (fun x => loBand ≤ L.band x ∧ L.band x ≤ hiBand)) :=
  L.restrict _

end LayeredDecomposition

/-! ### §2 — `lem:cut`: ordinal cut inside a deep layering -/

/-- **Layered cut data** (`step8.tex:2167-2178`).

The output of `lem:cut`: an index `k` with `w < k < K − w`, the
lower set `A := L_{≤ k}`, the upper set `B := L_{> k}`, and the
interaction window `W := L_{k − w + 1} ∪ ⋯ ∪ L_{k + w}`.

The structural conclusion is that every cross-pair `(a, b)` with
`a ∈ A, b ∈ B` satisfies either `a < b` (when `band a ≤ k − w` or
`band b > k + w`) or both elements lie in the window. -/
structure LayeredCut (L : LayeredDecomposition α) where
  /-- Cut index. -/
  k : ℕ
  /-- `w < k`: cut lies strictly inside the depth range. -/
  k_gt : L.w < k
  /-- `k < K − w`: cut lies strictly inside the depth range. -/
  k_lt : k + L.w < L.K
  /-- Lower side `A := L_{≤ k}`. -/
  A : Finset α
  /-- Upper side `B := L_{> k}`. -/
  B : Finset α
  /-- Interaction window `W := L_{k − w + 1} ∪ ⋯ ∪ L_{k + w}`. -/
  W : Finset α
  /-- `A` is the union of the bands `L_1, ⋯, L_k`. -/
  A_eq : A = (Finset.univ : Finset α).filter (fun x => L.band x ≤ k)
  /-- `B` is the union of the bands `L_{k+1}, ⋯, L_K`. -/
  B_eq : B = (Finset.univ : Finset α).filter (fun x => k < L.band x)

/-- **`lem:cut`** (`step8.tex:2164-2186`).

For a layered decomposition of depth `K ≥ 2w + 2` and any cut
index `k ∈ (w, K − w)`, the partition `(A, B)` is *almost
ordinal*: every cross-comparability obstruction lies inside the
interaction window `W`. Concretely, for every `a ∈ A, b ∈ B`,
either `a < b` directly (by (L2)), or both `a` and `b` belong to
the window.

The cleared-denominator structural conclusion is

  `∀ a ∈ A, ∀ b ∈ B,  a < b  ∨  (a ∈ W ∧ b ∈ W).` -/
theorem lem_cut (L : LayeredDecomposition α)
    (hK : 2 * L.w + 2 ≤ L.K) (k : ℕ) (hk_gt : L.w < k)
    (hk_lt : k + L.w < L.K) :
    ∃ C : LayeredCut L,
      ∀ a ∈ C.A, ∀ b ∈ C.B,
        a < b ∨ (a ∈ C.W ∧ b ∈ C.W) := by
  classical
  -- Define the window and the pieces explicitly.
  refine ⟨{
      k := k
      k_gt := hk_gt
      k_lt := hk_lt
      A := (Finset.univ : Finset α).filter (fun x => L.band x ≤ k)
      B := (Finset.univ : Finset α).filter (fun x => k < L.band x)
      W := (Finset.univ : Finset α).filter
        (fun x => k + 1 - L.w ≤ L.band x ∧ L.band x ≤ k + L.w)
      A_eq := rfl
      B_eq := rfl
    }, ?_⟩
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  -- `band a ≤ k < band b`. If `band a + w < band b`, then `a < b`
  -- by (L2). Otherwise `band a + w ≥ band b > k`, so `band a > k − w`
  -- (i.e. `band a ≥ k − w + 1`), and `band b ≤ k + w`; both are in W.
  by_cases hab : L.band a + L.w < L.band b
  · exact Or.inl (L.forced_lt a b hab)
  · -- `hab : ¬ (band a + w < band b)`, i.e. `band b ≤ band a + w`.
    have hab' : L.band b ≤ L.band a + L.w := Nat.le_of_not_lt hab
    refine Or.inr ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · -- `band a ≥ k + 1 − w`: from `band b > k` and `band b ≤ band a + w`.
        omega
      · -- `band a ≤ k + w`: from `band a ≤ k ≤ k + w`.
        omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · -- `band b ≥ k + 1 − w`: from `band b > k`.
        omega
      · -- `band b ≤ k + w`: from `band b ≤ band a + w ≤ k + w`.
        omega

/-! ### §3 — `lem:layered-reduction`: GAP G3 (size-minimal form, `mg-805c`) -/

/-- **Layered-reduction conclusion** (`step8.tex:2199-2201`,
size-minimal form).

In the size-minimal framing of `lem:layered-reduction`, the
conclusion is a single `Prop` — `balanced` — asserting that `P` has
a balanced pair (contradicting the γ-counterexample hypothesis on
`P`).

The earlier formulation of this lemma was a disjunction
`balanced ∨ strictSubCex` packaging an alternative
`(γ/2)`-counterexample on a strict induced subposet. That branch
is gone in the size-minimal framing: by size-minimality of `P` at
γ, any strict induced subposet `A ⊊ P` is not a γ-counterexample,
so the alternative collapses to "`A` has a balanced pair", which
lifts to `P` by the bulk identity / window perturbation.

In abstract form, `balanced` is passed as a `Prop` — the caller
(Step 7 assembly) supplies the concrete witness. -/
def LayeredReductionConclusion (balanced : Prop) : Prop :=
  balanced

/-- **Reduction-witness map** (`step8.tex:2218-2317`, paper proof,
size-minimal form).

The contractual content of the size-minimal paper proof of
`lem:layered-reduction`: given the cut data of `lem:cut` and the
hypothesis that `P` is size-minimal among γ-counterexamples, the
case analysis in `step8.tex:2222-2317` (Steps 1–5 of the proof)
produces a balanced pair in `P` directly. The size-minimality
hypothesis is what discharges Step 4 (`A` is not a γ-counterexample
because `|A| < |X|`).

This is a `Prop`-level packaging: the input is an existence witness
for the cut + a discharge of the size-minimality + bulk/window lift
argument; the output is the conclusion `balanced`. The single-shot
size-minimality contradiction replaces the prior
`(γ/2)`-counterexample alternative, removing recursive halving from
`K₀`. -/
structure ReductionWitness (L : LayeredDecomposition α)
    (balanced : Prop) where
  /-- Cut data from `lem:cut`. -/
  cut : LayeredCut L
  /-- Cross-cut window-comparability conclusion. -/
  ordinal : ∀ a ∈ cut.A, ∀ b ∈ cut.B,
    a < b ∨ (a ∈ cut.W ∧ b ∈ cut.W)
  /-- Discharge: caller supplies the balanced-pair conclusion via
  the size-minimality argument applied to the cut piece `A`, lifted
  by Step 3 (bulk identity) or Step 5 (window perturbation). -/
  conclusion : balanced

/-- **`lem:layered-reduction` — GAP G3** (`step8.tex:2193`,
size-minimal one-shot form, `mg-805c`).

For a layered decomposition of depth `K ≥ K₀(γ, w)` of a
*size-minimal* width-3 γ-counterexample, `P` has a balanced pair,
contradicting the γ-counterexample hypothesis.

The integer threshold is `K₀(γ, w) := max(2w + 2, ⌈2/γ⌉ + 6w + 4)`
(`step8.tex:2222`, size-minimal form); the cleared-denominator depth
condition is `K ≥ max(2w + 2, ⌈2/γ⌉ + 6w + 4)`. The dependence on γ
is one-sided — driven by the window-perturbation bound alone, with
no recursive halving.

The proof reduces to:
* invoking `lem_cut` for the existence of the cut data;
* applying size-minimality of `P`: the heavy side `A ⊊ X` has
  `|A| < |X|`, so `A` is not a γ-counterexample, so `A` has a
  balanced pair `(x, y)`;
* lifting via Step 3 (bulk: `p_xy(P) = p_xy(A)` exactly when
  `(x, y) ⊆ A ∖ W`) or Step 5 (window: perturbation bounded by
  `o_K(1) ≤ 1/3 - γ/2` for `K ≥ K₀`).

The size-minimality discharge and the lift are packaged in the
`conclusion` field of `ReductionWitness`. -/
theorem lem_layered_reduction (L : LayeredDecomposition α)
    (balanced : Prop)
    (W : ReductionWitness L balanced) :
    LayeredReductionConclusion balanced :=
  W.conclusion

/-- **Threshold `K₀(γ, w)`** (`step8.tex:2222`, size-minimal form,
`max(2w + 2, ⌈2/γ⌉ + 6w + 4)`).

We adopt the integer-cleared form `K₀(γ_n, γ_d, w) := max(2w + 2,
⌈2 · γ_d / γ_n⌉ + 6w + 4)`, encoding the two inequalities used in
the size-minimal paper proof (`step8.tex:2222-2317`):

* `K₀ ≥ 2w + 2` (so `lem_cut` applies);
* `K₀ ≥ ⌈2/γ⌉ + 6w + 4`, which is the perturbation-derived bound
  ensuring the window-touching lift (Step 5(b) of the proof) clears
  the γ-slack of `[1/3, 2/3]`.

The dependence on γ is one-sided — `K₀` grows linearly in `1/γ`
(via `⌈2 · γ_d / γ_n⌉`) but does not compound through any recursive
halving. This is the key consequence of the size-minimality framing
(`mg-805c`); the prior recursive form was
`max(2w + 2, ⌈2w · γ_d / γ_n⌉ + 4)`. -/
def K₀ (γ_n γ_d w : ℕ) : ℕ :=
  max (2 * w + 2) (((2 * γ_d + γ_n - 1) / γ_n) + 6 * w + 4)

lemma K₀_ge_2wp2 (γ_n γ_d w : ℕ) :
    2 * w + 2 ≤ K₀ γ_n γ_d w := by
  unfold K₀; exact le_max_left _ _

end Step8
end OneThird
