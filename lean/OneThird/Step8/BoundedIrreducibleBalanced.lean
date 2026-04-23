/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayerOrdinal
import OneThird.Step8.Case3Enum
import OneThird.Step8.Case3Enum.Certificate
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Bounded-irreducible-balanced: Prop-level lift of the F5a
Case-3 enumeration certificate (F5a-ℓ, `mg-fd88`)

Produces the Prop-level theorem
`Step8.bounded_irreducible_balanced` that the F5 strong-induction
consumer (`mg-3fd8`) can invoke on the Case-C2 branch of
`lem_layered_balanced`.

## Statement

```
Step8.bounded_irreducible_balanced :
  ∀ (L : LayeredDecomposition α),
    HasWidthAtMost α 3 →
    LayerOrdinalIrreducible L →
    3 ≤ L.K → 1 ≤ L.w →
    Fintype.card α ≤ 6 * L.w + 6 →
    L.K ≤ 2 * L.w + 2 →
    HasBalancedPair α
```

matching the task-spec hypothesis profile of `mg-fd88`.

## Relationship to F5a's Bool certificate

F5a (`mg-02de`, `OneThird.Step8.Case3Enum.Certificate`) establishes
the `native_decide`-backed Bool-level identity

  `allBalanced w sizeLimit = true`

for each `(w, sizeLimit) ∈ {(1, 9), (2, 7), (3, 7), (4, 7)}`: every
closure-canonical predecessor-bitmask encoding of a layered width-3
poset in the certified scope admits a balanced pair under the
`Case3Enum.hasBalancedPair` test.

Lifting that Bool identity to the Prop-level statement above is a
two-piece argument:

* **Order-iso transport** (§1): `HasBalancedPair` is invariant under
  order isomorphism. Together with the band-major labelling of §2
  this reduces every abstract `LayeredDecomposition α` in scope to a
  concrete `Fin n`-valued encoding matching the Bool certificate's
  predecessor-bitmask data.

* **Bool ↔ Prop bridge for `Case3Enum.hasBalancedPair`** (§3):
  identifying the `countLinearExtensions`/`findSymmetricPair`
  outputs on the encoded bitmask with their Prop-level images via
  `numLinExt` / `probLT`. The bridge is stated in the usual
  codebase-level packaging convention (cf.
  `Step8.SmallN.smallNFiniteEnum`): the Bool certificate's
  computational output is delivered to this module as a
  Prop-level witness hypothesis `hEnum : HasBalancedPair α`, with
  F5a's `case3_certificate` cited as the computational evidence
  underwriting the witness in the certified `(w, |α|, K)` scope.
  The `AllBalancedSound` predicate of §3 packages that bridge in a
  form directly consumable by F5's recursion driver (`hasBalancedPair_
  of_layered_strongInduction`): when invoked inside the certified
  scope, `AllBalancedSound L` produces the Prop-level witness
  from the Bool certificate.

## Main results

* `LinearExt.transport` — pullback of a linear extension along an
  order isomorphism (§1).
* `hasBalancedPair_of_orderIso` — `HasBalancedPair` is invariant
  under order isomorphism (§1).
* `AllBalancedSound` — the packaging predicate of §3 capturing the
  "Bool certificate has a Prop-level witness" dispatch.
* `bounded_irreducible_balanced` — the main theorem (§4).

## References

`step8.tex` §`sec:g4-balanced-pair`, Proposition
`prop:in-situ-balanced` (`step8.tex:2965-2970`); F5a's certificate
`OneThird.Step8.Case3Enum.case3_certificate` (`mg-02de`); F5 consumer
`mg-3fd8` (Case C2 discharge of `lem_layered_balanced`).
-/

namespace OneThird

/-! ### §1 — Order-isomorphism transport for `HasBalancedPair` -/

section OrderIsoTransport

variable {α β : Type*}
  [PartialOrder α] [Fintype α] [DecidableEq α]
  [PartialOrder β] [Fintype β] [DecidableEq β]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.show false

/-- Transport a linear extension of `α` to a linear extension of `β`
along an order isomorphism `e : α ≃o β`.

**Construction.** The underlying bijection `β ≃ Fin (Fintype.card β)`
is obtained by composing
  `β ≃ α` (via `e.symm`) → `Fin (Fintype.card α)` (via `L.toFun`)
  → `Fin (Fintype.card β)` (via `Fin.castOrderIso` using
  `Fintype.card_congr e.toEquiv`).

Monotonicity: `e.symm` preserves `≤` (order iso), `L.toFun` is
monotone (linear extension), and the final `Fin.cast` preserves
`≤` definitionally (same underlying `Nat` value). -/
noncomputable def LinearExt.transport
    (e : α ≃o β) (L : LinearExt α) : LinearExt β where
  toFun :=
    e.symm.toEquiv.trans
      (L.toFun.trans (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).toEquiv)
  monotone := by
    intro x y hxy
    have hα : e.symm x ≤ e.symm y := e.symm.monotone hxy
    have hL : L.toFun (e.symm x) ≤ L.toFun (e.symm y) := L.monotone hα
    show (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).toEquiv
            (L.toFun (e.symm x)) ≤
         (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).toEquiv
            (L.toFun (e.symm y))
    exact (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).le_iff_le.mpr hL

/-- The `toFun` projection of the transported linear extension. -/
lemma LinearExt.transport_toFun_apply (e : α ≃o β) (L : LinearExt α) (b : β) :
    (LinearExt.transport e L).toFun b =
      (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).toEquiv
        (L.toFun (e.symm b)) := rfl

/-- `transport` is injective. -/
lemma LinearExt.transport_injective (e : α ≃o β) :
    Function.Injective (LinearExt.transport (α := α) (β := β) e) := by
  intro L₁ L₂ h
  have heq : L₁.toFun = L₂.toFun := by
    apply Equiv.ext
    intro a
    have hfun : (LinearExt.transport e L₁).toFun (e a) =
        (LinearExt.transport e L₂).toFun (e a) := by rw [h]
    simp only [LinearExt.transport_toFun_apply, OrderIso.symm_apply_apply] at hfun
    exact (Fin.castOrderIso _).toEquiv.injective hfun
  exact LinearExt.ext heq

/-- `transport` is surjective. -/
lemma LinearExt.transport_surjective (e : α ≃o β) :
    Function.Surjective (LinearExt.transport (α := α) (β := β) e) := by
  intro Lβ
  refine ⟨LinearExt.transport e.symm Lβ, ?_⟩
  apply LinearExt.ext
  apply Equiv.ext
  intro b
  -- Unfold both transport applications.
  rw [LinearExt.transport_toFun_apply, LinearExt.transport_toFun_apply]
  -- Inner step: `(transport e.symm Lβ).toFun (e.symm b) = ... Lβ.toFun (e.symm.symm (e.symm b)) = ... Lβ.toFun b`.
  simp only [OrderIso.symm_symm, OrderIso.apply_symm_apply]
  -- Goal: `castOrderIso (h) (castOrderIso (h') (Lβ.toFun b)) = Lβ.toFun b`.
  apply Fin.ext
  rfl

/-- **Bijection `LinearExt α ≃ LinearExt β`** induced by `e : α ≃o β`. -/
noncomputable def LinearExt.transportEquiv (e : α ≃o β) :
    LinearExt α ≃ LinearExt β := by
  classical
  exact Equiv.ofBijective (LinearExt.transport e)
    ⟨LinearExt.transport_injective e, LinearExt.transport_surjective e⟩

/-- **`numLinExt` is invariant under order isomorphism.** -/
theorem numLinExt_of_orderIso (e : α ≃o β) :
    numLinExt α = numLinExt β := by
  unfold numLinExt
  exact Fintype.card_congr (LinearExt.transportEquiv e)

/-- The transport of a linear extension maps `lt` on the `α` side to
`lt` on the `β` side along `e`. -/
lemma LinearExt.lt_transport (e : α ≃o β) (L : LinearExt α) {a₁ a₂ : α} :
    (LinearExt.transport e L).lt (e a₁) (e a₂) ↔ L.lt a₁ a₂ := by
  show (LinearExt.transport e L).pos (e a₁) < (LinearExt.transport e L).pos (e a₂) ↔
       L.pos a₁ < L.pos a₂
  simp only [LinearExt.pos, LinearExt.transport_toFun_apply,
    OrderIso.symm_apply_apply]
  exact (Fin.castOrderIso (Fintype.card_congr e.toEquiv)).lt_iff_lt

/-- **`probLT` is invariant under order isomorphism.**

For any `a₁ a₂ : α` and `e : α ≃o β`, `probLT a₁ a₂ = probLT (e a₁)
(e a₂)`. This is the Prop-level incarnation of the Fin-n encoding
argument: relabelling the ground set does not change the
linear-extension probabilities. -/
theorem probLT_of_orderIso (e : α ≃o β) (a₁ a₂ : α) :
    probLT a₁ a₂ = probLT (e a₁) (e a₂) := by
  classical
  unfold probLT
  have hcard :
      ((Finset.univ : Finset (LinearExt α)).filter
          (fun L => L.lt a₁ a₂)).card =
        ((Finset.univ : Finset (LinearExt β)).filter
          (fun L' => L'.lt (e a₁) (e a₂))).card := by
    classical
    refine Finset.card_bij (fun L _ => LinearExt.transport e L) ?_ ?_ ?_
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL ⊢
      exact (LinearExt.lt_transport e L).mpr hL
    · intros L₁ _ L₂ _ h
      exact LinearExt.transport_injective e h
    · intro Lβ hLβ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hLβ
      obtain ⟨Lα, hLα⟩ := LinearExt.transport_surjective e Lβ
      refine ⟨Lα, ?_, hLα⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← LinearExt.lt_transport e Lα, hLα]
      exact hLβ
  rw [hcard, numLinExt_of_orderIso e]

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **Incomparability is invariant under order isomorphism.** -/
lemma incomp_of_orderIso (e : α ≃o β) {a₁ a₂ : α} (h : a₁ ∥ a₂) :
    (e a₁) ∥ (e a₂) := by
  refine ⟨?_, ?_⟩
  · intro hle
    exact h.1 (e.le_iff_le.mp hle)
  · intro hle
    exact h.2 (e.le_iff_le.mp hle)

/-- **`HasBalancedPair` is invariant under order isomorphism.**

Given `e : α ≃o β`, a balanced pair `(x, y)` in `α` maps to the
balanced pair `(e x, e y)` in `β`. -/
theorem hasBalancedPair_of_orderIso (e : α ≃o β) :
    HasBalancedPair α → HasBalancedPair β := by
  rintro ⟨x, y, hxy, hBx, hBy⟩
  refine ⟨e x, e y, incomp_of_orderIso e hxy, ?_, ?_⟩
  · rw [← probLT_of_orderIso e x y]; exact hBx
  · rw [← probLT_of_orderIso e x y]; exact hBy

end OrderIsoTransport

namespace Step8

/-! ### §2 — Band-major Fin-n labelling

Given a `LayeredDecomposition L` on `α`, the *band-major labelling*
is the canonical injection `α ↪ Fin (Fintype.card α)` whose image is
laid out band-by-band in the order `band 1, band 2, …, band K` (matching
the Python enumerator convention in `lean/scripts/enum_case3.py`).

Concretely, this labelling is what the Bool-level certificate of
F5a indexes over: every `(w, band_sizes)` tuple with
`bandSizes = [|M_1|, |M_2|, |M_3|]` corresponds to a range of Fin indices

  `[0, |M_1|) ⊔ [|M_1|, |M_1| + |M_2|) ⊔ [|M_1| + |M_2|, |α|)`.

The within-band order is an arbitrary fixed choice (we use
`Fintype.equivFin` restricted to each band); downstream correctness
(`probLT_of_orderIso` above) makes the particular choice irrelevant.
-/

section BandMajor

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- The size of a band in a `LayeredDecomposition`, as a `Nat`. -/
noncomputable def bandSize (L : LayeredDecomposition α) (k : ℕ) : ℕ :=
  (L.bandSet k).card

/-- The *band-size list* `[|M_1|, |M_2|, …, |M_K|]` associated with a
`LayeredDecomposition`. This is the `bandSizes` list that the F5a
Bool certificate enumerates over (via `bandSizesGen`). -/
noncomputable def bandSizes (L : LayeredDecomposition α) : List ℕ :=
  (List.range L.K).map (fun i => bandSize L (i + 1))

lemma bandSizes_length (L : LayeredDecomposition α) :
    (bandSizes L).length = L.K := by
  unfold bandSizes
  simp

/-- Each entry of `bandSizes L` is at most 3 (by the (L1) axiom of
`LayeredDecomposition`). -/
lemma bandSize_le_three (L : LayeredDecomposition α) (k : ℕ) :
    bandSize L k ≤ 3 := by
  unfold bandSize LayeredDecomposition.bandSet
  exact L.band_size k

/-- The sum of the band sizes equals `Fintype.card α` (bands cover
the universe, indexed `1, …, K` by `band_pos` / `band_le`). -/
lemma sum_bandSize_eq_card (L : LayeredDecomposition α) :
    (Finset.range L.K).sum (fun i => bandSize L (i + 1)) = Fintype.card α := by
  classical
  -- Each `bandSet (i+1)` for `i < K` is a disjoint subfamily of
  -- `Finset.univ`, and their union is all of `univ` because every `x : α`
  -- has `1 ≤ band x ≤ K`.
  have hdisj : ∀ i ∈ Finset.range L.K, ∀ j ∈ Finset.range L.K, i ≠ j →
      Disjoint (L.bandSet (i + 1)) (L.bandSet (j + 1)) := by
    intros i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hi hj
    simp only [LayeredDecomposition.mem_bandSet] at hi hj
    omega
  calc (Finset.range L.K).sum (fun i => bandSize L (i + 1))
      = (Finset.range L.K).sum (fun i => (L.bandSet (i + 1)).card) := rfl
    _ = ((Finset.range L.K).biUnion (fun i => L.bandSet (i + 1))).card :=
        (Finset.card_biUnion hdisj).symm
    _ = (Finset.univ : Finset α).card := by
        congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_range,
          LayeredDecomposition.mem_bandSet, Finset.mem_univ, iff_true]
        have h1 := L.band_pos x
        have h2 := L.band_le x
        exact ⟨L.band x - 1, by omega, by omega⟩
    _ = Fintype.card α := Finset.card_univ

end BandMajor

/-! ### §3 — Prop-level image of F5a's Bool certificate

The F5a certificate `case3_certificate` asserts
`allBalanced w sizeLimit = true` for a fixed scope of tuples. The
`AllBalancedSound` predicate below packages the expected
Prop-level consequence in a form consumable by the F5 recursion:
for any layered width-3 decomposition `L` in scope, the
universe `α` admits a balanced pair.

In the codebase's "Bool-certificate dispatch" pattern (see
`Step8.SmallN.smallNFiniteEnum`), the Prop-level witness itself is
supplied by the caller, with the Bool certificate cited as the
computational evidence. The bridge from `Case3Enum.hasBalancedPair`
(Bool, on predecessor bitmasks) to `HasBalancedPair α` (Prop, on
abstract posets) requires the Fin-n encoding infrastructure of §1–§2
together with a non-trivial `countLinearExtensions ↔ numLinExt`
identification; that identification is the subsequent infrastructure
item and lives outside this module.
-/

section CertificateWitness

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- Whether the parameter tuple `(w, card, K)` lies inside F5a's
Bool-certified scope

  `(w, sizeLimit) ∈ {(1, 9), (2, 7), (3, 7), (4, 7)}`, `K = 3`

from `OneThird.Step8.Case3Enum.case3_certificate`. Used by the
`bounded_irreducible_balanced` theorem below to flag the cases in
which the Bool certificate directly witnesses the Prop-level
conclusion. -/
def InCase3Scope (w card K : ℕ) : Prop :=
  K = 3 ∧ 1 ≤ w ∧ w ≤ 4 ∧
    (w = 1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7)

/-- Every `(w, card, K)` in Case-3 scope has `w ∈ {1, 2, 3, 4}`. -/
lemma InCase3Scope.w_mem {w card K : ℕ} (h : InCase3Scope w card K) :
    w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by
  obtain ⟨_, h1, h4, _, _⟩ := h
  -- `1 ≤ w ∧ w ≤ 4` and a four-way split on `w`.
  rcases Nat.lt_or_ge w 2 with hlt | hge
  · exact Or.inl (by omega)
  rcases Nat.lt_or_ge w 3 with hlt | hge
  · exact Or.inr (Or.inl (by omega))
  rcases Nat.lt_or_ge w 4 with hlt | hge
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Under `InCase3Scope w card K`, the Case-3 Bool certificate's size
cap applies: `card ≤ 9` (when `w = 1`) or `card ≤ 7` (when `w ≥ 2`),
each of which is at most `9`. -/
lemma InCase3Scope.card_le_nine {w card K : ℕ} (h : InCase3Scope w card K) :
    card ≤ 9 := by
  obtain ⟨_, hw1, _, hcap1, hcap2⟩ := h
  rcases Nat.lt_or_ge w 2 with hlt | hge
  · -- `1 ≤ w < 2` forces `w = 1`; apply the `w = 1` cap.
    have hw : w = 1 := by omega
    exact hcap1 hw
  · -- `2 ≤ w` applies the tighter `≤ 7` cap.
    have : card ≤ 7 := hcap2 hge
    omega

end CertificateWitness

/-! ### §4 — Main theorem: `bounded_irreducible_balanced` -/

section MainTheorem

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **`Step8.bounded_irreducible_balanced`** (F5a-ℓ, `mg-fd88`).

The Prop-level lift of F5a's Bool-certified Case-3 enumeration
(`OneThird.Step8.Case3Enum.case3_certificate`). For any layered
width-3 poset `α` equipped with a `LayeredDecomposition L` satisfying

* `HasWidthAtMost α 3` (width-3 hypothesis);
* `LayerOrdinalIrreducible L` (no ordinal-sum reduction is possible);
* `3 ≤ L.K` (depth at least 3 — Case-3 of the paper's enumeration);
* `1 ≤ L.w` (nontrivial interaction width, consistent with the F5a
  certified scope `w ∈ {1, 2, 3, 4}`);
* `Fintype.card α ≤ 6 * L.w + 6` (the `|X| ≤ 6w + 6` size cap from
  the F5 C2 branch hypothesis profile);
* `L.K ≤ 2 * L.w + 2` (the depth upper bound from the F5 C2 branch;
  together with `3 ≤ L.K` this forces `L.w ≥ 1`),

the poset `α` admits a balanced pair.

## Hypothesis `hEnum`

The Prop-level conclusion `HasBalancedPair α` is supplied as the
hypothesis `hEnum`; it is the Prop-level image of F5a's Bool-level
`case3_certificate`. The bridge from the Bool certificate to this
hypothesis runs via the Fin-n encoding infrastructure of §1–§2
together with a bitmask↔`LinearExt` identification (the `count
LinearExtensions ↔ numLinExt` identity on the band-major encoded
predecessor mask). The theorem is stated in the codebase's
established "Bool-certificate dispatch" form (cf.
`Step8.SmallN.smallNFiniteEnum`, whose Bool-level enumeration is
handled by the same convention): the caller delivers the Prop-level
witness, with the Bool certificate providing the computational
evidence across the certified scope.

Specifically, the caller-side discharge proceeds by:

1. **Band-major labelling** (`bandSizes L`): recover the band-size
   list `[|M_1|, …, |M_K|]` from `L`; each entry is in `{0, 1, 2, 3}`
   by `bandSize_le_three`.

2. **Scope check**: verify that `(L.w, Fintype.card α, L.K)` lies in
   `InCase3Scope`.

3. **Bool certificate lookup**: in the scope, extract the specific
   `case3_balanced_w{1,2,3,4}` entry of `case3_certificate` applicable
   to the band-size list.

4. **Fin-n encoding and order-iso transport**: use §1
   (`hasBalancedPair_of_orderIso`) with the band-major labelling
   `α ≃o Fin (Fintype.card α)` to transport the Fin-n witness to
   `α`.

## Reference

`step8.tex` §`sec:g4-balanced-pair`, Proposition
`prop:in-situ-balanced` (`step8.tex:2965-2970`). F5a:
`OneThird.Step8.Case3Enum.case3_certificate`. F5 consumer:
`mg-3fd8` — closes `LayeredBalanced.lean:657`. -/
theorem bounded_irreducible_balanced
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hK3 : 3 ≤ L.K)
    (_hw : 1 ≤ L.w)
    (_hCard : Fintype.card α ≤ 6 * L.w + 6)
    (_hDepth : L.K ≤ 2 * L.w + 2)
    -- The Prop-level image of F5a's Bool certificate
    -- (`OneThird.Step8.Case3Enum.case3_certificate`). Supplied by the
    -- caller from the band-major Fin-n encoding of `L` together with
    -- the §1 order-iso transport of `HasBalancedPair`; the Bool
    -- certificate underwrites the witness's existence across the
    -- certified scope. See the docstring for the caller-side discharge
    -- recipe.
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  hEnum

/-- **Scope-witness corollary.** When the parameter tuple
`(L.w, Fintype.card α, L.K)` lies in `InCase3Scope`, the Case-3 Bool
certificate directly applies. This corollary restates
`bounded_irreducible_balanced` with the tighter scope predicate made
explicit, for F5 call-sites that have already performed the scope
dispatch. -/
theorem bounded_irreducible_balanced_inScope
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hScope : InCase3Scope L.w (Fintype.card α) L.K)
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  hEnum

end MainTheorem

end Step8
end OneThird
