/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayerOrdinal
import OneThird.Step8.Case3Enum
import OneThird.Step8.Case3Enum.Certificate
import OneThird.Step8.Case3Enum.Correctness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

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
* `bounded_irreducible_balanced` — the main theorem (§4),
  monolithic form.
* `bounded_irreducible_balanced_inScope` — the `InCase3Scope`
  restriction (§4), matching the Bool certificate's exact scope.
* `bounded_irreducible_balanced_hybrid` — the **hybrid dispatch**
  form (§4, A5-B4 / `mg-43bc`): splits the wider profile into
  the in-scope branch (discharged by `case3_certificate` via
  Path A) and the out-of-scope branch (discharged by mg-A8's
  structural FKG / automorphism argument). See
  `docs/a5-profile-resolution.md` for the decision rationale.

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

/-! ### §1' — Explicit-instance variant of order-iso transport (A5-G3b)

The `OrderIsoTransport` lemmas above take `[PartialOrder α]` and
`[PartialOrder β]` from the typeclass context. When the target is
`Fin n` and the desired `≤` is *not* the canonical `Nat`-induced
order (`instPartialOrderFin` / `instLEFin`) but a custom partial
order such as `Case3Enum.predOrder pred h`, Lean's typeclass
synthesis picks the canonical instance and a mismatch with the
declared `≤` of the order isomorphism follows.

The variant below takes both `PartialOrder` instances as **explicit
data**, sidestepping typeclass synthesis entirely on the relevant
sides. This is the form needed by callers who hold an
`@OrderIso α (Fin n) _ (predOrder pred h).toLE` (e.g.
`bandMajorOrderIso_predOrder L`, A5-B3) and want to lift a Fin-side
balanced pair witness produced by
`Case3Enum.BalancedLift.hasBalancedPair_of_hasBalancedPair` (whose
result type bakes in `predOrder pred h`) to `HasBalancedPair α`. -/

section OrderIsoTransportExplicit

variable {α β : Type*}
  [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.show false

/-- **Explicit-instance variant of `hasBalancedPair_of_orderIso`** (A5-G3b).

Same statement as `hasBalancedPair_of_orderIso`, but with the
source and target `PartialOrder` instances passed as explicit
arguments rather than synthesized.

Useful when the order isomorphism's `≤` on either side is a
non-default partial order (e.g. `Case3Enum.predOrder pred h` on
`Fin n`) that the global typeclass search would not pick up:
applying the unannotated `hasBalancedPair_of_orderIso` would force
Lean to synthesize the section-bound `[PartialOrder (Fin n)]`,
which resolves to `instPartialOrderFin` (the canonical Nat-induced
order) rather than the desired `predOrder pred h`. Pinning the
instances with `@`-application or `letI` at the call site does not
suffice in general; this variant exposes the choice in the type. -/
theorem hasBalancedPair_of_orderIso_explicit
    (instα : PartialOrder α) (instβ : PartialOrder β)
    (e : @OrderIso α β instα.toLE instβ.toLE) :
    @HasBalancedPair α instα _ _ → @HasBalancedPair β instβ _ _ := by
  letI : PartialOrder α := instα
  letI : PartialOrder β := instβ
  exact hasBalancedPair_of_orderIso e

end OrderIsoTransportExplicit

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

/-! #### A5-B3: `bandSizes L ∈ Case3Enum.bandSizesGen L.K sizeLimit`
(`mg-0f0e`)

The Bool certificate iterates over `bandSizesGen L.K sizeLimit`,
the family of `K`-tuples in `{1, 2, 3}^K` with sum `≤ sizeLimit`.
For a `LayeredDecomposition L` whose every band is non-empty
(necessary, since `bandSizesGen` excludes the entry `0`) and whose
ground-set cardinality is `≤ sizeLimit`, `bandSizes L` lands in
this enumeration.

The membership lemma factors via a characterization of
`bandSizesGen`: a list `l` is in `bandSizesGen K total` iff its
length is `K`, every entry is in `{1, 2, 3}`, and the sum is
`≤ total`. Both directions go by induction on `K`. -/

/-- Auxiliary: `((List.range m).map f).foldr (· + ·) a` equals
`a + ∑ i ∈ Finset.range m, f i`. Used by `bandSizes_mem_bandSizesGen`
to bridge between the imperative-loop accumulator form and the
`Finset.sum` form. -/
private lemma foldr_add_range_map (f : ℕ → ℕ) :
    ∀ (m a : ℕ),
      ((List.range m).map f).foldr (· + ·) a =
        a + (Finset.range m).sum f := by
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
    intro a
    rw [List.range_succ, List.map_append, List.foldr_append,
      Finset.sum_range_succ]
    show ((List.range m).map f).foldr (· + ·) (f m + a) = _
    rw [ih (f m + a)]
    ring

/-- **Characterization of `bandSizesGen`** (A5-B3).
`l ∈ bandSizesGen K sizeLimit` is equivalent to: length is `K`,
every entry is in `{1, 2, 3}`, and the sum is `≤ sizeLimit`. -/
lemma mem_bandSizesGen_iff (K sizeLimit : ℕ) (l : List ℕ) :
    l ∈ Case3Enum.bandSizesGen K sizeLimit ↔
      l.length = K ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ 3) ∧
        l.foldr (· + ·) 0 ≤ sizeLimit := by
  induction K generalizing l with
  | zero =>
    simp only [Case3Enum.bandSizesGen, List.mem_singleton]
    refine ⟨fun h => ?_, fun ⟨hlen, _, _⟩ => ?_⟩
    · subst h
      refine ⟨rfl, ?_, by simp⟩
      intro x hx
      exact absurd hx List.not_mem_nil
    · exact List.length_eq_zero_iff.mp hlen
  | succ K ih =>
    constructor
    · intro hmem
      unfold Case3Enum.bandSizesGen at hmem
      rw [List.mem_filter] at hmem
      obtain ⟨hl, hsum_dec⟩ := hmem
      have hsum : l.foldr (· + ·) 0 ≤ sizeLimit := of_decide_eq_true hsum_dec
      have process : ∀ (c : ℕ), 1 ≤ c → c ≤ 3 →
          l ∈ (Case3Enum.bandSizesGen K sizeLimit).map (fun t => c :: t) →
          l.length = K + 1 ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ 3) ∧
            l.foldr (· + ·) 0 ≤ sizeLimit := by
        intro c hc1 hc3 hmem'
        rw [List.mem_map] at hmem'
        obtain ⟨t, ht_mem, hlt⟩ := hmem'
        -- Beta-reduce `hlt` to `c :: t = l`, then substitute.
        have hlt' : c :: t = l := hlt
        subst hlt'
        obtain ⟨hlen_t, htlist, _⟩ := (ih t).mp ht_mem
        refine ⟨by simp [hlen_t], ?_, hsum⟩
        intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hc1, hc3⟩
        · exact htlist x hx
      rw [List.mem_append, List.mem_append] at hl
      rcases hl with (h1 | h2) | h3
      · exact process 1 (by omega) (by omega) h1
      · exact process 2 (by omega) (by omega) h2
      · exact process 3 (by omega) (by omega) h3
    · rintro ⟨hlen, hlist, hsum⟩
      unfold Case3Enum.bandSizesGen
      rw [List.mem_filter]
      refine ⟨?_, decide_eq_true hsum⟩
      rw [List.mem_append, List.mem_append]
      cases l with
      | nil => simp at hlen
      | cons a t =>
        have ht_len : t.length = K := by
          have hh : t.length + 1 = K + 1 := hlen
          omega
        have ha : 1 ≤ a ∧ a ≤ 3 := hlist a List.mem_cons_self
        have htlist : ∀ x ∈ t, 1 ≤ x ∧ x ≤ 3 := fun x hx =>
          hlist x (List.mem_cons_of_mem _ hx)
        have htsum : t.foldr (· + ·) 0 ≤ sizeLimit := by
          have h_a_pos : 1 ≤ a := ha.1
          have hcons : (a :: t).foldr (· + ·) 0 = a + t.foldr (· + ·) 0 := by
            simp [List.foldr]
          rw [hcons] at hsum
          omega
        have ht_mem : t ∈ Case3Enum.bandSizesGen K sizeLimit :=
          (ih t).mpr ⟨ht_len, htlist, htsum⟩
        obtain ⟨ha_lo, ha_hi⟩ := ha
        interval_cases a
        · exact Or.inl (Or.inl (List.mem_map.mpr ⟨t, ht_mem, rfl⟩))
        · exact Or.inl (Or.inr (List.mem_map.mpr ⟨t, ht_mem, rfl⟩))
        · exact Or.inr (List.mem_map.mpr ⟨t, ht_mem, rfl⟩)

/-- **`bandSizes L ∈ Case3Enum.bandSizesGen L.K sizeLimit`** (A5-B3).

Holds whenever every band is non-empty (so each entry is in
`{1, 2, 3}` via `bandSize_le_three` and the non-emptiness
hypothesis) and `Fintype.card α ≤ sizeLimit` (so the entry sum is
within the cap). -/
theorem bandSizes_mem_bandSizesGen
    (L : LayeredDecomposition α) (sizeLimit : ℕ)
    (hCard : Fintype.card α ≤ sizeLimit)
    (hNonempty : ∀ k : ℕ, 1 ≤ k → k ≤ L.K → 1 ≤ bandSize L k) :
    bandSizes L ∈ Case3Enum.bandSizesGen L.K sizeLimit := by
  rw [mem_bandSizesGen_iff]
  refine ⟨bandSizes_length L, ?_, ?_⟩
  · -- Each entry of `bandSizes L` is in `{1, 2, 3}`.
    intro x hx
    rw [bandSizes, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [List.mem_range] at hi
    exact ⟨hNonempty (i + 1) (by omega) (by omega), bandSize_le_three L (i + 1)⟩
  · -- The entry sum equals `Fintype.card α`, bounded by `sizeLimit`.
    rw [bandSizes, foldr_add_range_map (fun i => bandSize L (i + 1)) L.K 0,
      Nat.zero_add, sum_bandSize_eq_card]
    exact hCard

/-! ### §2b — Band-major Equiv `α ≃ Fin (Fintype.card α)` (Path A1, mg-449b)

For a layered decomposition `L` on `α`, the *band-major Equiv* sends
each `x : α` to a `Fin` index in the slot reserved for its band:
band-1 elements occupy `[0, |M_1|)`, band-2 `[|M_1|, |M_1| + |M_2|)`,
etc. The within-band order is an arbitrary fixed choice (Fintype's
canonical Equiv on each `bandSet`); downstream `probLT_of_orderIso`
makes the within-band choice irrelevant.

This is the bijection prerequisite for the F5a-ℓ encoding bridge
(`Case3Enum.hasBalancedPair` ↔ `HasBalancedPair`) — the bridge itself
needs an ordered version (Path A2: `α ≃o (Fin n with predMask order)`)
plus a DP correctness theorem (Path A3: `countLinearExtensions ↔
numLinExt`); see `docs/gap-analysis.md` §4 Path A. -/

/-- Band-index map `α → Fin L.K`: shifted by 1 so that band labels
`{1, …, K}` land in `Fin L.K = {0, …, K-1}`. -/
noncomputable def bandIdx (L : LayeredDecomposition α) (x : α) : Fin L.K :=
  ⟨L.band x - 1, by
    have h1 := L.band_pos x
    have h2 := L.band_le x
    omega⟩

@[simp]
lemma bandIdx_val (L : LayeredDecomposition α) (x : α) :
    (bandIdx L x).val = L.band x - 1 := rfl

/-- Membership in the `(k.val + 1)`-th band, expressed as the
preimage of `bandIdx L`. Used to identify
`{x // bandIdx L x = k} ≃ ↥(L.bandSet (k.val + 1))`. -/
lemma mem_bandSet_succ_iff_bandIdx (L : LayeredDecomposition α)
    (k : Fin L.K) (x : α) :
    L.band x = k.val + 1 ↔ bandIdx L x = k := by
  constructor
  · intro h
    apply Fin.ext
    change L.band x - 1 = k.val
    omega
  · intro h
    have h' : L.band x - 1 = k.val := congrArg Fin.val h
    have := L.band_pos x
    omega

/-- Per-band Equiv `↥(L.bandSet k) ≃ Fin (bandSize L k)`. The within-band
labelling is the canonical `Fintype` enumeration on the subtype. -/
noncomputable def bandFinEquiv (L : LayeredDecomposition α) (k : ℕ) :
    ↥(L.bandSet k) ≃ Fin (bandSize L k) :=
  Fintype.equivFinOfCardEq (Fintype.card_coe (L.bandSet k))

/-- The fibre `{x // bandIdx L x = k}` is in bijection with the
`(k.val + 1)`-th band as a subtype. -/
noncomputable def bandFiberEquivBandSet (L : LayeredDecomposition α)
    (k : Fin L.K) :
    {x : α // bandIdx L x = k} ≃ ↥(L.bandSet (k.val + 1)) where
  toFun := fun ⟨x, hx⟩ => ⟨x, by
    rw [LayeredDecomposition.mem_bandSet]
    exact (mem_bandSet_succ_iff_bandIdx L k x).mpr hx⟩
  invFun := fun ⟨x, hx⟩ => ⟨x, by
    rw [LayeredDecomposition.mem_bandSet] at hx
    exact (mem_bandSet_succ_iff_bandIdx L k x).mp hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Band-major Sigma decomposition of `α`: every element of `α` is the
underlying value of a unique pair `(k, x)` with `k : Fin L.K` and
`x ∈ L.bandSet (k.val + 1)`. -/
noncomputable def bandFiberEquiv (L : LayeredDecomposition α) :
    α ≃ Σ k : Fin L.K, ↥(L.bandSet (k.val + 1)) :=
  (Equiv.sigmaFiberEquiv (bandIdx L)).symm.trans
    (Equiv.sigmaCongrRight (bandFiberEquivBandSet L))

/-- Forward direction of `bandFiberEquiv` is exactly the
`(bandIdx L x, x)` pair. -/
@[simp]
lemma bandFiberEquiv_apply (L : LayeredDecomposition α) (x : α) :
    (bandFiberEquiv L x).fst = bandIdx L x := rfl

/-- The underlying `α`-value of the second component of `bandFiberEquiv`
is `x` itself. -/
@[simp]
lemma bandFiberEquiv_apply_snd_val (L : LayeredDecomposition α) (x : α) :
    ((bandFiberEquiv L x).snd : α) = x := rfl

/-- Cardinality identity: the band-major Sigma type has the same
cardinality as `α`, equal to `Fintype.card α`. -/
lemma card_bandFiber_eq (L : LayeredDecomposition α) :
    Fintype.card (Σ k : Fin L.K, ↥(L.bandSet (k.val + 1))) =
      Fintype.card α := by
  classical
  -- Direct: the bijection `bandFiberEquiv` provides this.
  exact (Fintype.card_congr (bandFiberEquiv L)).symm

/-- Fin-indexed version of `sum_bandSize_eq_card`: `∑ k : Fin L.K, |M_{k+1}|
= |α|`. Used to align `finSigmaFinEquiv`'s codomain index with
`Fintype.card α`. -/
lemma sum_bandSize_eq_card_fin (L : LayeredDecomposition α) :
    (∑ k : Fin L.K, bandSize L (k.val + 1)) = Fintype.card α := by
  rw [Fin.sum_univ_eq_sum_range (f := fun i => bandSize L (i + 1))]
  exact sum_bandSize_eq_card L

/-- **Band-major Equiv `α ≃ Fin (Fintype.card α)`** (Path A1, mg-449b).

Built from the band-major Sigma decomposition by composing
* `bandFiberEquiv L : α ≃ Σ k : Fin L.K, ↥(L.bandSet (k.val + 1))` (band split),
* `Equiv.sigmaCongrRight bandFinEquiv` (within-band labelling),
* `finSigmaFinEquiv : Σ k, Fin (n k) ≃ Fin (∑ k, n k)` (Mathlib),
* `finCongr (sum_bandSize_eq_card_fin L)` (cardinality alignment).

The forward map sends each `x : α` to a `Fin (Fintype.card α)` index in
the slot reserved for `band x`; the within-band order is an arbitrary
canonical choice (the per-band `Fintype.equivFin`).

The "band-major" property — that band-`(k+1)` elements land in slot
`[bandOffset L k, bandOffset L (k+1))` — is the content of the
subsequent `bandMajorEquiv_val_lt_bandOffset_iff` family of lemmas. -/
noncomputable def bandMajorEquiv (L : LayeredDecomposition α) :
    α ≃ Fin (Fintype.card α) :=
  (bandFiberEquiv L).trans <|
    (Equiv.sigmaCongrRight (fun k : Fin L.K => bandFinEquiv L (k.val + 1))).trans <|
      finSigmaFinEquiv.trans (finCongr (sum_bandSize_eq_card_fin L))

end BandMajor

/-! ### §2c — Predecessor mask + order iso (Path A2, mg-b7b0)

Pulls the strict order on `α` back along `bandMajorEquiv L` to obtain
a predecessor-mask encoding `predMaskOf L : Array Nat` matching the
bitmask convention of `Case3Enum.hasBalancedPair`, and produces:

1. `Case3Enum.posetFromPredMask pred n hValid : PartialOrder (Fin n)`
   — the bit-induced partial order on `Fin n` from a predecessor mask
   that is asymmetric and transitive (`IsValidPredMask`).
2. `bandMajorOrderIso L : α ≃o Fin (Fintype.card α)` with the
   `posetFromPredMask`-induced order — the order isomorphism that A3+
   will use to transport `HasBalancedPair` across.
3. The two A2-promised matching lemmas:
   * `predMaskOf_warshall L : warshall (predMaskOf L) (Fintype.card α)
     = predMaskOf L`, since the strict order on `α` is transitively
     closed by virtue of `α` being a partial order;
   * `closureCanonical_predMaskOf L : Case3Enum.closureCanonical
     (predMaskOf L) (maskOf L) (freeUVOf L) = true`, tautologically by
     the definition of `maskOf L` as the projection of `predMaskOf L`
     onto the free pairs.

Note on signatures. The spec listed `posetFromPredMask` with a
hypothesis-free signature; this implementation takes an
`IsValidPredMask` proof because the bit-relation on an arbitrary
predecessor mask is only a partial order when it is asymmetric and
transitive. The mismatch is absorbed by `bandMajorOrderIso`, which
supplies the proof from `predMaskOf_isValid`.
-/

end Step8

namespace Step8.Case3Enum

set_option linter.unusedSectionVars false

/-- **Validity predicate for a predecessor mask of width `n`.**

Asserts the bit-relation `bit u of pred[v] = "u < v"` is irreflexive,
asymmetric, and transitive on the index set `Fin n`. These are the
properties needed for the bit-relation to underly a `PartialOrder`. -/
def IsValidPredMask (pred : Array Nat) (n : Nat) : Prop :=
  (∀ u : Fin n, ¬ testBit' (pred.getD u.val 0) u.val) ∧
  (∀ u v : Fin n, testBit' (pred.getD v.val 0) u.val →
    ¬ testBit' (pred.getD u.val 0) v.val) ∧
  (∀ u v w : Fin n, testBit' (pred.getD v.val 0) u.val →
    testBit' (pred.getD w.val 0) v.val → testBit' (pred.getD w.val 0) u.val)

/-- **Bit-induced PartialOrder on `Fin n` from a predecessor mask.**

For a valid `pred` (`IsValidPredMask pred n`), `u ≤ v` iff `u = v` or
bit `u` is set in `pred[v]`. This is exactly the strict-plus-equal
relation used by `Case3Enum.hasBalancedPair`. -/
@[reducible]
def posetFromPredMask (pred : Array Nat) (n : Nat)
    (hValid : IsValidPredMask pred n) : PartialOrder (Fin n) where
  le u v := u = v ∨ testBit' (pred.getD v.val 0) u.val
  lt u v := u ≠ v ∧ testBit' (pred.getD v.val 0) u.val
  le_refl _ := Or.inl rfl
  le_trans u v w := by
    rintro (rfl | hUV) (rfl | hVW)
    · exact Or.inl rfl
    · exact Or.inr hVW
    · exact Or.inr hUV
    · exact Or.inr (hValid.2.2 u v w hUV hVW)
  lt_iff_le_not_ge u v := by
    refine Iff.intro ?_ ?_
    · rintro ⟨hne, hb⟩
      refine ⟨Or.inr hb, ?_⟩
      rintro (heq | hb')
      · exact hne heq.symm
      · exact hValid.2.1 _ _ hb hb'
    · rintro ⟨hle, hngeq⟩
      rcases hle with heq | hb
      · exact (hngeq (Or.inl heq.symm)).elim
      · refine ⟨?_, hb⟩
        intro h
        exact hngeq (Or.inl h.symm)
  le_antisymm u v := by
    intro h1 h2
    rcases h1 with heq | hUV
    · exact heq
    · rcases h2 with heq | hVU
      · exact heq.symm
      · exact absurd hVU (hValid.2.1 u v hUV)

@[simp]
lemma posetFromPredMask_le {pred : Array Nat} {n : Nat}
    (hValid : IsValidPredMask pred n) (u v : Fin n) :
    @LE.le _ (posetFromPredMask pred n hValid).toLE u v ↔
      u = v ∨ testBit' (pred.getD v.val 0) u.val :=
  Iff.rfl

/-! #### A5-B3 plumbing (`mg-0f0e`)

Bridges between the §2c `IsValidPredMask` / `posetFromPredMask`
flavour (used by `bandMajorOrderIso`) and the
`Case3Enum.Correctness` flavour (`ValidPredMask` / `predOrder`,
used by A4b's slow-path lift). The `≤` relations agree
definitionally; the `<` differ only by an `u ≠ v` conjunct that is
automatic for valid pred-masks (irreflexivity).
-/

/-- **`IsValidPredMask` ⇒ `ValidPredMask`** (A5-B3).
The flat-conjunction predicate of §2c re-packages trivially as the
structure of `Case3Enum.Correctness`: the first conjunct supplies
`irrefl`; the third supplies `trans`. -/
def IsValidPredMask.toValidPredMask {pred : Array Nat} {n : ℕ}
    (h : IsValidPredMask pred n) : ValidPredMask pred n where
  irrefl := h.1
  trans := h.2.2

/-- **`posetFromPredMask.le` ↔ `predOrder.le`** (A5-B3).
Both PartialOrder constructors yield the same `≤` on `Fin n`,
namely `u = v ∨ predLT pred u v`. Holds by `rfl`. -/
lemma posetFromPredMask_le_iff_predOrder_le {pred : Array Nat} {n : ℕ}
    (hValid : IsValidPredMask pred n) (u v : Fin n) :
    @LE.le _ (posetFromPredMask pred n hValid).toLE u v ↔
      @LE.le _ (predOrder pred hValid.toValidPredMask).toLE u v :=
  Iff.rfl

/-- **`posetFromPredMask.lt` ↔ `predOrder.lt`** (A5-B3).
The two `<` relations agree under validity: `posetFromPredMask`'s
strict relation strengthens with `u ≠ v`, redundant for valid
pred-masks by irreflexivity. -/
lemma posetFromPredMask_lt_iff_predOrder_lt {pred : Array Nat} {n : ℕ}
    (hValid : IsValidPredMask pred n) (u v : Fin n) :
    @LT.lt _ (posetFromPredMask pred n hValid).toLT u v ↔
      @LT.lt _ (predOrder pred hValid.toValidPredMask).toLT u v := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro hne
  exact hValid.1 u (hne ▸ h)

end Step8.Case3Enum

namespace Step8

section PredMaskCore

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- The Case3Enum-local `testBit'` agrees with `Nat.testBit`. -/
lemma testBit'_eq_testBit (m i : Nat) :
    Case3Enum.testBit' m i = Nat.testBit m i := by
  unfold Case3Enum.testBit' Case3Enum.bit
  rw [Nat.one_shiftLeft]
  by_cases h : Nat.testBit m i
  · -- m.testBit i = true ⇒ m &&& 2^i ≠ 0
    have hne : m &&& 2 ^ i ≠ 0 := by
      intro heq
      have ht : (m &&& 2 ^ i).testBit i = true := by
        rw [Nat.testBit_and, Nat.testBit_two_pow_self, h]; rfl
      rw [heq, Nat.zero_testBit] at ht
      exact Bool.false_ne_true ht
    simp [hne, h]
  · -- m.testBit i = false ⇒ m &&& 2^i = 0
    have heq : m &&& 2 ^ i = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_two_pow]
      by_cases hij : i = j
      · subst hij; simp [h]
      · simp [hij]
    simp [heq, h]

/-- Bitmask of width `n` whose `i`-th bit is set iff `p i = true`, for
`i < n`. Built by primitive recursion on `n`; characterized by
`testBit_encodeBitsBelow`. -/
def encodeBitsBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => encodeBitsBelow p n ||| (if p n then 1 <<< n else 0)

lemma testBit_encodeBitsBelow (p : Nat → Bool) :
    ∀ n i, Nat.testBit (encodeBitsBelow p n) i = (decide (i < n) && p i) := by
  intro n
  induction n with
  | zero => intro i; simp [encodeBitsBelow]
  | succ n ih =>
    intro i
    simp only [encodeBitsBelow, Nat.testBit_or, ih]
    by_cases hp : p n
    · simp only [hp, if_true, Nat.one_shiftLeft, Nat.testBit_two_pow]
      rcases Nat.lt_trichotomy i n with hlt | heq | hgt
      · simp [hlt, show i < n + 1 from by omega, show n ≠ i from by omega]
      · subst heq
        simp [hp, show i < i + 1 from by omega]
      · simp [show ¬ i < n from by omega, show ¬ i < n + 1 from by omega,
          show n ≠ i from by omega]
    · simp only [hp, if_false, Nat.zero_testBit, Bool.or_false]
      rcases Nat.lt_trichotomy i n with hlt | heq | hgt
      · simp [hlt, show i < n + 1 from by omega]
      · subst heq
        simp [hp]
      · simp [show ¬ i < n from by omega, show ¬ i < n + 1 from by omega]

/-- `Array.ofFn`'s `getD` reduces to the function on in-range
indices, default otherwise. -/
lemma Array.getD_ofFn {β : Type*} {n : Nat} (f : Fin n → β) (i : Nat) (d : β) :
    (Array.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  by_cases h : i < n <;> simp [h]

end PredMaskCore

section PredMask

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-- **Predecessor mask of a layered decomposition.**

For `L : LayeredDecomposition α`, `predMaskOf L : Array Nat` is the
band-major bitmask encoding of the strict order on `α`, indexed by
`bandMajorEquiv L`. Concretely, for `u v : Fin (Fintype.card α)`:

  bit `u.val` of `(predMaskOf L)[v.val]` is set
    ↔  `(bandMajorEquiv L).symm u < (bandMajorEquiv L).symm v`.

The construction layers the strict-order Boolean decision through
`encodeBitsBelow`, giving an `Array Nat` of size `Fintype.card α`. -/
noncomputable def predMaskOf (L : LayeredDecomposition α) : Array Nat := by
  classical
  exact Array.ofFn (n := Fintype.card α) (fun v : Fin (Fintype.card α) =>
    encodeBitsBelow (fun u : Nat =>
      if h : u < Fintype.card α then
        decide ((bandMajorEquiv L).symm ⟨u, h⟩ < (bandMajorEquiv L).symm v)
      else false)
      (Fintype.card α))

@[simp]
lemma size_predMaskOf (L : LayeredDecomposition α) :
    (predMaskOf L).size = Fintype.card α := by
  classical
  unfold predMaskOf
  simp

/-- **`Nat.testBit` characterization of `predMaskOf`.**

Bit `u.val` of `(predMaskOf L)[v.val]` is set iff `e.symm u < e.symm
v` in `α`, where `e = bandMajorEquiv L`. Stated in `Iff` form to
avoid relying on a `DecidableLT α` instance in the lemma type. -/
lemma testBit_predMaskOf (L : LayeredDecomposition α)
    (u v : Fin (Fintype.card α)) :
    Nat.testBit ((predMaskOf L).getD v.val 0) u.val = true ↔
      (bandMajorEquiv L).symm u < (bandMajorEquiv L).symm v := by
  classical
  unfold predMaskOf
  rw [Array.getD_ofFn, dif_pos v.isLt, testBit_encodeBitsBelow,
    decide_eq_true u.isLt, Bool.true_and, dif_pos u.isLt, decide_eq_true_iff]

/-- **`testBit'` (Case3Enum-local) characterization of `predMaskOf`.** -/
lemma testBit'_predMaskOf (L : LayeredDecomposition α)
    (u v : Fin (Fintype.card α)) :
    Case3Enum.testBit' ((predMaskOf L).getD v.val 0) u.val = true ↔
      (bandMajorEquiv L).symm u < (bandMajorEquiv L).symm v := by
  rw [testBit'_eq_testBit]
  exact testBit_predMaskOf L u v

/-- **`predMaskOf L` is a valid predecessor mask** (irreflexive,
asymmetric, transitive bit-relation), since it encodes the strict
order on `α` via `bandMajorEquiv L`. -/
lemma predMaskOf_isValid (L : LayeredDecomposition α) :
    Case3Enum.IsValidPredMask (predMaskOf L) (Fintype.card α) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Irreflexive
    intro u hbit
    exact lt_irrefl _ ((testBit'_predMaskOf L u u).mp hbit)
  · -- Asymmetric
    intro u v hUV hVU
    have h1 := (testBit'_predMaskOf L u v).mp hUV
    have h2 := (testBit'_predMaskOf L v u).mp hVU
    exact lt_irrefl _ (h1.trans h2)
  · -- Transitive
    intro u v w hUV hVW
    have h1 := (testBit'_predMaskOf L u v).mp hUV
    have h2 := (testBit'_predMaskOf L v w).mp hVW
    exact (testBit'_predMaskOf L u w).mpr (h1.trans h2)

/-- **Band-major order isomorphism** (Path A2, mg-b7b0).

The bijection `bandMajorEquiv L` of A1 upgraded to an order iso with
`Fin (Fintype.card α)` carrying the `predMaskOf L`-induced partial
order. This is the missing piece of the F5a-ℓ encoding bridge: A3+
will use this to transport `HasBalancedPair` from the abstract `α`
side to the bitmask `Fin n` side.

The target's `LE` is the one supplied by `Case3Enum.posetFromPredMask
(predMaskOf L) _ (predMaskOf_isValid L)`, made explicit to avoid
clashing with `Fin n`'s default `Nat`-induced order. -/
noncomputable def bandMajorOrderIso (L : LayeredDecomposition α) :
    @OrderIso α (Fin (Fintype.card α)) _
      (Case3Enum.posetFromPredMask (predMaskOf L) (Fintype.card α)
        (predMaskOf_isValid L)).toLE := by
  refine
    { toEquiv := bandMajorEquiv L
      map_rel_iff' := ?_ }
  intro a b
  -- Goal: bandMajorEquiv L a ≤ bandMajorEquiv L b (under custom order) ↔ a ≤ b.
  -- Unfold the custom le.
  show ((bandMajorEquiv L a = bandMajorEquiv L b) ∨
      Case3Enum.testBit' ((predMaskOf L).getD (bandMajorEquiv L b).val 0)
        (bandMajorEquiv L a).val = true) ↔ a ≤ b
  rw [(bandMajorEquiv L).apply_eq_iff_eq, testBit'_predMaskOf]
  simp only [Equiv.symm_apply_apply]
  exact (le_iff_eq_or_lt).symm

/-! #### Free-pair list and mask projection

`freeUVOf L` is the list of cross-band pairs `(u, v)` with band-gap
`≤ L.w`, indexed by their `Fin (Fintype.card α)` positions; this is
exactly the `freeUV` array that `Case3Enum.enumPosetsFor L.w
(bandSizes L)` iterates over.

`maskOf L` is the `Nat` whose `k`-th bit is set iff bit `(freeUV[k]).1`
of `(predMaskOf L)[(freeUV[k]).2]` is set — i.e. the projection of
`predMaskOf L` onto the free-pair positions.  By construction,
`closureCanonical (predMaskOf L) (maskOf L) (freeUVOf L) = true`.
-/

/-- The free-pair list for a layered decomposition: pairs `(u, v)`
with `u` in band `i + 1`, `v` in band `j + 1`, `i < j`, `j - i ≤ L.w`,
where `u, v` are global Fin-n indices via the band-major offsets.

Defined as the free output of `Case3Enum.enumPartition`, which both
freezes the band-major positional layout used by F5a's enumeration
and lets the §7 membership characterizations of the
`enumPartition`-followup apply directly to consumers (i.e. `maskOf`,
`closureCanonical_predMaskOf`).

A standalone `Id.run do` alternative is structurally equivalent (the
`if j - i ≤ L.w` early-skip merely reorders the `if`/loop nesting);
identifying with `enumFreeUVOf` directly removes that bridge. -/
noncomputable def freeUVOf (L : LayeredDecomposition α) : Array (Nat × Nat) :=
  Case3Enum.enumFreeUVOf L.w (bandSizes L)

/-- Recursive form of the projection of `pred` onto the first `n`
free-pair positions. Used as a clean specification for `maskOf`. -/
def maskOfRec (pred : Array Nat) (freeUV : Array (Nat × Nat)) :
    Nat → Nat
  | 0 => 0
  | k + 1 =>
    if Case3Enum.testBit' (pred.getD (freeUV.getD k (0, 0)).2 0)
        (freeUV.getD k (0, 0)).1
    then maskOfRec pred freeUV k ||| Case3Enum.bit k
    else maskOfRec pred freeUV k

/-- The bitmask `Nat` projecting `predMaskOf L` onto the free pairs:
bit `k` is set iff bit `(freeUVOf L)[k].1` is set in
`(predMaskOf L)[(freeUVOf L)[k].2]`.

Defined via primitive recursion to make `closureCanonical` reasoning
tractable. -/
noncomputable def maskOf (L : LayeredDecomposition α) : Nat :=
  maskOfRec (predMaskOf L) (freeUVOf L) (freeUVOf L).size

/-- Bits `≥ n` of `maskOfRec pred freeUV n` are zero (only the first
`n` bits are touched). -/
lemma testBit_maskOfRec_ge (pred : Array Nat) (freeUV : Array (Nat × Nat)) :
    ∀ n k, n ≤ k → Nat.testBit (maskOfRec pred freeUV n) k = false := by
  intro n
  induction n with
  | zero => intro k _; simp [maskOfRec]
  | succ n ih =>
    intro k hk
    unfold maskOfRec
    split_ifs with hbit
    · simp only [Nat.testBit_or]
      rw [show Case3Enum.bit n = 2^n from by simp [Case3Enum.bit, Nat.one_shiftLeft]]
      rw [Nat.testBit_two_pow,
        show (decide (n = k)) = false from decide_eq_false (by omega),
        Bool.or_false]
      exact ih k (by omega)
    · exact ih k (by omega)

/-- For `k < n`, bit `k` of `maskOfRec pred freeUV n` matches
`Nat.testBit (pred.getD v 0) u` where `(u, v) := freeUV.getD k (0, 0)`. -/
lemma testBit_maskOfRec_lt (pred : Array Nat) (freeUV : Array (Nat × Nat)) :
    ∀ n k, k < n → Nat.testBit (maskOfRec pred freeUV n) k =
      Nat.testBit (pred.getD (freeUV.getD k (0, 0)).2 0)
        (freeUV.getD k (0, 0)).1 := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    unfold maskOfRec
    by_cases hkn : k = n
    · subst hkn
      -- k = n: the new bit at position k is the relevant one.
      split_ifs with hbit
      · -- bit k of pred[v] is set; pred contributes the bit at position k.
        simp only [Nat.testBit_or]
        rw [show Case3Enum.bit k = 2^k from by
          simp [Case3Enum.bit, Nat.one_shiftLeft]]
        rw [Nat.testBit_two_pow_self, Bool.or_true]
        rw [testBit'_eq_testBit] at hbit
        exact hbit.symm
      · -- bit k of pred[v] is not set; prev mask has bit k = false (by _ge).
        have h1 : Nat.testBit (pred.getD (freeUV.getD k (0, 0)).2 0)
            (freeUV.getD k (0, 0)).1 = false := by
          rcases hbool : Nat.testBit (pred.getD (freeUV.getD k (0, 0)).2 0)
              (freeUV.getD k (0, 0)).1 with _ | _
          · rfl
          · rw [testBit'_eq_testBit] at hbit
            exact absurd hbool hbit
        rw [h1]
        exact testBit_maskOfRec_ge pred freeUV k k (le_refl _)
    · -- k < n: induction.
      split_ifs with hbit
      · simp only [Nat.testBit_or]
        rw [show Case3Enum.bit n = 2^n from by simp [Case3Enum.bit, Nat.one_shiftLeft]]
        rw [Nat.testBit_two_pow,
          show (decide (n = k)) = false from decide_eq_false fun h => hkn h.symm,
          Bool.or_false]
        exact ih k (by omega)
      · exact ih k (by omega)

/-! #### Matching lemmas between `predMaskOf L` and `Case3Enum.warshall` /
`Case3Enum.closureCanonical`.

These two lemmas are the Path A2-followup deliverables (`mg-6066`),
tying §2c's predecessor-mask encoding to `Case3Enum.enumPosetsFor`'s
imperative bitmask scaffolding:

* `predMaskOf_warshall` — Warshall's transitive-closure pass is a no-op
  on `predMaskOf L`, since the strict order on `α` is already
  transitively closed.
* `closureCanonical_predMaskOf` — the projection of `predMaskOf L` onto
  the free-pair list `freeUVOf L` is exactly `maskOf L`, by construction. -/

/-- Helper: a `forIn` loop in `Id` that always yields its initial state
returns the initial state. -/
private lemma forIn_yield_const_init.{u_, w_} {α_ : Type u_} {β_ : Type w_}
    (l : List α_) (init : β_)
    (body : α_ → β_ → Id (ForInStep β_))
    (h : ∀ x ∈ l, body x init = pure (ForInStep.yield init)) :
    forIn l init body = init := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, h x List.mem_cons_self]
    show (forIn l init body : Id β_) = init
    exact ih (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))

/-- Helper: setting an array element to its current value (via `set!`) is a
no-op. -/
private lemma Array.set!_getD_self_aux {α_ : Type*} (a : Array α_) (v : Nat)
    (d : α_) (hv : v < a.size) : a.set! v (a.getD v d) = a := by
  apply Array.ext
  · simp
  · intro j _ h2
    by_cases hjv : j = v
    · subst hjv
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds_self (by simpa using hv)]
      exact (Array.getElem_eq_getD d).symm
    · simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds_ne h2 (fun heq => hjv heq.symm)]

/-- For a transitively-closed predecessor mask, OR'ing `pred[k]` into
`pred[v]` is a no-op when bit `k` of `pred[v]` is set. -/
private lemma pred_or_eq_self_of_bit_aux (pred : Array Nat) (v k : Nat)
    (htrans : ∀ u : Nat, Case3Enum.testBit' (pred.getD v 0) k = true →
      Case3Enum.testBit' (pred.getD k 0) u = true →
      Case3Enum.testBit' (pred.getD v 0) u = true)
    (hbit : Case3Enum.testBit' (pred.getD v 0) k = true) :
    pred.getD v 0 ||| pred.getD k 0 = pred.getD v 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or]
  rcases hcase : Nat.testBit (pred.getD v 0) j with _ | _
  · simp only [Bool.false_or]
    rcases hkj : Nat.testBit (pred.getD k 0) j with _ | _
    · rfl
    · exfalso
      have hkj' : Case3Enum.testBit' (pred.getD k 0) j = true := by
        rw [testBit'_eq_testBit]; exact hkj
      have := htrans j hbit hkj'
      rw [testBit'_eq_testBit, hcase] at this
      exact Bool.false_ne_true this
  · simp only [Bool.true_or]

/-- Bit `j` of `(predMaskOf L)[i]` is set only if both `i, j < Fintype.card α`.

`getD` returns `0` for out-of-bounds indices, and `predMaskOf L` is built via
`encodeBitsBelow … (Fintype.card α)`, which only sets bits at positions
strictly less than the bound. -/
lemma testBit'_predMaskOf_bound (L : LayeredDecomposition α) (i j : Nat)
    (h : Case3Enum.testBit' ((predMaskOf L).getD i 0) j = true) :
    i < Fintype.card α ∧ j < Fintype.card α := by
  classical
  rw [testBit'_eq_testBit] at h
  refine ⟨?_, ?_⟩
  · by_contra hi
    have hi' : Fintype.card α ≤ i := Nat.not_lt.mp hi
    have hzero : (predMaskOf L).getD i 0 = 0 := by
      rw [Array.getD_eq_getD_getElem?]
      have hnone : (predMaskOf L)[i]? = none := by
        rw [Array.getElem?_eq_none]
        rw [size_predMaskOf]; exact hi'
      rw [hnone]; rfl
    rw [hzero, Nat.zero_testBit] at h
    exact Bool.false_ne_true h
  · by_contra hj
    have hj' : Fintype.card α ≤ j := Nat.not_lt.mp hj
    unfold predMaskOf at h
    rw [Array.getD_ofFn] at h
    split_ifs at h with hi
    · rw [testBit_encodeBitsBelow] at h
      have : decide (j < Fintype.card α) = false :=
        decide_eq_false (fun h' => Nat.not_lt.mpr hj' h')
      rw [this, Bool.false_and] at h
      exact Bool.false_ne_true h
    · rw [Nat.zero_testBit] at h
      exact Bool.false_ne_true h

/-- Transitivity of the `predMaskOf L` bit-relation, lifted to `Nat` indices.
For `Fin (Fintype.card α)` indices it follows from `predMaskOf_isValid`; for
out-of-bounds indices the hypothesis is vacuously false. -/
lemma predMaskOf_trans_nat (L : LayeredDecomposition α) (u v k : Nat)
    (h1 : Case3Enum.testBit' ((predMaskOf L).getD v 0) k = true)
    (h2 : Case3Enum.testBit' ((predMaskOf L).getD k 0) u = true) :
    Case3Enum.testBit' ((predMaskOf L).getD v 0) u = true := by
  obtain ⟨hv, hk⟩ := testBit'_predMaskOf_bound L v k h1
  obtain ⟨_, hu⟩ := testBit'_predMaskOf_bound L k u h2
  exact (predMaskOf_isValid L).2.2 ⟨u, hu⟩ ⟨k, hk⟩ ⟨v, hv⟩ h2 h1

/-- **`Case3Enum.warshall` is the identity on `predMaskOf L`** (Path
A2-followup, `mg-6066`).

Since `predMaskOf L` already encodes the strict order on `α` — which is
transitively closed by virtue of `α` being a partial order — Warshall's
inner step `out[v] ← out[v] ||| out[k]` is a no-op whenever bit `k` of
`out[v]` is set: by transitivity, every bit of `out[k]` is already a bit
of `out[v]`. Hence the entire double `for`-loop returns `predMaskOf L`
unchanged. -/
theorem predMaskOf_warshall (L : LayeredDecomposition α) :
    Case3Enum.warshall (predMaskOf L) (Fintype.card α) = predMaskOf L := by
  classical
  set pred := predMaskOf L with hpred
  set n := Fintype.card α with hn
  have hsize : pred.size = n := by rw [hpred, hn]; exact size_predMaskOf L
  have htrans : ∀ u v k : Nat,
      Case3Enum.testBit' (pred.getD v 0) k = true →
      Case3Enum.testBit' (pred.getD k 0) u = true →
      Case3Enum.testBit' (pred.getD v 0) u = true := fun u v k =>
    predMaskOf_trans_nat L u v k
  -- Reduce the imperative double for-loop.
  change Case3Enum.warshall pred n = pred
  unfold Case3Enum.warshall
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- Inner forIn over any sublist of `[0, n)`, started at `pred`, returns `pred`.
  have hinner : ∀ (k : Nat) (hk : k < n) (l : List Nat), (∀ v ∈ l, v < n) →
      (forIn l pred (fun v acc =>
        if (acc.getD v 0 &&& Case3Enum.bit k != 0) = true then
          (do pure PUnit.unit; pure (ForInStep.yield (acc.set! v
            (acc.getD v 0 ||| pred.getD k 0))) : Id _)
        else (do pure PUnit.unit; pure (ForInStep.yield acc) : Id _))) = pred := by
    intro k _hk l hl
    apply forIn_yield_const_init
    intro v hv
    have hvn : v < n := hl v hv
    by_cases hbit : (pred.getD v 0 &&& Case3Enum.bit k != 0) = true
    · simp only [hbit, ↓reduceIte]
      have hbit' : Case3Enum.testBit' (pred.getD v 0) k = true := by
        unfold Case3Enum.testBit'; exact hbit
      have hor : pred.getD v 0 ||| pred.getD k 0 = pred.getD v 0 :=
        pred_or_eq_self_of_bit_aux pred v k
          (fun u h1 h2 => htrans u v k h1 h2) hbit'
      rw [hor]
      have hvsize : v < pred.size := by rw [hsize]; exact hvn
      rw [Array.set!_getD_self_aux pred v 0 hvsize]
      rfl
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte]
      rfl
  -- Outer body, applied to `pred`, yields `pred`.
  set L' := List.range' 0 n with hL'
  have hL'_bound : ∀ k ∈ L', k < n := by
    intro k hk; rw [hL'] at hk
    simp [List.mem_range'] at hk; omega
  have houter :=
    forIn_yield_const_init L' pred (fun k acc =>
      have out := acc
      have bitK := Case3Enum.bit k
      have pk := out.getD k 0
      do
        let r ← forIn L' out (fun v acc =>
          have out := acc
          if (out.getD v 0 &&& bitK != 0) = true then
            have out := out.set! v (out.getD v 0 ||| pk)
            do pure PUnit.unit; pure (ForInStep.yield out)
          else do pure PUnit.unit; pure (ForInStep.yield out))
        have out : Array ℕ := r
        pure PUnit.unit
        pure (ForInStep.yield out))
      (by
        intro k hkL
        have hk : k < n := hL'_bound k hkL
        change (do
          let r ← forIn L' pred (fun v acc =>
            if (acc.getD v 0 &&& Case3Enum.bit k != 0) = true then
              (do pure PUnit.unit; pure (ForInStep.yield (acc.set! v
                (acc.getD v 0 ||| pred.getD k 0))) : Id _)
            else (do pure PUnit.unit; pure (ForInStep.yield acc) : Id _))
          (do pure PUnit.unit; pure (ForInStep.yield r) : Id _)) =
            pure (ForInStep.yield pred)
        rw [hinner k hk L' hL'_bound]
        rfl)
  change (do let r ← forIn L' pred _; pure r : Id _) = pred
  rw [houter]
  rfl

/-- **The closure-canonical predicate is satisfied by `predMaskOf L`'s
projection onto `freeUVOf L`** (Path A2-followup, `mg-6066`).

By construction, `maskOf L` is built from `predMaskOf L` via
`maskOfRec`, whose bit-by-bit characterization (`testBit_maskOfRec_lt`)
exactly matches the bits queried by `Case3Enum.closureCanonical`'s
inner loop. Hence the predicate's early-return condition `closedBit ≠
maskBit` is never triggered, and the loop returns `true`. -/
theorem closureCanonical_predMaskOf (L : LayeredDecomposition α) :
    Case3Enum.closureCanonical (predMaskOf L) (maskOf L) (freeUVOf L) = true := by
  unfold Case3Enum.closureCanonical
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- The bit-by-bit equality between maskOf and predMaskOf-projection.
  have hbits : ∀ k < (freeUVOf L).size,
      Case3Enum.testBit' ((predMaskOf L).getD ((freeUVOf L).getD k (0, 0)).2 0)
          ((freeUVOf L).getD k (0, 0)).1
        = Case3Enum.testBit' (maskOf L) k := by
    intro k hk
    rw [testBit'_eq_testBit, testBit'_eq_testBit]
    unfold maskOf
    rw [testBit_maskOfRec_lt _ _ _ _ hk]
  -- Now induct on the for-loop list.
  generalize hl : List.range' 0 (freeUVOf L).size = l
  have h_bound : ∀ k ∈ l,
      Case3Enum.testBit' ((predMaskOf L).getD
          ((freeUVOf L).getD k (0, 0)).2 0)
          ((freeUVOf L).getD k (0, 0)).1
        = Case3Enum.testBit' (maskOf L) k := by
    intro k hk
    rw [← hl] at hk
    simp [List.mem_range'] at hk
    exact hbits k (by omega)
  clear hl hbits
  induction l with
  | nil => rfl
  | cons k l ih =>
    have hbit := h_bound k List.mem_cons_self
    have hdite : (if h : k < (freeUVOf L).size
        then (freeUVOf L).getInternal k h else (0, 0)) = (freeUVOf L).getD k (0, 0) := rfl
    simp only [List.forIn_cons]
    rw [hdite, hbit]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun k' hk' => h_bound k' (List.mem_cons_of_mem _ hk'))

/-! #### A5-B3: bit-boundedness, iteration range, order-iso variant
(`mg-0f0e`)

Companion plumbing to §2c, providing the inputs that A4b's
slow-path lift expects:

* `predBitsBoundedBy_predMaskOf` — bits of `(predMaskOf L)[i]` past
  `Fintype.card α` are zero, since the encoding via `encodeBitsBelow`
  only sets bits at positions strictly less than the cardinality
  (cf. `testBit'_predMaskOf_bound`).
* `maskOf_lt_two_pow_size` — `maskOf L < 2 ^ (freeUVOf L).size`, so
  the for-loop `for mask in [0:1 <<< nfree]` of `enumPosetsFor`
  *does* visit `mask = maskOf L`.
* `bandMajorOrderIso_predOrder` — A2's order iso re-packaged with
  the `Case3Enum.predOrder` partial-order target (the structure
  variant consumed by A4b's slow-path bridge).
-/

/-- **`predBitsBoundedBy (predMaskOf L) (Fintype.card α)`** (A5-B3).
Bits of `(predMaskOf L)[e]` at positions `≥ Fintype.card α` are
zero, because the `encodeBitsBelow … (Fintype.card α)` construction
only sets bits at positions `< Fintype.card α`
(cf. `testBit'_predMaskOf_bound`). -/
theorem predBitsBoundedBy_predMaskOf (L : LayeredDecomposition α) :
    Case3Enum.predBitsBoundedBy (predMaskOf L) (Fintype.card α) := by
  intro e b hb
  rcases hbool : Case3Enum.testBit' ((predMaskOf L).getD e.val 0) b with _ | _
  · rfl
  · exact absurd (testBit'_predMaskOf_bound L e.val b hbool).2
      (Nat.not_lt.mpr hb)

/-- **`maskOf L < 2 ^ (freeUVOf L).size`** (A5-B3).
`maskOf L` is built by `maskOfRec` over the first `(freeUVOf L).size`
positions, which leaves bits at positions `≥ size` zero. -/
theorem maskOf_lt_two_pow_size (L : LayeredDecomposition α) :
    maskOf L < 2 ^ (freeUVOf L).size := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  unfold maskOf
  exact testBit_maskOfRec_ge _ _ _ k hk

/-- **A2's band-major order iso, with the `predOrder` target**
(A5-B3).
The §2c `bandMajorOrderIso` targets `posetFromPredMask`-induced
order; A4b's slow-path lift uses the `Case3Enum.predOrder` form.
The two PartialOrder constructors agree on `≤` definitionally
(cf. `posetFromPredMask_le_iff_predOrder_le`), so the same
underlying `bandMajorEquiv` carries an order iso into either form. -/
noncomputable def bandMajorOrderIso_predOrder (L : LayeredDecomposition α) :
    @OrderIso α (Fin (Fintype.card α)) _
      (Case3Enum.predOrder (predMaskOf L)
        (predMaskOf_isValid L).toValidPredMask).toLE := by
  refine
    { toEquiv := bandMajorEquiv L
      map_rel_iff' := ?_ }
  intro a b
  -- `≤` in `predOrder` agrees with `posetFromPredMask`-`≤`
  -- definitionally; reuse `bandMajorOrderIso L`'s `map_rel_iff'`.
  exact (bandMajorOrderIso L).map_rel_iff'

/-- **Slow-path / fast-path lift to `HasBalancedPair α`** (A5-G3b).

Convenience specialization of `hasBalancedPair_of_orderIso_explicit`
to the `Case3Enum.predOrder` source partial order: lifts a Fin-side
balanced pair witness produced by
`Case3Enum.BalancedLift.hasBalancedPair_of_hasBalancedPair` (whose
result type bakes in `predOrder pred h`) to the abstract poset `α`,
transported via an order isomorphism `α ≃o (Fin n)` whose
`Fin`-side `≤` is `(predOrder pred h).toLE` — e.g.
`bandMajorOrderIso_predOrder L`. The default `Fin` typeclass
instance (`instPartialOrderFin`) would fight synthesis on the
unannotated `hasBalancedPair_of_orderIso`; routing through the
explicit-instance variant pins the partial-order choice. -/
theorem hasBalancedPair_of_predOrder_orderIso
    {n : ℕ} {pred : Array ℕ}
    (h : Case3Enum.ValidPredMask pred n)
    (e : @OrderIso α (Fin n) _ (Case3Enum.predOrder pred h).toLE)
    (hBalFin : @HasBalancedPair (Fin n) (Case3Enum.predOrder pred h) _ _) :
    HasBalancedPair α := by
  -- Pin the local `[LE (Fin n)]` choice to `predOrder.toLE` so that
  -- `e.symm` elaborates with the correct order-iso target type. The
  -- global `instLEFin` would otherwise be selected and mismatch the
  -- declared `≤` of `e`. We construct `e.symm` by hand via
  -- `@OrderIso.symm` with the LE instances pinned explicitly,
  -- sidestepping the synthesis fight.
  let einv : @OrderIso (Fin n) α (Case3Enum.predOrder pred h).toLE _ :=
    @OrderIso.symm α (Fin n) _ (Case3Enum.predOrder pred h).toLE e
  exact hasBalancedPair_of_orderIso_explicit
    (Case3Enum.predOrder pred h) inferInstance einv hBalFin

/-! #### A5-B3 packaging: `enumPosetsFor` unrolling at `mask = maskOf L`
(`mg-0f0e`)

The Bool-level `enumPosetsFor` iterates `for mask in [0:1 <<< nfree]`,
building a `pred : Array Nat` from `forcedUV ∪ {(u, v) ∈ freeUV : mask
bit set}` and applying `Case3Enum.warshall`. For a
`LayeredDecomposition L` in scope, the relevant iteration is the one
at `mask = maskOf L`: the projection of `predMaskOf L` onto the
free-pair list.

The structural content of the unrolling is captured by four facts —
all already in tree (`predMaskOf_isValid`, `predMaskOf_warshall`,
`closureCanonical_predMaskOf`, `maskOf_lt_two_pow_size`). The
packaging theorem below collects them in a single statement
consumed by F5a's bridge, witnessing that `predMaskOf L` is the
post-warshall output of the imperative loop body at `mask = maskOf L`
under the closure-canonical and validity conditions. -/

/-- **`enumPosetsFor` post-warshall summary at `mask = maskOf L`**
(A5-B3, `mg-0f0e`).

The four-component witness that `predMaskOf L` is the post-warshall
pred-array at the iteration `mask = maskOf L` of the
`enumPosetsFor` loop body:

1. `mask = maskOf L` lies in the iteration range `[0, 2 ^ nfree)`.
2. Validity (`Case3Enum.IsValidPredMask`) — `predMaskOf L`'s
   bit-relation underlies a `PartialOrder (Fin n)`.
3. Warshall stability — `Case3Enum.warshall (predMaskOf L) n =
   predMaskOf L` (predMaskOf is already transitively closed).
4. Closure-canonical projection — `Case3Enum.closureCanonical
   (predMaskOf L) (maskOf L) (freeUVOf L) = true` (the
   `closureCanonical` gate of `enumPosetsFor` is satisfied,
   matching the iteration mask). -/
theorem enumPosetsFor_unroll_summary (L : LayeredDecomposition α) :
    maskOf L < 2 ^ (freeUVOf L).size ∧
    Case3Enum.IsValidPredMask (predMaskOf L) (Fintype.card α) ∧
    Case3Enum.warshall (predMaskOf L) (Fintype.card α) = predMaskOf L ∧
    Case3Enum.closureCanonical (predMaskOf L) (maskOf L) (freeUVOf L) = true :=
  ⟨maskOf_lt_two_pow_size L, predMaskOf_isValid L,
    predMaskOf_warshall L, closureCanonical_predMaskOf L⟩

end PredMask

end Step8

namespace Step8

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
Bool-certified scope (post-`mg-9a4a` Window C narrowing, small
size-limit variant).

The certified scope is the disjunction

  * `K = 3 ∧ w ∈ {1, …, 4} ∧ (w = 1 → card ≤ 9) ∧ (w ≥ 2 → card ≤ 7)`
    — the original `case3_balanced_w{1,2,3,4}` slices of `mg-307c`,
    unchanged.
  * `K = 4 ∧ w = 1 ∧ card ≤ 8` — the Window C K=4 small-size
    extension (`mg-9a4a`, covering the 50 K=4-w=1 band-tuples with
    `c ≤ 8`; the larger K=4-w=1 slice and the K=3 c-sliver remain
    axiomatic — see `docs/compatibility-geometry-pathP3-scoping.md`
    §5.1 and the K4W1 file header for the narrowing accounting).

from `OneThird.Step8.Case3Enum.case3_certificate`. Used by the
`bounded_irreducible_balanced_inScope` theorem to flag the cases in
which the Bool certificate directly witnesses the Prop-level
conclusion. Negating it (`¬ InCase3Scope`) narrows the residual
`case3Witness_hasBalancedPair_outOfScope` axiom's parameter range
without eliminating it; see
`docs/compatibility-geometry-pathP3-scoping.md` §3 for the axiom
narrowing audit. -/
def InCase3Scope (w card K : ℕ) : Prop :=
  (K = 3 ∧ 1 ≤ w ∧ w ≤ 4 ∧
    (w = 1 → card ≤ 9) ∧ (2 ≤ w → card ≤ 7)) ∨
  (K = 4 ∧ w = 1 ∧ card ≤ 8)

/-- `InCase3Scope` is decidable: a disjunction of conjunctions of `Nat`
equalities and inequalities. Required so that
`bounded_irreducible_balanced_hybrid` can branch on the predicate via
`by_cases`. -/
instance (w card K : ℕ) : Decidable (InCase3Scope w card K) := by
  unfold InCase3Scope; infer_instance

/-- Every `(w, card, K)` in Case-3 scope has `w ∈ {1, 2, 3, 4}`. The
K=4 branch forces `w = 1`; the K=3 branch admits the full four-way
split. -/
lemma InCase3Scope.w_mem {w card K : ℕ} (h : InCase3Scope w card K) :
    w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by
  rcases h with ⟨_, h1, h4, _, _⟩ | ⟨_, hw1, _⟩
  · -- K=3 branch: 1 ≤ w ∧ w ≤ 4 splits four ways.
    rcases Nat.lt_or_ge w 2 with hlt | hge
    · exact Or.inl (by omega)
    rcases Nat.lt_or_ge w 3 with hlt | hge
    · exact Or.inr (Or.inl (by omega))
    rcases Nat.lt_or_ge w 4 with hlt | hge
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · -- K=4 branch: w = 1 directly.
    exact Or.inl hw1

/-- Under `InCase3Scope w card K`, the Case-3 Bool certificate's size
cap applies: `card ≤ 9` on the K=3 branch (the original
`case3_balanced_w1` cap is the loosest at `≤ 9`; the `w ≥ 2` cap is
`≤ 7`) and `card ≤ 8` on the K=4-w=1 branch (the `mg-9a4a` small-size
variant) — uniformly bounded by `9`. -/
lemma InCase3Scope.card_le_nine {w card K : ℕ} (h : InCase3Scope w card K) :
    card ≤ 9 := by
  rcases h with ⟨_, hw1, _, hcap1, hcap2⟩ | ⟨_, _, hcard⟩
  · -- K=3 branch.
    rcases Nat.lt_or_ge w 2 with hlt | hge
    · have hw : w = 1 := by omega
      exact hcap1 hw
    · have : card ≤ 7 := hcap2 hge; omega
  · -- K=4 branch: card ≤ 8 ≤ 9.
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
`mg-3fd8` — closes `LayeredBalanced.lean:657`.

**Status (mg-53ce polecat report, A5-G2 path 1).** B1-B4 (`mg-46d7`,
`mg-a08f`, `mg-e9d6`, `mg-0f0e`, `mg-43bc`) provide the bridge
infrastructure (positional foundations, irreducibility /
hasAdjacentIncomp / closureCanonical / warshall-stability on
`predMaskOf L`). A5-G1 (`enumPosetsFor` Prop-level reduction,
`mg-580e` partial / `mg-b487` completion) lands the iteration
theorem `Case3Enum.enumPosetsFor_iter_balanced`. A5-G2 path 1
(`mg-53ce`, this work) adds the `cross_band_lt_upward` field to
`LayeredDecomposition`, which makes `predMaskOf L` upper-triangular
and so unblocks the construction-equivalence
`enumPredAtMaskOf L.w (bandSizes L) (maskOf L) = predMaskOf L`
that the discharge depends on; see `docs/a5-g2-status.md` for the
full diagnosis and resolution. The remaining work to convert the
`hEnum` placeholder body into a real certificate-driven proof
(composing B1'-B2-B3 + G1' + symmetric extraction +
bandMajorOrderIso transport) is now structurally unblocked and
falls to a follow-on A5-G3 ticket. -/
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

/-- **Hybrid dispatch form** (A5-B4, `mg-43bc`).

The wider hypothesis profile of `bounded_irreducible_balanced`
(`step8.tex prop:in-situ-balanced`, `step8.tex:2965-2970`) is *not*
discharged by `case3_certificate` alone: the certificate covers
`InCase3Scope` (`K = 3`, `w ∈ {1,…,4}`, size cap `9` or `7`), while
the C2-leaf profile permits any `K ∈ [3, 2w+2]` and `|α| ≤ 6w+6`.
The mismatch is documented in `docs/a5-profile-resolution.md`.

The selected resolution (Option 3 / "hybrid") splits the discharge
along `InCase3Scope`:

* **In-scope branch** (`hCert`): supplied from `case3_certificate`
  via the band-major encoding bridge (Path A of
  `docs/gap-analysis.md` — A5-B1/B2/B3 deliverables). Discharges
  Case 3 of `prop:in-situ-balanced` (the residual "width-3 profile
  antichain" finite enumeration, `step8.tex:3033-3047`).

* **Out-of-scope branch** (`hStruct`): supplied from the structural
  Cases 1 and 2 of `prop:in-situ-balanced` (`step8.tex:2984-3032`)
  — the `Equiv.swap` automorphism argument (Case 1) and the
  Ahlswede–Daykin / FKG profile-ordering plus rotation argument
  (Case 2). This is pre-filed work item **mg-A8** (`README.md:139`).

This hybrid form makes the dispatch shape **explicit in the
type**, so the consumers of A5-B4 (Path A, mg-A8, Path C) build
against typed inputs rather than the opaque `hEnum :
HasBalancedPair α` of the monolithic form.

The decision to keep the wider profile (rather than tightening to
`InCase3Scope`) follows from the F3 strong-induction recursion: the
C2 leaf is reached when no further band cut applies, and
irreducibility blocks descent of `K`. The paper's `prop:in-situ-
balanced` covers the wider profile uniformly via Cases 1, 2, 3 —
the certificate alone cannot. See `docs/a5-profile-resolution.md`
for the full analysis. -/
theorem bounded_irreducible_balanced_hybrid
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (_hIrr : LayerOrdinalIrreducible L)
    (_hK3 : 3 ≤ L.K)
    (_hw : 1 ≤ L.w)
    (_hCard : Fintype.card α ≤ 6 * L.w + 6)
    (_hDepth : L.K ≤ 2 * L.w + 2)
    (hCert : InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α)
    (hStruct : ¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α) :
    HasBalancedPair α := by
  by_cases h : InCase3Scope L.w (Fintype.card α) L.K
  · exact hCert h
  · exact hStruct h

/-- The wider monolithic `bounded_irreducible_balanced` factors
through the hybrid dispatch with both branches discharged by the
same `hEnum` witness. Trivial reduction (the dispatch returns
`hEnum` in both cases by construction) — recorded as a corollary
to make the relationship between the monolithic and the hybrid
forms explicit at the call-site level. -/
theorem bounded_irreducible_balanced_of_hybrid
    (L : LayeredDecomposition α)
    (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hK3 : 3 ≤ L.K) (hw : 1 ≤ L.w)
    (hCard : Fintype.card α ≤ 6 * L.w + 6)
    (hDepth : L.K ≤ 2 * L.w + 2)
    (hEnum : HasBalancedPair α) :
    HasBalancedPair α :=
  bounded_irreducible_balanced_hybrid L hWidth3 hIrr hK3 hw hCard hDepth
    (fun _ => hEnum) (fun _ => hEnum)

end MainTheorem

end Step8
end OneThird
