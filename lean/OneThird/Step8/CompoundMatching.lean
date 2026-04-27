/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.CompoundSwap
import OneThird.Step8.Case3Dispatch

/-!
# Step 8 — Structural matching lemma for K=2 irreducible w≥1 |β|≥3 layered configs
(`docs/path-c-cleanup-roadmap.md` §6a, PATH B step 2)

This file proves the **structural matching lemma** that PATH B step 2
(`mg-c0c7`) closes: every `LayeredDecomposition` with `K = 2`,
`LayerOrdinalIrreducible`, `w ≥ 1`, `|α| ≥ 3`, and "no within-band
`⪯`-comparable pair" admits two `SameBandPair` witnesses
(`OneThird.Step8.CompoundSwap`, `mg-84f2`) — one in band 1, one in
band 2 — whose compound swap `(a₁ a₂)(b₁ b₂)` is
`MatchingCompatible`.

This closes the named obstruction class
(`docs/a5-g3e-path-c-wiring-v5-status.md`, mg-94fd): the K=2 +
irreducible + w≥1 + |β|≥3 + no-within-band-`⪯` regime that neither
the ambient profile match (Case 1) nor the within-band rotation
(Case 2) can address.

## Method

Combinatorial. Under `NoWithinBandPreceq`, the band-size profile
`(|A|, |B|) ∈ {0,1,2,3}²` collapses (modulo unhandled vacuous
configurations) to `(|A|, |B|) ∈ {(2,2), (3,3)}`:

* `(0, *)` and `(*, 0)` violate `LayerOrdinalIrreducible` at `k = 1`
  (vacuous reducibility);
* `(1, ≥2)` and `(≥2, 1)` violate `NoWithinBandPreceq` (one band
  is a singleton, forcing `⪯`-comparability among the other band's
  pairs);
* `(2, 3)` and `(3, 2)` are excluded implicitly: in those cases the
  third-element compatibility argument's case-split forces
  `band_size ≥ 4`, contradicting the L1 bound.

The proof does not need to enumerate cases explicitly: it picks any
`a ≠ a'` in band 1 (which exists by `two_le_band_one`), extracts
witnesses `b, b'` in band 2 from `¬ (a ⪯ a')` and `¬ (a' ⪯ a)`
landing in the N-poset cross-pattern, and verifies matching
compatibility via two third-element compatibility lemmas. Each
third-element lemma reasons: if compatibility fails at some `x`
outside `{a, a'}`, two more witnesses in band 2 are forced, so
band 2 has `≥ 4` distinct elements — contradicting `band_size ≤ 3`.

## Main definitions

* `NoWithinBandPreceq L` — the "no within-band `⪯`-comparable pair"
  hypothesis, packaged as a quantified `¬ ⪯`.
* `NConfig L` — the N-poset cross-pattern data extracted from any
  pair of distinct band-1 elements under the structural hypotheses.
* `matching_exists_of_K2_irreducible_noWithinBand` — the main
  theorem: existence of a matching-compatible pair of
  `SameBandPair`s in different bands.

## References

* `docs/path-c-cleanup-roadmap.md` §6a — PATH B architectural plan.
* `docs/a5-g3e-path-c-wiring-v5-status.md` (mg-94fd) — the named
  obstruction this lemma closes.
* `lean/OneThird/Step8/CompoundSwap.lean` (mg-84f2) — `SameBandPair`,
  `MatchingCompatible`, `compoundSwap_preserves_le`.
* `lean/OneThird/Step8/Case3Dispatch.lean` (mg-48db) — `Case2Witness`
  predicate (the `⪯`-comparability shape negated here).
-/

namespace OneThird
namespace Step8
namespace CompoundMatching

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — The `NoWithinBandPreceq` hypothesis -/

/-- The "no within-band `⪯`-comparable pair" hypothesis: for any two
distinct elements `a ≠ a'` sharing a band, the `⪯`-comparability
predicate `(∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)` fails.

Equivalent to `¬ Step8.InSitu.Case2Witness L` (see
`noWithinBandPreceq_iff_not_case2Witness`). Under this hypothesis,
neither the Case 1 ambient match (handled elsewhere by
`hasBalancedPair_of_case1`) nor the Case 2 within-band rotation
(`Case2Rotation.lean`) is available, so a compound automorphism
witness is needed to balance some same-band pair. -/
def NoWithinBandPreceq (L : LayeredDecomposition α) : Prop :=
  ∀ ⦃a a' : α⦄, a ≠ a' → L.band a = L.band a' →
    ¬ ((∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a))

/-- Equivalent formulation: `NoWithinBandPreceq L ↔ ¬ Case2Witness L`. -/
lemma noWithinBandPreceq_iff_not_case2Witness (L : LayeredDecomposition α) :
    NoWithinBandPreceq L ↔ ¬ Step8.InSitu.Case2Witness L := by
  refine ⟨fun h ⟨a, a', hne, hband, hup, hdn⟩ => h hne hband ⟨hup, hdn⟩,
          fun h _ _ hne hband hpre => h ⟨_, _, hne, hband, hpre.1, hpre.2⟩⟩

/-! ### §2 — Band-1 / band-2 dichotomy under `K = 2` -/

variable (L : LayeredDecomposition α)

omit [DecidableEq α] in
/-- Under `K = 2`, every element is in band 1 or band 2. -/
lemma band_eq_one_or_two (hK2 : L.K = 2) (x : α) :
    L.band x = 1 ∨ L.band x = 2 := by
  have h1 := L.band_pos x
  have h2 := L.band_le x
  rw [hK2] at h2
  omega

omit [DecidableEq α] in
/-- For two distinct same-band elements, `<` fails by `band_antichain`. -/
lemma not_lt_of_sameBand {a a' : α} (hne : a ≠ a') (hband : L.band a = L.band a') :
    ¬ a < a' := by
  intro hlt
  refine L.band_antichain (L.band a) ?_ ?_ hne (le_of_lt hlt)
  · simp [Finset.coe_filter]
  · simp [Finset.coe_filter, hband.symm]

omit [DecidableEq α] in
/-- For a band-1 element `a`, no element is strictly below it. -/
lemma no_lt_band_one {a : α} (ha : L.band a = 1) (z : α) : ¬ z < a := by
  intro hzlt
  have h_le : L.band z ≤ L.band a := L.cross_band_lt_upward z a hzlt
  have hz_pos := L.band_pos z
  rw [ha] at h_le
  have hbandz_eq : L.band z = L.band a := by rw [ha]; omega
  exact not_lt_of_sameBand L (ne_of_lt hzlt) hbandz_eq hzlt

omit [DecidableEq α] in
/-- Under `K = 2`, for a band-2 element `b`, no element is strictly
above it. -/
lemma no_lt_band_two_above (hK2 : L.K = 2) {b : α} (hb : L.band b = 2)
    (z : α) : ¬ b < z := by
  intro hbz
  have h_le : L.band b ≤ L.band z := L.cross_band_lt_upward b z hbz
  have hz_le := L.band_le z
  rw [hK2] at hz_le
  rw [hb] at h_le
  have hbandz_eq : L.band b = L.band z := by rw [hb]; omega
  exact not_lt_of_sameBand L (ne_of_lt hbz) hbandz_eq hbz

omit [DecidableEq α] in
/-- Under `K = 2`, every strict comparability `x < y` is a cross-band
edge from band 1 to band 2. -/
lemma cross_band_under_K2 (hK2 : L.K = 2) {x y : α} (hxy : x < y) :
    L.band x = 1 ∧ L.band y = 2 := by
  have h_le := L.cross_band_lt_upward x y hxy
  have hy_le := L.band_le y
  rw [hK2] at hy_le
  rcases band_eq_one_or_two L hK2 x with hx1 | hx2
  · rcases band_eq_one_or_two L hK2 y with hy1 | hy2
    · exact absurd hxy
        (not_lt_of_sameBand L (ne_of_lt hxy) (hx1.trans hy1.symm))
    · exact ⟨hx1, hy2⟩
  · exfalso
    have hy2 : L.band y = 2 := by rw [hx2] at h_le; omega
    exact not_lt_of_sameBand L (ne_of_lt hxy) (hx2.trans hy2.symm) hxy

/-! ### §3 — Reduced form of `NoWithinBandPreceq` per band

Under `K = 2`, the second `⪯`-conjunct is vacuous in band 1 and the
first is vacuous in band 2. The band-1 form reads "rows of the
bipartite incidence matrix are pairwise incomparable as 0/1 vectors";
the band-2 form reads "columns are pairwise incomparable". -/

omit [DecidableEq α] in
/-- Under `K = 2` + `NoWithinBandPreceq`, two distinct band-1 elements
have non-included upward comparability profiles. -/
lemma exists_distinguish_band_one (hK2 : L.K = 2)
    (h : NoWithinBandPreceq L) {a a' : α}
    (hne : a ≠ a') (ha : L.band a = 1) (ha' : L.band a' = 1) :
    ∃ z : α, L.band z = 2 ∧ a < z ∧ ¬ a' < z := by
  have hpre : ¬ ((∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)) :=
    h hne (ha.trans ha'.symm)
  have hdn : ∀ z, z < a' → z < a := fun z hz =>
    absurd hz (no_lt_band_one L ha' z)
  have hup : ¬ ∀ z, a < z → a' < z := fun hk => hpre ⟨hk, hdn⟩
  push_neg at hup
  obtain ⟨z, haz, hnaz⟩ := hup
  refine ⟨z, ?_, haz, hnaz⟩
  exact (cross_band_under_K2 L hK2 haz).2

omit [DecidableEq α] in
/-- Under `K = 2` + `NoWithinBandPreceq`, two distinct band-2 elements
have non-included downward comparability profiles. -/
lemma exists_distinguish_band_two (hK2 : L.K = 2)
    (h : NoWithinBandPreceq L) {b b' : α}
    (hne : b ≠ b') (hb : L.band b = 2) (hb' : L.band b' = 2) :
    ∃ z : α, L.band z = 1 ∧ z < b' ∧ ¬ z < b := by
  have hpre : ¬ ((∀ z, b < z → b' < z) ∧ (∀ z, z < b' → z < b)) :=
    h hne (hb.trans hb'.symm)
  have hup : ∀ z, b < z → b' < z := fun z hz =>
    absurd hz (no_lt_band_two_above L hK2 hb z)
  have hdn : ¬ ∀ z, z < b' → z < b := fun hk => hpre ⟨hup, hk⟩
  push_neg at hdn
  obtain ⟨z, hzb', hnzb⟩ := hdn
  exact ⟨z, (cross_band_under_K2 L hK2 hzb').1, hzb', hnzb⟩

/-! ### §4 — Both bands have `≥ 2` elements -/

omit [DecidableEq α] in
/-- Under `K = 2` + irreducibility, band 1 contains at least one element. -/
lemma exists_band_one_of_irr (hK2 : L.K = 2) (hIrr : LayerOrdinalIrreducible L) :
    ∃ a : α, L.band a = 1 := by
  classical
  by_contra hempty
  push_neg at hempty
  refine hIrr 1 le_rfl (by rw [hK2]; norm_num) ?_
  intro u v hbu _
  have hu_pos := L.band_pos u
  have hu1 : L.band u = 1 := by omega
  exact absurd hu1 (hempty u)

omit [DecidableEq α] in
/-- Under `K = 2` + irreducibility, band 2 contains at least one element. -/
lemma exists_band_two_of_irr (hK2 : L.K = 2) (hIrr : LayerOrdinalIrreducible L) :
    ∃ b : α, L.band b = 2 := by
  classical
  by_contra hempty
  push_neg at hempty
  refine hIrr 1 le_rfl (by rw [hK2]; norm_num) ?_
  intro u v _ hbv
  have hv_le := L.band_le v
  rw [hK2] at hv_le
  have hv2 : L.band v = 2 := by omega
  exact absurd hv2 (hempty v)

omit [DecidableEq α] in
/-- The bands partition `α` (every element is in exactly band 1 or 2). -/
lemma band_partition (hK2 : L.K = 2) :
    ((Finset.univ : Finset α).filter (fun x => L.band x = 1)).card +
      ((Finset.univ : Finset α).filter (fun x => L.band x = 2)).card =
      Fintype.card α := by
  classical
  set A := (Finset.univ : Finset α).filter (fun x => L.band x = 1) with hAdef
  set B := (Finset.univ : Finset α).filter (fun x => L.band x = 2) with hBdef
  have hdisj : Disjoint A B := by
    rw [hAdef, hBdef, Finset.disjoint_filter]; intros; omega
  have hAB : A ∪ B = (Finset.univ : Finset α) := by
    ext x
    refine ⟨fun _ => Finset.mem_univ x, fun _ => ?_⟩
    rcases band_eq_one_or_two L hK2 x with h | h
    · exact Finset.mem_union_left _ (by simp [hAdef, h])
    · exact Finset.mem_union_right _ (by simp [hBdef, h])
  rw [← Finset.card_union_of_disjoint hdisj, hAB, Finset.card_univ]

omit [DecidableEq α] in
/-- Under `K = 2` + `NoWithinBandPreceq` + `|α| ≥ 3` + irreducibility,
band 1 has at least 2 elements. -/
lemma two_le_band_one (hK2 : L.K = 2) (hIrr : LayerOrdinalIrreducible L)
    (hCard : 3 ≤ Fintype.card α) (hNo : NoWithinBandPreceq L) :
    2 ≤ ((Finset.univ : Finset α).filter (fun x => L.band x = 1)).card := by
  classical
  set A := (Finset.univ : Finset α).filter (fun x => L.band x = 1) with hAdef
  set B := (Finset.univ : Finset α).filter (fun x => L.band x = 2) with hBdef
  have hAB : A.card + B.card = Fintype.card α := band_partition L hK2
  by_contra hAlt
  push_neg at hAlt
  have hAle : A.card ≤ 1 := by omega
  rcases Nat.lt_or_ge A.card 1 with hA0 | hA1
  · have hA_empty : A = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨a, ha⟩ := exists_band_one_of_irr L hK2 hIrr
    have : a ∈ A := by simp [hAdef, ha]
    rw [hA_empty] at this; exact absurd this (Finset.notMem_empty _)
  have hA1' : A.card = 1 := le_antisymm hAle hA1
  have hB_ge : 2 ≤ B.card := by omega
  obtain ⟨a, ha_eq⟩ : ∃ a, A = {a} := Finset.card_eq_one.mp hA1'
  obtain ⟨b, hbB, b', hb'B, hbne⟩ := Finset.one_lt_card.mp hB_ge
  have hb : L.band b = 2 := (Finset.mem_filter.mp hbB).2
  have hb' : L.band b' = 2 := (Finset.mem_filter.mp hb'B).2
  obtain ⟨z, hz1, hzb', hnzb⟩ :=
    exists_distinguish_band_two L hK2 hNo hbne hb hb'
  have hz_in_A : z ∈ A := by simp [hAdef, hz1]
  rw [ha_eq, Finset.mem_singleton] at hz_in_A
  obtain ⟨z', hz'1, hz'b, hnz'b'⟩ :=
    exists_distinguish_band_two L hK2 hNo (Ne.symm hbne) hb' hb
  have hz'_in_A : z' ∈ A := by simp [hAdef, hz'1]
  rw [ha_eq, Finset.mem_singleton] at hz'_in_A
  rw [hz_in_A] at hzb' hnzb
  rw [hz'_in_A] at hz'b hnz'b'
  exact hnz'b' hzb'

omit [DecidableEq α] in
/-- Symmetric: under `K = 2` + `NoWithinBandPreceq` + `|α| ≥ 3` +
irreducibility, band 2 has at least 2 elements. -/
lemma two_le_band_two (hK2 : L.K = 2) (hIrr : LayerOrdinalIrreducible L)
    (hCard : 3 ≤ Fintype.card α) (hNo : NoWithinBandPreceq L) :
    2 ≤ ((Finset.univ : Finset α).filter (fun x => L.band x = 2)).card := by
  classical
  set A := (Finset.univ : Finset α).filter (fun x => L.band x = 1) with hAdef
  set B := (Finset.univ : Finset α).filter (fun x => L.band x = 2) with hBdef
  have hAB : A.card + B.card = Fintype.card α := band_partition L hK2
  by_contra hBlt
  push_neg at hBlt
  have hBle : B.card ≤ 1 := by omega
  rcases Nat.lt_or_ge B.card 1 with hB0 | hB1
  · have hB_empty : B = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨b, hb⟩ := exists_band_two_of_irr L hK2 hIrr
    have : b ∈ B := by simp [hBdef, hb]
    rw [hB_empty] at this; exact absurd this (Finset.notMem_empty _)
  have hB1' : B.card = 1 := le_antisymm hBle hB1
  have hA_ge : 2 ≤ A.card := by omega
  obtain ⟨b, hb_eq⟩ : ∃ b, B = {b} := Finset.card_eq_one.mp hB1'
  obtain ⟨a, haA, a', ha'A, hane⟩ := Finset.one_lt_card.mp hA_ge
  have ha : L.band a = 1 := (Finset.mem_filter.mp haA).2
  have ha' : L.band a' = 1 := (Finset.mem_filter.mp ha'A).2
  obtain ⟨z, hz2, haz, hnaz⟩ :=
    exists_distinguish_band_one L hK2 hNo hane ha ha'
  have hz_in_B : z ∈ B := by simp [hBdef, hz2]
  rw [hb_eq, Finset.mem_singleton] at hz_in_B
  obtain ⟨z', hz'2, ha'z', hna'z'⟩ :=
    exists_distinguish_band_one L hK2 hNo (Ne.symm hane) ha' ha
  have hz'_in_B : z' ∈ B := by simp [hBdef, hz'2]
  rw [hb_eq, Finset.mem_singleton] at hz'_in_B
  rw [hz_in_B] at haz hnaz
  rw [hz'_in_B] at ha'z' hna'z'
  exact hna'z' haz

/-! ### §5 — `NConfig`: picking the matching configuration -/

/-- The N-poset cross-pattern data: two distinct elements `a, a'` in
band 1 and two elements `b, b'` in band 2 with the asymmetric
cross-comparabilities `a < b`, `a' < b'`, `¬ a' < b`, `¬ a < b'`. -/
structure NConfig (L : LayeredDecomposition α) where
  /-- First element of band 1. -/
  a : α
  /-- Second element of band 1. -/
  a' : α
  /-- First element of band 2. -/
  b : α
  /-- Second element of band 2. -/
  b' : α
  ha : L.band a = 1
  ha' : L.band a' = 1
  hb : L.band b = 2
  hb' : L.band b' = 2
  ha_ne : a ≠ a'
  hab : a < b
  ha'b' : a' < b'
  hna'b : ¬ a' < b
  hnab' : ¬ a < b'

namespace NConfig

variable {L : LayeredDecomposition α}

omit [DecidableEq α] in
/-- The two band-2 elements of an `NConfig` are distinct (witnessed
by their differing relations to `a`). -/
lemma hb_ne (N : NConfig L) : N.b ≠ N.b' := by
  intro heq
  have h := N.hab
  rw [heq] at h
  exact N.hnab' h

end NConfig

/-- Construct an `NConfig` from the structural hypotheses. -/
lemma exists_NConfig (hK2 : L.K = 2) (hIrr : LayerOrdinalIrreducible L)
    (hCard : 3 ≤ Fintype.card α) (hNo : NoWithinBandPreceq L) :
    Nonempty (NConfig L) := by
  classical
  have hA2 := two_le_band_one L hK2 hIrr hCard hNo
  obtain ⟨a, haA, a', ha'A, hane⟩ := Finset.one_lt_card.mp hA2
  have ha : L.band a = 1 := (Finset.mem_filter.mp haA).2
  have ha' : L.band a' = 1 := (Finset.mem_filter.mp ha'A).2
  obtain ⟨b, hb, hab, hna'b⟩ :=
    exists_distinguish_band_one L hK2 hNo hane ha ha'
  obtain ⟨b', hb', ha'b', hnab'⟩ :=
    exists_distinguish_band_one L hK2 hNo (Ne.symm hane) ha' ha
  exact ⟨⟨a, a', b, b', ha, ha', hb, hb', hane, hab, ha'b', hna'b, hnab'⟩⟩

/-! ### §6 — Third-element compatibility lemmas -/

/-- Helper: if four distinct elements all live in band 2, the band has
size `≥ 4`, contradicting `band_size ≤ 3`. -/
private lemma band_two_card_lt_four
    {b₁ b₂ b₃ b₄ : α}
    (h1 : L.band b₁ = 2) (h2 : L.band b₂ = 2)
    (h3 : L.band b₃ = 2) (h4 : L.band b₄ = 2)
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h14 : b₁ ≠ b₄)
    (h23 : b₂ ≠ b₃) (h24 : b₂ ≠ b₄) (h34 : b₃ ≠ b₄) :
    False := by
  set B := (Finset.univ : Finset α).filter (fun y => L.band y = 2) with hBdef
  have hBle : B.card ≤ 3 := L.band_size 2
  have hb1 : b₁ ∈ B := by simp [hBdef, h1]
  have hb2 : b₂ ∈ B := by simp [hBdef, h2]
  have hb3 : b₃ ∈ B := by simp [hBdef, h3]
  have hb4 : b₄ ∈ B := by simp [hBdef, h4]
  have h4le : ({b₁, b₂, b₃, b₄} : Finset α).card ≤ B.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4eq : ({b₁, b₂, b₃, b₄} : Finset α).card = 4 := by
    rw [show ({b₁, b₂, b₃, b₄} : Finset α) =
        insert b₁ (insert b₂ (insert b₃ {b₄})) from rfl]
    rw [Finset.card_insert_of_notMem
          (by simp [h12, h13, h14] : b₁ ∉ insert b₂ (insert b₃ {b₄}))]
    rw [Finset.card_insert_of_notMem
          (by simp [h23, h24] : b₂ ∉ insert b₃ {b₄})]
    rw [Finset.card_insert_of_notMem (by simp [h34] : b₃ ∉ ({b₄} : Finset α))]
    rfl
  omega

/-- Same helper for band 1. -/
private lemma band_one_card_lt_four
    {a₁ a₂ a₃ a₄ : α}
    (h1 : L.band a₁ = 1) (h2 : L.band a₂ = 1)
    (h3 : L.band a₃ = 1) (h4 : L.band a₄ = 1)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄)
    (h23 : a₂ ≠ a₃) (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄) :
    False := by
  set A := (Finset.univ : Finset α).filter (fun y => L.band y = 1) with hAdef
  have hAle : A.card ≤ 3 := L.band_size 1
  have ha1 : a₁ ∈ A := by simp [hAdef, h1]
  have ha2 : a₂ ∈ A := by simp [hAdef, h2]
  have ha3 : a₃ ∈ A := by simp [hAdef, h3]
  have ha4 : a₄ ∈ A := by simp [hAdef, h4]
  have h4le : ({a₁, a₂, a₃, a₄} : Finset α).card ≤ A.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4eq : ({a₁, a₂, a₃, a₄} : Finset α).card = 4 := by
    rw [show ({a₁, a₂, a₃, a₄} : Finset α) =
        insert a₁ (insert a₂ (insert a₃ {a₄})) from rfl]
    rw [Finset.card_insert_of_notMem
          (by simp [h12, h13, h14] : a₁ ∉ insert a₂ (insert a₃ {a₄}))]
    rw [Finset.card_insert_of_notMem
          (by simp [h23, h24] : a₂ ∉ insert a₃ {a₄})]
    rw [Finset.card_insert_of_notMem (by simp [h34] : a₃ ∉ ({a₄} : Finset α))]
    rfl
  omega

/-- **Third-band-1 compatibility.** For any band-1 element `x` distinct
from the `NConfig` anchors `a, a'`, the cross-relations to `b, b'`
agree.

Proof: contradiction. WLOG assume `x < N.b ∧ ¬ x < N.b'` (the
symmetric case `¬ x < N.b ∧ x < N.b'` uses the `(a', x)` /
`(x, a')` applications instead of `(a, x)` / `(x, a)`).
Apply `NoWithinBandPreceq` to `(a, x)` to get `z₀` in band 2
with `a < z₀ ∧ ¬ x < z₀`; check `z₀ ∉ {N.b, N.b'}` (the
`= N.b` case contradicts `x < N.b`; the `= N.b'` case contradicts
`¬ a < N.b'`). Apply `NoWithinBandPreceq` to `(x, a)` to get
`z₁` in band 2 with `x < z₁ ∧ ¬ a < z₁`; same elimination puts
`z₁ ∉ {N.b, N.b'}`. If `z₀ = z₁`, then `a < z₀` and `¬ a < z₁ = z₀`
contradict; if `z₀ ≠ z₁`, then `{N.b, N.b', z₀, z₁}` are four
distinct band-2 elements, contradicting `band_size ≤ 3`. -/
lemma third_band_one_compat (hK2 : L.K = 2) (hNo : NoWithinBandPreceq L)
    (N : NConfig L) {x : α} (hx : L.band x = 1)
    (hxa : x ≠ N.a) (hxa' : x ≠ N.a') :
    (x < N.b ↔ x < N.b') := by
  -- Generic helper: same-pattern-as-anchor leads to contradiction.
  have key : ∀ {p : α}, L.band p = 1 → p ≠ N.a →
      p < N.b → ¬ p < N.b' → False := by
    intro p hp hpa hpb hnpb'
    obtain ⟨z₀, hz₀2, haz₀, hnpz₀⟩ :=
      exists_distinguish_band_one L hK2 hNo (Ne.symm hpa) N.ha hp
    obtain ⟨z₁, hz₁2, hpz₁, hnaz₁⟩ :=
      exists_distinguish_band_one L hK2 hNo hpa hp N.ha
    have hz₀_neb : z₀ ≠ N.b := fun heq => by rw [heq] at hnpz₀; exact hnpz₀ hpb
    have hz₀_neb' : z₀ ≠ N.b' := fun heq => by rw [heq] at haz₀; exact N.hnab' haz₀
    have hz₁_neb : z₁ ≠ N.b := fun heq => by rw [heq] at hnaz₁; exact hnaz₁ N.hab
    have hz₁_neb' : z₁ ≠ N.b' := fun heq => by rw [heq] at hpz₁; exact hnpb' hpz₁
    by_cases hzeq : z₀ = z₁
    · rw [← hzeq] at hnaz₁; exact hnaz₁ haz₀
    · exact band_two_card_lt_four L N.hb N.hb' hz₀2 hz₁2
        N.hb_ne hz₀_neb.symm hz₁_neb.symm hz₀_neb'.symm hz₁_neb'.symm hzeq
  -- Symmetric helper for the (a', anchor) direction.
  have key' : ∀ {p : α}, L.band p = 1 → p ≠ N.a' →
      ¬ p < N.b → p < N.b' → False := by
    intro p hp hpa' hnpb hpb'
    obtain ⟨z₀, hz₀2, ha'z₀, hnpz₀⟩ :=
      exists_distinguish_band_one L hK2 hNo (Ne.symm hpa') N.ha' hp
    obtain ⟨z₁, hz₁2, hpz₁, hna'z₁⟩ :=
      exists_distinguish_band_one L hK2 hNo hpa' hp N.ha'
    have hz₀_neb : z₀ ≠ N.b := fun heq => by rw [heq] at ha'z₀; exact N.hna'b ha'z₀
    have hz₀_neb' : z₀ ≠ N.b' := fun heq => by rw [heq] at hnpz₀; exact hnpz₀ hpb'
    have hz₁_neb : z₁ ≠ N.b := fun heq => by rw [heq] at hpz₁; exact hnpb hpz₁
    have hz₁_neb' : z₁ ≠ N.b' := fun heq => by rw [heq] at hna'z₁; exact hna'z₁ N.ha'b'
    by_cases hzeq : z₀ = z₁
    · rw [← hzeq] at hna'z₁; exact hna'z₁ ha'z₀
    · exact band_two_card_lt_four L N.hb N.hb' hz₀2 hz₁2
        N.hb_ne hz₀_neb.symm hz₁_neb.symm hz₀_neb'.symm hz₁_neb'.symm hzeq
  refine ⟨fun hxb => ?_, fun hxb' => ?_⟩
  · by_contra hnxb'; exact key hx hxa hxb hnxb'
  · by_contra hnxb; exact key' hx hxa' hnxb hxb'

/-- **Third-band-2 compatibility.** Symmetric to `third_band_one_compat`. -/
lemma third_band_two_compat (hK2 : L.K = 2) (hNo : NoWithinBandPreceq L)
    (N : NConfig L) {y : α} (hy : L.band y = 2)
    (hyb : y ≠ N.b) (hyb' : y ≠ N.b') :
    (N.a < y ↔ N.a' < y) := by
  have key : ∀ {q : α}, L.band q = 2 → q ≠ N.b →
      N.a < q → ¬ N.a' < q → False := by
    intro q hq hqb hay hna'y
    obtain ⟨z₀, hz₀1, hz₀b, hnz₀q⟩ :=
      exists_distinguish_band_two L hK2 hNo hqb hq N.hb
    obtain ⟨z₁, hz₁1, hz₁q, hnz₁b⟩ :=
      exists_distinguish_band_two L hK2 hNo (Ne.symm hqb) N.hb hq
    have hz₀_nea : z₀ ≠ N.a := fun heq => by rw [heq] at hnz₀q; exact hnz₀q hay
    have hz₀_nea' : z₀ ≠ N.a' := fun heq => by rw [heq] at hz₀b; exact N.hna'b hz₀b
    have hz₁_nea : z₁ ≠ N.a := fun heq => by rw [heq] at hnz₁b; exact hnz₁b N.hab
    have hz₁_nea' : z₁ ≠ N.a' := fun heq => by rw [heq] at hz₁q; exact hna'y hz₁q
    by_cases hzeq : z₀ = z₁
    · rw [← hzeq] at hnz₁b; exact hnz₁b hz₀b
    · exact band_one_card_lt_four L N.ha N.ha' hz₀1 hz₁1
        N.ha_ne hz₀_nea.symm hz₁_nea.symm hz₀_nea'.symm hz₁_nea'.symm hzeq
  have key' : ∀ {q : α}, L.band q = 2 → q ≠ N.b' →
      ¬ N.a < q → N.a' < q → False := by
    intro q hq hqb' hnay ha'y
    obtain ⟨z₀, hz₀1, hz₀b', hnz₀q⟩ :=
      exists_distinguish_band_two L hK2 hNo hqb' hq N.hb'
    obtain ⟨z₁, hz₁1, hz₁q, hnz₁b'⟩ :=
      exists_distinguish_band_two L hK2 hNo (Ne.symm hqb') N.hb' hq
    have hz₀_nea : z₀ ≠ N.a := fun heq => by rw [heq] at hz₀b'; exact N.hnab' hz₀b'
    have hz₀_nea' : z₀ ≠ N.a' := fun heq => by rw [heq] at hnz₀q; exact hnz₀q ha'y
    have hz₁_nea : z₁ ≠ N.a := fun heq => by rw [heq] at hz₁q; exact hnay hz₁q
    have hz₁_nea' : z₁ ≠ N.a' := fun heq => by rw [heq] at hnz₁b'; exact hnz₁b' N.ha'b'
    by_cases hzeq : z₀ = z₁
    · rw [← hzeq] at hnz₁b'; exact hnz₁b' hz₀b'
    · exact band_one_card_lt_four L N.ha N.ha' hz₀1 hz₁1
        N.ha_ne hz₀_nea.symm hz₁_nea.symm hz₀_nea'.symm hz₁_nea'.symm hzeq
  refine ⟨fun hay => ?_, fun ha'y => ?_⟩
  · by_contra hna'y; exact key hy hyb hay hna'y
  · by_contra hnay; exact key' hy hyb' hnay ha'y

/-! ### §7 — Building the matching-compatible pair -/

/-- The band-1 same-band pair from an `NConfig`. -/
def NConfig.pairBand1 (N : NConfig L) : CompoundSwap.SameBandPair L where
  a₁ := N.a
  a₂ := N.a'
  hSameBand := N.ha.trans N.ha'.symm
  hne := N.ha_ne

/-- The band-2 same-band pair from an `NConfig`. -/
def NConfig.pairBand2 (N : NConfig L) : CompoundSwap.SameBandPair L where
  a₁ := N.b
  a₂ := N.b'
  hSameBand := N.hb.trans N.hb'.symm
  hne := N.hb_ne

omit [DecidableEq α] in
/-- The four `NConfig` elements live in different bands, hence are
pairwise distinct (band 1 vs band 2). -/
lemma NConfig.ne_a_b (N : NConfig L) : N.a ≠ N.b := by
  intro heq
  have h := N.ha
  rw [heq, N.hb] at h
  exact absurd h (by decide)

omit [DecidableEq α] in
lemma NConfig.ne_a_b' (N : NConfig L) : N.a ≠ N.b' := by
  intro heq
  have h := N.ha
  rw [heq, N.hb'] at h
  exact absurd h (by decide)

omit [DecidableEq α] in
lemma NConfig.ne_a'_b (N : NConfig L) : N.a' ≠ N.b := by
  intro heq
  have h := N.ha'
  rw [heq, N.hb] at h
  exact absurd h (by decide)

omit [DecidableEq α] in
lemma NConfig.ne_a'_b' (N : NConfig L) : N.a' ≠ N.b' := by
  intro heq
  have h := N.ha'
  rw [heq, N.hb'] at h
  exact absurd h (by decide)

/-- The compound-swap matching is compatible: the four elements are
pairwise distinct (different bands) and the swap preserves `≤`. -/
theorem matchingCompatible_of_NConfig (hK2 : L.K = 2)
    (hNo : NoWithinBandPreceq L) (N : NConfig L) :
    CompoundSwap.MatchingCompatible L N.pairBand1 N.pairBand2 where
  ne_a₁_b₁ := N.ne_a_b
  ne_a₁_b₂ := N.ne_a_b'
  ne_a₂_b₁ := N.ne_a'_b
  ne_a₂_b₂ := N.ne_a'_b'
  preserves_le := by
    classical
    -- Reduce the field projections via `change`.
    intro x y hxy
    change Equiv.swap N.b N.b' (Equiv.swap N.a N.a' x) ≤
           Equiv.swap N.b N.b' (Equiv.swap N.a N.a' y)
    rcases lt_or_eq_of_le hxy with hlt | heq
    swap
    · subst heq; exact le_refl _
    obtain ⟨hx1, hy2⟩ := cross_band_under_K2 L hK2 hlt
    -- Key disjointness facts: bands 1, 2 are disjoint.
    have hxne_b : x ≠ N.b := fun he => by
      rw [he] at hx1; rw [N.hb] at hx1; exact absurd hx1 (by decide)
    have hxne_b' : x ≠ N.b' := fun he => by
      rw [he] at hx1; rw [N.hb'] at hx1; exact absurd hx1 (by decide)
    have hyne_a : y ≠ N.a := fun he => by
      rw [he] at hy2; rw [N.ha] at hy2; exact absurd hy2 (by decide)
    have hyne_a' : y ≠ N.a' := fun he => by
      rw [he] at hy2; rw [N.ha'] at hy2; exact absurd hy2 (by decide)
    -- Anchor disjointness packaged for `Equiv.swap_apply_of_ne_of_ne`.
    have hab : N.a ≠ N.b := N.ne_a_b
    have hab' : N.a ≠ N.b' := N.ne_a_b'
    have ha'b : N.a' ≠ N.b := N.ne_a'_b
    have ha'b' : N.a' ≠ N.b' := N.ne_a'_b'
    -- Compute the inner swap on the y side once.
    -- σ(y) = swap N.b N.b' (swap N.a N.a' y).
    -- Since y ≠ N.a and y ≠ N.a', the inner swap fixes y.
    have hsy_inner : Equiv.swap N.a N.a' y = y :=
      Equiv.swap_apply_of_ne_of_ne hyne_a hyne_a'
    rw [hsy_inner]
    -- Now case-split on x vs anchors and y vs anchors.
    by_cases hxa : x = N.a
    · -- x = N.a; inner swap a a' a = a'; outer swap b b' a' = a'.
      subst hxa
      rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne ha'b ha'b']
      by_cases hyb : y = N.b
      · subst hyb; rw [Equiv.swap_apply_left]; exact le_of_lt N.ha'b'
      by_cases hyb' : y = N.b'
      · subst hyb'; exact absurd hlt N.hnab'
      rw [Equiv.swap_apply_of_ne_of_ne hyb hyb']
      exact le_of_lt
        ((third_band_two_compat L hK2 hNo N hy2 hyb hyb').mp hlt)
    by_cases hxa' : x = N.a'
    · subst hxa'
      rw [Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hab hab']
      by_cases hyb : y = N.b
      · subst hyb; exact absurd hlt N.hna'b
      by_cases hyb' : y = N.b'
      · subst hyb'; rw [Equiv.swap_apply_right]; exact le_of_lt N.hab
      rw [Equiv.swap_apply_of_ne_of_ne hyb hyb']
      exact le_of_lt
        ((third_band_two_compat L hK2 hNo N hy2 hyb hyb').mpr hlt)
    -- x ∉ {a, a'}: inner swap fixes x. Outer swap fixes x too (x ≠ b, b').
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxa',
        Equiv.swap_apply_of_ne_of_ne hxne_b hxne_b']
    by_cases hyb : y = N.b
    · subst hyb; rw [Equiv.swap_apply_left]
      exact le_of_lt
        ((third_band_one_compat L hK2 hNo N hx1 hxa hxa').mp hlt)
    by_cases hyb' : y = N.b'
    · subst hyb'; rw [Equiv.swap_apply_right]
      exact le_of_lt
        ((third_band_one_compat L hK2 hNo N hx1 hxa hxa').mpr hlt)
    rw [Equiv.swap_apply_of_ne_of_ne hyb hyb']
    exact le_of_lt hlt

/-! ### §8 — Main theorem -/

/-- **The structural matching lemma** (`mg-c0c7`, PATH B step 2).

Every `LayeredDecomposition` with `K = 2`, `LayerOrdinalIrreducible`,
`w ≥ 1`, `|α| ≥ 3`, and "no within-band `⪯`-comparable pair" admits
two `SameBandPair` witnesses — one in band 1, one in band 2 — whose
compound swap is `CompoundSwap.MatchingCompatible`. -/
theorem matching_exists_of_K2_irreducible_noWithinBand
    (L : LayeredDecomposition α)
    (_hWidth3 : HasWidthAtMost α 3)
    (hK2 : L.K = 2)
    (hIrr : LayerOrdinalIrreducible L)
    (_hw : 1 ≤ L.w)
    (hCard : 3 ≤ Fintype.card α)
    (hNo : NoWithinBandPreceq L) :
    ∃ (P₁ P₂ : CompoundSwap.SameBandPair L),
      L.band P₁.a₁ ≠ L.band P₂.a₁ ∧
      CompoundSwap.MatchingCompatible L P₁ P₂ := by
  obtain ⟨N⟩ := exists_NConfig L hK2 hIrr hCard hNo
  refine ⟨N.pairBand1, N.pairBand2, ?_, matchingCompatible_of_NConfig L hK2 hNo N⟩
  change L.band N.a ≠ L.band N.b
  rw [N.ha, N.hb]
  decide

end CompoundMatching
end Step8
end OneThird
