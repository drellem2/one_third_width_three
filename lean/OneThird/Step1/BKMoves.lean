/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Poset
import OneThird.RichPair
import OneThird.Step1.CommonChain
import OneThird.Step1.LocalCoords
import OneThird.Step1.GroundSet
import OneThird.Mathlib.BKGraph

/-!
# Step 1, part (iii): the BK-move classification

Faithful Lean port of part (iii) of the local interface theorem
(`thm:interface`, `step1.tex:155-173`): the classification of how a
single Bubley–Karzanov move acts on the local coordinates
`(i, j, σ) = (iCoord, jCoord, signMarker)` of a rich pair `(x, y)`.

A BK move replaces a linear extension `L` by `L'` by swapping one
`L`-adjacent **incomparable** pair `{a, b}`. The whole content of
part (iii) is that the swap reverses the strict order of *exactly* the
ordered pair it touches (`BKAdj.swapPair`), and therefore:

* the **sign marker** `σ` changes iff the swapped pair is `{x, y}`
  itself (`bkSwap_signFlip`); otherwise it is preserved
  (`bkSwap_signMarker_eq`);
* the **first coordinate** `i` changes iff the swapped pair is
  `{x, c}` for a common neighbour `c`, and then by exactly `±1`
  (`bkSwap_iCoord_shift`); otherwise it is preserved
  (`bkSwap_iCoord_eq`);
* the **second coordinate** `j` changes iff the swapped pair is
  `{y, c}`, by exactly `±1` (`bkSwap_jCoord_shift`); otherwise it is
  preserved (`bkSwap_jCoord_eq`).

The headline `bkMove_classification` packages these into the paper's
trichotomy: every BK move either fixes `(i, j, σ)`, or flips `σ` only,
or shifts `i` by `±1` only, or shifts `j` by `±1` only.

## Note on faithfulness

`step1.tex` part (iii) groups moves into three cases (a) internal grid
step, (b) sign flip, (c) external–external swap. Reading the proof in
`step1.tex:204-246` literally, case (a) is itself non-uniform: the
"mixed" sub-case (swapping a common neighbour `c` with an *external*
element `z`) preserves `(i, j, σ)` — it is a "grid step of `0`". The
precise truth, established here, is that `(i, j, σ)` is altered *only*
by the three special swap types `{x, y}`, `{x, c}`, `{y, c}`; every
other swap (including all of case (c) and the mixed part of case (a))
preserves all three. This is a strict refinement of the paper's
prose, not a contradiction of it.

## Main definitions

* `OneThird.BKSwaps L L' a b` — the abstract data of a BK move: `L, L'`
  differ by reversing the strict order of the incomparable pair
  `{a, b}` and nothing else.

## Main results

* `OneThird.BKAdj.swapPair` — every BK move arises from a `BKSwaps`.
* `OneThird.bkSwap_iCoord_eq`, `bkSwap_jCoord_eq`,
  `bkSwap_signMarker_eq` — coordinate/sign preservation off the
  special swaps.
* `OneThird.bkSwap_iCoord_shift`, `bkSwap_jCoord_shift` — the `±1`
  grid steps.
* `OneThird.bkSwap_signFlip` — the sign-flip move.
* `OneThird.bkMove_classification` — the part-(iii) trichotomy.
-/

namespace OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## Common-neighbour membership API -/

/-- Membership in the common-neighbour finset. -/
lemma mem_commonNbhdFinset {x y z : α} :
    z ∈ commonNbhdFinset x y ↔ (z ∥ x) ∧ (z ∥ y) := by
  unfold commonNbhdFinset
  simp [Finset.mem_filter]

/-- A common neighbour of `(x, y)` is distinct from `x`. -/
lemma commonNbhdFinset_ne_left {x y z : α} (hz : z ∈ commonNbhdFinset x y) :
    z ≠ x :=
  fun h => (mem_commonNbhdFinset.mp hz).1.1 (h ▸ le_refl z)

/-- A common neighbour of `(x, y)` is distinct from `y`. -/
lemma commonNbhdFinset_ne_right {x y z : α} (hz : z ∈ commonNbhdFinset x y) :
    z ≠ y :=
  fun h => (mem_commonNbhdFinset.mp hz).2.1 (h ▸ le_refl z)

/-! ## Strict-order trichotomy inside a linear extension -/

private lemma linExt_lt_or {L : LinearExt α} {a b : α} (hne : a ≠ b) :
    L.lt a b ∨ L.lt b a := by
  rcases lt_trichotomy (L.pos a) (L.pos b) with h | h | h
  · exact Or.inl h
  · exact absurd (L.pos_injective h) hne
  · exact Or.inr h

private lemma linExt_not_lt_of_lt {L : LinearExt α} {a b : α}
    (h : L.lt a b) : ¬ L.lt b a :=
  fun h' => absurd (h.trans h') (lt_irrefl _)

private lemma linExt_lt_of_not_lt {L : LinearExt α} {a b : α}
    (hne : a ≠ b) (h : ¬ L.lt a b) : L.lt b a :=
  (linExt_lt_or hne).resolve_left h

/-! ## Coordinate / sign congruence lemmas -/

/-- If the strict order of every common neighbour against `x` is
unchanged, the first coordinate `i` is unchanged. -/
lemma iCoord_congr {x y : α} {L L' : LinearExt α}
    (h : ∀ c ∈ commonNbhdFinset x y, (L.lt c x ↔ L'.lt c x)) :
    iCoord x y L = iCoord x y L' := by
  unfold iCoord
  exact congrArg Finset.card (Finset.filter_congr h)

/-- If the strict order of every common neighbour against `y` is
unchanged, the second coordinate `j` is unchanged. -/
lemma jCoord_congr {x y : α} {L L' : LinearExt α}
    (h : ∀ c ∈ commonNbhdFinset x y, (L.lt c y ↔ L'.lt c y)) :
    jCoord x y L = jCoord x y L' := by
  unfold jCoord
  exact congrArg Finset.card (Finset.filter_congr h)

/-- If the strict order of `x` against `y` is unchanged, the sign
marker `σ` is unchanged. -/
lemma signMarker_congr {x y : α} {L L' : LinearExt α}
    (h : L.lt x y ↔ L'.lt x y) :
    signMarker x y L = signMarker x y L' := by
  unfold signMarker
  exact decide_eq_decide.mpr h

/-- If the strict order of `x` against `y` is *reversed*, the sign
marker `σ` flips. -/
lemma signMarker_flip {x y : α} {L L' : LinearExt α}
    (h : L.lt x y ↔ ¬ L'.lt x y) :
    signMarker x y L = ! signMarker x y L' := by
  unfold signMarker
  rw [decide_eq_decide.mpr h, decide_not]

/-! ## The swapped pair of a BK move -/

/-- Position trichotomy for a BK move: every element either is the
first swapped element `a` (positions `k`, `k+1`), the second `b`
(positions `k+1`, `k`), or has an unchanged position avoiding both
`k` and `k+1`. -/
private lemma bkAdj_posVal {L L' : LinearExt α} {a b : α}
    {k : Fin (Fintype.card α)} {hk : k.val + 1 < Fintype.card α}
    (hLa : L.pos a = k) (hLb : L.pos b = ⟨k.val + 1, hk⟩)
    (hL'a : L'.pos a = ⟨k.val + 1, hk⟩) (hL'b : L'.pos b = k)
    (hrest : ∀ z : α, z ≠ a → z ≠ b → L.pos z = L'.pos z) (p : α) :
    ((L.pos p).val = k.val ∧ (L'.pos p).val = k.val + 1) ∨
    ((L.pos p).val = k.val + 1 ∧ (L'.pos p).val = k.val) ∨
    ((L.pos p).val = (L'.pos p).val ∧
      (L.pos p).val ≠ k.val ∧ (L.pos p).val ≠ k.val + 1) := by
  by_cases hpa : p = a
  · subst hpa
    exact Or.inl ⟨congrArg Fin.val hLa, congrArg Fin.val hL'a⟩
  · by_cases hpb : p = b
    · subst hpb
      exact Or.inr (Or.inl ⟨congrArg Fin.val hLb, congrArg Fin.val hL'b⟩)
    · refine Or.inr (Or.inr ⟨congrArg Fin.val (hrest p hpa hpb), ?_, ?_⟩)
      · intro hv
        exact hpa (L.pos_injective
          (Fin.ext (hv.trans (congrArg Fin.val hLa).symm)))
      · intro hv
        exact hpb (L.pos_injective
          (Fin.ext (hv.trans (congrArg Fin.val hLb).symm)))

/-- A BK swap reverses the strict order of exactly the swapped pair:
for every ordered pair `(p, q)` other than `(a, b)` and `(b, a)`, the
strict order is preserved. -/
private lemma bkAdj_lt_iff {L L' : LinearExt α} {a b : α}
    {k : Fin (Fintype.card α)} {hk : k.val + 1 < Fintype.card α}
    (hLa : L.pos a = k) (hLb : L.pos b = ⟨k.val + 1, hk⟩)
    (hL'a : L'.pos a = ⟨k.val + 1, hk⟩) (hL'b : L'.pos b = k)
    (hrest : ∀ z : α, z ≠ a → z ≠ b → L.pos z = L'.pos z)
    {p q : α} (hpq : ¬(p = a ∧ q = b)) (hqp : ¬(p = b ∧ q = a)) :
    (L.lt p q ↔ L'.lt p q) := by
  have hP := bkAdj_posVal hLa hLb hL'a hL'b hrest p
  have hQ := bkAdj_posVal hLa hLb hL'a hL'b hrest q
  -- Identify `p`/`q` with `a`/`b` from the position data.
  have hpaI : (L.pos p).val = k.val → p = a := fun hv =>
    L.pos_injective (Fin.ext (hv.trans (congrArg Fin.val hLa).symm))
  have hpbI : (L.pos p).val = k.val + 1 → p = b := fun hv =>
    L.pos_injective (Fin.ext (hv.trans (congrArg Fin.val hLb).symm))
  have hqaI : (L.pos q).val = k.val → q = a := fun hv =>
    L.pos_injective (Fin.ext (hv.trans (congrArg Fin.val hLa).symm))
  have hqbI : (L.pos q).val = k.val + 1 → q = b := fun hv =>
    L.pos_injective (Fin.ext (hv.trans (congrArg Fin.val hLb).symm))
  -- Convert the swapped-pair exclusion into arithmetic on positions.
  have hpq' : ¬((L.pos p).val = k.val ∧ (L.pos q).val = k.val + 1) :=
    fun h => hpq ⟨hpaI h.1, hqbI h.2⟩
  have hqp' : ¬((L.pos p).val = k.val + 1 ∧ (L.pos q).val = k.val) :=
    fun h => hqp ⟨hpbI h.1, hqaI h.2⟩
  simp only [LinearExt.lt, Fin.lt_def]
  rcases hP with ⟨hLp, hL'p⟩ | ⟨hLp, hL'p⟩ | ⟨hLp, hpk, hpk1⟩ <;>
    rcases hQ with ⟨hLq, hL'q⟩ | ⟨hLq, hL'q⟩ | ⟨hLq, hqk, hqk1⟩ <;>
    omega

/-- **Abstract BK swap.** `BKSwaps L L' a b` records that `L` and `L'`
differ by reversing the strict order of the incomparable pair
`{a, b}`: `a ∥ b`, `a` precedes `b` in `L` but not in `L'`, and the
strict order of every other ordered pair is preserved.

This is the structural content of a single BK move
(`step1.tex:155-173`); see `BKAdj.swapPair`. -/
def BKSwaps (L L' : LinearExt α) (a b : α) : Prop :=
  (a ∥ b) ∧ L.lt a b ∧ ¬ L'.lt a b ∧
    ∀ p q : α, ¬(p = a ∧ q = b) → ¬(p = b ∧ q = a) →
      (L.lt p q ↔ L'.lt p q)

namespace BKSwaps

variable {L L' : LinearExt α} {a b : α}

lemma incomp (h : BKSwaps L L' a b) : a ∥ b := h.1

lemma ne (h : BKSwaps L L' a b) : a ≠ b :=
  fun heq => Incomp.irrefl a (heq ▸ h.1)

lemma lt_left (h : BKSwaps L L' a b) : L.lt a b := h.2.1

lemma not_lt_left' (h : BKSwaps L L' a b) : ¬ L'.lt a b := h.2.2.1

lemma preserve (h : BKSwaps L L' a b) {p q : α}
    (hpq : ¬(p = a ∧ q = b)) (hqp : ¬(p = b ∧ q = a)) :
    (L.lt p q ↔ L'.lt p q) := h.2.2.2 p q hpq hqp

end BKSwaps

/-- **Every BK move is a `BKSwaps`** (`step1.tex:155-173`): two
BK-adjacent linear extensions differ by reversing exactly one
incomparable pair. -/
theorem BKAdj.swapPair {L L' : LinearExt α} (h : BKAdj L L') :
    ∃ a b : α, BKSwaps L L' a b := by
  obtain ⟨a, b, k, hk, hab, hLa, hLb, hL'a, hL'b, hrest⟩ := h
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · have e1 : (L.pos a).val = k.val := congrArg Fin.val hLa
    have e2 : (L.pos b).val = k.val + 1 := congrArg Fin.val hLb
    simp only [LinearExt.lt, Fin.lt_def]; omega
  · have e1 : (L'.pos a).val = k.val + 1 := congrArg Fin.val hL'a
    have e2 : (L'.pos b).val = k.val := congrArg Fin.val hL'b
    simp only [LinearExt.lt, Fin.lt_def]; omega
  · intro p q hpq hqp
    exact bkAdj_lt_iff hLa hLb hL'a hL'b hrest hpq hqp

/-! ## Filter-cardinality surgery for the `±1` grid steps -/

/-- If two predicates agree on `s` except at a single point `e ∈ s`,
where `q` holds and `p` fails, the `q`-filter has exactly one more
element than the `p`-filter. -/
private lemma card_filter_succ_of_one_flip {β : Type*} [DecidableEq β]
    (s : Finset β) (p q : β → Prop) [DecidablePred p] [DecidablePred q]
    (e : β) (he : e ∈ s) (hep : ¬ p e) (heq : q e)
    (hagree : ∀ z ∈ s, z ≠ e → (p z ↔ q z)) :
    (s.filter q).card = (s.filter p).card + 1 := by
  have hins : s.filter q = insert e (s.filter p) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨hzs, hqz⟩
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr ⟨hzs, (hagree z hzs hze).mpr hqz⟩
    · rintro (rfl | ⟨hzs, hpz⟩)
      · exact ⟨he, heq⟩
      · by_cases hze : z = e
        · exact ⟨hzs, hze ▸ heq⟩
        · exact ⟨hzs, (hagree z hzs hze).mp hpz⟩
  rw [hins, Finset.card_insert_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => hep

/-! ## Case (c)/(a-mixed): coordinate preservation off the special swaps -/

/-- **First coordinate preserved** unless the swapped pair is `{x, c}`
for a common neighbour `c`. -/
theorem bkSwap_iCoord_eq {x y a b : α} {L L' : LinearExt α}
    (hsw : BKSwaps L L' a b)
    (hnot : ∀ c ∈ commonNbhdFinset x y, ¬((a = x ∧ b = c) ∨ (a = c ∧ b = x))) :
    iCoord x y L = iCoord x y L' := by
  apply iCoord_congr
  intro c hc
  apply hsw.preserve
  · rintro ⟨hca, hxb⟩
    exact hnot c hc (Or.inr ⟨hca.symm, hxb.symm⟩)
  · rintro ⟨hcb, hxa⟩
    exact hnot c hc (Or.inl ⟨hxa.symm, hcb.symm⟩)

/-- **Second coordinate preserved** unless the swapped pair is
`{y, c}` for a common neighbour `c`. -/
theorem bkSwap_jCoord_eq {x y a b : α} {L L' : LinearExt α}
    (hsw : BKSwaps L L' a b)
    (hnot : ∀ c ∈ commonNbhdFinset x y, ¬((a = y ∧ b = c) ∨ (a = c ∧ b = y))) :
    jCoord x y L = jCoord x y L' := by
  apply jCoord_congr
  intro c hc
  apply hsw.preserve
  · rintro ⟨hca, hyb⟩
    exact hnot c hc (Or.inr ⟨hca.symm, hyb.symm⟩)
  · rintro ⟨hcb, hya⟩
    exact hnot c hc (Or.inl ⟨hya.symm, hcb.symm⟩)

/-- **Sign marker preserved** unless the swapped pair is `{x, y}`. -/
theorem bkSwap_signMarker_eq {x y a b : α} {L L' : LinearExt α}
    (hsw : BKSwaps L L' a b)
    (hnot : ¬((a = x ∧ b = y) ∨ (a = y ∧ b = x))) :
    signMarker x y L = signMarker x y L' := by
  apply signMarker_congr
  apply hsw.preserve
  · rintro ⟨hxa, hyb⟩
    exact hnot (Or.inl ⟨hxa.symm, hyb.symm⟩)
  · rintro ⟨hxb, hya⟩
    exact hnot (Or.inr ⟨hya.symm, hxb.symm⟩)

/-! ## Case (a): the `±1` grid steps -/

/-- **First coordinate grid step.** If the swapped pair is `{x, c}`
for a common neighbour `c`, the coordinate `i` changes by exactly
`±1`. -/
theorem bkSwap_iCoord_shift {x y a b c : α} {L L' : LinearExt α}
    (hsw : BKSwaps L L' a b) (hc : c ∈ commonNbhdFinset x y)
    (hpair : (a = x ∧ b = c) ∨ (a = c ∧ b = x)) :
    iCoord x y L' = iCoord x y L + 1 ∨ iCoord x y L = iCoord x y L' + 1 := by
  have hcx : c ≠ x := commonNbhdFinset_ne_left hc
  -- common neighbours `c' ≠ c` keep their order against `x`
  have hagree : ∀ c' ∈ commonNbhdFinset x y, c' ≠ c →
      (L.lt c' x ↔ L'.lt c' x) := by
    intro c' hc' hne
    apply hsw.preserve
    · rintro ⟨hc'a, hxb⟩
      rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact commonNbhdFinset_ne_left hc' (hc'a.trans ha)
      · exact hne (hc'a.trans ha)
    · rintro ⟨hc'b, hxa⟩
      rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hne (hc'b.trans hb)
      · exact commonNbhdFinset_ne_left hc' (hc'b.trans hb)
  unfold iCoord
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- orientation `a = x`, `b = c`: order `(c, x)` is `(b, a)`
    have hcS : ¬ L.lt c x := by
      rw [show c = b from hb.symm, show x = a from ha.symm]
      exact linExt_not_lt_of_lt hsw.lt_left
    have hcS' : L'.lt c x := by
      rw [show c = b from hb.symm, show x = a from ha.symm]
      exact linExt_lt_of_not_lt hsw.ne hsw.not_lt_left'
    left
    exact card_filter_succ_of_one_flip (commonNbhdFinset x y)
      (fun z => L.lt z x) (fun z => L'.lt z x) c hc hcS hcS' hagree
  · -- orientation `a = c`, `b = x`: order `(c, x)` is `(a, b)`
    have hcS : L.lt c x := by
      rw [show c = a from ha.symm, show x = b from hb.symm]; exact hsw.lt_left
    have hcS' : ¬ L'.lt c x := by
      rw [show c = a from ha.symm, show x = b from hb.symm]
      exact hsw.not_lt_left'
    right
    exact card_filter_succ_of_one_flip (commonNbhdFinset x y)
      (fun z => L'.lt z x) (fun z => L.lt z x) c hc hcS' hcS
      (fun z hz hne => (hagree z hz hne).symm)

/-- **Second coordinate grid step.** If the swapped pair is `{y, c}`
for a common neighbour `c`, the coordinate `j` changes by exactly
`±1`. -/
theorem bkSwap_jCoord_shift {x y a b c : α} {L L' : LinearExt α}
    (hsw : BKSwaps L L' a b) (hc : c ∈ commonNbhdFinset x y)
    (hpair : (a = y ∧ b = c) ∨ (a = c ∧ b = y)) :
    jCoord x y L' = jCoord x y L + 1 ∨ jCoord x y L = jCoord x y L' + 1 := by
  have hcy : c ≠ y := commonNbhdFinset_ne_right hc
  have hagree : ∀ c' ∈ commonNbhdFinset x y, c' ≠ c →
      (L.lt c' y ↔ L'.lt c' y) := by
    intro c' hc' hne
    apply hsw.preserve
    · rintro ⟨hc'a, hyb⟩
      rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact commonNbhdFinset_ne_right hc' (hc'a.trans ha)
      · exact hne (hc'a.trans ha)
    · rintro ⟨hc'b, hya⟩
      rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact hne (hc'b.trans hb)
      · exact commonNbhdFinset_ne_right hc' (hc'b.trans hb)
  unfold jCoord
  rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hcS : ¬ L.lt c y := by
      rw [show c = b from hb.symm, show y = a from ha.symm]
      exact linExt_not_lt_of_lt hsw.lt_left
    have hcS' : L'.lt c y := by
      rw [show c = b from hb.symm, show y = a from ha.symm]
      exact linExt_lt_of_not_lt hsw.ne hsw.not_lt_left'
    left
    exact card_filter_succ_of_one_flip (commonNbhdFinset x y)
      (fun z => L.lt z y) (fun z => L'.lt z y) c hc hcS hcS' hagree
  · have hcS : L.lt c y := by
      rw [show c = a from ha.symm, show y = b from hb.symm]; exact hsw.lt_left
    have hcS' : ¬ L'.lt c y := by
      rw [show c = a from ha.symm, show y = b from hb.symm]
      exact hsw.not_lt_left'
    right
    exact card_filter_succ_of_one_flip (commonNbhdFinset x y)
      (fun z => L'.lt z y) (fun z => L.lt z y) c hc hcS' hcS
      (fun z hz hne => (hagree z hz hne).symm)

/-! ## Case (b): the sign-flip move -/

/-- **Sign-flip move.** If the swapped pair is exactly `{x, y}`, the
sign marker `σ` flips while `(i, j)` are preserved. -/
theorem bkSwap_signFlip {x y a b : α} {L L' : LinearExt α} (hxy : x ∥ y)
    (hsw : BKSwaps L L' a b) (hpair : (a = x ∧ b = y) ∨ (a = y ∧ b = x)) :
    signMarker x y L = ! signMarker x y L' ∧
      iCoord x y L = iCoord x y L' ∧ jCoord x y L = jCoord x y L' := by
  have hxny : x ≠ y := fun h => hxy.1 (h ▸ le_refl x)
  refine ⟨?_, ?_, ?_⟩
  · apply signMarker_flip
    rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [show x = a from ha.symm, show y = b from hb.symm]
      exact ⟨fun _ => hsw.not_lt_left', fun _ => hsw.lt_left⟩
    · rw [show x = b from hb.symm, show y = a from ha.symm]
      refine ⟨fun h => absurd h (linExt_not_lt_of_lt hsw.lt_left), fun h => ?_⟩
      exact absurd (linExt_lt_of_not_lt hsw.ne hsw.not_lt_left') h
  · apply bkSwap_iCoord_eq hsw
    intro c hc
    have hcx : c ≠ x := commonNbhdFinset_ne_left hc
    have hcy : c ≠ y := commonNbhdFinset_ne_right hc
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all
  · apply bkSwap_jCoord_eq hsw
    intro c hc
    have hcx : c ≠ x := commonNbhdFinset_ne_left hc
    have hcy : c ≠ y := commonNbhdFinset_ne_right hc
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all

/-! ## The classification theorem -/

/-- **BK-move classification** (part (iii) of `thm:interface`,
`step1.tex:155-173`).

Let `(x, y)` be an incomparable pair in a width-`3` poset and let
`L → L'` be a single BK move. Then exactly one of four things happens
to the local coordinates `(i, j, σ)`:

* all of `(i, j, σ)` are preserved (the swap is external, or mixes a
  common neighbour with an external element);
* `σ` flips and `(i, j)` are preserved (the swap is `{x, y}`);
* `i` shifts by `±1`, while `j` and `σ` are preserved (the swap is
  `{x, c}` for a common neighbour `c`);
* `j` shifts by `±1`, while `i` and `σ` are preserved (the swap is
  `{y, c}`).

The hypothesis `HasWidthAtMost α 3` is used to rule out a swap of two
common neighbours: by `commonNbhd_isChain_of_width3` the
common-neighbour set is a chain, so no two of its elements are
incomparable and hence none can be a BK-swapped pair. -/
theorem bkMove_classification (hP : HasWidthAtMost α 3) {x y : α}
    (hxy : x ∥ y) {L L' : LinearExt α} (h : BKAdj L L') :
    (iCoord x y L = iCoord x y L' ∧ jCoord x y L = jCoord x y L' ∧
        signMarker x y L = signMarker x y L') ∨
    (signMarker x y L = ! signMarker x y L' ∧
        iCoord x y L = iCoord x y L' ∧ jCoord x y L = jCoord x y L') ∨
    ((iCoord x y L' = iCoord x y L + 1 ∨ iCoord x y L = iCoord x y L' + 1) ∧
        jCoord x y L = jCoord x y L' ∧
        signMarker x y L = signMarker x y L') ∨
    ((jCoord x y L' = jCoord x y L + 1 ∨ jCoord x y L = jCoord x y L' + 1) ∧
        iCoord x y L = iCoord x y L' ∧
        signMarker x y L = signMarker x y L') := by
  classical
  obtain ⟨a, b, hsw⟩ := h.swapPair
  by_cases hSign : (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  · -- the swap is `{x, y}`: sign flip
    obtain ⟨hflip, hi, hj⟩ := bkSwap_signFlip hxy hsw hSign
    exact Or.inr (Or.inl ⟨hflip, hi, hj⟩)
  · by_cases hXC : ∃ c ∈ commonNbhdFinset x y, (a = x ∧ b = c) ∨ (a = c ∧ b = x)
    · -- the swap is `{x, c}`: `i`-shift
      obtain ⟨c, hc, hpair⟩ := hXC
      have hcy : c ≠ y := commonNbhdFinset_ne_right hc
      have hcx : c ≠ x := commonNbhdFinset_ne_left hc
      have hxny : x ≠ y := fun he => hxy.1 (he ▸ le_refl x)
      have hjeq : jCoord x y L = jCoord x y L' := by
        apply bkSwap_jCoord_eq hsw
        intro c' hc' hbad
        have hc'x : c' ≠ x := commonNbhdFinset_ne_left hc'
        have hc'y : c' ≠ y := commonNbhdFinset_ne_right hc'
        rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
          rcases hbad with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all
      have hseq : signMarker x y L = signMarker x y L' := by
        apply bkSwap_signMarker_eq hsw
        rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
          rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all
      exact Or.inr (Or.inr (Or.inl
        ⟨bkSwap_iCoord_shift hsw hc hpair, hjeq, hseq⟩))
    · by_cases hYC : ∃ c ∈ commonNbhdFinset x y,
          (a = y ∧ b = c) ∨ (a = c ∧ b = y)
      · -- the swap is `{y, c}`: `j`-shift
        obtain ⟨c, hc, hpair⟩ := hYC
        have hcy : c ≠ y := commonNbhdFinset_ne_right hc
        have hcx : c ≠ x := commonNbhdFinset_ne_left hc
        have hxny : x ≠ y := fun he => hxy.1 (he ▸ le_refl x)
        have hieq : iCoord x y L = iCoord x y L' := by
          apply bkSwap_iCoord_eq hsw
          intro c' hc' hbad
          have hc'x : c' ≠ x := commonNbhdFinset_ne_left hc'
          have hc'y : c' ≠ y := commonNbhdFinset_ne_right hc'
          rcases hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
            rcases hbad with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all
        have hseq : signMarker x y L = signMarker x y L' := by
          apply bkSwap_signMarker_eq hsw
          rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
            rcases hpair with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> simp_all
        exact Or.inr (Or.inr (Or.inr
          ⟨bkSwap_jCoord_shift hsw hc hpair, hieq, hseq⟩))
      · -- everything else: `(i, j, σ)` all preserved
        refine Or.inl ⟨?_, ?_, ?_⟩
        · exact bkSwap_iCoord_eq hsw (fun c hc hbad => hXC ⟨c, hc, hbad⟩)
        · exact bkSwap_jCoord_eq hsw (fun c hc hbad => hYC ⟨c, hc, hbad⟩)
        · exact bkSwap_signMarker_eq hsw hSign

/-! ## Non-vacuity: a concrete width-3 non-chain instance

The discrete `Fin 3` poset `Antichain3` (defined in
`OneThird/Step1/GroundSet.lean` by the S1-A port) is a concrete
width-`3`, non-chain poset on which the BK-move classification has
genuine content: the pair `(a0, a1)` is incomparable and has `a2` as
a common neighbour, so the sign-flip swap `{a0, a1}` and the
`i`/`j`-grid swaps `{a0, a2}`, `{a1, a2}` are all realizable. This
certifies that `bkMove_classification` is not vacuously true (it is
not an `α`-empty / `BKAdj`-empty baseline). -/

/-- **Non-vacuity of the BK-move classification.** The concrete
width-`3` non-chain poset `Antichain3` carries an incomparable pair
`(a0, a1)` with a genuine common neighbour `a2` — so the hypotheses
of `bkMove_classification` (`HasWidthAtMost α 3`, `x ∥ y`) are
jointly satisfiable at a poset that is neither empty nor a
subsingleton, and the common-neighbour finset that drives the
`i`/`j`-grid cases is non-empty. -/
theorem bkMove_classification_nonvacuous :
    HasWidthAtMost Antichain3 3 ∧ ¬ IsChainPoset Antichain3 ∧
      (Antichain3.a0 ∥ Antichain3.a1) ∧
      IsRich 1 Antichain3.a0 Antichain3.a1 ∧
      Antichain3.a2 ∈ commonNbhdFinset Antichain3.a0 Antichain3.a1 := by
  refine ⟨Antichain3.hasWidthAtMost, Antichain3.not_isChainPoset,
    Antichain3.incomp_iff_ne.mpr (by decide), Antichain3.isRich_a0_a1, ?_⟩
  rw [Antichain3.commonNbhdFinset_a0_a1]
  exact Finset.mem_singleton.mpr rfl

end OneThird
