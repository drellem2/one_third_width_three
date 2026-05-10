/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.RelationPoset.InnerInequality

/-!
# LE-adjacent swap infrastructure for `volumeInnerInequality` (EX-7 Session C.5)

This file lands a focused chunk of the chamber-by-chamber Brightwell §4 /
Daykin–Saks 1981 argument for `volumeInnerInequality`: the LE-level swap
bijection restricted to the chambers where `(a, b)` are *adjacent* in
the linear extension (i.e., `(L.pos a).val + 1 = (L.pos b).val`).

## Mathematical setup (Brightwell §4 / Daykin–Saks 1981, restricted form)

Let `Q : RelationPoset α` and `(a, b)` `Q`-incomparable.  Write
`Q⁺ := addRel Q a b _` (so `a < b` in `Q⁺`) and
`Q⁻ := addRel Q b a _` (so `b < a` in `Q⁻`).

For `L : LinearExt' Q⁺`, the cube-side swap `cubeSwap a b` does **not**
in general carry chambers `σ_L` to `σ_{L'}` for any `L' : LinearExt' Q⁻`,
because the position-swap `Equiv.swap a b ∘ L.toFun` need not respect
`Q⁺.le` in general (per mg-7b85 §1.29 cube-vertex counterexample (2)).

The position-swap **does** respect `Q⁻.le` precisely on the **LE-adjacent
chambers**: those `L` where `a` is immediately before `b` in `L.pos`,
i.e., `(L.pos a).val + 1 = (L.pos b).val`.  On these chambers, the swap
is a bijection
```
{L : LinearExt' Q⁺ | (L.pos a).val + 1 = (L.pos b).val}
  ≃ {L' : LinearExt' Q⁻ | (L'.pos b).val + 1 = (L'.pos a).val}
```
that exchanges the positions of `a` and `b` in `L`.  Combined with the
level-`k` initial-ideal behavior under this swap (this file §3), it
gives the LE-side input to the chamber-by-chamber Brightwell §4 closure.

## Scope (mg-afcf, EX-7 Session C.5; Option α-deeper, no 5th axiom)

This file lands the LE-side combinatorial half of the chamber-by-chamber
argument.  The cube-volume aggregation step (chamber-AD on the LE-adjacent
half plus the LE-non-adjacent residual) is **not** closed here — see
`docs/path-alpha-execution-arc/state.md` §1.30 (this commit) for the
4th-confirmation AMBER verdict and the refined α/β/γ option ladder.

## Main declarations

* `RelationPoset.LinearExt'.AdjLt` — predicate that `a` is immediately
  before `b` in `L.pos` (i.e., `(L.pos a).val + 1 = (L.pos b).val`).
* `RelationPoset.LinearExt'.swapAdj` — for `L : LinearExt' (addRel Q a b _)`
  with `L.AdjLt a b`, the position-swapped extension as a
  `LinearExt' (addRel Q b a _)`.
* `RelationPoset.LinearExt'.swapAdj_pos_a` /
  `RelationPoset.LinearExt'.swapAdj_pos_b` /
  `RelationPoset.LinearExt'.swapAdj_pos_other` — pointwise position
  formulae for the swap.
* `RelationPoset.LinearExt'.swapAdj_AdjLt` — the swap of an `AdjLt`
  extension is itself `AdjLt` (with `a` and `b` exchanged).
* `RelationPoset.LinearExt'.swapAdj_involutive` — the swap is
  involutive (after applying it twice, we get back the original `L`).
* `RelationPoset.LinearExt'.swapAdj_initialIdeal'_of_ne` — for
  `k ≠ (L.pos a).val + 1`, the swap preserves the level-`k` initial
  ideal.
* `RelationPoset.LinearExt'.swapAdj_initialIdeal'_succ_mem_iff` — for
  `k = (L.pos a).val + 1`, membership characterisation showing the
  swap exchanges `a` for `b` in the level-`k` initial ideal.

## Forward to the Brightwell §4 closure

The LE-adjacent swap bijection is the LE-side combinatorial input to the
chamber-by-chamber Brightwell §4 argument.  The remaining gap is the
cube-volume aggregation: showing
```
vol(O(Q⁻) ∩ chambers_adj) · vol(chamberSet' Q⁺ S k ∩ chambers_adj)
  ≥ vol(O(Q⁺) ∩ chambers_adj) · vol(chamberSet' Q⁻ S k ∩ chambers_adj)
```
on the LE-adjacent half (closed by chamber-wise four-function continuous
AD), plus a separate argument that the LE-non-adjacent residual either
vanishes by symmetry (under the swap-pair structure for non-adjacent
LEs, mg-7b85 §1.29 (3)) or is bounded by the adjacent half via
monotonicity.  Per mg-7b85 + this session: 4 polecats have now
independently confirmed that the full chamber-AD aggregation does not
fit a single-polecat budget; see state.md §1.30 (this commit) for the
α/β/γ option ladder.

## References

* G. Brightwell, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, §4 — drops headline.
* D. E. Daykin and M. E. Saks, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142, Theorem 1.
* `docs/path-alpha-execution-arc/state.md` §1.29 — Session C.4 (c4-1)
  hand-off brief (mg-7b85) with chamber-by-chamber LE-adjacent
  recommendation.
* `docs/path-alpha-execution-arc/state.md` §1.30 — Session C.5
  4th-confirmation AMBER verdict (this commit; mg-afcf).
-/

namespace OneThird

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace RelationPoset

namespace LinearExt'

variable {Q : RelationPoset α}

/-! ### §1 — `AdjLt`: `a` immediately before `b` in `L.pos` -/

/-- `L.AdjLt a b` means `a` is immediately before `b` in the position
function of `L`: `(L.pos a).val + 1 = (L.pos b).val`. -/
def AdjLt (L : LinearExt' Q) (a b : α) : Prop :=
  (L.pos a).val + 1 = (L.pos b).val

instance instDecidableAdjLt (L : LinearExt' Q) (a b : α) :
    Decidable (L.AdjLt a b) :=
  inferInstanceAs (Decidable ((L.pos a).val + 1 = (L.pos b).val))

lemma AdjLt.lt {L : LinearExt' Q} {a b : α} (h : L.AdjLt a b) :
    L.lt a b := by
  unfold LinearExt'.lt
  rw [Fin.lt_def, ← h]
  exact Nat.lt_succ_self _

lemma AdjLt.ne {L : LinearExt' Q} {a b : α} (h : L.AdjLt a b) : a ≠ b := by
  intro heq
  have : (L.pos a).val + 1 = (L.pos a).val := by rw [h, heq]
  exact Nat.succ_ne_self _ this

/-! ### §2 — `swapAdj`: position-swap on LE-adjacent extensions

For `L : LinearExt' (addRel Q a b hba)` with `L.AdjLt a b`, define
`L.swapAdj` as the position-swapped extension viewed as a member of
`LinearExt' (addRel Q b a hab)`.  At the bijection level, this is
`(Equiv.swap a b).trans L.toFun`, equivalently `L.toFun ∘ Equiv.swap a b`.

The verification that this respects `(addRel Q b a hab).le` uses the
adjacency hypothesis: for any `(x, y) ∈ Q.le`, swapping `a, b`'s
positions in `L` cannot violate the `≤` between `L.pos x` and
`L.pos y` precisely because `a` and `b` are at consecutive positions. -/

/-- The position-swap function `(α ≃ Fin (Fintype.card α))` exchanging
`a` and `b`'s positions, viewed as a left-precomposition of `L.toFun`
with `Equiv.swap a b` on `α`. -/
def swapEquiv (L : LinearExt' Q) (a b : α) :
    α ≃ Fin (Fintype.card α) :=
  (Equiv.swap a b).trans L.toFun

@[simp] lemma swapEquiv_apply_left (L : LinearExt' Q) (a b : α) :
    L.swapEquiv a b a = L.toFun b := by
  simp [swapEquiv]

@[simp] lemma swapEquiv_apply_right (L : LinearExt' Q) (a b : α) :
    L.swapEquiv a b b = L.toFun a := by
  simp [swapEquiv]

lemma swapEquiv_apply_of_ne_of_ne (L : LinearExt' Q) {a b x : α}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    L.swapEquiv a b x = L.toFun x := by
  simp [swapEquiv, Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-! Helper: position function under swap, in `ℕ` (val) form.

For `L : LinearExt' (addRel Q a b hba)` with `L.AdjLt a b`, define
`p_a := (L.pos a).val` and `p_b := (L.pos b).val`.  The position of
`z` under the swapped extension is:
* `p_b` if `z = a`,
* `p_a` if `z = b`,
* `(L.toFun z).val` otherwise.

This three-case characterisation is used implicitly by the `monotone`
verification of `swapAdj` below. -/

/-- **Adjacent swap.**  For `L : LinearExt' (addRel Q a b hba)` with
`L.AdjLt a b`, the position-swapped extension is a
`LinearExt' (addRel Q b a hab)`. -/
def swapAdj
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) :
    LinearExt' (addRel Q b a hab) where
  toFun := L.swapEquiv a b
  monotone := by
    intro x y hxy
    -- Reduce ≤ on Fin to ≤ on .val.
    rw [show (L.swapEquiv a b x ≤ L.swapEquiv a b y : Prop) =
      ((L.swapEquiv a b x).val ≤ (L.swapEquiv a b y).val : Prop) from rfl]
    -- Cleanly extract the swap formula at the val level.
    have hne : a ≠ b := AdjLt.ne hadj
    have h_succ : (L.pos a).val + 1 = (L.pos b).val := hadj
    have h_swap_a : (L.swapEquiv a b a).val = (L.pos b).val := by
      rw [swapEquiv_apply_left]; rfl
    have h_swap_b : (L.swapEquiv a b b).val = (L.pos a).val := by
      rw [swapEquiv_apply_right]; rfl
    have h_swap_other : ∀ z : α, z ≠ a → z ≠ b →
        (L.swapEquiv a b z).val = (L.pos z).val := by
      intro z hza hzb
      rw [swapEquiv_apply_of_ne_of_ne L hza hzb]; rfl
    -- Helper: x ≠ a, x ≠ b ⟹ swap.pos x = pos x; etc.
    -- Unfold (addRel Q b a hab).le.
    rw [addRel_le_iff] at hxy
    -- Two main cases: (x, y) ∈ Q.le, or (x, y) = (b, a) augmentation.
    rcases hxy with hQxy | ⟨hxb_le, hay_le⟩
    · -- Case 1: Q.le x y.
      -- For y, use eq_of_decidable: (y = a) ∨ (y = b) ∨ (y ∉ {a, b}).
      -- Apply the same to x.  We show pointwise positions.
      -- Use base monotonicity from L (over Q⁺).
      have h_base : L.toFun x ≤ L.toFun y :=
        L.monotone ((subseteq_addRel Q a b hba).le_of_le hQxy)
      -- Convert to val.
      have h_base_val : (L.pos x).val ≤ (L.pos y).val := h_base
      -- Bounded-injectivity facts.
      have hposx_ne : ∀ {z : α}, z ≠ x → L.pos x ≠ L.pos z :=
        fun hzx hh => hzx (L.toFun.injective hh.symm)
      have hposy_ne : ∀ {z : α}, z ≠ y → L.pos z ≠ L.pos y :=
        fun hzy hh => hzy (L.toFun.injective hh)
      -- Branch on whether x ∈ {a, b}.
      rcases eq_or_ne x a with hxa | hxa_ne
      · -- x = a.  Branch on y.
        rcases eq_or_ne y a with hya | hya_ne
        · -- y = a.  Same element; equal positions.
          rw [hxa, hya]
        · rcases eq_or_ne y b with hyb | hyb_ne
          · -- y = b.  Q.le a b false.
            rw [hxa, hyb] at hQxy; exact (hab hQxy).elim
          · -- y ≠ a, y ≠ b.  swap.pos x = pos b, swap.pos y = pos y.
            rw [hxa]
            rw [h_swap_a, h_swap_other y hya_ne hyb_ne]
            -- Need: (L.pos b).val ≤ (L.pos y).val.
            -- We have h_base_val (with x = a): (L.pos a).val ≤ (L.pos y).val.
            -- y ≠ a ⟹ pos y ≠ pos a ⟹ pos y > pos a.
            rw [hxa] at h_base_val
            have h_pos_ne : (L.pos a).val ≠ (L.pos y).val := by
              intro hh
              exact hya_ne.symm (L.toFun.injective (Fin.ext hh))
            -- pos y ≥ pos a + 1 = pos b.
            omega
      · rcases eq_or_ne x b with hxb | hxb_ne
        · -- x = b.  Branch on y.
          rcases eq_or_ne y a with hya | hya_ne
          · -- y = a.  Q.le b a false.
            rw [hxb, hya] at hQxy; exact (hba hQxy).elim
          · rcases eq_or_ne y b with hyb | hyb_ne
            · -- y = b.  Same.
              rw [hxb, hyb]
            · -- y ≠ a, y ≠ b.  swap.pos x = pos a, swap.pos y = pos y.
              rw [hxb]
              rw [h_swap_b, h_swap_other y hya_ne hyb_ne]
              -- Need: (L.pos a).val ≤ (L.pos y).val.
              -- Have: (L.pos b).val ≤ (L.pos y).val ≥ (L.pos a).val + 1.
              rw [hxb] at h_base_val
              omega
        · -- x ≠ a, x ≠ b.  Branch on y.
          rcases eq_or_ne y a with hya | hya_ne
          · -- y = a.  swap.pos y = pos b.  Need pos x ≤ pos b.
            rw [hya]
            rw [h_swap_other x hxa_ne hxb_ne, h_swap_a]
            -- pos x ≤ pos a (from h_base_val with y = a) ≤ pos b - 1 < pos b.
            rw [hya] at h_base_val
            omega
          · rcases eq_or_ne y b with hyb | hyb_ne
            · -- y = b.  swap.pos y = pos a.  Need pos x ≤ pos a.
              rw [hyb]
              rw [h_swap_other x hxa_ne hxb_ne, h_swap_b]
              -- pos x ≤ pos b = pos a + 1.  But pos x ≠ pos b (since x ≠ b).
              rw [hyb] at h_base_val
              have h_pos_ne : (L.pos x).val ≠ (L.pos b).val := by
                intro hh
                exact hxb_ne (L.toFun.injective (Fin.ext hh))
              omega
            · -- y ≠ a, y ≠ b.  swap.pos x = pos x, swap.pos y = pos y.  Direct monotonicity.
              rw [h_swap_other x hxa_ne hxb_ne, h_swap_other y hya_ne hyb_ne]
              exact h_base_val
    · -- Case 2: (x, y) = (b, a) augmentation.  hxb_le : Q.le x b, hay_le : Q.le a y.
      have h_base_xb : (L.pos x).val ≤ (L.pos b).val :=
        L.monotone ((subseteq_addRel Q a b hba).le_of_le hxb_le)
      have h_base_ay : (L.pos a).val ≤ (L.pos y).val :=
        L.monotone ((subseteq_addRel Q a b hba).le_of_le hay_le)
      rcases eq_or_ne x a with hxa | hxa_ne
      · -- x = a.  Q.le a b is false.
        rw [hxa] at hxb_le; exact (hab hxb_le).elim
      · rcases eq_or_ne x b with hxb | hxb_ne
        · -- x = b.  swap.pos x = pos a.
          rw [hxb]
          rw [h_swap_b]
          rcases eq_or_ne y a with hya | hya_ne
          · rw [hya]; rw [h_swap_a]
            -- Need: pos a ≤ pos b.
            omega
          · rcases eq_or_ne y b with hyb | hyb_ne
            · -- y = b.  Q.le a b false.
              rw [hyb] at hay_le; exact (hab hay_le).elim
            · -- y ≠ a, y ≠ b.  swap.pos y = pos y.  pos a ≤ pos y from h_base_ay.
              rw [h_swap_other y hya_ne hyb_ne]
              exact h_base_ay
        · -- x ≠ a, x ≠ b.  swap.pos x = pos x.
          rw [h_swap_other x hxa_ne hxb_ne]
          rcases eq_or_ne y a with hya | hya_ne
          · -- y = a.  swap.pos y = pos b.  Need pos x ≤ pos b.
            rw [hya]; rw [h_swap_a]
            exact h_base_xb
          · rcases eq_or_ne y b with hyb | hyb_ne
            · -- y = b.  Q.le a b false.
              rw [hyb] at hay_le; exact (hab hay_le).elim
            · -- y ≠ a, y ≠ b.  swap.pos y = pos y.
              rw [h_swap_other y hya_ne hyb_ne]
              -- Need: pos x ≤ pos y.
              -- pos x ≤ pos b = pos a + 1.  But x ≠ b ⟹ pos x ≠ pos b ⟹ pos x ≤ pos a.
              -- pos a ≤ pos y.
              have h_pos_x_ne : (L.pos x).val ≠ (L.pos b).val := by
                intro hh
                exact hxb_ne (L.toFun.injective (Fin.ext hh))
              omega

/-! ### §2.5 — Pointwise position formulae for `swapAdj` -/

@[simp] lemma swapAdj_pos_a
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) :
    (LinearExt'.swapAdj hba hab L hadj).pos a = L.pos b := by
  change (L.swapEquiv a b a) = L.pos b
  simp [LinearExt'.pos]

@[simp] lemma swapAdj_pos_b
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) :
    (LinearExt'.swapAdj hba hab L hadj).pos b = L.pos a := by
  change (L.swapEquiv a b b) = L.pos a
  simp [LinearExt'.pos]

lemma swapAdj_pos_other
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) {x : α} (hxa : x ≠ a) (hxb : x ≠ b) :
    (LinearExt'.swapAdj hba hab L hadj).pos x = L.pos x := by
  change (L.swapEquiv a b x) = L.pos x
  rw [swapEquiv_apply_of_ne_of_ne L hxa hxb]
  rfl

/-! ### §3 — Adjacency property of the swap; involutivity -/

/-- The swap of an `AdjLt` extension is itself `AdjLt`, with the order
of `a` and `b` exchanged. -/
lemma swapAdj_AdjLt
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) :
    (LinearExt'.swapAdj hba hab L hadj).AdjLt b a := by
  unfold AdjLt
  rw [swapAdj_pos_a hba hab L hadj, swapAdj_pos_b hba hab L hadj]
  -- Goal: (L.pos a).val + 1 = (L.pos b).val.  This is hadj.
  exact hadj

/-- **Involutivity of `swapAdj`**: applying `swapAdj` twice gives back
the original extension (the inner swap takes `Q⁺` to `Q⁻`; the outer
swap with arguments reversed takes `Q⁻` back to `Q⁺`).  Algebraically,
`swap b a ∘ swap a b = id` since `Equiv.swap a b = Equiv.swap b a` and
swap is an involution. -/
lemma swapAdj_swapAdj
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) :
    (LinearExt'.swapAdj hab hba
      (LinearExt'.swapAdj hba hab L hadj)
      (swapAdj_AdjLt hba hab L hadj)) = L := by
  -- Show the underlying Equiv is the same.
  apply LinearExt'.ext
  -- The outer swapAdj's toFun is `(swapAdj hba hab L hadj).swapEquiv b a`, by def.
  -- (swapEquiv b a) on top of (swapEquiv a b) is the identity at the equiv level.
  change ((LinearExt'.swapAdj hba hab L hadj).swapEquiv b a) = L.toFun
  unfold swapEquiv
  -- Now: (Equiv.swap b a).trans ((swapAdj hba hab L hadj).toFun) = L.toFun.
  change (Equiv.swap b a).trans ((Equiv.swap a b).trans L.toFun) = L.toFun
  rw [← Equiv.trans_assoc, Equiv.swap_comm b a]
  -- (swap a b).trans (swap a b) = refl
  rw [Equiv.swap_swap]
  exact Equiv.refl_trans _

/-! ### §4 — Level-`k` initial-ideal behavior under `swapAdj`

For `L : LinearExt' (addRel Q a b hba)` with `L.AdjLt a b`, denote
`m := (L.pos a).val` (so `(L.pos b).val = m + 1`).  The level-`k`
initial ideal `(swapAdj L hadj).initialIdeal' k` differs from
`L.initialIdeal' k` only when `k = m + 1`, in which case the swap
exchanges `a` for `b` in the initial ideal:

* For `k ≠ m + 1`: `(swapAdj L hadj).iI k = L.iI k`.
* For `k = m + 1`: `(swapAdj L hadj).iI k = (L.iI k \ {a}) ∪ {b}`. -/

lemma swapAdj_mem_initialIdeal'_iff
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) (k : ℕ) (x : α) :
    x ∈ (LinearExt'.swapAdj hba hab L hadj).initialIdeal' k ↔
      ((LinearExt'.swapAdj hba hab L hadj).pos x).val < k := by
  exact mem_initialIdeal'

/-- For levels `k ≠ (L.pos a).val + 1`, the swap preserves the level-`k`
initial ideal. -/
lemma swapAdj_initialIdeal'_of_ne
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) {k : ℕ}
    (hk : k ≠ (L.pos a).val + 1) :
    (LinearExt'.swapAdj hba hab L hadj).initialIdeal' k =
      L.initialIdeal' k := by
  -- The position function is the same except at a, b, where it is
  -- swapped.  At level k ≠ (L.pos a).val + 1, the membership question
  -- "is L.pos a < k" agrees with "is L.pos b < k" (both true if
  -- k > (L.pos b).val, both false if k ≤ (L.pos a).val, since adjacency
  -- forces (L.pos b).val = (L.pos a).val + 1).
  have hadj' : (L.pos a).val + 1 = (L.pos b).val := hadj
  ext x
  rw [swapAdj_mem_initialIdeal'_iff hba hab L hadj k x, mem_initialIdeal']
  by_cases hxa : x = a
  · subst hxa
    rw [swapAdj_pos_a hba hab L hadj]
    -- (L.pos b).val < k ↔ (L.pos a).val < k, given (L.pos a).val + 1 = (L.pos b).val
    -- and k ≠ (L.pos a).val + 1.
    omega
  · by_cases hxb : x = b
    · subst hxb
      rw [swapAdj_pos_b hba hab L hadj]
      -- (L.pos a).val < k ↔ (L.pos b).val < k.
      omega
    · rw [swapAdj_pos_other hba hab L hadj hxa hxb]

/-- For level `k = (L.pos a).val + 1`, the swap exchanges `a` for `b`
in the level-`k` initial ideal.  This is the case where the swap
genuinely changes the initial ideal: `a` is removed (now at position
`(L.pos a).val + 1 = k`, no longer `< k`) and `b` is added (now at
position `(L.pos a).val < k`).  Stated as a membership equivalence. -/
lemma swapAdj_initialIdeal'_succ_mem_iff
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (L : LinearExt' (addRel Q a b hba))
    (hadj : L.AdjLt a b) (x : α) :
    x ∈ (LinearExt'.swapAdj hba hab L hadj).initialIdeal'
        ((L.pos a).val + 1) ↔
      (x = b ∨ (x ≠ a ∧ x ∈ L.initialIdeal' ((L.pos a).val + 1))) := by
  rw [swapAdj_mem_initialIdeal'_iff hba hab L hadj _ x]
  rw [mem_initialIdeal']
  rcases eq_or_ne x a with hxa | hxa_ne
  · -- x = a.  swap.pos a = pos b.  (L.pos b).val < (L.pos a).val + 1 is false
    -- because the two are equal.
    rw [hxa, swapAdj_pos_a hba hab L hadj]
    have hne : a ≠ b := AdjLt.ne hadj
    have h_eq : (L.pos b).val = (L.pos a).val + 1 := hadj.symm
    constructor
    · intro h; exfalso; omega
    · rintro (h | ⟨h, _⟩)
      · exact (hne h).elim
      · exact (h rfl).elim
  · rcases eq_or_ne x b with hxb | hxb_ne
    · -- x = b.  swap.pos b = pos a.
      rw [hxb, swapAdj_pos_b hba hab L hadj]
      simp
    · rw [swapAdj_pos_other hba hab L hadj hxa_ne hxb_ne]
      simp [hxb_ne, hxa_ne]

/-! ### §5 — The bijection: LE-adjacent `Q⁺`-LEs ↔ LE-adjacent `Q⁻`-LEs

The map `swapAdj` extends to a bijection between:
* `{L : LinearExt' (addRel Q a b hba) | L.AdjLt a b}` and
* `{L' : LinearExt' (addRel Q b a hab) | L'.AdjLt b a}`.

This is the LE-side combinatorial bijection underpinning the chamber-
by-chamber Brightwell §4 closure on the LE-adjacent half. -/

/-- **The LE-adjacent swap equiv (forward map).** -/
def swapAdjEquivFun
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    {L : LinearExt' (addRel Q a b hba) // L.AdjLt a b} →
      {L' : LinearExt' (addRel Q b a hab) // L'.AdjLt b a} :=
  fun L => ⟨LinearExt'.swapAdj hba hab L.val L.property,
            swapAdj_AdjLt hba hab L.val L.property⟩

/-- **The LE-adjacent swap equiv.** -/
def swapAdjEquiv
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    {L : LinearExt' (addRel Q a b hba) // L.AdjLt a b} ≃
      {L' : LinearExt' (addRel Q b a hab) // L'.AdjLt b a} where
  toFun := swapAdjEquivFun hba hab
  invFun := swapAdjEquivFun hab hba
  left_inv := by
    rintro ⟨L, hL⟩
    apply Subtype.ext
    exact swapAdj_swapAdj hba hab L hL
  right_inv := by
    rintro ⟨L', hL'⟩
    apply Subtype.ext
    exact swapAdj_swapAdj hab hba L' hL'

/-- **Cardinality consequence:** the number of LE-adjacent `Q⁺`-LEs
equals the number of LE-adjacent `Q⁻`-LEs (with the orientations
reversed: `a` immediately before `b` vs. `b` immediately before `a`). -/
theorem card_adjLt_eq
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b) :
    (Finset.univ.filter
      (fun L : LinearExt' (addRel Q a b hba) => L.AdjLt a b)).card =
    (Finset.univ.filter
      (fun L' : LinearExt' (addRel Q b a hab) => L'.AdjLt b a)).card := by
  classical
  -- Use Fintype.card on the subtype.
  have h₁ : (Finset.univ.filter
      (fun L : LinearExt' (addRel Q a b hba) => L.AdjLt a b)).card =
      Fintype.card {L : LinearExt' (addRel Q a b hba) // L.AdjLt a b} :=
    (Fintype.card_subtype _).symm
  have h₂ : (Finset.univ.filter
      (fun L' : LinearExt' (addRel Q b a hab) => L'.AdjLt b a)).card =
      Fintype.card {L' : LinearExt' (addRel Q b a hab) // L'.AdjLt b a} :=
    (Fintype.card_subtype _).symm
  rw [h₁, h₂]
  exact Fintype.card_congr (swapAdjEquiv hba hab)

end LinearExt'

end RelationPoset

end OneThird
