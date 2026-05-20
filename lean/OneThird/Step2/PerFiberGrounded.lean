/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.WeakGridFull
import OneThird.Step1.Interface
import OneThird.Step1.GroundSet

/-!
# Step 2 — weak grid stability and the initial per-fiber transport, grounded

This file is **part 1 of the Step 2 Lean port** of the Option A' FULL
REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`, mg-d8c7
§2.1 Piece 1, Wave-2; work item mg-0893, ticket OneThird-S2-A).  It
delivers two products:

1. **`lem:weak-grid` as a Step 2 statement** (`step2.tex` Lemma
   `lem:weak-grid`).  The planar isoperimetric stability lemma was
   ported as a `Finset (ℤ × ℤ)` statement by F6a/F6b
   (`OneThird.Step2.WeakGrid.weak_grid`).  Here it is re-exposed with
   the **explicit stability rate** `δ(ε) = 4ε/c` named
   (`weakGridRate`) and the qualitative `δ(ε) → 0 as ε → 0` content
   recorded (`weakGridRate_le_of_le`, `weakGridRate_mono`).

2. **The initial per-fiber transport** (`step2.tex`
   §"From global conductance to per-fiber boundary", the part of
   `prop:per-fiber` that the weak grid lemma feeds).  This is the
   genuine *grounding* on the Step 1 interface: a good fiber
   `F : Finset (LinearExt α)` (Step 1's `IsGoodFiber`, `def:good-fiber`)
   is transported through the local coordinate map `localCoord` to a
   concrete order-convex grid domain `fiberGrid x y F ⊆ ℤ²`, and a
   cut `S ⊆ LinearExt α` to its image `fiberCut x y F S`.  The
   **`def:step1-data` clause (S1.4)** — "the BK-boundary of `S ∩ F`
   equals the grid boundary of its coordinate image" — is the
   load-bearing transport step `fiberBKBdy_card_eq_gridBdy_card`, and
   it lets `weak_grid` be applied fiber-by-fiber
   (`per_fiber_weak_grid`).

## What "grounded on `thm:interface`" means here

The per-fiber transport consumes the Step 1 *local interface theorem*
`thm:interface` (`OneThird.thm_interface`, `lean/OneThird/Step1/Interface.lean`)
through its part-(ii) good-fiber data: a fiber `F` carrying
`IsGoodFiber x y F` has

* (G1) `localCoord` injective once the sign is constant — used for the
  bijection `F ≃ fiberGrid x y F`;
* (G2) order-convex coordinate image — transported here from `ℕ²` to
  the ambient `ℤ²` lattice (`fiberGrid_isOrdConvex`), the hypothesis
  `weak_grid` needs;
* (G3) internal BK edges are exactly unit grid moves — the heart of
  the BK-boundary ↔ grid-boundary identity.

## Main results

* `weakGridRate` — the explicit stability rate `δ(ε) = 4ε/c`.
* `lem_weak_grid` — `lem:weak-grid` as a Step 2 statement, with the
  named rate.
* `fiberGrid` / `fiberCut` — the per-fiber grid domain `D_{x,y}` and
  cut image `A_{x,y}`, grounded on a good fiber.
* `fiberGrid_isOrdConvex`, `fiberGrid_box`, `fiberCut_subset`,
  `fiberGrid_card` — the planar shape facts the weak grid lemma needs.
* `fiberBKBdy_card_eq_gridBdy_card` — the (S1.4) transport: per-fiber
  BK-boundary count equals grid-boundary count.
* `per_fiber_weak_grid` — the initial per-fiber transport: a good
  fiber with small per-fiber BK-boundary admits a staircase
  approximation with error `≤ δ(ε) · |D_{x,y}|`.
* `per_fiber_grounded_nonvacuous` — the mg-0893 acceptance witness:
  the port fires non-vacuously at the concrete width-3 non-chain
  poset `Antichain3`.

The completion of `prop:per-fiber` (the global double-counting
`lem:fiber-avg` averaging and `thm:step2`) is the S2-B follow-on.
-/

namespace OneThird
namespace Step2
namespace PerFiberGrounded

open Finset OneThird.Mathlib.Grid2D OneThird.Step2.WeakGrid

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1. `lem:weak-grid` as a Step 2 statement

The planar weak grid stability lemma is the F6a/F6b deliverable
`OneThird.Step2.WeakGrid.weak_grid`.  Step 2 consumes it with the
stability rate named: `step2.tex` Lemma `lem:weak-grid` asserts that
"for every `ε > 0` there exists `δ(ε) > 0` with `δ(ε) → 0` as
`ε → 0`"; the F6 proof exhibits the explicit linear rate
`δ(ε) = 4ε/c`. -/

/-- The **weak grid stability rate** `δ(ε) = 4ε/c` of `lem:weak-grid`
(`step2.tex`).  The F6 proof obtains this explicit linear rate, which
the paper notes is even better than the crudely-claimed
`O(ε^{1/3})`. -/
def weakGridRate (c ε : ℚ) : ℚ := 4 * ε / c

/-- The stability rate is non-negative for non-negative `ε` and
positive `c`. -/
theorem weakGridRate_nonneg {c ε : ℚ} (hc : 0 < c) (hε : 0 ≤ ε) :
    0 ≤ weakGridRate c ε := by
  unfold weakGridRate
  positivity

/-- **The rate is monotone in `ε`.**  A smaller boundary budget gives
a smaller (better) staircase-approximation error. -/
theorem weakGridRate_mono {c ε₁ ε₂ : ℚ} (hc : 0 < c) (h : ε₁ ≤ ε₂) :
    weakGridRate c ε₁ ≤ weakGridRate c ε₂ := by
  unfold weakGridRate
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (inv_pos.mpr hc))

/-- **`δ(ε) → 0` as `ε → 0`** (quantitative form).  For every target
`ρ > 0` there is an `ε`-threshold below which the stability rate is
`≤ ρ`: explicitly, `ε ≤ ρ·c/4` forces `weakGridRate c ε ≤ ρ`.  This
is the `δ(ε) → 0` qualitative content of `step2.tex`
Lemma `lem:weak-grid`. -/
theorem weakGridRate_le_of_le {c ε ρ : ℚ} (hc : 0 < c)
    (h : ε ≤ ρ * c / 4) : weakGridRate c ε ≤ ρ := by
  unfold weakGridRate
  rw [div_le_iff₀ hc]
  nlinarith

/-- **`lem:weak-grid` (Step 2 statement).**  For an order-convex
`D ⊆ [0,t]²` with `|D| ≥ c·t²` and a subset `A ⊆ D` whose grid
boundary is `≤ ε·t`, there is a genuine `+`-staircase region `M` with
symmetric-difference error at most `δ(ε)·|D|`, where
`δ(ε) = weakGridRate c ε = 4ε/c`.

This is the Step 2 re-exposition of the F6a/F6b planar deliverable
`OneThird.Step2.WeakGrid.weak_grid`, with the stability rate named.
The qualitative `δ(ε) → 0` conclusion is `weakGridRate_le_of_le`. -/
theorem lem_weak_grid {D A : Finset (ℤ × ℤ)} {t : ℕ} {c ε : ℚ}
    (hc : 0 < c)
    (hD : IsOrdConvex (D : Set (ℤ × ℤ)))
    (hbox : ∀ p ∈ D, 0 ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (t : ℤ))
    (ht : 1 ≤ t)
    (hmass : c * (t : ℚ) ^ 2 ≤ (D.card : ℚ))
    (hAD : A ⊆ D)
    (hbdy : ((gridBdy D A).card : ℚ) ≤ ε * (t : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircasePlus D M ∧
      ((symmDiff A M).card : ℚ) ≤ weakGridRate c ε * (D.card : ℚ) := by
  unfold weakGridRate
  exact weak_grid hc hD hbox ht hmass hAD hbdy

/-! ## §2. Per-fiber grid data, grounded on a good fiber

A good fiber `F` (Step 1 `IsGoodFiber`, `def:good-fiber`) carries a
local coordinate map `localCoord x y : LinearExt α → ℕ × ℕ` whose
image is order-convex in `ℕ²` (clause G2).  The weak grid lemma lives
on the ambient lattice `ℤ²`, so this section casts the coordinate
data to `ℤ²` and transports the order-convexity. -/

/-- The lattice embedding `ℕ² ↪ ℤ²`. -/
def toGrid (p : ℕ × ℕ) : ℤ × ℤ := ((p.1 : ℤ), (p.2 : ℤ))

@[simp] theorem toGrid_fst (p : ℕ × ℕ) : (toGrid p).1 = (p.1 : ℤ) := rfl
@[simp] theorem toGrid_snd (p : ℕ × ℕ) : (toGrid p).2 = (p.2 : ℤ) := rfl

theorem toGrid_injective : Function.Injective toGrid := by
  intro p q h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- The **per-fiber grid domain** `D_{x,y}`: the coordinate image of
the good fiber `F`, cast into the ambient lattice `ℤ²`.  This is the
`def:step1-data` clause (S1.2) domain. -/
noncomputable def fiberGrid (x y : α) (F : Finset (LinearExt α)) :
    Finset (ℤ × ℤ) :=
  F.image (fun L => toGrid (localCoord x y L))

/-- The **per-fiber cut image** `A_{x,y} = π_{x,y}(S ∩ fib_{x,y})`:
the coordinate image of the part of the cut `S` lying in `F`. -/
noncomputable def fiberCut (x y : α) (F S : Finset (LinearExt α)) :
    Finset (ℤ × ℤ) :=
  (F ∩ S).image (fun L => toGrid (localCoord x y L))

theorem mem_fiberGrid {x y : α} {F : Finset (LinearExt α)} {p : ℤ × ℤ} :
    p ∈ fiberGrid x y F ↔ ∃ L ∈ F, toGrid (localCoord x y L) = p := by
  unfold fiberGrid; rw [Finset.mem_image]

theorem mem_fiberCut {x y : α} {F S : Finset (LinearExt α)} {p : ℤ × ℤ} :
    p ∈ fiberCut x y F S ↔ ∃ L ∈ F ∩ S, toGrid (localCoord x y L) = p := by
  unfold fiberCut; rw [Finset.mem_image]

/-- The cut image is a subset of the grid domain (`A ⊆ D`). -/
theorem fiberCut_subset (x y : α) (F S : Finset (LinearExt α)) :
    fiberCut x y F S ⊆ fiberGrid x y F :=
  Finset.image_subset_image (Finset.inter_subset_left)

/-- **`localCoord` is injective on a constant-sign good fiber.**
Clause G1 of `IsGoodFiber` gives `(localCoord, signMarker)`
injectivity; with the sign constant on `F`, `localCoord` alone is
injective. -/
theorem localCoord_injOn {x y : α} {F : Finset (LinearExt α)} {ε₀ : Bool}
    (hF : IsGoodFiber x y F) (hsign : ∀ L ∈ F, signMarker x y L = ε₀)
    {L₁ : LinearExt α} (h₁ : L₁ ∈ F) {L₂ : LinearExt α} (h₂ : L₂ ∈ F)
    (hpq : localCoord x y L₁ = localCoord x y L₂) : L₁ = L₂ :=
  hF.1 L₁ h₁ L₂ h₂ hpq (by rw [hsign L₁ h₁, hsign L₂ h₂])

/-- **Box bound.**  Every cell of the per-fiber grid domain lies in
`[0, t]²`, where `t = t(x, y)` is the common-neighbour-chain length.
This is `def:step1-data` clause (S1.2)'s `D_{x,y} ⊆ [0,t]²`. -/
theorem fiberGrid_box (x y : α) (F : Finset (LinearExt α)) :
    ∀ p ∈ fiberGrid x y F,
      0 ≤ p.1 ∧ p.1 ≤ (commonNbhdLength x y : ℤ) ∧
      0 ≤ p.2 ∧ p.2 ≤ (commonNbhdLength x y : ℤ) := by
  intro p hp
  rw [mem_fiberGrid] at hp
  obtain ⟨L, _, rfl⟩ := hp
  simp only [toGrid_fst, toGrid_snd]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · exact_mod_cast localCoord_fst_le x y L
  · exact_mod_cast localCoord_snd_le x y L

/-- **Order-convexity transport (G2).**  The per-fiber grid domain is
order-convex in the ambient lattice `ℤ²`.  Clause G2 of `IsGoodFiber`
delivers order-convexity of the coordinate image in `ℕ²`; this lemma
transports it through the embedding `toGrid : ℕ² ↪ ℤ²`.  Order-convexity
is the hypothesis `lem:weak-grid` consumes. -/
theorem fiberGrid_isOrdConvex {x y : α} {F : Finset (LinearExt α)}
    (hF : IsGoodFiber x y F) :
    IsOrdConvex ((fiberGrid x y F : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  constructor
  intro P hP Q hQ R hR
  -- `R` lies in the order-interval `[P, Q]`.
  rw [Set.mem_Icc] at hR
  obtain ⟨hPR, hRQ⟩ := hR
  -- Unpack `P`, `Q` as coordinate images and substitute.
  rw [Finset.mem_coe, mem_fiberGrid] at hP hQ
  obtain ⟨L, hLF, hL⟩ := hP
  obtain ⟨L', hL'F, hL'⟩ := hQ
  subst hL; subst hL'
  simp only [Prod.le_def, toGrid_fst, toGrid_snd] at hPR hRQ
  obtain ⟨hPR1, hPR2⟩ := hPR
  obtain ⟨hRQ1, hRQ2⟩ := hRQ
  -- `R` has non-negative coordinates, so it is the image of a `ℕ²` point.
  have hcL1 : (0 : ℤ) ≤ ((localCoord x y L).1 : ℤ) := by positivity
  have hcL2 : (0 : ℤ) ≤ ((localCoord x y L).2 : ℤ) := by positivity
  have hR1 : (0 : ℤ) ≤ R.1 := le_trans hcL1 hPR1
  have hR2 : (0 : ℤ) ≤ R.2 := le_trans hcL2 hPR2
  have hrR : toGrid (R.1.toNat, R.2.toNat) = R := by
    apply Prod.ext
    · change ((R.1.toNat : ℤ)) = R.1
      exact Int.toNat_of_nonneg hR1
    · change ((R.2.toNat : ℤ)) = R.2
      exact Int.toNat_of_nonneg hR2
  -- Apply clause G2 to `localCoord L`, `localCoord L'`, `r`.
  have hp_mem : localCoord x y L ∈ F.image (localCoord x y) :=
    Finset.mem_image_of_mem _ hLF
  have hq_mem : localCoord x y L' ∈ F.image (localCoord x y) :=
    Finset.mem_image_of_mem _ hL'F
  have hPQ1 : (localCoord x y L).1 ≤ (localCoord x y L').1 := by
    have : ((localCoord x y L).1 : ℤ) ≤ ((localCoord x y L').1 : ℤ) :=
      le_trans hPR1 hRQ1
    exact_mod_cast this
  have hPQ2 : (localCoord x y L).2 ≤ (localCoord x y L').2 := by
    have : ((localCoord x y L).2 : ℤ) ≤ ((localCoord x y L').2 : ℤ) :=
      le_trans hPR2 hRQ2
    exact_mod_cast this
  have hr1 : (localCoord x y L).1 ≤ (R.1.toNat, R.2.toNat).1 ∧
      (R.1.toNat, R.2.toNat).1 ≤ (localCoord x y L').1 := by
    change (localCoord x y L).1 ≤ R.1.toNat ∧ R.1.toNat ≤ (localCoord x y L').1
    omega
  have hr2 : (localCoord x y L).2 ≤ (R.1.toNat, R.2.toNat).2 ∧
      (R.1.toNat, R.2.toNat).2 ≤ (localCoord x y L').2 := by
    change (localCoord x y L).2 ≤ R.2.toNat ∧ R.2.toNat ≤ (localCoord x y L').2
    omega
  have hr_mem : (R.1.toNat, R.2.toNat) ∈ F.image (localCoord x y) :=
    hF.2.1 _ hp_mem _ hq_mem hPQ1 hPQ2 _ hr1 hr2
  -- `R = toGrid r` is therefore in the grid domain.
  rw [Finset.mem_coe, mem_fiberGrid]
  obtain ⟨L'', hL''F, hL''⟩ := Finset.mem_image.mp hr_mem
  exact ⟨L'', hL''F, by rw [hL'', hrR]⟩

/-- **The coordinate map is a bijection `F ≃ D_{x,y}`** (`def:step1-data`
clause (S1.3)): on a constant-sign good fiber, the grid domain has the
same cardinality as the fiber.  This is the bijection `π_{x,y}` that
makes the per-fiber transport mass-preserving. -/
theorem fiberGrid_card {x y : α} {F : Finset (LinearExt α)} {ε₀ : Bool}
    (hF : IsGoodFiber x y F) (hsign : ∀ L ∈ F, signMarker x y L = ε₀) :
    (fiberGrid x y F).card = F.card := by
  unfold fiberGrid
  apply Finset.card_image_of_injOn
  intro L₁ h₁ L₂ h₂ h
  exact localCoord_injOn hF hsign h₁ h₂ (toGrid_injective h)

/-! ## §3. The per-fiber transport: BK-boundary = grid-boundary

This is the load-bearing step `def:step1-data` clause (S1.4): inside a
good fiber, a BK-edge is a unit grid move (clause G3), so the
BK-boundary of `S ∩ F` is in bijection with the grid boundary of the
coordinate image `A_{x,y} ⊆ D_{x,y}`. -/

/-- The **per-fiber BK-boundary** of a cut `S`, in directed form: the
ordered BK-edges `(L, L')` with `L ∈ F ∩ S`, `L' ∈ F ∖ S`.  This is
`step2.tex` Definition `def:edge-internal` restricted to edges
internal to `F`, presented as directed pairs (each undirected
boundary edge contributes exactly one directed pair, from its `S`
endpoint to its `Sᶜ` endpoint). -/
noncomputable def fiberBKBdy (F S : Finset (LinearExt α)) :
    Finset (LinearExt α × LinearExt α) := by
  classical
  exact ((F ∩ S) ×ˢ (F \ S)).filter (fun p => BKAdj p.1 p.2)

theorem mem_fiberBKBdy {F S : Finset (LinearExt α)}
    {p : LinearExt α × LinearExt α} :
    p ∈ fiberBKBdy F S ↔
      (p.1 ∈ F ∩ S ∧ p.2 ∈ F \ S) ∧ BKAdj p.1 p.2 := by
  classical
  unfold fiberBKBdy
  rw [Finset.mem_filter, Finset.mem_product]

/-- `ℓ¹` distance of two `toGrid`-images, expanded. -/
theorem l1dist_toGrid (p q : ℕ × ℕ) :
    l1dist (toGrid p) (toGrid q)
      = ((p.1 : ℤ) - (q.1 : ℤ)).natAbs + ((p.2 : ℤ) - (q.2 : ℤ)).natAbs :=
  rfl

/-- **Unit grid move ↔ `ℓ¹`-adjacency.**  The clause-G3 description of
a BK move (one coordinate shifts by `±1`, the other is fixed) is
exactly `ℓ¹`-distance `1` between the `toGrid`-images. -/
theorem unitMove_iff_l1dist (i₁ j₁ i₂ j₂ : ℕ) :
    ((i₁ = i₂ + 1 ∧ j₁ = j₂) ∨ (i₂ = i₁ + 1 ∧ j₁ = j₂) ∨
     (j₁ = j₂ + 1 ∧ i₁ = i₂) ∨ (j₂ = j₁ + 1 ∧ i₁ = i₂))
    ↔ l1dist (toGrid (i₁, j₁)) (toGrid (i₂, j₂)) = 1 := by
  rw [l1dist_toGrid]
  omega

/-- **`def:step1-data` clause (S1.4): the per-fiber transport.**

On a constant-sign good fiber `F`, the per-fiber BK-boundary of a cut
`S` (Definition `def:edge-internal`) is in cardinality-bijection with
the grid boundary of the transported cut `fiberCut x y F S` inside the
grid domain `fiberGrid x y F`.

The bijection sends a directed BK-edge `(L, L')` to the directed grid
pair `(π L, π L')`.  Forward direction uses G1 (injectivity) to place
`π L'` outside the cut image, and G3 to turn the BK move into a unit
grid move; the reverse direction inverts both. -/
theorem fiberBKBdy_card_eq_gridBdy_card {x y : α}
    {F S : Finset (LinearExt α)} {ε₀ : Bool}
    (hF : IsGoodFiber x y F) (hsign : ∀ L ∈ F, signMarker x y L = ε₀) :
    (fiberBKBdy F S).card
      = (gridBdy (fiberGrid x y F) (fiberCut x y F S)).card := by
  classical
  refine Finset.card_bij
    (fun p _ => (toGrid (localCoord x y p.1), toGrid (localCoord x y p.2)))
    ?_ ?_ ?_
  · -- image lands in the grid boundary
    intro p hp
    rw [mem_fiberBKBdy] at hp
    obtain ⟨⟨hp1, hp2⟩, hadj⟩ := hp
    obtain ⟨hp1F, hp1S⟩ := Finset.mem_inter.mp hp1
    obtain ⟨hp2F, hp2S⟩ := Finset.mem_sdiff.mp hp2
    rw [mk_mem_gridBdy]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `π p.1 ∈ A`
      rw [mem_fiberCut]
      exact ⟨p.1, Finset.mem_inter.mpr ⟨hp1F, hp1S⟩, rfl⟩
    · -- `π p.2 ∈ D`
      rw [mem_fiberGrid]
      exact ⟨p.2, hp2F, rfl⟩
    · -- `π p.2 ∉ A`
      rw [mem_fiberCut]
      rintro ⟨L'', hL'', hL''eq⟩
      obtain ⟨hL''F, hL''S⟩ := Finset.mem_inter.mp hL''
      have : L'' = p.2 :=
        localCoord_injOn hF hsign hL''F hp2F (toGrid_injective hL''eq)
      exact hp2S (this ▸ hL''S)
    · -- the move is a unit grid move (the G3 sign-flip branch is ruled
      -- out by the constant sign `ε₀` of the fiber `F`)
      rcases (hF.2.2 p.1 hp1F p.2 hp2F).mp hadj with ⟨_, hmove⟩ | ⟨hflip, _⟩
      · change L1Adj _ _
        unfold L1Adj
        have := (unitMove_iff_l1dist (iCoord x y p.1) (jCoord x y p.1)
          (iCoord x y p.2) (jCoord x y p.2)).mp hmove
        simpa [localCoord] using this
      · exfalso
        rw [hsign p.1 hp1F, hsign p.2 hp2F] at hflip
        exact absurd hflip (by cases ε₀ <;> simp)
  · -- injectivity
    intro p hp q hq hpq
    rw [mem_fiberBKBdy] at hp hq
    obtain ⟨hpeq1, hpeq2⟩ := Prod.mk.inj hpq
    have h1 : localCoord x y p.1 = localCoord x y q.1 := toGrid_injective hpeq1
    have h2 : localCoord x y p.2 = localCoord x y q.2 := toGrid_injective hpeq2
    have hp1F := (Finset.mem_inter.mp hp.1.1).1
    have hq1F := (Finset.mem_inter.mp hq.1.1).1
    have hp2F := (Finset.mem_sdiff.mp hp.1.2).1
    have hq2F := (Finset.mem_sdiff.mp hq.1.2).1
    have e1 : p.1 = q.1 := localCoord_injOn hF hsign hp1F hq1F h1
    have e2 : p.2 = q.2 := localCoord_injOn hF hsign hp2F hq2F h2
    exact Prod.ext e1 e2
  · -- surjectivity
    intro b hb
    rw [mem_gridBdy] at hb
    obtain ⟨hbA, hbD, hbnA, hbadj⟩ := hb
    rw [mem_fiberCut] at hbA
    obtain ⟨L, hLFS, hLeq⟩ := hbA
    rw [mem_fiberGrid] at hbD
    obtain ⟨L', hL'F, hL'eq⟩ := hbD
    obtain ⟨hLF, hLS⟩ := Finset.mem_inter.mp hLFS
    -- `L' ∉ S`
    have hL'S : L' ∉ S := by
      intro hL'S
      apply hbnA
      rw [mem_fiberCut]
      exact ⟨L', Finset.mem_inter.mpr ⟨hL'F, hL'S⟩, hL'eq⟩
    -- the grid move pulls back to a BK adjacency
    have hl1 : l1dist (toGrid (localCoord x y L)) (toGrid (localCoord x y L')) = 1 := by
      have h := hbadj
      unfold L1Adj at h
      rw [← hLeq, ← hL'eq] at h
      exact h
    have hmove := (unitMove_iff_l1dist (iCoord x y L) (jCoord x y L)
        (iCoord x y L') (jCoord x y L')).mpr (by simpa only [localCoord] using hl1)
    have hsgn : signMarker x y L = signMarker x y L' := by
      rw [hsign L hLF, hsign L' hL'F]
    have hadj : BKAdj L L' :=
      (hF.2.2 L hLF L' hL'F).mpr (Or.inl ⟨hsgn, hmove⟩)
    refine ⟨(L, L'), ?_, ?_⟩
    · rw [mem_fiberBKBdy]
      exact ⟨⟨Finset.mem_inter.mpr ⟨hLF, hLS⟩,
        Finset.mem_sdiff.mpr ⟨hL'F, hL'S⟩⟩, hadj⟩
    · change (toGrid (localCoord x y L), toGrid (localCoord x y L')) = b
      rw [hLeq, hL'eq]

/-! ## §4. The initial per-fiber transport

Chaining §1–§3: a good fiber with a small per-fiber BK-boundary
(`def:edge-internal`) is transported, via the (S1.4) identity, to a
grid with a small grid boundary, and `lem:weak-grid` then supplies a
staircase approximation. -/

/-- **Per-fiber staircase, grid-boundary form.**  Intermediate form of
the transport: with the *grid* boundary bounded directly, `weak_grid`
applies on a good fiber. -/
theorem per_fiber_staircase_of_gridBdy {x y : α}
    {F : Finset (LinearExt α)} {S : Finset (LinearExt α)} {c ε : ℚ}
    (hc : 0 < c)
    (hF : IsGoodFiber x y F)
    (ht : 1 ≤ commonNbhdLength x y)
    (hmass : c * (commonNbhdLength x y : ℚ) ^ 2 ≤ ((fiberGrid x y F).card : ℚ))
    (hbdy : ((gridBdy (fiberGrid x y F) (fiberCut x y F S)).card : ℚ)
              ≤ ε * (commonNbhdLength x y : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircasePlus (fiberGrid x y F) M ∧
      ((symmDiff (fiberCut x y F S) M).card : ℚ)
        ≤ weakGridRate c ε * ((fiberGrid x y F).card : ℚ) :=
  lem_weak_grid (t := commonNbhdLength x y) hc
    (fiberGrid_isOrdConvex hF) (fiberGrid_box x y F) ht hmass
    (fiberCut_subset x y F S) hbdy

/-- **The initial per-fiber transport** (`step2.tex`
Proposition `prop:per-fiber`, part (ii), per-fiber core).

Let `F` be a good fiber for the rich pair `(x, y)` (Step 1
`IsGoodFiber`, `def:good-fiber`) with constant sign `ε₀`, and let
`S ⊆ LinearExt α` be a cut.  Assume the fiber has the shape hypothesis
`|D_{x,y}| ≥ c·t²` and the **per-fiber BK-boundary** of `S`
(`def:edge-internal`) is small, `|∂_BK(S ∩ F)| ≤ ε·t`.  Then the
coordinate image `A_{x,y} = π_{x,y}(S ∩ F)` is `δ(ε)·|D_{x,y}|`-close
to a monotone staircase region `M`, with `δ(ε) = weakGridRate c ε`.

This is the genuine per-fiber transport: it grounds the planar
`lem:weak-grid` on the Step 1 interface data, routing the global cut
`S` through the (S1.4) BK-boundary ↔ grid-boundary identity
(`fiberBKBdy_card_eq_gridBdy_card`). -/
theorem per_fiber_weak_grid {x y : α}
    {F : Finset (LinearExt α)} {S : Finset (LinearExt α)} {c ε : ℚ}
    {ε₀ : Bool}
    (hc : 0 < c)
    (hF : IsGoodFiber x y F)
    (hsign : ∀ L ∈ F, signMarker x y L = ε₀)
    (ht : 1 ≤ commonNbhdLength x y)
    (hmass : c * (commonNbhdLength x y : ℚ) ^ 2 ≤ ((fiberGrid x y F).card : ℚ))
    (hbdy : ((fiberBKBdy F S).card : ℚ)
              ≤ ε * (commonNbhdLength x y : ℚ)) :
    ∃ M : Finset (ℤ × ℤ), IsStaircasePlus (fiberGrid x y F) M ∧
      ((symmDiff (fiberCut x y F S) M).card : ℚ)
        ≤ weakGridRate c ε * ((fiberGrid x y F).card : ℚ) := by
  refine per_fiber_staircase_of_gridBdy hc hF ht hmass ?_
  have heq := fiberBKBdy_card_eq_gridBdy_card (S := S) hF hsign
  rw [← heq]
  exact hbdy

/-! ## §5. Non-vacuity — the port fires at `Antichain3`

Per the mg-0893 acceptance bar, the Step 2 port must instantiate
non-vacuously at a concrete width-3 non-chain poset, with no
Subsingleton-on-empty degeneracy. -/

/-- **A singleton is always a good fiber.**  All three clauses of
`IsGoodFiber` hold trivially on `{L}`: G1 and G3 because the only pair
is the diagonal `(L, L)` (and `BKAdj L L` is false), G2 because a
one-point coordinate image is order-convex.  Used to build a concrete
non-empty grounded witness. -/
theorem isGoodFiber_singleton (x y : α) (L : LinearExt α) :
    IsGoodFiber x y {L} := by
  refine ⟨?_, ?_, ?_⟩
  · intro L₁ h₁ L₂ h₂ _ _
    rw [Finset.mem_singleton] at h₁ h₂
    rw [h₁, h₂]
  · intro p hp q hq hpq1 hpq2 r hr1 hr2
    rw [Finset.image_singleton, Finset.mem_singleton] at hp hq ⊢
    subst hp; subst hq
    obtain ⟨ha, hb⟩ := hr1
    obtain ⟨hc', hd⟩ := hr2
    exact Prod.ext (by omega) (by omega)
  · intro L₁ h₁ L₂ h₂
    rw [Finset.mem_singleton] at h₁ h₂
    subst L₁; subst L₂
    constructor
    · intro hadj; exact absurd hadj (BKAdj.irrefl L)
    · rintro (⟨_, h⟩ | ⟨hf, _⟩)
      · omega
      · exact absurd hf (by cases signMarker x y L <;> simp)

/-- A 2×2 axis-aligned grid block, the concrete order-convex domain
used to exercise the planar `lem:weak-grid` non-vacuously. -/
def grid2x2 : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 0), (1, 1)}

theorem grid2x2_isOrdConvex : IsOrdConvex (grid2x2 : Set (ℤ × ℤ)) := by
  have h : (grid2x2 : Set (ℤ × ℤ)) = Set.Icc ((0, 0) : ℤ × ℤ) (1, 1) := by
    ext ⟨i, j⟩
    simp only [grid2x2, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_Icc, Prod.le_def, Prod.mk.injEq]
    omega
  rw [h]; exact IsOrdConvex.Icc _ _

/-- **Non-vacuity of the Step 2 weak-grid + per-fiber port** (the
mg-0893 acceptance witness).

* `lem_weak_grid` **fires on a genuine multi-cell grid**: the
  `2 × 2` block `grid2x2` with the corner cut `A = {(0,0)}` admits a
  staircase approximation — the planar weak-grid lemma is exercised
  non-trivially, not on an empty or one-point degenerate domain.
* The per-fiber transport **fires at the concrete width-3 non-chain
  poset `Antichain3`**: with the rich pair `(a0, a1)` (genuine
  common-neighbour-chain length `t = 1`) and a concrete non-empty good
  fiber, `per_fiber_weak_grid` delivers a per-fiber staircase
  approximation.

Neither branch is a Subsingleton-on-empty baseline: `Antichain3` is
genuinely width-3 and non-chain (`Antichain3.hasWidth`,
`Antichain3.not_isChainPoset`), and the fiber / grid domains are
non-empty. -/
theorem per_fiber_grounded_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    commonNbhdLength Antichain3.a0 Antichain3.a1 = 1 ∧
    -- the planar weak-grid lemma fires on a genuine 2×2 grid
    (∃ M : Finset (ℤ × ℤ), IsStaircasePlus grid2x2 M ∧
      ((symmDiff ({(0, 0)} : Finset (ℤ × ℤ)) M).card : ℚ)
        ≤ weakGridRate 1 2 * (grid2x2.card : ℚ)) ∧
    -- the per-fiber transport fires at a concrete good fiber on Antichain3
    (∃ L : LinearExt Antichain3, ∃ M : Finset (ℤ × ℤ),
      IsStaircasePlus
        (fiberGrid Antichain3.a0 Antichain3.a1 {L}) M ∧
      ((symmDiff (fiberCut Antichain3.a0 Antichain3.a1 {L} ∅) M).card : ℚ)
        ≤ weakGridRate 1 0 *
            ((fiberGrid Antichain3.a0 Antichain3.a1 {L}).card : ℚ)) := by
  classical
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset,
    Antichain3.commonNbhdLength_a0_a1, ?_, ?_⟩
  · -- planar weak-grid on the 2×2 grid, corner cut, `c = 1`, `ε = 2`, `t = 1`.
    have hcard : grid2x2.card = 4 := by decide
    have hbox : ∀ p ∈ grid2x2, 0 ≤ p.1 ∧ p.1 ≤ (1 : ℤ) ∧
        0 ≤ p.2 ∧ p.2 ≤ (1 : ℤ) := by decide
    have hAD : ({(0, 0)} : Finset (ℤ × ℤ)) ⊆ grid2x2 := by decide
    have hbdy : ((gridBdy grid2x2 ({(0, 0)} : Finset (ℤ × ℤ))).card : ℚ)
        ≤ 2 * (1 : ℚ) := by
      have : (gridBdy grid2x2 ({(0, 0)} : Finset (ℤ × ℤ))).card = 2 := by decide
      rw [this]; norm_num
    have hmass : (1 : ℚ) * (1 : ℚ) ^ 2 ≤ (grid2x2.card : ℚ) := by
      rw [hcard]; norm_num
    exact lem_weak_grid (t := 1) (by norm_num) grid2x2_isOrdConvex
      hbox (by norm_num) hmass hAD hbdy
  · -- per-fiber transport at a singleton good fiber on `Antichain3`.
    obtain ⟨L⟩ : Nonempty (LinearExt Antichain3) := by
      have h := Antichain3.two_le_numLinExt
      unfold numLinExt at h
      exact Fintype.card_pos_iff.mp (by omega)
    refine ⟨L, ?_⟩
    have ht : 1 ≤ commonNbhdLength Antichain3.a0 Antichain3.a1 := by
      rw [Antichain3.commonNbhdLength_a0_a1]
    have hgood : IsGoodFiber Antichain3.a0 Antichain3.a1 {L} :=
      isGoodFiber_singleton _ _ L
    have hsign : ∀ L' ∈ ({L} : Finset (LinearExt Antichain3)),
        signMarker Antichain3.a0 Antichain3.a1 L'
          = signMarker Antichain3.a0 Antichain3.a1 L := by
      intro L' hL'
      rw [Finset.mem_singleton] at hL'
      rw [hL']
    have hcardF : (fiberGrid Antichain3.a0 Antichain3.a1 {L}).card = 1 := by
      rw [fiberGrid_card hgood hsign]
      exact Finset.card_singleton L
    have hmass : (1 : ℚ) *
        (commonNbhdLength Antichain3.a0 Antichain3.a1 : ℚ) ^ 2
          ≤ ((fiberGrid Antichain3.a0 Antichain3.a1 {L}).card : ℚ) := by
      rw [Antichain3.commonNbhdLength_a0_a1, hcardF]
      norm_num
    have hbdy : ((fiberBKBdy {L} ∅).card : ℚ)
        ≤ (0 : ℚ) * (commonNbhdLength Antichain3.a0 Antichain3.a1 : ℚ) := by
      have hempty : fiberBKBdy ({L} : Finset (LinearExt Antichain3)) ∅ = ∅ := by
        unfold fiberBKBdy
        simp
      rw [hempty]
      simp
    exact per_fiber_weak_grid (ε₀ := signMarker Antichain3.a0 Antichain3.a1 L)
      (by norm_num) hgood hsign ht hmass hbdy

end PerFiberGrounded
end Step2
end OneThird
