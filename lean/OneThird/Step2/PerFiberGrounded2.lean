/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step2.PerFiberGrounded
import OneThird.Step2.FiberAvg

/-!
# Step 2 — per-fiber staircase approximation and density bookkeeping (part 2)

This file is **part 2 of the Step 2 Lean port** of the Option A' FULL
REFACTOR (`docs/OneThird-Option-A-FULL-REFACTOR-scoping.md`, mg-d8c7
§2.1 Piece 1, Wave-2; work item mg-0868, ticket OneThird-S2-B).  It
completes Step 2 by porting `step2.tex` `prop:per-fiber` (the
per-fiber staircase approximation, quantitative form) and `thm:step2`
(the Step 2 conclusion exported to Steps 3–6), built on top of the
S2-A deliverable `OneThird.Step2.PerFiberGrounded`.

S2-A (`PerFiberGrounded.lean`, mg-0893) delivered `lem:weak-grid` as a
Step 2 statement and the **initial per-fiber transport**
`per_fiber_weak_grid` — the per-fiber *core* of `prop:per-fiber` (ii)
applied to a *single* good fiber.  This file delivers the remaining
two halves:

1. **The global double-counting** (`step2.tex` `lem:fiber-avg` /
   `cor:fiber-avg-tail`), now **grounded on the BK graph**: the
   abstract double-counting lives in `Step2/FiberAvg.lean`
   (`double_counting_bounded_multiplicity`); here it is instantiated
   at the concrete directed BK-boundary `globalBKBdy S` of a cut
   `S ⊆ LinearExt α`, against a `RichFamily` of good fibers carrying
   the Step 1 (S1.6) bounded-multiplicity constant `K`.

2. **The `prop:per-fiber` assembly** — combining the bad-fiber mass
   bound (part (i)) with the per-fiber staircase across the whole
   fiber family (part (ii)) — and **`thm:step2`**, the Step 2
   conclusion stated with the explicit `ε₂` bookkeeping that the
   downstream Step 6 (`step6.tex` `lem:most-good`) consumes.

## The `ε₂` bookkeeping (downstream signature match)

Per mg-6ab8 §2.2 and the mg-0868 ticket, the Step 2 staircase error
constant `ε₂ = ε₂(γ)` must enter **quantitatively** into the Step 2
output, with the exact shape Step 6 consumes.  The per-fiber rate is
named `fiberStaircaseRate c η |fib| t`: it is the weak-grid stability
rate `δ` (`weakGridRate`, S2-A) evaluated at the boundary budget
`η·|fib_{x,y}|/t_{x,y}` of a good fiber.  `thm_step2` takes a uniform
upper bound `ε₂` on these per-fiber rates as an explicit parameter and
concludes the uniform per-fiber error `|E_{x,y}| ≤ ε₂·|fib_{x,y}|`;
`fiberStaircaseRate_le_of_le` records the `ε₂ → 0` qualitative content
(`step2.tex` `lem:weak-grid`'s `δ(ε)→0`).

## Main results

* `globalBKBdy` — the directed BK-boundary of a cut `S` (one directed
  pair per undirected boundary edge, `step2.tex` `def:edge-internal`
  ambient form).
* `fiberBKBdy_eq_filter_globalBKBdy` — the per-fiber boundary is the
  restriction of the global boundary to edges internal to the fiber.
* `RichFamily` — a finite family of rich good fibers with constant
  per-fiber sign (`step2.tex` `prop:per-fiber`'s `𝓡`).
* `lem_fiber_avg` / `lem_fiber_avg_conductance` — `step2.tex`
  `lem:fiber-avg` grounded: under bounded BK-edge multiplicity, the
  total per-fiber boundary count is `≤ K·|∂_BK S| ≤ K·κ·|S|`.
* `cor_fiber_avg_tail` — `step2.tex` `cor:fiber-avg-tail` grounded:
  the Markov tail bound on the mass of bad fibers.
* `fiberStaircaseRate` — the explicit per-fiber `ε₂` constant.
* `prop_per_fiber` — `step2.tex` `prop:per-fiber`: bad-fiber mass
  bound (i) plus the per-fiber staircase across the family (ii).
* `thm_step2` — `step2.tex` `thm:step2`: the Step 2 conclusion with
  the uniform `ε₂` bookkeeping.
* `step2_good_mass_fraction` — the `(1-α)`-mass-fraction corollary
  (`prop:per-fiber`'s "consequently" clause / the `1-o(1)` of
  `thm:step2`).
* `per_fiber_grounded2_nonvacuous` — the mg-0868 acceptance witness:
  `thm_step2` and `lem_fiber_avg` fire non-vacuously at the concrete
  width-3 non-chain poset `Antichain3`.
-/

namespace OneThird
namespace Step2
namespace PerFiberGrounded

open Finset OneThird.Mathlib.Grid2D OneThird.Step2.WeakGrid

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ## §1. The global directed BK-boundary of a cut

`step2.tex` `def:edge-internal` works with the *undirected* BK-boundary
`∂_BK S` of a cut `S ⊆ lext(P)`.  The S2-A per-fiber boundary
`fiberBKBdy` is presented in *directed* form — each undirected
boundary edge contributes one ordered pair, from its `S` endpoint to
its `Sᶜ` endpoint.  We match that convention for the ambient
boundary: `globalBKBdy S` is the set of directed BK-edges `(L, L')`
with `L ∈ S`, `L' ∉ S`.  This is a cardinality-faithful encoding of
`∂_BK S` (one directed pair per undirected boundary edge). -/

/-- The **global directed BK-boundary** of a cut `S`: the ordered
BK-edges `(L, L')` with `L ∈ S` and `L' ∉ S`.  Cardinality-equal to
the undirected `∂_BK S` of `step2.tex` `def:edge-internal`. -/
noncomputable def globalBKBdy (S : Finset (LinearExt α)) :
    Finset (LinearExt α × LinearExt α) := by
  classical
  exact (S ×ˢ Sᶜ).filter (fun p => BKAdj p.1 p.2)

theorem mem_globalBKBdy {S : Finset (LinearExt α)}
    {p : LinearExt α × LinearExt α} :
    p ∈ globalBKBdy S ↔ (p.1 ∈ S ∧ p.2 ∉ S) ∧ BKAdj p.1 p.2 := by
  classical
  unfold globalBKBdy
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_compl]

@[simp] theorem globalBKBdy_empty :
    globalBKBdy (∅ : Finset (LinearExt α)) = ∅ := by
  classical
  ext p
  simp [mem_globalBKBdy]

/-! ## §2. Per-fiber boundary as a restriction of the global boundary

The bridge from the S2-A per-fiber boundary `fiberBKBdy F S` to the
ambient `globalBKBdy S`: a directed BK-edge is in `fiberBKBdy F S`
exactly when it is in `globalBKBdy S` *and* both endpoints lie in the
fiber `F` (`step2.tex` `def:edge-internal`, "internal to a fiber"). -/

/-- **`fiberBKBdy` is the fiber-internal restriction of `globalBKBdy`.**
A directed BK-boundary edge of `S` is internal to the fiber `F` iff
both endpoints lie in `F`. -/
theorem fiberBKBdy_eq_filter_globalBKBdy (F S : Finset (LinearExt α)) :
    fiberBKBdy F S
      = (globalBKBdy S).filter (fun p => p.1 ∈ F ∧ p.2 ∈ F) := by
  classical
  ext p
  rw [Finset.mem_filter, mem_fiberBKBdy, mem_globalBKBdy]
  constructor
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    obtain ⟨h1F, h1S⟩ := Finset.mem_inter.mp h1
    obtain ⟨h2F, h2S⟩ := Finset.mem_sdiff.mp h2
    exact ⟨⟨⟨h1S, h2S⟩, hadj⟩, h1F, h2F⟩
  · rintro ⟨⟨⟨h1S, h2S⟩, hadj⟩, h1F, h2F⟩
    exact ⟨⟨Finset.mem_inter.mpr ⟨h1F, h1S⟩,
      Finset.mem_sdiff.mpr ⟨h2F, h2S⟩⟩, hadj⟩

/-- Every per-fiber BK-boundary edge is a global BK-boundary edge —
the observation `step2.tex` `lem:fiber-avg`'s proof opens with
("the latter condition depends only on `S` and `e`, not on the
fiber"). -/
theorem fiberBKBdy_subset_globalBKBdy (F S : Finset (LinearExt α)) :
    fiberBKBdy F S ⊆ globalBKBdy S := by
  rw [fiberBKBdy_eq_filter_globalBKBdy]
  exact Finset.filter_subset _ _

/-! ## §3. The rich-fiber family and `lem:fiber-avg`

A **rich-fiber family** packages the data `step2.tex` `prop:per-fiber`
calls `𝓡`: a finite collection of rich incomparable pairs `(x, y)`,
each carrying a good fiber `fib_{x,y}` (Step 1 `IsGoodFiber`) of
constant sign.  `lem:fiber-avg` is then the double-counting bound on
the per-fiber boundaries, instantiating the abstract
`FiberAvg.double_counting_bounded_multiplicity` at the concrete BK
boundary. -/

/-- A **rich-fiber family** (`step2.tex` `prop:per-fiber`'s `𝓡`): a
finite `Finset` of rich pairs, each assigned a good fiber of constant
sign. -/
structure RichFamily (α : Type*) [PartialOrder α] [Fintype α]
    [DecidableEq α] where
  /-- The index set: a finite collection of rich incomparable pairs. -/
  carrier : Finset (α × α)
  /-- The fiber `fib_{x,y}` assigned to each rich pair. -/
  fib : α × α → Finset (LinearExt α)
  /-- The constant sign `ε₀` carried by the fiber. -/
  sgn : α × α → Bool
  /-- Each fiber in the family is a good fiber (Step 1 `IsGoodFiber`). -/
  good : ∀ r ∈ carrier, IsGoodFiber r.1 r.2 (fib r)
  /-- The sign is constant across each fiber. -/
  signConst : ∀ r ∈ carrier, ∀ L ∈ fib r, signMarker r.1 r.2 L = sgn r

@[simp] theorem RichFamily.carrier_def (Fam : RichFamily α) :
    Fam.carrier = Fam.carrier := rfl

/-- The relation "the BK-edge `e` is internal to the fiber of `r`"
(`step2.tex` `def:edge-internal`): both endpoints lie in `fib r`. -/
def edgeInternal (Fam : RichFamily α) (r : α × α)
    (e : LinearExt α × LinearExt α) : Prop :=
  e.1 ∈ Fam.fib r ∧ e.2 ∈ Fam.fib r

instance edgeInternal_decidable (Fam : RichFamily α) :
    DecidableRel (edgeInternal Fam) := fun r e =>
  inferInstanceAs (Decidable (e.1 ∈ Fam.fib r ∧ e.2 ∈ Fam.fib r))

/-- The abstract `FiberAvg.internalCount` of the global boundary, with
`edgeInternal` as the incidence relation, is exactly the per-fiber
boundary count. -/
theorem internalCount_eq (Fam : RichFamily α) (S : Finset (LinearExt α))
    (r : α × α) :
    FiberAvg.internalCount (globalBKBdy S) (edgeInternal Fam) r
      = (fiberBKBdy (Fam.fib r) S).card := by
  rw [fiberBKBdy_eq_filter_globalBKBdy]
  unfold FiberAvg.internalCount
  congr 1

/-- **`step2.tex` `lem:fiber-avg` (grounded form).**  Under the
bounded BK-edge multiplicity hypothesis — every directed boundary edge
is internal to at most `K` fibers of the family — the sum of the
per-fiber BK-boundary counts over the family is at most
`K·|∂_BK S|`.  This is the double-counting `eq:fiber-avg` of
`step2.tex`, grounded at the concrete BK boundary. -/
theorem lem_fiber_avg (Fam : RichFamily α) (S : Finset (LinearExt α))
    {K : ℕ}
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K) :
    ∑ r ∈ Fam.carrier, (fiberBKBdy (Fam.fib r) S).card
      ≤ K * (globalBKBdy S).card := by
  have h := FiberAvg.double_counting_bounded_multiplicity
    Fam.carrier (globalBKBdy S) (edgeInternal Fam) hmult
  simp only [internalCount_eq] at h
  exact h

/-- **`lem:fiber-avg` with the global conductance bound folded in.**
If additionally `|∂_BK S| ≤ κ·|S|` (the low-conductance hypothesis of
`step2.tex` `prop:per-fiber`), the total per-fiber boundary is bounded
by `K·κ·|S|`. -/
theorem lem_fiber_avg_conductance (Fam : RichFamily α)
    (S : Finset (LinearExt α)) {K : ℕ} {κ : ℚ}
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ)) :
    (∑ r ∈ Fam.carrier, ((fiberBKBdy (Fam.fib r) S).card : ℚ))
      ≤ (K : ℚ) * κ * (S.card : ℚ) := by
  have h := lem_fiber_avg Fam S hmult
  have hcast : (∑ r ∈ Fam.carrier, ((fiberBKBdy (Fam.fib r) S).card : ℚ))
      = (((∑ r ∈ Fam.carrier, (fiberBKBdy (Fam.fib r) S).card : ℕ)) : ℚ) := by
    push_cast; ring
  calc (∑ r ∈ Fam.carrier, ((fiberBKBdy (Fam.fib r) S).card : ℚ))
      = (((∑ r ∈ Fam.carrier, (fiberBKBdy (Fam.fib r) S).card : ℕ)) : ℚ) := hcast
    _ ≤ ((K * (globalBKBdy S).card : ℕ) : ℚ) := by exact_mod_cast h
    _ = (K : ℚ) * ((globalBKBdy S).card : ℚ) := by push_cast; ring
    _ ≤ (K : ℚ) * (κ * (S.card : ℚ)) :=
        mul_le_mul_of_nonneg_left hcond (by positivity)
    _ = (K : ℚ) * κ * (S.card : ℚ) := by ring

/-! ## §4. `cor:fiber-avg-tail` — the bad-fiber mass bound

A fiber is **bad** if its per-fiber BK-boundary exceeds the
density threshold `η·|fib_{x,y}|`, **good** otherwise.  `step2.tex`
`cor:fiber-avg-tail` is the Markov-type tail: the bad fibers carry
total mass at most `K·κ·|S|/η`. -/

/-- The **bad fibers** of the family at density threshold `η`: those
whose per-fiber BK-boundary exceeds `η·|fib_{x,y}|`. -/
noncomputable def badFibers (Fam : RichFamily α) (S : Finset (LinearExt α))
    (η : ℚ) : Finset (α × α) :=
  Fam.carrier.filter
    (fun r => η * ((Fam.fib r).card : ℚ)
      < ((fiberBKBdy (Fam.fib r) S).card : ℚ))

/-- The **good fibers** of the family at density threshold `η`
(`step2.tex` `prop:per-fiber`'s `𝓖`): those whose per-fiber
BK-boundary is at most `η·|fib_{x,y}|`. -/
noncomputable def goodFibers (Fam : RichFamily α) (S : Finset (LinearExt α))
    (η : ℚ) : Finset (α × α) :=
  Fam.carrier.filter
    (fun r => ((fiberBKBdy (Fam.fib r) S).card : ℚ)
      ≤ η * ((Fam.fib r).card : ℚ))

theorem mem_badFibers {Fam : RichFamily α} {S : Finset (LinearExt α)}
    {η : ℚ} {r : α × α} :
    r ∈ badFibers Fam S η ↔
      r ∈ Fam.carrier ∧
      η * ((Fam.fib r).card : ℚ)
        < ((fiberBKBdy (Fam.fib r) S).card : ℚ) := by
  unfold badFibers; rw [Finset.mem_filter]

theorem mem_goodFibers {Fam : RichFamily α} {S : Finset (LinearExt α)}
    {η : ℚ} {r : α × α} :
    r ∈ goodFibers Fam S η ↔
      r ∈ Fam.carrier ∧
      ((fiberBKBdy (Fam.fib r) S).card : ℚ)
        ≤ η * ((Fam.fib r).card : ℚ) := by
  unfold goodFibers; rw [Finset.mem_filter]

theorem badFibers_subset (Fam : RichFamily α) (S : Finset (LinearExt α))
    (η : ℚ) : badFibers Fam S η ⊆ Fam.carrier := by
  unfold badFibers; exact Finset.filter_subset _ _

theorem goodFibers_subset (Fam : RichFamily α) (S : Finset (LinearExt α))
    (η : ℚ) : goodFibers Fam S η ⊆ Fam.carrier := by
  unfold goodFibers; exact Finset.filter_subset _ _

/-- The good and bad fibers partition the family: `𝓖 = 𝓡 ∖ 𝓡^bad`. -/
theorem goodFibers_eq_sdiff (Fam : RichFamily α)
    (S : Finset (LinearExt α)) (η : ℚ) :
    goodFibers Fam S η = Fam.carrier \ badFibers Fam S η := by
  ext r
  rw [Finset.mem_sdiff, mem_goodFibers, mem_badFibers]
  constructor
  · rintro ⟨hc, hle⟩
    exact ⟨hc, fun h => absurd hle (not_le.mpr h.2)⟩
  · rintro ⟨hc, hnb⟩
    refine ⟨hc, ?_⟩
    by_contra hlt
    exact hnb ⟨hc, not_le.mp hlt⟩

/-- **`step2.tex` `cor:fiber-avg-tail` (grounded form).**  The
mass-weighted Markov tail: scaling the total mass of the bad fibers by
the density threshold `η` is bounded by `K·κ·|S|`. -/
theorem cor_fiber_avg_tail (Fam : RichFamily α)
    (S : Finset (LinearExt α)) {K : ℕ} {κ η : ℚ}
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ)) :
    η * (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
      ≤ (K : ℚ) * κ * (S.card : ℚ) := by
  have hstep1 : η * (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
      ≤ ∑ r ∈ badFibers Fam S η,
          ((fiberBKBdy (Fam.fib r) S).card : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    exact le_of_lt (mem_badFibers.mp hr).2
  have hstep2 : ∑ r ∈ badFibers Fam S η,
        ((fiberBKBdy (Fam.fib r) S).card : ℚ)
      ≤ ∑ r ∈ Fam.carrier, ((fiberBKBdy (Fam.fib r) S).card : ℚ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (badFibers_subset Fam S η)
    intro r _ _; positivity
  exact hstep1.trans
    (hstep2.trans (lem_fiber_avg_conductance Fam S hmult hcond))

/-! ## §5. The per-fiber staircase rate `ε₂`

`step2.tex` `prop:per-fiber` (ii) states the per-fiber staircase error
as `δ(ε_{x,y})·|fib_{x,y}|` with `ε_{x,y} = η·t_{x,y}` and
`δ = weakGridRate` (S2-A).  We name the grounded rate
`fiberStaircaseRate c η |fib| t`: the weak-grid rate evaluated at the
boundary budget `η·|fib|/t` of a good fiber.  (A good fiber has
`|∂_BK(S∩fib)| ≤ η·|fib|`, so the boundary-budget parameter `ε` of
`weak_grid`, defined by `|∂| ≤ ε·t`, can be taken to be exactly
`η·|fib|/t`; the paper's coarser `ε_{x,y} = η·t` follows from
`|fib| ≤ t²`.)  This is the explicit `ε₂ = ε₂(γ)` constant the
downstream Step 6 (`step6.tex` `lem:most-good`) consumes. -/

/-- The **per-fiber Step 2 staircase rate** `ε₂(x,y)`: the weak-grid
stability rate `δ` (`weakGridRate`) evaluated at the boundary budget
`η·|fib_{x,y}|/t_{x,y}` of a good fiber.  This is the explicit
`ε₂ = ε₂(γ)` quantity of `step2.tex` `prop:per-fiber` (ii). -/
def fiberStaircaseRate (c η : ℚ) (cardF t : ℕ) : ℚ :=
  weakGridRate c (η * (cardF : ℚ) / (t : ℚ))

/-- The per-fiber staircase rate is non-negative. -/
theorem fiberStaircaseRate_nonneg {c η : ℚ} {cardF t : ℕ}
    (hc : 0 < c) (hη : 0 ≤ η) :
    0 ≤ fiberStaircaseRate c η cardF t :=
  weakGridRate_nonneg hc (by positivity)

/-- **`ε₂ → 0` as `η → 0`** (quantitative form).  For every target
`ρ > 0`, taking the density threshold `η` small enough that
`η·|fib|/t ≤ ρ·c/4` forces `fiberStaircaseRate c η |fib| t ≤ ρ`.
This is the `δ(ε) → 0` qualitative content of `step2.tex`
`lem:weak-grid` propagated to the per-fiber rate — the bookkeeping
fact Step 6 relies on to drive `ε₂` below its dichotomy threshold. -/
theorem fiberStaircaseRate_le_of_le {c η ρ : ℚ} {cardF t : ℕ}
    (hc : 0 < c) (h : η * (cardF : ℚ) / (t : ℚ) ≤ ρ * c / 4) :
    fiberStaircaseRate c η cardF t ≤ ρ :=
  weakGridRate_le_of_le hc h

/-! ## §6. `prop:per-fiber` — the per-fiber staircase approximation

`step2.tex` `prop:per-fiber` has two parts: (i) the bad-fiber mass
bound (a restatement of `cor:fiber-avg-tail`), and (ii) the per-fiber
staircase on every good fiber.  Part (ii) is the family-level
application of the S2-A per-fiber transport `per_fiber_weak_grid`. -/

/-- **`prop:per-fiber` part (i): mass of bad fibers.**  The total mass
of the bad fibers is at most `K·κ·|S|/η`. -/
theorem prop_per_fiber_bad_mass (Fam : RichFamily α)
    (S : Finset (LinearExt α)) {K : ℕ} {κ η : ℚ} (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ)) :
    (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
      ≤ (K : ℚ) * κ * (S.card : ℚ) / η := by
  rw [le_div_iff₀ hη]
  have h := cor_fiber_avg_tail Fam S (η := η) hmult hcond
  linarith

/-- **`prop:per-fiber` part (ii): the per-fiber staircase on a good
fiber.**  A good fiber `(x, y) ∈ 𝓖` — one whose per-fiber BK-boundary
is at most `η·|fib_{x,y}|` — admits a monotone staircase region
`M_{x,y}` with symmetric-difference error at most
`fiberStaircaseRate c η |fib| t · |D_{x,y}|`.  This is the
family-level instance of the S2-A per-fiber transport
`per_fiber_weak_grid`: the boundary-budget parameter is `η·|fib|/t`,
so the staircase rate is exactly `fiberStaircaseRate`. -/
theorem prop_per_fiber_staircase (Fam : RichFamily α)
    (S : Finset (LinearExt α)) {c η : ℚ} {r : α × α} (hc : 0 < c)
    (hr : r ∈ goodFibers Fam S η)
    (ht : 1 ≤ commonNbhdLength r.1 r.2)
    (hmass : c * (commonNbhdLength r.1 r.2 : ℚ) ^ 2
              ≤ ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ)) :
    ∃ M : Finset (ℤ × ℤ),
      IsStaircasePlus (fiberGrid r.1 r.2 (Fam.fib r)) M ∧
      ((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) M).card : ℚ)
        ≤ fiberStaircaseRate c η (Fam.fib r).card
            (commonNbhdLength r.1 r.2)
          * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ) := by
  obtain ⟨hrc, hrgood⟩ := mem_goodFibers.mp hr
  have htℚ : (0 : ℚ) < (commonNbhdLength r.1 r.2 : ℚ) := by
    have h1 : (1 : ℚ) ≤ (commonNbhdLength r.1 r.2 : ℚ) := by
      exact_mod_cast ht
    linarith
  have hbdy : ((fiberBKBdy (Fam.fib r) S).card : ℚ)
      ≤ (η * ((Fam.fib r).card : ℚ) / (commonNbhdLength r.1 r.2 : ℚ))
          * (commonNbhdLength r.1 r.2 : ℚ) := by
    rw [div_mul_cancel₀ _ htℚ.ne']
    exact hrgood
  unfold fiberStaircaseRate
  exact per_fiber_weak_grid (ε₀ := Fam.sgn r) hc (Fam.good r hrc)
    (Fam.signConst r hrc) ht hmass hbdy

/-- **`step2.tex` `prop:per-fiber` (per-fiber staircase
approximation; quantitative form).**  Combines part (i) — the
bad-fiber mass bound — with part (ii) — the per-fiber staircase across
the whole good-fiber family. -/
theorem prop_per_fiber (Fam : RichFamily α) (S : Finset (LinearExt α))
    {c : ℚ} {K : ℕ} {κ η : ℚ} (hc : 0 < c) (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ))
    (ht : ∀ r ∈ goodFibers Fam S η, 1 ≤ commonNbhdLength r.1 r.2)
    (hmass : ∀ r ∈ goodFibers Fam S η,
      c * (commonNbhdLength r.1 r.2 : ℚ) ^ 2
        ≤ ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ)) :
    -- (i) mass of bad fibers
    (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
        ≤ (K : ℚ) * κ * (S.card : ℚ) / η ∧
    -- (ii) per-fiber staircase on every good fiber
    (∀ r ∈ goodFibers Fam S η, ∃ M : Finset (ℤ × ℤ),
      IsStaircasePlus (fiberGrid r.1 r.2 (Fam.fib r)) M ∧
      ((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) M).card : ℚ)
        ≤ fiberStaircaseRate c η (Fam.fib r).card
            (commonNbhdLength r.1 r.2)
          * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ)) := by
  refine ⟨prop_per_fiber_bad_mass Fam S hη hmult hcond, ?_⟩
  intro r hr
  exact prop_per_fiber_staircase Fam S hc hr (ht r hr) (hmass r hr)

/-! ## §7. `thm:step2` — the Step 2 conclusion

`step2.tex` `thm:step2` is the output exported to Steps 3–6.  We state
it with the **explicit `ε₂` bookkeeping** the downstream Step 6
(`step6.tex` `lem:most-good`) consumes: `ε₂` is supplied as a uniform
upper bound on the per-fiber staircase rates `fiberStaircaseRate`, and
the conclusion records the uniform per-fiber error
`|E_{x,y}| ≤ ε₂·|fib_{x,y}|`. -/

/-- **`step2.tex` `thm:step2` (Step 2 conclusion).**  Given a
rich-fiber family with bounded BK-edge multiplicity `K`, a cut `S`
with global conductance `|∂_BK S| ≤ κ·|S|`, the Step 1 (S1.1) density
hypothesis `|D_{x,y}| ≥ c·t²` on good fibers, and a uniform staircase
rate `ε₂` dominating every per-fiber `fiberStaircaseRate`:

* **(i)** the bad fibers carry mass at most `K·κ·|S|/η`;
* **(ii)** every good fiber `(x, y)` admits a monotone staircase
  `M_{x,y}` with uniform per-fiber error
  `|A_{x,y} △ M_{x,y}| ≤ ε₂·|D_{x,y}|`.

The constant `ε₂` enters the statement quantitatively (mg-0868
downstream signature match): `fiberStaircaseRate_le_of_le` records
that `ε₂` can be driven to `0` by shrinking the density threshold
`η`. -/
theorem thm_step2 (Fam : RichFamily α) (S : Finset (LinearExt α))
    {c : ℚ} {K : ℕ} {κ η ε₂ : ℚ} (hc : 0 < c) (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ))
    (ht : ∀ r ∈ goodFibers Fam S η, 1 ≤ commonNbhdLength r.1 r.2)
    (hmass : ∀ r ∈ goodFibers Fam S η,
      c * (commonNbhdLength r.1 r.2 : ℚ) ^ 2
        ≤ ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ))
    (huniform : ∀ r ∈ goodFibers Fam S η,
      fiberStaircaseRate c η (Fam.fib r).card
          (commonNbhdLength r.1 r.2) ≤ ε₂) :
    -- (i) mass of bad fibers
    (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
        ≤ (K : ℚ) * κ * (S.card : ℚ) / η ∧
    -- (ii) uniform per-fiber staircase with error rate ε₂
    (∀ r ∈ goodFibers Fam S η, ∃ M : Finset (ℤ × ℤ),
      IsStaircasePlus (fiberGrid r.1 r.2 (Fam.fib r)) M ∧
      ((symmDiff (fiberCut r.1 r.2 (Fam.fib r) S) M).card : ℚ)
        ≤ ε₂ * ((fiberGrid r.1 r.2 (Fam.fib r)).card : ℚ)) := by
  refine ⟨prop_per_fiber_bad_mass Fam S hη hmult hcond, ?_⟩
  intro r hr
  obtain ⟨M, hM, hMerr⟩ :=
    prop_per_fiber_staircase Fam S hc hr (ht r hr) (hmass r hr)
  refine ⟨M, hM, hMerr.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (huniform r hr) (by positivity)

/-- **The `(1-α)`-mass-fraction corollary** (`step2.tex`
`prop:per-fiber`'s "consequently" clause, the `1-o(1)` quantifier of
`thm:step2`).  If the conductance budget satisfies
`K·κ·|S| ≤ α·η·W` for `W` the total fiber mass and `α ∈ (0,1)`, then
the good fibers carry mass-fraction at least `1-α`. -/
theorem step2_good_mass_fraction (Fam : RichFamily α)
    (S : Finset (LinearExt α)) {K : ℕ} {κ η a : ℚ} (hη : 0 < η)
    (hmult : ∀ e ∈ globalBKBdy S,
      (Fam.carrier.filter (fun r => edgeInternal Fam r e)).card ≤ K)
    (hcond : ((globalBKBdy S).card : ℚ) ≤ κ * (S.card : ℚ))
    (hsmall : (K : ℚ) * κ * (S.card : ℚ)
        ≤ a * (η * (∑ r ∈ Fam.carrier, ((Fam.fib r).card : ℚ)))) :
    (1 - a) * (∑ r ∈ Fam.carrier, ((Fam.fib r).card : ℚ))
      ≤ ∑ r ∈ goodFibers Fam S η, ((Fam.fib r).card : ℚ) := by
  set W := ∑ r ∈ Fam.carrier, ((Fam.fib r).card : ℚ) with hW
  have hsplit : ∑ r ∈ goodFibers Fam S η, ((Fam.fib r).card : ℚ)
      + ∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ) = W := by
    rw [goodFibers_eq_sdiff, hW]
    exact Finset.sum_sdiff (badFibers_subset Fam S η)
  have hbad : ∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ)
      ≤ a * W := by
    have h1 := cor_fiber_avg_tail Fam S hmult hcond (η := η)
    have h2 : η * (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
        ≤ η * (a * W) := by
      calc η * (∑ r ∈ badFibers Fam S η, ((Fam.fib r).card : ℚ))
          ≤ (K : ℚ) * κ * (S.card : ℚ) := h1
        _ ≤ a * (η * W) := hsmall
        _ = η * (a * W) := by ring
    exact le_of_mul_le_mul_left h2 hη
  linarith [hsplit, hbad]

/-! ## §8. Non-vacuity — the assembly fires at `Antichain3`

Per the mg-0868 acceptance bar, the Step 2 assembly must instantiate
non-vacuously at a concrete width-3 non-chain poset, with no
Subsingleton-on-empty degeneracy. -/

/-- A concrete one-pair rich-fiber family on `Antichain3`, carried by
the genuine rich pair `(a0, a1)` (common-neighbour-chain length
`t = 1`) with a singleton good fiber.  Singletons are good fibers
(`isGoodFiber_singleton`, S2-A) of constant sign. -/
noncomputable def antichain3Family (L : LinearExt Antichain3) :
    RichFamily Antichain3 where
  carrier := {(Antichain3.a0, Antichain3.a1)}
  fib := fun _ => {L}
  sgn := fun _ => signMarker Antichain3.a0 Antichain3.a1 L
  good := by
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst hr
    exact isGoodFiber_singleton Antichain3.a0 Antichain3.a1 L
  signConst := by
    intro r hr L' hL'
    rw [Finset.mem_singleton] at hr
    subst hr
    rw [Finset.mem_singleton] at hL'
    subst hL'
    rfl

@[simp] theorem antichain3Family_carrier (L : LinearExt Antichain3) :
    (antichain3Family L).carrier
      = {(Antichain3.a0, Antichain3.a1)} := rfl

@[simp] theorem antichain3Family_fib (L : LinearExt Antichain3)
    (r : Antichain3 × Antichain3) :
    (antichain3Family L).fib r = {L} := rfl

/-- The per-fiber boundary of any cut inside a singleton fiber is
empty: a singleton fiber carries no internal BK-edge. -/
theorem fiberBKBdy_singleton_empty (L : LinearExt Antichain3)
    (S : Finset (LinearExt Antichain3)) :
    fiberBKBdy ({L} : Finset (LinearExt Antichain3)) S = ∅ := by
  classical
  unfold fiberBKBdy
  rw [Finset.filter_eq_empty_iff]
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have h1 := (Finset.mem_inter.mp hp1).1
  have h2 := (Finset.mem_sdiff.mp hp2).1
  rw [Finset.mem_singleton] at h1 h2
  rw [show p.2 = p.1 from h2.trans h1.symm]
  exact BKAdj.irrefl p.1

/-- **Non-vacuity of the Step 2 assembly** (the mg-0868 acceptance
witness).

At the concrete width-3 non-chain poset `Antichain3`, with the
genuine rich pair `(a0, a1)`, a singleton good fiber, and the empty
cut:

* the rich-fiber family is genuinely non-empty;
* `lem_fiber_avg` (the grounded double-counting) fires;
* the good-fiber set `𝓖` is genuinely non-empty (contains `(a0, a1)`);
* `thm_step2` fires — both the bad-fiber mass bound (i) and a genuine
  per-fiber staircase (ii) on the good fiber, with the explicit
  `ε₂ = fiberStaircaseRate 1 1 1 1` bookkeeping.

`Antichain3` is genuinely width-3 and non-chain
(`Antichain3.hasWidth`, `Antichain3.not_isChainPoset`); the family,
fiber, and good-fiber set are all non-empty — no Subsingleton-on-empty
baseline. -/
theorem per_fiber_grounded2_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    ∃ L : LinearExt Antichain3,
      -- the rich-fiber family is genuinely non-empty
      (antichain3Family L).carrier.Nonempty ∧
      -- lem:fiber-avg (grounded double-counting) fires
      (∑ r ∈ (antichain3Family L).carrier,
          (fiberBKBdy ((antichain3Family L).fib r)
            (∅ : Finset (LinearExt Antichain3))).card)
        ≤ 1 * (globalBKBdy (∅ : Finset (LinearExt Antichain3))).card ∧
      -- the good-fiber set 𝓖 is genuinely non-empty
      (Antichain3.a0, Antichain3.a1)
        ∈ goodFibers (antichain3Family L) ∅ 1 ∧
      -- thm:step2 (i): bad-fiber mass bound
      ((∑ r ∈ badFibers (antichain3Family L) ∅ 1,
          (((antichain3Family L).fib r).card : ℚ))
        ≤ (1 : ℚ) * 1
            * ((∅ : Finset (LinearExt Antichain3)).card : ℚ) / 1) ∧
      -- thm:step2 (ii): a genuine per-fiber staircase on the good fiber
      (∃ M : Finset (ℤ × ℤ),
        IsStaircasePlus
          (fiberGrid Antichain3.a0 Antichain3.a1 {L}) M ∧
        ((symmDiff (fiberCut Antichain3.a0 Antichain3.a1 {L}
            (∅ : Finset (LinearExt Antichain3))) M).card : ℚ)
          ≤ fiberStaircaseRate 1 1 1 1
              * ((fiberGrid Antichain3.a0 Antichain3.a1 {L}).card
                  : ℚ)) := by
  classical
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset, ?_⟩
  -- a genuine linear extension exists
  obtain ⟨L⟩ : Nonempty (LinearExt Antichain3) := by
    have h := Antichain3.two_le_numLinExt
    unfold numLinExt at h
    exact Fintype.card_pos_iff.mp (by omega)
  refine ⟨L, ⟨_, Finset.mem_singleton_self _⟩, ?_, ?_, ?_, ?_⟩
  · -- lem:fiber-avg fires
    have hmult : ∀ e ∈ globalBKBdy (∅ : Finset (LinearExt Antichain3)),
        ((antichain3Family L).carrier.filter
          (fun r => edgeInternal (antichain3Family L) r e)).card ≤ 1 := by
      intro e he
      rw [globalBKBdy_empty] at he
      simp at he
    exact lem_fiber_avg (antichain3Family L)
      (∅ : Finset (LinearExt Antichain3)) hmult
  · -- (a0, a1) is a good fiber
    rw [mem_goodFibers]
    refine ⟨Finset.mem_singleton_self _, ?_⟩
    rw [antichain3Family_fib, fiberBKBdy_singleton_empty]
    simp
  · -- thm:step2 (i): bad-fiber mass bound, here trivially 0 ≤ 0
    have hbad : badFibers (antichain3Family L)
        (∅ : Finset (LinearExt Antichain3)) 1 = ∅ := by
      unfold badFibers
      rw [Finset.filter_eq_empty_iff]
      intro r _
      rw [antichain3Family_fib, fiberBKBdy_singleton_empty]
      simp
    rw [hbad]
    simp
  · -- thm:step2 (ii): a genuine per-fiber staircase on the good fiber
    have hgood : (Antichain3.a0, Antichain3.a1)
        ∈ goodFibers (antichain3Family L) ∅ 1 := by
      rw [mem_goodFibers]
      refine ⟨Finset.mem_singleton_self _, ?_⟩
      rw [antichain3Family_fib, fiberBKBdy_singleton_empty]
      simp
    have ht : (1 : ℕ) ≤ commonNbhdLength
        (Antichain3.a0, Antichain3.a1).1
        (Antichain3.a0, Antichain3.a1).2 := by
      change 1 ≤ commonNbhdLength Antichain3.a0 Antichain3.a1
      rw [Antichain3.commonNbhdLength_a0_a1]
    have hsign : ∀ L' ∈ ({L} : Finset (LinearExt Antichain3)),
        signMarker Antichain3.a0 Antichain3.a1 L'
          = signMarker Antichain3.a0 Antichain3.a1 L := by
      intro L' hL'
      rw [Finset.mem_singleton] at hL'
      rw [hL']
    have hcardF : (fiberGrid Antichain3.a0 Antichain3.a1
        ({L} : Finset (LinearExt Antichain3))).card = 1 := by
      rw [fiberGrid_card (isGoodFiber_singleton _ _ L) hsign]
      exact Finset.card_singleton L
    have hmass : (1 : ℚ)
        * (commonNbhdLength (Antichain3.a0, Antichain3.a1).1
            (Antichain3.a0, Antichain3.a1).2 : ℚ) ^ 2
        ≤ ((fiberGrid (Antichain3.a0, Antichain3.a1).1
            (Antichain3.a0, Antichain3.a1).2
            ((antichain3Family L).fib
              (Antichain3.a0, Antichain3.a1))).card : ℚ) := by
      change (1 : ℚ)
        * (commonNbhdLength Antichain3.a0 Antichain3.a1 : ℚ) ^ 2
        ≤ ((fiberGrid Antichain3.a0 Antichain3.a1 {L}).card : ℚ)
      rw [Antichain3.commonNbhdLength_a0_a1, hcardF]
      norm_num
    obtain ⟨M, hM, hMerr⟩ :=
      prop_per_fiber_staircase (antichain3Family L)
        (∅ : Finset (LinearExt Antichain3)) (by norm_num) hgood ht hmass
    refine ⟨M, hM, ?_⟩
    -- the per-fiber rate at this fiber is fiberStaircaseRate 1 1 1 1
    have hrate : fiberStaircaseRate 1 1
        ((antichain3Family L).fib (Antichain3.a0, Antichain3.a1)).card
        (commonNbhdLength (Antichain3.a0, Antichain3.a1).1
          (Antichain3.a0, Antichain3.a1).2)
        = fiberStaircaseRate 1 1 1 1 := by
      rw [antichain3Family_fib, Finset.card_singleton]
      change fiberStaircaseRate 1 1 1
        (commonNbhdLength Antichain3.a0 Antichain3.a1)
        = fiberStaircaseRate 1 1 1 1
      rw [Antichain3.commonNbhdLength_a0_a1]
    rw [hrate] at hMerr
    exact hMerr

end PerFiberGrounded
end Step2
end OneThird
