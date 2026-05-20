/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step3.Step3Theorem
import OneThird.Step2.PerFiberGrounded2

/-!
# Step 3 — `lem:local-sign` orientation lemma and the coherence definition (grounded)

This file is the **FULL REFACTOR** (Option A', mg-d8c7 §2.1 Piece 1,
Wave 2) grounded port of the two Step 3 deliverables that Step 4
consumes:

* **`lem:local-sign`** (`step3.tex:93`) — existence and *structural*
  uniqueness of the local sign `σ_{x,y} ∈ {±1}` of the Step 2
  staircase.  The abstract scaffold `OneThird.Step3.LocalSign`
  delivered only the existence half and the *easy* `(⇐)` half of
  structural uniqueness (`coordinateStrip_has_both_types`), deferring
  the substantive `(⇒)` half ("a two-type staircase is a coordinate
  strip") to the paper.  This file **proves that substantive half**
  (`coordinateStrip_of_both_types`), completing `lem:local-sign`(i),
  and **grounds** it against the actual Step 2 output:
  `prop_per_fiber_staircase` / `thm_step2` produce
  `WeakGrid.IsStaircasePlus D M`, and `isStaircasePlus_iff_isStaircaseType_false`
  identifies that with the column-threshold staircase notion of
  `LocalSign.lean`, so `lem_local_sign` extracts the sign directly
  from a Step 2 staircase.

* **`def:eta` + `def:coherent`** (`step3.tex:626` / `step3.tex:660`) —
  the per-state local sign `η_{x,y}(L)` on the regular overlap, and
  the coherence / incoherence dichotomy.  The abstract
  `OneThird.Step3.Step3Theorem` carries `Coherent` / `Incoherent` /
  `correlation_card_identity` for a *black-box* `η`.  This file
  **defines `η` from the geometry** (`def:eta`: `etaOfDir` / the
  per-state `etaOnState`), pinning the floating sign function to the
  local sign `σ` and the common axis, and re-exports the coherence
  predicates and `prop:correlation` with that grounded `η`
  (`CoherentPair` / `IncoherentPair` / `coherence_correlation_grounded`).

## Non-vacuity

`localSign_coherence_grounded_nonvacuous` instantiates the whole
framework at the concrete width-3 non-chain poset `Antichain3`:

* `lem_local_sign` fires on a **genuinely two-dimensional** staircase
  (`sampleStaircase ⊆ sampleGrid`, an `L`-shape that is *not* a
  coordinate strip and lies strictly between `∅` and the full grid),
  so structural uniqueness pins `σ = false` non-trivially;
* `def:eta` is genuinely two-valued (`etaOfDir σ (1,0) ≠ etaOfDir σ (-1,0)`);
* the coherence dichotomy fires on a genuine overlap
  `Ωreg := (univ : Finset (LinearExt Antichain3))` with `2 ≤ |Ωreg|`.

No `Subsingleton`-on-empty baseline: the grid, the staircase, and the
overlap are all non-degenerate.

## Downstream

Step 4 (the two-interface incompatibility lemma) consumes the local
sign, `etaOfDir`, and `CoherentPair` / `IncoherentPair`.
-/

namespace OneThird
namespace Step3

open Finset OneThird.Step2.WeakGrid

/-! ## §1. Reading the local sign off a `+`-staircase

The Step 2 grounded output (`prop_per_fiber_staircase`, `thm_step2`)
is `WeakGrid.IsStaircasePlus D M` — `M` is a *product-order lower set*
of `D`.  We identify that with the column-threshold staircase notion
`IsStaircaseType false D M` of `LocalSign.lean` (decreasing threshold
function), giving `lem:local-sign` a concrete sign to extract. -/

/-- A strict lower bound for every second coordinate of `D`: one below
the minimum of `D`'s `j`-coordinates (with a `0` fallback making the
finset nonempty even when `D = ∅`). -/
noncomputable def gridBot (D : Finset (ℤ × ℤ)) : ℤ :=
  (insert (0 : ℤ) (D.image Prod.snd)).min' (Finset.insert_nonempty _ _) - 1

/-- Every point of `D` has second coordinate strictly above `gridBot D`. -/
theorem gridBot_lt {D : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ D) :
    gridBot D < p.2 := by
  have hle : (insert (0 : ℤ) (D.image Prod.snd)).min'
      (Finset.insert_nonempty _ _) ≤ p.2 :=
    Finset.min'_le _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  unfold gridBot
  omega

/-- The **decreasing column-threshold** of a `+`-staircase `M ⊆ D`:
the largest `j`-coordinate of `M` over columns `≥ i`, floored at
`gridBot D`.  This is the threshold function witnessing that a
product-order lower set is a `IsStaircaseType false` staircase. -/
noncomputable def plusThreshold (D M : Finset (ℤ × ℤ)) (i : ℤ) : ℤ :=
  (insert (gridBot D) ((M.filter (fun p => i ≤ p.1)).image Prod.snd)).max'
    (Finset.insert_nonempty _ _)

/-- `plusThreshold` is weakly decreasing: dropping the column floor
`i` can only enlarge the finset whose maximum is taken. -/
theorem plusThreshold_antitone {D M : Finset (ℤ × ℤ)} {i i' : ℤ}
    (h : i ≤ i') : plusThreshold D M i' ≤ plusThreshold D M i := by
  unfold plusThreshold
  apply Finset.max'_le
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with hx | hx
  · subst hx
    exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter] at hq
    refine Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨q, ?_, hqx⟩))
    rw [Finset.mem_filter]
    exact ⟨hq.1, le_trans h hq.2⟩

/-- Every point of `M` lies weakly below its column threshold. -/
theorem le_plusThreshold_of_mem {D M : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hp : p ∈ M) : p.2 ≤ plusThreshold D M p.1 := by
  unfold plusThreshold
  refine Finset.le_max' _ _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, ?_, rfl⟩))
  rw [Finset.mem_filter]
  exact ⟨hp, le_refl _⟩

/-- For a `+`-staircase, a `D`-point weakly below its column threshold
is a member of `M`: the threshold maximum is attained at a genuine
`M`-point `q` with `p ≤ q`, and `M` is a product-order lower set. -/
theorem mem_of_le_plusThreshold {D M : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hSP : IsStaircasePlus D M) (hpD : p ∈ D)
    (hle : p.2 ≤ plusThreshold D M p.1) : p ∈ M := by
  obtain ⟨hMD, hlower⟩ := hSP
  have hmem := Finset.max'_mem
    (insert (gridBot D) ((M.filter (fun q => p.1 ≤ q.1)).image Prod.snd))
    (Finset.insert_nonempty _ _)
  rw [Finset.mem_insert] at hmem
  rcases hmem with hmem | hmem
  · exact absurd (le_of_le_of_eq hle hmem) (not_le.mpr (gridBot_lt hpD))
  · obtain ⟨q, hqf, hqeq⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_filter] at hqf
    have hpq : p ≤ q :=
      Prod.le_def.mpr ⟨hqf.2, le_of_le_of_eq hle hqeq.symm⟩
    exact hlower q hqf.1 p hpD hpq

/-- **The Step 2 staircase notion and the Step 3 sign notion coincide.**
`WeakGrid.IsStaircasePlus D M` (a product-order lower set, the output
of the grounded Step 2 `prop:per-fiber`) is exactly an
`IsStaircaseType false D M` staircase in the column-threshold form of
`step3.tex` `def:staircase-type` — the `σ = -1` (decreasing-threshold)
orientation. -/
theorem isStaircasePlus_iff_isStaircaseType_false (D M : Finset (ℤ × ℤ)) :
    IsStaircasePlus D M ↔ IsStaircaseType false D M := by
  constructor
  · rintro ⟨hMD, hlower⟩
    refine ⟨hMD, plusThreshold D M, ?_, ?_⟩
    · intro i i' hii'
      exact plusThreshold_antitone hii'
    · intro p hpD
      exact ⟨fun hpM => le_plusThreshold_of_mem hpM,
        fun hle => mem_of_le_plusThreshold ⟨hMD, hlower⟩ hpD hle⟩
  · rintro ⟨hMD, g, hg_mono, hg⟩
    refine ⟨hMD, ?_⟩
    intro p hpM q hqD hqp
    have hpg : p.2 ≤ g p.1 := (hg p (hMD hpM)).mp hpM
    have hq1 : q.1 ≤ p.1 := (Prod.le_def.mp hqp).1
    have hq2 : q.2 ≤ p.2 := (Prod.le_def.mp hqp).2
    have hgmono : g p.1 ≤ g q.1 := hg_mono q.1 p.1 hq1
    exact (hg q hqD).mpr (le_trans hq2 (le_trans hpg hgmono))

/-! ## §2. `lem:local-sign`(i) — structural uniqueness

The abstract `LocalSign.lean` proved the easy direction
(`coordinateStrip_has_both_types`: a coordinate strip carries *both*
signs).  We prove the substantive converse: a staircase that carries
*both* signs *is* a coordinate strip — and hence, off the coordinate
strips, the local sign is unique. -/

/-- **`lem:local-sign`(i), substantive `(⇒)` direction** (`step3.tex:128-194`).

If `M ⊆ D` is a staircase of type `+1` (increasing threshold `f`) *and*
of type `-1` (decreasing threshold `g`), then `M` is a coordinate
strip `D ∩ {j ≤ h}`.

The proof needs *no* order-convexity of `D` (the paper's argument
threads it through the diagonal change of variables; the direct finite
argument here does not).  Take `h := max {p.2 : p ∈ M}`, attained at
some `q ∈ M`.  For any `p ∈ D` with `p.2 ≤ h = q.2`: comparing columns
`p.1` and `q.1`, the increasing `f` (if `q.1 ≤ p.1`) or the decreasing
`g` (if `p.1 ≤ q.1`) carries `p.2 ≤ q.2 ≤ threshold(q.1) ≤ threshold(p.1)`,
forcing `p ∈ M`. -/
theorem coordinateStrip_of_both_types {D M : Finset (ℤ × ℤ)}
    (hpos : IsStaircaseType true D M) (hneg : IsStaircaseType false D M) :
    IsCoordinateStrip D M := by
  classical
  obtain ⟨hMD, f, hf_mono, hf⟩ := hpos
  obtain ⟨-, g, hg_mono, hg⟩ := hneg
  by_cases hMne : M.Nonempty
  · have himg : (M.image Prod.snd).Nonempty := Finset.image_nonempty.mpr hMne
    refine ⟨(M.image Prod.snd).max' himg, ?_⟩
    ext p
    rw [mem_coordinateStrip]
    constructor
    · intro hpM
      exact ⟨hMD hpM,
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hpM, rfl⟩)⟩
    · rintro ⟨hpD, hph⟩
      obtain ⟨q, hqM, hqeq⟩ :=
        Finset.mem_image.mp (Finset.max'_mem (M.image Prod.snd) himg)
      have hqle : p.2 ≤ q.2 := le_of_le_of_eq hph hqeq.symm
      rcases le_total q.1 p.1 with hcase | hcase
      · -- `q.1 ≤ p.1`: the increasing threshold `f` carries `p` into `M`.
        have hfq : q.2 ≤ f q.1 := (hf q (hMD hqM)).mp hqM
        have hfm : f q.1 ≤ f p.1 := hf_mono q.1 p.1 hcase
        exact (hf p hpD).mpr (le_trans (le_trans hqle hfq) hfm)
      · -- `p.1 ≤ q.1`: the decreasing threshold `g` carries `p` into `M`.
        have hgq : q.2 ≤ g q.1 := (hg q (hMD hqM)).mp hqM
        have hgm : g q.1 ≤ g p.1 := hg_mono p.1 q.1 hcase
        exact (hg p hpD).mpr (le_trans (le_trans hqle hgq) hgm)
  · -- `M = ∅` is the coordinate strip at height `gridBot D`.
    rw [Finset.not_nonempty_iff_eq_empty] at hMne
    subst hMne
    refine ⟨gridBot D, ?_⟩
    symm
    unfold coordinateStrip
    rw [Finset.filter_eq_empty_iff]
    intro p hp
    exact not_le.mpr (gridBot_lt hp)

/-- **`lem:local-sign`(i), full equivalence.**  A staircase carries
*both* signs iff it is a coordinate strip — combining the substantive
`coordinateStrip_of_both_types` with the abstract scaffold's
`coordinateStrip_has_both_types`. -/
theorem isStaircaseType_both_iff_coordinateStrip {D M : Finset (ℤ × ℤ)} :
    (IsStaircaseType true D M ∧ IsStaircaseType false D M) ↔
      IsCoordinateStrip D M :=
  ⟨fun h => coordinateStrip_of_both_types h.1 h.2,
   fun h => coordinateStrip_has_both_types D M h⟩

/-- **`lem:local-sign`(i), uniqueness on the generic stratum.**  Off
the coordinate strips, the local sign is *uniquely determined* by `M`:
any two signs witnessing a staircase type for `M` are equal. -/
theorem localSign_unique {D M : Finset (ℤ × ℤ)}
    (hns : ¬ IsCoordinateStrip D M) {σ σ' : Sign}
    (h : IsStaircaseType σ D M) (h' : IsStaircaseType σ' D M) : σ = σ' := by
  by_contra hne
  have hboth : IsStaircaseType true D M ∧ IsStaircaseType false D M := by
    cases σ <;> cases σ' <;>
      first
        | exact absurd rfl hne
        | exact ⟨h, h'⟩
        | exact ⟨h', h⟩
  exact hns (coordinateStrip_of_both_types hboth.1 hboth.2)

/-! ## §3. `lem:local-sign` — grounded extraction

The grounded `lem:local-sign`: feed a Step 2 staircase
(`IsStaircasePlus`, the literal output type of `prop_per_fiber_staircase`)
and obtain its local sign, with the structural-uniqueness guarantee. -/

/-- **`lem:local-sign` (grounded).**  Every Step 2 staircase
`IsStaircasePlus D M` has a local sign `σ` (here the
decreasing-threshold sign `σ = false`, paper `σ = -1`): `M` is a
staircase of type `σ`, and — *off the coordinate strips* — `σ` is the
*unique* type of `M` (`step3.tex` `lem:local-sign`, parts existence +
(i)).  The coordinate-strip degeneracy (`rem:strip-degeneracy`) is the
recorded exception: there both signs are valid, by
`coordinateStrip_has_both_types`. -/
theorem lem_local_sign {D M : Finset (ℤ × ℤ)} (hM : IsStaircasePlus D M) :
    ∃ σ : Sign, IsStaircaseType σ D M ∧
      (¬ IsCoordinateStrip D M →
        ∀ σ', IsStaircaseType σ' D M → σ' = σ) := by
  have hfalse : IsStaircaseType false D M :=
    (isStaircasePlus_iff_isStaircaseType_false D M).mp hM
  exact ⟨false, hfalse, fun hns σ' hσ' => localSign_unique hns hσ' hfalse⟩

/-! ## §4. `def:eta` — the per-state local sign on the overlap

`step3.tex` `def:eta` defines `η_{x,y}(L) ∈ {±1}` from the positive
cone: `+1` if the common axis `a(L)` lies in `P_{x,y}(L)`, `-1` if
`-a(L)` does.  The abstract `Step3Theorem.lean` carries `η` as a
black box; here we *define* it from the local sign `σ` and the axis. -/

/-- **`def:eta` (core).**  The local sign of a grid direction `e` with
respect to the positive cone of sign `σ`: `+1` (`true`) iff `e` lies
in `positiveCone σ` (i.e. `e` increases `h_σ`), `-1` (`false`)
otherwise. -/
def etaOfDir (σ : Sign) (e : ℤ × ℤ) : Sign :=
  decide (e ∈ positiveCone σ)

@[simp] theorem etaOfDir_eq_true_iff {σ : Sign} {e : ℤ × ℤ} :
    etaOfDir σ e = true ↔ e ∈ positiveCone σ := by
  unfold etaOfDir
  exact decide_eq_true_iff

/-- The positive `i`-axis `(1,0)` is always in the positive cone, so
its `def:eta` sign is `+1`. -/
@[simp] theorem etaOfDir_e1 (σ : Sign) : etaOfDir σ (1, 0) = true := by
  cases σ <;> decide

/-- The negative `i`-axis `(-1,0)` is never in the positive cone, so
its `def:eta` sign is `-1`. -/
@[simp] theorem etaOfDir_neg_e1 (σ : Sign) : etaOfDir σ (-1, 0) = false := by
  cases σ <;> decide

/-- **`def:eta` is well-defined on grid directions.**  For a genuine
grid direction `e`, *exactly one* of `e` and `-e` lies in
`positiveCone σ` — so `η` is a genuine `{±1}`-valued choice, never
ambiguous.  This is the `step3.tex:644-647` well-definedness clause. -/
theorem etaOfDir_neg_ne {σ : Sign} {e : ℤ × ℤ} (he : e ∈ gridDirs) :
    etaOfDir σ e ≠ etaOfDir σ (-e) := by
  rw [mem_gridDirs] at he
  rcases he with rfl | rfl | rfl | rfl <;> cases σ <;> decide

/-- **`def:eta` (per-state).**  The per-state local sign `η_{x,y}(L)`
on the regular overlap: the `def:eta` sign of the common axis `a(L)`. -/
def etaOnState {γ : Type*} (σ : Sign) (a : γ → ℤ × ℤ) (L : γ) : Sign :=
  etaOfDir σ (a L)

/-! ## §5. `def:coherent` — the coherence definition, grounded

The abstract `Step3Theorem.lean` carries `Coherent` / `Incoherent` /
`correlation_card_identity` for a black-box `η`.  Here we re-package
them with the geometric `etaOnState` `η`, so the coherence predicate
is pinned to the local sign and the common axes. -/

-- The abstract `Step3Theorem` API (`Coherent`, `Incoherent`,
-- `correlation_card_identity`) carries a `[DecidableEq γ]` it does not
-- use in its conclusion; the grounded re-exports below inherit that.
set_option linter.unusedDecidableInType false

variable {γ : Type*} [DecidableEq γ]

/-- **`def:coherent` (grounded).**  Two rich pairs with local signs
`σxy, σuv` and common axes `axy, buv` are *coherent* on the regular
overlap `Ωreg` when their `def:eta` signs disagree on at most an
`a/c`-fraction of `Ωreg` (`step3.tex:662`, cleared-denominator form). -/
def CoherentPair (Ωreg : Finset γ) (σxy σuv : Sign)
    (axy buv : γ → ℤ × ℤ) (a c : ℕ) : Prop :=
  Coherent Ωreg (etaOnState σxy axy) (etaOnState σuv buv) a c

/-- **`def:incoherent` (grounded).**  The two rich pairs are
*incoherent* when their `def:eta` signs disagree on at least a
`cinc/d`-fraction of `Ωreg` (`step3.tex:665`). -/
def IncoherentPair (Ωreg : Finset γ) (σxy σuv : Sign)
    (axy buv : γ → ℤ × ℤ) (cinc d : ℕ) : Prop :=
  Incoherent Ωreg (etaOnState σxy axy) (etaOnState σuv buv) cinc d

/-- **`prop:correlation` (grounded).**  With the geometric `def:eta`
`η`, the per-overlap correlation sum equals `|Ωreg| − 2·|disagree|`,
i.e. `Corr = 1 − 2·Pr[η ≠ η']` (`step3.tex:672-684`). -/
theorem coherence_correlation_grounded (Ωreg : Finset γ)
    (σxy σuv : Sign) (axy buv : γ → ℤ × ℤ) :
    ∑ L ∈ Ωreg, corrProduct (etaOnState σxy axy) (etaOnState σuv buv) L =
      (Ωreg.card : ℤ) -
        2 * ((disagreeSet Ωreg (etaOnState σxy axy)
          (etaOnState σuv buv)).card : ℤ) :=
  correlation_card_identity Ωreg _ _

/-- **`prop:correlation` (grounded, incoherent branch).**  An
`IncoherentPair` (disagreement `≥ cinc/d`) forces the correlation down
to `Corr ≤ 1 − 2·cinc/d`. -/
theorem incoherentPair_correlation_le (Ωreg : Finset γ)
    (σxy σuv : Sign) (axy buv : γ → ℤ × ℤ) (cinc d : ℕ) (hd : 0 < d)
    (h : IncoherentPair Ωreg σxy σuv axy buv cinc d) :
    (d : ℤ) * ∑ L ∈ Ωreg,
        corrProduct (etaOnState σxy axy) (etaOnState σuv buv) L ≤
      ((d : ℤ) - 2 * (cinc : ℤ)) * (Ωreg.card : ℤ) :=
  correlation_incoherent_bound Ωreg _ _ cinc d hd h

/-- **`prop:correlation` (grounded, coherent branch).**  A
`CoherentPair` (disagreement `≤ a/c`) keeps the correlation up at
`Corr ≥ 1 − 2·a/c`. -/
theorem coherentPair_correlation_ge (Ωreg : Finset γ)
    (σxy σuv : Sign) (axy buv : γ → ℤ × ℤ) (a c : ℕ) (hc : 0 < c)
    (h : CoherentPair Ωreg σxy σuv axy buv a c) :
    (c : ℤ) * ∑ L ∈ Ωreg,
        corrProduct (etaOnState σxy axy) (etaOnState σuv buv) L ≥
      ((c : ℤ) - 2 * (a : ℤ)) * (Ωreg.card : ℤ) :=
  correlation_coherent_bound Ωreg _ _ a c hc h

/-! ## §6. Non-vacuity at the concrete width-3 non-chain poset

Per the mg-7a22 acceptance bar, the port must instantiate
non-vacuously at a concrete width-3 non-chain `α` — `Antichain3` —
with no `Subsingleton`-on-empty baseline. -/

/-- A concrete `2 × 2` grid `{0,1}²`. -/
def sampleGrid : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 0), (1, 1)}

/-- A concrete `L`-shaped staircase inside `sampleGrid`: the
product-order lower set missing only the top corner `(1,1)`.  It is
genuinely two-dimensional — not `∅`, not the full grid, and *not* a
coordinate strip. -/
def sampleStaircase : Finset (ℤ × ℤ) := {(0, 0), (0, 1), (1, 0)}

/-- `sampleStaircase` is a genuine `+`-staircase of `sampleGrid`. -/
theorem sampleStaircase_isStaircasePlus :
    IsStaircasePlus sampleGrid sampleStaircase :=
  ⟨by decide, by decide⟩

/-- `sampleStaircase` is **not** a coordinate strip: `(0,1) ∈ M` forces
the height `h ≥ 1`, but then `(1,1)` — which is *not* in `M` — would
also be `≤ h` and inside the strip.  So `lem:local-sign`'s structural
uniqueness applies *non-vacuously* here. -/
theorem sampleStaircase_not_coordinateStrip :
    ¬ IsCoordinateStrip sampleGrid sampleStaircase := by
  rintro ⟨h, hMh⟩
  have h01 : ((0 : ℤ), (1 : ℤ)) ∈ sampleStaircase := by decide
  have h11 : ((1 : ℤ), (1 : ℤ)) ∉ sampleStaircase := by decide
  rw [hMh, mem_coordinateStrip] at h01
  have hh : (1 : ℤ) ≤ h := h01.2
  apply h11
  rw [hMh, mem_coordinateStrip]
  exact ⟨by decide, hh⟩

/-- **Non-vacuity of the Step 3 grounded port** (the mg-7a22 acceptance
witness).

At the concrete width-3 non-chain poset `Antichain3`:

* **(local sign)** `lem_local_sign` fires on the genuinely
  two-dimensional, non-coordinate-strip staircase
  `sampleStaircase ⊆ sampleGrid`, pinning the local sign to `false`
  *and* certifying it is the unique type (`sampleStaircase` is neither
  `∅` nor the full grid);
* **(`def:eta`)** the per-direction sign is genuinely two-valued:
  `etaOfDir σ (1,0) ≠ etaOfDir σ (-1,0)`;
* **(coherence)** the coherence dichotomy fires on a genuine overlap
  `Ωreg := (univ : Finset (LinearExt Antichain3))` with `2 ≤ |Ωreg|`:
  the two `def:eta` sign functions built from the axes `(1,0)` and
  `(-1,0)` disagree on *all* of `Ωreg`, witnessing an `IncoherentPair`,
  and the grounded `prop:correlation` evaluates the correlation sum to
  `-|Ωreg|`.

No `Subsingleton`-on-empty baseline: `Antichain3` is genuinely width-3
and non-chain, the grid and staircase are non-degenerate, and the
overlap has at least two elements. -/
theorem localSign_coherence_grounded_nonvacuous :
    HasWidth Antichain3 3 ∧
    ¬ IsChainPoset Antichain3 ∧
    -- (local sign) lem:local-sign fires non-degenerately
    (sampleStaircase.Nonempty ∧ sampleStaircase ≠ sampleGrid ∧
      ¬ IsCoordinateStrip sampleGrid sampleStaircase ∧
      ∃ σ : Sign, IsStaircaseType σ sampleGrid sampleStaircase ∧
        σ = false ∧
        ∀ σ', IsStaircaseType σ' sampleGrid sampleStaircase → σ' = σ) ∧
    -- (def:eta) genuinely two-valued
    (∀ σ : Sign, etaOfDir σ (1, 0) ≠ etaOfDir σ (-1, 0)) ∧
    -- (coherence) the dichotomy fires on a genuine overlap
    (2 ≤ (Finset.univ : Finset (LinearExt Antichain3)).card ∧
      IncoherentPair (Finset.univ : Finset (LinearExt Antichain3))
        true true (fun _ => (1, 0)) (fun _ => (-1, 0)) 1 1 ∧
      ∑ L ∈ (Finset.univ : Finset (LinearExt Antichain3)),
          corrProduct (etaOnState true (fun _ => (1, 0)))
            (etaOnState true (fun _ => (-1, 0))) L
        = - ((Finset.univ : Finset (LinearExt Antichain3)).card : ℤ)) := by
  classical
  refine ⟨Antichain3.hasWidth, Antichain3.not_isChainPoset, ?_, ?_, ?_⟩
  · -- lem:local-sign on a genuine 2D non-strip staircase
    obtain ⟨σ, hσtype, hσuniq⟩ := lem_local_sign sampleStaircase_isStaircasePlus
    refine ⟨⟨((0 : ℤ), (0 : ℤ)), by decide⟩, by decide,
      sampleStaircase_not_coordinateStrip,
      σ, hσtype, ?_, hσuniq sampleStaircase_not_coordinateStrip⟩
    -- the extracted sign is `false`
    exact localSign_unique sampleStaircase_not_coordinateStrip hσtype
      ((isStaircasePlus_iff_isStaircaseType_false _ _).mp
        sampleStaircase_isStaircasePlus)
  · -- def:eta is genuinely two-valued
    intro σ
    rw [etaOfDir_e1, etaOfDir_neg_e1]
    decide
  · -- the coherence dichotomy fires on Ωreg = univ
    -- the def:eta signs disagree on all of Ωreg
    have hdis : disagreeSet (Finset.univ : Finset (LinearExt Antichain3))
        (etaOnState true (fun _ => ((1 : ℤ), (0 : ℤ))))
        (etaOnState true (fun _ => ((-1 : ℤ), (0 : ℤ))))
        = (Finset.univ : Finset (LinearExt Antichain3)) := by
      unfold disagreeSet
      apply Finset.filter_true_of_mem
      intro L _
      simp [etaOnState]
    have hcard : 2 ≤ (Finset.univ : Finset (LinearExt Antichain3)).card := by
      have hcu : (Finset.univ : Finset (LinearExt Antichain3)).card
          = numLinExt Antichain3 := by
        rw [Finset.card_univ]; rfl
      rw [hcu]
      exact Antichain3.two_le_numLinExt
    have hdiscard : (disagreeSet (Finset.univ : Finset (LinearExt Antichain3))
        (etaOnState true (fun _ => ((1 : ℤ), (0 : ℤ))))
        (etaOnState true (fun _ => ((-1 : ℤ), (0 : ℤ))))).card
        = (Finset.univ : Finset (LinearExt Antichain3)).card := by
      rw [hdis]
    refine ⟨hcard, ?_, ?_⟩
    · -- IncoherentPair with cinc = d = 1
      unfold IncoherentPair Incoherent
      omega
    · -- the grounded prop:correlation evaluates to -|Ωreg|
      rw [coherence_correlation_grounded, hdis]
      ring

end Step3
end OneThird
