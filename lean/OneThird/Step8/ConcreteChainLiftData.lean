/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ChainPotentials
import OneThird.Step8.LayeredReduction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Step 8 — A concrete, non-degenerate `ChainLiftData` (S7-F bridge input; F7a)

This file is **part R1 of the FULL REFACTOR Phase-2 Checkpoint-3
re-scope** (`docs/state-S7F-Checkpoint3-Session1.md`, mg-ca83 §6 R1;
work item mg-974c). It **settles the open F7a constructibility
question**.

## What F7a is, and the verdict

Checkpoint 3 (mg-ca83) found Piece 2 delivered the **wrong object** —
`L_S7E : Step7.LayeredWidth3` is a rich-pair window-confinement
packaging with no poset-structural content, while the S7-F bridge
`lem:layered-from-step7` consumes a **`ChainLiftData α`**
(`ChainPotentials.lean:328` — Dilworth triple `A/B/C` + chain
potential + sync maps `f_AB/f_AC/f_BC` + bandwidth constant `K_bw`).
R2 (mg-3119) reconciled the bridge contract to consume a
`ChainLiftData α`; **F7a** is the question it left open:

> *Is a concrete, **non-degenerate** `ChainLiftData α` constructible
> for `α` a width-3 non-chain poset?*

No concrete `ChainLiftData` instance existed in tree (mg-ca83 §6 R1:
the structure was referenced only in `LayeredBridges.lean` /
`MainAssembly.lean` / its defining file, never instantiated).

**Verdict: F7a is GREEN — constructible.** `gridChainLiftData` below
is a concrete `ChainLiftData (Fin 3 × Fin 3)` on the 3×3 grid (a
genuine width-3, non-chain, 9-element finite poset), and it is
**non-degenerate** on every axis Checkpoint 3 Finding D flagged:

* **Chain potential is non-constant** — `potFun (i,j) = i + j` takes
  the 5 distinct values `{0,1,2,3,4}` (contrast the rejected constant
  BFS potential `signedWeight := fun _ => 0`).
* **Sync maps carry genuine content** — `f_AB`, `f_BC` are total and
  non-constant; `f_AC` is genuinely *partial*, with a real chain-tail
  orphan (`X^exc_sync`) at index `0` (contrast the rejected
  `SyncMap.empty`).
* **`K_bw` is non-inert** — `K_bw = 1` is the *actual* maximum
  chain-potential gap across incomparable pairs
  (`gridChainLiftData_bandwidth_genuine`), and it is *tight*
  (`gridChainLiftData_bandwidth_tight` — it cannot be lowered to `0`).
  Contrast the rejected inert `bandwidth ≤ 4` that reduced to `4 ≤ 4`.
* **The three chains genuinely cover** the 9-element ground set, each
  a real length-3 chain.

`f7a_chainLiftData_constructible` packages the verdict as the exact
codomain of the §4.2 §D′ constructor `chainLiftData_of_cascade`
(`∃ cld : ChainLiftData α, cld.K_bw ≤ 2`).

## What this does NOT claim — the §11.3 caveat

F7a asks whether the *structure* is constructible. It is. But — per
`docs/state-MA-Sig-Session1.md` §11.3 — the **bare** `ChainLiftData`
structure carries no soundness invariant tying `pot`/sync-maps to a
genuine Steps-1-7 cascade output: the bare structure is inhabited
even for the 3-disjoint-chains family `Δ_ℓ`, where the bridge's
`L.w ≤ 4` conclusion is *false* for large `ℓ`. So constructibility of
the structure (this file, F7a = GREEN) does **not** by itself make
the S7-F bridge *body* go through — that is the separate §11.3
resolution-(B) question (strengthen the structure with soundness
fields), an explicit **Piece-3 / F7-bridge** concern, not R1's.

To show this witness is the *genuine* kind and not a `Δ_ℓ`-style
vacuous-but-inhabited one, `gridChainLiftData_bandwidth_genuine`
proves the grid's chain potential confines **every** incomparable
pair within `K_bw = 1` — a property that is provably *false* for
`Δ_ℓ` (disjoint chains have cross-chain potential gaps growing with
`ℓ`). `gridLayered` corroborates further: the grid carrier admits a
genuine ground-set `LayeredDecomposition` with `w = 1 ≤ 4` — the
exact object shape the S7-F bridge is meant to produce.

Per MA-Sig §11.4 this is **case 1**: R1 lands GREEN with a concrete
non-degenerate `ChainLiftData α` matching the bare structure, so
§4.2 §D′/§E stand as pinned.

## Cross-references

* `lean/OneThird/Step8/ChainPotentials.lean:328` — `ChainLiftData α`
  (the structure instantiated here); `:211` `SyncMap`; `:238`
  `SyncMap.empty` (the degenerate inhabitant avoided here); `:267`
  `ChainPotential`.
* `lean/OneThird/Step8/LayeredReduction.lean:113` —
  `LayeredDecomposition` (the `gridLayered` corroboration target).
* `docs/state-S7F-Checkpoint3-Session1.md` (mg-ca83) — Checkpoint 3
  audit; §6 R1 the re-scope; Finding D the degeneracy bar.
* `docs/state-MA-Sig-Session1.md` §11 (mg-3119) — the reconciled
  contract; §11.4 the F7a provisionality cases.
* `docs/state-S7F-R1-Session1.md` — this session's state doc.
-/

namespace OneThird
namespace Step8
namespace GridChainLift

/-! ### §1 — The concrete carrier: the 3×3 grid -/

/-- **The concrete carrier**: the 3×3 grid `Fin 3 × Fin 3` under the
product partial order — a width-3, non-chain, 9-element finite
poset. (`W3` of `Step5/G1G2Grounded.lean` is the same type; it is
re-introduced here to keep this file an independent leaf.) -/
abbrev Grid : Type := Fin 3 × Fin 3

instance : DecidableLT Grid := decidableLTOfDecidableLE

/-! ### §2 — The Dilworth chain triple -/

/-- Dilworth chain `A` — the first column `{0} × Fin 3`. -/
def chainA : IndexedChain Grid where
  length := 3
  elem := fun i => (0, i)
  strictMono := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide

/-- Dilworth chain `B` — the middle column `{1} × Fin 3`. -/
def chainB : IndexedChain Grid where
  length := 3
  elem := fun i => (1, i)
  strictMono := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide

/-- Dilworth chain `C` — the last column `{2} × Fin 3`. -/
def chainC : IndexedChain Grid where
  length := 3
  elem := fun i => (2, i)
  strictMono := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide

/-- The three columns cover the grid — a genuine Dilworth cover for a
width-3 poset. -/
def triple : ChainTriple Grid where
  A := chainA
  B := chainB
  C := chainC
  cover := by decide

/-! ### §3 — The chain potential -/

/-- The chain potential `a(i,j) = i + j` — the grid rank function,
strictly increasing along every column. Non-constant: it takes the 5
distinct values `{0,1,2,3,4}` (`gridChainLiftData_pot_nonconstant`). -/
def potFun : Grid → ℤ := fun p => ((p.1 : ℕ) : ℤ) + ((p.2 : ℕ) : ℤ)

/-- The chain potential bundled as a `ChainPotential` — strictly
monotone along each of the three columns. -/
def pot : ChainPotential triple where
  a := potFun
  strictMonoA := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide
  strictMonoB := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide
  strictMonoC := by intro i j h; revert h; fin_cases i <;> fin_cases j <;> decide

/-! ### §4 — The synchronization maps -/

/-- Sync map `f_AB : A → B` — the `K_bw`-windowed argmin alignment
of chain `A` into chain `B`. Total and non-constant: `[0, 0, 1]`.
(`A` potentials `[0,1,2]`, `B` potentials `[1,2,3]`; each `A` index
aligns to the closest `B` index within `K_bw = 1`.) -/
def syncAB : SyncMap 3 3 where
  partner := ![some 0, some 0, some 1]
  weakly_monotone := by decide

/-- Sync map `f_AC : A → C` — the `K_bw`-windowed argmin alignment of
chain `A` into chain `C`. **Genuinely partial**: index `0` is a
chain-tail orphan (`X^exc_sync`), `[none, 0, 0]`. Chain-`A` element
`(0,0)` has potential `0`, more than `K_bw = 1` away from every
element of `C` (potentials `[2,3,4]`), so it has no `C`-partner —
see `gridChainLiftData_orphan_forced`. -/
def syncAC : SyncMap 3 3 where
  partner := ![none, some 0, some 0]
  weakly_monotone := by decide

/-- Sync map `f_BC : B → C` — the `K_bw`-windowed argmin alignment of
chain `B` into chain `C`. Total and non-constant: `[0, 0, 1]`. -/
def syncBC : SyncMap 3 3 where
  partner := ![some 0, some 0, some 1]
  weakly_monotone := by decide

/-! ### §5 — The concrete `ChainLiftData` -/

/-- **The concrete, non-degenerate `ChainLiftData`** on the 3×3 grid
— the genuine S7-F bridge input object. Settles F7a: a concrete
`ChainLiftData` IS constructible, non-degenerately (see the
non-degeneracy certificates of §6). -/
def gridChainLiftData : ChainLiftData Grid where
  triple := triple
  pot := pot
  K_bw := 1
  fAB := syncAB
  fAC := syncAC
  fBC := syncBC

/-! ### §6 — Non-degeneracy certificates -/

/-- The deliverable's contract conjunct: `K_bw ≤ 2` — so the lifted
`LayeredDecomposition` has `w = K_bw + 2 ≤ 4` (MA-Sig §4.2 §D′/§E). -/
theorem gridChainLiftData_K_bw_le_two : gridChainLiftData.K_bw ≤ 2 := by decide

/-- **Genuine `lem:bandwidth` content.** Every incomparable pair of
grid elements has chain-potential gap at most `K_bw = 1`. This is the
non-inert width bound: `K_bw` is the *actual* maximum potential gap
across incomparable pairs, not a free parameter fixed to a literal.

This property is what distinguishes the grid (a genuine carrier)
from the `Δ_ℓ` family (`docs/state-MA-Sig-Session1.md` §11.3): in
`Δ_ℓ` the three chains are disjoint, so cross-chain incomparable
pairs have potential gaps growing with `ℓ` — no finite `K_bw` bounds
them. -/
theorem gridChainLiftData_bandwidth_genuine :
    ∀ x y : Grid, ¬ x ≤ y → ¬ y ≤ x →
      |potFun x - potFun y| ≤ (gridChainLiftData.K_bw : ℤ) := by decide

/-- The bandwidth bound is **tight** — `K_bw` cannot be lowered to
`0`: there is an incomparable pair with potential gap exactly `1`. -/
theorem gridChainLiftData_bandwidth_tight :
    ∃ x y : Grid, ¬ x ≤ y ∧ ¬ y ≤ x ∧
      |potFun x - potFun y| = (gridChainLiftData.K_bw : ℤ) :=
  ⟨(0, 2), (1, 0), by decide, by decide, by decide⟩

/-- The chain potential is **non-constant** — it takes 5 distinct
values `{0,1,2,3,4}`. Contrast the constant BFS potential of
Checkpoint 3 Finding D. -/
theorem gridChainLiftData_pot_nonconstant :
    (Finset.univ.image potFun).card = 5 := by decide

/-- The sync maps are **not** `SyncMap.empty`. `f_AB` and `f_BC` are
total (full domain) and non-constant; `f_AC` is genuinely partial —
its domain is non-empty but proper (it has a real chain-tail
orphan). Contrast the rejected empty sync maps of Finding D. -/
theorem gridChainLiftData_sync_genuine :
    gridChainLiftData.fAB.domain = Finset.univ ∧
    gridChainLiftData.fBC.domain = Finset.univ ∧
    gridChainLiftData.fAB.partner (0 : Fin 3) ≠
      gridChainLiftData.fAB.partner (2 : Fin 3) ∧
    gridChainLiftData.fAC.domain.Nonempty ∧
    gridChainLiftData.fAC.domain ≠ Finset.univ ∧
    gridChainLiftData.fAC.partner (0 : Fin 3) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The orphan is genuine `X^exc_sync`, forced by `K_bw`.**
Chain-`A` index `0` has `f_AC 0 = none` *because* its chain potential
is strictly more than `K_bw` away from every element of chain `C` —
a real bandwidth-window exclusion, not an arbitrary `none`. -/
theorem gridChainLiftData_orphan_forced :
    gridChainLiftData.fAC.partner (0 : Fin 3) = none ∧
    ∀ k : Fin triple.C.length,
      (gridChainLiftData.K_bw : ℤ) <
        |potFun (triple.A.elem (0 : Fin 3)) - potFun (triple.C.elem k)| := by
  refine ⟨by decide, ?_⟩
  decide

/-- The three chains genuinely cover the 9-element ground set, each a
real length-3 chain. -/
theorem gridChainLiftData_chains_genuine :
    triple.A.length = 3 ∧ triple.B.length = 3 ∧ triple.C.length = 3 ∧
    Fintype.card Grid = 9 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  decide

/-- **F7a — SETTLED GREEN.** A concrete, non-degenerate
`ChainLiftData` for a width-3 non-chain poset *is* constructible.
`gridChainLiftData` witnesses the §4.2 §D′/§E contract conclusion
shape `∃ cld : ChainLiftData α, cld.K_bw ≤ 2`, non-degenerately
(§6 certificates). -/
theorem f7a_chainLiftData_constructible :
    ∃ cld : ChainLiftData Grid, cld.K_bw ≤ 2 :=
  ⟨gridChainLiftData, gridChainLiftData_K_bw_le_two⟩

/-! ### §7 — Corroboration: the grid admits a genuine `LayeredDecomposition`

This section is **not** the S7-F bridge (which is the general
`ChainLiftData α → LayeredDecomposition` function, Piece 3). It is a
concrete *witness* that the grid carrier is a genuine one — the
target object the bridge is meant to produce genuinely exists for
this `α`, with `w = 1 ≤ 4`. This directly refutes the worry that
`gridChainLiftData` could be a `Δ_ℓ`-style vacuous-but-inhabited
witness (`docs/state-MA-Sig-Session1.md` §11.3): for `Δ_ℓ` with
large `ℓ` no such bounded-`w` `LayeredDecomposition` exists. -/

/-- The band map `band(i,j) = i + j + 1` — the 1-indexed grid rank;
band labels run `1, …, 5`, each band an anti-diagonal antichain. -/
def gridBand : Grid → ℕ := fun p => (p.1 : ℕ) + (p.2 : ℕ) + 1

/-- Two grid elements in the same band with equal first coordinate
are equal. (Used for the `band_size ≤ 3` antidiagonal count.) -/
theorem gridBand_inj_aux :
    ∀ x y : Grid, gridBand x = gridBand y → x.1 = y.1 → x = y := by decide

/-- Same band + comparable ⇒ equal — each band is an antichain. -/
theorem gridBand_same_le_eq :
    ∀ x y : Grid, gridBand x = gridBand y → x ≤ y → x = y := by decide

/-- **The grid's genuine ground-set `LayeredDecomposition`** with
depth `K = 5` and interaction width `w = 1`. The `w = 1` is *tight*
(`w = 0` would fail `forced_lt` — e.g. `(1,0)` and `(0,2)` are
band-adjacent but incomparable). This is the exact object shape the
S7-F bridge `lem:layered-from-step7` produces from a `ChainLiftData`. -/
def gridLayered : LayeredDecomposition Grid where
  K := 5
  w := 1
  band := gridBand
  band_pos := by decide
  band_le := by decide
  band_size := by
    intro k
    refine le_trans (Finset.card_le_card_of_injOn (fun x => x.1)
      (fun _ _ => Finset.mem_univ _) ?_) (by decide)
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact gridBand_inj_aux x y (hx.2.trans hy.2.symm) hxy
  band_antichain := by
    intro k x hx y hy hne hle
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact hne (gridBand_same_le_eq x y (hx.2.trans hy.2.symm) hle)
  forced_lt := by decide
  cross_band_lt_upward := by decide

/-- The grid's genuine layered decomposition has interaction width
`w = 1 ≤ 4` — the bridge's `L.w ≤ 4` cap holds on this carrier with
room to spare. -/
theorem gridLayered_w_le_four : gridLayered.w ≤ 4 := by decide

/-- The grid carrier is genuine — it admits a `LayeredDecomposition`
with `w ≤ 4`. (Contrast `Δ_ℓ`, where no bounded-`w` layered
decomposition exists for large `ℓ`.) -/
theorem grid_admits_bounded_layered :
    ∃ L : LayeredDecomposition Grid, L.w ≤ 4 :=
  ⟨gridLayered, gridLayered_w_le_four⟩

end GridChainLift
end Step8
end OneThird
