/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.ExcBalancedLift
import OneThird.Step8.LayeredDecomposition.Compactify

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# Step 8 — S7-F bridge sub-arc Z: integration — `lem_layered_from_step7`

This file is **FULL REFACTOR Phase-2, Piece 3 (the S7-F bridge),
sub-arc Z** (work item `mg-02cd`). It is the **integration** that
completes Piece 3: it wires sub-arcs A–D together and produces the
finalised bridge theorem `lem_layered_from_step7`.

## What the bridge does (paper `lem:layered-from-step7`, `step8.tex:2009-2089`)

The S7-F bridge consumes a `ChainLiftData α` — the genuine
globalization bundle (Dilworth triple + chain potential + sync maps
+ `K_bw`) — and produces a ground-set `LayeredDecomposition` on
`X ∖ X^exc`. The re-pinned **three-cap** output (`MA-Sig §4.2 §E`,
re-pinned by `mg-faf8`; the satisfiable replacement for the
`mg-0bd1` 8th-vacuity five-cap form) is:

1. `Xexc.card ≤ C_exc T` — the exceptional set is `O_T(1)` (item (i));
2. `∀ k ∈ [1, L.K], (L.bandSet k).Nonempty` — bands non-empty
   (compactified);
3. `L.w ≤ 4` — interaction width `≤ 4` (item (ii)).

## The four sub-arcs this integration assembles

* **S7-F-A** (`ExceptionalSet.lean`, `mg-08d7`) — the exceptional set
  `Xexc cld` and the `O_T(1)` bound `Xexc_card_le` (under the named
  obligation `ExcBudget cld T`). Delivers **cap 1** of the output.
* **S7-F-B** (`SyncMaps.lean`, `mg-120d`) — the wired synchronization
  maps. Consumed *transitively*: `Xexc cld` folds in `Xexc_sync`
  (S7-F-A built from S7-F-B's orphan index sets), and `bridgeLayered`
  uses `anchor_not_refOrphan` / `fAB_defined_on_compl`.
* **S7-F-C** (`BridgeLayered.lean`, `mg-bcc9`) — `bridgeLayered`, the
  `LayeredDecomposition ↥((Xexc cld)ᶜ)` with `(L1)`–`(L4)` verified
  (under the named obligation `PotPosetMono`). Delivers **cap 3** and
  the layered structure underlying **cap 2**.
* **S7-F-D** (`ExcBalancedLift.lean`, `mg-876f`) — the exceptional-set
  perturbation lift. Consumes the bridge *output carrier* `↥(Xexcᶜ)`;
  see `excPerturbLift_of_bridge_output` for the integration boundary.

## The band-nonempty cap — `compactifySelf`

`bridgeLayered`'s band map is the chain potential normalised to a
`1`-indexed `ℕ`; its bands are potential **level sets**, which may
*skip values* (a potential image `{0, 5}` leaves bands `2, 3, 4`
empty). The re-pinned cap 2 demands every band index in `[1, K]` be
non-empty. The integration therefore post-composes the bridge output
with `LayeredDecomposition.compactifySelf` (`Compactify.lean` §6) —
the same-type empty-band compactification — which renumbers band
indices densely and preserves the interaction width `w` exactly. The
cap is then `compactifySelf_bandSet_nonempty`.

## QA — the genuinely-concrete bar (`mg-02cd` non-triviality bar)

`lem_layered_from_step7` is **genuinely concrete**:

* **No `sorry`, no new `axiom`.** `#print axioms lem_layered_from_step7`
  is `propext` / `Classical.choice` / `Quot.sound` only — the opaque
  Step-5 constant `c₁` (`ExceptionalSet.lean`) is an opaque
  *definition*, not an axiom. `AXIOMS.md` unchanged.
* **No free hypothesis beyond the documented call-site contract.** The
  hypotheses are `cld` / `hKbw` (`MA-Sig §4.2 §E`), `hMono` (the
  S7-F-C Resolution-A obligation `PotPosetMono`, paper `prop:71`), and
  `hBudget` (the S7-F-A Resolution-A obligation `ExcBudget`, paper
  item (i)). **Every one is load-bearing** — drop any and the proof
  fails. See `docs/state-S7F-Z-Session1.md` §2 for the precise status
  of the `MA-Sig §4.2 §E` `hCex` domain pin: under the Resolution-A
  design crystallised by S7-F-A/C, the `Δ_ℓ`-exclusion role of `hCex`
  is discharged by `hMono` / `hBudget` themselves (both provably fail
  on `Δ_ℓ`), so `hCex` is **not** a bridge-body input — carrying it
  unused would be an inert hypothesis. It remains the §D′/§4.3
  domain pin from which a future Piece-1 `chainLiftData_of_cascade`
  derives `cld` + `hMono` + `hBudget`.
* **No inert bounds.** `C_exc T = c₁ T + 6` is a genuine `O_T(1)`
  function; `L.w ≤ 4` reduces to the genuine `K_bw ≤ 2`
  (`lem:bandwidth`), not a literal `4 ≤ 4`; band-nonemptiness is
  *earned* by `compactifySelf`, not asserted.
* **Non-vacuous.** `hMono ∧ hBudget` is satisfiable — instantiated
  against the concrete R1 witness `gridChainLiftData` in `§3`
  (`grid_lem_layered_from_step7`); the output is a genuine
  `LayeredDecomposition` on the 8-element `Grid ∖ {(0,0)}` with
  `w = 3`, depth `K = 4`, a non-constant band map. The obligations
  genuinely *fail* for the degenerate `Δ_ℓ` family, so they are real
  soundness filters, not disguised `True`.

## Cross-references

* `lean/OneThird/Step8/ExceptionalSet.lean` — S7-F-A (`Xexc`,
  `ExcBudget`, `C_exc`, `Xexc_card_le`).
* `lean/OneThird/Step8/SyncMaps.lean` — S7-F-B (sync wiring).
* `lean/OneThird/Step8/BridgeLayered.lean` — S7-F-C (`bridgeLayered`,
  `ChainLiftData.PotPosetMono`, `bridgeLayered_w_le_four`).
* `lean/OneThird/Step8/ExcBalancedLift.lean` — S7-F-D (the
  perturbation lift, `not_isGammaCounterexample_of_exc_balanced_compl`).
* `lean/OneThird/Step8/LayeredDecomposition/Compactify.lean` §6 —
  `compactifySelf`, the band-nonempty compactification.
* `docs/state-MA-Sig-Session1.md` §4.2 §E — the pinned contract.
* `step8.tex:2009-2089` — paper `lem:layered-from-step7`.

No `sorry`. No new `axiom` (`AXIOMS.md` unchanged).
-/

namespace OneThird
namespace Step8

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]
  [DecidableLE α]

/-! ### §1 — `lem_layered_from_step7`: the finalised S7-F bridge -/

/-- **The S7-F bridge — `lem:layered-from-step7`** (`step8.tex:2009-2089`,
`MA-Sig §4.2 §E` re-pinned by `mg-faf8`). **Piece 3 of the FULL
REFACTOR, finalised.**

Given a `ChainLiftData α` `cld` with `K_bw ≤ 2` (`lem:bandwidth`) and
the two Resolution-A soundness obligations —

* `hMono : cld.PotPosetMono` — the chain potential is strictly
  increasing along every poset cover (paper `prop:71`, the S7-F-C
  named obligation);
* `hBudget : ExcBudget cld T` — the genuine `O_T(1)` cascade facts
  (paper item (i), the S7-F-A named obligation) —

the bridge produces the exceptional set `Xexc` and a
`LayeredDecomposition` on `X ∖ X^exc` satisfying the re-pinned
three-cap output:

1. `Xexc.card ≤ C_exc T` (item (i));
2. every band index in `[1, L.K]` is non-empty (compactified);
3. `L.w ≤ 4` (item (ii)).

The output `L` lives on the carrier `↥(Xexcᶜ)` — exactly the carrier
that Piece 6 (`lem_layered_balanced_full`) and the S7-F-D
perturbation lift (`not_isGammaCounterexample_of_exc_balanced_compl`)
consume; see `excPerturbLift_of_bridge_output`.

This is the **assembly** of S7-F-A (`Xexc` + the `O_T(1)` bound),
S7-F-B (sync wiring, transitively), and S7-F-C (`bridgeLayered`),
post-composed with `compactifySelf` to discharge the band-nonempty
cap. Sorry-free; no new axiom; non-vacuous (`§3`). -/
theorem lem_layered_from_step7 (T : ℕ) (cld : ChainLiftData α)
    (hKbw : cld.K_bw ≤ 2)
    (hMono : cld.PotPosetMono)
    (hBudget : ExcBudget cld T) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition ↥(Xexcᶜ)),
      Xexc.card ≤ C_exc T ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4 := by
  refine ⟨Xexc cld,
    LayeredDecomposition.compactifySelf (bridgeLayered cld hMono), ?_, ?_, ?_⟩
  · -- Cap 1 — item (i): `|X^exc| ≤ C_exc T` (S7-F-A).
    exact Xexc_card_le cld T hKbw hBudget
  · -- Cap 2 — bands non-empty: earned by `compactifySelf` (Compactify §6).
    intro k hk1 hk2
    exact LayeredDecomposition.compactifySelf_bandSet_nonempty _ hk1 hk2
  · -- Cap 3 — item (ii): `L.w ≤ 4` (S7-F-C); `compactifySelf` preserves `w`.
    rw [LayeredDecomposition.compactifySelf_w]
    exact bridgeLayered_w_le_four cld hMono hKbw

/-! ### §2 — Integration with S7-F-D: the perturbation-lift boundary

The S7-F-D perturbation lift (`ExcBalancedLift.lean`) consumes a
balanced pair on the bridge's output carrier `↥(Xexcᶜ)` and refutes
the γ-counterexample. The theorem below is the **A–D wiring**: it
threads S7-F-A's `Xexc cld` straight into S7-F-D's `↥(Tᶜ)`-carrier
lift `not_isGammaCounterexample_of_exc_balanced_compl`. The balanced
pair `hBP` is the Piece-6 hand-off — `lem_layered_balanced_full`
applied to the bridge output `L` produces exactly
`HasBalancedPair ↥((Xexc cld)ᶜ)`. Piece 6 is a separate piece of the
FULL REFACTOR, so `hBP` is left as an explicit hypothesis here; the
point of this theorem is that the **carrier types line up** — the
bridge emits, and S7-F-D consumes, the *same* `↥((Xexc cld)ᶜ)`. -/

/-- **A–D integration: the bridge output feeds the S7-F-D lift.**

Given a balanced pair on the bridge's output carrier
`↥((Xexc cld)ᶜ)` (the Piece-6 output) and the `exc_perturb` side
condition `ε ≤ γ`, the S7-F-D perturbation lift refutes the
γ-counterexample. This is the integration boundary between Piece 3
(the S7-F bridge) and S7-F-D's `lem:layered-from-step7` item (iii). -/
theorem excPerturbLift_of_bridge_output (γ : ℚ) (cld : ChainLiftData α)
    (hε : 2 * ((Xexc cld).card : ℚ)
        / (Fintype.card α - (Xexc cld).card + 1 : ℚ) ≤ γ)
    (hBP : HasBalancedPair ↥((Xexc cld)ᶜ)) :
    ¬ IsGammaCounterexample α γ :=
  not_isGammaCounterexample_of_exc_balanced_compl γ (Xexc cld) hε hBP

/-! ### §3 — Non-vacuous instantiation against the R1 witness `gridChainLiftData`

The integration acceptance certificate. The concrete `ChainLiftData`
from R1 (`gridChainLiftData` on the 3×3 grid, `ConcreteChainLiftData.lean`)
satisfies **both** Resolution-A obligations — `grid_PotPosetMono`
(S7-F-C) and `grid_excBudget` (S7-F-A) — so the finalised bridge
fires on it and the three-cap output is a genuine, non-degenerate
`LayeredDecomposition` on the 8-element ground set `Grid ∖ {(0,0)}`. -/

namespace GridChainLift

/-- **The finalised S7-F bridge, instantiated on the R1 witness.**
`lem_layered_from_step7` fires on `gridChainLiftData`: both
Resolution-A obligations hold (`grid_PotPosetMono`, `grid_excBudget`),
so the three-cap output is delivered, non-vacuously, for every `T`. -/
theorem grid_lem_layered_from_step7 (T : ℕ) :
    ∃ (Xexc : Finset (Fin 3 × Fin 3))
      (L : LayeredDecomposition ↥(Xexcᶜ)),
      Xexc.card ≤ C_exc T ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧
      L.w ≤ 4 :=
  lem_layered_from_step7 T gridChainLiftData
    gridChainLiftData_K_bw_le_two grid_PotPosetMono (grid_excBudget T)

/-- The finalised bridge output on the grid — the genuine three-cap
`LayeredDecomposition` on the 8-element `Grid ∖ {(0,0)}`. -/
noncomputable def gridLayeredFromStep7 :
    LayeredDecomposition ↥((Xexc gridChainLiftData)ᶜ) :=
  LayeredDecomposition.compactifySelf
    (bridgeLayered gridChainLiftData grid_PotPosetMono)

/-- The grid point `(0,1)`, off `X^exc = {(0,0)}`. -/
def gridQ01 : ↥((Xexc gridChainLiftData)ᶜ) :=
  ⟨(0, 1), by rw [Finset.mem_compl, grid_Xexc]; decide⟩

/-- The grid point `(2,2)`, off `X^exc = {(0,0)}`. -/
def gridQ22 : ↥((Xexc gridChainLiftData)ᶜ) :=
  ⟨(2, 2), by rw [Finset.mem_compl, grid_Xexc]; decide⟩

/-- The output interaction width is genuinely `K_bw + 2 = 3` — not the
inert cap `4`. `compactifySelf` preserves `w` exactly
(`compactifySelf_w`), and `bridgeLayered`'s `w = K_bw + 2` with the
tight `K_bw = 1`. -/
theorem gridLayeredFromStep7_w : gridLayeredFromStep7.w = 3 :=
  grid_bridgeLayered_w

/-- **The output band map is genuinely non-constant.** The grid points
`(0,1)` and `(2,2)` (both off `X^exc = {(0,0)}`) land in *different*
bands of the finalised output — the three-cap bound is tied to a real
band map, not an inert one. Proved structurally: `compactifySelf`
relabels injectively (`compactBand_inj_on_S`), so the pre-compaction
non-constancy `grid_bridgeLayered_band_nonconstant` (S7-F-C) survives. -/
theorem gridLayeredFromStep7_band_nonconstant :
    gridLayeredFromStep7.band gridQ01 ≠ gridLayeredFromStep7.band gridQ22 := by
  intro h
  have heq :
      LayeredDecomposition.compactBand
          (bridgeLayered gridChainLiftData grid_PotPosetMono) Finset.univ
          ((bridgeLayered gridChainLiftData grid_PotPosetMono).band gridQ01)
        = LayeredDecomposition.compactBand
          (bridgeLayered gridChainLiftData grid_PotPosetMono) Finset.univ
          ((bridgeLayered gridChainLiftData grid_PotPosetMono).band gridQ22) :=
    h
  have hband :=
    LayeredDecomposition.compactBand_inj_on_S
      (bridgeLayered gridChainLiftData grid_PotPosetMono) Finset.univ
      (z := ⟨gridQ01, Finset.mem_univ gridQ01⟩)
      (w := ⟨gridQ22, Finset.mem_univ gridQ22⟩) heq
  exact grid_bridgeLayered_band_nonconstant hband

/-- **The output depth is genuinely non-trivial** — `K ≥ 2`. The
8-element ground set spreads across at least two distinct,
densely-renumbered bands (`gridLayeredFromStep7_band_nonconstant`). -/
theorem gridLayeredFromStep7_K_ge_two : 2 ≤ gridLayeredFromStep7.K := by
  have hb01 := gridLayeredFromStep7.band_pos gridQ01
  have hb22 := gridLayeredFromStep7.band_pos gridQ22
  have hle01 := gridLayeredFromStep7.band_le gridQ01
  have hle22 := gridLayeredFromStep7.band_le gridQ22
  have hne := gridLayeredFromStep7_band_nonconstant
  omega

/-- **A–D pipeline on the R1 witness.** The grid's ground set
`Grid ∖ X^exc` has a balanced pair (S7-F-D's coordinate-swap witness),
so routing it through `excPerturbLift_of_bridge_output` — the A–D
integration boundary — refutes the `(2/9)`-counterexample. This
exercises the full Piece-3 pipeline carrier-to-carrier on the
concrete R1 witness: S7-F-A's `Xexc gridChainLiftData` is exactly the
finset S7-F-D's lift deletes. -/
theorem grid_excPerturbLift_of_bridge :
    ¬ IsGammaCounterexample (Fin 3 × Fin 3) (2 / 9) := by
  have hBP : HasBalancedPair ↥((Xexc gridChainLiftData)ᶜ) := by
    have h := hasBalancedPair_orderIso
      (complNotMemOrderIso
        ({((0 : Fin 3), (0 : Fin 3))} : Finset (Fin 3 × Fin 3))).symm
      ExcBalancedLiftGrid.gridMinusCorner_hasBalancedPair
    rwa [← grid_Xexc] at h
  refine excPerturbLift_of_bridge_output (2 / 9) gridChainLiftData ?_ hBP
  rw [grid_Xexc]
  rw [ExcBalancedLiftGrid.grid_exc_eps]

end GridChainLift

end Step8
end OneThird
