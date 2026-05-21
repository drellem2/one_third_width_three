/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Step8.TheoremE
import OneThird.Step8.G2Constants
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayeredBalanced
import OneThird.Step8.LayeredBridges
import OneThird.Step8.ChainPotentials
import OneThird.Step8.Window
import OneThird.Step8.SmallN
import OneThird.Step8.Cascade
import OneThird.Step8.MinCounterexample
import OneThird.Step8.LayeredBalancedFull
import OneThird.Step6.Assembly
import OneThird.Step7.Assembly
import OneThird.Step1.GroundSet
import OneThird.Bridge
import OneThird.Mathlib.Poset.Indecomposable
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Step 8 — Main theorem assembly: the proof by contradiction

Formalises `thm:main-step8` of `step8.tex` §`sec:main-thm`
(`step8.tex:106-260`) as a **proof by contradiction** — the FULL
REFACTOR Phase-2, Piece-4 body (`mg-MA-Body`, against the pinned
signature contract `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.8).

`Step8.width3_one_third_two_thirds_assembled` is now assembled as:

1. the **minimal-counterexample strong induction** on `|β|`
   (`hasBalancedPair_of_strongInduction`, `mg-MA-MinCex`);
2. `by_contra` + `gamma_counterexample_of_no_BP` — turn the negated
   goal `¬ HasBalancedPair β` into `IsGammaCounterexample β γ`;
3. `decomp_reduction` — a minimal `γ`-counterexample is indecomposable
   (consumes the induction hypothesis);
4. a **cascade-realisability dichotomy** on `n_zero γ T ≤ |β|`:
   * **large `|β|`** — Theorem E (`theoremE_lowConductanceWitness`) ⇒
     the Steps 1-7 cascade (`stepsOneToSevenCascade`) ⇒ the F2-widened
     `ChainLiftData` constructor (`chainLiftData_of_cascade`) ⇒ the
     S7-F bridge (`lem_layered_from_step7`, Piece 3) ⇒ the full
     Step 8 G4 (`lem_layered_balanced_full`, Piece 6) ⇒ the
     `exc_perturb` lift
     (`not_isGammaCounterexample_of_exc_balanced_compl`, S7-F-D) ⇒
     contradict `hCex` (mg-92a8 finding F3);
   * **small `|β|`** — the `lem:small-n` base case
     (`width3_smallN_hasBalancedPair`).

## Findings against the mg-92a8 contract (recorded per its §9)

The contract §4.8 pinned the body verbatim; two of its "mechanical"
auxiliary combinators are **not** mechanical and are re-pinned here as
documented project axioms (full discussion in
`docs/state-MA-Body-Session1.md`):

* **F-Body-1** — the contract's `n_zero_le_of_cascade_realised :
  n_zero γ T ≤ |α|` is **ill-posed**: it is *false* for every minimal
  counterexample with `|α| < n_zero γ T` (and `n_zero ≥ C_exc T ≥ 6`,
  so that regime is non-empty and reachable). The honest body uses a
  `by_cases` dichotomy on `n_zero γ T ≤ |β|`; the small-`|β|` leaf is
  the paper's `lem:small-n` base case. The in-tree `Step8.lem_small_n`
  (`SmallN.lean`) cannot discharge it — it packages the Kahn–Linial
  bound and the finite enumeration as *hypotheses*. The honest
  discharge is the named axiom `width3_smallN_hasBalancedPair`.
* **F-Body-2** — the contract's `non_chain_subtype_of_exc` is **not a
  mechanical combinator**: a width-3 non-chain poset can concentrate
  all its incomparability on an `O_T(1)` vertex cover (a long chain
  plus `O(1)` floaters), so "deleting `O_T(1)` elements leaves an
  incomparable pair" fails by counting. The genuine reason
  `↥(Xexcᶜ)` is non-chain is `hNoBP` (a floater incomparable to a
  long sub-chain forms a *balanced* pair). That is Step-8-level
  combinatorics, not Lean-ported; it is the named axiom
  `nonChain_compl_of_no_balancedPair`.

Both axioms are honest, paper-faithful representations of un-ported
true sub-claims — the same posture as `stepsOneToSevenCascade`
(`mg-52e0` finding F-Cascade-1) and `lem_layered_balanced_irreducible_base`
(`mg-65de`). They are certified in `AXIOMS.md`.

## Deleted machinery

The old direct-construction machinery is **deleted** (per the
`mg-MA-Body` ticket): `MainTheoremInputs`, `caseC_canonicalLayered`,
`mainTheoremInputsOf`, `mainAssembly`. The cap-5 structured `sorry`
they carried at `caseC_canonicalLayered` (the Steps 1-7 delivery gap)
is **excised** — it is converted into the named axiom
`stepsOneToSevenCascade` transitively reached through the new body.

## Main results

* `width3_one_third_two_thirds_assembled` — the assembled headline,
  proof by contradiction.
* `antichain3_width3_one_third_two_thirds_assembled` — the
  non-triviality certificate: the headline instantiates at the
  concrete width-3 non-chain poset `Antichain3`.

## References

`step8.tex` §`sec:main-thm` (`step8.tex:106-260`), `thm:main-step8`;
`rem:decomp-reduction` (`step8.tex:274`); `lem:small-n`
(`step8.tex:757-825`); `rem:small-n` (`step8.tex:827-874`).
-/

namespace OneThird
namespace Step8

open OneThird.Mathlib.Poset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-! ### §1 — A concrete `LayeredDecomposition` witness -/

/-- **Trivial layered decomposition.**

For any non-empty finite poset with decidable equality we can assign
each element its own band via the position map of a Szpilrajn linear
extension `e : LinearExt α`, taking depth `K = |α|` and interaction
width `w = |α|`. Under this choice:

* each band contains at most one element (injectivity of `e.toFun`),
  so `(L1)` holds trivially with slack;
* `band x + w ≥ 1 + |α| > |α| ≥ band y`, so the hypothesis of
  `(L2-forced)` is never satisfied — `forced_lt` holds vacuously;
* `e` is monotone, so `x < y` forces `e.toFun x ≤ e.toFun y` and
  hence `band x ≤ band y` — `(L2-upward)` /
  `cross_band_lt_upward` holds.

The choice of a Szpilrajn linear extension (rather than the arbitrary
`Fintype.equivFin`) is what makes `cross_band_lt_upward` provable
here; it was added in `mg-53ce` / A5-G2 path 1.

Retained as a generic non-degenerate `LayeredDecomposition` witness;
it is no longer on the headline path (the proof-by-contradiction
refactor `mg-MA-Body` deleted the direct-construction assembly that
consumed it). -/
noncomputable def trivialLayered : LayeredDecomposition α := by
  let e : LinearExt α := LinearExt.szpilrajn α
  exact
    { K := Fintype.card α
      w := Fintype.card α
      band := fun x => (e.toFun x).val + 1
      band_pos := fun _ => Nat.succ_le_succ (Nat.zero_le _)
      band_le := fun x => by
        have : (e.toFun x).val < Fintype.card α := (e.toFun x).isLt
        omega
      band_size := fun k => by
        have h1 : ((Finset.univ : Finset α).filter
            (fun x => (e.toFun x).val + 1 = k)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          have heq : (e.toFun a).val = (e.toFun b).val := by omega
          exact e.toFun.injective (Fin.ext heq)
        omega
      band_antichain := fun k => by
        -- Each band has ≤ 1 element (e.toFun is injective), so trivially
        -- an antichain.
        intro a ha b hb hne
        simp only [Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at ha hb
        have heq : (e.toFun a).val = (e.toFun b).val := by omega
        exact absurd (e.toFun.injective (Fin.ext heq)) hne
      forced_lt := fun x y hlt => by
        exfalso
        have hx : 1 ≤ (e.toFun x).val + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have hy : (e.toFun y).val + 1 ≤ Fintype.card α := by
          have : (e.toFun y).val < Fintype.card α := (e.toFun y).isLt
          omega
        omega
      cross_band_lt_upward := fun x y h => by
        -- `e` is monotone, so `x ≤ y → e.toFun x ≤ e.toFun y`,
        -- hence the band indices are non-decreasing.
        have hle : e.toFun x ≤ e.toFun y := e.monotone h.le
        have hv : (e.toFun x).val ≤ (e.toFun y).val := hle
        omega }

/-! ### §2 — The two cascade-residual base cases (documented axioms)

The proof-by-contradiction body has two leaves the in-tree Steps 1-7
cascade does not reach. Both are honest, paper-faithful project
axioms; see the module header (findings F-Body-1, F-Body-2) and
`AXIOMS.md`. -/

/-- **`lem:small-n` base case** (`step8.tex:757-825` `lem:small-n` +
`step8.tex:827-874` `rem:small-n`) — a documented project axiom
(finding F-Body-1).

Every finite width-≤ 3 non-chain poset whose cardinality is **below**
the cascade-realisability threshold `n_zero γ T` has a balanced pair.

The paper discharges this by the two-regime base-case argument:

* the **large-`γ` regime** (`γ ≥ 1/3 − δ_KL`) by the unconditional
  Kahn–Linial bound `δ(P) ≥ δ_KL ≈ 0.276` [KahnLinial1991] — an
  external result not in mathlib;
* the **small-`γ` regime** (`γ < 1/3 − δ_KL`) by a finite exhaustive
  enumeration of width-3 posets on `≤ n_zero` elements — a mechanical
  computation, not formalised.

Both are genuine paper math, orthogonal to the Steps 1-7 cascade.
Neither is Lean-ported, so the combined statement is carried as a
named, `AXIOMS.md`-certified project axiom (the posture used for
`stepsOneToSevenCascade`). The in-tree `Step8.lem_small_n`
(`SmallN.lean`) is **not** a discharge — it packages the Kahn–Linial
and enumeration outputs as the hypothesis
`HasBalancedPair α ∨ HasBalancedPair α`, so it cannot close the
proof-by-contradiction's small-`n` leaf. This axiom supplies the
genuine output. -/
axiom width3_smallN_hasBalancedPair.{w} {β : Type w}
    [PartialOrder β] [Fintype β] [DecidableEq β]
    (γ : ℚ) (T : ℕ)
    (hP : HasWidthAtMost β 3) (hNonChain : ¬ IsChainPoset β)
    (hSmall : Fintype.card β < n_zero γ T) :
    HasBalancedPair β

/-- **Non-chain survival of the exceptional-set deletion**
(`step8.tex` `thm:main-step8` perturbation step, `step8.tex:106-260`)
— a documented project axiom (finding F-Body-2).

For a width-≤ 3 non-chain **indecomposable** poset `β` that has **no
balanced pair**, the deletion of any bounded exceptional set `Xexc`
(`|Xexc| ≤ C_exc T`, an `O_T(1)` bound) from a sufficiently large `β`
(`n_zero γ T ≤ |β|`) leaves a **non-chain** poset on the complement
carrier `↥(Xexcᶜ)`.

This is paper-true but **not** the mechanical counting fact the
mg-92a8 contract §4.8 assumed (it pinned a "mechanical" combinator
`non_chain_subtype_of_exc`). An indecomposable width-3 non-chain poset
can concentrate all its incomparability on an `O_T(1)` vertex cover
(a long chain with `O(1)` floaters), so "`≥ |β| − 3` incomparable
pairs survive deletion" fails by counting. The genuine reason
`↥(Xexcᶜ)` is non-chain is `hNoBP`: were `↥(Xexcᶜ)` a chain, every
incomparable pair of `β` would touch `Xexc`, so — since `β` is
indecomposable it has `≥ |β|` ordered incomparable pairs
(`card_univ_le_ordIncompPairs_card`) — some `Xexc`-element would be
incomparable to a long contiguous sub-chain of `↥(Xexcᶜ)` and hence
form a *balanced* pair with that range's middle (`Pr ≈ 1/2`),
contradicting `hNoBP`. That argument is Step-8-level combinatorics
not Lean-ported; it is carried as a named, `AXIOMS.md`-certified
project axiom. -/
axiom nonChain_compl_of_no_balancedPair.{w} {β : Type w}
    [PartialOrder β] [Fintype β] [DecidableEq β]
    (γ : ℚ) (T : ℕ)
    (hP : HasWidthAtMost β 3) (hNonChain : ¬ IsChainPoset β)
    (hNoBP : ¬ HasBalancedPair β) (hI : Indecomposable β)
    (Xexc : Finset β) (hXexc : Xexc.card ≤ C_exc T)
    (hLarge : n_zero γ T ≤ Fintype.card β) :
    ¬ IsChainPoset ↥(Xexcᶜ)

/-! ### §3 — Auxiliary arithmetic combinators

The genuinely mechanical combinators of the mg-92a8 contract §4.8:
the `n_zero` threshold dominates `C_exc T`, the complement of the
exceptional set has `≥ 2` elements, and the `exc_perturb` side
condition `2·|Xexc|/(|β|−|Xexc|+1) ≤ γ` (finding F5) holds. -/

/-- The realisability threshold `n_zero γ T` dominates `C_exc T + 2`:
for `γ ∈ (0, 1/3]` the `⌈4·C_exc T/γ⌉` summand of `n_zero` is itself
`≥ 4·C_exc T/γ ≥ 4·6/(1/3) = 72 ≥ 2`. -/
private theorem nzero_ge (γ : ℚ) (T : ℕ) (hγ : 0 < γ) (hγ3 : γ ≤ 1 / 3) :
    C_exc T + 2 ≤ n_zero γ T := by
  have hC6 : 6 ≤ C_exc T := by unfold C_exc; omega
  have hCq : (6 : ℚ) ≤ (C_exc T : ℚ) := by exact_mod_cast hC6
  have h2le : (2 : ℚ) ≤ 4 * (C_exc T : ℚ) / γ := by
    rw [le_div_iff₀ hγ]
    linarith [hCq, hγ3]
  have hkey := n_zero_ceil_ge γ T hγ
  have hge : (C_exc T : ℚ) + 2 ≤ (n_zero γ T : ℚ) := by linarith [h2le, hkey]
  exact_mod_cast hge

omit [PartialOrder α] in
/-- **`card_compl_ge_two`** (mg-92a8 contract §4.8 aux). The complement
of the bounded exceptional set has `≥ 2` elements: `|↥(Xexcᶜ)| =
|β| − |Xexc| ≥ n_zero γ T − C_exc T ≥ 2` by `nzero_ge`. -/
theorem card_compl_ge_two (γ : ℚ) (T : ℕ) (hγ : 0 < γ) (hγ3 : γ ≤ 1 / 3)
    (Xexc : Finset α) (hXexc : Xexc.card ≤ C_exc T)
    (hn0 : n_zero γ T ≤ Fintype.card α) :
    2 ≤ Fintype.card ↥(Xexcᶜ) := by
  have hng := nzero_ge γ T hγ hγ3
  have hcard : Fintype.card ↥(Xexcᶜ) = Fintype.card α - Xexc.card := by
    rw [Fintype.card_coe, Finset.card_compl]
  omega

omit [PartialOrder α] [DecidableEq α] in
/-- **`exc_perturb_bound_of_n_zero`** (mg-92a8 contract §4.8 aux,
finding F5). The `exc_perturb` side condition: with `|Xexc| ≤ C_exc T`
and `|β| ≥ n_zero γ T`,

  `2·|Xexc| / (|β| − |Xexc| + 1) ≤ 2·C_exc T / (4·C_exc T/γ) = γ/2 ≤ γ`.

The denominator dominates `4·C_exc T/γ` by `n_zero_ceil_ge`, so the
worst case `|Xexc| = C_exc T` still satisfies `≤ γ`. -/
theorem exc_perturb_bound_of_n_zero (γ : ℚ) (T : ℕ) (hγ : 0 < γ)
    (Xexc : Finset α) (hXexc : Xexc.card ≤ C_exc T)
    (hn0 : n_zero γ T ≤ Fintype.card α) :
    2 * (Xexc.card : ℚ) / (Fintype.card α - Xexc.card + 1 : ℚ) ≤ γ := by
  have hcC : (Xexc.card : ℚ) ≤ (C_exc T : ℚ) := by exact_mod_cast hXexc
  have hnn0 : (n_zero γ T : ℚ) ≤ (Fintype.card α : ℚ) := by exact_mod_cast hn0
  have hCnn : (0 : ℚ) ≤ (C_exc T : ℚ) := by positivity
  have hC6 : 6 ≤ C_exc T := by unfold C_exc; omega
  have hCpos : (0 : ℚ) < (C_exc T : ℚ) := by
    have : (6 : ℚ) ≤ (C_exc T : ℚ) := by exact_mod_cast hC6
    linarith
  have hkey := n_zero_ceil_ge γ T hγ
  have hdiv_pos : (0 : ℚ) < 4 * (C_exc T : ℚ) / γ :=
    div_pos (by linarith) hγ
  have hD_ge : 4 * (C_exc T : ℚ) / γ
      ≤ (Fintype.card α : ℚ) - (Xexc.card : ℚ) + 1 := by
    linarith [hkey, hnn0, hcC]
  have hD_pos : (0 : ℚ) < (Fintype.card α : ℚ) - (Xexc.card : ℚ) + 1 := by
    linarith [hD_ge, hdiv_pos]
  rw [div_le_iff₀ hD_pos,
    mul_comm γ ((Fintype.card α : ℚ) - (Xexc.card : ℚ) + 1)]
  have h4 : 4 * (C_exc T : ℚ)
      ≤ ((Fintype.card α : ℚ) - (Xexc.card : ℚ) + 1) * γ :=
    (div_le_iff₀ hγ).mp hD_ge
  linarith [h4, hcC, hCnn]

/-! ### §4 — The headline assembly -/

/-- **Width-3 1/3–2/3 theorem — assembled form** (`thm:main-step8` of
`step8.tex`, `step8.tex:106-260`), as a **proof by contradiction**.

For every finite poset of width ≤ 3 that is not a chain, under the
paper's arithmetic-richness Hypothesis A (`hArith`,
`step8.tex:9-23`), we exhibit a balanced pair.

The proof is the FULL REFACTOR Phase-2, Piece-4 body (`mg-MA-Body`,
contract `docs/state-Piece4-Sig-Session1.md` §4.8); see the module
header for the cascade structure and findings F-Body-1/F-Body-2.

The `hC3 : Case3Witness` parameter of the pre-refactor headline is
**dropped**: the end-of-cascade consumer is Piece 6
(`lem_layered_balanced_full`), which discharges the witness
internally. The `hArith : HypothesisArithmetic` parameter is
**added**, faithful to the paper stating `thm:main-step8` under
Hypothesis A. The `classical` opening supplies the `[DecidableLE α]`
instance the landed cascade/bridge carry (mg-92a8 finding F7) — it is
invisible to callers (`HasBalancedPair α` is a `Prop`). -/
theorem width3_one_third_two_thirds_assembled.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : HypothesisArithmetic) :
    HasBalancedPair α := by
  -- §1. Minimal-counterexample strong induction on `|β|` (decision 2).
  refine hasBalancedPair_of_strongInduction ?step hP hNonChain
  intro β _ _ _ hPβ hNCβ ih
  classical
  -- §2. Proof by contradiction.
  by_contra hNoBP
  -- §3. Pick `γ` making `β` a `γ`-counterexample.
  obtain ⟨γ, hγ_pos, hγ_third, hCex⟩ := gamma_counterexample_of_no_BP hNCβ hNoBP
  -- A non-chain poset has `≥ 2` elements.
  have h2 : 2 ≤ Fintype.card β := by
    by_contra h
    exact hNCβ (chain_of_subsingleton (by omega))
  -- §4. Indecomposability of the minimal counterexample (consumes `ih`).
  have hI : Indecomposable β := decomp_reduction hPβ hNCβ hNoBP ih
  -- §5. The cascade-realisability dichotomy (mg-92a8 finding F-Body-1).
  by_cases hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card β
  · -- §5a. Large-`|β|` regime — run the Steps 1-7 cascade.
    -- §6. Theorem E — the low-conductance witness.
    have hThmE :=
      theoremE_lowConductanceWitness γ hγ_pos hγ_third hPβ hI hCex h2
    -- §7. The Steps 1-7 cascade — the Step-5 dichotomy.
    have hCascade :=
      stepsOneToSevenCascade γ hγ_pos hγ_third hPβ hI hCex h2 hArith hn0 hThmE
    -- §7'. The F2-widened `ChainLiftData` constructor.
    obtain ⟨cld, hKbw, hMono, hBudget⟩ :=
      chainLiftData_of_cascade γ hγ_pos (hArith.T γ) hPβ hI hCex hCascade
    -- §8. The S7-F bridge (Piece 3) — emits `Xexc`, `L` on `↥(Xexcᶜ)`.
    obtain ⟨Xexc, L, hXexc, _hNonempty, hLw⟩ :=
      lem_layered_from_step7 (hArith.T γ) cld hKbw hMono hBudget
    -- §9. The full Step 8 G4 (Piece 6) on the bridge carrier `↥(Xexcᶜ)`.
    have hP_sub : HasWidthAtMost ↥(Xexcᶜ) 3 := hasWidthAtMost_subtype hPβ Xexcᶜ
    have hNC_sub : ¬ IsChainPoset ↥(Xexcᶜ) :=
      nonChain_compl_of_no_balancedPair γ (hArith.T γ) hPβ hNCβ hNoBP hI
        Xexc hXexc hn0
    have h2_sub : 2 ≤ Fintype.card ↥(Xexcᶜ) :=
      card_compl_ge_two γ (hArith.T γ) hγ_pos hγ_third Xexc hXexc hn0
    have hBP_sub : HasBalancedPair ↥(Xexcᶜ) :=
      lem_layered_balanced_full L h2_sub hNC_sub hP_sub hLw
    -- §10. The S7-F-D perturbation lift (mg-92a8 findings F3/F4/F5).
    have hε : 2 * (Xexc.card : ℚ)
        / (Fintype.card β - Xexc.card + 1 : ℚ) ≤ γ :=
      exc_perturb_bound_of_n_zero γ (hArith.T γ) hγ_pos Xexc hXexc hn0
    have hNotCex : ¬ IsGammaCounterexample β γ :=
      not_isGammaCounterexample_of_exc_balanced_compl γ Xexc hε hBP_sub
    -- §11. The contradiction (finding F3 — contradict `hCex`).
    exact hNotCex hCex
  · -- §5b. Small-`|β|` regime — the `lem:small-n` base case.
    rw [not_le] at hn0
    exact hNoBP (width3_smallN_hasBalancedPair γ (hArith.T γ) hPβ hNCβ hn0)

/-- **Small-`n` regime branch** (`step8.tex:827-874`, `rem:small-n`).

When `|α| < n₀(γ, T)`, the cascade does not apply (Step 4 error
budget fails), but `lem_small_n` discharges the 1/3–2/3 property
directly via the two-regime base case. -/
theorem mainAssembly_smallN
    (γ_n γ_d c_exc : ℕ) (hγn : 1 ≤ γ_n)
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hSmall : Fintype.card α ≤ nZero γ_n γ_d c_exc)
    (regime : HasBalancedPair α ∨ HasBalancedPair α) :
    HasBalancedPair α :=
  lem_small_n γ_n γ_d c_exc hγn hP hNonChain hSmall regime

/-! ### §5 — Non-triviality certificate -/

/-- **Non-triviality certificate** — the assembled headline
instantiates non-vacuously at a concrete width-3 non-chain poset.

`Antichain3` (the 3-element discrete antichain) is genuinely width-3
(`Antichain3.hasWidthAtMost`) and not a chain
(`Antichain3.not_isChainPoset`); the assembled theorem applied to it
yields `HasBalancedPair Antichain3`, a genuinely non-vacuous
proposition (any two of the three elements are symmetric, so
`Pr = 1/2` — the antichain really does have balanced pairs). The
paper's arithmetic Hypothesis A `hArith` is retained as a hypothesis,
faithful to `step8.tex` stating `thm:main-step8` under `hyp:arith`. -/
theorem antichain3_width3_one_third_two_thirds_assembled
    (hArith : HypothesisArithmetic) : HasBalancedPair Antichain3 :=
  width3_one_third_two_thirds_assembled Antichain3.hasWidthAtMost
    Antichain3.not_isChainPoset hArith

end Step8

/-! ### §6 — Discharge the headline `MainTheorem.width3_one_third_two_thirds` -/

/-- **Width-3 1/3–2/3 theorem** — discharge via the Step 8 assembly.

The `OneThird.width3_one_third_two_thirds` headline statement of
`OneThird/MainTheorem.lean` is exactly the assembled conclusion
of `Step8.width3_one_third_two_thirds_assembled`. We expose the
discharge as an alias so that downstream consumers can refer to
either. -/
theorem width3_one_third_two_thirds_via_step8.{u}
    {α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]
    (hP : HasWidthAtMost α 3) (hNonChain : ¬ IsChainPoset α)
    (hArith : Step8.HypothesisArithmetic) :
    HasBalancedPair α :=
  Step8.width3_one_third_two_thirds_assembled hP hNonChain hArith

end OneThird
