/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Step8.TheoremE

/-!
# Piece 4 (MainAssembly refactor) — Theorem E wiring

This file is the **`mg-MA-ThmE`** deliverable of FULL REFACTOR Phase 2,
Piece 4 (the `MainAssembly` proof-by-contradiction refactor). It is
**wiring only**: Theorem E itself — `cexImpliesLowBKExpansion`
(`OneThird.Step8.TheoremE`) — is already landed sorry-free and
axiom-free, so nothing here re-proves it.

## What this wires

Per the pinned Piece-4 signature contract
(`docs/state-Piece4-Sig-Session1.md`, mg-92a8, §2.4 / §4.4 / §4.8 body
step §6), the proof-by-contradiction body
`width3_one_third_two_thirds_assembled` calls Theorem E with the
argument tuple `(γ, hγ_pos, hγ_third, hP, hI, hCex, h2)` to produce the
**low-conductance witness** — a cut `S ⊆ 𝓛(P)` of bulk volume
`≥ γ·vol(𝓛(P))` and BK conductance `Φ(S) ≤ 2/(γn)`. That witness is
exactly what the Steps 1-7 cascade `stepsOneToSevenCascade`
(`mg-MA-Cascade`) consumes as its `hS` hypothesis (pinned at contract
§4.5).

`theoremE_lowConductanceWitness` is that wired call, with its conclusion
written out as the **exact** cascade-`hS` shape. It fixes the
Theorem-E → cascade boundary at one named point: `mg-MA-Body` invokes it
at body step §6 and `mg-MA-Cascade` feeds its result as `hS`, so any
future drift in `cexImpliesLowBKExpansion`'s statement is caught here
rather than at the assembly.

## Non-vacuity

`theoremE_lowConductanceWitness_nonempty` is the genuineness
certificate. It machine-checks that the wired witness is
non-degenerate: the cut `S` it produces is a genuinely *non-empty*
subset of `𝓛(P)`. Were `S` empty, the bulk-volume bound would read
`γ·vol(𝓛(P)) ≤ vol(∅) = 0`, contradicting `γ > 0` and
`vol(𝓛(P)) > 0` (`volume_univ_pos`). So this is genuine wiring of a
substantive theorem, not vacuous routing.

## References

* `step8.tex` §`sec:G1` — Theorem E (`thm:cex-implies-low-expansion`).
* `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §2.4, §4.4, §4.8.
* `OneThird.Step8.cexImpliesLowBKExpansion` — Theorem E (landed).
-/

namespace OneThird.Step8

open Finset OneThird

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- The bulk volume `vol(𝓛(P)) = |𝓛(P)|·(n−1)` of the full chamber is
strictly positive whenever `n = |α| ≥ 2`: there is always at least one
linear extension (`numLinExt_pos`, Szpilrajn) and `n − 1 ≥ 1`. -/
theorem volume_univ_pos (h2 : 2 ≤ Fintype.card α) :
    0 < volume (Finset.univ : Finset (LinearExt α)) := by
  have hcard : 0 < (Finset.univ : Finset (LinearExt α)).card := by
    rw [Finset.card_univ]; exact numLinExt_pos
  have hn1 : 0 < Fintype.card α - 1 := by omega
  simpa [volume] using Nat.mul_pos hcard hn1

/-- **Theorem E wiring** — Piece 4, `mg-MA-ThmE` (contract §4.4, body
step §6).

The wired call of Theorem E (`cexImpliesLowBKExpansion`, landed
sorry-free / axiom-free) inside the proof-by-contradiction body of
`width3_one_third_two_thirds_assembled`.

Given a width-3 indecomposable `γ`-counterexample on `n ≥ 2` elements
with `γ ∈ (0, 1/3]`, it produces the **low-conductance witness**: a cut
`S ⊆ 𝓛(P)` with

* `vol(S) ≥ γ·vol(𝓛(P))` (bulk volume), and
* `Φ(S) ≤ 2/(γn)` (low conductance).

The conclusion is written out as the exact shape the Steps 1-7 cascade
`stepsOneToSevenCascade` consumes as its `hS` hypothesis (contract
§4.5). The argument tuple `(γ, hγ_pos, hγ_third, hP, hI, hCex, h2)` is
the Theorem E signature verbatim (contract §2.4); `hI`
(`Indecomposable α`) is supplied by `decomp_reduction` (`mg-MA-MinCex`)
and `hCex` by `gamma_counterexample_of_no_BP` (`mg-MA-MinCex`) at the
`mg-MA-Body` call site. -/
theorem theoremE_lowConductanceWitness
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (hP : HasWidthAtMost α 3)
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
          ≤ (volume S : ℚ) ∧
      Phi S ≤ 2 / (γ * (Fintype.card α : ℚ)) :=
  cexImpliesLowBKExpansion γ hγ_pos hγ_third hP hI hCex h2

/-- **Genuineness certificate for the Theorem E wiring.**

The low-conductance witness produced by `theoremE_lowConductanceWitness`
is non-degenerate: the cut `S` is a genuinely non-empty subset of
`𝓛(P)`. This is forced by the bulk-volume bound — were `S` empty, the
bound would read `γ·vol(𝓛(P)) ≤ vol(∅) = 0`, which contradicts `γ > 0`
together with `vol(𝓛(P)) > 0` (`volume_univ_pos`). So the wiring
threads a witness with real content, not vacuous routing. -/
theorem theoremE_lowConductanceWitness_nonempty
    (γ : ℚ) (hγ_pos : 0 < γ) (hγ_third : γ ≤ 1 / 3)
    (hP : HasWidthAtMost α 3)
    (hI : OneThird.Mathlib.Poset.Indecomposable α)
    (hCex : IsGammaCounterexample α γ)
    (h2 : 2 ≤ Fintype.card α) :
    ∃ S : Finset (LinearExt α),
      S.Nonempty ∧
      γ * (volume (Finset.univ : Finset (LinearExt α)) : ℚ)
          ≤ (volume S : ℚ) ∧
      Phi S ≤ 2 / (γ * (Fintype.card α : ℚ)) := by
  obtain ⟨S, hbulk, hcond⟩ :=
    theoremE_lowConductanceWitness γ hγ_pos hγ_third hP hI hCex h2
  refine ⟨S, ?_, hbulk, hcond⟩
  -- The bulk bound forces `0 < vol(S)`, hence `S` is non-empty.
  have hvu : (0 : ℚ) < (volume (Finset.univ : Finset (LinearExt α)) : ℚ) := by
    exact_mod_cast volume_univ_pos h2
  have hbulk_pos : (0 : ℚ) < (volume S : ℚ) :=
    lt_of_lt_of_le (mul_pos hγ_pos hvu) hbulk
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [volume] at hbulk_pos
  · exact hne

end OneThird.Step8
