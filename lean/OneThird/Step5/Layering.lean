/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Step 5 — Activation absorption and global layering

Formalises §§5 G5 of `step5.tex`, together with the cyclic-compatibility
sub-lemma (`lem:cyclic-compat`, `step5.tex:704`) that carries the
content of G5.

## Setup

Fix three chain index ranges `A = Fin p`, `B = Fin q`, `C = Fin r`.
Each of the three bipartite incomparability relations has an "interval
form" supplied by `lem:interval-form` (`step5.tex:35`):

* `IC(a_i) = [alphaAC i, betaAC i]` on `C`, with `alphaAC, betaAC : Fin p → ℤ`;
* `IC(b_j) = [gammaBC j, deltaBC j]` on `C`, with `gammaBC, deltaBC : Fin q → ℤ`.

The hypothesis of `lem:global-layering` (`step5.tex:670-686`) is that
these intervals lie in `K`-bands around monotone "envelope" maps
`f_AC : Fin p → ℤ`, `f_BC : Fin q → ℤ`: captured by the `InBand`
predicate below.

## Content

* `InBand` — the band hypothesis of `lem:global-layering`.
* `IntervalsTouch` — the key combinatorial fact discharged in Step 1
  of the paper proof of `lem:cyclic-compat` (`step5.tex:723-736`):
  if `a_i ∥ b_j` and both `IC(a_i), IC(b_j) ≠ ∅`, then the intervals
  `[alpha_i, beta_i]` and `[gamma_j, delta_j]` "touch" on `C`, i.e.
  `alpha_i ≤ delta_j + 1` and `gamma_j ≤ beta_i + 1`.
* `cyclic_compat` — the cyclic-compatibility lemma, main content of G5
  (`step5.tex:704-753`, Step 2 *"band bracketing"*). From `InBand` for
  both relations and `IntervalsTouch`, conclude
  `|f_AC(i) − f_BC(j)| ≤ 2K + 1`.
* `case_AC`, `case_BC` — the pointwise height bounds of Cases 1–2 of
  `lem:global-layering` (`step5.tex:774-782`): height differences on
  incomparable `A`–`C` and `B`–`C` pairs are at most `K`.
* `global_layering_bound_AB` — Case 3 of `lem:global-layering`
  (`step5.tex:784-805`, non-empty-interval branch): height difference
  on incomparable `A`–`B` pairs is at most `2K + 1`.
* `activation_absorb` — G4-closure packaging: the per-pair bulk mass
  lower bound of `lem:fiber-mass` (supplied by `FiberMass.lean`)
  remains valid after absorbing the activation band; the only change
  is an inflation of the band width by an additive `O(K)`, which is
  invisible in the structural statement.
-/

namespace OneThird
namespace Step5

/-! ### Band hypothesis (`step5.tex:676-682`) -/

section Band

variable {p q r : ℕ}

/-- **Band containment** (`step5.tex:676-682`, hypothesis (i)).

The interval `[alpha i, beta i]` lies inside the `K`-band around
`f i`, pointwise in `i`. In the paper notation with
`IC(a_i) = [alpha_i, beta_i]`,

  `IC(a_i) ⊆ [f(i) − K, f(i) + K]`.

When `IC(a_i) = ∅` the two inequalities trivially hold — this is how
the paper handles degenerate cases (`step5.tex:785-813`): the
interval is "empty" in the sense that `alpha i > beta i`, so both
`alpha i` and `beta i` can be placed inside the band vacuously. We
state the predicate in its non-vacuous form — the caller is
responsible for providing endpoints consistent with the
`lem:interval-form` convention. -/
def InBand (alpha beta : Fin p → ℤ) (f : Fin p → ℤ) (K : ℤ) : Prop :=
  ∀ i, f i - K ≤ alpha i ∧ beta i ≤ f i + K

end Band

/-! ### `lem:cyclic-compat` (`step5.tex:704`) -/

section CyclicCompat

variable {p q : ℕ}

/-- **Intervals touch on `C`** (`step5.tex:723-736`, Step 1 of the
paper proof of `lem:cyclic-compat`).

Abstract form: for `a_i ∥ b_j` with both `IC(a_i), IC(b_j) ≠ ∅`,
the two integer intervals `[alpha_i, beta_i]` and `[gamma_j, delta_j]`
on the reference chain `C` *touch*:

  `alpha_i ≤ delta_j + 1` and `gamma_j ≤ beta_i + 1`.

The proof in the paper uses the interval-form partition
`C = L_C ⊔ IC ⊔ U_C` for each of `a_i, b_j` together with
transitivity of the poset: a chain element sandwiched between `beta_i`
and `gamma_j` would force `a_i < c_k < b_j`, contradicting
incomparability. The conclusion is a purely arithmetic statement on
the interval endpoints, which we take as the hypothesis of
`cyclic_compat` — its derivation from the poset context lives in the
downstream Step 6 / Step 7 assembly (where poset-level incomparability
inputs are available), *not* in the pure interval-geometry core of
Step 5. -/
def IntervalsTouch (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ)
    (i : Fin p) (j : Fin q) : Prop :=
  alpha i ≤ delta j + 1 ∧ gamma j ≤ beta i + 1

/-- **`lem:cyclic-compat`** (`step5.tex:704`, Step 2 of the paper proof).

From the band hypotheses `InBand alpha beta fAC K` and
`InBand gamma delta fBC K`, together with `IntervalsTouch` at `(i, j)`,
conclude

  `|fAC(i) − fBC(j)| ≤ 2K + 1`.

Proof (`step5.tex:742-752`). From `gamma_j ≤ beta_i + 1` and the
two band inequalities `fBC(j) − K ≤ gamma_j`, `beta_i ≤ fAC(i) + K`,
we chain:

  `fBC(j) − K ≤ gamma_j ≤ beta_i + 1 ≤ fAC(i) + K + 1`,

which gives `fBC(j) − fAC(i) ≤ 2K + 1`. The symmetric bound from
`alpha_i ≤ delta_j + 1` yields `fAC(i) − fBC(j) ≤ 2K + 1`. -/
theorem cyclic_compat
    (alpha beta : Fin p → ℤ) (gamma delta : Fin q → ℤ)
    (fAC : Fin p → ℤ) (fBC : Fin q → ℤ) (K : ℤ)
    (hAC : InBand alpha beta fAC K)
    (hBC : InBand gamma delta fBC K)
    {i : Fin p} {j : Fin q}
    (touch : IntervalsTouch alpha beta gamma delta i j) :
    |fAC i - fBC j| ≤ 2 * K + 1 := by
  obtain ⟨hαl, hβu⟩ := hAC i
  obtain ⟨hγl, hδu⟩ := hBC j
  obtain ⟨hαδ, hγβ⟩ := touch
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- fAC i - fBC j ≥ -(2K+1): use alpha_i ≤ delta_j + 1 and the two bands
    linarith
  · -- fAC i - fBC j ≤ 2K+1: use gamma_j ≤ beta_i + 1 and the two bands
    linarith

end CyclicCompat

/-! ### Cases of `lem:global-layering` (`step5.tex:774-805`) -/

section GlobalLayering

variable {p q r : ℕ}

/-- **Case 1 of `lem:global-layering`** (`step5.tex:774-776`).

If `c_k ∈ IC(a_i)`, i.e. `alpha i ≤ k ≤ beta i`, and `IC(a_i)` lies in
the `K`-band around `fAC(i)`, then `|fAC(i) − k| ≤ K`. -/
theorem case_AC
    (alpha beta : Fin p → ℤ) (fAC : Fin p → ℤ) (K : ℤ)
    (hAC : InBand alpha beta fAC K)
    (i : Fin p) (k : ℤ)
    (hk : alpha i ≤ k ∧ k ≤ beta i) :
    |fAC i - k| ≤ K := by
  obtain ⟨hαl, hβu⟩ := hAC i
  obtain ⟨hl, hu⟩ := hk
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-- **Case 2 of `lem:global-layering`** (`step5.tex:779-781`).

Same as `case_AC`, with `(A, a_i, fAC)` replaced by `(B, b_j, fBC)`.
Symmetric argument. -/
theorem case_BC
    (gamma delta : Fin q → ℤ) (fBC : Fin q → ℤ) (K : ℤ)
    (hBC : InBand gamma delta fBC K)
    (j : Fin q) (k : ℤ)
    (hk : gamma j ≤ k ∧ k ≤ delta j) :
    |fBC j - k| ≤ K := by
  obtain ⟨hγl, hδu⟩ := hBC j
  obtain ⟨hl, hu⟩ := hk
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-- **Case 3 of `lem:global-layering`** (`step5.tex:784-805`,
non-empty interval branch).

For an incomparable `A`–`B` pair `(a_i, b_j)` with both
`IC(a_i) ≠ ∅` and `IC(b_j) ≠ ∅`, the pairwise height difference
`|fAC(i) − fBC(j)|` is at most `2K + 1`. This is exactly the content
of `cyclic_compat`. -/
theorem global_layering_bound_AB
    (alphaAC betaAC : Fin p → ℤ) (gammaBC deltaBC : Fin q → ℤ)
    (fAC : Fin p → ℤ) (fBC : Fin q → ℤ) (K : ℤ)
    (hAC : InBand alphaAC betaAC fAC K)
    (hBC : InBand gammaBC deltaBC fBC K)
    {i : Fin p} {j : Fin q}
    (touch : IntervalsTouch alphaAC betaAC gammaBC deltaBC i j) :
    |fAC i - fBC j| ≤ 2 * K + 1 :=
  cyclic_compat alphaAC betaAC gammaBC deltaBC fAC fBC K hAC hBC touch

/-- **`lem:global-layering` — structural conclusion, packaged**
(`step5.tex:670`).

The three pointwise height-difference bounds for incomparable pairs
coming from `A`, `B`, `C`:

* Case 1 (`A`–`C`): height difference `≤ K`;
* Case 2 (`B`–`C`): height difference `≤ K`;
* Case 3 (`A`–`B`, non-empty intervals): height difference `≤ 2K + 1`.

Since `K ≤ 2K + 1` for `K ≥ 0` (the relevant regime), the universal
bound `|h(x) − h(y)| ≤ 2K + 1` claimed in
`lem:global-layering` follows immediately. We state the three cases
separately; the universal form is a trivial consequence.

The degenerate-interval branch (one of `IC(a_i), IC(b_j)` empty;
`step5.tex:788-813`) is omitted from the structural statement
because it requires the poset-level `|{c : c < a_i}|` "gap position"
redefinition of `h`, which is supplied at the Step 7 assembly level
and does not belong in the pure interval-geometry core of Step 5. -/
theorem global_layering_structural
    (alphaAC betaAC : Fin p → ℤ) (gammaBC deltaBC : Fin q → ℤ)
    (fAC : Fin p → ℤ) (fBC : Fin q → ℤ) (K : ℤ)
    (hAC : InBand alphaAC betaAC fAC K)
    (hBC : InBand gammaBC deltaBC fBC K) :
    -- (i) A–C case: incomparable a_i with c_k ∈ IC(a_i) gives
    -- |fAC(i) - k| ≤ K.
    (∀ (i : Fin p) (k : ℤ),
        alphaAC i ≤ k ∧ k ≤ betaAC i →
        |fAC i - k| ≤ K) ∧
    -- (ii) B–C case: symmetric.
    (∀ (j : Fin q) (k : ℤ),
        gammaBC j ≤ k ∧ k ≤ deltaBC j →
        |fBC j - k| ≤ K) ∧
    -- (iii) A–B case: cyclic compatibility, bound 2K+1.
    (∀ {i : Fin p} {j : Fin q},
        IntervalsTouch alphaAC betaAC gammaBC deltaBC i j →
        |fAC i - fBC j| ≤ 2 * K + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k hk
    exact case_AC alphaAC betaAC fAC K hAC i k hk
  · intro j k hk
    exact case_BC gammaBC deltaBC fBC K hBC j k hk
  · intro i j touch
    exact cyclic_compat alphaAC betaAC gammaBC deltaBC fAC fBC K hAC hBC touch

end GlobalLayering

/-! ### Activation absorption (`step5.tex:537-666`, G4 closure) -/

section ActivationAbsorb

/-- **Activation absorption** (G4 closure, `step5.tex:537-666`).

The G4 fiber-mass conversion lemma (formalised as
`OneThird.Step5.fiber_mass_sum_lower_bound` in `FiberMass.lean`) uses
only the per-pair bulk bound `2 · fiberSize α ≥ LP`. The paper's G4
proof *absorbs* the activation band (the Step-1 `Bad_{x,y}` set;
`step5.tex:560-575`) into that per-pair bound by choosing the
threshold `T ≥ T₀` large enough that `|B_α|/|F_α| = O(1/T) ≤ 1/2`.

Formal statement: if the raw fiber satisfies
`2 · fiberRaw α ≥ LP + 2 · bad α`, then after subtracting the
activation (`Bad`) set, the purified good fiber still satisfies the
per-pair bulk bound `2 · fiberPure α ≥ LP` where
`fiberPure α := fiberRaw α - bad α`.

This is the arithmetic content of the "absorption" step. It is
independent of the fiber-mass averaging in `FiberMass.lean` — the two
fit together as: first absorb activation, then average. -/
theorem activation_absorb
    {Pair : Type*}
    (fiberRaw bad : Pair → ℕ) (LP : ℕ) (α : Pair)
    (hper : 2 * fiberRaw α ≥ LP + 2 * bad α)
    (hle : bad α ≤ fiberRaw α) :
    2 * (fiberRaw α - bad α) ≥ LP := by
  have h1 : 2 * fiberRaw α - 2 * bad α ≥ LP := by omega
  have h2 : 2 * (fiberRaw α - bad α) = 2 * fiberRaw α - 2 * bad α := by
    have : bad α ≤ fiberRaw α := hle
    omega
  omega

/-- **Activation absorption, summed form** (`step5.tex:537-666`,
together with `step5.tex:604-611`).

Under the per-pair post-absorption bound, the summed lower bound of
`OneThird.Step5.fiber_mass_sum_lower_bound` extends to the purified
fiber `fiberRaw α - bad α`. -/
theorem activation_absorb_summed
    {Pair : Type*}
    (richPairs : Finset Pair) (fiberRaw bad : Pair → ℕ) (LP : ℕ)
    (hper : ∀ α ∈ richPairs, 2 * fiberRaw α ≥ LP + 2 * bad α)
    (hle : ∀ α ∈ richPairs, bad α ≤ fiberRaw α) :
    ∀ α ∈ richPairs, 2 * (fiberRaw α - bad α) ≥ LP :=
  fun α hα => activation_absorb fiberRaw bad LP α (hper α hα) (hle α hα)

end ActivationAbsorb

end Step5
end OneThird
