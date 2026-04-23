/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.FiberSize
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Brightwell sharp centred bound (axiomatized)

This file declares a single named axiom,
`brightwell_sharp_centred`, packaging the FKG/Ahlswede–Daykin
single-element perturbation bound of Brightwell
(\[Brightwell1999, Theorem 4.1\]) in the form consumed by the Step 8
single-element deletion coupling (paper `step8.tex:1042`).

## Paper statement (`step8.tex`, `eq:sharp-centred`)

Let `Q` be a finite poset with `|Q| = m ≥ 2`, let `z ∈ Q`, and put
`α := Q − z`. Write `pred(z), succ(z) ⊆ α` for the predecessor /
successor sets of `z` in `Q`. For `L' ∈ L(α)` define

```
  P(L') := max { pos_{L'}(u) : u ∈ pred(z) }       (= 0 if pred(z) = ∅)
  S(L') := min { pos_{L'}(v) : v ∈ succ(z) }       (= |Q| if succ(z) = ∅)
  f(L') := S(L') − P(L')                            ∈ {1, …, m}
```

Set `N := |L(Q)|`, `N' := |L(α)|`, and `f̄ := N / N'`. Then for any
`x, y ∈ α`,

```
  | Σ_{L' ∈ A} ( f(L') − f̄ ) |   ≤   2 N / m,                 (*)
```

where `A := { L' ∈ L(α) : x <_{L'} y }`. This is
`eq:sharp-centred`; A10b (commit `c6d76d6`) formally derives it from
FKG/AD on the product distributive lattice
`L(α) × {1, …, m}`, the 1-Lipschitz property of `f = S − P` on the
adjacent-transposition graph of `L(α)`, and the Kahn–Saks /
Brightwell per-term covariance bound
`|Cov_μ(1_A, S)|, |Cov_μ(1_A, P)| ≤ f̄/m`.

The Lean inputs — FKG on the uniform measure on `LinearExt α`
(`OneThird.Mathlib.LinearExtension.FKG.fkg_uniform_initialLowerSet`)
and the 1-Lipschitz property of `f = S − P`
(`OneThird.Mathlib.LinearExtension.FiberSize.fiberSize_lipschitz_on_bkAdj`) —
are already formalised. The present file declares the Brightwell
coupling bound itself as an axiom; the full Lean port is deferred to
work item `mg-b699` ("F6-4-port: post-sorry-free"), which will
replace the axiom with a proof combining those inputs.

## Axiom signature

We phrase `(*)` in a division-free integer form: multiplying by
`m · N'` and using integer cast,

```
  m · | N' · (Σ_{L' ∈ A} f(L')) − |A| · N |   ≤   2 · N · N',
```

where `N := Σ_{L' : L(α)} f(L')` (which agrees with `|L(Q)|` by the
fibre-sum identity `step8.tex:939`). This form is reusable by the
downstream F6a port without committing to a specific numeric type,
and is trivially rearranged into rational / real forms.

The hypotheses pin the paper scope:

* `Pred, Succ : Finset α` satisfy the disjointness and comparability
  axioms of Step 8 (so that `fiberSize Pred Succ` is consistent with
  a single-element extension of `α`);
* `m ≥ 2` is the ambient `|Q|`;
* `fiberSize Pred Succ L' ≤ m` for every `L' : LinearExt α` — this
  encodes `f ∈ {1, …, m}` (the lower bound `f ≥ 1` is not used by the
  bound);
* `x, y : α` are arbitrary — when `(x, y)` is comparable in `α` the
  indicator `1_A` is constant and the bound holds trivially; the
  content is for the incomparable case.

## Downstream use

* **`mg-1f5e` (F6a).** Consumes this axiom to close
  `lem:one-elem-perturb` (`|p_{xy}(Q) − p_{xy}(Q−z)| ≤ 2/m`) after
  dividing by `N · N' > 0` and translating to `probLT`.
* **`mg-a6a1` (F6-4-QA).** Verifies the axiom is a faithful
  transcription of the paper statement.
* **`mg-b699` (F6-4-port).** Replaces the axiom with a full proof.

## References

* G. Brightwell, *Balanced pairs in partial orders*, §4.
* R. Ahlswede, D. E. Daykin, *An inequality for the weights of two
  families of sets…* (1978).
* C. M. Fortuin, P. W. Kasteleyn, J. Ginibre, *Correlation
  inequalities on some partially ordered sets* (1971).
* J. Kahn, M. Saks, *Balancing poset extensions* (1984), Lemma 2.2.
-/

namespace OneThird
namespace LinearExt

open Finset

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

/-- **Brightwell sharp centred bound** (`step8.tex:1042`,
`eq:sharp-centred`). Axiomatized.

For a finite poset `α` with pred/succ sets `Pred, Succ ⊆ α`
satisfying disjointness and comparability (so that
`fiberSize Pred Succ = S − P` is the insertion-fibre size for an
ambient `Q = α ⊔ {z}`), and any `m ≥ 2` upper-bounding the fibre
size, the centred sum

```
  Σ_{L' ∈ A} ( f(L') − f̄ ),      f̄ := N / N',
```

over `A := { L' : x <_{L'} y }` is bounded by `2 N / m` in absolute
value. Multiplying by `m · N'` and using integer arithmetic:

```
  m · | N' · Σ_{L' ∈ A} f(L') − |A| · N |  ≤  2 · N · N',
```

where `N := Σ_{L' : LinearExt α} f L'` (the paper's `|L(Q)|`, via the
fibre-sum identity `step8.tex:939`) and
`N' := Fintype.card (LinearExt α)`.

**Why an axiom.** The paper proof invokes FKG/Ahlswede–Daykin on the
product lattice `L(α) × {1, …, m}` together with the per-term
Kahn–Saks / Brightwell covariance bound
`|Cov_μ(1_A, S)|, |Cov_μ(1_A, P)| ≤ f̄/m`. The FKG and 1-Lipschitz
inputs are available (`FKG.lean`, `FiberSize.lean`); the Brightwell
coupling combining them is a load-bearing external result tracked
under `mg-b699` for post-sorry-free formalisation.
-/
axiom brightwell_sharp_centred
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ u ∈ Pred, ∀ v ∈ Succ, u ≤ v)
    (m : ℕ) (hm : 2 ≤ m)
    (hmbd : ∀ L : LinearExt α, fiberSize Pred Succ L ≤ m)
    (x y : α) :
    (m : ℤ) *
      |(Fintype.card (LinearExt α) : ℤ) *
          (∑ L ∈ (Finset.univ : Finset (LinearExt α)).filter (fun L => L.lt x y),
              (fiberSize Pred Succ L : ℤ))
        - (((Finset.univ : Finset (LinearExt α)).filter
              (fun L => L.lt x y)).card : ℤ) *
          (∑ L : LinearExt α, (fiberSize Pred Succ L : ℤ))|
      ≤ 2 * (∑ L : LinearExt α, (fiberSize Pred Succ L : ℤ))
          * (Fintype.card (LinearExt α) : ℤ)

/-! ### Thin rearrangement wrappers

These are paper-shaped restatements of `brightwell_sharp_centred`
that do not introduce new mathematical content; they only rearrange
the bound to the forms most convenient for F6a. -/

/-- Abbreviation for the order-ideal subfamily `A = {L' : x <_{L'} y}`
of `step8.tex:942`. -/
noncomputable def brightwellA (x y : α) : Finset (LinearExt α) :=
  (Finset.univ : Finset (LinearExt α)).filter (fun L => L.lt x y)

@[simp] lemma mem_brightwellA {x y : α} {L : LinearExt α} :
    L ∈ brightwellA (α := α) x y ↔ L.lt x y := by
  simp [brightwellA]

/-- Rational-scaled form of `brightwell_sharp_centred`, matching
the paper's `eq:sharp-centred` exactly:
`|Σ_{L' ∈ A} (f L' − f̄)| ≤ 2 N / m`, where
`f̄ := (Σ_{L' : LinearExt α} f L') / N'` and
`N = Σ_{L' : LinearExt α} f L'`. -/
lemma brightwell_sharp_centred_rat
    (Pred Succ : Finset α)
    (hDisj : Disjoint Pred Succ)
    (hComp : ∀ u ∈ Pred, ∀ v ∈ Succ, u ≤ v)
    (m : ℕ) (hm : 2 ≤ m)
    (hmbd : ∀ L : LinearExt α, fiberSize Pred Succ L ≤ m)
    (x y : α) :
    |(∑ L ∈ brightwellA (α := α) x y, (fiberSize Pred Succ L : ℚ))
       - ((brightwellA (α := α) x y).card : ℚ) *
           ((∑ L : LinearExt α, (fiberSize Pred Succ L : ℚ)) /
            (Fintype.card (LinearExt α) : ℚ))|
      ≤ 2 * (∑ L : LinearExt α, (fiberSize Pred Succ L : ℚ)) / (m : ℚ) := by
  classical
  set Nprime : ℤ := (Fintype.card (LinearExt α) : ℤ) with hNpdef
  set Ntot : ℤ := ∑ L : LinearExt α, (fiberSize Pred Succ L : ℤ) with hNdef
  set A : Finset (LinearExt α) := brightwellA (α := α) x y with hAdef
  set sumA : ℤ := ∑ L ∈ A, (fiberSize Pred Succ L : ℤ) with hsumAdef
  have hNp_pos : (0 : ℤ) < Nprime := by
    rw [hNpdef]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (LinearExt α))
  have hm_pos : (0 : ℤ) < (m : ℤ) := by
    have : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hm
    exact_mod_cast this
  -- The integer form of the axiom.
  have hint :
      (m : ℤ) * |Nprime * sumA - (A.card : ℤ) * Ntot|
        ≤ 2 * Ntot * Nprime := by
    simpa [hNpdef, hNdef, hAdef, hsumAdef, brightwellA] using
      brightwell_sharp_centred (α := α) Pred Succ hDisj hComp m hm hmbd x y
  -- Cast to ℚ. The cast commutes with `|·|`, `*`, `-`.
  have hint_rat :
      (m : ℚ) * |(Nprime : ℚ) * (sumA : ℚ) - (A.card : ℚ) * (Ntot : ℚ)|
        ≤ 2 * (Ntot : ℚ) * (Nprime : ℚ) := by
    have h1 : (((m : ℤ) * |Nprime * sumA - (A.card : ℤ) * Ntot| : ℤ) : ℚ)
        ≤ ((2 * Ntot * Nprime : ℤ) : ℚ) := by exact_mod_cast hint
    simpa [Int.cast_mul, Int.cast_abs, Int.cast_sub] using h1
  have hm_posQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm_pos
  have hNp_posQ : (0 : ℚ) < (Nprime : ℚ) := by exact_mod_cast hNp_pos
  -- (m) * |·| ≤ 2 N N' ⟹ |·| ≤ 2 N N' / m.
  have hstep1 :
      |((Nprime : ℚ) * (sumA : ℚ) - (A.card : ℚ) * (Ntot : ℚ))|
        ≤ 2 * (Ntot : ℚ) * (Nprime : ℚ) / (m : ℚ) := by
    rw [le_div_iff₀ hm_posQ]; linarith [hint_rat]
  -- Factor N' out of the absolute value and divide.
  have heq :
      (Nprime : ℚ) * (sumA : ℚ) - (A.card : ℚ) * (Ntot : ℚ)
        = (Nprime : ℚ) *
            ((sumA : ℚ) - (A.card : ℚ) * ((Ntot : ℚ) / (Nprime : ℚ))) := by
    field_simp
  have habs :
      |((Nprime : ℚ) * (sumA : ℚ) - (A.card : ℚ) * (Ntot : ℚ))|
        = (Nprime : ℚ) *
            |(sumA : ℚ) - (A.card : ℚ) * ((Ntot : ℚ) / (Nprime : ℚ))| := by
    rw [heq, abs_mul, abs_of_pos hNp_posQ]
  rw [habs] at hstep1
  have hcancel :
      2 * (Ntot : ℚ) * (Nprime : ℚ) / (m : ℚ)
        = (Nprime : ℚ) * (2 * (Ntot : ℚ) / (m : ℚ)) := by
    field_simp
  rw [hcancel] at hstep1
  have hstep2 :
      |(sumA : ℚ) - (A.card : ℚ) * ((Ntot : ℚ) / (Nprime : ℚ))|
        ≤ 2 * (Ntot : ℚ) / (m : ℚ) :=
    le_of_mul_le_mul_left (by linarith [hstep1]) hNp_posQ
  -- Translate back to the original sums (ℚ-valued).
  have hsumA_cast : (sumA : ℚ)
      = ∑ L ∈ A, (fiberSize Pred Succ L : ℚ) := by
    rw [hsumAdef]
    rw [show (∑ L ∈ A, ((fiberSize Pred Succ L : ℤ)) : ℤ)
          = ((∑ L ∈ A, (fiberSize Pred Succ L : ℕ) : ℕ) : ℤ) by push_cast; rfl]
    push_cast
    rfl
  have hNtot_cast : (Ntot : ℚ)
      = ∑ L : LinearExt α, (fiberSize Pred Succ L : ℚ) := by
    rw [hNdef]
    rw [show (∑ L : LinearExt α, ((fiberSize Pred Succ L : ℤ)) : ℤ)
          = ((∑ L : LinearExt α, (fiberSize Pred Succ L : ℕ) : ℕ) : ℤ)
          by push_cast; rfl]
    push_cast
    rfl
  have hNp_cast : (Nprime : ℚ) = (Fintype.card (LinearExt α) : ℚ) := by
    rw [hNpdef]; push_cast; rfl
  rw [hsumA_cast, hNtot_cast, hNp_cast] at hstep2
  exact hstep2

end LinearExt
end OneThird
