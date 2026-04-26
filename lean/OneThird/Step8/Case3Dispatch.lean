/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.LinearExtension
import OneThird.Poset
import OneThird.Step8.LayeredReduction
import OneThird.Step8.LayerOrdinal
import OneThird.Step8.BoundedIrreducibleBalanced
import OneThird.Step8.Case3Struct

/-!
# Step 8 — Case dispatch for `prop:in-situ-balanced` on `¬ InCase3Scope` leaves
(`mg-A8` sub-split A8-S1, `mg-48db`)

This file packages the three-way case analysis of
`prop:in-situ-balanced` (`step8.tex:2965-3048`) as a **typed dispatch**
shared by the three downstream sub-splits of `mg-A8`:

* **A8-S1** (this commit) — the dispatch theorem itself, plus the
  two new typed witness predicates `Case2Witness L`, `Case3Witness L`.
* **A8-S2** (`mg-8801`) — discharges `Case2Witness L → HasBalancedPair α`
  via the Ahlswede–Daykin / FKG profile-ordering argument
  (`step8.tex:3001-3032`).
* **A8-S3** (`mg-b846`) — discharges `Case3Witness L → HasBalancedPair α`
  via the residual width-3 profile-antichain argument
  (`step8.tex:3033-3047, 3157-3173`), restricted to `¬ InCase3Scope`
  parameter ranges (since the F5a `case3_certificate` enumeration
  handles `InCase3Scope`).

## Main definitions

(All in the `OneThird.Step8.InSitu` sub-namespace, to disambiguate
from the outer `Step8.Case3Witness` of `LayeredBalanced.lean`.)

* `Step8.InSitu.Case2Witness L` — within-band pair `(a, a')` with
  one-sided ambient profile inclusion:
  `(∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)`. This is the Lean
  encoding of `prop:in-situ-balanced` Case 2's hypothesis "two-sided
  profile of `a` is `⪯`-below that of `a'`" (`step8.tex:3001-3014`).
  The within-band condition `L.band a = L.band a'` is the L1
  antichain that frames the FKG monotonicity argument.

* `Step8.InSitu.Case3Witness L` — the residual: neither a Case 1
  ambient profile match pair nor a Case 2 within-band ⪯-comparable
  pair exists. The "structural" content of Case 3 (a width-3
  within-band antichain whose two-sided profiles are pairwise
  ⪯-incomparable, plus the "two of three share a profile coordinate"
  claim of `step8.tex:3157-3173`) is *derived* from this negation form
  by A8-S3, using the wider hypothesis profile (width-3,
  irreducibility, `¬ InCase3Scope`).

## Main theorem

```
theorem case1_dispatch_inScope
    (L : LayeredDecomposition α) (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K) :
    (∃ a a' : α, a ≠ a' ∧
        (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a'))
      ∨ Case2Witness L
      ∨ Case3Witness L
```

The dispatch is provable by classical excluded middle on Case 1 and
then on Case 2; the hypothesis profile (`hWidth3`, `hIrr`, `hScope`)
is documented in the signature for downstream call-site clarity but
is not used by the dispatch itself. Each branch carries its own proof
obligation:

* The Case 1 branch (`∃ a a' : α, …`) plugs directly into
  `Step8.hasBalancedPair_of_ambient_profile_match`
  (`Case3Struct.lean`, mg-f92d), giving `HasBalancedPair α` immediately.
* The Case 2 / Case 3 branches are typed slots for A8-S2 and A8-S3
  to fill. See `case1_branch_balanced` below for the wired form of
  Case 1.

## Why typed witnesses

The hybrid theorem
`Step8.bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1587`) takes its `hStruct` slot as
an opaque function `¬ InCase3Scope … → HasBalancedPair α`. Splitting
the structural argument into three sub-tasks via typed witnesses
makes the dispatch shape **explicit in the type**, so A8-S2 / A8-S3
build against typed inputs rather than re-deriving the case split
each time.

The hypothesis profile (`HasWidthAtMost α 3`, `LayerOrdinalIrreducible L`,
`¬ InCase3Scope L.w (Fintype.card α) L.K`) is *not* baked into the
witness predicates: A8-S2 / A8-S3 will take it as separate hypotheses
on their `Case2Witness`/`Case3Witness` discharge lemmas, matching the
hybrid theorem's call-site shape.

## What this file does **not** do

* It does **not** discharge `Case2Witness L → HasBalancedPair α`
  (deferred to A8-S2 / `mg-8801`).
* It does **not** discharge `Case3Witness L → HasBalancedPair α`
  (deferred to A8-S3 / `mg-b846`).
* It introduces no new `sorry`, `axiom`, or `native_decide` shortcut.

## References

* `step8.tex` `prop:in-situ-balanced` (`2965-3048`); `rem:enumeration`
  (`3157-3173`).
* `lean/OneThird/Step8/Case3Struct.lean` — Case 1 ambient form
  (`hasBalancedPair_of_ambient_profile_match`, mg-f92d).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean` —
  `bounded_irreducible_balanced_hybrid` consumer.
* `docs/a8-status.md` — full mg-A8 status report and sub-split rationale.
-/

namespace OneThird
namespace Step8
namespace InSitu

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### §1 — Witness predicates for Cases 2 and 3 of `prop:in-situ-balanced`

The witnesses live in the `Step8.InSitu` sub-namespace to disambiguate
from the *outer* `Step8.Case3Witness` of `LayeredBalanced.lean` (the
∀-family covering F5a-ℓ's recursion across all layered width-3
sub-posets, supplied as a hypothesis to `lem_layered_balanced`). The
`InSitu.Case2Witness` / `InSitu.Case3Witness` of this file are the
*inner* sub-case witnesses of `prop:in-situ-balanced` Cases 2 and 3,
sitting one level below the outer dispatch. -/

/-- **Case 2 witness** of `prop:in-situ-balanced`
(`step8.tex:3001-3032`).

A within-band pair `(a, a')` with one-sided ambient profile inclusion:
the strict-`<` up-set of `a` is contained in that of `a'`, and the
strict-`<` down-set of `a'` is contained in that of `a`. In the
notation of the paper, the two-sided profile of `a` is `⪯`-below
that of `a'`:

* every `z` strictly above `a` is also strictly above `a'`
  (`Π⁺(a) ⊆ Π⁺(a')`);
* every `z` strictly below `a'` is also strictly below `a`
  (`Π⁻(a') ⊆ Π⁻(a)`).

The within-band condition `L.band a = L.band a'` reflects the (L1)
antichain on which the paper's Ahlswede–Daykin / FKG monotonicity
argument operates.

A8-S2 (`mg-8801`) discharges `Case2Witness L → HasBalancedPair α`
under the wider hypothesis profile of
`bounded_irreducible_balanced_hybrid`. -/
def Case2Witness (L : LayeredDecomposition α) : Prop :=
  ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧
    (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)

/-- **Case 3 (residual) witness** of `prop:in-situ-balanced`
(`step8.tex:3033-3047`).

The negation form: neither a Case 1 ambient profile match pair nor a
Case 2 within-band ⪯-comparable pair exists. The "structural"
positive form of Case 3 — a width-3 within-band antichain with
pairwise ⪯-incomparable two-sided profiles, satisfying the "two of
three share a profile coordinate" claim of `rem:enumeration`
(`step8.tex:3157-3173`) — is *derived* from this negation by A8-S3
(`mg-b846`) using the wider hypothesis profile (width-3,
irreducibility, `¬ InCase3Scope`).

Encoding the residual as a negation here keeps A8-S1 lightweight
(the dispatch is classical excluded middle); A8-S3 bears the
mathematical burden of unpacking the negation into the structural
configuration that the residual argument operates on. -/
def Case3Witness (L : LayeredDecomposition α) : Prop :=
  ¬ (∃ a a' : α, a ≠ a' ∧
        (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a'))
    ∧ ¬ Case2Witness L

/-! ### §2 — Case 1 → balanced pair (direct wiring of mg-f92d's lemma) -/

/-- **Case 1 branch → balanced pair** (`step8.tex:2984-2999`).

The Case 1 branch of `case1_dispatch_inScope` plugs directly into
`hasBalancedPair_of_ambient_profile_match` from `Case3Struct.lean`
(mg-f92d): from the existence of two distinct elements with identical
ambient strict-`<` profile in both directions, the `Equiv.swap a a'`
automorphism argument yields a balanced pair with `probLT a a' = 1/2`.

This corollary makes the wiring explicit so downstream callers of
`case1_dispatch_inScope` can dispatch the Case 1 branch with one
`exact` rather than re-unpacking the ambient match hypothesis. -/
theorem hasBalancedPair_of_case1
    (h : ∃ a a' : α, a ≠ a' ∧
          (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')) :
    HasBalancedPair α := by
  obtain ⟨a, a', hne, h_up, h_down⟩ := h
  exact Step8.hasBalancedPair_of_ambient_profile_match a a' hne h_up h_down

/-! ### §3 — Case dispatch theorem -/

set_option linter.unusedVariables false in
/-- **Case dispatch on `¬ InCase3Scope` leaves**
(`mg-A8` sub-split A8-S1, `mg-48db`).

The three-way case analysis of `prop:in-situ-balanced`
(`step8.tex:2965-3048`), packaged as a typed dispatch for the
discharge of the `hStruct` slot of
`Step8.bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1587`).

Under the hybrid theorem's wider hypothesis profile —
* `HasWidthAtMost α 3` (width-3 hypothesis);
* `LayerOrdinalIrreducible L` (no ordinal-sum reduction is possible);
* `¬ InCase3Scope L.w (Fintype.card α) L.K` (out-of-scope leaves
  beyond the F5a `case3_certificate` enumeration scope) —

one of three structural cases applies:

1. **Case 1** (existence of an ambient profile-match pair, inline
   form): `∃ a a' : α, a ≠ a' ∧ (∀ z, a < z ↔ a' < z) ∧
   (∀ z, z < a ↔ z < a')`. This is the Case 1 hypothesis of
   `prop:in-situ-balanced` (`step8.tex:2984-2999`); it plugs
   directly into `hasBalancedPair_of_ambient_profile_match`
   (`Case3Struct.lean`, mg-f92d) — see `hasBalancedPair_of_case1`.
2. **Case 2** (`Case2Witness L`): a within-band pair with one-sided
   ambient profile inclusion (`prop:in-situ-balanced` Case 2,
   `step8.tex:3001-3032`). Discharged by A8-S2 (`mg-8801`).
3. **Case 3** (`Case3Witness L`): the residual — neither Case 1 nor
   Case 2 applies (`prop:in-situ-balanced` Case 3,
   `step8.tex:3033-3047`). Discharged by A8-S3 (`mg-b846`).

**Proof.** Classical excluded middle on Case 1 then on Case 2: if
either witness exists, dispatch into its branch; otherwise both
negations hold, packaging into `Case3Witness L`.

The hypothesis profile (`hWidth3`, `hIrr`, `hScope`) is documented
in the signature for downstream call-site clarity (and to anchor the
"on `¬ InCase3Scope` leaves" name). It is not used by the dispatch
itself, since the trichotomy is universally true; A8-S2 and A8-S3
will consume the hypothesis profile when discharging their typed
branches into `HasBalancedPair α`. -/
theorem case1_dispatch_inScope
    (L : LayeredDecomposition α) (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K) :
    (∃ a a' : α, a ≠ a' ∧
        (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a'))
      ∨ Case2Witness L
      ∨ Case3Witness L := by
  classical
  by_cases h1 : ∃ a a' : α, a ≠ a' ∧
      (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')
  · exact Or.inl h1
  by_cases h2 : Case2Witness L
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨h1, h2⟩)

/-! ### §4 — Composed dispatch: `case1_dispatch_inScope` + Case 1 wiring -/

set_option linter.unusedVariables false in
/-- **Dispatch with Case 1 already discharged.**

A convenience repackaging of `case1_dispatch_inScope` that wires the
Case 1 branch through `hasBalancedPair_of_case1`, leaving the caller
with a binary disjunction `HasBalancedPair α ∨ Case2Witness L ∨
Case3Witness L`. This is the form A5-G2 / A8-S2 / A8-S3 will consume
when assembling the full `hStruct` discharge of
`bounded_irreducible_balanced_hybrid`. -/
theorem case1_dispatch_balanced_or_witness
    (L : LayeredDecomposition α) (hWidth3 : HasWidthAtMost α 3)
    (hIrr : LayerOrdinalIrreducible L)
    (hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K) :
    HasBalancedPair α ∨ Case2Witness L ∨ Case3Witness L := by
  rcases case1_dispatch_inScope L hWidth3 hIrr hScope with h1 | h2 | h3
  · exact Or.inl (hasBalancedPair_of_case1 h1)
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

end InSitu
end Step8
end OneThird
