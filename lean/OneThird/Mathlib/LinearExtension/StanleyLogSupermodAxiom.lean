/-
Copyright (c) 2026 The OneThird Authors. All rights reserved.
Released under the MIT License.
-/
import OneThird.Mathlib.LinearExtension.Fintype
import OneThird.Mathlib.LinearExtension.FKG

/-!
# Stanley log-supermodularity (axiomatized)

This file declares a single named axiom, `stanley_log_supermod`,
packaging Stanley's log-supermodularity inequality for the
linear-extension counting function `e : J(α) → ℕ`,
`e(K) := |L(α[K])|`, on the lattice `J(α)` of order ideals of `α`.

## Paper statement

Let `α` be a finite poset and let `J(α)` denote its lattice of
order ideals (lower sets of `α`). For each `K ∈ J(α)`, let
`e(K) := |L(α[K])|` be the number of linear extensions of the
sub-poset `α[K]` (carved out by `K ⊆ α` and inheriting the order
from `α`). Then `e` is **log-supermodular** on `J(α)`:

```
  e(I) · e(J) ≤ e(I ⊔ J) · e(I ⊓ J),       I, J ∈ J(α).            (*)
```

In `LowerSet α`, the lattice operations satisfy `(I ⊔ J : Set α) =
(I : Set α) ∪ (J : Set α)` and `(I ⊓ J : Set α) = (I : Set α) ∩
(J : Set α)`, so `(*)` reads `e(I) e(J) ≤ e(I ∪ J) e(I ∩ J)`.

## Provenance and trust surface

This is **Stanley 1981**, *Two combinatorial applications of the
Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A.
The deepest known proofs go via the Aleksandrov–Fenchel
inequalities (Stanley 1981, ~3000–5000 LoC mathlib gap including
order-polytope volume formulas and mixed-volume infrastructure)
or via cleaner combinatorial arguments (Daykin 1990 4FT-direct;
Bjorner 1989 combinatorial induction). The cheap closure variants
explored by mg-c7b9 (Bjorner-style induction) were RED'd by
mg-7928 §1.2 on a fresh structural fact: the Bjorner injection
`Ψ : LE(α[I]) × LE(α[J]) ↪ LE(α[I⁺]) × LE(α[J⁺])` combined with
the IH on the smaller-δ pair produces a strictly weaker inequality
than the target, with no IH re-application closing the gap
(see `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-induction-closure.md`
and state.md §1.10).

This file therefore declares `stanley_log_supermod` as a
**temporary named project axiom** under
`docs/path-alpha-execution-arc/state.md` §3.4 Option A. It is
audit-bar-compliant per the four-condition check
(`feedback_audit_bar_for_axioms`):

1. **External.** Stanley 1981 (J. Combin. Theory Ser. A);
   Aleksandrov–Fenchel inequalities. Established result.
2. **Difficult.** Mathlib-gap; full AF port estimated ~3000–5000
   LoC; cheap variants 2–4 surveyed and rejected (mg-7928 §3.1).
3. **Labeled.** Catalogued in `lean/AXIOMS.md` with full audit-bar
   4-condition table (this ticket, mg-d0fc).
4. **Low-risk.** Stanley 1981 is well-cited, mature literature
   foundation; no plausible error in the established result.

The axiom is **temporary** in the sense of `lean/AXIOMS.md`: it is
the discharge target of either
- **DH-1.** Mathlib upstream of Stanley log-supermod, file
  `Mathlib/Combinatorics/Order/StanleyLogSupermod.lean` (target
  maintainer: Yael Dillies); or
- **Option B.** Full in-tree port of the Stanley 1981 AF proof
  (~3000–5000 LoC) bundled with sub-α-C EX-3 onward.

When either lands, this file's `axiom` keyword is replaced by a
`theorem` with the imported / ported proof, with no signature
change required at consumer call sites.

## Downstream use

The axiom is consumed by EX-3 (chamber-decomposition scoping) and
later sub-α-C execution tickets, where Stanley log-supermod enters
as a hypothesis to the chamber decomposition / Hibi polytope
infrastructure. It is **not** consumed by the existing
`width3_one_third_two_thirds` headline or any Step-8 / Step-1 /
F5a / F6 / Path γ pathway — those remain on the existing two-named-
axiom trust surface (`brightwell_sharp_centred`,
`case3Witness_hasBalancedPair_outOfScope`).

## References

* R. P. Stanley, *Two combinatorial applications of the
  Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A
  **31** (1981), no. 1, 56–65.
* A. Bjorner, *The Möbius function of factor order*, Theoret.
  Comput. Sci. **117** (1993) — also surveyed for closure variants.
* D. E. Daykin, *A hierarchy of inequalities*, Studia Sci. Math.
  Hungar. **25** (1990) — 4FT-direct route.
-/

namespace OneThird
namespace LinearExt

open Set

variable {α : Type*}

/-! ### §1 — Sub-poset infrastructure for the axiom signature

Stanley's inequality is stated on sub-posets `α[K]` carved out by
a set `K ⊆ α` with the inherited order. We package the subtype
together with its inherited `PartialOrder`, `Fintype`, and
`DecidableEq` instances so that `numLinExt (subPoset K)` is
well-typed for `K : Set α`. -/

/-- Sub-poset of `α` carved out by a `Set α`. Definitionally
`↥s = Subtype (· ∈ s)`, with the inherited `PartialOrder`. The
companion `Fintype` and `DecidableEq` instances are populated below.

Wrapping `↥s` in a `def` (rather than an `abbrev`) keeps the
noncomputable `Fintype` instance below scoped to this definition,
so it does not bleed into the global instance database for
arbitrary subtypes. -/
def subPoset [PartialOrder α] (s : Set α) : Type _ := ↥s

instance subPoset.instPartialOrder [PartialOrder α] (s : Set α) :
    PartialOrder (subPoset s) :=
  (inferInstance : PartialOrder ↥s)

instance subPoset.instDecidableEq [PartialOrder α] [DecidableEq α]
    (s : Set α) : DecidableEq (subPoset s) :=
  (inferInstance : DecidableEq ↥s)

/-- `subPoset s` is a `Fintype` whenever `α` is a `Fintype`. The
construction routes through the classical `Set.Finite` instance for
subsets of a finite type, which is noncomputable. -/
noncomputable instance subPoset.instFintype [PartialOrder α] [Fintype α]
    (s : Set α) : Fintype (subPoset s) :=
  haveI : Finite ↥s := inferInstance
  (Set.toFinite s).fintype

/-! ### §2 — The named axiom

This is the only `axiom` declaration in the file. It is added to the
project's trust surface as the third named project axiom, audit-bar-
compliant; see `lean/AXIOMS.md` for the full 4-condition table. -/

/-- **Stanley's log-supermodularity inequality** for the
linear-extension counting function `e : J(α) → ℕ`,
`e(K) := |L(α[K])|`. For lower sets `I, J ∈ J(α)`,

```
  e(I) · e(J)  ≤  e(I ⊔ J) · e(I ⊓ J).
```

Reference: Stanley 1981, *Two combinatorial applications of the
Aleksandrov–Fenchel inequalities*, J. Combin. Theory Ser. A.

This is a **temporary named project axiom**, retained until either
**DH-1** (mathlib upstream of Stanley log-supermod) lands or
**Option B** (full in-tree port of the Stanley 1981 AF proof,
~3000–5000 LoC) is dispatched. See
`docs/path-alpha-execution-arc/state.md` §1.5, §1.10, §3.4 for the
audit trail and replacement plan, and `lean/AXIOMS.md` for the
audit-bar 4-condition table. -/
axiom stanley_log_supermod [PartialOrder α] [Fintype α] [DecidableEq α]
    (I J : LowerSet α) :
    numLinExt (subPoset (α := α) (I : Set α)) *
        numLinExt (subPoset (α := α) (J : Set α))
      ≤ numLinExt (subPoset (α := α) ((I ⊔ J : LowerSet α) : Set α)) *
          numLinExt (subPoset (α := α) ((I ⊓ J : LowerSet α) : Set α))

/-! ### §3 — Corollary `μ(I) := e(I) · e(α \ I)` log-supermod (deferred)

The "doubled" form `μ(I) := e(I) · e(α \ I)` is also log-supermodular
on `J(α)` (Stanley 1981 corollary; mg-91be §3.2; sub-α-C scoping
§5.2 EX-2). Its derivation requires applying `stanley_log_supermod`
twice — once to `(I, J)` and once to the dual pair `(α \ I, α \ J)` —
and then combining via De Morgan:

```
μ(I) μ(J) = e(I) e(J) · e(α \ I) e(α \ J)
        ≤  e(I ⊔ J) e(I ⊓ J) · e((α \ I) ⊔ᵒᵖ (α \ J)) e((α \ I) ⊓ᵒᵖ (α \ J))
        =  e(I ⊔ J) e(I ⊓ J) · e(α \ (I ⊓ J)) e(α \ (I ⊔ J))
        =  μ(I ⊔ J) μ(I ⊓ J).
```

The dual application — Stanley on the *upper-set* complements
`α \ I, α \ J ⊆ α` — requires either (a) instantiating
`stanley_log_supermod` on the order-dual `αᵒᵖ`, where the upper-set
complements become lower sets, plus a `numLinExt`-on-dual identity
`numLinExt (subPoset s in αᵒᵖ) = numLinExt (subPoset s in α)`, or
(b) a parallel axiom `stanley_log_supermod_upper`.

This corollary is deferred to a narrow follow-up ticket per
mg-d0fc §5 AMBER verdict. EX-3 (chamber-decomposition scoping) does
not consume the corollary directly — only `stanley_log_supermod` —
so the deferral does not block the next sub-α-C execution ticket.
The corollary will be filed by PM as a small follow-up
(estimated ~50–150 LoC once the dual-poset bridge lemma is in place,
or trivially as `~50 LoC` once a parallel upper-set axiom is added). -/

end LinearExt
end OneThird
