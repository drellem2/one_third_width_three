# mg-A8 status — `pc-f92d` polecat report

**Work item:** `mg-f92d` (mg-A8: structural argument for the `hStruct`
slot of `bounded_irreducible_balanced_hybrid` — `¬ InCase3Scope`
out-of-scope leaves of `prop:in-situ-balanced`).
**Status:** partial — Case 1 (general ambient form) lifted as reusable
infrastructure; full `hStruct` discharge **not** in tree.
**Author:** `pc-f92d` polecat, 2026-04-26.

---

## 1. What was supposed to land

> mg-A8 — Structural argument: 'width-3 profile antichain' for
> ¬ InCase3Scope leaves.
>
> Discharge `prop:in-situ-balanced` Case 3 (`step8.tex:2714-2728`) for
> the **out-of-scope leaves** (¬ InCase3Scope) — the K=4..2w+2 cases
> that the certificate enumeration doesn't cover. Plug into B4's
> `bounded_irreducible_balanced_hybrid` via the `hStruct` slot.

The hybrid theorem's `hStruct` slot, established by mg-43bc / B4, is

```
hStruct : ¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α
```

under the wider hypothesis profile of `bounded_irreducible_balanced`
(width 3, irreducible, `3 ≤ L.K ≤ 2 L.w + 2`, `1 ≤ L.w`,
`Fintype.card α ≤ 6 L.w + 6`). `¬ InCase3Scope` covers the parameter
ranges outside the F5a Case-3 Bool certificate's certified scope:
`K ≠ 3`, or `w ∉ {1, 2, 3, 4}`, or `(w = 1 ∧ |α| > 9)`, or
`(w ≥ 2 ∧ |α| > 7)`.

---

## 2. What's in tree at the start of this polecat

Before this commit:

* The hybrid theorem `bounded_irreducible_balanced_hybrid`
  (`BoundedIrreducibleBalanced.lean:1587`) — typed dispatch, both
  `hCert` and `hStruct` are unfilled hypotheses.
* `bipartite_balanced_enum` (`BipartiteEnum.lean:284`) — fully proves
  `prop:in-situ-balanced` Case 1 in the **K = 2 bipartite
  specialisation**: a height-2 poset `α = A ⊔ B` with directed
  cross-comparabilities and an incomparable pair admits the
  symmetric-pair `Equiv.swap u v` automorphism, giving
  `probLT u v = 1/2`.
* The Brightwell sharp centred bound
  (`OneThird.LinearExt.brightwell_sharp_centred`) and FKG
  infrastructure (`Mathlib/LinearExtension/FKG.lean`) — but these
  are oriented toward the F6 single-element-perturbation argument
  (`step8.tex:1042`, Step 6/7 perturbation chain), **not** toward
  the within-band FKG profile-ordering argument of
  `prop:in-situ-balanced` Case 2 (`step8.tex:3001-3032`).

---

## 3. The honest picture

After reading `step8.tex` `prop:in-situ-balanced` and the surrounding
remarks, the situation is more delicate than the mg-A8 ticket
description suggests:

### 3a. The paper does not actually carry out the structural argument for `¬ InCase3Scope`

`prop:in-situ-balanced` (`step8.tex:2965-3048`) splits into three
cases:

* **Case 1** (`step8.tex:2984-2999`) — symmetric within-band pair with
  full ambient profile match → `Equiv.swap` automorphism →
  `Pr = 1/2`.
* **Case 2** (`step8.tex:3001-3032`) — within-band pair with
  `⪯`-comparable two-sided profiles → Ahlswede–Daykin / FKG coupling
  → `Pr ∈ [1/2, 2/3]` or rotation argument extracts a triple in
  `[1/3, 2/3]`.
* **Case 3** (`step8.tex:3033-3047`) — width-3 profile antichain
  residual → "finite enumeration" (deferred to `lem:enum`,
  `step8.tex:3050-3056`).

The paper's `lem:enum` (`step8.tex:3050-3067`) and
`rem:residual-base` (`step8.tex:3194-3236`) are explicit that the
residual Case 3 is discharged by the machine-checked enumeration —
i.e., F5a's `case3_certificate` (`Case3Enum/Certificate.lean:57`).
That certificate covers exactly `InCase3Scope`. **There is no
self-contained structural argument in the paper for the residual
Case 3 outside `InCase3Scope`.**

The paper's `rem:enumeration` (`step8.tex:3157-3173`) **sketches** a
structural argument for the residual antichain configurations:

> For $w \ge 1$, the configurations with $|A| = 3$ whose profiles
> form a $\preceq$-antichain are enumerated modulo the symmetries of
> (L1); each is discharged by exhibiting either a Case 1 symmetric
> pair (after taking into account that two of the three elements
> must share *some* coordinate of the two-sided profile whenever
> $|Q| \le 3(3w+1)$ and (L2) restricts the profile codomain), or a
> Case 2 pair with aligned one-sided profiles restricted to the
> bands strictly above (or strictly below) the antichain under
> consideration.

This is the "two of three share a profile coordinate" hint cited in
the mg-A8 ticket. But the paper **does not flesh this out into a
proof**. The actual paper proof for the residual regime
(`rem:residual-base`, `step8.tex:3194-3236`) instead falls back on
the certificate enumeration via `enum_case3.py` over the bounded
parameter range `(w ∈ {1..4}, K = 3, |α| ≤ 9)`.

### 3b. The Brightwell §4 reference is misplaced

The mg-A8 ticket body cites "Brightwell §4" for the structural
argument. Brightwell §4 is the **sharp centred bound** for
single-element perturbation, already axiomatised here as
`brightwell_sharp_centred` (`Mathlib/LinearExtension/BrightwellAxiom.lean:159`)
and consumed by F6a (`OneElemPerturb.lean`, lifts to
`lem:one-elem-perturb` / `step8.tex:997-1013`). It is not directly
about the within-band Case 1 / Case 2 structural arguments of
`prop:in-situ-balanced`, nor about width-3 profile-antichain
residuals.

### 3c. Implication for `hStruct`

A constructive proof of

```
hStruct : ¬ InCase3Scope L.w (Fintype.card α) L.K → HasBalancedPair α
```

— under the hybrid theorem's wider hypothesis profile — therefore
requires **new mathematical work** beyond what the paper provides:

1. Either a fleshed-out proof of the `rem:enumeration` "two of three
   share a profile coordinate" sketch, **and** its consequences
   (Case 1 symmetric-pair existence, or Case 2 aligned-profile
   existence) for every `¬ InCase3Scope` parameter point.
2. Or an extension of the F5a `case3_certificate` enumeration to
   the wider scope (Path B of `docs/gap-analysis.md`).

Path B is explicitly rejected in `docs/a5-profile-resolution.md`
(§2 Option 2) on grounds of computational blowup and architectural
mismatch (the `bandSizesGen` / `enum_case3.py` script is hardwired
to `K = 3`).

Path "(1) above" is the actual mathematical content of mg-A8 — but
it is **not a port** of an existing paper proof. It is new
formalised content, with the paper providing only the high-level
sketch in `rem:enumeration`.

The mg-A8 ticket's estimate of "300–600 LOC if FKG primitives are
reusable" assumes the structural argument is well-developed in the
paper and only needs porting. That estimate underestimates the
work.

Per the explicit polecat-instruction guidance:

> Do NOT introduce new sorry's / axioms / hacky shortcuts. If FKG
> infrastructure isn't there, report honestly and recommend a
> sub-split rather than introducing axioms.

—the responsible deliverable for one polecat session is **partial
infrastructure + a sub-split recommendation**, not a sham
discharge.

---

## 4. What this polecat (`pc-f92d`, mg-f92d) actually delivers

### 4a. `OneThird/Step8/Case3Struct.lean` — Case 1 (general ambient form)

The Case 1 automorphism argument of `prop:in-situ-balanced`
(`step8.tex:2984-2999`), generalised from the K=2 bipartite
specialisation in `BipartiteEnum.bipartite_balanced_enum` to the
**ambient profile-match form**:

```
theorem hasBalancedPair_of_ambient_profile_match
    (a a' : α) (hne : a ≠ a')
    (h_up : ∀ z, a < z ↔ a' < z)
    (h_down : ∀ z, z < a ↔ z < a') :
    HasBalancedPair α
```

The hypothesis is the strict-`<` profile-match form of Case 1 (a, a'
have identical ambient up- and down-sets). The proof:

1. The strict-`<` hypotheses force `a ∥ a'` (irreflexivity at
   `z = a, a'`).
2. `Equiv.swap a a'` preserves `≤` by case-analysis on whether
   `x, y ∈ {a, a'}`; the non-trivial cases use the `h_up` / `h_down`
   profile equivalences after upgrading `a ≤ y` / `x ≤ a` to strict
   form via `lt_of_le_of_ne`.
3. Pullback along the swap is an involution on `LinearExt α`
   exchanging the filters `{L : L.lt a a'}` and `{L : L.lt a' a}`,
   giving `probLT a a' = 1/2`.

This is **reusable infrastructure**: any future implementation of
`hStruct` (or A8-S2 / A8-S3 below) that produces a within-band pair
with matching ambient profile can plug directly into this lemma.

### 4b. This status doc + README pointer

This file documents the situation and the recommended sub-split (§5).

### 4c. What this polecat does **not** do

* It does **not** discharge the `hStruct` slot of
  `bounded_irreducible_balanced_hybrid`. The Case 1 hypothesis
  (existence of an ambient-profile-matching within-band pair) is
  **not implied** by the hybrid theorem's hypotheses on every
  `¬ InCase3Scope` leaf — Cases 2 and 3 of `prop:in-situ-balanced`
  may apply instead, and require their own proofs.
* It does **not** modify the `bounded_irreducible_balanced_hybrid`
  signature or the `hStruct`/`hCert` slots.
* It does **not** introduce any new `sorry`, `axiom`, or
  `native_decide` shortcut. The current
  `#print axioms OneThird.width3_one_third_two_thirds` output stays
  clean (mathlib trio + `brightwell_sharp_centred`).

---

## 5. Recommended sub-split

To discharge `hStruct` constructively, split mg-A8 into three
follow-up work items:

### A8-S1 — Case 1 application: when does an ambient-profile-matching pair exist?

**Deliverable.** A theorem of the shape

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

splitting the discharge into the three cases of
`prop:in-situ-balanced`. Case 1 hits `hasBalancedPair_of_ambient_profile_match`
(this commit) directly. Cases 2 and 3 produce typed witnesses for
A8-S2 and A8-S3 to consume.

**Estimate.** ~200–400 LOC. Mostly the case analysis plumbing and
the witness predicate definitions.

### A8-S2 — Case 2 FKG monotonicity argument

**Deliverable.** Discharge of `Case2Witness L` from A8-S1, via the
Ahlswede–Daykin / FKG coupling of `prop:in-situ-balanced` Case 2
(`step8.tex:3001-3032`). The within-band pair `(a, a')` with
`Π(a) ⪯ Π(a')` admits

```
1/2 ≤ Pr_Q[a <_L a'] ≤ Pr_Q'[a <_L a'],
```

where `Q'` is obtained from `Q` by removing one comparability that
distinguishes `a` from `a'`. The rotation argument
(`step8.tex:2877-2914`) then either gives `Pr ∈ [1/2, 2/3]`
directly, or extracts a triple in `[1/3, 2/3]` from the three
`⪯`-adjacent within-`A` pairs.

**Infrastructure dependencies.**

* The mathlib FKG lemma `Mathlib.Combinatorics.SetFamily.fkg`
  (already wired through `Mathlib/LinearExtension/FKG.lean`).
* The `lowerSet_fkg_uniform_correlation` and
  `lowerSet_fkg_uniform_events` helpers
  (`FKG.lean:209, 218`).
* A new "one-comparability removal" coupling: given posets `Q`
  and `Q'` with `Q'` obtained from `Q` by adding a single relation,
  `Pr_Q[A] ≤ Pr_{Q'}[A]` for any monotone event `A`. This may
  reuse the `Mathlib.Order.UpperLower` infrastructure.

**Estimate.** ~400–800 LOC. The FKG primitives are reusable; the
profile-coupling and rotation-argument plumbing is new.

### A8-S3 — Case 3 residual: "two of three share a profile coordinate"

**Deliverable.** Discharge of `Case3Witness L` from A8-S1, restricted
to `¬ InCase3Scope` (since the certificate handles `InCase3Scope`).

**Mathematical content.** The claim of `step8.tex:3168-3170`:

> two of the three elements must share *some* coordinate of the
> two-sided profile whenever $|Q| \le 3(3w+1)$ and (L2) restricts
> the profile codomain.

To prove: in a width-3 antichain `A = {a₁, a₂, a₃}` with
`⪯`-incomparable two-sided profiles, two elements share either
`Π⁺` or `Π⁻` modulo a (L2)-permitted permutation. This shared
coordinate then either (i) gives a Case 1 ambient-profile match
on the *restricted* sub-poset (handled by A8-S1's Case 1 branch
applied to the restriction), or (ii) provides the input to a
modified Case 2 FKG argument restricted to the bands strictly
above/below the antichain.

**Estimate.** ~300–600 LOC, **including** the missing
mathematical content. This is the genuinely new work of mg-A8.

### Path C wiring (deferred to A5-G3)

A8-S1 + A8-S2 + A8-S3 together produce `hStruct`. Composed with
A5-G2's `hCert` (the band-major encoding bridge for
`case3_certificate` in `InCase3Scope`), this makes
`bounded_irreducible_balanced` constructive. Path C of
`docs/gap-analysis.md` (= A5-G3 of `docs/a5-glue-status.md`) then
wires the result into `lem_layered_balanced` to eliminate the
`hC3 : Case3Witness` hypothesis from `width3_one_third_two_thirds`.

---

## 6. References

* Polecat instructions: `mg-f92d` task body.
* `step8.tex` `prop:in-situ-balanced` (`2965-3048`); `lem:enum`
  (`3050-3067`); `rem:enumeration` (`3157-3173`);
  `rem:residual-base` (`3194-3236`).
* `lean/OneThird/Step8/Case3Struct.lean` — this commit.
* `lean/OneThird/Step8/BipartiteEnum.lean` — K=2 specialisation
  (already in tree).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1587` — the
  hybrid theorem with `hStruct`/`hCert` slots.
* `docs/a5-profile-resolution.md` — B4 hybrid resolution + scope
  analysis.
* `docs/a5-glue-status.md` — A5 partial-deliverable status (the
  `hCert` half of the dispatch).
* `docs/gap-analysis.md` — full Case3Witness gap analysis (Paths A,
  B, C).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (clean,
  unchanged by this commit).
