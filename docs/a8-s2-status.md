# mg-A8 sub-split A8-S2 status — `pc-8801` polecat report

**Work item:** `mg-8801` (A8-S2: discharge `Case2Witness L → HasBalancedPair α`
via the Ahlswede–Daykin / FKG profile-ordering argument of
`prop:in-situ-balanced` Case 2, `step8.tex:3001-3032`).
**Status:** partial — Case 1 collapse + WLOG reduction to the strict
`⪯`-comparability sub-case lifted as reusable infrastructure;
the FKG monotonicity argument itself **not** in tree.
**Author:** `pc-8801` polecat, 2026-04-26.

---

## 1. What was supposed to land

> A8-S2 (`mg-8801`) — Case 2 FKG monotonicity argument
> (within-band ⪯-comparable profiles).
>
> Discharge `Case2Witness L` from A8-S1 (mg-48db, just merged) via
> the Ahlswede–Daykin / FKG coupling of `prop:in-situ-balanced`
> Case 2 (`step8.tex:3001-3032`). The within-band pair `(a, a')`
> with `Π(a) ⪯ Π(a')` admits
>
> ```
> 1/2 ≤ Pr_Q[a <_L a'] ≤ Pr_Q'[a <_L a']
> ```
>
> where `Q'` is obtained from `Q` by removing one comparability
> that distinguishes `a` from `a'`. The rotation argument
> (`step8.tex:2877-2914`) then either gives `Pr ∈ [1/2, 2/3]`
> directly, or extracts a triple in `[1/3, 2/3]` from the three
> `⪯`-adjacent within-`A` pairs.
>
> Estimate: ~400-800 LOC.

---

## 2. What's in tree at the start of this polecat

After mg-48db (A8-S1, just merged at `98334af`):

* **`Step8.InSitu.Case2Witness L`** (`Case3Dispatch.lean:156-158`) —
  the typed predicate this polecat must discharge:

  ```
  def Case2Witness (L : LayeredDecomposition α) : Prop :=
    ∃ a a' : α, a ≠ a' ∧ L.band a = L.band a' ∧
      (∀ z, a < z → a' < z) ∧ (∀ z, z < a' → z < a)
  ```

  Encoding: `a` has more lower-comparabilities, `a'` has more
  upper-comparabilities — i.e., in the paper's notation
  `Π(a') ⪯ Π(a)` (`a'` has at least as many reasons to come early
  as `a`). Hence the target is `Pr_Q[a' <_L a] ≥ 1/2`
  (equivalently `Pr_Q[a <_L a'] ≤ 1/2`), plus the symmetric
  `≤ 2/3` bound that yields balance.

* **`case1_dispatch_inScope`** and
  **`case1_dispatch_balanced_or_witness`**
  (`Case3Dispatch.lean:244, 271`) — A8-S1's typed dispatch into
  Case 1 / Case 2 / Case 3, with Case 1 already wired through
  `hasBalancedPair_of_ambient_profile_match` (mg-f92d).

* **`hasBalancedPair_of_ambient_profile_match`** (`Case3Struct.lean:263`,
  mg-f92d) — Case 1 ambient form: from
  `(∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')`, get
  `HasBalancedPair α` via the `Equiv.swap a a'` automorphism.
  The "swap" is **only** an automorphism when the two profiles
  match, which is the symmetric case of Case 2.

* **FKG primitives** (`Mathlib/LinearExtension/FKG.lean`) —
  uniform FKG correlation on a finite distributive lattice
  (`fkg_uniform_correlation`), specialised to `LowerSet α`
  (`lowerSet_fkg_uniform_correlation`, `lowerSet_fkg_uniform_events`),
  the product lattice `Fin (n+1) → LowerSet α`
  (`pi_fkg_uniform_correlation`), and the level-`k` projection from
  `LinearExt α` (`fkg_uniform_initialLowerSet`). All operate on a
  **single fixed `PartialOrder α`**.

---

## 3. The honest picture

### 3a. The paper's argument crosses two distinct posets

Re-reading `step8.tex:2858-2875` (the K=2 sub-claim in
`prop:bipartite-balanced` Case 2, on which `prop:in-situ-balanced`
Case 2 is built):

> Couple `𝓛(Q)` with the distribution `𝓛(Q')` obtained by
> "equalizing" `a_i` and `a_{i+1}` ... considering the poset `Q'`
> where `a_{i+1}`'s profile is replaced by `Π(a_i)`, which adds at
> least one comparability ... Starting from the symmetric poset
> `Q''` in which `a_i` and `a_{i+1}` share the profile
> `Π(a_i) ∩ Π(a_{i+1})`, `Pr_{Q''}[a_i <_L a_{i+1}] = 1/2`;
> successively adding back the comparabilities of `a_i` ... raises
> this probability to its value in `Q`. Hence
> `Pr_Q[a_i <_L a_{i+1}] ≥ 1/2`.

So the paper's argument constructs **three distinct posets** on
the same underlying ground set:

* `Q` — the original (input) poset.
* `Q'` — obtained from `Q` by adding comparabilities to `a_{i+1}` so
  that `Π_{Q'}(a_{i+1}) = Π_Q(a_i)` (symmetric profile).
* `Q''` — obtained from `Q` by *removing* comparabilities from `a_i`
  (or, equivalently, restricting both `a_i`, `a_{i+1}` to share
  `Π(a_i) ∩ Π(a_{i+1})`).

Each modification (adding or removing one comparability) is
FKG-monotone for `Pr[a_i <_L a_{i+1}]`, which is the actual
content of the Ahlswede–Daykin step. The chain of inequalities
builds `Pr_Q ≥ Pr_{Q'} = 1/2` (or, going the other way,
`Pr_Q ≥ Pr_{Q''} = 1/2`).

### 3b. Lean's typeclass `PartialOrder α` makes this awkward

In Lean / Mathlib, `PartialOrder α` is a typeclass on the type `α`,
so `α` carries a *fixed* `≤` relation. The paper's argument
requires comparing linear extensions of *three different posets on
the same `α`* — which forces one of two structural choices:

**Option A: relations as data.** Define an alternative finite
poset notion as a `Finset (α × α)` (or `α → α → Prop`) satisfying
poset axioms as a hypothesis. Re-implement linear extensions
(`LinearExt'`), counting (`numLinExt'`), probability
(`probLT'`), Birkhoff transport (`initialLowerSet'`), and FKG
(`fkg_uniform_initialLowerSet'`) on top of the data version.
Then prove:

```
relPoset_subseteq Q Q' →
  (∀ {a b : α}, Q.lt a b → Q'.lt a b) →
  ∀ E : LinearExt' Q' → Prop,
    UpClosed E →
    (probLT' Q').onEvent E ≤ (probLT' Q).onEvent E
```

This is the FKG monotonicity for adding constraints.

**Estimated cost:** ~1500-2500 LOC. The bulk is reproducing the
existing `LinearExt α` API (Fintype, Subtype, FiberSize,
Birkhoff, FKG) on the data version. The actual Case 2 argument
is then ~200-400 LOC on top.

**Option B: ambient empty-relation poset.** Take the universal
empty-relation poset `αₑ` (the discrete order on `α` — only `x ≤ x`)
as the ambient, and view `Q` and `Q'` as augmentations represented
by the set of added comparabilities. Linear extensions of any
`Q` then live inside `LinearExt αₑ` (which is just permutations).

This avoids the data-poset duplication, but loses the cleanness of
the Birkhoff transport (`αₑ`'s `LowerSet` lattice is the entire
`Set α`, with no order constraint pruning the chains). The FKG
monotonicity becomes a statement about subsets of permutations,
which is *not* directly FKG-on-a-distributive-lattice and would
need a separate proof (essentially a re-derivation of the
Ahlswede–Daykin argument from scratch).

**Estimated cost:** ~2000-3500 LOC. Cleaner-feeling but actually
harder, because the existing FKG primitives don't apply.

**Option C: full mathlib upstreaming.** Contribute the
data-poset version of `LinearExt` to mathlib, then build A8-S2 on
top. Mathlib's existing linear-extension theory is already
data-relation-based (`Mathlib.Order.Extension.Linear`); extending
it to FKG-monotonicity-under-relation-augmentation would be a
~2000-3000 LOC mathlib PR, with a multi-month review cycle.

### 3c. Why Brightwell's proof in `Brightwell1999` does not transfer cleanly

`Brightwell1999` (cited in `step8.tex:1042` for the F6 sharp
centred bound) gives an FKG argument *within a single poset's*
linear extensions, viewing them as ideal chains in the lattice
`LowerSet α`. This is exactly what
`Mathlib/LinearExtension/FKG.lean` ports.

But the F6 bound is `Pr[size(I_k) ≥ t]` — a probability over a
single poset's randomness, where the events live in the same
ambient sample space. The Case 2 argument needs `Pr_Q[E] ≥ Pr_{Q'}[E]`
— a probability over **two different sample spaces** (`𝓛(Q)` and
`𝓛(Q')` are different finite sets when `Q ≠ Q'`), which is a
genuinely different inequality.

The fact that `𝓛(Q) ⊆ 𝓛(Q')` (every linear extension of the
larger poset `Q` is a linear extension of the smaller `Q'`) is
where the FKG step bites, but extracting `Pr_Q[E] ≥ Pr_{Q'}[E]`
from the inclusion + FKG-correlation on `𝓛(Q')` is the actual
mathematical content that needs Option A or B's infrastructure.

### 3d. The rotation argument also requires new infrastructure

Even *if* we had `Pr_Q[a <_L a'] ≥ 1/2` (the sub-claim), the second
half of Case 2 (`step8.tex:2877-2914`) needs:

* The `m = 2` upper bound `Pr_Q[a <_L a'] ≤ 2/3` — argued in the
  paper by **direct enumeration of bipartite extremal
  configurations** (`step8.tex:2916-2940`), not by FKG. This is
  essentially the same machine-checked finite enumeration as the
  bipartite Case 2 of `prop:bipartite-balanced`, but applied at
  the ambient layered level. Status: would reuse the
  `bipartite_balanced_enum` infrastructure (already in tree at
  `BipartiteEnum.lean:284`), but the layered-to-bipartite
  reduction is non-trivial and is part of A8-S3's scope per the
  recommended split.

* The `m = 3` rotation argument — needs *three* `⪯`-comparable
  within-band pairs, not just one. A `Case2Witness L` only carries
  *one* such pair, so the rotation argument requires either:
  * strengthening the witness predicate to carry a `⪯`-chain of
    three within-band elements, or
  * reading off such a chain from the layered hypothesis profile
    (width 3, irreducibility, etc.) at the call site.

  Either route is a chunk of new mathematical content beyond the
  FKG primitives.

---

## 4. What this polecat lands

`lean/OneThird/Step8/Case2FKG.lean` adds three reusable lemmas (no
new sorries, no new axioms, builds clean against the existing
project):

* **`incomp_of_within_band`** —
  `L.band a = L.band a' → a ≠ a' → a ∥ a'`. Direct consequence of
  `LayeredDecomposition.band_antichain`. Reused by both A8-S2 and
  A8-S3 as a within-band incomparability primitive.

* **`case2Witness_symmetric_collapse`** — if a Case 2 pair `(a, a')`
  *also* satisfies the reverse profile inclusions
  `(∀ z, a' < z → a < z) ∧ (∀ z, z < a → z < a')`, then the two
  one-sided inclusions collapse to bi-implications, recovering the
  Case 1 ambient profile match → `HasBalancedPair α` via
  `hasBalancedPair_of_ambient_profile_match` (mg-f92d). Justifies
  the paper's parenthetical "(strictly, by the failure of Case 1)"
  on `step8.tex:3014`: the symmetric (= equal-profile) case is
  already absorbed into Case 1.

* **`case2Witness_balanced_or_strict`** — every `Case2Witness L` is
  *either* `HasBalancedPair α` (via the symmetric collapse above)
  *or* a `StrictCase2Witness L`: a within-band incomparable pair
  with strict `⪯`-comparability (one-sided inclusion holds, the
  reverse fails). The strict sub-case is the input to the deferred
  FKG monotonicity argument; the symmetric sub-case is fully
  discharged by this commit.

The `StrictCase2Witness L` predicate is recorded as the named
target shape for the deferred FKG argument, so the follow-up
discharge has a fixed signature to aim for:

```
theorem strictCase2Witness_balanced
    (L : LayeredDecomposition α) (hC2s : StrictCase2Witness L) :
    HasBalancedPair α
```

Combined with `case2Witness_balanced_or_strict`, this would give
the full `Case2Witness L → HasBalancedPair α` discharge.

`#print axioms` on the new theorems reports only the mathlib trio
(`propext`, `Classical.choice`, `Quot.sound`); no new axioms or
sorrys.

---

## 5. Recommended next steps

### A8-S2-cont — Cross-poset coupling infrastructure (the actual blocker)

**Deliverable.** Either:

* **Option A** (recommended) — add a `RelationPoset α` alternative
  to `PartialOrder α`, implement `LinearExt'`, `probLT'`, etc., and
  prove the FKG monotonicity-under-relation-augmentation lemma.
  Estimated ~1500-2500 LOC including the duplicated `LinearExt`
  API.

* **Option C** (long-term) — upstream the cross-poset FKG
  monotonicity to mathlib. Estimated multi-month review cycle.

Option B is an option but not recommended (~2000-3500 LOC, with no
reusable upstreaming).

This is the genuine mathematical / infrastructure gap. After
A8-S2-cont lands, A8-S2's `strictCase2Witness_balanced`
discharge is ~200-400 LOC on top.

### A8-S2-bipartite-bound — `Pr ≤ 2/3` from bipartite enumeration

**Deliverable.** Lift the bipartite extremal `Pr ≤ 2/3` upper
bound (`step8.tex:2916-2940`) from the K=2 setup of
`bipartite_balanced_enum` (`BipartiteEnum.lean:284`) to a
within-band statement on `LayeredDecomposition`. This is the
upper-bound counterpart to A8-S2-cont's lower bound.

Estimated ~200-400 LOC. Can land in parallel with A8-S2-cont.

### A8-S2-rotation — rotation argument for `m = 3`

**Deliverable.** Either strengthen `StrictCase2Witness` to carry
a `⪯`-chain of three within-band elements, or extract such a
chain from the layered hypothesis profile (width 3,
irreducibility, `¬ InCase3Scope`) at the call site of
`case1_dispatch_balanced_or_witness`. Then implement the rotation
argument (`step8.tex:2877-2914`).

Estimated ~300-500 LOC. Depends on A8-S2-cont and
A8-S2-bipartite-bound.

### Total revised estimate for full A8-S2

~2000-3500 LOC, dominated by the cross-poset infrastructure layer.
The original ticket estimate of ~400-800 LOC underestimated the
infrastructure cost by a factor of 4-5x; the existing FKG
primitives in tree handle within-poset correlation, not
cross-poset coupling.

---

## 6. References

* Polecat instructions: `mg-8801` task body.
* `step8.tex` `prop:in-situ-balanced` Case 2 (`3001-3032`); the
  K=2 sub-claim of `prop:bipartite-balanced` Case 2
  (`2858-2875`); rotation argument (`2877-2914`); bipartite
  extremal upper bound (`2916-2940`).
* `lean/OneThird/Step8/Case2FKG.lean` — this commit.
* `lean/OneThird/Step8/Case3Dispatch.lean` — A8-S1 typed dispatch
  (mg-48db, just merged).
* `lean/OneThird/Step8/Case3Struct.lean` — Case 1 ambient form
  (`hasBalancedPair_of_ambient_profile_match`, mg-f92d).
* `lean/OneThird/Step8/BipartiteEnum.lean` — K=2 bipartite Case 1
  (`bipartite_balanced_enum`, mg-68af).
* `lean/OneThird/Mathlib/LinearExtension/FKG.lean` — within-poset
  FKG primitives (uniform measure on `LinearExt α` via Birkhoff
  transport).
* `docs/a8-status.md` — full mg-A8 status report and original
  sub-split rationale (mg-f92d).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (clean,
  unchanged by this commit).
