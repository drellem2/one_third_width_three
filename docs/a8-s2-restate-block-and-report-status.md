# A8-S2-restate (η₄) status — block-and-report (≤ 2/3 upper bound is not provable from existing Brightwell + chain-swap)

**Work item:** `mg-b0de` (lean: A8-S2-restate (η₄) — restate
`Case2FKGSubClaim` with correct direction (≤ 1/2 chain swap), redesign
consumer, add ≤ 2/3 upper bound from Brightwell covariance).

**Status:** **Block and report — case (a) of mg-b0de's hard
block-and-report rule.** The `≤ 2/3` upper bound for the strict K=2
within-band chain pair is **not** provable from existing Brightwell
sharp centred bound + chain-swap + standard probability
manipulations: the Brightwell single-element-perturbation bound
`|p(Q) − p(Q−z)| ≤ 2/|Q|` is too loose for the K=2 regime
(`|Q| ≤ 6`), and the existing `Case2BipartiteBound`-style argument
covers only `K=2, w=0` (relying on `bipartite_balanced_enum`'s
`hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b` hypothesis, which fails for
`w ≥ 1`). The paper's `≤ 2/3` proof (`step8.tex:2916-2940`) routes
through bipartite extremal enumeration with FKG-monotonicity
averaging, requiring infrastructure beyond chain-swap + Brightwell —
specifically the deferred A8-S2-cont cross-poset
probability-normalised FKG monotonicity. Per `mg-b0de`'s
pre-committed pivot, η₅ (drop SubClaim path; keep `hC3` in headline)
is the recommended next round.

**Author.** `pc-b0de` polecat, 2026-04-27.

---

## TL;DR

* **Step 1 — restate.** The SubClaim direction restatement (`≤ 1/2`,
  not `≥ 1/2`) is **mathematically straightforward**: with the
  corrected direction, `Case2FKGSubClaim L` is provable as a theorem
  via `probLT_le_half_of_chain` (mg-ba0c, `Case2Rotation.lean:629`)
  applied to the `pair` and `chain` fields.

* **Step 3 — `≤ 2/3` upper bound — UNPROVABLE from existing
  infrastructure.** For the strict K=2 within-band chain pair
  `(a, a')` with `upper(a) ⊊ upper(a')`, we need `probLT a' a ≤ 2/3`
  (equivalently `probLT a a' ≥ 1/3`). None of the in-tree paths
  works:

  - **Brightwell sharp centred** (`BrightwellAxiom.lean:159`) gives
    `|p_{xy}(Q) − p_{xy}(Q−z)| ≤ 2/|Q|` (single-element
    perturbation). Specialised to `z` = unique strictness witness in
    `upper(a') \ upper(a)`, with `Q−z` being the symmetric
    configuration where `Pr_{Q−z}[a < a'] = 1/2`, yields
    `Pr_Q[a < a'] ∈ [1/2 − 2/|Q|, 1/2 + 2/|Q|]`. To get
    `Pr ≥ 1/3` (i.e., `Pr_Q[a' < a] ≤ 2/3`), we need
    `1/2 − 2/|Q| ≥ 1/3`, i.e., `|Q| ≥ 12`. **K=2 has
    `|Q| = |α| ≤ 6`**, so the Brightwell bound is vacuous in our
    regime.

  - **`Case2BipartiteBound.lean`** (mg-ed4d) proves
    `probLT u v = 1/2` for K=2, **`w = 0`** within-band pairs via
    `bipartite_balanced_enum` with the `hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b`
    bipartite-forced hypothesis. **For `w ≥ 1`** (the regime of the
    consumer `bipartite_balanced_enum_general`, mg-02c2), `hAB` is
    NOT forced (`forced_lt` requires `band x + w < band y`, which is
    vacuous at `K=2, w ≥ 1`), so the existing bipartite enumeration
    does not lift. Building an `hAB`-free bipartite enumeration is
    essentially the deferred A8-S2-cont scope (~2000-3500 LoC per
    `docs/a8-s2-status.md` §5).

  - **Cross-poset count-form FKG**
    (`probLT'_count_div_le_of_relExt`, `RelationPoset/FKG.lean:521`)
    bounds count numerators across augmented posets but does NOT
    give the probability-normalised form needed (different
    denominators). The probability form is the deferred A8-S2-cont
    headline (`Mathlib/RelationPoset/FKG.lean §11`,
    lines 407-426).

  - **Iterating Brightwell across multiple strictness witnesses**
    gives a harmonic-sum bound `2 · H_{|Q|}` which is even weaker
    (≈ 4.9 for `|Q| = 6`).

  - **Chain swap on `(a, z)` for `z ∈ upper(a') \ upper(a)`** does
    NOT apply: the chain hypothesis on `(a, z)` requires
    `∀ w, a < w → z < w` and `∀ w, w < z → w < a`, both of which
    fail in the natural K=2 strict-chain configuration (band-2
    elements are mutually incomparable; `a' < z` puts `a'` in
    `lower(z)` but `a ∥ a'` rules out `a' < a`).

* **Step 2 — consumer redesign — depends on Step 3.** The redesign
  combines `≤ 1/2` (chain swap) with `≤ 2/3` (the bound that fails
  to discharge in Step 3). Without Step 3, the consumer
  redesign cannot close `HasBalancedPair α` from a strict chain pair
  alone; it would have to take a NEW hypothesis (call it
  `Case2UpperBound`) for the missing `≤ 2/3`, which simply renames
  the unprovable burden — not a meaningful improvement over the
  current `Case2FKGSubClaim` hypothesis (modulo direction
  correctness).

* **Acceptance criteria not met.** `mg-b0de`'s acceptance requires
  Step 3 to discharge cleanly with no new axioms, no `sorry`, and
  `lake build` clean. Without an in-tree `≤ 2/3` proof, the criteria
  are not satisfiable.

* **No code changes landed.** Per the brief's "audit-as-deliverable"
  instruction under hard block-and-report.

* **Pre-committed pivot recommended: η₅** (drop SubClaim path; keep
  `hC3`; mg-5f0c reverts to v5 (δ) park; PATH A docs become the
  close, with disclosure update for the mg-27c2 issue).

---

## 1. What was supposed to land

Per `mg-b0de`'s brief, R3.1-compatible η₄ pivot:

* **Step 1.** Restate `Step8.InSitu.Case2FKGSubClaim`'s `pair` and
  `chain` field directions from `1/2 ≤ probLT a a'` (FALSE, per
  pc-a79e block-and-report) to `probLT a a' ≤ 1/2` (TRUE, chain
  swap). Discharge `Case2FKGSubClaim L` as a theorem via
  `probLT_le_half_of_chain` (mg-ba0c).

* **Step 2.** Redesign `strictCase2Witness_m2_balanced` and
  `case2Witness_balanced_under_FKG` to combine the now-true
  `≤ 1/2` (chain swap) with a separately-derived `≤ 2/3` upper
  bound for the reverse direction (`probLT a' a ≤ 2/3`), giving a
  balanced pair via `[1/3, 2/3]` containment.

* **Step 3.** Prove `probLT a' a ≤ 2/3` for any K=2 strict
  within-band `⪯`-chain pair, integrating the existing Brightwell
  axiom (`BrightwellAxiom.lean:159`) with chain-swap and standard
  probability manipulations. Estimated 100-300 LoC per the brief.

* **Step 4.** Verify `lake build OneThird` rebuilds clean and that
  mg-02c2 / mg-84f2 / mg-c0c7 downstream theorems compile.

Hard block-and-report rule (case a): "the ≤ 2/3 upper bound from
Brightwell covariance does NOT discharge cleanly".

---

## 2. Why Step 1 is straightforward

The current `Case2FKGSubClaim L` (`Case2Rotation.lean:772`) is:

```lean
structure Case2FKGSubClaim (L : LayeredDecomposition α) : Prop where
  pair  : … → (1 : ℚ) / 2 ≤ probLT a a'        -- FALSE on natural inputs
  chain : … → (1 : ℚ) / 2 ≤ probLT a₁ a₂ ∧ …    -- same direction issue
```

Restated:

```lean
structure Case2FKGSubClaim (L : LayeredDecomposition α) : Prop where
  pair  : … → probLT a a' ≤ (1 : ℚ) / 2          -- TRUE, chain swap
  chain : … → probLT a₁ a₂ ≤ (1 : ℚ) / 2 ∧ …      -- same
```

Discharged by:

```lean
theorem case2FKGSubClaim_holds (L : LayeredDecomposition α) :
    Case2FKGSubClaim L where
  pair  a a' hne hband hi hu hd :=
    probLT_le_half_of_chain hne hi hu hd
  chain a₁ a₂ a₃ … :=
    ⟨probLT_le_half_of_chain h12 hi12 hu12 hd12,
     probLT_le_half_of_chain h23 hi23 hu23 hd23,
     probLT_le_half_of_chain h13 hi13 hu13 hd13⟩
```

(where `h13/hu13/hd13` come from `StrictCase2WitnessChain.chain_one_three`
`Case2Rotation.lean:178`).

Approximately **15-25 LoC** for Step 1 alone. **No barriers.**

But Step 1 alone is not a complete deliverable: the consumer
(`strictCase2Witness_m2_balanced`, `strictCase2Witness_balanced_under_FKG`,
`case2Witness_balanced_under_FKG`) currently relies on the FALSE
`≥ 1/2` direction to derive `probLT a a' = 1/2` (combining `≥ 1/2`
hypothesis with `≤ 1/2` chain swap) and hence the balanced pair
witness `1/3 ≤ 1/2 ≤ 2/3`. With the corrected direction, only the
`≤ 1/2` half remains — the `≥ 1/3` lower bound (equivalently
`probLT a' a ≤ 2/3`) is **NOT** derivable from the restated
SubClaim alone.

So Step 1 without Step 3 breaks `lake build` (the consumer's proof
no longer goes through). Step 1 is meaningful only paired with a
working Step 3.

---

## 3. Why Step 3 fails: detailed analysis

The strict K=2 within-band chain pair `(a, a')` has:

* `band a = band a'` (same band, K=2 ⇒ band ∈ {1, 2}).
* `a ∥ a'` (band antichain).
* `upper(a) ⊊ upper(a')` (strict ⪯-chain, upper-set inclusion
  proper).
* `lower(a') ⊆ lower(a)` (vacuously true for K=2: lower sets of
  band-1 elements are empty; for band-2 pairs, `lower(a')` and
  `lower(a)` are subsets of band 1).

Goal: `probLT a' a ≤ 2/3` (equivalently `probLT a a' ≥ 1/3`).

### 3.1 Brightwell sharp centred bound is too loose

`brightwell_sharp_centred` (`BrightwellAxiom.lean:159`) gives, in
its rational form (`brightwell_sharp_centred_rat:195`),

```
|Σ_{L' ∈ A} f(L') − |A| · f̄|  ≤  2 · N / m,
```

where `m = |Q| = |α| + 1` (paper's ambient depth-`m` poset) and
`A := {L' : x <_{L'} y}`. After dividing by `N · N'` and using
the fibre-sum identity (consumed in `OneElemPerturb.lean:709`'s
`one_elem_perturb`):

```
|p_{xy}(Q) − p_{xy}(Q − z)|  ≤  2 / |Q|.
```

Take `x = a`, `y = a'`, and `z` = a strictness witness in
`upper(a') \ upper(a)`. If `z` is the **unique** strictness witness
(i.e., `upper(a) = upper(a') \ {z}`), then in `Q − z`:

* `upper(a) ∩ (α \ {z}) = upper(a)` (z ∉ upper(a)),
* `upper(a') ∩ (α \ {z}) = upper(a') \ {z} = upper(a)`,

so the pair `(a, a')` is symmetric in `Q − z`. The Case 1 ambient
profile match collapse (`hasBalancedPair_of_ambient_profile_match`,
mg-f92d, `Step8.InSitu.Case3Struct`) gives
`probLT_{Q−z}[a < a'] = 1/2`.

Combining:

```
|probLT_Q[a < a']  −  1/2|  ≤  2 / |Q|.
```

To extract `probLT_Q[a' < a] ≤ 2/3`, equivalent to
`probLT_Q[a < a'] ≥ 1/3`, we need

```
1/2  −  2/|Q|  ≥  1/3,    ⟺    |Q|  ≥  12.
```

**K=2 has `|Q| = |α| ≤ 6`** (sum of two band sizes, each `≤ 3` by
`band_size`). So Brightwell's bound is `≥ 1/2 − 2/6 = 1/6`, giving
only `probLT_Q[a' < a] ≤ 5/6`. **Vacuous for the `≤ 2/3` target.**

### 3.2 Case2BipartiteBound is K=2, w=0 only

`Case2BipartiteBound.lean` (mg-ed4d) proves
`probLT_le_two_thirds_of_within_band_K2_w0` for **K=2, w=0** layered
decompositions. The proof routes through `bipartite_balanced_enum`'s
`probLT_eq_half_of_same_layer`, which requires
`hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b` (bipartite forced).

For K=2, the bipartite forced condition `hAB` is established by
`bandSet_one_le_bandSet_two_of_w0` (`Case2BipartiteBound.lean:182`),
which **requires `L.w = 0`** (`forced_lt : band x + w < band y → x < y`
needs `1 + w < 2`, i.e., `w = 0`).

The consumer of mg-b0de (`bipartite_balanced_enum_general`,
mg-02c2) has hypothesis `hw : 1 ≤ L.w` — it operates at `w ≥ 1`,
where `hAB` does NOT hold and `Case2BipartiteBound` does NOT lift.

Generalising `Case2BipartiteBound` to `K=2, w ≥ 1` would require
an `hAB`-free bipartite enumeration argument, equivalent in
combinatorial content to the deferred A8-S2-cont scope (cross-poset
probability-form FKG monotonicity, ~2000-3500 LoC per
`docs/a8-s2-status.md` §5).

### 3.3 Cross-poset count-form FKG is not enough

`probLT'_mono_of_relExt` (`RelationPoset/FKG.lean:464`) gives
count-form cross-poset monotonicity:

```
For Q.Subseteq Q' (Q' ⊋ Q):
  |{L' ∈ LE(Q') : S(L'.iI k)}|  ≤  |{L ∈ LE(Q) : S(L.iI k)}|.
```

Applied to the natural augmentation `Q'' := Q ∪ {a < z : z ∈ upper(a') \ upper(a)}`
(which forces upper(a) = upper(a'), making the pair symmetric):

```
|{LE(Q'') : a < a'}|  ≤  |{LE(Q) : a < a'}|.
```

In `Q''`, the pair is symmetric, so
`Pr_{Q''}[a < a'] = 1/2`, i.e.,
`|{LE(Q'') : a < a'}| = |LE(Q'')| / 2`.

Therefore:

```
|{LE(Q) : a < a'}|  ≥  |LE(Q'')| / 2.
```

Dividing by `|LE(Q)|`:

```
Pr_Q[a < a']  ≥  |LE(Q'')| / (2 · |LE(Q)|).
```

This gives `Pr_Q[a < a'] ≥ 1/3` if and only if
`|LE(Q'')| / |LE(Q)| ≥ 2/3`. Equivalently,
`Pr_Q[a < z_i for all z_i ∈ upper(a') \ upper(a)] ≥ 2/3`.

This is the same `≤ 2/3` content one level deeper: bounding the
joint probability of multiple `a < z_i` events. Without
probability-form cross-poset FKG (the deferred A8-S2-cont
infrastructure), there is no clean way to bound this joint
probability.

**Empirical confirmation.** In the minimal counterexample of
pc-a79e (`α = {a, a', y}`, `a' < y`, K=2, w=1):

* `|LE(Q)| = 3`, `|LE(Q'')| = 2` (LE(Q'') requires both `a < y`
  and `a' < y`). Ratio `2/3` exactly. `Pr_Q[a < a'] = 1/3`
  exactly. Bound is tight.

In a 4-element example (`α = {a, a', y, z}`, `a' < y`, `a' < z`,
`a < y`, K=2, w=1): `|LE(Q)| = 5`, `|LE(Q'')| = 4`, ratio `4/5`.
`Pr_Q[a < a'] = 2/5 ≥ 1/3` ✓. Both examples respect the bound but
both witness it being a coincidence of the specific configuration,
not derivable from chain-swap + Brightwell alone.

### 3.4 Chain swap on auxiliary pairs does not apply

For `z ∈ upper(a') \ upper(a)`, the chain hypothesis on `(a, z)`
requires:

* `∀ w, a < w → z < w` (upper(a) ⊆ upper(z)). For K=2 with
  `a` in band 1 and `z` in band 2: `upper(z) ⊆ band ≥ 2 = ∅`
  (band 2 is an antichain by `band_antichain`). So
  `upper(z) = ∅`, and `upper(a) ⊆ ∅` requires `upper(a) = ∅`.
  Fails in general.
* `∀ w, w < z → w < a` (lower(z) ⊆ lower(a)). `lower(z)` includes
  `a'` (since `a' < z` is forced). But `a ∥ a'`, so `a' < a` is
  false. Hypothesis fails.

So `probLT_le_half_of_chain` does not apply to `(a, z)`. There is
no direct chain swap for the auxiliary `Pr_Q[a < z]` event.

### 3.5 Iterating Brightwell across multiple strictness witnesses

If `|upper(a') \ upper(a)| = k > 1`, going from `Q` to `Q''` adds
`k` comparabilities, each contributing a Brightwell perturbation
of magnitude at most `2/m_i` (where `m_i` is the size at step `i`,
which decreases as we delete and add back elements; or remains at
`|Q|` if we just iteratively add comparabilities to the same poset
size).

In the additive bound, the cumulative perturbation is at most
`Σ_i 2/m_i`. For fixed `m = |Q| ≤ 6` and `k` strictness witnesses,
this is `2k/m`, which can be ≥ 1/2 for `k ≥ m/4`. Vacuous.

A more careful Brightwell-style covariance argument might tighten
this, but each new step requires the full Brightwell infrastructure
to be re-applied — and the infrastructure as currently formalised
(`brightwell_sharp_centred`) gives only the single-element form.
Multi-element / chain-form covariance is NOT in tree.

### 3.6 Direct enumeration (Decide tactic)

For K=2 with band sizes ≤ 3, `|α| ≤ 6`. The number of distinct
K=2 layered decompositions modulo automorphism is finite. In
principle, a Lean `decide` tactic could enumerate all
configurations and verify `probLT a' a ≤ 2/3` for each
strict-chain pair.

However:

* `LinearExt α` is not decidable-finiteness-friendly without
  significant boilerplate (the existing `bipartite_balanced_enum`
  required ~600 LoC of structural enumeration over `|A|, |B| ≤ 3`
  with `hAB`).

* Without `hAB`, the case enumeration grows: `|α| ≤ 6` partitioned
  into two antichains with arbitrary cross-comparabilities,
  modulo automorphism. The ambient `bipartite_balanced_enum`
  enumeration is the natural structural template, but it relies
  on `probLT_eq_half_of_same_layer`'s `Equiv.swap` automorphism —
  which fails in the strict-chain (asymmetric) configuration.

* Conservatively, an `hAB`-free K=2 bipartite enumeration would be
  500-1500 LoC, well above the brief's 100-300 LoC target and
  matching the deferred A8-S2-cont scope.

### 3.7 Summary of all attempted paths

| Path                                            | Status                                                                |
|-------------------------------------------------|-----------------------------------------------------------------------|
| Brightwell sharp centred (single-element)       | Vacuous for `\|Q\| ≤ 6` (needs `\|Q\| ≥ 12` for `≤ 2/3`)              |
| Brightwell iterated across `k` witnesses        | Cumulative bound vacuous (`2k/m` ≥ 1/2 for moderate `k`)               |
| `Case2BipartiteBound` lift                      | Only K=2 **w=0**; consumer needs **w ≥ 1**                            |
| Cross-poset count-form FKG                      | Reduces to `Pr_Q[a < z_i ∀ i] ≥ 2/3`, same problem one level deeper   |
| Chain swap on `(a, z)`                          | Chain hypothesis fails: `upper(z) = ∅`, `a' ∈ lower(z)` but `a ∥ a'`   |
| Direct `decide` / structural enumeration         | Estimated 500-1500 LoC, matches deferred A8-S2-cont scope             |

**Conclusion.** No 100-300 LoC clean path exists from in-tree
infrastructure (chain-swap + Brightwell + FKG count-form) to
`probLT a' a ≤ 2/3` for K=2 strict within-band chain pairs. The
brief's hard block-and-report rule fires under case (a).

---

## 4. Direction-bearing error candor check

Per the build candor clause: I checked whether the Brightwell bound
applies in a direction-bearing-error sense.

* `brightwell_sharp_centred` is symmetric: `|p(Q) − p(Q−z)| ≤ 2/m`.
  No direction issue.
* The `≤ 2/3` upper bound is on `probLT a' a`, equivalently a lower
  bound on `probLT a a'`. Both directions checked: the loose
  Brightwell bound rules out neither direction.
* The chain-swap direction is consistent across pc-a79e's analysis,
  this analysis, and `step8.tex:2855-2875`. No new direction-bearing
  error surfaced.
* `Case2BipartiteBound`'s `probLT_le_two_thirds_of_within_band_K2_w0`
  matches the paper's `≤ 2/3` direction (paper's labelling
  `Pr[a_1 <_L a_m] ≤ 2/3` ⟺ Lean's `probLT a' a ≤ 2/3` with the
  convention `a` has fewer upper edges).

**No second direction-bearing error surfaced.** The blocker is
purely a magnitude / regime issue (Brightwell too loose for K=2
sized posets).

---

## 5. What this means for the consumer redesign (Step 2)

Without Step 3, the consumer redesign is ill-posed. The
`strictCase2Witness_m2_balanced` function currently has shape:

```lean
theorem strictCase2Witness_m2_balanced
    {a a' : α} … (hp : (1 : ℚ) / 2 ≤ probLT a a') :   -- FALSE
    HasBalancedPair α := …
```

After Step 1 restate, with Step 3 working, it would become:

```lean
theorem strictCase2Witness_m2_balanced
    {a a' : α} … :
    -- chain swap gives ≤ 1/2 internally;
    -- ≤ 2/3 reverse direction supplied by the (new) upper-bound proof
    HasBalancedPair α := by
  have h_le_half : probLT a a' ≤ 1/2 := probLT_le_half_of_chain …
  have h_ge_third : 1/3 ≤ probLT a a' := …  -- THIS IS THE GAP
  refine ⟨a, a', hi, h_ge_third, ?_⟩
  linarith
```

Without an in-tree proof of `1/3 ≤ probLT a a'`, the function
cannot be discharged unconditionally. The only options are:

1. **Add a NEW hypothesis** `h_upper : probLT a' a ≤ 2/3` to the
   consumer's signature, replacing or adding to the existing
   `Case2FKGSubClaim` hypothesis. This **shifts** the unprovable
   burden but does not eliminate it (downstream callers still cannot
   construct the new hypothesis without the same missing
   infrastructure). Effectively renames the problem.

2. **Drop the consumer entirely** and route `Case2Witness L`
   through a different discharge path (η₅ scope; not
   single-polecat).

3. **Add the `≤ 2/3` upper bound as a project axiom**, similar to
   how `brightwell_sharp_centred` is retained as a published
   external result. **Per `mg-b0de`'s constraints, NEW project
   axioms are explicitly forbidden.** This option is foreclosed.

Per `mg-b0de`'s acceptance criteria, none of (1)/(2)/(3) satisfies
the brief: (1) does not produce a closure (only renames), (2) is
out of single-polecat scope, (3) violates the no-new-axiom
constraint.

---

## 6. Pre-committed pivot recommendation

Per `mg-b0de`'s "Pre-committed next-round pivot (PM-side)" §:

> Case (a): if the ≤ 2/3 upper bound needs new cross-poset
> infrastructure → η₅ (drop SubClaim path; keep hC3; mg-5f0c
> reverts to v5 (δ) park; PATH A docs become the close, with
> disclosure update for the mg-27c2 issue). PM mails Daniel.

This is the recommended pivot. The mg-27c2 disclosure update
should record both:

* The original direction error (pc-a79e's finding).
* This polecat's confirmation that the η₄ pivot's `≤ 2/3` upper
  bound is also out of scope without A8-S2-cont infrastructure.

The compound-automorphism arc (mg-84f2 / mg-c0c7 / mg-02c2) does
NOT depend on `Case2FKGSubClaim` — it handles K=2 Case 1 (ambient
match) and K=2 Case 3 (NoWithinBandPreceq) cleanly. Only the K=2
strict Case 2 branch routes through the unprovable hypothesis,
matching the disclosure pattern of v5 / v6 hC3 hypothesis.

η₅ retains all the compound-automorphism work (mg-84f2 / mg-c0c7 /
mg-02c2) as production-quality K=2 Case-1 + Case-3 closures, with
the strict Case-2 sub-case guarded by an explicit `hC3`-style
hypothesis in the headline (matching the existing v5 / v6 framing
documented in `docs/a5-g3e-path-c-wiring-v6-status.md`).

---

## 7. What this polecat lands

* **This status doc** (`docs/a8-s2-restate-block-and-report-status.md`).
* **No Lean changes.** No code modifications to `Case2Rotation.lean`,
  `BipartiteEnumGeneral.lean`, or any other file. The current
  in-tree `Case2FKGSubClaim` retains its (mathematically wrong)
  `≥ 1/2` direction; restating it without a working consumer
  redesign would break `lake build` and provide no functional
  improvement (the consumer would still be unreachable).
* **No new axioms, no `sorry` / `admit`.**
* **`#print axioms width3_one_third_two_thirds`** unchanged from
  baseline.

The decision to leave the in-tree `Case2FKGSubClaim` direction
unchanged (rather than restating it as a stand-alone correction) is
deliberate: the consumer's proof structure currently hinges on the
combination `≥ 1/2 ∧ ≤ 1/2 ⇒ = 1/2`, and the `≥ 1/2` direction —
though wrong on natural inputs — keeps the proof-internal logic
compilable. Restating the SubClaim direction without a working
`≤ 2/3` upper bound would require either (i) breaking `lake build`
(unacceptable), or (ii) moving the unprovable burden to a renamed
hypothesis (not a meaningful improvement). Per the brief's
"audit-as-deliverable" instruction under hard block-and-report, the
status doc itself is the deliverable, and η₅'s structural drop of
the SubClaim path is the correct next step rather than a partial
in-tree restatement.

---

## 8. References

* **mg-b0de** (this ticket) — task body with η₄ pivot brief and
  hard block-and-report rule.
* **mg-a79e** (`docs/a8-path-b-block-and-report-status.md`,
  commit `64f2d87`) — pc-a79e block-and-report establishing the
  SubClaim's `≥ 1/2` direction is FALSE on natural inputs.
* **mg-602e** — Daniel OVERRIDE.
* **mg-27c2** — `Case2FKGSubClaim` structure currently in tree
  (this status doc does not modify).
* **mg-ba0c** (`docs/a8-s2-rotation-residual-status.md` §3) —
  earlier independent flag of the direction issue (chain-swap /
  FKG sub-claim direction mismatch).
* **mg-43f3** (`docs/a8-s2-strict-witness-status.md`) — earlier
  closure-shape analysis on the StrictCase2 closure.
* **mg-b699** — brightwell retention decision
  (`lean/AXIOMS.md`); Brightwell sharp centred axiom retained as
  faithful transcription of published external result.
* **mg-ed4d** — `Case2BipartiteBound`, K=2 w=0 lift.
* **mg-02c2** — `bipartite_balanced_enum_general`, the K=2
  consumer (would route through the unprovable `Case2FKGSubClaim`
  in its Case 2 branch).
* **mg-84f2** / **mg-c0c7** — compound-automorphism arc; UNAFFECTED
  by this block-and-report (no dependency on `Case2FKGSubClaim`).
* **mg-5f0c** (`docs/a5-g3e-path-c-wiring-v6-status.md`) — v6 wiring
  status with `hC3`-style hypothesis (the η₅ fallback pattern).
* `lean/OneThird/Step8/Case2Rotation.lean:629` —
  `probLT_le_half_of_chain` (chain swap, mg-ba0c).
* `lean/OneThird/Step8/Case2Rotation.lean:772` —
  `Case2FKGSubClaim` structure (mg-27c2).
* `lean/OneThird/Step8/Case2Rotation.lean:813` —
  `strictCase2Witness_m2_balanced` (consumer's `m=2` branch).
* `lean/OneThird/Step8/Case2Rotation.lean:870` —
  `strictCase2Witness_balanced_under_FKG` (consumer's dispatch).
* `lean/OneThird/Step8/Case2Rotation.lean:894` —
  `case2Witness_balanced_under_FKG` (consumer's headline form).
* `lean/OneThird/Step8/Case2BipartiteBound.lean:260` —
  `probLT_le_two_thirds_of_within_band_K2_w0` (K=2 **w=0** only).
* `lean/OneThird/Step8/BipartiteEnumGeneral.lean:210` —
  `bipartite_balanced_enum_general` (K=2 **w ≥ 1** consumer,
  `Case2FKGSubClaim`-dependent).
* `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean:159` —
  `brightwell_sharp_centred` axiom.
* `lean/OneThird/Step8/OneElemPerturb.lean:709` —
  `one_elem_perturb`, `|p_{xy}(Q) − p_{xy}(Q−z)| ≤ 2/|Q|`.
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:464` —
  `probLT'_mono_of_relExt` (count-form cross-poset
  monotonicity).
* `lean/OneThird/Mathlib/RelationPoset/FKG.lean:407-426` —
  documented future work (probability-form cross-poset FKG
  monotonicity, the deferred A8-S2-cont headline lemma).
* `lean/AXIOMS.md` — `brightwell_sharp_centred` entry.
* `step8.tex:2855-2875` — paper's chain-swap argument (`m=2` `≥ 1/2`
  sub-claim direction; matches Lean's `≤ 1/2` after labelling
  conversion).
* `step8.tex:2916-2940` — paper's `≤ 2/3` upper bound argument
  (bipartite extremal enumeration with FKG-monotonicity averaging;
  the deferred A8-S2-cont scope).
* `lean/PRINT_AXIOMS_OUTPUT.txt` — current axioms baseline (this
  docs-only commit does not change it).

---

## 9. Final state

* No code changes landed. The in-tree `Case2FKGSubClaim` retains
  its (incorrect) `≥ 1/2` direction; correcting it without a
  working consumer redesign would break `lake build`.
* This status doc records why the η₄ pivot's `≤ 2/3` upper bound
  cannot be discharged from existing infrastructure, and why the
  consumer redesign is consequently ill-posed without new
  cross-poset infrastructure.
* η₅ (drop SubClaim path; keep `hC3`) is the recommended pivot
  per `mg-b0de`'s pre-committed plan.
* `pc-b0de` will mail mayor with the verdict and `mg done` is
  conditional on refinery merge of this status doc.
