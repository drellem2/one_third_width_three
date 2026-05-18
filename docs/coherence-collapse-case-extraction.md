# Width-3 1/3–2/3 — coherence-collapse case: structural extraction and proof-technique audit

**Owner.** `mg-ac13` (Daniel directive 2026-05-18T12:48Z), **SUPERSEDES**
`mg-2970`'s `R1+R2` framing. This file extracts the specific structural
property that the paper's *coherence-collapse case* assumes about `α`,
verifies it is narrower than "width-3 non-chain", and reports honestly
on the proof-technique known-ness.

**Inputs.**

- `paper/`: `step3.tex` (coherence definition), `step5.tex`
  (Rich-or-Collapse dichotomy), `step6.tex` (coherence dichotomy
  `prop:step6`), `step7.tex` (`prop:71`/`prop:72`/`prop:73`
  "coherence ⇒ collapse"), `step8.tex` (def `def:layered`,
  `lem:layered-balanced`, `prop:in-situ-balanced`, `lem:enum`).
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04).
- `docs/width3-residual-statement.md` (mg-2970) — mg-2970 `R1+R2` form
  (which this file diagnoses as misformed, then proposes the correction).
- `docs/onethird-proof-outline-audit.md` (mg-82fc) — F3
  conclusion-lift audit; per-step proof-tree tagging.
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2) —
  layered-form ↔ coherence relationship; canonicalLayered diagnosis.

---

## Verdict (top-of-page) — **GREEN-honest-stop with twist**

The paper *does* have a clean coherence-collapse case, and the
structural property it delivers IS narrower than "width-3 non-chain".
But mg-2970's `R1+R2` framing **misnames which half is the residual**
and **over-states the other half**:

| mg-2970 label | mg-2970's statement | Honest re-classification |
|---|---|---|
| `R1` | "Given `(α, L)` with `L.w ≤ 4`, balanced pair exists." | **Step 8 in full** (paper's `lem:layered-balanced`). NOT a narrow residual — it IS the entire `Step 8` work. Daniel's "R1 is the entire conjecture" complaint is **correct** with respect to "decomposes the problem any further". |
| `R2` | "For every width-3 non-chain α, `∃ L` with `L.w ≤ 4`." | **FALSE as universally quantified.** Counterexample below (§3). Properly an *axiomatic interface* (Steps 1-7 deliver `L` *only* for minimal γ-counterexamples); cannot be pursued as a free-standing Lean lemma. |

**Phase A** (§1) locates the coherence-collapse case at
`step5.tex` (R/C dichotomy) → `step6.tex prop:step6` (coherence
dichotomy) → `step7.tex prop:72` (coherence ⇒ layered).

**Phase B** (§2) extracts the structural property the case
delivers on α: **α admits a layered decomposition L (paper
`def:layered`, step8.tex:1983) with each band an antichain of size
≤ 3 and interaction width `w(L) ≤ w₀(γ) ≤ 4`.** Equivalently in
Lean: `∃ L : LayeredDecomposition α, L.w ≤ 4`.

**Phase C** (§3) gives an explicit width-3 non-chain α that does
**not** admit such an L: **α = three disjoint chains of length 10**
(|α| = 30, width 3, non-chain; minimum layered bandwidth = 9 > 4 in
*any* decomposition, singleton-band or not). This is a strictly
stronger counterexample than mg-2970's `3-antichain ⊕ 3-antichain`
(which fails *only* singleton-band cap-1; admits w=0 with two size-3
bands). The 3-disjoint-chains example rules out *any* layered L with
`w ≤ 4`.

**Phase D** (§4) reports the proof-technique status:

> **The technique IS known.** Paper-proved strong induction
> (`lem:layered-balanced`) reduces to `prop:in-situ-balanced`'s three
> cases: (1) swap-symmetry (rigorous), (2) FKG inequality on linear
> extensions (cited, `[AhlswedeDaykin1978, FKG1971]`), (3) **finite
> machine-checked enumeration** (per-w bounded; partial Lean port
> via mg-4d7b + F5a `case3_certificate`). Tag: **(a) rigorous +
> (c) cited + (a)-with-computer-aided base case**.

**Phase E** (§5) forward action:

* **Daniel's "the technique to prove R2 is unknown so we shouldn't
  even go there yet" instinct is partially right and partially
  wrong.** It is RIGHT that pursuing mg-2970's R2 as a stand-alone
  Lean lemma is futile (R2 is false — see §3). It is WRONG that the
  underlying technique is unknown; the paper-proved
  `lem:layered-balanced` strong induction *is* the technique, and it
  *is* rigorous.
* **Recommended forward action: NO new "prove the R2 narrower
  property" follow-on ticket.** The "narrower property" is exactly
  what `def:layered` + `L.w ≤ 4` already states. Steps 1-7 deliver
  it only for minimal γ-counterexamples; this is an *axiomatic
  interface* in the current Lean tree and should remain so until
  the long-arc Steps 1-7 formalisation. **Do not chase R2 as a
  free-standing lemma — it is false.**
* **For Step 8 (R1 = `lem:layered-balanced`), the existing engineering
  recommendation stands: Option D-narrow per `mg-0cbf` §5e**
  (rewire `lem_layered_balanced` K≥2 to consume caller's L, drop
  `canonicalLayered` substitution; extend `mg-4d7b` enumeration to
  cap-light cells; close cap-5 sorry at `LayeredBalanced.lean:755`).
  Mathematics known, engineering remains.

Daniel's "R1 is the entire conjecture and that's stupid" complaint
is **structurally correct**: R1 IS `Step 8` in full, not a narrow
residual. The `R1+R2` split adds a phantom L parameter to the
conjecture and renames it; it does not decompose the problem
mathematically.

---

## §1. Phase A — locating the coherence-collapse case in the paper

### §1.1. The dichotomy ladder

The paper proves width-3 1/3–2/3 by contradiction. Assume `P` is a
minimal γ-counterexample (width-3, non-chain, no balanced pair, size
minimal). The contradiction is built by successive dichotomies:

```
                  P minimal γ-counterexample (width 3, non-chain)
                                   │
                          Step 5 (Rich-or-Collapse)
                            ├─ (R) rich      ─────┐
                            └─ (C) collapse  ────────► layered L
                                              │            │
                          Step 6 (coherence)  │
                            ├─ (i)  incoherent fraction > δ ─► Step 4 BK boundary > conductance ─► ⊥
                            └─ (ii) coherent  fraction ≥ 1-δ ─┐
                                                              │
                          Step 7 prop:72 ─────────────────────┴► layered L
                                                                       │
                          Step 8 lem:layered-balanced ──────────────► HasBalancedPair P  ─► ⊥
```

The **coherence-collapse case** is the union of the two paths that
land in "layered L": the (C) direct-collapse branch of Step 5 AND
the (R)+(ii) "rich + coherent" → Step 7 prop:72 branch. The third
branch (i) "incoherent" is handled differently — by Step 4's BK
boundary lower-bound contradicting low conductance, without ever
producing a balanced pair.

### §1.2. Source artefacts

| Step | Paper anchor | What it proves |
|---|---|---|
| Step 5 | `step8.tex:443` `prop:step5` (R/C dichotomy) | Either `(R)` rich-overlap mass is `Ω(1)`, or `(C)` `P` is layered on its Dilworth chains modulo `O_T(1)` exceptions. |
| Step 6 | `step8.tex:450` `prop:step6` (coherence dichotomy) | For `P` in `(R)`, either `(i)` incoherent fraction `> δ` (Step 4 contradicts low conductance) or `(ii)` coherent fraction `≥ 1−δ`. |
| Step 7.1 | `step7.tex:1112` `prop:71` "coherence globalizes" | Coherent case `⇒ ∃` potential `a : X → ℝ` and threshold `c` s.t. `S ≈ {H ≥ c}` up to `o(1)`. |
| Step 7.2 | `step7.tex:1173` `prop:72` "low-boundary threshold cut is 1D" | The `(1−o(1))`-aligned cut `{H ≥ c}` forces `P` to admit a **layered width-3 decomposition** on `(1−o(1))` mass with interaction width `w = K(T)+O(1)`. |
| Step 7.3 | `step7.tex:1224` `prop:73` "layered width-3 is harmless" | Layered (per `prop:72` or `prop:step5(C)`) width-3 `P` cannot be a counterexample. Reduces to `lem:layered-balanced` (shallow `K < K_0`) or `lem:layered-reduction` (deep `K ≥ K_0`). |
| Lift to exact `def:layered` | `step8.tex:1990` `lem:layered-from-step7` | Either input (5(C) or 7(ii)) yields, after removing `≤ 3·c_1(T) = O_T(1)` exceptional elements, an *exact* `def:layered` decomposition of `P|_{X∖X^exc}` with `w = K_bw + O(1)` (resp. `w_coll`). |
| The "narrower property" | `step8.tex:1983` `def:layered` | (L1) each band an antichain of size `≤ 3`; (L2) `i < j−w ⇒ x <_P y`; (L3) `|i−j| > w ⇒` comparable; (L4) cross-band comparability respects band index. |
| Lean side | `LayeredReduction.lean:115` `structure LayeredDecomposition` | Fields `K`, `w`, `band`, `band_size ≤ 3`, `band_antichain`, `forced_lt` (L2), `cross_band_lt_upward` (L4). Matches `def:layered` faithfully. |

### §1.3. What the "coherence-collapse case" actually does

It performs the **forward** half of the proof-by-contradiction:
given a minimal counterexample `P` and the (R)+(ii) coherent
regime, it produces a **layered decomposition `L` with bandwidth
`w(L) = w(T) = O_T(1) ≤ 4`** in current Lean alignment
(`step7.tex:1195` `rem:w0-constant`).

This layered decomposition is then handed to `lem:layered-balanced`
(Step 8, `step8.tex:2453`) which extracts a balanced pair, yielding
the desired contradiction with the counterexample assumption.

**The case does NOT directly produce a balanced pair from coherence.**
It only produces the *structural prerequisite* (the layered L)
needed by `lem:layered-balanced`. The "balanced-pair extraction" is
the work of Step 8.

---

## §2. Phase B — the structural property (X, Y, Z) delivered

The coherence-collapse case delivers on `α` the following property,
which we name `P_layered(α, L)`:

```
∃ (L : LayeredDecomposition α),
    -- (X) each band an antichain of size ≤ 3
    (∀ k, |{x : α | L.band x = k}| ≤ 3) ∧
    (∀ k, IsAntichain (≤) {x : α | L.band x = k}) ∧
    -- (Y) cross-band monotonicity (L2)–(L4) of def:layered
    (∀ x y : α, L.band x + L.w < L.band y → x < y) ∧
    (∀ x y : α, x < y → L.band x ≤ L.band y) ∧
    -- (Z) bounded interaction width
    L.w ≤ 4
```

In Lean this is exactly `∃ L : LayeredDecomposition α, L.w ≤ 4`
(the antichain/monotonicity conditions are baked into the
`LayeredDecomposition` structure; the only side-condition that's not
structurally enforced is the bandwidth bound `L.w ≤ 4`).

### §2.1. Why this is the *output*, not the *input*, of the coherence-collapse case

The coherence-collapse case takes a *minimal γ-counterexample* `P` in
the `(R)+(ii)` regime and produces `L`. It does not take `L` as input.

So the proper formulation of the case's contract is:

```
[minimal γ-counterexample in (R)+(ii)]  ⇒  P_layered(α, L)
```

The "narrower property" is the **conclusion** `P_layered(α, L)`. It is
narrower than "width-3 non-chain" because not every width-3 non-chain
satisfies it (see §3).

### §2.2. The incoherence case does NOT deliver `P_layered`

Step 6 dichotomy clause `(i)` — incoherent fraction `> δ` — yields
contradiction via Step 4's BK boundary lower-bound, without producing
either a balanced pair OR a layered decomposition. Specifically
(`step8.tex:464-469`):

> "If instead more than a `δ`-fraction were incoherent, Step 4 applied
> to the Step 5 overlap mass would force `|∂S| ≥ c_5(T)·c_6·(δ −
> K(T)·ε)|L(P)|`, contradicting `Φ(S) ≤ η`."

So `(i)` derives `⊥` from incoherence + low conductance. The
incoherent-regime α (if any) is NOT handled by producing a layered
L; it is ruled out by Step 4 BK accounting.

### §2.3. Why the property is precise (no hidden caps)

Reading `def:layered` (step8.tex:1983) precisely: the only hypotheses
on `(α, L)` are (L1) band ≤ 3 and antichain, (L2) far-apart bands
forced to be comparable upward, (L3) (derived from L2), (L4)
cross-band comparability respects band index. The Lean
`LayeredDecomposition` structure carries exactly these fields. No
"cap 1" (injective band, i.e., singleton bands) and no "cap 2"
(K ≤ 2w+2) and no "cap 3" (|α| ≤ 6w+6) appear in either the paper's
`def:layered` or in `lem:layered-balanced`'s hypothesis statement.

The cap-1, cap-2, cap-3 obligations in
`OptionC.Case3WitnessProof.lean` are **call-shape artefacts** of the
Lean F5a Bool-certificate dispatch (see mg-82fc Phase D and
PROOF-STRUCTURE-ONBOARDING §3 pitfall #2). They are not part of the
paper's structural property.

---

## §3. Phase C — the property IS strictly narrower than "width-3 non-chain"

### §3.1. Counterexample: three disjoint chains of length 10

Let `α = C₁ ⊔ C₂ ⊔ C₃`, where each `C_i = (x_{i,1} <_α x_{i,2} <_α
⋯ <_α x_{i,10})` is a chain of length 10, with **no relations between
different chains**.

Then:

- **Width(α) = 3.** The maximum antichain is any cross-section
  `{x_{1,h₁}, x_{2,h₂}, x_{3,h₃}}` — three pairwise incomparable
  elements. No larger antichain exists.
- **α is non-chain.** Any cross-chain pair `(x_{1,h}, x_{2,k})` is
  incomparable.
- **|α| = 30**, well above the cap-5 unsatisfiability cutoff
  `|α| ≤ 10` that mg-2970 flagged for the cap-1 sub-slice.
- **HasBalancedPair α holds trivially.** Any cross-chain incomparable
  pair has `Pr[x_{1,h} <_L x_{2,k}] = 1/2` by independence of the
  three chains' relative orderings under uniform `L`. So α is *not*
  a γ-counterexample.

**Claim:** there is no `L : LayeredDecomposition α` with `L.w ≤ 4`.

**Proof of claim.** Let `L` be any layered decomposition of α. Write
`α_h := L.band(x_{1,h})`, `β_k := L.band(x_{2,k})`,
`γ_l := L.band(x_{3,l})`.

1. Within `C_1`: for `h < h'`, the pair `(x_{1,h}, x_{1,h'})` is
   comparable (`x_{1,h} <_α x_{1,h'}`), so by (L1) they cannot share
   a band (a band is an antichain). By (L4)
   (`cross_band_lt_upward`) we have `L.band x_{1,h} ≤ L.band x_{1,h'}`.
   The two together give **strict** inequality: `α_h < α_{h'}`. So
   `α_1 < α_2 < ⋯ < α_{10}`, i.e., `α_{10} ≥ α_1 + 9`.
2. By symmetry, `β_1 < β_2 < ⋯ < β_{10}` and
   `γ_1 < γ_2 < ⋯ < γ_{10}`. So `β_{10} ≥ β_1 + 9`,
   `γ_{10} ≥ γ_1 + 9`.
3. Cross-chain pairs are **incomparable** in α. By (L3) (`comparable_of_far`
   derived from L2), if `|L.band x − L.band y| > L.w` then `x < y` or
   `y < x`. Contrapositive: `x, y` incomparable ⇒
   `|L.band x − L.band y| ≤ L.w`.
4. Applied to `(x_{1,1}, x_{2,10})`: `|α_1 − β_{10}| ≤ L.w`.
   Applied to `(x_{1,10}, x_{2,1})`: `|α_{10} − β_1| ≤ L.w`.
5. From (2) and (4): `β_{10} ≤ α_1 + L.w` and `α_{10} ≤ β_1 + L.w`.
   Subtracting and using `β_{10} ≥ β_1 + 9`, `α_{10} ≥ α_1 + 9`:

   ```
   β_1 + 9 ≤ β_{10} ≤ α_1 + L.w
       ⇒ β_1 ≤ α_1 + L.w − 9
   α_1 + 9 ≤ α_{10} ≤ β_1 + L.w
       ⇒ α_1 + 9 − L.w ≤ β_1
   ```
6. Combining: `α_1 + 9 − L.w ≤ β_1 ≤ α_1 + L.w − 9`, which forces
   `9 − L.w ≤ L.w − 9`, i.e., `L.w ≥ 9`.

So every `L : LayeredDecomposition α` for `α =` 3 disjoint chains of
length 10 has bandwidth at least 9. **`L.w ≤ 4` is impossible.** ∎

### §3.2. Consequences

1. **The "narrower property" `P_layered(α, L)` with `L.w ≤ 4` is
   STRICTLY narrower than "width-3 non-chain".** There exist width-3
   non-chain α (the example above) not satisfying it.
2. **mg-2970's `R2 := ∀ α width-3 non-chain, ∃ L with L.w ≤ 4` is
   FALSE.** The 3-disjoint-chains example violates it directly. This
   is a NEW finding relative to mg-2970, which only flagged the
   weaker `cap-1 singleton-band` failure for
   `3-antichain ⊕ 3-antichain` at |α|=6.
3. **The paper does NOT claim R2 in the form mg-2970 wrote it.**
   The paper only claims `P_layered(α, L)` for `α` arising as a
   *minimal γ-counterexample*. For non-counterexample α, no `L` need
   be constructed; the conjecture's conclusion holds by other means
   (in the example above, by independence-symmetry on cross-chain
   pairs). The proof-by-contradiction's `R2`-equivalent is
   conditional: `[α is minimal γ-counterexample in (R)+(ii)] ⇒ ∃ L
   with L.w ≤ w₀(γ) ≤ 4`.

### §3.3. mg-2970's diagnostic counterexample vs this one

mg-2970 §1 (errata correcting mg-5c32) flagged
`α = 3-antichain ⊕ 3-antichain` (|α|=6) as showing the
*cap-1 singleton-band* sub-slice fails to cover all small α. That
α admits a layered L with `K=2`, two bands of size 3, `w=0` — so it
**does satisfy** mg-2970 R2 (non-singleton bands allowed). It only
violates the singleton-band cap-1 restriction.

The 3-disjoint-chains-of-length-10 example here is a **strictly
stronger** counterexample: no layered L with `w ≤ 4` exists at all,
singleton-band or not. It refutes mg-2970 R2 directly in its full
strength (the "cap-light" form). This is the answer to Daniel's
question: the "narrower property" really is narrower than every
width-3 non-chain.

### §3.4. Other concrete narrow examples (for cross-checking)

The same argument generalises:
* **3 disjoint chains of length `M`**: any layered decomposition has
  `L.w ≥ M − 1`. So `L.w ≤ 4` fails for `M ≥ 6`.
* **2 disjoint chains of length `M`, plus a third element**: same
  argument with the cross-chain pair forces `L.w ≥ M − 1`.
* **Boolean lattice `2³`** (8 elements, width 3): admits a layered
  decomposition with `K = 4` antichain levels (by rank) and small
  bandwidth; this *does* satisfy `P_layered`. (Not a counterexample
  to mg-2970 R2.)
* **Crown poset `S₃⁰`** (6 elements, 3 minimal + 3 maximal, every
  maximal covers every non-corresponding minimal): width 3; layered
  with `K = 2`, `w = 1` (the minimal antichain and the maximal
  antichain as two bands, with cross-band comparabilities forced).
  *Does* satisfy `P_layered`. (Not a counterexample.)

The defining feature of the 3-disjoint-chains counterexample is the
combination of **long chains** + **no cross-chain relations**: the
long-chain forces band-index spread; the absence of cross-chain
relations forces bandwidth to absorb the full spread. Adding any
cross-chain relations would compress the band-index spread.

---

## §4. Phase D — proof-technique status for `P_layered ⇒ HasBalancedPair`

The implication

```
∃ L : LayeredDecomposition α, L.w ≤ 4   ⇒   HasBalancedPair α
```

is `lem:layered-balanced` (step8.tex:2453, GAP G4). The paper proves
it in `step8.tex:3211-3266` by strong induction on `|α|`. The
sub-cases:

### §4.1. Top-level case split (paper-proved, rigorous)

* **Case A (K = 1).** `P = L_1` is a single antichain of size 2 or 3;
  any incomparable pair has `Pr[x <_L y] = 1/2` by uniform symmetry.
  **Rigorous.** Lean: `Step8.lem_layered_balanced` K=1 branch
  (`LayeredBalanced.lean:626-680`), tagged S by mg-82fc.
* **Case B (`P` layer-ordinal-reducible).** `P = P_1 ⊕ P_2` via
  `lem:reducible-witness`. Descend to the non-chain factor (smaller
  `|P|`) and apply IH; lift via `cor:reducibility-transfer`
  (`Pr_P = Pr_{P_j}` for pairs within `P_j`, by ordinal-sum
  factorisation of `L(P)`). **Rigorous** — relies on
  `lem:ordinal-factorisation` (step8.tex:2404-2418), a clean OS
  combinatorics fact. Lean: `OrdinalDecomp.hasBalancedPair_lift`
  (`Mathlib/LinearExtension/Subtype.lean:1152`), tagged S by mg-82fc.
* **Case C (irreducible, `K ≥ 2`).** Take any incomparable pair
  `(x, y)`, with `x ∈ L_i`, `y ∈ L_j`, `|i−j| ≤ w`. Apply
  `lem:window-localization`:
  * **C1 (`W ⊊ X`).** `|P|_W| < |X|`; descend to `P|_W` (bounded
    `|P|_W| ≤ 3(3w+1)`), apply IH; the lifted pair is balanced in
    `P` by the pair-identity from window localisation. **Rigorous.**
  * **C2 (`W = X`).** `|X| ≤ 3(3w+1)`, so `|X|` is bounded
    (`≤ 39` when `w = 4`). Apply `prop:in-situ-balanced` directly.

### §4.2. `prop:in-situ-balanced` (the base case)

`prop:in-situ-balanced` (step8.tex:3094) splits into three sub-cases:

* **Case 1 (ambient profile match).** Two distinct `a, a' ∈ A`
  with identical two-sided ambient profile. The transposition
  `τ = (a a')` is a poset-automorphism (since profiles agree, all
  comparabilities are preserved). Pullback of LEs is an involution
  exchanging `{L : a <_L a'}` ↔ `{L : a' <_L a}`, forcing
  `Pr[a <_L a'] = 1/2`. **Rigorous** — pure symmetry argument. Lean:
  `hasBalancedPair_of_ambient_profile_match` (mg-f92d), tagged S.
* **Case 2 (FKG profile-ordering).** `Π(a) ⪯ Π(a')` in the
  product-of-inclusions order. By the Ahlswede–Daykin / FKG
  inequality on linear extensions (`[AhlswedeDaykin1978, FKG1971]`):
  `Pr_Q[a <_L a'] ≥ 1/2`. Combined with the rotation argument from
  `prop:bipartite-balanced`, produces a `[1/3, 2/3]` value. **Cited
  (FKG)** — relies on the AD/FKG external theorem. Lean: routed
  through `prop:in-situ-balanced` Case 2 internally to
  `case3_certificate` (which subsumes the FKG-derivable cases by
  enumeration).
* **Case 3 (profile antichain, |A|=3, no `⪯`-ordering).** The
  three two-sided profiles in `A` (or `B`) are pairwise
  `⪯`-incomparable. **Paper conceded**:

  > "Because `⪯` is the product of two inclusion orders ... and
  > `|Q| ≤ 3(3w+1)`, the profile lattice has at most `2^{3(3w+1)−1} ·
  > 2^{3(3w+1)−1}` points and the joint configuration `(A, B, Q)` is
  > determined up to isomorphism by finitely many data. ... the total
  > number of such irreducible configurations on `≤ 3(3w+1)` elements
  > is a finite function of `w`. A direct machine-checked enumeration
  > verifies that every such configuration contains a balanced pair"
  > (step8.tex `prop:in-situ-balanced` Case 3 + `lem:enum` +
  > `rem:enumeration`).

  This is a **finite-enumeration argument**. For fixed `w ≤ 4`, it
  enumerates (up to isomorphism + L1 symmetries) all irreducible
  layered width-3 posets of depth `K ≥ 2` and size `≤ 3(3w+1)` with
  profile-antichain `|A|=3`, and checks each contains a balanced
  pair. The paper claims this enumeration is performed.

  **Lean status (partial):**
  - F5a Bool certificate `case3_certificate`
    (`Case3Enum/Certificate.lean:71`, `native_decide`): closes
    `(K, w) ∈ {(3,1), (3,2), (3,3), (3,4), (4,1)}` with `sizeLimit`
    `9` or `7` (`K=3`) and `8` (`K=4, w=1`). **SC (substantive
    computational), in-tree.**
  - `mg-4d7b` Python enumeration: closes the **cap-1 singleton-band
    sub-slice** for `(K, w)` with `K ∈ {4..10}`, `w ∈ {2, 3, 4}`,
    `K ≤ 2w+2` (15 cells, ~1.72M configurations, certificate
    `lean/scripts/enum_cap5_certificate.json`). **Partial Lean port
    via `Case3Enum/Cap5Singletons.lean` for `K=2..9`; K=10 cell
    out-of-tree (JSON).**
  - **Not covered by either:** non-singleton-band configurations
    beyond the F5a 5 cells. These would need an *extended* Lean
    enumeration to close `prop:in-situ-balanced` Case 3 in full
    cap-light form.

### §4.3. Honest technique tag

The proof-technique for `P_layered ⇒ HasBalancedPair` is

| Sub-case | Technique | Tag |
|---|---|---|
| Case A (`K=1`) | uniform symmetry of antichain | **(a) rigorous** |
| Case B (reducible) | ordinal-sum factorisation + IH | **(a) rigorous** (depends on `lem:ordinal-factorisation`, paper-proved + Lean-formalised at `Mathlib/LinearExtension/Subtype.lean:1152`) |
| Case C1 (irreducible window proper) | window localisation + IH | **(a) rigorous** (depends on `lem:window-localization`, paper-proved) |
| Case C2 = `prop:in-situ-balanced` Case 1 | swap automorphism | **(a) rigorous** |
| C2 = Case 2 | AD/FKG inequality | **(c) cited** (Ahlswede–Daykin 1978, FKG 1971) |
| C2 = Case 3 | finite enumeration per fixed `w` | **(a) rigorous-by-enumeration** with **(b) gap in Lean port** for cap-light cells beyond mg-4d7b + F5a's 5 cells |

**Aggregate: technique IS known.** It is a paper-proved structural
strong induction with a base case that reduces to (per-`w`-finite)
machine-checked enumeration. There is no opaque or unknown step.

**Lean engineering gap (NOT a math gap):**
1. `lem_layered_balanced` K≥2 dispatch substitutes `canonicalLayered α`
   for caller's `L` (`LayeredBalanced.lean:498`), discarding the
   bandwidth bound → structured `sorry` at `LayeredBalanced.lean:755`
   (mg-d5a0). Rewiring is needed to consume caller's `L` (Option
   D-narrow, mg-0cbf §5e).
2. `prop:in-situ-balanced` Case 3 enumeration: extend `mg-4d7b`'s
   cap-1 enumeration to cap-light cells (or replace with a Lean-side
   `decide`/`native_decide` enumeration over the bounded
   configuration space). Per `lem:enum` the universe size is
   `(3w+1)^{3(3w+1)} · 2^{(3(3w+1))^2}` for fixed `w`; tractable for
   `w ≤ 4` with appropriate symmetry quotients.

---

## §5. Phase E — forward action

### §5.1. mg-2970 framing corrections

| Issue | Fix |
|---|---|
| R1 as stated IS the entire Step 8 / Daniel's "R1 is the entire conjecture" complaint is structurally correct. | Accept: R1 = `lem:layered-balanced` in full. There is no further narrowing of R1 the paper provides. Stop calling R1 a "residual"; it is the *outer engineering target* (Step 8 Lean closure). |
| R2 as universally quantified over width-3 non-chain α is FALSE (§3 counterexample). | Stop pursuing R2 as a free-standing Lean lemma. The proper formulation is *paper-axiomatised*: `Step7.LayeredWidth3` interface (already in tree, `Step7/Assembly.lean:302-348`). For non-counterexample α not satisfying `P_layered`, the proof doesn't need to construct `L`; the conjecture's conclusion holds by other means (in the 3-disjoint-chains example, by independence-symmetry). |
| The cardinality split `|α| ≤ 10` vs `|α| ≥ 11` that mg-2970 introduced for R2 discharge. | Mostly moot once mg-2970 R2 is dropped as a free-standing lemma. The Lean-side `|α| ≤ 10` slice via mg-4d7b is best understood as a *partial Lean port of `prop:in-situ-balanced` Case 3* (the base case of R1), NOT as a discharge of R2. |

### §5.2. Recommended forward actions

**DO** (engineering, technique known):

1. **Option D-narrow (mg-0cbf §5e):** Rewire
   `lem_layered_balanced` K≥2 to consume caller's `L` (drop
   `canonicalLayered α` substitution). This makes the bandwidth
   bound `L.w ≤ 4` actually consumable downstream and removes the
   cap-5 sorry at `LayeredBalanced.lean:755`. **Scope:** 3–5
   polecat sessions per mg-82fc Phase E. **Math: known.**
2. **Extend `mg-4d7b` enumeration to cap-light** (or write a fresh
   Lean-side enumeration via `decide`/`native_decide` over the
   bounded-`w` configuration space). Closes the `prop:in-situ-balanced`
   Case 3 base case fully. **Scope:** independent
   sub-project; finite per fixed `w ≤ 4`. **Math: rigorous by
   enumeration.**

**DO NOT** (math unknown — but for the *wrong* claim):

3. **Do not file a follow-on for "prove R2 as stated by mg-2970".**
   R2 is false in its universally-quantified form (§3). The Lean
   tree's correct treatment of R2's content is the axiomatised
   `Step7.LayeredWidth3` interface, which already exists.
4. **Do not chase a "narrower-than-bandwidth-≤4 property" hoping
   it is provable for all width-3 non-chain α.** The narrowness IS
   "admits L with `w ≤ 4`"; this is *exactly* what the paper's
   coherence-collapse case delivers, and it is *exactly* the input
   to `lem:layered-balanced`. There is no narrower property that
   makes R2 universally provable; the 3-disjoint-chains example
   rules out any such narrowing of the form "α admits *some* L with
   *some* uniform bandwidth bound".

**KEEP HONEST** (Daniel's "shouldn't even go there yet" instinct):

5. **The Steps 1-7 long-arc paper-axiomatisation REMAINS** for the
   `|α| ≥ 11` regime where mg-4d7b enumeration cannot reach
   directly. This is per `prop:72 + rem:w0-constant` (step7.tex:1195)
   and per `Step7.LayeredWidth3` axiom. Daniel's "we shouldn't even
   go there yet" applies to **the Steps 1-7 long-arc**, not to
   Step 8 R1's engineering completion.

### §5.3. Practical impact on the in-tree headline

Current `OneThird.width3_one_third_two_thirds`
(`MainTheorem.lean:56`) is **AMBER**: one cap-5 `sorry` + two
project axioms (`Step7.LayeredWidth3` for `|α| ≥ 11`,
`case3Witness_hasBalancedPair_outOfScope` for non-singleton-band
`prop:in-situ-balanced` cells). Per this audit:

* Path to dropping `case3Witness_hasBalancedPair_outOfScope` axiom:
  Action #2 (extend `mg-4d7b` to cap-light). Math known.
* Path to dropping the `sorry`: Action #1 (Option D-narrow). Math
  known.
* Path to dropping `Step7.LayeredWidth3` axiom: faithful Lean port
  of Steps 1-7's `prop:72`. **Math is paper-proved**, but Lean
  port is a multi-year project. Daniel's "we shouldn't even go
  there yet" applies HERE.

### §5.4. Verdict tag

**GREEN-honest-stop with twist.**

* **GREEN** on the structural extraction question: the narrower
  property `P_layered(α, L) ∧ L.w ≤ 4` IS well-defined and is
  strictly narrower than "width-3 non-chain" (§3 counterexample
  proves it).
* **GREEN** on technique-known: paper proves `lem:layered-balanced`
  rigorously with cited/computational base case; technique is
  known across all sub-cases. No research gap.
* **HONEST-STOP** on mg-2970 R2's universal-existence form: it
  is FALSE; no Lean lemma will discharge it; the proper Lean shape
  is the existing `Step7.LayeredWidth3` axiomatic interface.
* **TWIST**: Daniel's "R1 is the entire conjecture" complaint is
  CORRECT *structurally* (R1 = Step 8 in full), but the math is
  known so this is an engineering project, not new mathematics. No
  "honest stop" warranted on the Step 8 closure work itself; the
  honest stop is on chasing R2 as a stand-alone Lean lemma.

---

## §6. Cross-reference index

**Paper.** `step5.tex:74` `thm:step5` (Rich-or-Collapse); `step6.tex`
(coherence dichotomy); `step7.tex:1112` `prop:71`,
`step7.tex:1173` `prop:72`, `step7.tex:1195` `rem:w0-constant`,
`step7.tex:1224` `prop:73`; `step8.tex:443` `prop:step5`,
`step8.tex:450` `prop:step6`, `step8.tex:472` `prop:step7`,
`step8.tex:1983` `def:layered`, `step8.tex:1990`
`lem:layered-from-step7`, `step8.tex:2453` `lem:layered-balanced`,
`step8.tex:3094` `prop:in-situ-balanced`, `step8.tex:3164` `lem:enum`,
`step8.tex:3211-3266` proof of `lem:layered-balanced`.

**Lean (this worktree).**
- `LayeredReduction.lean:115` `structure LayeredDecomposition`
- `LayeredBalanced.lean:498` `canonicalLayered`,
  `LayeredBalanced.lean:626` K=1 case,
  `LayeredBalanced.lean:755` cap-5 sorry (mg-d5a0),
  `LayeredBalanced.lean:681-755` K≥2 dispatch.
- `OptionC/Case3WitnessProof.lean:256` `Case3Witness_proof.{u}`,
  `OptionC/Case3WitnessProof.lean:286` strong induction.
- `Case3Enum/Certificate.lean:71` `case3_certificate`
  (`native_decide`).
- `Case3Enum/Cap5Singletons.lean`, `Cap5SingletonsK9.lean` —
  mg-4d7b partial Lean port.
- `Step7/Assembly.lean:302-348` `Step7.LayeredWidth3` axiom.
- `Mathlib/LinearExtension/Subtype.lean:1152`
  `OrdinalDecomp.hasBalancedPair_lift` — paper
  `lem:ordinal-factorisation`.

**Predecessor docs.**
- `docs/width3-residual-statement.md` (mg-2970) — the R1+R2 form
  this file supersedes.
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — onboarding
  TL;DR; this file UPDATES §0 / §3 implicitly via the supersession
  recorded above (a separate same-commit edit to ONBOARDING is
  recommended for §5.1 fix in §5 below).
- `docs/onethird-proof-outline-audit.md` (mg-82fc) — F3 audit;
  Option D-narrow follow-on basis.
- `docs/layered-form-vs-coherence-architecture-audit.md` (mg-74d2)
  — layered ↔ coherence architecture; `canonicalLayered`
  bypass diagnosis.
- `docs/onethird-Case3Witness-architecture-analysis.md` (mg-e2e9)
  — cap-5 proposal.
- `docs/state-Case3Witness-cap5-fix.md` (mg-d5a0) — sorry placement.
- `docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`
  (mg-0cbf) — Option D-narrow / D-broad framing.
- `docs/state-Case3Witness-cap5-enumeration.md` (mg-4d7b) — Python
  enumeration certificate.

**Predecessor work-items (this is the 6th vacuity-discovery
audit; pattern explicit per Daniel directive 2026-05-18T12:48Z).**
mg-e2e9 + mg-74d2 + mg-5c32 + mg-82fc + mg-2970 each transcribed
API surface or conflated constructs without verifying
satisfiability or substantive-ness. This audit's distinguishing
feature: paper-first reading of the coherence-collapse case in
context, with a fresh structural counterexample (3 disjoint chains
of length 10) refuting mg-2970 R2's universal-existence form in
its full strength (cap-light, not just cap-1).
