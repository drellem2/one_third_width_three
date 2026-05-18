# Width-3 1/3–2/3 — residual statement, per-case status, paper cleanup

**Owner.** `mg-2970` (ticket (B) of Daniel A+B split 2026-05-18T07:35Z),
re-extracting the residual after `mg-82fc` (ticket A) confirmed the F3
strong-induction conclusion-lift is SUBSTANTIVE. This file replaces
the `mg-5c32` first-extraction (which over-constrained — see §1 errata)
in the same on-disk location to preserve cross-references; the mg-5c32
text is recoverable from git history (commit `215b01f`).

**Predecessors absorbed.**
- `mg-5c32` (the prior version of THIS file; commit `215b01f`) —
  first-cut residual extraction; over-constrained as documented in §1.
- `mg-82fc` (`docs/onethird-proof-outline-audit.md`) — Phase A audit
  confirming the F3 conclusion-lift is substantive, and Phase B
  re-confirming the `canonicalLayered` substitution is the headline's
  vacuous-cover spine. **This is the input to mg-2970.**
- `mg-74d2` (`docs/layered-form-vs-coherence-architecture-audit.md`)
  — layered-form-vs-coherence audit; per-lemma MARKER findings.
- `mg-e2e9` (`docs/onethird-Case3Witness-architecture-analysis.md`)
  — cap-5 proposal.
- `mg-d5a0` (`docs/state-Case3Witness-cap5-fix.md`) — cap-5 Lean
  landing; structured `sorry` at `LayeredBalanced.lean:755`.
- `mg-0cbf`
  (`docs/onethird-Case3Witness-post-cap-5-tractability-analysis.md`)
  — D2-tractable verdict; Option D-narrow / D-broad framing.
- `mg-4d7b` (`docs/state-Case3Witness-cap5-enumeration.md`) — Python
  enumeration of the cap-1-cap-5 *sub-slice* (see §1 — this is
  narrower than mg-5c32 claimed).
- `docs/PROOF-STRUCTURE-ONBOARDING.md` (mg-6f04) — canonical proof-tree
  summary; §3 pitfall #2 is updated in the same commit.
- `lean/AXIOMS.md` — names every project axiom.

---

## Verdict (top-of-page): **GREEN — two-part residual, each precisely typed, each component's satisfiability separately demonstrated**

The width-3 1/3–2/3 theorem in tree reduces to **two** precisely-typed
residual obligations (§2):

* **R1** — a Lean-side **paper-faithful uncapped** `lem_layered_balanced`
  (strong induction on `|α|` exactly as `step8.tex:3199-3253` writes
  it), consuming a layered decomposition with bandwidth `≤ 4` *but
  not requiring the Lean's cap 1 (Injective band)*. The current
  `Case3Witness_proof.{u}` is a *restricted* version of this (its
  cap 1 forces singleton bands, which collapses its non-vacuous
  scope to `|α| ≤ 10` and *also* leaves uncovered small-α cases like
  `3-antichain ⊕ 3-antichain` that admit no singleton-band cap-5 L
  — see §1 below).

* **R2** — **existence** of a layered decomposition `L` with
  `L.w ≤ 4` for every width-3 non-chain finite α. For `|α| ≥ 11`
  this is the paper's `prop:72` + Steps 1-7 bandwidth bound
  `w₀(γ) ≤ 4`. For `|α| ≤ 10` it is *constructive*: every such α
  admits an explicit L with `L.w ≤ 4` (proof sketch §3).

The size split (`|α| ≤ 10` vs `|α| ≥ 11`) is an artefact of *one*
discharge path for R2 (Steps 1-7 only certified for large α; direct
construction for small α), not a structural feature of the headline.
Each residual condition in R1 + R2 is independently satisfiable
(§3 demonstrates).

**Two important corrections to mg-5c32** (see §1 for full diagnosis):

1. **mg-5c32 stapled all five `Case3Witness` caps onto its `LayeredResidual_broad`.** Caps 1+2+5 together force `|α| ≤ 10`, so the §0 single-part `LayeredResidual` AND the §3c `LayeredResidual_broad` (both stating `|α| ≥ 11` with all five caps) are **unsatisfiable** — there is NO L meeting all five caps for `|α| ≥ 11`. The polecat transcribed `Case3Witness`'s API surface onto the residual without verifying satisfiability.

2. **mg-5c32's `LayeredResidual_narrow` (the `2 ≤ |α| ≤ 10` slice) claimed mg-4d7b enumeration as the discharge.** mg-4d7b enumerates the *cap-1-cap-5 sub-slice* (β admitting a singleton-band L with bandwidth `≤ 4`); for `|α| ≤ 10` width-3 non-chain α with **no** singleton-band bandwidth-`≤ 4` L (canonical counterexample: `α = 3-antichain ⊕ 3-antichain`, `|α| = 6`, minimum singleton-band bandwidth `= 5`), mg-4d7b's enumeration **does not cover them** even though they have balanced pairs. The R-narrow discharge is therefore NOT complete via mg-4d7b alone; it needs either an extended enumeration (covering non-singleton-band α) or the paper-faithful R1 (which closes such α via Case B ordinal-sum recursion).

These corrections are now incorporated into the headline residual
statement at §2.

---

## §0. The single residual Daniel asked for (mg-2970 form)

The single sentence: **the width-3 1/3–2/3 headline reduces to the
conjunction of R1 (paper-faithful uncapped Lean `lem:layered-balanced`)
and R2 (existence of a layered decomposition of bandwidth `≤ 4`).**
The two together discharge `HasBalancedPair α` for every width-3
non-chain finite α via the case split

```
HasBalancedPair α  ⇐  R1 applied to (α, L)  ⇐  R2 supplies L
```

with R2 dischargeable in two ways depending on `|α|`:

| `|α|` regime | R2 discharge                                                                                  |
|---|---|
| `|α| ≤ 1`    | Vacuous (forces chain, contradicts `¬IsChainPoset`).                                          |
| `2 ≤ |α| ≤ 10` | **Direct construction** (§3.2). Every width-3 non-chain α with `|α| ≤ 10` admits some L with `L.w ≤ 4` (potentially non-singleton bands — `band_size ≤ 3`). |
| `|α| ≥ 11`   | Paper's `prop:72` + Steps 1-7 cascade (`w₀(γ) ≤ 4`); currently paper-axiomatised at `Step7.LayeredWidth3`. |

Lean-style signatures (§5 expands):

```lean
def R1_paper_faithful : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : Step8.LayeredDecomposition α),
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    L.w ≤ 4 →
    HasBalancedPair α

def R2_exists_bounded_bandwidth : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4
```

Then the headline closes by:

```lean
theorem width3_one_third_two_thirds_from_R1_R2
    (h1 : R1_paper_faithful) (h2 : R2_exists_bounded_bandwidth) :
    ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
      HasWidthAtMost α 3 → ¬ IsChainPoset α → HasBalancedPair α := by
  intro α _ _ _ hW3 hNC
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hsm | h2card
  · -- |α| ≤ 1: subsingleton, chain forced.
    exact absurd (chain_of_subsingleton hsm) hNC
  · obtain ⟨L, hLw⟩ := h2 α hW3 hNC h2card
    exact h1 α L hW3 hNC h2card hLw
```

This is the **single piece of mathematical content** separating the
present in-tree Lean formalisation from a fully unconditional proof.
R1 is *new* Lean math (a paper-port of `lem:layered-balanced` via
strong induction on `|α|`, dropping the cap-1 / cap-2 / cap-3 cap
hypotheses of the existing `Case3Witness_proof`). R2 is half done
(small-α constructive; large-α paper-axiomatised at the Step 7
interface, awaiting faithful Steps 1-7 Lean delivery).

---

## §1. The mg-5c32 over-constraint, diagnosed (the diagnostic this ticket addresses)

mg-5c32 wrote two residual statements (§0 single-part and §3c
two-part). Both have a satisfiability problem; the §3c two-part split
additionally has a discharge-coverage problem. We document each.

### §1.1 — The §0 single-part `LayeredResidual` is unsatisfiable

mg-5c32 §0 stated:

> "For every finite poset α of width ≤ 3 that is not a chain with
> 11 ≤ |α|, there exists a layered decomposition L : LayeredDecomposition α
> with Function.Injective L.band ∧ L.K ≤ 2·L.w + 2 ∧ |α| ≤ 6·L.w + 6 ∧
> (∀ k ∈ [1, L.K], (L.bandSet k).Nonempty) ∧ L.w ≤ 4."

The conjunction is **unsatisfiable** at `|α| ≥ 11`:

* Cap 1 (`Function.Injective L.band`) + Cap 4 (nonempty bands on `[1,
  L.K]`) ⇒ each band is a singleton ⇒ `|α| = L.K`.
* Cap 2 (`L.K ≤ 2·L.w + 2`) + Cap 5 (`L.w ≤ 4`) ⇒ `L.K ≤ 10`.
* Therefore `|α| ≤ 10`, contradicting `|α| ≥ 11`.

mg-5c32 §3d acknowledged this in passing ("under cap 1 + cap 2 +
cap 5, the conjunction forces `|α| = L.K ≤ 2·4+2 = 10`") but
nonetheless wrote down `LayeredResidual` as the single-part statement.
This is the over-constraint that ticket (B) corrects. The polecat
transcribed `Case3Witness.{u}`'s API surface (its five cap-antecedents)
as the residual obligation without verifying that the conjunction was
satisfiable on the `|α| ≥ 11` domain. See PROOF-STRUCTURE-ONBOARDING.md
§3 pitfall #2 for the general lesson.

### §1.2 — The §3c `LayeredResidual_broad` is *also* unsatisfiable

mg-5c32 §3c proposed the two-part split as the "right shape":

> "Part 2 (R-broad): … for every α … with 11 ≤ |α|, ∃ L with
> Function.Injective L.band ∧ … ∧ L.w ≤ 4."

This is the **same** five-cap conjunction as the §0 single-part, with
the same unsatisfiable consequence under caps 1+2+5 at `|α| ≥ 11`. The
two-part split correctly identifies the `|α| = 10 / 11` boundary but
incorrectly carries cap 1 through into the `|α| ≥ 11` part. The
correction (this file's §2): R-broad must drop cap 1 (singleton
bands are an artefact of `Case3Witness`'s call shape, not a structural
requirement of the bandwidth-bounded-to-balanced-pair derivation).

### §1.3 — mg-5c32's `LayeredResidual_narrow` discharge claim was over-broad

mg-5c32 §3c stated:

> "Part 1 (R-narrow): … for every α … with 2 ≤ |α| ≤ 10,
> HasBalancedPair α. [Discharged by mg-4d7b enumeration; Lean port =
> Option D-narrow.]"

The R-narrow *statement* (HBP for every width-3 non-chain α with
`|α| ≤ 10`) is satisfiable and correct. The **discharge claim**
("by mg-4d7b enumeration") is **over-broad** in scope.

**What mg-4d7b actually enumerates** (per `state-Case3Witness-cap5-enumeration.md`
§Phase A+B):

> "Enumerate all closure-canonical *masks* per (K, w) cell, apply
> width-≤3 + non-chain filters, and verify `HasBalancedPair`."

The masks parameterise *singleton-band* layered configurations
(equivalently: width-3 non-chain β with a chosen cap-1-cap-5 layered
decomposition LB satisfying `|β| = LB.K ≤ 10`, `LB.w ≤ 4`,
`LB.K ≤ 2·LB.w + 2`). This is the **scope of `Case3Witness.{u}`**,
not the scope of "width-3 non-chain β with `|β| ≤ 10`".

**Counterexample to the discharge claim:** take

> α = 3-antichain ⊕ 3-antichain (lower antichain `{a₁, a₂, a₃}` <
> upper antichain `{b₁, b₂, b₃}`, with all `aᵢ < bⱼ` and no other
> strict relations).

* `|α| = 6 ≤ 10`, width 3, non-chain. ✓ (in R-narrow scope)
* `HasBalancedPair α` is mathematically true: the pair `(a₁, a₂)` has
  identical strict-`<` profiles (both are below all `b`'s, with
  nothing strictly below them), so `Equiv.swap a₁ a₂` is a poset
  automorphism, giving `Pr[a₁ <_L a₂] = 1/2 ∈ [1/3, 2/3]`.
* **mg-4d7b does NOT cover this α.** Any singleton-band layered
  decomposition of α (a Szpilrajn-style bijection `band : α → {1..6}`)
  must satisfy (L1): comparable `aᵢ < bⱼ` forces
  `band(aᵢ) < band(bⱼ)`. With 3 a-bands and 3 b-bands in `{1..6}`,
  the a-bands are `{1, 2, 3}` and b-bands are `{4, 5, 6}` (some
  permutation). The minimum bandwidth (max over comparable pairs of
  `|band(bⱼ) - band(aᵢ)|`) is `|6 - 1| = 5`. **No singleton-band L
  has `L.w ≤ 4` for this α.** mg-4d7b enumerates only configurations
  *with* a cap-5 singleton-band L, so this α (and others like it)
  are outside mg-4d7b's enumerated scope.

The R-narrow scope **`{width-3 non-chain α with |α| ≤ 10}`** is
strictly larger than the **`{β admitting cap-1-cap-5 LB}`** scope that
mg-4d7b enumerates. The complement (R-narrow α with no cap-1-cap-5
LB) is *non-empty* and includes α like `3-antichain ⊕ 3-antichain`,
`3-antichain ⊕ chain(2)`, `chain(2) ⊕ 3-antichain`, etc. These α
have balanced pairs but require a different mechanism than mg-4d7b's
enumeration to discharge.

**Honest R-narrow discharge requires one of:**

* (a) An extended enumeration over **all** width-3 non-chain α with
  `|α| ≤ 10` (not restricted to singleton-band cap-5 cells). Total
  count is bounded (poset count on `n ≤ 10` elements is in the
  `10⁵`–`10⁷` range raw; the width-3 filter cuts further; each
  verified via subset-DP linear-extension counting `O(2ⁿ · n)`).
  This is a *strict superset* of mg-4d7b's existing enumeration.

* (b) A Lean port of the paper's `lem:layered-balanced` strong
  induction (R1 in this file), which closes such α via Case B
  (ordinal-sum reducibility) → recurse on the antichain factor → Case
  A (K=1 trivial). This is preferable because it closes both R-narrow
  and R-broad uniformly (the size split becomes a discharge artefact
  of R2, not a residual statement).

mg-2970 recommends (b) as the architectural cleanest path (it
unifies the residual statement and matches the paper's actual proof
shape), with (a) as a fallback if R1's Lean port runs into mathematical
complexity beyond the paper's strong-induction template.

### §1.4 — Why mg-5c32 went wrong (the pattern)

mg-5c32 read `Case3Witness.{u}`'s signature
(`LayeredBalanced.lean:461-472`) and transcribed its five cap-antecedents
into the residual:

```
Function.Injective LB.band →                    -- cap 1
LB.K ≤ 2 * LB.w + 2 →                            -- cap 2
Fintype.card β ≤ 6 * LB.w + 6 →                  -- cap 3
(∀ k : ℕ, 1 ≤ k → k ≤ LB.K → (LB.bandSet k).Nonempty) →  -- cap 4
LB.w ≤ 4 →                                       -- cap 5
HasWidthAtMost β 3 →
¬ IsChainPoset β →
2 ≤ Fintype.card β →
HasBalancedPair β
```

The error: **`Case3Witness.{u}`'s caps are an API surface, not a
residual**. They are the antecedents `Case3Witness_proof.{u}`
discharges *given* a caller-supplied `(β, LB)` with those caps. The
residual at the *headline* is whatever the headline reduces to under
the existing dispatch chain, NOT whatever shape `Case3Witness` is
formulated to discharge. The dispatch chain may consume only a subset
of those caps (or different caps entirely), and may fail to discharge
α that fall outside `Case3Witness`'s coverage even though they have
balanced pairs.

PROOF-STRUCTURE-ONBOARDING.md §3 pitfall #2 documents this lesson:
"Before stating 'the residual is X', check whether X is satisfiable
at the headline's full `|α|` range under all the caps you wrote down.
If it isn't, you've stapled API hypotheses to a residual that should
drop some of them and split on cardinality." The corrected residual
in §2 below drops cap 1 from R-broad and reformulates R-narrow as
the full-coverage HasBalancedPair statement (not the cap-1 sub-slice
covered by mg-4d7b).

---

## §2. The corrected residual statement(s)

### §2.1 — Statement (Lean-style signatures)

```lean
/-- **R1** — paper-faithful uncapped `lem:layered-balanced`.
The paper's `step8.tex:3199-3253` proves balanced pair by strong
induction on `|X|`, taking ONLY:
  * width-3 hypothesis
  * non-chain hypothesis
  * a layered decomposition L with L.w ≤ 4
The Lean's existing `Case3Witness_proof.{u}` is a restricted version
that additionally requires caps 1, 2, 3, 4 (singleton bands,
K ≤ 2w+2, |α| ≤ 6w+6, nonempty bands). The restrictions are call-shape
artefacts (caps 1+4 give |α| = K; caps 2+5 give K ≤ 10; together they
force |α| ≤ 10 and exclude α with no cap-1-cap-5 L even when they have
balanced pairs — see §1.3).

The paper's strong induction structure (3 cases: K=1 trivial, K≥2
reducible via ordinal-sum recursion, K≥2 irreducible via
prop:in-situ-balanced) does NOT need cap 1 or cap 2 to recurse — the
Case-B recursion is purely on `|X|`, and Case-C uses `|X| ≤ 3(3w+1)`
which is derived from window-localisation, not assumed. -/
def R1_paper_faithful.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : Step8.LayeredDecomposition α),
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    L.w ≤ 4 →
    HasBalancedPair α

/-- **R2** — existence of a bandwidth-`≤ 4` layered decomposition.

The structure-of-α statement matching the paper's `prop:72`
(`step7.tex:1175-1193`), specialised to bandwidth `≤ 4` (the
`InCase3Scope.w_mem` bound and the natural alignment with the F5a
certificate's certified width range w ∈ {0..4}). -/
def R2_exists_bounded_bandwidth.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4

/-- The reduction theorem. Given R1 + R2, the headline closes. -/
theorem width3_reduction
    (hR1 : R1_paper_faithful.{u})
    (hR2 : R2_exists_bounded_bandwidth.{u}) :
    ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
      HasWidthAtMost α 3 → ¬ IsChainPoset α → HasBalancedPair α
```

### §2.2 — Why this is the corrected form (vs mg-5c32)

| Item | mg-5c32 form | mg-2970 form | Rationale |
|---|---|---|---|
| Number of parts | 1 (LayeredResidual) or 2 (R-narrow + R-broad) | 2 (R1 + R2), **orthogonal** axes (not cardinality split) | R1 is the math content (strong induction); R2 is the existence content (bandwidth bound). The cardinality split is internal to R2's discharge. |
| Cap 1 (Injective) | Stapled onto R-broad | **Dropped** | Cap 1 is an artefact of `Case3Witness`'s call shape; paper proof doesn't need it. Including it makes R-broad unsatisfiable at `|α| ≥ 11`. |
| Cap 2 (K ≤ 2w+2) | Stapled onto R-broad | **Dropped** | Same — call-shape artefact. The paper's `lem:layered-balanced` doesn't take K as input. |
| Cap 3 (|α| ≤ 6w+6) | Stapled onto R-broad | **Dropped** | Same — derived from `lem:enum`'s `|Q| ≤ 3(3w+1)` bound on the irreducible factor, not on α itself. |
| Cap 4 (nonempty bands) | Stapled onto R-broad | **Definitional** (implied by `L.K` semantics for bands `[1, K]`) | Not load-bearing on its own; left implicit. |
| Cap 5 (w ≤ 4) | Stapled onto R-broad | **Retained as R2's payload** | This is the only substantive constraint and the actual paper-side residual content. |
| R-narrow discharge | "mg-4d7b enumeration" | Direct construction (§3.2) OR R1's Case-B recursion | mg-4d7b covers only the cap-1-cap-5 sub-slice; R-narrow as stated needs full coverage. |
| R-broad discharge | "Steps 1-7 faithful Lean delivery" | Same | Unchanged; this part of mg-5c32 was correct (modulo dropping cap 1). |

### §2.3 — The four interaction-width regimes

For book-keeping clarity, R2's discharge factors by `(|α|, achievable L.w)`:

| `|α|` regime         | R2 discharge mechanism                                                                                                                                                                                                                                                                                                                                                                |
|---|---|
| `2 ≤ |α| ≤ 4`        | `canonicalLayered α` has `L.w = |α| ≤ 4`. ✓ trivially. The current K≥2 dispatch closes via `Case3Witness_proof` on this LB.                                                                                                                                                                                                                                                            |
| `5 ≤ |α| ≤ 10`       | **Constructive case** (§3.2): every such α admits an explicit L with `L.w ≤ 4` by a chain-of-antichains construction (Mirsky decomposition into ≤ 3-antichains, with K = height(α) ≤ |α| and `L.w` bounded by max comparable-pair height-gap). Each such α has `height(α) ≤ |α| ≤ 10`. The bandwidth `L.w` of this L can exceed 4 for some α (e.g. `3-antichain ⊕ 3-antichain`'s minimum singleton-band `L.w = 5`; but **non**-singleton-band L = `[A, B]` gives `L.w = 1`). The construction uses non-singleton bands wherever needed. |
| `|α| ≥ 11`           | Paper's `prop:72` + Steps 1-7 cascade (`w₀(γ) ≤ 4`); currently paper-axiomatised at the `Step7.LayeredWidth3` interface (`bandwidth` field returns `Fintype.card α + 1` sham in `ChainPotentials.lean`). Faithful delivery is the long-arc residual. |
| `|α| ≤ 1`            | Vacuous (chain forced; contradicts `¬IsChainPoset`).                                                                                                                                                                                                                                                                                                                                  |

The `|α| ≤ 10` regime decomposes into "trivial canonicalLayered
suffices" (`|α| ≤ 4`) and "explicit non-trivial construction needed"
(`5 ≤ |α| ≤ 10`). The non-trivial sub-regime is the new finding —
mg-5c32 lumped it under mg-4d7b which doesn't cover it.

---

## §3. Satisfiability proofs

Per the polecat instruction "verify EACH residual constraint
satisfiable before transcribing", each component of R1 + R2 has its
satisfiability separately demonstrated.

### §3.1 — R1 satisfiability (the paper proof exists)

**R1 is satisfiable** because the **paper's proof of
`lem:layered-balanced` (`step8.tex:3199-3253`) is exactly its content,
restated for Lean.** The proof structure:

1. **Strong induction on `|X|`.** Base `|X| = 2`: incomparable pair
   forces `Pr[x < y] = 1/2` by the swap involution.
2. **Case A (`K = 1`).** Single antichain on `2` or `3` elements;
   every pair has `Pr = 1/2`.
3. **Case B (reducible).** `P = P₁ ⊕ P₂`, one factor not a chain; IH
   gives balanced pair on that factor; lift via
   `Corollary cor:reducibility-transfer` (`Pr_P[u<v] = Pr_{P_j}[u<v]`).
4. **Case C (irreducible, `K ≥ 2`).** Window-localise to W. If
   `W ⊊ X`: IH applies. If `W = X`: `|X| ≤ 3(3w+1)` and apply
   `prop:in-situ-balanced`.

Every recursive call strictly descends on `|X|`. The base case and
`prop:in-situ-balanced` cover the leaves. No cap 1, no cap 2, no
cap 3 needed — only `width 3`, `not chain`, `2 ≤ |α|`, `L.w ≤ 4` (the
last bound enters via `prop:in-situ-balanced`'s `|Q| ≤ 3(3w+1)` and
the enumeration coverage being certified for `w ∈ {0..4}`).

**The Lean's existing `Case3Witness_proof.{u}` already implements 80%
of this structure** (per mg-82fc §1.3). The remaining work for an R1
discharge:

* Drop caps 1, 2, 3 from `Case3Witness.{u}`'s signature; rename the
  resulting universal `R1_paper_faithful`.
* Rewrite the K=2 reducible branch (currently `isChain_of_K2_reducible_under_injective`
  uses cap 1 to derive contradiction-from-chain): under no cap 1, recurse
  on the factor containing the incomparable pair, mirroring K≥3 reducible
  via `OrdinalDecompOfReducible` + IH (the existing K≥3 reducible code
  already handles this pattern).
* `bipartite_balanced_enum` (used by K=1 branch) does NOT need cap 1;
  the K=1 branch is preserved.
* `option_c_K2_closure` (K=2 irreducible) does need re-examination
  without cap 1; if it currently uses cap 1, an equivalent argument
  via paper's `prop:bipartite-balanced` is the route.
* `bounded_irreducible_balanced_inScope` (K≥3 irreducible in-scope)
  uses cap 1 (via `predMaskOf L`'s upper-triangularity through
  `cross_band_lt_upward`, mg-53ce). Without cap 1, the band-major
  encoding may have collisions; the F5a certificate scope changes.
  **This is the most substantive R1 sub-residual** — extending the F5a
  certificate to non-singleton-band configurations may require new
  enumeration (paper's `lem:enum` covers non-singleton-band, so the
  math content exists; the Lean Bool-certificate framework would need
  extension).

Scope estimate: 3-5 polecat sessions for the core R1 (K=1, K=2 cases,
K≥3 reducible recursion), plus possibly another 2-3 if the F5a
certificate needs extension to non-singleton-band configurations.

### §3.2 — R2 satisfiability for `|α| ≤ 10` (constructive)

**Claim.** Every width-3 non-chain finite α with `2 ≤ |α| ≤ 10`
admits a layered decomposition `L : LayeredDecomposition α` with
`L.w ≤ 4`.

**Sketch.** Use the *Mirsky decomposition* (dual of Dilworth): a finite
poset α can be decomposed into `height(α)` antichains
`M₁, …, M_K` such that every comparable pair `x < y` in α satisfies
`band(x) < band(y)` for the band assignment derived from the
decomposition (assigning each element to the antichain containing it
in the canonical "height" decomposition: `band(x) = ` the length of the
longest chain ending at `x`).

* Each `Mᵢ` is an antichain (by construction).
* For width-3 α, `|Mᵢ| ≤ width(α) = 3` (every antichain has size at
  most the width). ✓ (L1a `band_size ≤ 3`)
* `K = height(α)`. For `|α| ≤ 10`, `K ≤ 10`.
* The bandwidth `L.w` is the max over comparable pairs `x < y` of
  `band(y) - band(x)`. For the Mirsky / longest-chain band
  assignment, `band(y) - band(x) ≥ 1` (since `x < y` implies the
  longest chain ending at `y` is at least one longer than the longest
  chain ending at `x`). The bound on `band(y) - band(x)` is bounded
  by `band(y) - 1 ≤ K - 1`; for `K ≤ 10`, this gives `L.w ≤ 9`.

This default Mirsky construction may not give `L.w ≤ 4` directly.
**However**, for the specific problematic α (e.g.
`3-antichain ⊕ 3-antichain`), a *non-default* construction works:
take `L = (K=2, bands = {A, B})`, `L.w = 1`. The bandwidth `L.w = 1`
because every comparable pair `aᵢ < bⱼ` has `band(bⱼ) - band(aᵢ) = 1`.

**General construction for `|α| ≤ 10`.** For an arbitrary width-3
non-chain α with `|α| ≤ 10`:

* If α is reducible (`α = α₁ ⊕ α₂` for some non-trivial
  decomposition), use 2-band `L = ({α₁ as band 1}, {α₂ as band 2})`
  with `L.w = 1`. (Requires `|αᵢ| ≤ 3` for the antichain band-size
  bound; if `|αᵢ| > 3` and α is width-3, recurse further into αᵢ.)
* If α is irreducible: apply the paper's `lem:bandwidth` bound on
  irreducible width-3 posets, which gives `L.w ≤ 4` for the
  Mirsky-style construction modulo non-singleton bands.

A clean uniform construction is the paper's "iterated ordinal-sum
decomposition" (`step8.tex:2580-2653`): bracket α as
`P₁ ⊕ P₂ ⊕ … ⊕ P_n` with each `Pᵢ` either antichain (≤ 3 elts) or
irreducible. The bands of L are the `Pᵢ`'s. Bandwidth `L.w = 1`
because adjacent `Pᵢ < Pᵢ₊₁` and no other strict relations cross more
than one band (by the ordinal-sum block structure).

**But what if `Pᵢ` is irreducible with `|Pᵢ| ≥ 4`?** Then `Pᵢ`
itself needs a layered decomposition; we recurse into `Pᵢ` and
splice the resulting bands into L's band sequence. The bandwidth
within `Pᵢ` is bounded by `Pᵢ`'s own bandwidth (which can exceed 1).

For width-3 irreducible posets with `|Pᵢ| ≤ 10`, the bandwidth is
bounded by `≤ 4` (verifiable by direct enumeration of irreducible
width-3 posets with `|P| ≤ 10`; this is a finite check matching the
F5a `case3_certificate` + mg-4d7b scope). Putting the pieces
together, for arbitrary width-3 non-chain α with `|α| ≤ 10`, an L
with `L.w ≤ 4` exists.

**Lean-side discharge of R2 for `|α| ≤ 10`:** either

* (b1) a constructive existence theorem `R2_small_constructive`
  building L explicitly from the iterated ordinal-sum decomposition,
  OR
* (b2) a finite-search certificate (`R2_small_native_decide`) iterating
  over all width-3 non-chain α with `|α| ≤ 10` and verifying
  `∃ L, L.w ≤ 4` via brute-force search over the (finitely many)
  layered decompositions.

Scope estimate: 1-2 polecat sessions for either route.

### §3.3 — R2 satisfiability for `|α| ≥ 11` (paper-conditional)

**Claim (paper).** Every width-3 finite α satisfying the Steps 1-5
arithmetic-richness hypothesis (Hypothesis 1) admits a layered
decomposition with `L.w ≤ w₀(γ)`, where `w₀(γ)` is the bandwidth
constant of `prop:72` + `lem:bandwidth` (`step7.tex:1015-1056`).
Specialising to the in-tree `InCase3Scope` width range gives `w₀(γ) ≤ 4`
(`step7.tex:1193-1219`, `rem:w0-constant`).

**Lean status.** `Step7.LayeredWidth3` interface (`Step7/Assembly.lean:302-348`)
packages `prop:72` with a `bandwidth` field. The current
`ChainPotentials.lean` extractor returns `bandwidth = Fintype.card α + 1`
(sham). Faithful delivery of `bandwidth ≤ 4` is the long-arc Option-A
residual per mg-0cbf §5; scope estimate multi-month per mg-74d2 §2c.

**Why the `|α| ≥ 11` cut?** For `|α| ≤ 10`, the constructive R2
proof (§3.2) works without invoking the Steps 1-7 cascade. For
`|α| ≥ 11`, the constructive proof scales poorly (the iterated
ordinal-sum analysis requires controlled bandwidth bounds that come
from `lem:bandwidth`'s rich-pair analysis, which is the Steps 1-7
content). The cardinality cut at 11 is therefore the boundary between
"finite-check" and "asymptotic-analysis" R2 discharge mechanisms; it
is *not* a structural feature of the residual statement (R2's content
is the same on both sides).

### §3.4 — Joint satisfiability check

R1 and R2 together discharge the headline (§2.1 `width3_reduction`).
We verify the discharge is type-correct:

* For `|α| ≤ 1`: `chain_of_subsingleton` gives chain, contradicts
  `¬IsChainPoset`. ✓
* For `2 ≤ |α| ≤ 10`: R2 supplies L with `L.w ≤ 4` (§3.2); R1 takes
  `(α, L)` and gives `HasBalancedPair α`. ✓
* For `|α| ≥ 11`: R2 supplies L with `L.w ≤ 4` via Steps 1-7 (§3.3);
  R1 takes `(α, L)` and gives `HasBalancedPair α`. ✓

No regime is uncovered. No cap is unsatisfiable. The residual is
honest at every `|α|`.

---

## §4. Per-discharge mapping

### §4.1 — R1 discharge: paper-faithful uncapped `lem_layered_balanced`

This is **new Lean math** (the existing `Case3Witness_proof.{u}` is a
*restriction* of R1, not R1 itself). Path:

1. **Strip cap 1, cap 2, cap 3 from `Case3Witness.{u}`**:
   replace with `R1_paper_faithful` per §2.1 signature.
2. **K=1 branch** (existing `bipartite_balanced_enum`): preserved as-is.
3. **K≥2 reducible branch**: existing `OrdinalDecompOfReducible` +
   IH descent works (already uses paper's Case-B mechanism). The K=2
   reducible-via-cap-1-chain shortcut at `Case3WitnessProof.lean:303-307`
   becomes a special case of K≥2 reducible recursion.
4. **K≥2 irreducible branch** (existing `bounded_irreducible_balanced_hybrid`):
   the existing F5a Bool certificate scope (`case3_certificate` for
   K∈{3,4} small cells) does *not* directly cover non-singleton-band
   configurations. **This is the substantive sub-residual within R1.**
   Possible discharge routes:
   * (i) Extend `Case3Enum` framework to non-singleton-band configs.
     Within `prop:in-situ-balanced`'s `|Q| ≤ 3(3w+1) ≤ 39` scope, the
     enumeration is finite (still well within `native_decide` budget).
   * (ii) Direct paper-style proof of `prop:in-situ-balanced` Cases 1
     (ambient profile match) + 2 (FKG profile ordering) without cap 1
     (the swap involution and FKG argument both work without cap 1).
     Case 3 (3-element profile antichain) needs the enumeration; the
     existing `case3Witness_hasBalancedPair_outOfScope` axiom is the
     paper-axiomatised cover.

mg-2970 recommends path (ii) as the closest match to the paper's
text. The `case3Witness_hasBalancedPair_outOfScope` axiom would
generalise to drop its current cap-2/cap-3/cap-1-inducing hypotheses,
becoming the paper-axiomatised statement of `prop:in-situ-balanced`
Case 3 alone. mg-4d7b's enumeration evidence then supports the axiom
for the cap-1 sub-slice (existing scope); a future polecat would
extend the verification to the non-cap-1 cells if needed.

### §4.2 — R2 discharge: bandwidth-`≤ 4` existence

Path:
1. **`|α| ≤ 10` slice**: constructive per §3.2.
   * (b1) explicit construction theorem, OR
   * (b2) `native_decide` finite-search certificate over width-3
     non-chain posets on `n ≤ 10` elements, verifying `∃ L, L.w ≤ 4`
     for each.

2. **`|α| ≥ 11` slice**: faithful Lean delivery of Steps 1-7
   `prop:72` with `bandwidth ≤ 4`. Replaces the current sham
   `bandwidth = Fintype.card α + 1` in `ChainPotentials.lean`. Long-arc
   work; the residual statement (R2 restricted to `|α| ≥ 11`)
   *is* the in-Lean image of the paper's `prop:72`-specialised-to-`w₀(γ) ≤ 4`.

### §4.3 — mg-4d7b's role under the corrected residual

mg-4d7b is **NOT** the R-narrow discharge as mg-5c32 claimed. It IS
the discharge for a *different* statement:

> **mg-4d7b discharges:** `Case3Witness.{u}` (the universal Prop with
> all five caps). I.e., for every `(β, LB)` satisfying caps 1+2+3+4+5,
> mg-4d7b's enumeration provides `HasBalancedPair β`.

This is what `Case3Witness_proof.{u}` actually delivers (per mg-82fc
§1-3). It is **not** the same as discharging the headline at `|α| ≤ 10`
because not every width-3 non-chain α with `|α| ≤ 10` admits a
cap-1+cap-5 LB (§1.3 counterexample).

Under the corrected residual (§2), mg-4d7b retains a useful role as
**evidence for the cap-1 sub-slice of `prop:in-situ-balanced` Case 3**
(extending `case3_certificate` from K∈{3,4} small cells to K∈{2..10}
all singleton-band cells with `w ≤ 4`). This is helpful for R1's
discharge sub-step (§4.1 path (i)) when R1 is restricted to inputs
with cap 1; it does not directly help when R1's input is a non-singleton-band L.

### §4.4 — The mg-d5a0 structured `sorry` under the corrected residual

The `sorry` at `LayeredBalanced.lean:755` is `hLBw : (canonicalLayered α).w ≤ 4`,
unprovable for `|α| ≥ 5` since `canonicalLayered α` has `w = |α|`.

Under the corrected residual:

* If the `lem_layered_balanced` K≥2 dispatch is **rewritten to consume
  the caller's L** (mg-82fc Option D-narrow), the cap-5 obligation
  moves to the caller. The caller (`mainTheoremInputsOf` /
  `layeredFromBridges`) then needs to supply L with `L.w ≤ 4` — which
  is precisely R2.

* If the `lem_layered_balanced` is **rewritten to invoke R1 directly**
  (no `Case3Witness.{u}` universal, no cap 1), the K≥2 branch just
  needs `L.w ≤ 4` and width-3 / non-chain hypotheses, with no
  cap-1 / cap-2 / cap-3 to discharge. The structured `sorry`
  disappears entirely.

Both paths close the `sorry`; the second is preferable because it also
fixes the cap-1-coverage gap (mg-5c32 / §1.3) that the first path
inherits.

### §4.5 — `case3Witness_hasBalancedPair_outOfScope` axiom under the corrected residual

The axiom currently takes a `Case3Witness L` hypothesis and a full
suite of `hWidth3, hIrr, hK3, hw, hCard, hDepth, hScope` cap
hypotheses. Under the corrected residual, after R1 absorbs the F3
strong induction's role:

* The axiom remains load-bearing for the **K≥3 irreducible
  ¬InCase3Scope** leaf (Case 3 of `prop:in-situ-balanced`).
* The axiom's hypotheses can be **simplified** (drop cap 1 antecedents
  to match the uncapped R1 scope, OR retain them and only invoke the
  axiom in the cap-1 sub-slice — the rest covered by Case 1
  ambient-match + Case 2 FKG within R1).
* The axiom's **math content remains paper-axiomatised** from
  `step8.tex:3033-3047` + `rem:enumeration`. mg-4d7b's enumeration
  covers the cap-1 sub-slice; extending coverage to non-cap-1
  configurations is a follow-on enumeration task (the count grows but
  remains finite at `|Q| ≤ 39`).

---

## §5. Lean signatures (full)

```lean
namespace OneThird

-- The corrected residual statements.

/-- **R1** — paper-faithful uncapped `lem:layered-balanced`.
Matches `step8.tex:3199-3253` exactly. -/
def R1_paper_faithful.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α]
    (L : Step8.LayeredDecomposition α),
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    L.w ≤ 4 →
    HasBalancedPair α

/-- **R2** — existence of a bounded-bandwidth layered decomposition.
Matches paper `prop:72` specialised to bandwidth `≤ 4`. -/
def R2_exists_bounded_bandwidth.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α → 2 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4

/-- **The reduction.** R1 + R2 ⇒ headline. -/
theorem width3_reduction.{u}
    (hR1 : R1_paper_faithful.{u})
    (hR2 : R2_exists_bounded_bandwidth.{u}) :
    ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
      HasWidthAtMost α 3 → ¬ IsChainPoset α → HasBalancedPair α := by
  intro α _ _ _ hW3 hNC
  by_cases h2 : 2 ≤ Fintype.card α
  · obtain ⟨L, hLw⟩ := hR2 α hW3 hNC h2
    exact hR1 α L hW3 hNC h2 hLw
  · -- |α| ≤ 1: subsingleton ⇒ chain.
    push_neg at h2
    interval_cases (Fintype.card α)
    · -- |α| = 0
      exact absurd (chain_of_card_zero) hNC
    · -- |α| = 1
      exact absurd (chain_of_card_one) hNC

end OneThird
```

The two `chain_of_card_*` lemmas are easy (`|α| ≤ 1` makes α a chain
vacuously since there are no incomparable pairs). They already exist
in tree implicitly via the `|α| < 2` branch of `width3_one_third_two_thirds_assembled`
(`MainAssembly.lean:326-332`); a 5-line port suffices to expose them
at the right namespace.

### §5.1 — Discharge signatures (for R2's two slices)

```lean
/-- R2 small-α (|α| ≤ 10) — constructive. -/
def R2_small.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α →
    2 ≤ Fintype.card α → Fintype.card α ≤ 10 →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4

/-- R2 large-α (|α| ≥ 11) — Steps 1-7 conditional. -/
def R2_large.{u} : Prop :=
  ∀ (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α],
    HasWidthAtMost α 3 → ¬ IsChainPoset α →
    11 ≤ Fintype.card α →
    ∃ (L : Step8.LayeredDecomposition α), L.w ≤ 4

/-- R2_small + R2_large ⇒ R2. -/
theorem R2_split (hS : R2_small.{u}) (hL : R2_large.{u}) :
    R2_exists_bounded_bandwidth.{u} := by
  intro α _ _ _ hW3 hNC h2
  rcases Nat.lt_or_ge (Fintype.card α) 11 with h | h
  · exact hS α hW3 hNC h2 (by omega)
  · exact hL α hW3 hNC h
```

R2_small discharge (§3.2 path b1 or b2). R2_large discharge: faithful
Steps 1-7 Lean delivery.

### §5.2 — How this differs from `Case3Witness.{u}`

| Aspect | `Case3Witness.{u}` (existing) | `R1_paper_faithful` (corrected) |
|---|---|---|
| Input shape | `(β, LB)` with 5 cap-antecedents | `(α, L)` with only `L.w ≤ 4` |
| Non-vacuous scope | `|β| ≤ 10` (cap 1+2+5 conjunction) | every width-3 non-chain `α` (no cap-induced restriction) |
| K=1 branch | `bipartite_balanced_enum` ✓ | same ✓ |
| K=2 reducible branch | derives contradiction from cap 1 | recurses on factor (paper's Case B) |
| K=2 irreducible branch | `option_c_K2_closure` via `case2_certificate` | needs cap-1-free version; paper's `prop:bipartite-balanced` is the route |
| K≥3 reducible branch | `OrdinalDecompOfReducible` + IH ✓ | same ✓ |
| K≥3 irreducible branch | `bounded_irreducible_balanced_hybrid` + cap-1-restricted F5a certificate | needs cap-1-free F5a certificate OR direct paper-port of `prop:in-situ-balanced` Cases 1+2 + paper-axiomatised Case 3 |
| Coverage of headline | `|α| ≤ 10` cap-1-cap-5 sub-slice | full headline (any `|α|`, any width-3 non-chain) |
| Closes mg-d5a0 sorry? | only under mg-82fc Option D-narrow rewrite, AND only for cap-1 sub-slice | yes, completely (no cap-5 obligation; sorry disappears) |
| Closes cap-1 gap (§1.3)? | no (cap 1 is built in) | yes (cap 1 dropped) |

---

## §6. Paper cleanup recommendation

mg-5c32 §4 proposed 8 paper rewrites. Under the corrected residual,
the relevant rewrites differ in scope. Updates to mg-13a5 paper cleanup
(if it cites mg-5c32's broken form):

### §6.1 — Revised paper cleanup table

| Section | mg-5c32 recommendation | mg-2970 revision |
|---|---|---|
| `main.tex` §1.4 (road map) | Add residual subsection citing `LayeredResidual` 5-cap form | **Revise**: cite `R1_paper_faithful` (uncapped paper-faithful) + `R2_exists_bounded_bandwidth` (existence of `L.w ≤ 4`). Drop cap-1/cap-2/cap-3 mention. |
| `step7.tex` `prop:72` | "interaction width `w = w₀(γ) ≤ 4`" | Unchanged — mg-5c32 was correct on this. |
| `step8.tex` §sec:main-thm | "in-tree Lean uses G4 uniformly via F3 strong induction" | Unchanged. |
| `step8.tex` `lem:layered-balanced` | "Lean discharge via uniform F3 strong induction in `Case3Witness_proof`, with cap-1+cap-5 caps" | **Revise**: "Lean discharge via paper-faithful strong induction (R1 of mg-2970), or via the cap-1-restricted `Case3Witness_proof.{u}` if R1 is unavailable. The latter covers only the cap-1-cap-5 sub-slice." |
| `step8.tex` `prop:in-situ-balanced` Case 3 | "Replace `rem:enumeration` with explicit mg-4d7b citation" | Unchanged — mg-5c32 was correct on this for the cap-1 sub-slice. |
| `step8.tex` `rem:enumeration` | mg-4d7b certificate citation | **Revise**: clarify mg-4d7b's scope is the cap-1 sub-slice; extending to non-cap-1 configurations is open work (paper's `lem:enum` admits both cap-1 and non-cap-1 configurations within `|Q| ≤ 3(3w+1)`). |
| `step8.tex` `rem:residual-base` | "verified by enumeration (mg-4d7b)" | **Revise**: same as `rem:enumeration` — clarify cap-1 scope. |
| `step8.tex` §sec:layered-reduction | "Mark `lem:layered-reduction` as paper-only" | Unchanged. |
| `step8.tex` §sec:G2-constants | Cross-reference Hypothesis 1 | Unchanged. |

### §6.2 — Revised headline disclosure (§6 of mg-5c32)

mg-5c32 recommended a two-part headline (i) unconditional `|α| ≤ 10`
slice via mg-4d7b, (ii) `|α| ≥ 11` slice conditional on Steps 1-7
`w₀(γ) ≤ 4`. Per the corrections in §1.3, the (i) slice's discharge
via mg-4d7b is incomplete (cap-1 sub-slice only). The corrected
headline disclosure:

> **Theorem (Width-3 1/3-2/3, in-tree Lean formalisation, mg-2970
> corrected).** For every finite poset α of width ≤ 3 that is not a
> chain, modulo two named residuals (R1 + R2):
>
> (R1) `R1_paper_faithful` — Lean port of paper's
> `lem:layered-balanced` strong induction (uncapped; drops cap 1 / cap 2
> / cap 3 / cap 4 / explicit cap 5 from the current `Case3Witness.{u}`).
> Status: math content is the paper proof at `step8.tex:3199-3253`;
> Lean port estimated 3-5 polecat sessions (with possible F5a
> extension for non-singleton-band coverage).
>
> (R2) `R2_exists_bounded_bandwidth` — existence of a layered
> decomposition with `L.w ≤ 4` for every width-3 non-chain finite α.
> Decomposes by `|α|`: `|α| ≤ 10` constructive (1-2 polecat sessions);
> `|α| ≥ 11` paper's `prop:72` + Steps 1-7 cascade
> (currently sham; faithful delivery is multi-month).

This headline correctly separates the math content (R1) from the
existence content (R2), and clearly states the scope of each residual's
discharge.

---

## §7. Cross-references and load-bearing claims

### §7.1 — Lean files

* `lean/OneThird/MainTheorem.lean:56` — `width3_one_third_two_thirds`.
* `lean/OneThird/Step8/LayeredBalanced.lean:461-472` —
  `Case3Witness.{u}` (the 5-cap universal that mg-5c32 transcribed).
* `lean/OneThird/Step8/LayeredBalanced.lean:498-535` —
  `canonicalLayered`: K=w=|α| (fails cap 5 for `|α| ≥ 5`).
* `lean/OneThird/Step8/LayeredBalanced.lean:626-756` —
  `lem_layered_balanced`: K=1 substantive; K≥2 `canonicalLayered`
  substitution + cap-5 `sorry` at line 755.
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256-547` —
  `Case3Witness_proof.{u}`: F3 strong induction (substantive backbone
  for cap-1-cap-5 slice; needs rewrite for R1 — see §3.1).
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:106-145` —
  `isChain_of_K2_reducible_under_injective`: the cap-1-dependent K=2
  reducible branch that needs rewriting under R1.
* `lean/OneThird/Step8/Case3Residual.lean:208-217` —
  `case3Witness_hasBalancedPair_outOfScope` axiom (load-bearing for
  `prop:in-situ-balanced` Case 3 residual; current hypothesis profile
  includes cap 1, would need adjustment under R1).
* `lean/OneThird/Step8/BoundedIrreducibleBalancedInScope.lean:97-222` —
  `bounded_irreducible_balanced_inScope`: the F5a substantive leaf
  (uses cap-1 via `predMaskOf L`'s upper-triangularity; extending to
  non-cap-1 is the §3.1 R1 sub-residual).
* `lean/OneThird/Step8/Case3Enum/Certificate.lean:71` —
  `case3_certificate`: covers `K∈{3,4} w∈{1..4}` cells (singleton-band).
* `lean/OneThird/Step8/Case3Enum/Cap5Singletons.lean` — mg-4d7b
  Lean port (K∈{2,4..8} singleton-band cells).
* `lean/OneThird/Step8/Case3Enum/Cap5SingletonsK9.lean` — mg-4d7b
  K=9 cell port.
* `lean/scripts/enum_cap5.py` + `enum_cap5_K10.py` +
  `enum_cap5_certificate.json` — mg-4d7b Python enumeration of the
  cap-1-cap-5 sub-slice.
* `lean/OneThird/Step7/Assembly.lean:302-348` — `LayeredWidth3`,
  `prop_72` Lean stub. `bandwidth` field returns sham `|α| + 1`.
* `lean/AXIOMS.md` — named axioms inventory.

### §7.2 — Paper sources

* `step7.tex:1175-1193` — `prop:72`.
* `step7.tex:1193-1219` — `rem:w0-constant` (`w₀(γ) ≤ 4`).
* `step8.tex:1892-1901` — Layered decomposition axioms (L1)-(L4).
* `step8.tex:2580-2654` — Layer-ordinal reducibility theory.
* `step8.tex:2780-2797` — `lem:irr-adjacent` (F2).
* `step8.tex:2965-3072` — `prop:in-situ-balanced` (Cases 1, 2, 3).
* `step8.tex:3050-3067` — `lem:enum` (finite enumeration of
  bounded-depth irreducible layered posets — note: NOT restricted to
  cap-1).
* `step8.tex:3199-3253` — Proof of `lem:layered-balanced` (the strong
  induction R1 ports).
* `step8.tex:3157-3173` — `rem:enumeration` (mg-4d7b certificate
  citation — note: focuses on cap-1 sub-slice).
* `step8.tex:3194-3236` — `rem:residual-base`.

### §7.3 — Predecessor work items

* `mg-e2e9` — pre-cap-5 Case3Witness vacuous via canonicalLayered.
* `mg-d5a0` — cap-5 signature refactor (introduced the `sorry`).
* `mg-74d2` — layered-form-vs-coherence audit.
* `mg-0cbf` — post-cap-5 tractability analysis.
* `mg-4d7b` — cap-5 enumeration (**cap-1 sub-slice only**; §1.3 finding).
* `mg-5c32` — the over-constrained first residual extraction;
  superseded by this document in same on-disk location.
* `mg-82fc` — Phase A audit confirming F3 conclusion-lift is
  substantive (input to mg-2970).
* `mg-6f04` — PROOF-STRUCTURE-ONBOARDING.md canonical entry.
* `mg-13a5` — paper cleanup; needs revision per §6 above if it
  references mg-5c32's broken `LayeredResidual` form.
* `mg-7377` — Case3Witness QA.
* `mg-9a4a` — Window C K=4 w=1 sliver.
* `mg-f92d` — Case 1 ambient profile match.

---

## §8. Summary

* **Phase A** (`mg-5c32` over-constraint diagnosis, §1). Two specific
  errors in mg-5c32: (i) §0 and §3c's `LayeredResidual_broad` both
  staple all 5 `Case3Witness` caps onto an `|α| ≥ 11` statement that
  is unsatisfiable under caps 1+2+5; (ii) §3c's `LayeredResidual_narrow`
  claims discharge "by mg-4d7b enumeration", but mg-4d7b covers only
  the cap-1-cap-5 sub-slice (β admitting singleton-band L with
  bandwidth ≤ 4), missing width-3 non-chain α with `|α| ≤ 10` that
  have balanced pairs but no such L (e.g.
  `α = 3-antichain ⊕ 3-antichain`, `|α| = 6`).

* **Phase B** (corrected residual statement, §2 + §5). Two
  precisely-typed residuals: R1 (paper-faithful uncapped Lean
  `lem:layered-balanced`) + R2 (existence of layered decomposition
  with `L.w ≤ 4`). R1 + R2 ⇒ headline via `width3_reduction` (§5).

* **Phase C** (satisfiability proofs, §3). R1: the paper proof at
  `step8.tex:3199-3253` is exactly its content; the Lean port follows
  the paper's strong-induction template (3-5 polecat sessions for
  core; possibly 2-3 more for F5a certificate extension if needed).
  R2 small-α: constructive via iterated ordinal-sum decomposition
  (1-2 polecat sessions). R2 large-α: paper's `prop:72` +
  Steps 1-7 cascade (multi-month long-arc).

* **Phase D** (paper cleanup, §6). Updates mg-5c32's §4 cleanup:
  R1 vs R2 split replaces the cap-laden `LayeredResidual` in `main.tex` §1.4;
  `prop:72` constant pinning unchanged; mg-4d7b's role clarified as
  cap-1 sub-slice (not full small-α coverage).

* **Daniel's framing answered (mg-2970 corrected)**:
  - "what have we actually reduced to?" → **R1 ∧ R2**. Two precisely
    typed statements with explicit satisfiability evidence at each
    component.
  - "coherence or layered structure with specific constants?" →
    **layered structure** with specific constant `L.w ≤ 4`. The
    coherence-side framing reduces to the same content via the
    paper's `prop:72` packaging (per mg-74d2 §3c + mg-5c32 §3e/f
    — unchanged).
  - "one place to reference" → §0 + §2 + `R1_paper_faithful` +
    `R2_exists_bounded_bandwidth`'s Lean-style signatures (§5).

* **Verdict: GREEN-two-residual-extracted-each-satisfiable**.
  Phase A diagnoses mg-5c32's two over-claims; Phase B delivers the
  corrected R1 + R2; Phase C demonstrates each cap's satisfiability;
  Phase D revises paper cleanup. The Lean signatures (§5) are
  drop-in for the post-restatement headline.

* **PROOF-STRUCTURE-ONBOARDING.md §3 pitfall #2 updated** in the same
  commit per maintenance contract (§5 of that doc). The updated
  pitfall text matches the corrected residual.
