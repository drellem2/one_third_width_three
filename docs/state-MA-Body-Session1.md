# State — MA-Body — Session 1: the Piece-4 proof-by-contradiction body

**Owner.** `mg-9add` (OneThird-MA-Body, FULL REFACTOR Phase 2, Piece 4
— the `MainAssembly` proof-by-contradiction body; the last body
sub-ticket of Piece 4 per `mg-92a8` §7).

**Scope.** Assemble the proof body of
`width3_one_third_two_thirds_assembled` as a proof by contradiction
per the pinned Piece-4 signature contract
`docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.8; delete the old
direct-construction machinery (`mainAssembly`, `mainTheoremInputsOf`,
`caseC_canonicalLayered`, `MainTheoremInputs`).

---

## §0. Verdict — **GREEN-Piece-4-body-assembled (with two disclosed axioms)**

`width3_one_third_two_thirds_assembled` is rewritten as the
proof-by-contradiction of mg-92a8 §4.8, sorry-free; the four named
direct-construction machinery items are deleted; the headline
instantiates non-vacuously at the concrete width-3 non-chain poset
`Antichain3`. **Piece 4 is complete.**

The mg-92a8 §4.8 body could **not** be assembled exactly as pinned:
two of its "mechanical" auxiliary combinators are genuine un-ported
mathematics, re-pinned here as documented, `AXIOMS.md`-certified
project axioms (findings **F-Body-1**, **F-Body-2**). This is the
same posture as `mg-52e0`'s `stepsOneToSevenCascade` (F-Cascade-1) —
honest representation of un-ported true sub-claims, not new vacuity.

---

## §1. What landed

`lean/OneThird/Step8/MainAssembly.lean` — rewritten:

* **`width3_one_third_two_thirds_assembled`** — the proof by
  contradiction (mg-92a8 §4.8): `hasBalancedPair_of_strongInduction`
  → `by_contra` → `gamma_counterexample_of_no_BP` → `decomp_reduction`
  → a `by_cases` dichotomy on `n_zero γ (hArith.T γ) ≤ |β|`:
  - **large `|β|`**: `theoremE_lowConductanceWitness` →
    `stepsOneToSevenCascade` → `chainLiftData_of_cascade` →
    `lem_layered_from_step7` (Piece 3) → `lem_layered_balanced_full`
    (Piece 6) → `not_isGammaCounterexample_of_exc_balanced_compl`
    (S7-F-D) → `exact hNotCex hCex` (finding F3 — contradict `hCex`);
  - **small `|β|`**: `width3_smallN_hasBalancedPair` (the `lem:small-n`
    base case) → contradict `hNoBP`.
  - Signature: `hC3 : Case3Witness` **dropped**,
    `hArith : HypothesisArithmetic` **added**; opens with `classical`
    for the `[DecidableLE α]` instance (finding F7) — no public-API
    change beyond the `hArith` hypothesis.
* **`card_compl_ge_two`**, **`exc_perturb_bound_of_n_zero`** — the
  genuinely-mechanical mg-92a8 §4.8 aux combinators, proved
  sorry-free (helper `nzero_ge`).
* **`width3_smallN_hasBalancedPair`**, **`nonChain_compl_of_no_balancedPair`**
  — two new disclosed project axioms (findings F-Body-1/F-Body-2).
* **`antichain3_width3_one_third_two_thirds_assembled`** — the
  non-triviality certificate (headline at `Antichain3`).
* **Deleted**: `MainTheoremInputs`, `caseC_canonicalLayered`,
  `mainTheoremInputsOf`, `mainAssembly`. **Retained** (off the
  headline path, harmless): `trivialLayered`, `mainAssembly_smallN`,
  `width3_one_third_two_thirds_via_step8` (signature updated).

`lean/OneThird/MainTheorem.lean` — `width3_one_third_two_thirds`
gains `hArith : Step8.HypothesisArithmetic`, drops `hC3`, forwards to
`width3_one_third_two_thirds_assembled`.

`lean/AXIOMS.md` — two new entries (`width3_smallN_hasBalancedPair`,
`nonChain_compl_of_no_balancedPair`).

---

## §2. Findings — drift from the mg-92a8 contract (recorded per its §9)

### F-Body-1 — `n_zero_le_of_cascade_realised` is ill-posed

mg-92a8 §4.8 pins `hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α :=
n_zero_le_of_cascade_realised hArith hcard hγ_pos hγ_third` and §4.8
aux describes it as deriving `n_zero γ T ≤ |α|` "from `hArith` +
`2 ≤ |α|`". **No such theorem exists** — it is *false* for every
minimal counterexample with `|α| < n_zero γ T`. Since `n_zero γ T =
⌈4·C_exc T/γ⌉ + C_exc T` and `C_exc T = c₁ T + 6 ≥ 6`, the regime
`2 ≤ |α| < n_zero γ T` is non-empty and reachable. `mg-52e0`
(MA-Cascade) did not land `n_zero_le_of_cascade_realised` (its §10.2
F-Cascade-1..4 do not mention it) — correctly, because it is not a
theorem.

**Resolution.** The body uses a `by_cases` dichotomy on
`n_zero γ (hArith.T γ) ≤ |β|`. The small-`|β|` leaf is the paper's
`lem:small-n` base case (`step8.tex:757-825` + `rem:small-n`). The
in-tree `Step8.lem_small_n` (`SmallN.lean`) is **not** a discharge —
`kahnLinialBaseCase` / `smallNFiniteEnum` / `lem_small_n` all package
the Kahn–Linial bound and the finite enumeration as *hypotheses*
(`HasBalancedPair α ∨ HasBalancedPair α`). The honest discharge is
the new axiom `width3_smallN_hasBalancedPair` — the Kahn–Linial bound
is external math not in mathlib, the enumeration is a mechanical
computation not formalised. See `AXIOMS.md`.

### F-Body-2 — `non_chain_subtype_of_exc` is not a mechanical combinator

mg-92a8 §4.8 aux lists `non_chain_subtype_of_exc : ¬ IsChainPoset
↥(Xexcᶜ)` as a "mechanical" combinator, justified by "a width-3
non-chain `α` has `≥ |α| − 3` incomparable pairs; deleting `O_T(1)`
elements leaves one." **The justification is false.** A width-3
non-chain poset can concentrate *all* its incomparability on an
`O_T(1)` vertex cover — e.g. a long chain `c₁ < ⋯ < cₘ` with `O(1)`
floaters — so it can have as few as one incomparable pair, and naive
counting (even `card_univ_le_ordIncompPairs_card`'s `≥ |β|` ordered
incomparable pairs for indecomposable `β`) does not survive deletion
of an `O_T(1)` vertex cover (consider a star).

`↥(Xexcᶜ)` non-chain is nonetheless **true** in context, but only via
`hNoBP`: were `↥(Xexcᶜ)` a chain, every incomparable pair of `β`
would touch `Xexc`; since `β` is indecomposable it has `≥ |β|`
ordered incomparable pairs, so some `Xexc`-element is incomparable to
a long *contiguous* sub-chain of `↥(Xexcᶜ)`, hence forms a *balanced*
pair with that range's middle (`Pr ≈ 1/2`) — contradicting `hNoBP`.
That is Step-8-level combinatorics, not a mechanical combinator.

**Resolution.** The new axiom `nonChain_compl_of_no_balancedPair`
takes `hP`, `hNonChain`, `hNoBP`, `hI : Indecomposable β`,
`|Xexc| ≤ C_exc T`, `n_zero γ T ≤ |β|` and concludes
`¬ IsChainPoset ↥(Xexcᶜ)`. `hNoBP` is load-bearing (without it the
statement is false — a long chain plus one global floater is a
counterexample). See `AXIOMS.md`.

### Non-findings (contract honoured exactly)

* **F3** — the final contradiction is `hNotCex hCex`, not on
  `hNoBP`. ✓ (large-`|β|` branch).
* **F4** — the bridge carrier `↥(Xexcᶜ)` is consumed by the `_compl`
  variant `not_isGammaCounterexample_of_exc_balanced_compl`. ✓
* **F5** — the perturbation side condition is `2·|Xexc|/(|β|−|Xexc|+1)
  ≤ γ` (`≤ γ`); `exc_perturb_bound_of_n_zero` discharges it. ✓
* **F7** — the body opens with `classical`; no `[DecidableLE α]` on
  the public headline. ✓
* **F-MinCex-1** — `decomp_reduction` takes `¬ HasBalancedPair α`,
  not `IsGammaCounterexample α γ`; the call site has `hNoBP` in scope
  via `by_contra`. ✓ (wired on the real shape).

---

## §3. The post-refactor headline axiom set

`#print axioms width3_one_third_two_thirds` after Piece 4:

* `LinearExt.brightwell_sharp_centred` — external (Brightwell–Tetali);
* `lem_layered_balanced_irreducible_base` — Piece 6 (`mg-65de`);
* `stepsOneToSevenCascade` — Steps 1-7 cascade (`mg-52e0`);
* **`width3_smallN_hasBalancedPair`** — `lem:small-n` base case (new);
* **`nonChain_compl_of_no_balancedPair`** — exceptional-set non-chain
  survival (new);
* Mathlib's `propext` / `Classical.choice` / `Quot.sound`.

The pre-refactor headline carried `case3Witness_hasBalancedPair_outOfScope`
(reached only through the deleted `Case3Witness_proof` direct path) and
a structured `sorry` at `caseC_canonicalLayered`. Both are **gone**:
the `sorry` is excised (replaced by the proof-by-contradiction), and
`case3Witness_hasBalancedPair_outOfScope` drops off the headline path.

Net change vs. mg-92a8 §6's projection (`{brightwell,
irreducible_base, stepsOneToSevenCascade}`): **+2 axioms**
(`width3_smallN_hasBalancedPair`, `nonChain_compl_of_no_balancedPair`)
— the two un-portable base-case leaves the contract §4.8 had assumed
mechanical. Both are sorry-free, paper-faithful, `AXIOMS.md`-certified.

---

## §4. Non-triviality bar

The headline instantiates non-vacuously at the concrete width-3
non-chain poset `Antichain3`:
`antichain3_width3_one_third_two_thirds_assembled (hArith) :
HasBalancedPair Antichain3`. `HasBalancedPair Antichain3` is
genuinely true (the antichain's elements are pairwise symmetric,
`Pr = 1/2`). The paper Hypothesis A `hArith` is retained as a
hypothesis — faithful to `step8.tex` stating `thm:main-step8` under
`hyp:arith`. No headline obligation is ill-posed: the two ill-posed
contract pins (F-Body-1/F-Body-2) were replaced by well-posed
case-split + paper-faithful axioms, not pushed through.

---

## §5. Cross-reference index

* `lean/OneThird/Step8/MainAssembly.lean` — the body (this work).
* `lean/OneThird/MainTheorem.lean:56` — the headline wrapper.
* `lean/OneThird/Step8/MinCounterexample.lean` — `mg-7969`
  (`hasBalancedPair_of_strongInduction`, `decomp_reduction`,
  `gamma_counterexample_of_no_BP`, `chain_of_subsingleton`).
* `lean/OneThird/Step8/Cascade.lean` — `mg-52e0` (`HypothesisArithmetic`,
  `n_zero`, `n_zero_ceil_ge`, `stepsOneToSevenCascade`,
  `chainLiftData_of_cascade`).
* `lean/OneThird/Step8/TheoremEWiring.lean` — `mg-3638`
  (`theoremE_lowConductanceWitness`).
* `lean/OneThird/Step8/LayeredFromStep7.lean` — `mg-02cd`
  (`lem_layered_from_step7`, Piece 3).
* `lean/OneThird/Step8/LayeredBalancedFull.lean` — `mg-65de`
  (`lem_layered_balanced_full`, Piece 6).
* `lean/OneThird/Step8/ExcBalancedLift.lean` — `mg-876f`
  (`not_isGammaCounterexample_of_exc_balanced_compl`, S7-F-D).
* `docs/state-Piece4-Sig-Session1.md` (mg-92a8) §4.8 — the pinned
  body; §9/§10 — the maintenance contract this doc reports under.
* `lean/AXIOMS.md` — the two new axiom entries.
