# S7-F-bridge — Session 2: RED 8th vacuity discovery on the MA-Sig bridge signature (mg-0bd1)

**Ticket:** mg-0bd1 (OneThird-Refactor-P3: S7-F bridge
`lem:layered-from-step7` — structural ground-set lift, all 5 caps).
**Predecessors:** mg-5fbd (S7-F bridge audit Session 1, RED 7th
vacuity), mg-a22b (MA-Sig signature contract, commit `369a0a0`),
mg-d8c7 (Option A' FULL REFACTOR scoping).
**Verdict:** **RED — 8th vacuity discovery.** The S7-F bridge
`lem_layered_from_step7` **cannot be built honestly against the
pinned MA-Sig §4.2 §E signature**, because that signature's
five-cap conclusion is **structurally unsatisfiable for large
minimal γ-counterexamples** — the exact `Case3Witness`-cap
transcription error that `PROOF-STRUCTURE-ONBOARDING.md` §3
pitfall #2 warns against, recurring inside the MA-Sig pseudo-Lean.

This session produced **no Lean changes**. The deliverable is this
audit document plus the maintenance-contract updates to
`PROOF-STRUCTURE-ONBOARDING.md` (§3 pitfall #6) and
`docs/state-MA-Sig-Session1.md` (§9 8th-vacuity record). Mirrors the
mg-5fbd Session 1 doc-only RED pattern.

---

## §0. Verdict — **RED-signature-unsatisfiable**

Building piece 3 (the S7-F bridge) against the pinned signature
contract is impossible, and the obstruction is **not** in the
bridge construction — it is in the **pinned signature itself**.

The contract `MA-Sig §4.2 §E` pins:

```lean
theorem lem_layered_from_step7
    (γ : ℚ) (hγ_pos : 0 < γ) (T : ℕ)
    (hP : HasWidthAtMost α 3) (hI : Indecomposable α)
    (hCascade : Step5R α γ T ∨ Step5C α T)
    (ih : ∀ m, m < Fintype.card α → …) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition {a : α // a ∉ Xexc}),
      Xexc.card ≤ C_exc T ∧
      Function.Injective L.band ∧                  -- cap 1
      L.K ≤ 2 * L.w + 2 ∧                          -- cap 2
      (Fintype.card α - Xexc.card) ≤ 6 * L.w + 6 ∧ -- cap 3
      (∀ k, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧ -- cap 4
      L.w ≤ 4                                      -- cap 5
```

**Claim (proved in §2): this conclusion forces
`Fintype.card α ≤ 10 + C_exc T`.** Since `C_exc T` is `O_T(1)`
(a constant for fixed `T`) and the bridge is invoked on minimal
γ-counterexamples of **unbounded** size (§3), the theorem is
**false** — not merely vacuous — for every large minimal
γ-counterexample. No bridge construction, however much Lean
effort, can prove a false statement.

**Root cause (§4): `lem_layered_balanced` / `Case3Witness` is the
`|β| ≤ 30`, `K ≤ 10` finitely-bounded restriction, NOT the full
Step 8 G4.** The MA-Sig contract §4.2 §G pinned `lem_layered_balanced`
"UNCHANGED" and therefore had to pin the bridge (its producer) to
emit `Case3Witness`'s five caps. But `lem_layered_balanced`'s own
in-tree docstring (`LayeredBalanced.lean:449`) states verbatim:
*"Under cap 5 the existing caps become honest finite-domain
restrictions (`|β| ≤ 30`, `K ≤ 10`, `w ∈ {1,2,3,4}`)."* It is the
`|β| ≤ 10` base sub-slice of Step 8, not Step 8.

**Consequence: the 5-piece mg-d8c7 decomposition is missing a
piece** — the faithful Lean port of the **full** Step 8 G4
(`lem:layered-balanced` taking `(β, L)` with only `L.w ≤ 4`,
strong induction on `|β|`, no caps 1/2/3). `PROOF-STRUCTURE-
ONBOARDING.md` §3 pitfall #2 calls this *"the entire Step 8
engineering target"*; mg-d8c7 §4.1 instead lists the existing
`lem_layered_balanced` as *already-in-tree, usable*. It is not
usable as the Step-8 endpoint — only as the bounded base case.

**Recommendation (§7-§8): re-scope before any P3/P4 Lean work.**
The minimal repair (§7) is to (a) correct the bridge conclusion to
drop caps 1/2/3 and keep only `L.w ≤ 4` (+ `Xexc.card ≤ C_exc T`,
+ optionally cap 4); and (b) add a **6th piece** to mg-d8c7: the
full Step 8 G4 port. Building piece 3 against the current pinned
signature would be the literal "paper over it" anti-pattern.

Acceptance bar against the ticket body:

| Bar | Status |
|---|---|
| Construct S7-F bridge satisfying all 5 caps | **Impossible** — 5-cap conclusion unsatisfiable for large α (§2-§3) |
| Non-triviality: hold on arbitrary width-3 non-chain α | The 5-cap form holds **only** for `\|α\| ≤ 10 + C_exc T` — a bounded slice (§2) |
| Verify against mg-5fbd counterexample (3 chains of 3) | The counterexample's mechanism (caps 1+4 → singletons → K bounded) is *exactly* what kills the pinned signature (§2.3) |
| Block-and-report if hypotheses cannot be supplied | **Invoked.** This document is the block-and-report. |

---

## §1. Context — what piece 3 was asked to do

Piece 3 of the Option A' FULL REFACTOR (mg-d8c7 §2.3) is the
**structural ground-set lift**: a Lean port of paper
`lem:layered-from-step7` (`step8.tex:1983-2106`) that takes the
Steps 1-7 cascade output and produces an exact
`LayeredDecomposition` on `X ∖ X^exc` with interaction width
`w ≤ 4`, which the headline then feeds to `lem_layered_balanced`
(G4) and lifts back to `X` via `exc_perturb` (F6b).

mg-a22b (MA-Sig, the Phase-1 signature pre-flight) pinned the
public signature of every cascade component in `§4.2`, so that
piece 3 (this ticket) parallelizes with piece 1 (Steps 1-6 port).
The pinned bridge signature is `MA-Sig §4.2 §E`, reproduced in §0
above.

The mg-0bd1 ticket body's explicit instructions are honoured:

* *"Non-triviality bar: the bridge must hold on arbitrary width-3
  non-chain alpha, not a vacuous slice."* — checked; it does not
  (§2).
* *"verify against the mg-5fbd counterexample (3 disjoint chains
  of length 3, |alpha|=9)."* — checked; the counterexample's
  mechanism is the proof of the obstruction (§2.3).
* *"Block-and-report if the bridge still requires hypotheses the
  call site cannot supply."* — invoked, generalised: the bridge
  cannot *emit* the conclusion the consumer requires.

---

## §2. The defect — the five-cap conclusion bounds `|α|`

### §2.1. caps 1 + 4 force singleton bands: `card = K`

Let `L : LayeredDecomposition β` for any finite poset `β`. The
structure fields (`LayeredReduction.lean:115-149`) give
`band : β → ℕ` with `band_pos : ∀ x, 1 ≤ L.band x` and
`band_le : ∀ x, L.band x ≤ L.K`. So `L.band` factors through the
finite set `Finset.Icc 1 L.K`, which has `L.K` elements.

* **cap 1** (`Function.Injective L.band`): an injection
  `β ↪ Icc 1 L.K` gives `Fintype.card β ≤ L.K`.
* **cap 4** (`∀ k, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty`):
  every `k ∈ [1, L.K]` is hit by some `x` (`L.band x = k`), so
  `L.band` surjects onto `Icc 1 L.K`, giving `Fintype.card β ≥ L.K`.

Together: **caps 1 + 4 ⟹ `Fintype.card β = L.K`** (singleton
bands). This is airtight — it is a theorem, not a heuristic.

### §2.2. caps 2 + 5 cap `K`, hence cap `|α|`

* **cap 2** (`L.K ≤ 2 * L.w + 2`) **+ cap 5** (`L.w ≤ 4`) ⟹
  `L.K ≤ 2·4 + 2 = 10`.
* With §2.1: `Fintype.card β = L.K ≤ 10`.
* **cap 3** (`Fintype.card α - Xexc.card ≤ 6 * L.w + 6`) **+
  cap 5** ⟹ `Fintype.card α - Xexc.card ≤ 30` independently.

In the bridge conclusion `β := {a : α // a ∉ Xexc}`, and
`Fintype.card {a // a ∉ Xexc} = Fintype.card α - Xexc.card`.
Therefore the five-cap conclusion entails

```
Fintype.card α - Xexc.card  =  L.K  ≤  10        (caps 1+4+2+5)
Fintype.card α            ≤  10 + Xexc.card
                          ≤  10 + C_exc T        (since Xexc.card ≤ C_exc T)
```

**The pinned `lem_layered_from_step7` conclusion implies
`Fintype.card α ≤ 10 + C_exc T`.** For fixed `T` this is a fixed
finite bound on `|α|`.

This is precisely `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.1
(*"Stapling caps 1+4+2+5 together gives an unsatisfiable residual"*)
— here recurring not at residual-extraction but inside the MA-Sig
**pinned signature**.

### §2.3. The mg-5fbd counterexample is the obstruction's mechanism

mg-5fbd §2.3 used `α = 3 disjoint chains of length 3` (`|α| = 9`)
to show no `L` satisfies all five caps. That counterexample is a
*specialisation* of §2.2: caps 1+4 force singletons, caps 2+5
force `K ≤ 10` and `w = 4`, and then `(L2-forced)` cannot be met.
The mg-0bd1 ticket asked to *"verify against"* this counterexample.
Verification result: **the counterexample's mechanism is not a
peculiarity of `|α| = 9` — it is the general §2.2 bound.** The
3-disjoint-chains family at length `ℓ` (`|α| = 3ℓ`) violates the
five caps for every `ℓ ≥ 4` (`|α| ≥ 12 > 10`), and indeed every
width-3 non-chain `α` with `|α| > 10 + C_exc T` does.

The bridge "holds on" the 3-disjoint-chains-of-3 case only in the
degenerate sense that *that* poset has a balanced pair by symmetry
(it is not a γ-counterexample, so `hCascade` is never supplied for
it). It does **not** hold non-trivially on arbitrary large
width-3 non-chain `α` — failing the ticket's non-triviality bar.

---

## §3. Why this is a falsity, not a vacuity

A conditional theorem `H → C` with `H` unsatisfiable is vacuously
*true* and harmless. The S7-F bridge is **not** in that situation.

The bridge's hypothesis is `hCascade : Step5R α γ T ∨ Step5C α T`
— the Step 5 dichotomy output. By paper `thm:step5`, for **every**
minimal γ-counterexample `α` above the small-`n` threshold
`n_0(γ, T)`, the dichotomy holds: `Step5R α γ T ∨ Step5C α T` is
**true**. Minimal γ-counterexamples are of unbounded size (the
1/3–2/3 conjecture ranges over all finite posets; the small ones
are dispatched by `lem_small_n`, the large ones are exactly the
cascade's domain).

So there exist `α` with `Fintype.card α > 10 + C_exc T` (in fact
all sufficiently large minimal γ-counterexamples) for which
`hCascade` is **satisfiable** while the five-cap conclusion is
**unsatisfiable** (§2.2). For such `α`, `lem_layered_from_step7`
is a **false** proposition.

Two escape attempts, both refuted:

* *"Define `Step5R`/`Step5C` to be false for large `α`."* Then the
  bridge is vacuously true — but piece 1's `stepsOneToSevenCascade`
  (`MA-Sig §4.2 §D`), which must *produce* `Step5R ∨ Step5C` from
  Theorem E's low-conductance output, becomes unprovable. The block
  merely relocates to piece 1, and contradicts paper `thm:step5`.
* *"Use the `ih` to shrink `α`."* The bridge conclusion is one
  `LayeredDecomposition` on **all** of `{a // a ∉ Xexc}`, and
  `Xexc.card ≤ C_exc T` is bounded — there is no room to route the
  bulk of `α` through `ih`. The `ih` cannot weaken a `∃ L, …caps…`
  conclusion.

---

## §4. Root cause — `lem_layered_balanced` is the bounded base case

The five caps in the bridge conclusion are exactly the antecedents
of `lem_layered_balanced` (`MA-Sig §4.2 §G`, in tree at
`LayeredBalanced.lean:640`), which the refactored headline body
(`MA-Sig §4.3 §9`) applies to `{a // a ∉ Xexc}`:

```lean
have hBP_sub : HasBalancedPair {a : α // a ∉ Xexc} :=
  lem_layered_balanced L h2_sub hNonChain_sub hP_sub
    hInj hKw hCardw hNonempty hLw hC3
```

`lem_layered_balanced`'s antecedent `hCardw : Fintype.card β ≤
6 * L.w + 6` **already** bounds its domain to `|β| ≤ 30`
independently of the bridge. Its discharge `Case3Witness_proof`
(`OptionC/Case3WitnessProof.lean:256`) is a strong induction whose
`Case3Witness` hypothesis (`LayeredBalanced.lean:461-472`) carries
the same five caps. The in-tree docstring is explicit
(`LayeredBalanced.lean:447-450`):

> *"Under cap 5 the existing caps become honest finite-domain
> restrictions (`|β| ≤ 30`, `K ≤ 10`, `w ∈ {1,2,3,4}`), so
> `Case3Witness` is a finitely-decidable claim over a bounded
> family."*

So `lem_layered_balanced` **is, by its own design and
documentation, the `|β| ≤ 30` / `K ≤ 10` bounded restriction of
Step 8 G4** — what `PROOF-STRUCTURE-ONBOARDING.md` §1 step 3 and
§3 pitfall #2 call the *"cap-1-cap-5 sub-slice"*, the
*"|α| ≤ 10 slice"*.

The full Step 8 G4 — paper `lem:layered-balanced`
(`step8.tex:3071-3124`), strong induction on `|β|`, consuming
`(β, L)` with **only** `L.w ≤ 4` (plus width-3, non-chain,
`2 ≤ |β|`), no caps 1/2/3 — is **not in the tree**.
`PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 says so verbatim:

> *"Step 8 = Lean port of `lem:layered-balanced` … taking
> `(α, L)` with only `L.w ≤ 4` … This IS the entire Step 8
> engineering target — NOT a narrow residual. … The current
> `Case3Witness_proof.{u}` is a restriction of this covering only
> the cap-1-cap-5 sub-slice."*

### §4.1. Where the MA-Sig contract erred

`MA-Sig §4.2 §G` pins `lem_layered_balanced` as
*"(UNCHANGED — LayeredBalanced.lean:626)"* and §4.2 §E pins the
bridge to emit its five caps. `MA-Sig §4.4` ("Why this types
cleanly — no 8th vacuity") checked, for the
`lem_layered_from_step7 → lem_layered_balanced` boundary, only
that *"5 caps match"* — i.e. **producer/consumer type
compatibility**. It did **not** run `PROOF-STRUCTURE-ONBOARDING.md`
§3 pitfall #2's mandated **check #1 — satisfiability under caps**:
*"Is X satisfiable at the headline's full |α| range under all the
caps you wrote down?"*

The MA-Sig pseudo-Lean was internally type-consistent and
therefore passed §4.4's type audit, but the shared five-cap shape
is unsatisfiable above `|α| = 10 + C_exc T`. This is the **8th
vacuity discovery**, after mg-e2e9, mg-74d2, mg-5c32, mg-82fc,
mg-2970, mg-ac13, mg-5fbd — and it is the *same* pitfall (#2) as
mg-5c32, recurring one architectural layer up.

---

## §5. The missing 6th piece — full Step 8 G4

The Option A' FULL REFACTOR (mg-d8c7) decomposes into 5 pieces:
1 = Steps 1-6 cascade; 2 = S7-A-E concretisation; 3 = S7-F bridge;
4 = MainAssembly proof-by-contradiction refactor; 5 = integration.
**None ports the full Step 8 G4.** mg-d8c7 §4.1 lists
`LayeredBalanced.lean … lem_layered_balanced … Consumed by piece 4`
under *"§4.1 Already-in-tree (✓ usable)"*.

Per §4 above it is **not usable as the Step-8 endpoint**. A faithful
refactor needs a **piece 6**:

> **Piece 6 — full Step 8 G4 (`lem:layered-balanced`).** Lean port
> of `step8.tex:3071-3124`: for every finite width-3 non-chain
> poset `β` with `2 ≤ |β|` and a `LayeredDecomposition L` with
> `L.w ≤ 4`, `HasBalancedPair β`. Strong induction on `|β|`; the
> existing `Case3Witness_proof` is the `|β| ≤ 10` base sub-slice.
> The inductive step is the paper's ordinal-cut / window-
> localisation argument (`lem:cut`, `lem:window-localization`,
> `lem:layered-reduction` — in tree as `lem_cut`,
> `windowLocalization`, `lem_layered_reduction`, currently **NC**
> "not consumed", per `PROOF-STRUCTURE-ONBOARDING.md` §2). These
> NC lemmas are exactly the missing inductive machinery: piece 6
> is largely *wiring already-built infrastructure into the
> headline path*, plus the FKG / second-moment leaf.

Piece 6 is a non-trivial sub-arc but its proof technique is known
(paper-proved; `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2:
*"the in-tree gap is engineering, not math"*). Rough estimate by
analogy with the mg-d8c7 piece budgets: **3-6 polecat sessions /
0.8M-1.6M tokens** (it consumes `lem_cut` + `windowLocalization`
+ `lem_layered_reduction`, which are already substantive Lean, and
re-targets them from the abandoned size-minimal framing onto the
strong-induction headline path).

---

## §6. The bridge itself is fine — only the signature is wrong

To be precise about what is and is not broken: the **paper**
`lem:layered-from-step7` is sound, and a faithful Lean port of it
is feasible. What is broken is the **MA-Sig pinned conclusion
shape**. A paper-faithful bridge produces a `LayeredDecomposition`
with:

* bands of size `≤ 3` (the `band_size` field — automatic, **not**
  singletons; `L.band` is **not** injective in general);
* depth `L.K = Θ(|X ∖ X^exc|)` (roughly `|X∖X^exc| / 3`);
* interaction width `L.w ≤ 4`;
* `|X^exc| ≤ C_exc T`.

That object satisfies cap 5 (`L.w ≤ 4`) and cap 4 (nonempty bands,
after `compactify`), but **violates caps 1, 2, 3** for large `α`
— correctly, because caps 1/2/3 are `Case3Witness` API artefacts,
not properties of a paper layered decomposition. This is the
`def:layered` object (`step8.tex:1883-1907`), faithfully.

So the bridge is buildable; it just must not be asked to emit
caps 1/2/3, and its consumer must be piece 6 (full Step 8 G4),
not the bounded `lem_layered_balanced`.

---

## §7. Corrected architecture (recommendation)

Two coupled corrections; both are **re-scoping decisions** above a
polecat's authority, hence block-and-report rather than unilateral
implementation.

### §7.1. Corrected bridge signature

```lean
theorem lem_layered_from_step7
    (γ : ℚ) (hγ_pos : 0 < γ) (T : ℕ)
    (hP : HasWidthAtMost α 3) (hI : Indecomposable α)
    (hCascade : Step5R α γ T ∨ Step5C α T)
    (ih : ∀ m, m < Fintype.card α → …) :
    ∃ (Xexc : Finset α) (L : LayeredDecomposition {a : α // a ∉ Xexc}),
      Xexc.card ≤ C_exc T ∧
      (∀ k, 1 ≤ k → k ≤ L.K → (L.bandSet k).Nonempty) ∧  -- cap 4 (kept; natural)
      L.w ≤ 4                                            -- cap 5 (kept; the real one)
      -- caps 1, 2, 3 DROPPED: they are Case3Witness API
      -- artefacts, false for |X∖X^exc| > 10.
```

### §7.2. Add piece 6 to mg-d8c7

The corrected bridge feeds **piece 6** (full Step 8 G4, §5), not
`lem_layered_balanced`. `MA-Sig §4.2 §G` and `§4.3 §9` must be
re-pinned to the piece-6 signature:

```lean
theorem lem_layered_balanced_full      -- piece 6 deliverable
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :                  -- ONLY cap 5
    HasBalancedPair β
```

The existing `lem_layered_balanced` / `Case3Witness_proof` become
the `|β| ≤ 10` base case *inside* `lem_layered_balanced_full`'s
strong induction.

### §7.3. Downstream signature drift

Per `MA-Sig §8` maintenance contract, the consumer-side signature
in `MA-Sig §4.2 §E/§G` and `§4.3 §8-§9` must be updated. The
`hC3 : Case3Witness` parameter threading is replaced by the
piece-6 strong induction (no separate witness object needed once
G4 is full). `state-MA-Sig-Session1.md` §9 records this drift
(added this session).

---

## §8. Forward options for Daniel / pm-onethird

Adapting mg-5fbd §6.1 to the post-MA-Sig state:

**Option (R1): RE-SCOPE then resume (recommended).** A short
scoping session re-pins `MA-Sig §4.2` per §7, adds piece 6 to
mg-d8c7, and re-issues P3 (corrected bridge) + P6 (full Step 8 G4)
as buildable tickets. Cost: ~250-400k tokens / 1 session, then the
revised execution arc. This keeps the FULL REFACTOR on its honest
track; the §7 corrections are mechanical once accepted.

**Option (R2): build piece 6 first, then P3.** Piece 6 (full
Step 8 G4) has no upstream dependency on the cascade — it consumes
only a `LayeredDecomposition` with `L.w ≤ 4`, and the inductive
infrastructure (`lem_cut`, `windowLocalization`,
`lem_layered_reduction`) is already in tree. It could be dispatched
**immediately**, in parallel with piece 1, ahead of P3. P3 (the
corrected §7.1 bridge) then has a real consumer. This is the
lowest-idle-time ordering.

**Option (C''): status-quo (retain the `MainAssembly.lean:265`
sorry).** As mg-5fbd §6.1 Option (C'). The FULL REFACTOR pauses;
the headline keeps its documented architectural-debt sorry. Only
if Daniel deprioritises the refactor.

**Recommendation: (R1) then (R2) ordering** — re-scope, then
dispatch piece 6 early. Do **not** dispatch P3 or P4 against the
current pinned signature; both would build on the unsatisfiable
five-cap shape.

---

## §9. Verification log

Every claim above was checked against `origin/main` (`369a0a0`)
source, not inferred from docs:

* `LayeredDecomposition` fields `band_pos`, `band_le` —
  `LayeredReduction.lean:124-126`. → §2.1.
* `LayeredDecomposition.bandSet`, `mem_bandSet` —
  `LayeredReduction.lean:156-161`. → §2.1.
* `Case3Witness` five-cap definition —
  `LayeredBalanced.lean:461-472`. → §2, §4.
* `Case3Witness` docstring "`|β| ≤ 30`, `K ≤ 10`" —
  `LayeredBalanced.lean:447-450`. → §4.
* `lem_layered_balanced` antecedents `hKw`/`hCardw`/`hLw` —
  `LayeredBalanced.lean:647-650`. → §4.
* MA-Sig pinned bridge signature — `state-MA-Sig-Session1.md`
  §4.2 §E (lines 414-436). → §0, §2.
* MA-Sig `lem_layered_balanced` pinned "UNCHANGED" —
  `state-MA-Sig-Session1.md` §4.2 §G (lines 449-465). → §4.1.
* MA-Sig §4.4 type-only audit — `state-MA-Sig-Session1.md`
  lines 556-571 (checks "5 caps match", not satisfiability).
  → §4.1.
* `Step5R`/`Step5C`/`C_exc` are P1-owned, `C_exc : ℕ → ℕ` a
  function of `T` only — `state-MA-Sig-Session1.md` §4.1
  (lines 352-380). → §2.2, §3.
* `PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2.1 (caps 1+4+2+5
  unsatisfiable) and "right framing" (full Step 8 = only
  `L.w ≤ 4`) — `PROOF-STRUCTURE-ONBOARDING.md:254-298`.
  → §2.2, §4, §5.
* `lem_cut` / `windowLocalization` / `lem_layered_reduction`
  tagged **NC** "not consumed" —
  `PROOF-STRUCTURE-ONBOARDING.md:170`. → §5.

**The §2 unsatisfiability is a theorem of finite combinatorics**
(injection + surjection into `Icc 1 K`), independent of any
unbuilt P1/P2 deliverable. It does not depend on how `Step5R`,
`Step5C`, or `C_exc` are eventually defined — only on `C_exc`
being a function of `T` (so a constant for fixed `T`), which the
MA-Sig contract and the paper (`|X^exc| = O_T(1)`) both fix.

---

## §10. Cross-references

* `lean/OneThird/Step8/LayeredReduction.lean:115-161` —
  `LayeredDecomposition` structure + `bandSet`.
* `lean/OneThird/Step8/LayeredBalanced.lean:447-472` —
  `Case3Witness` definition + the "`|β| ≤ 30`" docstring.
* `lean/OneThird/Step8/LayeredBalanced.lean:640-651` —
  `lem_layered_balanced` signature (five cap antecedents).
* `lean/OneThird/Step8/MainAssembly.lean:236-267` —
  `caseC_canonicalLayered` (the `sorry` piece 3+4 was to close).
* `lean/OneThird/Step8/LayeredBridges.lean` — `layeredFromBridges`
  (the current sham-bandwidth placeholder; would have been
  replaced by the §7.1 corrected bridge).
* `docs/state-MA-Sig-Session1.md` §4.2 §E/§G, §4.4, §8 — the
  pinned signature contract + its type-only audit + its
  maintenance contract.
* `docs/state-S7-F-bridge-Session1.md` (mg-5fbd) — the 7th
  vacuity discovery; §2.3's 3-disjoint-chains-of-3 counterexample,
  whose mechanism §2 generalises.
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` (mg-d8c7)
  §2.3 (piece 3 scope), §4.1 (`lem_layered_balanced` listed as
  "already-in-tree, usable" — the error).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 (the
  recurring pitfall) + §3 pitfall #6 (added this session).
* `paper/step8.tex:1983-2106` — `lem:layered-from-step7`.
* `paper/step8.tex:3071-3124` — paper `lem:layered-balanced`
  (the full Step 8 G4, piece 6's port target).

---

## §11. Maintenance contract notes

Per `PROOF-STRUCTURE-ONBOARDING.md` §5, this session's landing
warrants, in the same commit:

* **Add pitfall #6** to `PROOF-STRUCTURE-ONBOARDING.md` §3 — the
  MA-Sig five-cap bridge-signature defect + the missing piece 6.
* Update §1 TL;DR bullet on the S7-F bridge to point at this
  Session 2 finding.
* Add this doc to the §4 predecessor index.
* Update `docs/state-MA-Sig-Session1.md` §9 (new) recording the
  8th vacuity discovery and the §7 re-pin.
* Flag `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §0 with a
  pointer to this finding (5 pieces → 6).
* No `AXIOMS.md` changes (no axioms added or removed).
* No Lean changes (doc-only RED session — mg-5fbd Session 1
  precedent).
