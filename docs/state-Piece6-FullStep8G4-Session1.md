# Piece 6 — full Step 8 G4 (`lem_layered_balanced_full`) — Session 1: RED, base-case coverage gap (mg-fdc2)

**Ticket:** mg-fdc2 (OneThird-Piece6-FullStep8G4: full Step 8 G4
Lean port — `lem:layered-balanced` by strong induction, `L.w ≤ 4`
only).
**Predecessors:** mg-faf8 (MA-Sig re-pin + Piece 6 recorded,
`docs/state-MA-Sig-Session1.md` §10 / `…-scoping.md` §2.6),
mg-0bd1 (S7-F bridge Session 2, RED 8th vacuity), mg-d8c7 (Option A'
FULL REFACTOR scoping).
**Verdict:** **RED — the obligation is not buildable as scoped.**
Piece 6 (`lem_layered_balanced_full`) is a *true* proposition, but
the routing the ticket pins — "`Case3Witness_proof` becomes the base
case; the inductive step wires `lem_cut`, `windowLocalization`,
`lem_layered_reduction`" — **cannot be discharged with the current
in-tree infrastructure** without (a) substantial new formalization
(a non-singleton-band irreducible base case + the genuine
window-localization marginal-invariance lift) or (b) a new project
axiom. Both are re-scoping decisions above a polecat's authority.
This is the **scoping doc §2.6 risk 1 / Checkpoint 6 gate firing** —
explicitly anticipated as "the one place Piece 6 could surface a
9th vacuity".

This session produced **no Lean changes**. The deliverable is this
audit document plus the maintenance-contract updates to
`PROOF-STRUCTURE-ONBOARDING.md` (§1 TL;DR + §3 pitfall #7 + §4
index) and `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6 (risk 1
marked materialised). Mirrors the mg-5fbd / mg-0bd1 doc-only RED
pattern.

---

## §0. Verdict — **RED-base-case-not-buildable**

`lem_layered_balanced_full` (MA-Sig §4.2 §G) — the full Step 8 G4 —
is the proposition

```lean
theorem lem_layered_balanced_full.{u}
    {β : Type u} [PartialOrder β] [Fintype β] [DecidableEq β]
    (L : LayeredDecomposition β)
    (h2 : 2 ≤ Fintype.card β)
    (hNotChain : ¬ IsChainPoset β)
    (hW3 : HasWidthAtMost β 3)
    (hLw : L.w ≤ 4) :          -- ONLY the interaction-width cap
    HasBalancedPair β
```

It is a faithful transcription of paper `lem:layered-balanced`
(`step8.tex:2453-2464` / proof `3211-3266`), a sound theorem
(mg-faf8 satisfiability-verified it, `state-MA-Sig-Session1.md`
§10.6). **The proposition is not the problem.** The problem is the
**proof routing** the ticket pins.

The ticket scopes Piece 6 as:

> "The in-tree `Case3Witness_proof` (the bounded base sub-slice,
> beta cardinality at most 10) becomes the base case; the inductive
> step wires the in-tree but currently-unused lemmas `lem_cut`,
> `windowLocalization`, and `lem_layered_reduction`."

Both halves of that routing are unbuildable:

1. **`Case3Witness_proof` cannot serve as the base case.** It
   requires `Function.Injective LB.band` (cap 1 of `Case3Witness`,
   `LayeredBalanced.lean:461-472`) as a *load-bearing* hypothesis —
   it is used in **every** branch of its strong induction (§3.1).
   The re-pinned Piece 6 signature **deliberately drops band
   injectivity** (mg-faf8: caps 1/2/3 dropped from the bridge
   because the paper `def:layered` object has bands of size `≤ 3`,
   *not* singletons — `state-MA-Sig-Session1.md` §10.3). So the
   `L` that `lem_layered_balanced_full` receives is, by contract,
   **not** band-injective, and `Case3Witness_proof` does not apply
   to it (§3.2).

2. **`windowLocalization` and `lem_layered_reduction` are vacuous
   placeholders.** `windowLocalization` (`LayeredBalanced.lean:103`)
   proves `∃ q, probLT x y = q ∧ W.card ≤ 3(3w+1)` by taking
   `q := probLT x y` — it carries the window *size bound* and
   **nothing of the marginal-invariance content**. `lem_layered_-
   reduction` (`LayeredReduction.lean:491`) is literally
   `W.conclusion` where `W : ReductionWitness` *carries the
   conclusion as an input field* (`LayeredReduction.lean:455-465`).
   "Wiring" these two produces exactly the **vacuous routing** the
   ticket says to refuse (§4).

3. **The genuine inductive-step + base-case content is not in
   tree.** The honest proof needs (i) a real window-localization
   marginal-invariance lift `HasBalancedPair ↥W → HasBalancedPair β`
   and (ii) a discharge of irreducible, width-3, non-chain bounded
   posets with a **non-singleton-band** layered decomposition. (ii)
   has **no in-tree route at all**: the only in-tree discharge for
   irreducible posets, `bounded_irreducible_balanced_hybrid`, needs
   a `Case2Witness L → HasBalancedPair β` discharge on its
   out-of-scope branch, available only via band injectivity or via
   the **provably-false** `Case2FKGSubClaim` (§3.3).

Acceptance bar against the ticket body:

| Bar | Status |
|---|---|
| Port `lem_layered_balanced_full` (strong induction on `\|β\|`) | **Blocked** — base case not buildable as scoped (§3) |
| `Case3Witness_proof` becomes the base case | **Impossible** — it requires band injectivity that Piece 6's input `L` does not carry (§3.1-§3.2) |
| Inductive step wires `lem_cut` / `windowLocalization` / `lem_layered_reduction` | **`lem_cut` is substantive; the other two are vacuous placeholders** — wiring them = vacuous routing (§4) |
| Non-triviality: hold for unbounded `\|β\|`, beyond `\|β\| ≤ 10` | The inductive step would close Case A + Case B genuinely (§5), but the irreducible base case (Case C2) blocks closure for **all** `\|β\|`, bounded or not (§3.3) |
| Block-and-report on ill-posed obligation rather than vacuous routing | **Invoked.** This document is the block-and-report. |

---

## §1. Context — what Piece 6 was asked to do

Piece 6 of the Option A' FULL REFACTOR was **added by mg-faf8** as
the fix for the mg-0bd1 8th vacuity discovery: the S7-F bridge
(Piece 3) was re-pinned to emit a `LayeredDecomposition` carrying
only `L.w ≤ 4` (plus `Xexc.card ≤ C_exc T` and band-nonempty), and
its consumer became Piece 6 — the **full** Step 8 G4 — instead of
the bounded `lem_layered_balanced` (`state-MA-Sig-Session1.md`
§4.2 §E/§G, §9).

The paper proof of `lem:layered-balanced` (`step8.tex:3211-3266`)
is a strong induction on `|β|` with the case structure
(`OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6):

* **base `|β| = 2`** — non-chain ⇒ incomparable pair, `Pr = 1/2`;
* **Case A (`K = 1`)** — single antichain, every pair `Pr = 1/2`;
* **Case B (layer-ordinal-reducible)** — `β = β₁ ⊕ β₂`; recurse on
  the non-chain factor, lift via marginal invariance;
* **Case C (irreducible, `K ≥ 2`)** — window-localise to
  `W = W(i,j)`; sub-case **C1** (`W ⊊ β`) recurses on `P|_W`;
  sub-case **C2** (`W = β`) is the bounded base case
  (`|β| ≤ 3(3w+1) ≤ 39`), discharged by `prop:in-situ-balanced`.

mg-faf8 §10.6 already flagged the load-bearing caveat verbatim:

> "the C2 bounded base must cover *all* width-3 non-chain posets
> with `|β| ≤ 3(3w+1)`, whereas the in-tree `Case3Witness_proof`
> covers only the singleton-band (cap-1) sub-slice of that range.
> Piece 6's base case must therefore extend coverage to
> non-singleton-band bounded posets — via the mg-be48 cap-light
> enumeration extension or a direct `prop:in-situ-balanced` port."

The scoping doc §2.6 records this as **risk 1** (base-case coverage
gap, ~35% probability of needing its own sub-arc, +300k-600k) and
§3.4 **Checkpoint 6** as the gate "before coding mg-G4-D … the one
place Piece 6 could surface a 9th vacuity". The mg-fdc2 ticket
itself instructs: "Block-and-report on any ill-posed obligation
rather than shipping a vacuous routing."

This session is that Checkpoint 6 gate firing **before** any Lean
is written. Risk 1 has materialised — and it is worse than the
scoping estimate: it is not a "needs its own sub-arc" cost overrun,
it is a **hard blocker** with no in-tree route (§3.3).

---

## §2. The proof obligation, decomposed

`lem_layered_balanced_full` would be proven via the in-tree
strong-induction skeleton
`hasBalancedPair_of_layered_strongInduction_width3`
(`LayerOrdinal.lean:472`), which is genuine and reusable. It hands
the proof body (`hStep`) an induction hypothesis

```
ih : ∀ β [..] (LB : LayeredDecomposition β),
       Fintype.card β < Fintype.card α →
       HasWidthAtMost β 3 → 2 ≤ Fintype.card β →
       ¬ IsChainPoset β → HasBalancedPair β
```

The `hStep` body must then dispatch on `L.K` and reducibility.
Per-case buildability against the **current** tree:

| Case | In-tree machinery | Buildable? |
|---|---|---|
| `K = 1` | `bipartite_balanced_enum` (single antichain, `≤ 3` elts) | **Yes** — genuine, no injectivity (§5) |
| `K ≥ 2` reducible | `OrdinalDecompOfReducible` (`LayerOrdinal.lean:108`) + `OrdinalDecomp.hasBalancedPair_lift_lower/upper` (`Subtype.lean:1227/1237`); recurse via `ih` on `L.restrict D.Lower/Upper` | **Yes** — genuine, no injectivity (§5) |
| `K ≥ 2` irreducible, **C1** (`W ⊊ β`) | `lem_cut` (substantive) gives the cut; **but no in-tree lift** `HasBalancedPair ↥W → HasBalancedPair β` (§4.1) | **No** — needs the genuine window marginal-invariance lift |
| `K ≥ 2` irreducible, **C2** (`W = β`) | `bounded_irreducible_balanced_hybrid` — but its out-of-scope branch needs a Case 2 discharge unavailable for non-injective `L` (§3.3) | **No** — hard blocker |

The two "No" rows are the obstruction. C2 (the base case) is the
**hard** blocker — it has no in-tree route at all. C1 is a
"substantial new formalization" blocker. Either alone prevents
closure; together they sink the scoped routing.

---

## §3. The blocker — the irreducible base case for non-injective `L`

### §3.1. `Case3Witness_proof` requires band injectivity in every branch

`Case3Witness_proof.{u}` (`OptionC/Case3WitnessProof.lean:256`)
discharges `Case3Witness.{u}` (`LayeredBalanced.lean:461-472`),
whose **cap 1** is `Function.Injective LB.band`. Injectivity is not
decorative — it is consumed in **every** branch of the strong
induction:

* **`K = 1`** — `absurd_K1_of_injective`
  (`Case3WitnessProof.lean:81`, used at `:297`): two distinct
  elements both land in band 1; injectivity gives the
  contradiction.
* **`K = 2` reducible** — `isChain_of_K2_reducible_under_injective`
  (`:106`, used at `:306`): injectivity + nonempty bands ⇒ each
  band a singleton ⇒ `β` is a 2-element chain.
* **`K ≥ 3` reducible** — the `compactify` descent
  (`:383-384`, `:467-469`) propagates cap 1 via
  `compactify_band_injective_of_injective`; the IH call
  (`:435`, `:514`) **requires** `hInj'` as an argument.
* **`K ≥ 3` irreducible** — the out-of-scope `hStruct` branch
  (`:541-544`) supplies the Case 2 discharge as
  `case2_discharge_of_injective hInj` (`:147`): `Case2Witness LB`
  posits two distinct elements with **equal band**, and
  injectivity collapses that to `a = a'`, contradiction.

There is no branch of `Case3Witness_proof` that does not use cap 1.
It is not a strong induction "with injectivity threaded for
convenience"; it is a strong induction **about singleton-band
posets**.

### §3.2. Piece 6's input `L` is, by contract, not band-injective

`lem_layered_balanced_full` takes `L : LayeredDecomposition β` with
**only** `hLw : L.w ≤ 4`. The caller chooses `L`. Its actual
caller is the re-pinned S7-F bridge (Piece 3), whose output is —
verbatim from `state-MA-Sig-Session1.md` §10.3 — the paper
`def:layered` object with

> "bands of size `≤ 3` — *not* singletons — and depth
> `K ≥ (|X| − |X^exc|)/3 ≥ |X|/6`".

mg-faf8 **dropped cap 1 (band injectivity) from the bridge on
purpose**: caps 1+2 jointly forced `|α| ≤ 10 + C_exc T`, the
mg-0bd1 8th vacuity. Re-imposing injectivity inside Piece 6 — by
demanding it of the input `L`, or by rebuilding a singleton-band
`L'` — would simply **reinstate the mg-0bd1 defect one layer down**.

Can a non-singleton-band `L` always be *converted* to a
singleton-band `L'` with `L'.w ≤ 4`? **No.** Singleton bands force
`band` to be a linear extension whose every incomparable pair sits
within band-distance `w'`. Three disjoint chains of lengths
`(4,3,3)` (`|β| = 10`, width 3, non-chain) admit a non-singleton
layered decomposition with `w ≤ 4` (band by level: `K = 4`,
size-`≤ 3` bands, `w = 3`) but **no** singleton-band decomposition
with `w' ≤ 4` — the three chains' first/last elements are pairwise
cross-chain-incomparable and cannot all be packed within distance
`4` in a 10-element linear extension. So `Case3Witness_proof`'s
domain (singleton-band, hence `|β| = K ≤ 2w+2 ≤ 10`) is a *strict*
sub-slice of "width-3 non-chain `|β| ≤ 10`", and Piece 6 must cover
the complement.

**Conclusion.** "`Case3Witness_proof` becomes the base case" is an
ill-posed instruction: the base case it discharges and the base
case Piece 6 reaches are different sets of posets, and the
recursion (which only ever shrinks `|β|` and restricts `L`, never
manufactures injectivity) cannot bridge them.

### §3.3. The non-singleton-band irreducible base case has no in-tree discharge

The base case Piece 6 actually needs (Case C2): **irreducible,
width-3, non-chain, `|β|` bounded, layered with `w ≤ 4`, bands of
size `≤ 3` (not singletons)**. The only in-tree discharge of an
irreducible poset is `bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1681`), a pure `by_cases` on
`InCase3Scope` (`BoundedIrreducibleBalanced.lean:1498`):

```
InCase3Scope w card K :=
  (K = 3 ∧ 1 ≤ w ≤ 4 ∧ size caps) ∨ (K = 4 ∧ w = 1 ∧ card ≤ 8)
```

* **In-scope branch** (`hCert`) — discharged by `case3_certificate`
  (`native_decide`) via `bounded_irreducible_balanced_inScope`.
  This **does** cover non-singleton bands (it enumerates
  `bandSizesGen`). Likewise `option_c_K2_closure`
  (`OptionC/K2Closure.lean:500`) covers all `K = 2`, `|β| ≤ 6`
  non-singleton-band cells. So part of the base case is fine.
* **Out-of-scope branch** (`hStruct`) — for the `¬ InCase3Scope`
  cells (`K = 3` with `card` over cap; `K = 4, w ≥ 2`; `K ≥ 5`;
  all reachable within `w ≤ 4`, `K ≤ 2w+2`, `card ≤ 6w+6`), the
  composed dispatch `hStruct_of_case2_discharge`
  (`Case3Residual.lean:265`) splits into Case 1 (closed), Case 3
  (the `case3Witness_hasBalancedPair_outOfScope` axiom — existing),
  and **Case 2**, which it consumes as a hypothesis
  `case2Discharge : Case2Witness L → HasBalancedPair β`.

`Case3Witness_proof` fills that `case2Discharge` slot with
`case2_discharge_of_injective hInj` — i.e. **it makes Case 2
vacuous using band injectivity**. For a non-injective `L`,
`Case2Witness L` (`Case3Dispatch.lean:156`: two distinct
same-band elements with nested two-sided profiles) is **not**
vacuous, and there is **no in-tree theorem** discharging it:

* `case2Witness_balanced_under_FKG` (`Case2Rotation.lean:894`)
  proves `Case2Witness L → HasBalancedPair β` — but **only** under
  the extra hypothesis `hFKG : Case2FKGSubClaim L`
  (`Case2Rotation.lean:772`).
* `Case2FKGSubClaim L` is **provably false** — stated verbatim in
  `OptionC/K2Closure.lean:21` ("**bypassing the provably-false
  `Case2FKGSubClaim`**", per `docs/path-c-cleanup-roadmap.md` §6b).
  Its own docstring (`Case2Rotation.lean:760-771`) labels it "a
  hypothesis … not a theorem", with the FKG infrastructure that
  *would* prove it listed as **future work**
  (`Mathlib/RelationPoset/FKG.lean §11`).

So `case2Witness_balanced_under_FKG` is, at every genuine call
site, **inapplicable** (its hypothesis is unsatisfiable). There is
**no in-tree route from `Case2Witness L` to `HasBalancedPair β`
for non-injective `L`.** The out-of-scope irreducible base case is
a genuine open gap.

This is the hard blocker. It is present even within the `|β| ≤ 10`
slice: e.g. `K = 4, w = 1, |β| = 9` or `10` is `¬ InCase3Scope`
(K=4 needs `card ≤ 8`), irreducible, non-singleton-band cells with
no discharge.

---

## §4. Secondary finding — two of the three "wiring" lemmas are vacuous placeholders

The ticket says the inductive step "wires the in-tree but
currently-unused lemmas `lem_cut`, `windowLocalization`, and
`lem_layered_reduction`". Audited:

### §4.1. `windowLocalization` carries no marginal-invariance content

`windowLocalization` (`LayeredBalanced.lean:103-172`) concludes

```lean
∃ q : ℚ, probLT x y = q ∧ W.card ≤ 3 * (3 * L.w + 1)
```

and is proven by `refine ⟨probLT x y, rfl, ?_⟩` — the witness `q`
is `probLT x y` itself, so the first conjunct is `rfl`. The lemma
delivers **only** the window *size* bound `|W| ≤ 3(3w+1)`. Its own
docstring concedes it: "the probability invariance is reflected
here trivially (by taking `q := probLT x y`)".

The genuine Case C1 step needs `probLT x y` in `β` to *equal* the
marginal in `P|_W` — the ordinal-sum factorisation
`LinearExt β ≃ LinearExt X⁻ × LinearExt W × LinearExt X⁺`
(`step8.tex:2541-2569`). `windowLocalization` does not provide it;
nothing in tree does, in the window-localization shape. The
related genuine lift, `OrdinalDecomp.hasBalancedPair_lift`
(`Subtype.lean:1152`), requires a constructed `OrdinalDecomp β`
with `Mid = W`. The window of half-width `w` does **not**
ordinal-decompose `β`: for `z` just below the window and `ω ∈ W`,
`forced_lt` needs `band z + w < band ω`, but the window's lower
edge only guarantees `band ω ≥ minB − w`, giving `band z + w <
minB ≤ band ω + w` — i.e. `band z < band ω`, *not*
`band z + w < band ω`. A correct ordinal decomposition needs a
window padded to half-width `2w` (then `|W| ≤ 3(5w+1) ≤ 63`), and
that construction — plus its `OrdinalDecomp` packaging and the
recursion-termination bookkeeping — is **new formalization**, not
"wiring".

### §4.2. `lem_layered_reduction` is a conclusion-carrying shell

`lem_layered_reduction` (`LayeredReduction.lean:491-495`) is

```lean
theorem lem_layered_reduction (L) (balanced : Prop)
    (W : ReductionWitness L balanced) :
    LayeredReductionConclusion balanced := W.conclusion
```

where `LayeredReductionConclusion balanced := balanced`
(`:435`) and `ReductionWitness` (`:455-465`) carries
`conclusion : balanced` **as an input field**. So
`lem_layered_reduction` returns its own input. It is a typed
packaging of "size-minimal reductio", with the entire mathematical
content (the cut + bulk/window lift) deferred to whoever supplies
`ReductionWitness.conclusion`. Wiring it into Piece 6 routes the
obligation in a circle — exactly the "vacuous routing" the ticket
forbids.

### §4.3. Only `lem_cut` is substantive

`lem_cut` (`LayeredReduction.lean:373`) genuinely produces the cut
data `LayeredCut L` with the structural cross-pair conclusion
`∀ a ∈ A, ∀ b ∈ B, a < b ∨ (a ∈ W ∧ b ∈ W)`. It is real and
reusable — but it is one substantive lemma, not "the inductive
machinery". It delivers a 2-way *almost-ordinal* cut; converting
that into the 3-way `OrdinalDecomp` with `Mid` the window (needed
for the §4.1 lift) is the missing step.

**Net.** The ticket's premise — "Piece 6 is largely wiring
already-built infrastructure" (scoping §2.6) — holds for `lem_cut`
and for the reducible-case lift, but **not** for the
window-localization inductive step nor the base case. Two of the
three named lemmas are placeholders.

---

## §5. What *would* close — Case A and Case B are genuinely buildable

To be precise about the boundary between buildable and blocked
(and to scope the eventual fix), the following **are** honestly
buildable today, no injectivity, no new axiom:

* **Case A (`K = 1`).** `K = 1` + `band_pos`/`band_le` ⇒ every
  element in band 1 ⇒ `univ` is a `band_antichain` of size `≤ 3`
  ⇒ `bipartite_balanced_enum univ ∅ …`. This is exactly the
  existing `K = 1` branch of `lem_layered_balanced`
  (`LayeredBalanced.lean:666-699`) — it never touches `hInj`.

* **Case B (`K ≥ 2` reducible).** From
  `LayerOrdinalReducible L k`, `OrdinalDecompOfReducible L k h`
  gives an `OrdinalDecomp β` with `Mid = ∅`. The incomparable
  pair lands wholly in `Lower` or wholly in `Upper` (a cross-pair
  is `<`-forced by reducibility). Recurse via the strong-induction
  `ih` on `L.restrict D.Lower` / `L.restrict D.Upper` (plain
  `restrict`, `LayeredReduction.lean:203`, preserves `w`; no
  `compactify`, so no injectivity needed), then lift via
  `D.hasBalancedPair_lift_lower` / `_upper`
  (`Subtype.lean:1227/1237`). This is the
  `Case3WitnessProof.lean:310-516` reducible branch with
  `compactify`→`restrict` and the cap bookkeeping deleted.

So a genuine Piece 6 would close `K = 1` and the reducible case
outright, and would recurse correctly through them for **unbounded
`|β|`**. The recursion bottoms out at irreducible posets — and
**there** (Case C) it stalls: C1 needs the §4.1 lift, C2 needs the
§3.3 base case. The non-triviality bar ("hold for unbounded `|β|`")
is therefore *not* met: every recursion branch eventually reaches an
irreducible leaf, and no irreducible leaf closes.

---

## §6. Why this is not "just hard" — the obligation is ill-posed *as scoped*

The ticket distinguishes "ill-posed obligation" from "hard work".
The distinction here:

* The **proposition** `lem_layered_balanced_full` is well-posed and
  true (mg-faf8 §10.6).
* The **scoped routing** is ill-posed: it names `Case3Witness_proof`
  as the base case (a theorem about a strictly smaller class —
  §3.1-§3.2) and names two vacuous placeholders as the inductive
  machinery (§4.1-§4.2). Following the routing literally yields
  either a type error (`Case3Witness_proof` wants `hInj` that does
  not exist) or a vacuous term (`lem_layered_reduction` returning
  its input).

Closing Piece 6 *honestly* requires content that is **new**, not
**wired**:

1. The genuine window-localization marginal-invariance lift
   (`OrdinalDecomp` with `Mid` = a `2w`-padded window + the
   `tripleEquiv` factorisation) — substantial but technique-known.
2. A discharge of irreducible width-3 non-chain **non-singleton-band**
   bounded posets — i.e. either
   * a Lean port of `prop:in-situ-balanced` Case 2 for non-injective
     `L` (the genuine FKG / Ahlswede-Daykin coupling — the
     `Case2FKGSubClaim` that is *currently provably false* must be
     replaced by a correct, narrower FKG statement, which is
     itself listed as future work in
     `Mathlib/RelationPoset/FKG.lean §11`); **or**
   * a new project axiom transcribing it (the
     `case3Witness_hasBalancedPair_outOfScope` pattern, extended to
     drop the implicit injectivity).

Item 2 is a re-scoping decision: mg-faf8 §10.6 explicitly said the
base case is "a Piece 6 scope item, **not** papered over". Choosing
the axiom route papers it over; choosing the formalization route is
its own multi-session sub-arc (the FKG infrastructure alone). Per
the FULL REFACTOR's standing rule ("if execution surfaces a gap,
**stop and re-scope**" — `state-MA-Sig-Session1.md` §8), this is
block-and-report territory, not unilateral-implementation territory.

This is the **9th gap discovery** of the OneThird arc (after
mg-e2e9, mg-74d2, mg-5c32, mg-82fc, mg-2970, mg-ac13, mg-5fbd,
mg-0bd1). It differs in kind from the 8th: mg-0bd1 was a *false
signature* (a type-clean but unsatisfiable proposition). This one
is a *true* proposition with an *unbuildable scoped routing* — a
buildability gap, not a falsity. But the lesson is the same:
mg-faf8's §2.6 "risk 1" was a known unknown, and Checkpoint 6
existed precisely to catch it before coding. The gate worked.

---

## §7. Forward options for Daniel / pm-onethird

Adapting mg-0bd1 §8 to the post-Checkpoint-6 state. **Do not
dispatch a Piece 6 coding ticket against the current scoped routing
— it is unbuildable.**

**Option (G1): split Piece 6, formalise the base case honestly
(highest fidelity, highest cost).** Re-scope Piece 6 into:
  * **mg-G4-A** — induction skeleton + Case A + Case B
    (genuinely buildable today, §5; ~1 session, 200k-350k).
  * **mg-G4-C1** — the padded-window `OrdinalDecomp` construction
    + marginal-invariance lift (replaces the vacuous
    `windowLocalization`; ~1-2 sessions, 300k-550k).
  * **mg-G4-C2-FKG** — the genuine non-singleton-band
    `prop:in-situ-balanced` Case 2 discharge: a correct narrower
    FKG sub-claim (replacing the provably-false `Case2FKGSubClaim`)
    + its discharge. **This is the load-bearing new math**; needs
    the `Mathlib/RelationPoset/FKG.lean §11` infrastructure. Hard
    to bound — 2-4 sessions, 0.5M-1.2M, with its own gap risk.
  Total Piece 6 revised: ~1.0M-2.1M (was 0.8M-1.6M). Drops no
  axioms beyond the existing `case3Witness_hasBalancedPair_-
  outOfScope`; adds none.

**Option (G2): formalise Case A/B/C1, axiomatise the C2 base case
(pragmatic, one disclosed axiom).** Build mg-G4-A + mg-G4-C1 as in
G1, but discharge the irreducible base case (Case C2) with a new
project axiom — `lem_layered_balanced_bounded_base` or similar:
"every irreducible width-3 non-chain poset with `|β| ≤ 3(5w+1)`
and a layered decomposition of width `w ≤ 4` has a balanced pair",
faithfully transcribing `prop:in-situ-balanced` (the same paper
result the existing `case3Witness_hasBalancedPair_outOfScope`
axiom already partially covers — this would be its
injectivity-free generalisation). Fully disclosed in `AXIOMS.md`.
Cost ~1.0M / 3-4 sessions. **Net axiom count: +1** (or +0 if the
new axiom subsumes and replaces `case3Witness_hasBalancedPair_-
outOfScope`). This contradicts mg-faf8 §10.6's "not papered over"
stance — needs Daniel's explicit sign-off.

**Option (G3): status-quo (recommended short-term).** Keep the
`MainAssembly.lean:265` cap-5 `sorry` and the existing bounded
`lem_layered_balanced`; do not build Piece 6 yet. The headline
`width3_one_third_two_thirds` is unchanged (still AMBER: one
`sorry`, one named axiom). The FULL REFACTOR pauses on the Piece 6
edge. Pieces 1 and 2 proceed unaffected (Piece 6 has no upstream
dependency, and equally nothing downstream depends on it until
Piece 4-Body — so its absence does not block Pieces 1/2/3).

**Recommendation: (G3) now, decide (G1) vs (G2) at a scoping
session.** The choice between G1 and G2 turns on whether the
project wants Piece 6 to *reduce* the axiom surface (G1, the FULL
REFACTOR's stated goal) or accepts a disclosed base-case axiom for
tractability (G2). That is a project-direction call. Either way the
current ticket (mg-fdc2) cannot be executed as written: its base
case is not in tree and two of its three named "wiring" lemmas are
vacuous.

---

## §8. Verification log

Every claim checked against the worktree source at the mg-fdc2
branch point (`a554cbb`), not inferred from docs:

* `Case3Witness` 5 caps incl. `Function.Injective LB.band` —
  `LayeredBalanced.lean:461-472`. → §3.1.
* `Case3Witness_proof` strong induction; injectivity in every
  branch — `OptionC/Case3WitnessProof.lean:256-547`; helpers
  `absurd_K1_of_injective:81`, `isChain_of_K2_reducible_under_-
  injective:106`, `case2_discharge_of_injective:147`;
  `compactify_band_injective_of_injective` at `:384/:468`;
  IH calls demanding `hInj'` at `:435/:514`. → §3.1.
* `bounded_irreducible_balanced_hybrid` is a pure
  `by_cases InCase3Scope` dispatch —
  `BoundedIrreducibleBalanced.lean:1681-1694`. → §3.3.
* `InCase3Scope` definition (`K=3` / `K=4,w=1` only) —
  `BoundedIrreducibleBalanced.lean:1498-1501`. → §3.3.
* `hStruct_of_case2_discharge` consumes
  `case2Discharge : Case2Witness L → HasBalancedPair α` as a
  hypothesis — `Case3Residual.lean:265-280`. → §3.3.
* `Case2Witness` = two distinct same-band elements with nested
  profiles — `Case3Dispatch.lean:156-158`. → §3.3.
* `case2Witness_balanced_under_FKG` requires
  `hFKG : Case2FKGSubClaim L` — `Case2Rotation.lean:894-900`.
  → §3.3.
* `Case2FKGSubClaim` is "a hypothesis … not a theorem", FKG
  infrastructure listed as future work —
  `Case2Rotation.lean:760-799`. → §3.3.
* `Case2FKGSubClaim` is **provably false** —
  `OptionC/K2Closure.lean:21` ("bypassing the provably-false
  `Case2FKGSubClaim`"). → §3.3.
* `windowLocalization` proven by `⟨probLT x y, rfl, …⟩`; carries
  only the size bound — `LayeredBalanced.lean:103-172`,
  docstring `:94-98`. → §4.1.
* `lem_layered_reduction := W.conclusion`;
  `ReductionWitness.conclusion : balanced` is an input field;
  `LayeredReductionConclusion balanced := balanced` —
  `LayeredReduction.lean:435/455-465/491-495`. → §4.2.
* `lem_cut` substantive cut data —
  `LayeredReduction.lean:373-413`. → §4.3.
* Strong-induction skeleton
  `hasBalancedPair_of_layered_strongInduction_width3` (IH does
  not thread `w ≤ 4`, so usable) — `LayerOrdinal.lean:472-510`.
  → §2, §5.
* `OrdinalDecompOfReducible` + `OrdinalDecomp.hasBalancedPair_-
  lift_lower/upper` exist and are genuine —
  `LayerOrdinal.lean:108`, `Subtype.lean:1152/1227/1237`. → §5.
* `restrict` preserves `w` (`w_restrict`) —
  `LayeredReduction.lean:203/279`. → §5.
* Bridge output is non-singleton (`bands of size ≤ 3 … not
  singletons`, `K = Θ(|α|)`) — `state-MA-Sig-Session1.md`
  §10.3. → §3.2.
* mg-faf8 §10.6 base-case caveat ("not papered over") —
  `state-MA-Sig-Session1.md` §10.6. → §1, §6.
* §2.6 risk 1 + §3.4 Checkpoint 6 —
  `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6, §3.4. → §1.
* Only `sorry` in `Step8/` is `MainAssembly.lean:265` (the cap-5
  sorry) — `grep -rn sorry`. No `sorry`/axiom added by this
  session.

**The §3 obstruction is structural**, independent of any unbuilt
P1/P2/P3 deliverable: it is a fact about which in-tree theorems
exist and which hypotheses they consume. It does not depend on how
`Step5R`/`Step5C`/`C_exc` are eventually defined.

---

## §9. Cross-references

* `lean/OneThird/Step8/LayeredBalanced.lean:103` (`windowLocalization`),
  `:461` (`Case3Witness`), `:640` (bounded `lem_layered_balanced`).
* `lean/OneThird/Step8/LayeredReduction.lean:373` (`lem_cut`),
  `:435/:455/:491` (`LayeredReductionConclusion` / `ReductionWitness`
  / `lem_layered_reduction`).
* `lean/OneThird/Step8/OptionC/Case3WitnessProof.lean:256`
  (`Case3Witness_proof`).
* `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1498`
  (`InCase3Scope`), `:1681` (`bounded_irreducible_balanced_hybrid`).
* `lean/OneThird/Step8/Case3Residual.lean:208`
  (`case3Witness_hasBalancedPair_outOfScope` axiom), `:265`
  (`hStruct_of_case2_discharge`).
* `lean/OneThird/Step8/Case2Rotation.lean:772` (`Case2FKGSubClaim`),
  `:894` (`case2Witness_balanced_under_FKG`).
* `lean/OneThird/Step8/OptionC/K2Closure.lean:21` (the
  "provably-false `Case2FKGSubClaim`" assessment), `:500`
  (`option_c_K2_closure`).
* `lean/OneThird/Step8/LayerOrdinal.lean:108`
  (`OrdinalDecompOfReducible`), `:472`
  (`hasBalancedPair_of_layered_strongInduction_width3`).
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152/1227/1237`
  (`OrdinalDecomp.hasBalancedPair_lift[_lower/_upper]`).
* `docs/state-MA-Sig-Session1.md` §4.2 §G (Piece 6 signature),
  §10.3 (bridge output non-singleton), §10.6 (base-case caveat).
* `docs/OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6 (Piece 6
  scope; risk 1), §3.4 (Checkpoint 6 gate).
* `docs/state-S7-F-bridge-Session2.md` (mg-0bd1, the 8th vacuity).
* `docs/PROOF-STRUCTURE-ONBOARDING.md` §3 pitfall #2 / #6 (the
  recurring cap-stapling pattern) / pitfall #7 (added this session).
* `paper/step8.tex:2453-2464` (`lem:layered-balanced` statement),
  `:3211-3266` (its proof), `:2965-3048` (`prop:in-situ-balanced`).

---

## §10. Maintenance contract notes

Per `PROOF-STRUCTURE-ONBOARDING.md` §5, this session's RED finding
warrants, in the same commit:

* **Add pitfall #7** to `PROOF-STRUCTURE-ONBOARDING.md` §3 — the
  Piece 6 base-case coverage gap (`Case3Witness_proof` needs
  injectivity; the placeholder "wiring" lemmas).
* Update §1 TL;DR bullet on Piece 6 / the S7-F bridge to point at
  this Session 1 finding.
* Add this doc to the §4 predecessor index.
* Flag `OneThird-Option-A-FULL-REFACTOR-scoping.md` §2.6 risk 1 as
  **materialised** with a pointer here.
* No `AXIOMS.md` changes (no axioms added or removed).
* No Lean changes (doc-only RED — mg-5fbd / mg-0bd1 precedent).

If a future session re-scopes Piece 6 (Option G1 or G2 of §7),
this doc's §7 is the starting point and `state-MA-Sig-Session1.md`
§4.2 §G must be re-pinned to whichever routing is chosen.
