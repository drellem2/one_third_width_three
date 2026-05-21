# State — MA-MinCex — Session 1: Piece-4 minimal-counterexample machinery

**Owner.** `mg-7969` (OneThird-MA-MinCex, re-scoped 2026-05-21) — the
Piece-4 *body* sub-ticket for the minimal-counterexample machinery of
the `MainAssembly` proof-by-contradiction refactor.

**Scope.** Build the minimal-counterexample machinery of the Piece-4
signature contract (`docs/state-Piece4-Sig-Session1.md`, `mg-92a8`)
§4.3/§4.4: the `Nat.strong_induction_on` minimal-counterexample
induction, `decomp_reduction`, `ih_descent`, `gamma_counterexample_of_no_BP`.
The first session of this ticket ran ~5h as a RUNAWAY (stopped by
pm-onethird) grinding on a single type-class synthesis error; nothing
was committed.

**Deliverable.** `lean/OneThird/Step8/MinCounterexample.lean` (NEW),
imported into `lean/OneThird.lean`.

---

## §0. Verdict — **GREEN-machinery-landed-sorry-free-axiom-clean**

`lean/OneThird/Step8/MinCounterexample.lean` builds clean. All six
declarations are **sorry-free** and depend only on the three standard
Mathlib axioms `[propext, Classical.choice, Quot.sound]` — **no
`sorryAx`, no project axiom** (`#print axioms`, verified). The full
`OneThird` root builds (`lake build OneThird`, 1450 jobs); the only
`sorry` in the tree is the pre-existing cap-5 structured `sorry` at
`MainAssembly.lean:236`, which Piece 4 / Piece 5 (`mg-MA-Body`) deletes
and which this ticket does not touch.

---

## §1. The `WithEdge` design problem — RESOLVED

The runaway first session invented a fresh type `WithEdge x y` (the
poset `α` with the edge `x ≤ y` adjoined) and tried to hand it a
`private` `PartialOrder` instance.  Lean's type-class resolution cannot
find an ad-hoc `PartialOrder` on a freshly-defined wrapper type — that
is the root cause of the 2h+ edit-build-fail loop.  It is a **design**
problem, not an edit-distance problem.

**Resolution: do not introduce a `WithEdge` type at all.**  The
codebase already ships the order-refinement pattern the ticket asked
for — `OneThird.RelationPoset α` (`lean/OneThird/Mathlib/RelationPoset.lean`,
A8-S2-cont): a finite poset whose order is a **value** (a
`Finset (α × α)`), *not* a typeclass, so there is nothing to
synthesize.  Multiple `RelationPoset α` values coexist on one ground
type.  The relevant API:

* `RelationPoset.ofPartialOrder α` — the data poset of the ambient
  order;
* `RelationPoset.addRel Q a b hba` — augment `Q` by one comparability
  `a ≤ b` (the data-level edge adjunction; `subseteq_addRel`,
  `addRel_le`);
* `RelationPoset.LinearExt' Q` / `numLinExt' Q` / `probLT' Q` — the
  data-poset linear-extension API (`LinearExt'.szpilrajn`,
  `LinearExt'.restrict` along `Subseteq`);
* `RelationPoset.probLT'_ofPartialOrder` — bridges `probLT'
  (ofPartialOrder α)` back to the typeclass `probLT`.

This is needed in exactly **one** place: `probLT_pos_of_not_le` (§3),
the positivity fact that keeps `gamma_counterexample_of_no_BP`
non-vacuous.  `decomp_reduction` needs no edge adjunction at all.

No new type was defined; no `PartialOrder` instance was constructed.
The same instance error did **not** recur — block-and-report was not
needed because the design has an in-tree, already-proven answer.

---

## §2. Deliverables (`MinCounterexample.lean`)

All in `namespace OneThird`, universe-polymorphic
(`{α : Type u} [PartialOrder α] [Fintype α] [DecidableEq α]`).

| Declaration | Statement | Notes |
|---|---|---|
| `chain_of_subsingleton` | `Fintype.card α ≤ 1 → IsChainPoset α` | trivial; §4.8 aux |
| `probLT_pos_of_not_le` | `x ≠ y → ¬ y ≤ x → 0 < probLT x y` | the order-refinement step (§1) |
| `gamma_counterexample_of_no_BP` | `¬ IsChainPoset α → ¬ HasBalancedPair α → ∃ γ, 0 < γ ∧ γ ≤ 1/3 ∧ IsGammaCounterexample α γ` | §4.8 aux |
| `decomp_reduction` | minimal `γ`-cex ⇒ `Indecomposable α` (paper `rem:decomp-reduction`) | §4.4 — see finding F-MinCex-1 |
| `ih_descent` | re-index the `Nat.strong_induction_on` IH to the `< Fintype.card α` form | §4.3 |
| `hasBalancedPair_of_strongInduction` | the packaged `Nat.strong_induction_on` minimal-counterexample induction principle | §4.3 |

`probLT_pos_of_not_le` and the `private isChainPoset_of_split` are
support lemmas; the other five are the named contract deliverables.

### §2.1. `hasBalancedPair_of_strongInduction` — the induction principle

`hasBalancedPair_of_strongInduction` packages the
`Nat.strong_induction_on generalizing` minimal-counterexample induction
(Piece-4 contract §4.3) as a self-contained induction principle: it
takes the inductive `step` (produce a balanced pair from the width-3
non-chain hypotheses + the IH for strictly smaller posets) and yields
`HasBalancedPair α` for every width-3 non-chain `α`.  The `mg-MA-Body`
proof of `width3_one_third_two_thirds_assembled` discharges `step` with
the Theorem-E + Steps-1-7 + bridge + Piece-6 cascade.  The IH handed to
`step` is byte-for-byte the form `decomp_reduction` consumes.  The
implementation mirrors the in-tree idiom of
`LayeredBalancedFull.lean:179-227` (`suffices ∀ n, ∀ β …` then
`induction n using Nat.strong_induction_on`).

---

## §3. Non-vacuity / satisfiability (the acceptance bar)

Per the contract's default-skeptical posture, **satisfiability**, not
type-compatibility:

* **`probLT_pos_of_not_le`** — genuinely establishes `0 < probLT x y`.
  Witness path: `addRel` adjoins the edge `x ≤ y` to `ofPartialOrder α`;
  `LinearExt'.szpilrajn` of the augmentation is non-vacuous
  (`numLinExt' ≥ 1`); restricting it back along `subseteq_addRel`
  yields a linear extension of `α` that genuinely places `x` before
  `y`, so the `x`-before-`y` filter is non-empty.  This is the fact
  that forecloses the vacuity hazard in `gamma_counterexample_of_no_BP`:
  without it the produced `γ` could not be shown positive.
* **`gamma_counterexample_of_no_BP`** — `0 < γ` is *genuinely proved*,
  not assumed.  For each incomparable pair the balance slack
  `min (probLT x y) (probLT y x)` lies strictly in `(0, 1/3)` — lower
  bound from `probLT_pos_of_not_le` (both one-sided probabilities
  positive), upper bound from `¬ IsBalanced` plus
  `probLT x y + probLT y x = 1`.  `γ` is half the finite infimum over
  the (non-empty, since non-chain) set of incomparable pairs of
  `min (slack) (1/3 − slack)`; all three output conjuncts hold.
* **`decomp_reduction`** — substantive: the proof genuinely partitions
  `α` into `A < B` (preimages of the two ordinal-sum summands),
  applies the IH to whichever induced sub-poset is non-chain, and
  lifts the resulting balanced pair via the in-tree
  `OrdinalDecomp.hasBalancedPair_lift_lower` / `_upper` (the same lift
  the R1 grid witness exercises, contract §5.2).  No `true → false`
  pin.
* **`hasBalancedPair_of_strongInduction`** — a sound logical
  repackaging of `Nat.strong_induction_on`; whether `step` is
  dischargeable is `mg-MA-Body`'s cascade obligation, not a vacuity of
  this principle.

---

## §4. Findings

### F-MinCex-1 — `decomp_reduction` takes `¬ HasBalancedPair α`, not `IsGammaCounterexample α γ`

The Piece-4 contract §4.4 pins `decomp_reduction` with
`hCex : IsGammaCounterexample α γ`.  The landed `decomp_reduction`
instead takes `hNoBP : ¬ HasBalancedPair α` directly.

**Reason.** `decomp_reduction` uses only the fact "α has no balanced
pair" — it derives `HasBalancedPair α` from a supposed decomposition
and contradicts it.  Deriving `¬ HasBalancedPair α` *from*
`IsGammaCounterexample α γ` additionally needs `0 ≤ γ`: an incomparable
balanced pair has `min (probLT x y) (probLT y x) ≥ 1/3`, while a
`γ`-counterexample forces `min < 1/3 − γ`; these contradict only when
`γ ≥ 0`.  The §4.4 signature as written would need an extra
`0 ≤ γ` hypothesis.  Taking `¬ HasBalancedPair α` is the honest minimal
hypothesis.

**Call-site impact: none.**  The §4.8 body opens with
`by_contra hNoBP`, so `hNoBP : ¬ HasBalancedPair α` is in scope exactly
where `decomp_reduction` is called.  The §4.8 line becomes
`decomp_reduction hP hNonChain hNoBP (ih_descent hcard ih)` instead of
`… hCex …`.

This is the predictable Phase-1-pseudo-Lean vs Phase-2-finalised drift
the contract §9 anticipates; it is **not** a satisfiability defect.
Recorded in `state-Piece4-Sig-Session1.md` §10 in the same commit.

### F-MinCex-2 — `gamma_counterexample_of_no_BP` is the honest source of `IsGammaCounterexample`

`gamma_counterexample_of_no_BP` produces a *positive* `γ`.  The §4.8
body obtains `⟨γ, hγ_pos, hγ_third, hCex⟩` from it; `hγ_pos : 0 < γ`
and `hγ_third : γ ≤ 1/3` are genuine (not placeholder).  No vacuity:
see §3.

---

## §5. Build / integration

* New file `lean/OneThird/Step8/MinCounterexample.lean`; imports
  `OneThird.Step8.LayeredBalanced` (for `Step8.hasWidthAtMost_subtype`),
  `OneThird.Mathlib.Poset.Indecomposable` (`Indecomposable`, `ordSum`),
  `OneThird.Mathlib.RelationPoset.LinearExt` (the order-refinement
  pattern).
* `lean/OneThird.lean` gains `import OneThird.Step8.MinCounterexample`.
* `lake build OneThird` — completes successfully (1450 jobs).
* `#print axioms` on all six declarations — only
  `[propext, Classical.choice, Quot.sound]`.
* `MainAssembly.lean` is **not** touched (the refactor body
  `width3_one_third_two_thirds_assembled` and the deletion of
  `mainAssembly` / `mainTheoremInputsOf` / `caseC_canonicalLayered` are
  `mg-MA-Body` / Piece 5).

## §6. Hand-off to `mg-MA-Body`

`mg-MA-Body` writes the §4.8 proof-by-contradiction body.  It can:

1. call `hasBalancedPair_of_strongInduction` and supply the cascade as
   the `step` (cleanest), **or** inline `Nat.strong_induction_on` per
   §4.8 and use `ih_descent` to adapt the IH;
2. inside the body: `by_contra hNoBP`;
   `obtain ⟨γ, hγ_pos, hγ_third, hCex⟩ := gamma_counterexample_of_no_BP
   hNonChain hNoBP`;
3. `have hI : Indecomposable α := decomp_reduction hP hNonChain hNoBP
   (ih_descent hcard ih)` — note `hNoBP`, per finding F-MinCex-1;
4. proceed with Theorem E / cascade / bridge / Piece 6 as §4.6–§4.8.

The small-`n` branch uses `chain_of_subsingleton`.

---

## §7. Cross-reference

* `lean/OneThird/Step8/MinCounterexample.lean` — the deliverable.
* `lean/OneThird/Mathlib/RelationPoset.lean` /
  `RelationPoset/LinearExt.lean` — the order-refinement pattern.
* `lean/OneThird/Mathlib/Poset/Indecomposable.lean:60` —
  `Indecomposable`; `ordSum`.
* `lean/OneThird/Mathlib/LinearExtension/Subtype.lean:1152/1227/1237` —
  `OrdinalDecomp.hasBalancedPair_lift{,_lower,_upper}`.
* `lean/OneThird/Step8/LayeredBalanced.lean:375` —
  `hasWidthAtMost_subtype` (in `namespace OneThird.Step8`).
* `docs/state-Piece4-Sig-Session1.md` (`mg-92a8`) — the contract; §4.3,
  §4.4, §4.8, §9, and the §10 landing note added here.
* `step8.tex:106-260` `thm:main-step8`; `step8.tex:274`
  `rem:decomp-reduction`.
