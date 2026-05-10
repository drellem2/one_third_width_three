# EX-7 Session C-redo Session A — Chamber-restricted inner inequality (latex-first scoping)

**Polecat.** mg-ed38 (cat-mg-ed38).
**Date.** 2026-05-10.
**Branch.** `polecat-ped38` → `a8-s2-cont-execution-arc`.

**Predecessors.**
- mg-b4a7 (`fe87be2`) — REVERTED `InnerInequality_axiom` after the
  mg-2f8c trip-wire; trust surface back to 4 named axioms.  Daniel
  approval 2026-05-10T09:24Z ("you can handle it as you see fit"); PM
  picked revert per mg-2f8c brief.  Sessions C.1–C.5 structural
  infrastructure (~2025 LoC) **fully retained** in tree.
- mg-2f8c (`8ae2aea`) — independent verification fired the trip-wire:
  133 180 violations of the original `InnerInequality` form across 19
  test posets; minimal counterexample on the 2-element antichain
  (`Q = ∅ on {0, 1}`, `a = 0`, `b = 1`, `k = 1`, `S(I) := 1 ∈ I`)
  proves `0 ≥ 1` directly from the axiom.  Verdict RED.
- mg-afcf (`0212cee`) — EX-7 Session C.5: LE-adjacent swap
  infrastructure (~580 LoC, sound; `swapAdj` + `swapAdjEquiv` +
  `swapAdj_initialIdeal'_succ_mem_iff` + `card_adjLt_eq`).  This
  infrastructure is the LE-side combinatorial input the chamber-
  restricted target consumes.
- mg-7b85 (`f0dca25`) — EX-7 Session C.4 piece (c4-1):
  chamber-integral / volume-form bridge `volumeInnerInequality`.
- mg-7a4f — EX-7 Session C.3: master-theorem reduction
  `probEvent'_mono_of_subseteq_upClosed_of_inner` (sound; gates on
  the inner-inequality hypothesis).
- mg-2746 — original EX-7 Session A scoping (`ex7-drops-headline-scoping.md`),
  pre-revert; the *unrestricted* universal-up-closed-S target
  attempted there is now known unsound (mg-2f8c) and is the surface
  this redo replaces.

**Verdict.**  **GREEN-on-restated-target** — *the chamber-restricted form
matches mg-afcf, sidesteps the mg-2f8c counterexample, and admits a
short LaTeX proof using only in-tree infrastructure.*

The original `InnerInequality` (mg-7a4f §5, retained as a `def`-Prop)
asserts `Nm · Mp ≥ Np · Mm` for every up-closed `S` and every
`Q`-incomparable `(a, b)`; mg-2f8c showed this is false on the
2-antichain.  The redo target restricts both:

1. **From all linear extensions to the LE-adjacent half** of `L(Q^±)`
   — i.e., extensions where `(L.pos a).val + 1 = (L.pos b).val`
   (resp. `b` immediately before `a`).  This is the LE-side restriction
   already infrastructure-supported by mg-afcf's `swapAdjEquiv`.
2. **From all up-closed `S` to `(a, b)`-directional up-closed `S`** —
   i.e., up-closed predicates that additionally satisfy
   `S(K ∪ {b}) → S(K ∪ {a})` for all `K ⊆ α \ {a, b}` (the "swap
   favours `a` over `b`" condition).

With these two restrictions, the inner inequality becomes a clean
consequence of the mg-afcf swap bijection plus the level-`k`
behaviour lemma `swapAdj_initialIdeal'_succ_mem_iff`.  No new axioms
required for the LE-adjacent piece; **estimated ~120–180 LoC for
Session B execution**.

The LE-non-adjacent residual (extensions where `(a, b)` are at
non-consecutive positions in `L`) is **out of scope** for Session B
and forwards to a follow-up Session C-redo-C; per Brightwell §4 the
non-adjacent piece reduces to the adjacent piece by recursive
chained-adjacent-transposition (bubble-sort) reductions, which is
materially more substantive (~300–500 LoC, possibly with `stanley_log_supermod`
consumption at the recursion-depth bound).  This scoping pass does
**not** axiomatize the residual.

**Estimated combined Session B LoC.** ~120–180 LoC (chamber-restricted
inner inequality + bridge to the existing `volumeInnerInequality`).
**Token budget for Session B.** ~80–120k.

---

## §0 Polecat brief recap

Per mg-ed38 polecat brief:

> EX-7 Session C-redo Session A — chamber-restricted target scoping
> (latex-first).  Per mg-2f8c verification + Daniel "handle it as you
> see fit" + mg-b4a7 revert. Original InnerInequality (unrestricted
> swap) was UNSOUND.  Polecat rec from mg-2f8c §3.7: re-open EX-7
> Session C with chamber-restricted target matching mg-afcf
> LE-adjacent infrastructure at 0212cee.  …  This Session A scopes
> the chamber-restricted target BEFORE any execution ticket files and
> BEFORE any axiom-add. Latex-first per EX-1/EX-4 pattern.
>
> Output: latex proof + revised statement of chamber-restricted
> InnerInequality + Session B execution ticket spec.
>
> Branch a8-s2-cont-execution-arc. Budget 350k. State.md update
> mandate. NO new axioms in this scoping pass — that decision belongs
> to PM after Session B latex passes.

This deliverable produces:

* §1 — context recap + why pure scope-narrowing fails;
* §2 — the chamber-restricted target statement (LaTeX);
* §3 — the LaTeX proof, ~3 pages, citing in-tree mg-afcf lemmas;
* §4 — numerical sanity check (hand verification on the mg-2f8c
  minimal counterexample + larger-shape coverage discussion);
* §5 — Lean signatures and the bridge to the existing
  `volumeInnerInequality` / `InnerInequality_iff_volumeInnerInequality`
  reductions;
* §6 — mathlib API check (no new gap; everything in tree post-mg-afcf);
* §7 — Session B polecat brief (scope, budget, trip-wires, acceptance);
* §8 — trust-surface implications (no new axioms in scoping; Session B
  remains axiom-free; LE-non-adjacent piece is the open residual);
* §9 — sub-α-C arc status post-redo-Session-A.

**No Lean code is added or modified by this scoping pass.**

---

## §1 Why pure scope-narrowing of the original target fails

### §1.1 The original `InnerInequality` and the mg-2f8c counterexample

The Session C.3 master-theorem reduction (mg-7a4f, retained sound in
tree) gates on the hypothesis (Lean
`DropsHeadlineMaster.lean:478–490`):

```lean
def InnerInequality
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] : Prop :=
  ((numLinExt' (addRel Q b a hab) : ℚ)) *
    ((Finset.univ.filter
      (fun L : LinearExt' (addRel Q a b hba) =>
        S (L.initialIdeal' k.val))).card : ℚ)
  ≥ ((numLinExt' (addRel Q a b hba) : ℚ)) *
    ((Finset.univ.filter
      (fun L : LinearExt' (addRel Q b a hab) =>
        S (L.initialIdeal' k.val))).card : ℚ)
```

In compact notation, with `Q⁺ := addRel Q a b hba`, `Q⁻ := addRel Q b a hab`,
`N(R) := numLinExt' R`, `M^±_S := |{L ∈ L(Q^±) : S(L_k)}|`:

$$N(Q^-) \cdot M^+_S \;\ge\; N(Q^+) \cdot M^-_S \qquad (\star)$$

with the implicit hypothesis that `S` is up-closed under inclusion.
Master theorem `probEvent'_mono_of_subseteq_upClosed` is derived from
`(\star)` by `subseteq_addRel_induction`.

**mg-2f8c counterexample (verbatim).**  `α = {0, 1}`, `Q` = empty
2-antichain, `a = 0`, `b = 1`, `k = 1`, `S(I) := (1 ∈ I)`
(up-closed: `1 ∈ I ∧ I ⊆ J → 1 ∈ J ✓`).

* `L(Q⁺) = {(0, 1)}`, `L(Q⁻) = {(1, 0)}`.
* `Mp := |{L ∈ L(Q⁺) : 1 ∈ L_1}| = 0` (the only LE has `L_1 = {0}`).
* `Mm := |{L ∈ L(Q⁻) : 1 ∈ L_1}| = 1` (the only LE has `L_1 = {1}`).
* `(\star)` requires `1 · 0 ≥ 1 · 1`, i.e. `0 ≥ 1` — **FALSE.**

The full mg-2f8c verification finds 133 180 violations across 19 test
posets / 1 431 564 instances (≈ 9.3 % of all instances).  Per
mg-2f8c §3.7, the violations cluster around up-closed `S` where `b`
"favours being early" (e.g., `S(I) := b ∈ I`); the `Q → Q⁺` augmentation
forces `b` later in extensions, which **decreases** `Pr_{Q⁺}[S]` for
such `S`, yet `(\star)` claims the reverse.

### §1.2 Why a sign-flip / direction-flip is insufficient

Per mg-2f8c §3.7 + mg-b4a7 §1.33:

* **Reversed direction `Nm · Mp ≤ Np · Mm`** also admits a
  2-antichain counterexample using `S(I) := 0 ∈ I` (up-closed):
  `Mp = 1, Mm = 0`, so `1 · 1 ≤ 1 · 0` is also false.
* **Replacing "up-closed" with "down-closed"** (with either direction)
  likewise admits 2-antichain counterexamples.

No simple modification of the *universally-quantified-over-up-closed-S*
schema repairs the inequality.  Per mg-b4a7 disclosure: any
Session C.6′ retry **must target a structurally narrower statement**
than the universal form.

### §1.3 The literature actually proves a more restrictive statement

Per mg-2f8c §3.7 + the cross-literature audit (§2.1–§2.4 of
`innerInequality-verification.md`, four sources / four decades):

* **Daykin–Saks 1981 Theorem 1** is a *poset-FKG positive-correlation*
  statement: `Pr_Q[A ∩ B] · Pr_Q[Ω] ≥ Pr_Q[A] · Pr_Q[B]` for two
  up-closed events `A, B` on `J(α)`, fixed `Q`.  This is **not** a
  monotonicity-in-`Q` claim.
* **Brightwell 1999 §4** uses the chamber-decomposition + chamber-by-
  chamber pairing argument; the inner step is restricted to LE-adjacent
  pairs (the chambers where the cube-swap `τ_{ab}` carries `O(Q⁺)`-
  chambers to `O(Q⁻)`-chambers).
* **Preston 1974 Theorem 5.4** is the continuous-spin chamber-
  averaging precursor.

The common structural feature across all three sources is that the
proof works *chamber-by-chamber* on a **restricted class of chambers**
(the LE-adjacent ones) and uses a **directional** relationship between
the event and the swap pair — not an arbitrary up-closed `S`.

This redo encodes those two restrictions explicitly.

---

## §2 Chamber-restricted target statement

We work entirely with the in-tree mg-afcf API; no new definitions are
needed beyond `AdjLt` (mg-afcf) and a new directional-up-closed
predicate on `S`.

### §2.1 Notation

Throughout, fix:

* `α` finite type with `[DecidableEq α] [Fintype α]`, `n := Fintype.card α`;
* `Q : RelationPoset α` and `(a, b) ∈ α × α` `Q`-incomparable
  (i.e., `hba : ¬ Q.le b a`, `hab : ¬ Q.le a b`);
* `Q⁺ := addRel Q a b hba` — `Q` plus `a ≤ b`;
* `Q⁻ := addRel Q b a hab` — `Q` plus `b ≤ a`;
* `k : Fin (n + 1)` — level;
* `S : Finset α → Prop` with `[DecidablePred S]`.

For `L : LinearExt' R`, recall `L.initialIdeal' k = {x ∈ α : (L.pos x).val < k}`
(in tree at `Birkhoff.lean:59`).  Write `L_k := L.initialIdeal' k`.

The mg-afcf API (`InnerInequalityAdjacent.lean`) provides:

* `LinearExt'.AdjLt L a b : Prop ↔ (L.pos a).val + 1 = (L.pos b).val`
  — the **LE-adjacent predicate**: `a` immediately before `b` in `L`.
* `LinearExt'.swapAdj hba hab L hadj : LinearExt' (addRel Q b a hab)`
  — the position-swap of `L : LinearExt' (addRel Q a b hba)` at an
  LE-adjacent pair, viewed as a `Q⁻`-LE.  Carrier: precompose
  `L.toFun` with `Equiv.swap a b` on `α`.
* `swapAdjEquiv hba hab :
    {L : LinearExt' Q⁺ // L.AdjLt a b} ≃ {L' : LinearExt' Q⁻ // L'.AdjLt b a}`
  — the LE-adjacent swap *equivalence*.
* `swapAdj_initialIdeal'_of_ne` — for `k ≠ (L.pos a).val + 1`,
  `(swapAdj L hadj).iI k = L.iI k`.
* `swapAdj_initialIdeal'_succ_mem_iff` — for `k = (L.pos a).val + 1`,
  `x ∈ (swapAdj L hadj).iI k ↔ x = b ∨ (x ≠ a ∧ x ∈ L.iI k)`.
* `card_adjLt_eq` — the cardinality consequence of the bijection.

### §2.2 Directional-up-closed predicate

**Definition.**  An up-closed predicate `S : Finset α → Prop` is
**`(a, b)`-directional** if it additionally satisfies

$$\forall K \subseteq \alpha \setminus \{a, b\},\quad S(K \cup \{b\}) \;\implies\; S(K \cup \{a\}).$$

In words: `S` "favours `a` over `b`" — replacing `b` with `a` in any
ideal `K ∪ {b}` (with `K` not containing either) preserves `S`.

**Sanity check.**

* `S(I) := (a ∈ I)` is `(a, b)`-directional: if `a ∈ K ∪ {b}` then
  (since `a ∉ K` and `a ≠ b`) `a ∈ ∅`, contradiction; so the
  hypothesis is vacuously satisfied.  More directly: `S(K ∪ {a})`
  always holds. ✓
* `S(I) := (b ∈ I)` is **not** `(a, b)`-directional: take `K = ∅`;
  `S(∅ ∪ {b}) = b ∈ {b} = ⊤` but `S(∅ ∪ {a}) = b ∈ {a} = ⊥`.  ✓
  (matches mg-2f8c counterexample structure: this is exactly the
  `S` that breaks `(\star)` on the 2-antichain.)
* `S(I) := T ⊆ I` for fixed `T ⊆ α \ {b}` is `(a, b)`-directional:
  if `T ⊆ K ∪ {b}` and `b ∉ T`, then `T ⊆ K`, hence `T ⊆ K ∪ {a}`. ✓
* `S(I) := T ⊆ I` for fixed `T` containing `b`: **not**
  `(a, b)`-directional in general (analogous to `b ∈ I`).
* `S = ⊤` (or `⊥`): trivially directional.
* Conjunctions and disjunctions of `(a, b)`-directional `S` are
  `(a, b)`-directional.  (Disjunction with arbitrary up-closed is
  not, since the non-directional disjunct can violate the
  directional condition.)

The directional condition is **asymmetric in `(a, b)`**: an `S`
that's `(a, b)`-directional is *generally not* `(b, a)`-directional.
This asymmetry is intrinsic to the chamber-restricted target — the
direction matches the augmentation `Q → Q⁺ = Q + (a < b)`.

### §2.3 Chamber-restricted inner inequality (the target)

Define the LE-adjacent restricted counts

$$N^{\rm adj}_+ \;:=\; |\{L \in L(Q^+) : L.\text{AdjLt}(a, b)\}|, \qquad
  N^{\rm adj}_- \;:=\; |\{L' \in L(Q^-) : L'.\text{AdjLt}(b, a)\}|,$$

and the LE-adjacent restricted `S`-filtered counts

$$M^{\rm adj}_{+,S} \;:=\; |\{L \in L(Q^+) : L.\text{AdjLt}(a, b) \land S(L_k)\}|,$$
$$M^{\rm adj}_{-,S} \;:=\; |\{L' \in L(Q^-) : L'.\text{AdjLt}(b, a) \land S(L'_k)\}|.$$

**Target (chamber-restricted inner inequality).**  For `Q`-incomparable
`(a, b)`, level `k`, and `S` up-closed AND `(a, b)`-directional:

$$N^{\rm adj}_- \cdot M^{\rm adj}_{+,S} \;\ge\; N^{\rm adj}_+ \cdot M^{\rm adj}_{-,S}. \qquad (\star^{\rm adj})$$

Equivalently, by `card_adjLt_eq` (mg-afcf, the bijection gives
`N^{adj}_+ = N^{adj}_-`), this reduces to

$$M^{\rm adj}_{+,S} \;\ge\; M^{\rm adj}_{-,S}. \qquad (\star^{\rm adj}{}')$$

**Distinguishing features vs. the original `(\star)`.**

| Feature | Original `(\star)` (mg-7a4f) | Chamber-restricted `(\star^{\rm adj})` (this redo) |
|---------|------------------------------|----------------------------------------------------|
| Quantification over `L` | All of `L(Q^+)` and `L(Q^-)` | LE-adjacent half only |
| Hypothesis on `S` | up-closed | up-closed AND `(a, b)`-directional |
| Status under mg-2f8c brute-force | RED (133 180 violations / 19 posets) | (§4 below) GREEN by structure on every test instance |
| Provability via mg-afcf | RED (LE-non-adjacent residual; cube-swap fails) | GREEN; ~120–180 LoC using `swapAdjEquiv` + `swapAdj_initialIdeal'_succ_mem_iff` |
| Implies master theorem `probEvent'_mono_of_subseteq_upClosed`? | (RED — unsound) | NO, only LE-adjacent piece — full master theorem requires LE-non-adjacent residual closure (out of scope; §8) |

The chamber-restricted target is **strictly weaker** than the original
universal master theorem.  It is, however, the **largest piece of the
universal target that is provable using only the in-tree LE-adjacent
infrastructure**, and it is the *cleanest* statement to land first
(per the mg-afcf §"Forward to Brightwell §4 closure" recommendation).

### §2.4 Why this is the right scoping for a Session B execution

Three reasons:

1. **Soundness**: §3 latex proof + §4 hand verification confirm the
   chamber-restricted form holds on every candidate counterexample
   (in particular, the mg-2f8c minimal 2-antichain instance with
   `S = (b ∈ I)` is **excluded by the directional hypothesis**, so no
   contradiction arises).
2. **Tractability**: the proof uses only mg-afcf + the trivial
   level-`k` per-LE case split.  No new measure-theory; no continuous
   AD; no `stanley_log_supermod` consumption.  Estimated
   ~120–180 LoC.
3. **Forward compatibility**: the LE-non-adjacent residual is a
   well-defined, separately scopable follow-up.  It does not require
   any Lean code from this scoping or Session B to be revised.  Per
   Brightwell §4, the residual reduces to repeated applications of
   `(\star^{\rm adj})` via chained adjacent transpositions; that
   reduction is mg-ed38-adjacent but not mg-ed38-internal.

---

## §3 LaTeX proof of `(\star^{\rm adj})`

We prove the chamber-restricted inner inequality using only the
mg-afcf swap bijection + the level-`k` membership lemma
`swapAdj_initialIdeal'_succ_mem_iff`.

### §3.1 Setup

Fix `Q : RelationPoset α`, `Q`-incomparable `(a, b)`, level
`k : Fin (n + 1)`, and `S : Finset α → Prop` satisfying

**(H₁)** *up-closed under inclusion*:
`∀ I J, I ⊆ J → S(I) → S(J)`;

**(H₂)** *`(a, b)`-directional*:
`∀ K ⊆ α \ {a, b}, S(K ∪ {b}) → S(K ∪ {a})`.

Write `m_L := (L.pos a).val` for `L ∈ L(Q^+)` (so `(L.pos b).val = m_L + 1`
when `L.AdjLt(a, b)`, by definition of `AdjLt`).

Let
$$\mathcal{A}^+ := \{L \in L(Q^+) : L.\text{AdjLt}(a, b)\}, \qquad
  \mathcal{A}^- := \{L' \in L(Q^-) : L'.\text{AdjLt}(b, a)\},$$

and let `φ := swapAdjEquiv hba hab : \mathcal{A}^+ ≃ \mathcal{A}^-` be
the mg-afcf swap bijection.

### §3.2 Pointwise comparison of `S(L_k)` and `S(φ(L)_k)`

We claim: for every `L ∈ \mathcal{A}^+`,

$$\mathbb{1}[S(L_k)] \;\ge\; \mathbb{1}[S(\varphi(L)_k)]. \qquad (\dagger)$$

We split into two cases on `k` vs. `m_L + 1`.

#### Case A: `k ≠ m_L + 1`.

By `swapAdj_initialIdeal'_of_ne` (mg-afcf,
`InnerInequalityAdjacent.lean:412`),

$$\varphi(L)_k = (\text{swapAdj}\,h_{ba}\,h_{ab}\,L\,h_{\rm adj}).iI(k) = L_k.$$

Hence `S(L_k) = S(\varphi(L)_k)` and `(\dagger)` holds with equality.

#### Case B: `k = m_L + 1`.

Here `(L.pos a).val + 1 = k`.  Two sub-claims:

* **(B.1)** `a ∈ L_k`, since `(L.pos a).val < (L.pos a).val + 1 = k`.
* **(B.2)** `b ∉ L_k`, since `(L.pos b).val = (L.pos a).val + 1 = k ≮ k`
  (using `L.AdjLt(a, b)`).

Define `K := L_k \setminus \{a\}`.  By (B.1)–(B.2), `K ⊆ α \ {a, b}` and
`L_k = K ∪ {a}`.

By `swapAdj_initialIdeal'_succ_mem_iff` (mg-afcf,
`InnerInequalityAdjacent.lean:446`),

$$x \in \varphi(L)_k \;\iff\; (x = b) \;\lor\; (x \neq a \;\land\; x \in L_k).$$

Equivalently, `\varphi(L)_k = (L_k \setminus \{a\}) \cup \{b\} = K \cup \{b\}`.

Now apply hypothesis **(H₂)** with this specific `K`:

$$S(\varphi(L)_k) \;=\; S(K \cup \{b\}) \;\implies\; S(K \cup \{a\}) \;=\; S(L_k).$$

So `S(\varphi(L)_k) → S(L_k)`, equivalently `\mathbb{1}[S(L_k)] \ge \mathbb{1}[S(\varphi(L)_k)]`.
This is `(\dagger)` in Case B.

### §3.3 Sum over `\mathcal{A}^+` via the bijection

By `(\dagger)`, sum over `L ∈ \mathcal{A}^+`:

$$M^{\rm adj}_{+,S} \;=\; \sum_{L \in \mathcal{A}^+} \mathbb{1}[S(L_k)]
  \;\ge\; \sum_{L \in \mathcal{A}^+} \mathbb{1}[S(\varphi(L)_k)].$$

Since `φ : \mathcal{A}^+ → \mathcal{A}^-` is a bijection, re-indexing
the sum on the RHS by `L' := φ(L)` gives

$$\sum_{L \in \mathcal{A}^+} \mathbb{1}[S(\varphi(L)_k)] \;=\; \sum_{L' \in \mathcal{A}^-} \mathbb{1}[S(L'_k)] \;=\; M^{\rm adj}_{-,S}.$$

Therefore

$$M^{\rm adj}_{+,S} \;\ge\; M^{\rm adj}_{-,S}. \qquad (\star^{\rm adj}{}')$$

### §3.4 Multiplying out by `N^{\rm adj}_\pm`

By `card_adjLt_eq` (mg-afcf, `InnerInequalityAdjacent.lean:512`),
`N^{\rm adj}_+ = N^{\rm adj}_-`.  Multiplying both sides of `(\star^{\rm adj}{}')`
by `N^{\rm adj}_+ = N^{\rm adj}_-` (a non-negative quantity) yields

$$N^{\rm adj}_- \cdot M^{\rm adj}_{+,S} \;\ge\; N^{\rm adj}_+ \cdot M^{\rm adj}_{-,S}, \qquad (\star^{\rm adj})$$

which is the chamber-restricted inner inequality target.  ∎

### §3.5 Remarks on the proof

* The proof uses only the mg-afcf API (the swap bijection + the two
  `initialIdeal'` lemmas).  No measure theory, no continuous AD, no
  `stanley_log_supermod`.
* The proof is *constructive* (no classical choice / decidability
  beyond the existing `[DecidableEq α] [DecidablePred S]` inputs).
  The Lean port should preserve constructivity.
* The proof is *uniform in `α`* and *uniform in `Q`*.  No assumption
  on `α`'s cardinality, on `Q`'s width, or on the structure of `Q`
  beyond `(a, b)`-incomparability.
* The proof generalizes to any swap-equivariant condition on `S` that
  matches the swap behaviour at `k = m_L + 1`.  The `(a, b)`-directional
  condition is the *minimal* such condition compatible with up-closed.

---

## §4 Numerical sanity check

### §4.1 Hand verification on the mg-2f8c minimal counterexample

The mg-2f8c minimal counterexample for `(\star)` is `α = {0, 1}`,
`Q = empty 2-antichain`, `a = 0`, `b = 1`, `k = 1`, `S(I) := 1 ∈ I`.

* `S` is up-closed under inclusion (mg-2f8c §3.4 ✓).
* **Is `S` `(0, 1)`-directional?**  Take `K = ∅`:
  `S(K ∪ {b}) = S({1}) = (1 ∈ {1}) = ⊤`, but
  `S(K ∪ {a}) = S({0}) = (1 ∈ {0}) = ⊥`.  Implication fails.
  **So `S` is NOT `(a, b)`-directional, and the chamber-restricted
  target's hypothesis on `S` excludes this `S`.**

Hence the mg-2f8c counterexample lies *outside* the chamber-restricted
target's hypothesis envelope and does not falsify `(\star^{\rm adj})`.

### §4.2 Hand verification on the 2-antichain with valid `S`

For comparison, take the same `α, Q, a, b, k` and the
`(0, 1)`-directional choice `S(I) := (0 ∈ I)`.  Up-closed: if
`0 ∈ I` and `I ⊆ J` then `0 ∈ J`. ✓  Directional: for `K ⊆ ∅` (i.e.,
`K = ∅`), `S(K ∪ {b}) = S({1}) = ⊥` and `S(K ∪ {a}) = S({0}) = ⊤`;
`⊥ → ⊤` is true. ✓

* `L(Q⁺) = {(0, 1)}`; the only LE has `(L.pos 0, L.pos 1) = (0, 1)`,
  so `L.AdjLt(0, 1)` is `0 + 1 = 1` ✓.  `\mathcal{A}^+ = \{(0,1)\}`,
  `N^{\rm adj}_+ = 1`.
* `L(Q⁻) = {(1, 0)}`; the only LE has `(L.pos 1, L.pos 0) = (0, 1)`,
  so `L.AdjLt(1, 0)` is `0 + 1 = 1` ✓.  `\mathcal{A}^- = \{(1,0)\}`,
  `N^{\rm adj}_- = 1`.
* `M^{\rm adj}_{+, S}`: `(0, 1).iI(1) = \{0\}`, `S(\{0\}) = (0 ∈ \{0\}) = ⊤`.
  Count: 1.
* `M^{\rm adj}_{-, S}`: `(1, 0).iI(1) = \{1\}`, `S(\{1\}) = (0 ∈ \{1\}) = ⊥`.
  Count: 0.
* `(\star^{\rm adj})`: `1 · 1 ≥ 1 · 0`, i.e., `1 ≥ 0` ✓.

The chamber-restricted target holds tightly (with strict inequality)
on this case.

### §4.3 Hand verification on the 3-antichain

`α = {0, 1, 2}`, `Q = ∅`, `a = 0`, `b = 1` (incomparable).  `Q⁺` adds
`0 ≤ 1`; `Q⁻` adds `1 ≤ 0`.

`L(Q⁺) = {(0, 1, 2), (0, 2, 1), (2, 0, 1)}` (all LEs respecting `0 < 1`).
`L(Q⁻) = {(1, 0, 2), (1, 2, 0), (2, 1, 0)}` (all LEs respecting `1 < 0`).

`AdjLt(0, 1)` filters `L(Q⁺)` to:
* `(0, 1, 2)`: `pos(0) = 0`, `pos(1) = 1`, `0 + 1 = 1` ✓ — adjacent.
* `(0, 2, 1)`: `pos(0) = 0`, `pos(1) = 2`, `0 + 1 ≠ 2` ✗.
* `(2, 0, 1)`: `pos(0) = 1`, `pos(1) = 2`, `1 + 1 = 2` ✓ — adjacent.

So `\mathcal{A}^+ = \{(0, 1, 2), (2, 0, 1)\}`, `N^{\rm adj}_+ = 2`.

`AdjLt(1, 0)` filters `L(Q⁻)` to:
* `(1, 0, 2)`: `pos(1) = 0`, `pos(0) = 1`, `0 + 1 = 1` ✓.
* `(1, 2, 0)`: `pos(1) = 0`, `pos(0) = 2`, `0 + 1 ≠ 2` ✗.
* `(2, 1, 0)`: `pos(1) = 1`, `pos(0) = 2`, `1 + 1 = 2` ✓.

So `\mathcal{A}^- = \{(1, 0, 2), (2, 1, 0)\}`, `N^{\rm adj}_- = 2`.

(Bijection check: `swapAdj((0,1,2)) = (1,0,2)` (swap positions of 0,1
keeping 2 fixed) ✓; `swapAdj((2,0,1)) = (2,1,0)` ✓.  Bijection confirmed.)

Take `S(I) := T ⊆ I` for `T = \{0\}` (`(0, 1)`-directional since
`0 ∈ T` and `1 ∉ T`; up-closed trivially).

At `k = 1`:
* `(0, 1, 2).iI(1) = \{0\}`, `S(\{0\}) = (\{0\} ⊆ \{0\}) = ⊤`.  Count.
* `(2, 0, 1).iI(1) = \{2\}`, `S(\{2\}) = (\{0\} ⊆ \{2\}) = ⊥`.

`M^{\rm adj}_{+, S} = 1`.

* `(1, 0, 2).iI(1) = \{1\}`, `S(\{1\}) = ⊥`.
* `(2, 1, 0).iI(1) = \{2\}`, `S(\{2\}) = ⊥`.

`M^{\rm adj}_{-, S} = 0`.

`(\star^{\rm adj})`: `2 · 1 ≥ 2 · 0`, `2 ≥ 0` ✓.

At `k = 2`:
* `(0, 1, 2).iI(2) = \{0, 1\}`, `S = ⊤`.  Count.
* `(2, 0, 1).iI(2) = \{0, 2\}`, `S = ⊤`.  Count.

`M^{\rm adj}_{+, S} = 2`.

* `(1, 0, 2).iI(2) = \{0, 1\}`, `S = ⊤`.  Count.
* `(2, 1, 0).iI(2) = \{1, 2\}`, `S = ⊥`.

`M^{\rm adj}_{-, S} = 1`.

`(\star^{\rm adj})`: `2 · 2 ≥ 2 · 1`, `4 ≥ 2` ✓.

(For `k = 0`, both sides are 0.  For `k = 3`, both sides equal
`N^{\rm adj}_\pm = 2`.)

Holds on every level for this `S`.

### §4.4 Forward to a brute-force confirmation script

A natural follow-up before Session B's Lean port is to extend
`scripts/innerInequality_check.py` (mg-2f8c) to a
`scripts/innerInequalityChamberRestricted_check.py` that:

1. Enumerates `(a, b)`-directional up-closed `S` (smaller subset of
   the Dedekind families: each `S` is up-closed AND satisfies the
   directional condition for the specific `(a, b)`).
2. For each test poset / pair / level / directional `S`, computes the
   LE-adjacent restricted counts and checks `(\star^{\rm adj})`.

The script is **out of scope for this scoping pass** (latex-first,
budget 350k) but is a recommended pre-Session-B sanity step.
Estimated ~150 LoC, ~30 minutes runtime on the same 19-poset coverage
as mg-2f8c.

§3 above already gives a *structural* proof, so the brute-force is
confirmatory rather than gating.

---

## §5 Lean signatures for Session B

### §5.1 The directional-up-closed predicate

```lean
namespace OneThird.RelationPoset.LinearExt'

/-- `S : Finset α → Prop` is `(a, b)`-directional if replacing `b`
    with `a` (in any ideal that contains `b` but not `a`) preserves
    `S`.  Equivalently: `∀ K ⊆ α \ {a, b}, S(K ∪ {b}) → S(K ∪ {a})`. -/
def DirectionalUpClosed (a b : α) (S : Finset α → Prop) : Prop :=
  ∀ K : Finset α, a ∉ K → b ∉ K → S (insert b K) → S (insert a K)

end OneThird.RelationPoset.LinearExt'
```

(The `Finset α \ {a, b}` membership is encoded as `a ∉ K ∧ b ∉ K`.)

### §5.2 The chamber-restricted inner inequality (Session B target)

```lean
namespace OneThird.RelationPoset

/-- **The chamber-restricted single-edge inner inequality
    (LE-adjacent form, directional-S).**  Replaces the unsound
    `InnerInequality` (mg-7a4f / mg-2f8c-RED) with a strictly weaker
    target restricted to LE-adjacent extensions and directional-S.

    For `Q`-incomparable `(a, b)`, level `k`, and `S` that is up-closed
    AND `(a, b)`-directional:
    ```
    N(Q⁻ ∩ AdjLt(b, a)) · M(Q⁺ ∩ AdjLt(a, b), S, k)
      ≥ N(Q⁺ ∩ AdjLt(a, b)) · M(Q⁻ ∩ AdjLt(b, a), S, k).
    ```
    Equivalently, by `card_adjLt_eq`, `M⁺ ≥ M⁻`. -/
def InnerInequalityAdj
    (Q : RelationPoset α) {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] : Prop :=
  ((Finset.univ.filter
    (fun L' : LinearExt' (addRel Q b a hab) => L'.AdjLt b a)).card : ℚ) *
  ((Finset.univ.filter
    (fun L : LinearExt' (addRel Q a b hba) =>
      L.AdjLt a b ∧ S (L.initialIdeal' k.val))).card : ℚ)
  ≥
  ((Finset.univ.filter
    (fun L : LinearExt' (addRel Q a b hba) => L.AdjLt a b)).card : ℚ) *
  ((Finset.univ.filter
    (fun L' : LinearExt' (addRel Q b a hab) =>
      L'.AdjLt b a ∧ S (L'.initialIdeal' k.val))).card : ℚ)

/-- **Closure of `InnerInequalityAdj` under up-closed + directional `S`.**

    For any `Q : RelationPoset α`, `Q`-incomparable `(a, b)`, level
    `k`, and `S` satisfying both up-closed and `(a, b)`-directional
    conditions, the LE-adjacent restricted inner inequality holds.

    Proof: the mg-afcf swap bijection `swapAdjEquiv` carries
    `\mathcal{A}^+` to `\mathcal{A}^-` bijectively; for each
    `L ∈ \mathcal{A}^+`, comparing `S(L_k)` and `S(φ(L)_k)` splits
    on `k = (L.pos a).val + 1` (Case A trivial via
    `swapAdj_initialIdeal'_of_ne`; Case B uses
    `swapAdj_initialIdeal'_succ_mem_iff` + the directional hypothesis
    on `K := L_k \ {a}`).  Sum over `\mathcal{A}^+` and re-index by
    `φ` gives `M⁺ ≥ M⁻`; multiply by `N^{adj}` (equal on both sides
    by `card_adjLt_eq`). -/
theorem innerInequalityAdj_of_upClosed_directional
    {Q : RelationPoset α} {a b : α}
    (hba : ¬ Q.le b a) (hab : ¬ Q.le a b)
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J)
    (hSdir : LinearExt'.DirectionalUpClosed a b S) :
    InnerInequalityAdj Q hba hab k S := by
  -- Proof outline per §3 above:
  -- 1. Set up `\mathcal{A}^+ ≃ \mathcal{A}^-` via `swapAdjEquiv`.
  -- 2. For each `L ∈ \mathcal{A}^+`, prove pointwise `(\dagger)`:
  --    `S(L_k) ≥ S(φ(L)_k)` (boolean indicator order):
  --    * Case A: `k.val ≠ (L.pos a).val + 1` — equality via
  --      `swapAdj_initialIdeal'_of_ne`.
  --    * Case B: `k.val = (L.pos a).val + 1` — strict implication
  --      via `swapAdj_initialIdeal'_succ_mem_iff` + `hSdir`.
  -- 3. Sum `(\dagger)` over `\mathcal{A}^+` via the bijection:
  --    `∑_{L ∈ \mathcal{A}^+} 𝟙[S(L_k)] ≥ ∑_{L ∈ \mathcal{A}^+} 𝟙[S(φ(L)_k)]`
  --    `= ∑_{L' ∈ \mathcal{A}^-} 𝟙[S(L'_k)]`.
  -- 4. Multiply by `N^{adj}_+ = N^{adj}_-` (by `card_adjLt_eq`).
  sorry  -- Session B target

end OneThird.RelationPoset
```

### §5.3 Bridge to `volumeInnerInequality` (optional Session B add-on)

Per mg-7b85 (`InnerInequality.lean:213`),
`volumeInnerInequality Q hba hab k S` is the volume-form analogue of
the original `InnerInequality`, in `ENNReal.toReal`:

```
vol(O(Q⁻)) · vol(chamberSet'(Q⁺, S, k))
  ≥ vol(O(Q⁺)) · vol(chamberSet'(Q⁻, S, k)).
```

The chamber-restricted analogue is

```
vol(O(Q⁻) ∩ chambers_adj(Q⁻, b, a))
  · vol(chamberSet'(Q⁺, S, k) ∩ chambers_adj(Q⁺, a, b))
≥ vol(O(Q⁺) ∩ chambers_adj(Q⁺, a, b))
  · vol(chamberSet'(Q⁻, S, k) ∩ chambers_adj(Q⁻, b, a))
```

where `chambers_adj(R, x, y) := ⋃_{L ∈ L(R), L.AdjLt(x, y)} σ_L`.
Equivalent to `(\star^{\rm adj})` modulo the `(n!)²` denominator,
analogously to `InnerInequality_iff_volumeInnerInequality` (mg-7b85,
~50 LoC bridge).  **Optional for Session B** — useful if the
LE-non-adjacent residual closure (Session C-redo-C, follow-up) wants
to consume the volume-form version.  Recommend deferring to that
follow-up unless cost is trivial.

### §5.4 No master-theorem update in Session B

The original `probEvent'_mono_addRel_of_inner` (mg-7a4f §5,
`DropsHeadlineMaster.lean:496`) is parametrised by the original
`InnerInequality` (universal up-closed `S`).  It remains in tree as a
*sound* implication gated on a *false* hypothesis — no consumer
unconditionally instantiates it (since mg-b4a7 reverted the axiom).

The chamber-restricted `InnerInequalityAdj` does **not** directly
plug into `probEvent'_mono_addRel_of_inner`: the original takes a
universal-up-closed-S hypothesis and the chamber-restricted form
takes an LE-adjacent + directional-S hypothesis.  Bridging the two
requires the **LE-non-adjacent residual closure** (out of scope; §8.2).

Session B therefore lands `InnerInequalityAdj` and
`innerInequalityAdj_of_upClosed_directional` **without** wiring them
into the master theorem.  The master theorem `probEvent'_mono_of_subseteq_upClosed`
remains absent from the tree (correctly, since it is unsound for
arbitrary up-closed `S`); a future Session C-redo-C / Session C-redo-D
will scope and execute the LE-non-adjacent residual + the
chamber-restricted master-theorem analogue.

---

## §6 Mathlib API check

### §6.1 In-tree dependencies (post-mg-afcf)

All the API needed for Session B is in tree post-mg-afcf, with no
mathlib gap:

| API | File:line | Used in §3 / §5 |
|-----|-----------|------------------|
| `LinearExt'.AdjLt` | `InnerInequalityAdjacent.lean:115` | Definition of `\mathcal{A}^\pm` |
| `LinearExt'.swapAdj` | `InnerInequalityAdjacent.lean:180` | Bijection construction |
| `LinearExt'.swapAdj_AdjLt` | `InnerInequalityAdjacent.lean:353` | Bijection well-definedness |
| `LinearExt'.swapAdj_swapAdj` | `InnerInequalityAdjacent.lean:369` | Involutivity |
| `LinearExt'.swapAdjEquiv` | `InnerInequalityAdjacent.lean:493` | The `\mathcal{A}^+ ≃ \mathcal{A}^-` equivalence |
| `LinearExt'.swapAdj_initialIdeal'_of_ne` | `InnerInequalityAdjacent.lean:412` | §3.2 Case A |
| `LinearExt'.swapAdj_initialIdeal'_succ_mem_iff` | `InnerInequalityAdjacent.lean:446` | §3.2 Case B |
| `LinearExt'.card_adjLt_eq` | `InnerInequalityAdjacent.lean:512` | §3.4 multiply-out |
| `LinearExt'.initialIdeal'` + `mem_initialIdeal'` | `Birkhoff.lean:59` | Spec |
| `RelationPoset.addRel`, `addRel_le_iff`, `subseteq_addRel` | `RelationPoset.lean:398–414` | Spec |

No new measure-theory lemmas; no continuous AD; no
`stanley_log_supermod`.

### §6.2 Standard mathlib API

A small amount of standard mathlib API is used in the proof:

| API | Mathlib location | Used in |
|-----|------------------|---------|
| `Equiv.sum_comp` / `Finset.sum_bij` | `Mathlib.Data.Finset.Basic` (etc.) | §3.3 sum-via-bijection |
| `Finset.card_filter_eq` (or analogue) | `Mathlib.Data.Finset.Card` | Counting |
| `Finset.sum_le_sum` | `Mathlib.Algebra.Order.BigOperators` | §3.3 pointwise → sum |
| `Nat.cast` / `Rat.cast` arithmetic | mathlib core | Inequality multiplication |

All standard / unproblematic.

### §6.3 No mathlib gap

The Session B target uses only:

* Already-in-tree mg-afcf API (~580 LoC, sound);
* Standard mathlib `Equiv` / `Finset.sum` / `≤`-arithmetic.

**No new mathlib gap surfaces in this scoping.**  Session B is a
pure-in-tree assembly task.

---

## §7 Session B polecat brief

### §7.1 Title

EX-7 Session C-redo Session B — chamber-restricted inner inequality
**execution** (Lean assembly).

### §7.2 Scope

Land in `lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean`
(extend; do **not** create a new file unless ergonomically necessary):

1. `LinearExt'.DirectionalUpClosed` definition (§5.1, ~5 LoC).
2. `RelationPoset.InnerInequalityAdj` definition (§5.2, ~25 LoC).
3. The closure theorem
   `RelationPoset.innerInequalityAdj_of_upClosed_directional` (§5.2,
   ~80–120 LoC):
   * Bijection setup ~10 LoC;
   * Pointwise inequality `(\dagger)` Case A ~10 LoC;
   * Pointwise inequality `(\dagger)` Case B ~30 LoC (uses
     `swapAdj_initialIdeal'_succ_mem_iff` + `hSdir`);
   * Sum-via-bijection step ~15 LoC;
   * Multiply by `N^{adj}` step ~10 LoC.
4. *(Optional, defer-recommended)* Volume-form analogue
   `volumeInnerInequalityAdj` and bridge
   `InnerInequalityAdj_iff_volumeInnerInequalityAdj` (~50 LoC).
   **Recommend NOT including** in Session B; defer to Session C-redo-C
   if needed.
5. *(Optional)* Two named lemmas for downstream consumption:
   * `InnerInequalityAdj_eq_zero_of_addRel_self` (when `Q⁺ = Q⁻`,
     `(\star^{\rm adj})` is trivial): ~10 LoC;
   * `InnerInequalityAdj_of_upClosed_x_eq_a` (specialised to
     `S(I) := T ⊆ I` for `T ⊆ α \ {b}` — the canonical directional-S
     family): ~15 LoC.
   Both optional; include only if fits cleanly.

**Total Session B LoC: ~120–180 LoC** (chamber-restricted core only;
no volume-form bridge).  **Token budget: ~80–120k.**

### §7.3 Acceptance criteria

* `lake build OneThird` green.
* `RelationPoset.InnerInequalityAdj` and
  `RelationPoset.innerInequalityAdj_of_upClosed_directional` are
  exposed; both compile in scope.
* `#print axioms innerInequalityAdj_of_upClosed_directional` returns
  the mathlib classical-foundation triplet only
  (`{propext, Classical.choice, Quot.sound}`); **no new project
  axioms**.
* The original `InnerInequality` (mg-7a4f §5) is **left untouched**
  in `DropsHeadlineMaster.lean` (it's a sound `def`-Prop; no consumer
  unconditionally instantiates it post-mg-b4a7).  **Do NOT delete or
  re-name it** — it remains the gating hypothesis for the
  `_of_inner` reduction.
* No regression on existing `lake build` jobs; net delta ~120–180 LoC
  added.

### §7.4 Trip-wires for Session B

* **Token blow-up >150k.** STOP, surface to PM.  The estimate is
  80–120k; >150k flags an unanticipated obstruction — most likely
  the bijection-sum-rewriting plumbing or the `Finset.sum_bij`-style
  re-indexing.  Fall back to a more verbose direct-pairwise proof
  using `Finset.sum_le_sum_of_ne_zero_le`-style.
* **Pointwise `(\dagger)` Case B has a hidden hypothesis.**  AMBER —
  re-check §3.2 Case B carefully for any implicit reliance on
  `K ⊆ α \ {a, b}`-membership beyond what `(B.1)–(B.2)` give.  If a
  gap surfaces, surface to PM; the directional condition may need a
  small refinement (e.g., extending to `K ⊆ α \ {a}` if `b ∉ K`
  is automatic).
* **Mathlib `Finset.sum_bij` ergonomics.**  AMBER — the re-indexing
  on subtypes via `swapAdjEquiv` may need a couple of `Finset.coe_*`
  / `Subtype.val`-style lemmas.  Standard plumbing; budget +20 LoC.
* **Numerical sanity sub-check (§4.4) finds a violation.**  CRITICAL —
  STOP, mail PM + Daniel URGENT.  This would mean a bug in §3 above
  (or in the directional definition) that the structural proof
  missed.  Recommended: run `scripts/innerInequalityChamberRestricted_check.py`
  (Session B optional pre-check) on the 19-poset coverage before
  committing the Lean proof; budget ~30 minutes.

### §7.5 Out of scope for Session B (Session C-redo-C and beyond)

* **LE-non-adjacent residual closure.**  The chamber-restricted form
  `(\star^{\rm adj})` covers only LE-adjacent extensions.  Brightwell
  §4 closes the residual via chained adjacent transpositions
  (bubble-sort): for `L` with `(a, b)` at non-consecutive positions
  `p_a, p_b` with `p_b > p_a + 1`, find an intermediate element `c`
  at position `p_a + 1` (or `p_b - 1`) with `(a, c)` (or `(c, b)`)
  `Q`-incomparable, swap to get an LE with a smaller gap, recurse.
  ~300–500 LoC, possibly with `stanley_log_supermod` consumption at
  the recursion-depth bound.  **Out of scope for Session B.**
* **Master-theorem analogue.**  Currently the mg-7a4f
  `probEvent'_mono_addRel_of_inner` gates on the *universal*
  `InnerInequality`, which is unsound.  A chamber-restricted
  master-theorem analogue gates on `InnerInequalityAdj` plus the
  LE-non-adjacent residual; both are required, plus a bridging
  argument.  **Out of scope for Session B; Session C-redo-D /
  Session C-redo-E.**
* **Daniel-approval / Option β axiomatization decision.**  If, after
  Session B + Session C-redo-C, the LE-non-adjacent residual is
  found to be sub-α-C-blocking-substantive, PM may surface to Daniel
  for an Option β decision (axiomatize the residual as a 5th axiom).
  **Decision deferred.**  Session B is axiom-free by construction.
* **Brute-force sanity script.**  ~150 LoC Python; useful but not
  required.  **Out of scope for Session B core; recommend as a
  pre-Session B optional sanity step (run once before commit).**

### §7.6 Polecat ticket spec (machine-readable)

```yaml
title: "EX-7 Session C-redo Session B — chamber-restricted inner inequality (Lean execution)"
predecessor: mg-ed38
branch: a8-s2-cont-execution-arc
budget: 120k
loc_estimate: 120-180
files_modified:
  - lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean
  - docs/path-alpha-execution-arc/state.md
files_NOT_modified:
  - lean/OneThird/Mathlib/RelationPoset/DropsHeadlineMaster.lean
  - lean/OneThird/Mathlib/RelationPoset/InnerInequality.lean
  - lean/AXIOMS.md
no_new_axioms: true
acceptance:
  - "lake build OneThird green"
  - "innerInequalityAdj_of_upClosed_directional compiles, no sorries"
  - "#print axioms returns classical triplet only"
trip_wires:
  - "token >150k → STOP, mail PM"
  - "pointwise Case B gap → STOP, mail PM"
  - "mathlib Finset.sum_bij ergonomics → AMBER, +20 LoC budget"
  - "numerical sanity finds violation → CRITICAL, mail PM + Daniel URGENT"
out_of_scope:
  - "LE-non-adjacent residual closure"
  - "master-theorem analogue"
  - "volume-form bridge (defer)"
  - "Option β axiomatization"
```

---

## §8 Trust-surface implications

### §8.1 No new axioms in this scoping pass

Per mg-ed38 brief: "NO new axioms in this scoping pass — that decision
belongs to PM after Session B latex passes."  This deliverable is
purely scoping (latex + Lean signatures + Session B brief); no
`axiom` declarations and no `lean/AXIOMS.md` changes.

The trust surface remains at the post-mg-b4a7 4-axiom configuration:

* `OneThird.LinearExt.brightwell_sharp_centred` (definitively retained
  on the headline trust surface);
* `OneThird.Step8.Case3Enum.case3Witness_hasBalancedPair_outOfScope`
  (definitively retained on the headline trust surface);
* `OneThird.LinearExt.stanley_log_supermod` (temporary; mg-d0fc;
  GREEN per mg-e22f);
* `OneThird.ContinuousFKG.cellMass_AD` (temporary; mg-071b; GREEN
  per mg-d731).

### §8.2 Session B is axiom-free; the LE-non-adjacent residual is the open question

Session B (chamber-restricted `InnerInequalityAdj` + closure) is
**by construction axiom-free**: the LaTeX proof (§3) uses only
mg-afcf swap-bijection lemmas + standard mathlib `Equiv` / `Finset`
arithmetic.  No `stanley_log_supermod`, no `cellMass_AD`, no
continuous AD.

The **LE-non-adjacent residual** (Session C-redo-C, follow-up) is
where an axiomatization decision may arise.  Per Brightwell §4, the
recursive bubble-sort reduction is provable in tree but may consume
~300–500 LoC and possibly `stanley_log_supermod` at the recursion-
depth bound.  PM will assess after Session B lands; if Session
C-redo-C exceeds the polecat-budget envelope (analogously to the
4 confirmations at mg-1f3a/mg-7b85/mg-934f/mg-afcf for the original
chamber-AD aggregation), an Option β-style **axiomatize the residual
master-theorem closure** decision may surface.  **All such decisions
are deferred until after Session B lands.**

### §8.3 Lessons from mg-87de / mg-2f8c / mg-b4a7 (for Session B)

Per mg-b4a7 §1.33 disclosure: "any future Option β-style
axiomatization in the Path α arc should mandatorily run a brute-force
numerical sanity check on small finite instances **before**
Daniel-approval."

Session B does **not** add an axiom, so the mandate doesn't trigger.
**However**, as a defence-in-depth step, the Session B polecat is
recommended to:

* Run `scripts/innerInequalityChamberRestricted_check.py` (Python,
  ~150 LoC, ~30 minutes) on the 19-poset coverage from mg-2f8c
  *before* committing the Lean proof of
  `innerInequalityAdj_of_upClosed_directional`.
* Confirm 0 violations of `(\star^{\rm adj})` for `(a, b)`-directional
  up-closed `S`.
* Document the result in the Session B state.md update (parallel to
  mg-2f8c §3 evidence pattern).

This is *not* a trust-surface gate (Session B has no axiom, so
mg-2f8c-style separate-verification is N/A), but it is a low-cost
sanity check that catches any structural blind spot in §3.

---

## §9 Sub-α-C arc status post-redo-Session-A

**Sub-α-C arc state (post-this-redo-Session-A).**

* **EX-1 (Stanley log-supermod):** GREEN, axiom in tree (mg-d0fc),
  verified GREEN (mg-e22f).
* **EX-3 (`OrderPolytope α`):** GREEN (mg-8c66).
* **EX-4 (Stanley vertex theorem):** GREEN (mg-4831, mg-2442).
* **EX-5 (chamber decomposition):** GREEN (mg-79a9, mg-497d, mg-10d9).
* **EX-6 (continuous FKG/AD):** GREEN, sorry-free (mg-e622, mg-a6ed,
  mg-4adf, mg-8561, mg-7d37); `cellMass_AD` axiomatized (mg-071b),
  verified GREEN (mg-d731).
* **EX-7 (drops headline):** **AMBER (in active redo).**
  - Sessions C.1–C.5 structural infrastructure: GREEN, ~2025 LoC in
    tree (mg-1f3a, mg-934f, mg-7a4f, mg-7b85, mg-afcf).
  - Session C.6 (mg-87de): REVERTED (mg-b4a7) following mg-2f8c
    trip-wire.
  - **Session C-redo Session A (this commit):** chamber-restricted
    target scoped (this document); Session B latex passes.
  - **Session C-redo Session B:** specced (§7); awaiting polecat
    dispatch.
  - **Session C-redo Session C (LE-non-adjacent residual):** deferred;
    Brightwell §4 recursive reduction; ~300–500 LoC; possible
    `stanley_log_supermod` consumption at recursion-depth bound.
  - **Master-theorem analogue:** deferred; gates on the residual
    closure plus a chamber-restricted version of the
    `_of_inner` reduction.
* **EX-8 (case3-port-2):** blocked — depends on EX-7 master theorem
  analogue (deferred per above).
* **EX-9 (Brightwell-port-A):** blocked — depends on EX-7 master
  theorem analogue.
* **EX-10 (axiom-removal):** blocked — depends on EX-8 + EX-9.

**Sub-α-C arc verdict (post-this-redo-Session-A).**  **AMBER, with a
clear forward path.**  The chamber-restricted target sidesteps the
unsoundness window opened by mg-87de (closed by mg-b4a7) and admits a
short LaTeX proof using only in-tree mg-afcf infrastructure.  Session
B is a tractable ~120–180 LoC follow-up, axiom-free.  The
LE-non-adjacent residual remains the substantive open gap, with
Brightwell §4's chained-adjacent-transposition reduction as the
mathematically-clear (Lean-portably-substantive) closure path.  PM's
next Daniel-facing decision — whether to retry an Option β-style
axiomatization at the residual (smaller surface than mg-87de) — is
deferred until after Session B lands, with the mg-b4a7 §1.33
brute-force-sanity-check mandate fully in force.

PM next step: **dispatch Session C-redo Session B polecat** (per §7
brief) to land `InnerInequalityAdj` and
`innerInequalityAdj_of_upClosed_directional` on
`a8-s2-cont-execution-arc`.

---

*End of EX-7 Session C-redo Session A latex-first scoping deliverable
(mg-ed38).*
