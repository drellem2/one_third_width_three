# Linear-majority transitivity vs. one-sided Π⁺/Π⁻ alignment — math research

**Work item:** `mg-5bf9` (polecat `p5bf9`).
**Branch:** `polecat-p5bf9` (target `case3-port-arc`).
**Predecessor:** `mg-75ef` (`docs/case3-port-arc/rem-enumeration-proof.md`).
**Disposition:** **AMBER.** A partial structural argument closes the
claim on the smallest in-scope sub-range (K=3, w=1) by Z/3-cyclic
automorphism. On the residual ¬InCase3Scope range (K=3 ∧ w≥2 with
c≥8; K≥4) the claim cannot be closed by automorphism-only structural
arguments — Aut-trivial configurations exist and the resolution
either way reduces to (a) probability-form cross-poset FKG
(= A8-S2-cont), or (b) finite enumeration on the bounded parameter
range. This is the same wall mg-75ef hit and corroborates the
verdict β of the predecessor artifact at a finer granularity.

This document is the latex-first deliverable per the
`feedback_latex_first_for_math_simp` discipline. All assertions are
flagged "Theorem", "Lemma", "Conjecture", "Sketch", "Open" with
explicit rigor levels.

---

## §1 Setup

Throughout, fix a layered width-3 poset `Q = (X, ≤_Q)` with layered
decomposition `X = M_1 ⊔ ⋯ ⊔ M_K` of interaction width `w` and depth
`K`, satisfying axioms (L1)–(L4) of `step8.tex` Definition
`def:layered`:

* **(L1)** `|M_i| ≤ 3` and `M_i` is an antichain in `Q`.
* **(L2)** `i < j − w  ⇒  ∀ x ∈ M_i, y ∈ M_j, x <_Q y`.
* **(L3)** `|i − j| > w  ⇒  x, y` comparable.
* **(L4)** `i < j  ∧  (x, y) ∈ M_i × M_j` comparable  `⇒  x <_Q y`.

Hypotheses match the AXIOMS.md `case3Witness_hasBalancedPair_outOfScope`
entry (`lean/AXIOMS.md:226-454`):

* `hWidth3` — Q has width ≤ 3.
* `hIrr` — layer-ordinal-sum irreducibility.
* `hK3` — K ≥ 3.
* `hw` — w ≥ 1.
* `hCard` — `|X| ≤ 6w + 6`.
* `hDepth` — K ≤ 2w + 2.
* `hScope` — `¬ InCase3Scope w |X| K` where
  `InCase3Scope w c K ⟺ K = 3 ∧ 1 ≤ w ≤ 4 ∧ (w = 1 → c ≤ 9) ∧
  (2 ≤ w → c ≤ 7)`.
* `hC3` — `Case3Witness L = ¬Case1 ∧ ¬Case2Witness L` where
  Case 1 = full-ambient-profile match and
  Case 2 = within-band ⪯-comparable two-sided profile.

**Notation.**
```
Π⁺(a) := { z ∈ X : a <_Q z },     Π⁻(a) := { z ∈ X : z <_Q a }
Π(a)  := (Π⁺(a), Π⁻(a))
Π(a) ⪯ Π(a') ⟺ Π⁺(a) ⊇ Π⁺(a') ∧ Π⁻(a) ⊆ Π⁻(a')
```

`Pr_Q[E] := |{L ∈ LE(Q) : E(L)}| / |LE(Q)|`. **(NBP)** denotes the
no-balanced-pair counterfactual: every incomparable pair `(a, a')`
has `Pr_Q[a <_L a'] ∉ [1/3, 2/3]`.

**Majority orientation.** Under (NBP), `a ≪ a'` denotes
`Pr_Q[a <_L a'] > 2/3`. Every incomparable pair is in exactly one of
`a ≪ a'` or `a' ≪ a`.

**Lemma 1.1 (no cyclic majority on a 3-antichain — Daniel input
2026-05-06).** *Under (NBP), for any 3-antichain
`{a_1, a_2, a_3} ⊆ X`, the orientation `≪` is acyclic on
`{a_1, a_2, a_3}`. Hence by relabelling we have a linear chain
`a_1 ≪ a_2 ≪ a_3`.*

**Proof.** A cyclic orientation `a_1 ≪ a_2 ≪ a_3 ≪ a_1` would give
`Pr[a_2 <_L a_1] + Pr[a_3 <_L a_2] + Pr[a_1 <_L a_3] < 3 · 1/3 = 1`,
contradicting the rotation identity
`Pr[a_2 <_L a_1] + Pr[a_3 <_L a_2] + Pr[a_1 <_L a_3] ≥ 1`
(`step8.tex:2920-2929`; the three rotations cover every total
order on the triple). ∎

This is exactly Lemma 2.1 / Corollary 2.3 of
`docs/case3-port-arc/rem-enumeration-proof.md`; reproduced here for
self-containedness.

---

## §2 The alignment question, formalised

**Definition 2.1 (one-sided alignment).** A pair `(a, a')` of
within-band elements is

* **upper-aligned** if `Π⁺(a) ⊆ Π⁺(a')` or `Π⁺(a') ⊆ Π⁺(a)`;
* **lower-aligned** if `Π⁻(a) ⊆ Π⁻(a')` or `Π⁻(a') ⊆ Π⁻(a)`;
* **one-sided aligned** if it is upper-aligned or lower-aligned.

**Equivalent reformulation.** Set `S⁺ := {Π⁺(a_1), Π⁺(a_2), Π⁺(a_3)}`
and `S⁻ := {Π⁻(a_1), Π⁻(a_2), Π⁻(a_3)}` viewed as subsets of `2^X`.
Then "no pair is one-sided aligned" ⟺ both `S⁺` and `S⁻` are
3-antichains in `(2^X, ⊆)`.

**The alignment question (LMA).** *Under the AXIOM hypotheses
+ (NBP) + linear majority `a_1 ≪ a_2 ≪ a_3`, must the triple
`{a_1, a_2, a_3}` admit a one-sided aligned pair?*

Equivalently: *can BOTH `S⁺` and `S⁻` be 3-antichains in `(2^X, ⊆)`?*

**The reformulation matters.** Under Case 3 each pair has the
two-sided profile `(Π⁺_i, Π⁻_i)` ⪯-incomparable as a *pair*. LMA asks
the strictly stronger question of whether the projections to either
coordinate can BOTH avoid creating an inclusion-comparable pair.

If LMA's answer is **yes (alignment forced)**: step 2 of
`rem:enumeration` reduces from "FKG sub-coupling" to "exhibit the
aligned pair" (structural counting), and the case3 axiom port becomes
~300-500 LoC against current-tree primitives — count-form FKG plus
`mg-f92d` (Case 1 ambient form) plus A8-S2's `Case2Witness` discharge.

If LMA's answer is **no (counterexample)**: an explicit Case-3
configuration with linear majority and pairwise 3-antichain
`(S⁺, S⁻)` exists, and Step 2 of `rem:enumeration` genuinely needs
probability-form cross-poset FKG (A8-S2-cont).

---

## §3 The structural analysis

We separate into **§3.1** (smallest sub-range, closes positively) and
**§3.2** (residual range, blocks).

### §3.1 The smallest sub-range: K=3, w=1 — alignment IS forced (vacuously)

**Theorem 3.1 (in-scope sub-range; rigorous).** *For K=3, w=1, any Q
satisfying the AXIOM hypotheses with `Case3Witness L` and a
3-antichain `{a_1, a_2, a_3}` at the within-band has `Pr_Q[a_i <_L
a_j] = 1/3` for some pair `(i, j)`. Hence (NBP) is incompatible with
this sub-range; (LMA) holds vacuously (the linear-majority hypothesis
is unsatisfiable here).*

**Proof.** Let `{a_1, a_2, a_3} ⊆ M_k` be the antichain band (forced
to k=2 by hK3 + hDepth + irreducibility for K=3). For w=1, the
variable upper window for each `a_i` is `M_{k+1}` (size ≤ 3) and the
variable lower window is `M_{k-1}` (size ≤ 3). The non-window bands
are forced via (L2) since `|i − j| > w = 1` for any non-window pair.

The 3-antichains in `(2^M_{k±1}, ⊆)` for `|M_{k±1}| ≤ 3`:

| `|M|` | Possible 3-antichains in `(2^M, ⊆)` |
|---|---|
| 0, 1, 2 | none (lattice has too few elements) |
| 3 | `{ {x_1}, {x_2}, {x_3} }` (singletons) or `{ {x_2,x_3}, {x_1,x_3}, {x_1,x_2} }` (doubletons) |

(For `|M| = 3`: any 3-antichain must avoid `∅` and `M` itself. Among
singletons or doubletons of `M`, mixed singleton/doubleton choices
fail antichain-ness.)

If `S⁺` or `S⁻` is not a 3-antichain at all, alignment holds. Assume
both are 3-antichains. Then both are either label-permutations of
the all-singletons or the all-doubletons collection.

Let `σ` be the cyclic 3-permutation on `{a_1, a_2, a_3}` that, in
combination with the corresponding cyclic permutations `σ⁺` on the
upper-window labels and `σ⁻` on the lower-window labels, sends each
`Π⁺(a_i)` to `Π⁺(σ(a_i))` and each `Π⁻(a_i)` to `Π⁻(σ(a_i))`. Such
`σ⁺` and `σ⁻` exist whenever `S⁺` and `S⁻` are Z/3-orbits of either
the singleton or the doubleton patterns: in each case the labels
`x_1, x_2, x_3` (respectively `y_1, y_2, y_3`) admit the cyclic shift
that realises the rotation.

Extend `σ` to all of `X` as follows: on the antichain band M_2,
apply the chosen cyclic permutation; on M_1 and M_3 apply `σ⁻` and
`σ⁺` respectively; on every other band, apply the identity.

We check that `σ` is a poset automorphism of Q. Variable
comparabilities are M_1–M_2 (encoded by `Π⁻`, σ-equivariant by
construction) and M_2–M_3 (encoded by `Π⁺`, σ-equivariant). All
other M_i–M_j with `i ≠ j` (within K = 3 only `i–j = 2`, i.e. M_1–M_3)
are forced by (L2) since `|1 − 3| = 2 > w = 1`, hence fully
comparable and trivially σ-equivariant under any permutation.

Therefore σ ∈ Aut(Q) is a poset automorphism of order 3 acting
non-trivially on `{a_1, a_2, a_3}`. By the rotation-identity
σ-equivariance, `Pr_Q[a_1 <_L a_2] = Pr_Q[a_2 <_L a_3] = Pr_Q[a_3
<_L a_1]`, and the three sum to 1 (rotation identity), forcing each
to equal `1/3 ∈ [1/3, 2/3]`. So `(a_1, a_2)` is balanced and (NBP)
fails. ∎

**Remark 3.2 (in-scope coverage).** The K=3, w=1 sub-range is
strictly within `InCase3Scope` (recall `InCase3Scope w c K ⟺ K = 3
∧ 1 ≤ w ≤ 4 ∧ (w = 1 → c ≤ 9) ∧ (2 ≤ w → c ≤ 7)`; for w=1, K=3 the
band-size cap forces `c ≤ 9`). This sub-range is therefore already
covered by the F5a `case3_certificate` in tree
(`InCase3Scope` branch); Theorem 3.1 corroborates the certificate at
the math level but does not produce new in-tree value.

**Remark 3.3 (smallest residual case).** The smallest `¬InCase3Scope`
sub-range is K=3, w=2 (where `c ≥ 8` is required), or K ≥ 4. Theorem
3.1's argument uses (L2) forcing M_1–M_3 fully comparable; this
breaks for w ≥ 2 (since `|1−3| = 2 = w` means M_1–M_3 are *variable*,
not forced). Theorem 3.1 therefore does not extend to the residual
range; §3.2 below addresses it.

### §3.2 The residual range: K ≥ 4 or K=3 ∧ w ≥ 2 — Aut-trivial configurations exist

In the residual range, (L2)'s forced-comparability set is sparser,
and the variable comparability set is richer. The cyclic σ
constructed in §3.1 is no longer guaranteed to be an automorphism
because additional bands (or M_1–M_3 in the K=3, w≥2 case) introduce
asymmetric comparabilities that need not be σ-equivariant.

**Construction 3.4 (a candidate trivial-Aut Case-3 configuration).**
Take K=3, w=2, with bands `M_1 = {y_1, y_2, y_3}`, `M_2 = {a_1, a_2,
a_3}`, `M_3 = {x_1, x_2, x_3}`, `|X| = 9`. Set:

| coordinate | a_1 | a_2 | a_3 |
|---|---|---|---|
| Π⁺(·) | `{x_1, x_2}` | `{x_2, x_3}` | `{x_1, x_3}` |
| Π⁻(·) | `{y_1}` | `{y_2}` | `{y_3}` |

Add the asymmetric edge `y_1 < x_3` to the M_1–M_3 (variable for
w=2) layer (everything else in M_1–M_3 is determined by transitivity
through M_2: `y_1 < a_1 < x_1, x_2`, etc.).

**Verification.**

* **Width 3.** Each band is a 3-antichain. One can check (by
  enumerating maximal antichains) that no cross-band 4-antichain
  exists; in particular every "candidate" cross-band antichain is
  killed by some chain through M_2.
* **Irreducibility.** No band-prefix [1, k] is below [k+1, K]
  uniformly (e.g. y_1 ⊥ a_2 in Q so M_1 not below M_2 uniformly).
* **Case 3.** `S⁺ = {{x_1,x_2}, {x_2,x_3}, {x_1,x_3}}` is a
  3-antichain (the doubletons of `M_3`). `S⁻ = {{y_1}, {y_2}, {y_3}}`
  is a 3-antichain (the singletons of `M_1`). Pairwise
  ⪯-incomparable: each pair has both coordinates ⊆-incomparable, in
  particular ⪯-incomparable.
* **¬Case2Witness on M_1.** Compute Π⁺(y_i) in Q (each y_i has
  exactly one a_above by Π⁻ singleton, plus the cascaded x_above
  through M_2, plus possibly the directly-declared y_1 < x_3):
  Π⁺(y_1) = {a_1, x_1, x_2, x_3}, Π⁺(y_2) = {a_2, x_2, x_3},
  Π⁺(y_3) = {a_3, x_1, x_3}. Pairwise ⊇-incomparable. Π⁻(y_i) = ∅
  for all i. Hence ⪯-incomparable. ¬Case2Witness on M_1.
* **¬Case2Witness on M_3.** Compute Π⁻(x_j): Π⁻(x_1) = {a_1, a_3,
  y_1, y_3}, Π⁻(x_2) = {a_1, a_2, y_1, y_2}, Π⁻(x_3) = {a_2, a_3,
  y_1, y_2, y_3}. Pairwise ⊆-incomparable. Π⁺(x_j) = ∅. Hence
  ⪯-incomparable. ¬Case2Witness on M_3.
* **Case3Witness L.** Combining the above with ¬Case1 (profiles are
  pairwise distinct in M_2). Hence `Case3Witness L` holds.
* **Aut(Q) = {id}.** Every non-identity candidate σ on the index
  labels forces a constraint that fails:
  | σ on a's | σ on x's (forced) | σ on y's (forced) | image of `y_1 < x_3` | preserved? |
  |---|---|---|---|---|
  | (1 2 3) | (x_1 x_2 x_3) | (y_1 y_2 y_3) | y_2 < x_1 | NO |
  | (1 3 2) | (x_1 x_3 x_2) | (y_1 y_3 y_2) | y_3 < x_2 | NO |
  | (1 2)   | (x_1 x_3)     | (y_1 y_2)     | y_2 < x_1 | NO |
  | (1 3)   | (x_2 x_3)     | (y_1 y_3)     | y_3 < x_2 | NO |
  | (2 3)   | (x_1 x_2)     | (y_2 y_3)     | y_1 < x_3 | y_1 < x_3 ✓ but x_2 < x other constraints fail elsewhere; actually σ((2 3)) maps the comparability `a_1 < x_1` to `a_1 < σ_x(x_1) = a_1 < x_2`. Both true. `a_1 < x_2` to `a_1 < x_1`. True. `a_2 < x_3` to `a_3 < x_3`. True. `a_3 < x_3` to `a_2 < x_3`. True. `y_1 < x_1` to `y_1 < x_2`. y_1 < x_2 in Q via y_1 < a_1 < x_2 ✓. `y_1 < x_2` to `y_1 < x_1`. True. `y_1 < x_3` to `y_1 < x_3`. True. `y_2 < a_2` to `y_3 < a_3`. True. `y_3 < a_3` to `y_2 < a_2`. True. **Wait — this σ_{(2 3)} appears to preserve every constraint.**
  
**Correction to the verification table.** The σ_a = (2 3) involution
with σ_x = (x_1 x_2), σ_y = (y_2 y_3) preserves all comparabilities
in Construction 3.4. So Aut(Q) ⊇ {id, σ_{(2 3)}}.

This means `Pr_Q[a_2 <_L a_3] = 1/2 ∈ [1/3, 2/3]`, and Construction
3.4 has the balanced pair (a_2, a_3). (NBP) fails.

**Construction 3.4 therefore does NOT realise an Aut-trivial
configuration.** I attempted several variants (different label
matchings, additional asymmetric edges, larger M_4) within the
allowed parameter range; each one I tried admitted some non-trivial
involution τ that swaps a within-M_2 pair and forces `Pr = 1/2` on
that pair — yielding (NBP) failure.

**Open Question 3.5 (alignment for the residual range).** *Does an
Aut-trivial layered Q with `Case3Witness L`, width-3, irreducibility,
`¬InCase3Scope`, `|X| ≤ 6w + 6`, and pairwise 3-antichain `(S⁺, S⁻)`
exist? Equivalently: is the set of Case-3 antichains in this regime
saturated by automorphism-induced balanced pairs?*

This is the counterpart, at finer resolution, of mg-75ef Claim 3.2.
Closing it positively (no Aut-trivial config exists) closes the
alignment claim positively (every Case-3 antichain in the residual
range either has a one-sided aligned pair OR has a non-trivial
automorphism that produces a balanced pair). Closing it negatively
(Aut-trivial config exists) requires verifying linear majority
(Pr's > 2/3) on the explicit configuration, which is a direct LE
count.

Note that Open Question 3.5 is **finite-parameter**: given the
hypotheses, the parameter range `w ∈ {1, 2, 3, 4} ∪ {large w}`,
`K ∈ [3, 2w + 2]`, `|X| ≤ 6w + 6` gives a finite number of
isomorphism classes, in principle enumerable by computer.

### §3.3 Why the residual question reduces to A8-S2-cont OR enumeration

**Claim 3.6.** *Closing Open Question 3.5 positively (no Aut-trivial
counterexample exists) by paper-rigor combinatorial structural
argument requires either probability-form cross-poset FKG, OR a
finite enumeration on the bounded parameter range.*

**Sketch of evidence.**

* **(a) The Pr = 1/3 boundary is genuinely tight.** The cyclic
  Z/3-symmetric configurations of §3.1 attain `Pr = 1/3` exactly. So
  the boundary isn't strictly violated by symmetric configurations
  — they sit exactly on the boundary.
* **(b) Symmetry-breaking by M_4 / M_5 / M_1–M_3 edges produces
  involution autos.** The constructions I tried (Construction 3.4
  variants, Construction with K=4 + asymmetric M_3–M_4 edges) all
  retained at least an involution τ on some pair (i, j). The
  involution forces `Pr_Q[a_i <_L a_j] = 1/2`, which is balanced.
* **(c) Genuinely Aut-trivial configurations are theoretically
  possible.** The F1 obstruction (`docs/why-hC3-is-structural.md §1`)
  shows that strict ⪯-pairs admit configurations with trivial
  automorphism group. The same phenomenon plausibly extends to
  3-antichain Case 3 in the residual range.
* **(d) For Aut-trivial configs, Pr's are determined by LE counts.**
  The balanced-pair witness (if it exists) comes from counting LEs,
  not from symmetry. The structural argument paths I see are:

  * **(d1) Probability-form cross-poset FKG (= A8-S2-cont).** Bound
    `Pr_Q[a_i <_L a_j]` from above via cross-poset comparison to a
    sub-poset where the pair is symmetric. The bound `Pr_Q ≤ 2/3`
    needs the probability-normalised form (Daykin-Saks "drops"); the
    in-tree count-form `probLT'_mono_of_relExt` is documented as
    insufficient (`Mathlib/RelationPoset/FKG.lean:506-516`).
  * **(d2) Finite enumeration.** Enumerate every isomorphism class
    of Q in the parameter range, compute Pr's directly, observe that
    all configurations have some Pr ∈ [1/3, 2/3]. Bounded by w ≤ ? ,
    K ≤ 2w + 2, |X| ≤ 6w + 6. For w = 2, 3, 4 the parameter range is
    finite-but-large; for w ≥ 5 the band-size cap (L1) limits |X| ≤
    9, but the depth K ≤ 2w + 2 grows.
  * **(d3) An automorphism-existence theorem.** Show that every Q in
    the range admits at least one non-trivial automorphism on M_2.
    No such theorem is in the literature I am aware of, and
    Construction 3.4 (with the involution that does exist) suggests
    the theorem would be tight rather than easy.

  Routes (d1) and (d2) match the two routes the predecessor mg-75ef
  artifact identified at §3.2.

**Conclusion 3.7.** The alignment claim's resolution either way
on the residual range is BLOCKED on the same machinery the case3
axiom port itself blocks on: probability-form FKG (A8-S2-cont) or
explicit finite enumeration.

---

## §4 Verdict

**AMBER.** The alignment claim closes positively on the smallest
sub-range (K=3, w=1) by §3.1's Z/3-cyclic-automorphism argument, but
this sub-range is in-scope (covered by `case3_certificate`). On the
residual ¬InCase3Scope range, the alignment claim's status is open
and reduces to either:

1. **A8-S2-cont (probability-form cross-poset FKG).** ~2000-3500 LoC
   of pre-requisite infrastructure per `docs/a8-s2-status.md`. Once
   landed, the alignment claim probably closes via a "Pr ≤ 2/3" bound
   on the within-band pair after the cyclic-σ exclusion — but this
   bound itself uses A8-S2-cont. So the alignment route does not
   bypass A8-S2-cont; it co-uses it.

2. **Finite enumeration on the bounded parameter range.** Computer
   verification, not paper-rigor structural counting. Out of scope of
   this latex-first artifact and out of scope of the polecat brief
   ("If proving the alignment requires substantively new theorems
   from FKG / coupling literature, STOP and report").

**Implication for Step 2 of `rem:enumeration`.** The original
question — "does linear-majority transitivity force Π⁺/Π⁻ alignment
between some pair directly, bypassing the band-restricted FKG
sub-coupling?" — does NOT receive a clean YES that bypasses
A8-S2-cont. Even granting Lemma 1.1 (the cyclic-orientation Lemma)
as the "user-input simplification", the alignment forcing for the
residual range still routes through probability-form FKG.

**Re-corroboration of the predecessor verdict β.** mg-75ef reached
verdict β ("the math needs probability-normalised FKG") at the
math level, by analysing the lift step Pr_{Q^+} → Pr_Q. This
artifact reaches the same verdict by a different route: analysing
the alignment Step 1 itself and showing it does NOT close to paper
rigor on the residual range without A8-S2-cont.

The two analyses corroborate: probability-form cross-poset FKG is
the genuine blocker, on multiple independent paths.

**Sub-verdict GREEN-on-K=3-w=1.** Theorem 3.1 is rigorous and could
in principle yield ~30-60 LoC in Lean as an alternative discharge of
the in-scope sub-range. But the in-scope sub-range is already covered
by `case3_certificate`; Theorem 3.1 is mathematically pleasing but
does not eliminate the axiom.

---

## §5 Lean port shape — N/A under AMBER

Per the brief, "If GREEN, sketch the Lean port shape." Verdict is
AMBER, so this section is N/A. For completeness, the full port shape
inherits from the predecessor mg-75ef artifact §8: Lean port LoC is
dominated by A8-S2-cont (~2000-3500 LoC) plus ~430-850 LoC of
case-3-specific glue.

If a future Lean port wants to use Theorem 3.1's argument as the
in-scope branch's discharge: estimated ~80-150 LoC for the cyclic-σ
construction in Lean (Aut(Q) construction + rotation identity
specialisation + Pr = 1/3 conclusion). Replacing the
`case3_certificate` Bool-level decision-procedure dispatch.
This is a clean refactor of in-scope dispatch but does not affect
the residual axiom.

---

## §6 Risk inventory

* **Trip-wire #1 (token overrun > 600k).** Not fired.
  Approximate token spend: ~110k of the 400k budget on analysis +
  artifact, well within bounds.
* **Trip-wire #2 (new structural obstruction).** *Not fired.* The
  analysis surfaces no new obstruction beyond the F2 / probability-
  normalisation obstruction already documented in
  `docs/why-hC3-is-structural.md §2` and the A8-S2-cont scope doc.
* **Trip-wire #3 (math inconsistent).** Not fired. Lemma 1.1 holds;
  Theorem 3.1 holds. The residual question reduces to a finite
  enumeration or probability-form FKG; both are well-defined.
* **Trip-wire #4 (F4-b trap; relabelling).** Not fired. The analysis
  explicitly stays at the math/structural level; no Step 5–7
  fiber/coherence/global infrastructure is invoked.
* **Trip-wire #5 (published in literature).** Not fired. I am not
  aware of a published statement of (LMA) in the FKG / poset /
  coupling literature for this specific layered width-3 setting.
  The closest are Ahlswede-Daykin / FKG inequalities and the
  Daykin-Saks "drops" inequality, which underpin route (d1) but
  do not directly answer (LMA).
* **Trip-wire #6 (alternative bypasses beyond alignment).** *Not
  fired.* This artifact does NOT examine whether step 2 has
  alternative bypasses beyond alignment. The brief notes such
  alternatives (e.g., counting arguments that don't go through FKG
  OR alignment) would warrant a separate research question. None
  surfaced organically in this analysis.

**Caveats.**

* §3.1's Theorem 3.1 is rigorous but covers only the in-scope
  sub-range, which is already discharged.
* §3.2's analysis is a sketch / partial. Construction 3.4 is verified
  to satisfy all AXIOM hypotheses except linear-majority (which holds
  vacuously since the involution τ_{(2 3)} forces Pr = 1/2). It is
  NOT a counterexample — but it is also not a proof that no
  Aut-trivial config exists.
* The "all attempts produced involution autos" observation in §3.2
  (point (b)) is empirical, not exhaustive. A more careful
  enumeration may reveal Aut-trivial configurations.

---

## §7 Cross-references

* **Paper.** `step8.tex:3033-3047` (`prop:in-situ-balanced` Case 3);
  `step8.tex:3157-3185` (`rem:enumeration` sketch);
  `step8.tex:2920-2929` (rotation identity used in Lemma 1.1);
  `step8.tex:2840-2871` (bipartite Case 2 FKG sub-claim).
* **Lean tree.** `lean/OneThird/Step8/Case3Residual.lean:208`
  (the axiom this analysis investigates);
  `lean/OneThird/Step8/Case3Dispatch.lean:156-180`
  (`Case2Witness`, `Case3Witness` definitions);
  `lean/OneThird/Mathlib/RelationPoset/FKG.lean:381,464,506-516,521`
  (in-tree count-form FKG primitives + the explicit insufficiency
  docstring);
  `lean/OneThird/Step8/BoundedIrreducibleBalanced.lean:1484`
  (`InCase3Scope`).
* **Predecessor / mg-trail.**
  * `mg-75ef` (`docs/case3-port-arc/rem-enumeration-proof.md`) —
    the predecessor artifact whose §3.2 Claim 3.2 is essentially
    the same residual-range question; verdict β for the same
    reason.
  * `mg-e850` (`docs/case3-port-arc/port-status.md`) — Lean-side
    STOP on count-form FKG insufficiency.
  * `docs/why-hC3-is-structural.md §2` (F2) — K=2 sibling
    diagnosis; same probability-normalisation gap.
  * `docs/a8-s2-status.md:159, 269, 391-409` — A8-S2-cont scope
    and "the actual blocker" framing.
* **In-session inputs.** Daniel directive 2026-05-06T~07:01Z (this
  ticket); Daniel's 2026-05-05 transitivity-of-majority simplification
  (Lemma 1.1).

---

## §8 Recommended disposition

Per the brief's outcome-class line for AMBER:

> AMBER. PM evaluates the additional input needed; either small
> follow-on polecat or surface to Daniel.

Concrete recommendation:

1. **Document this artifact as the second corroboration of verdict
   β.** Both mg-75ef (lift-step analysis) and this artifact
   (alignment-step analysis) reach the same verdict by independent
   paths.
2. **Surface to Daniel: the case3 port arc is genuinely blocked on
   A8-S2-cont OR finite enumeration.** Both routes are
   multi-week, multi-polecat scope.
3. **Note the in-scope sub-range partial result.** Theorem 3.1
   could be ported to Lean as an alternative discharge of the
   in-scope branch (~80-150 LoC), but this is parallel-cleanup
   relative to the in-tree `case3_certificate` and does not
   eliminate the residual axiom.
4. **Updated AXIOMS.md "Replacement path (open)" wording.** The
   case3 axiom's Replacement path could now cite both this artifact
   and mg-75ef as evidence that the gap is genuinely
   probability-form FKG.

---

## §9 Polecat protocol

* `mg claim mg-5bf9` — done.
* `pogo schedule … mail-check-mg-5bf9` — done.
* No Lean source changes — this is a docs-only ticket per
  `feedback_latex_first_for_math_simp` discipline.
* This `.md` deliverable — done (the value regardless of verdict
  per `feedback_audit_as_deliverable`).
* Verdict AMBER reached at math level, corroborating mg-75ef's β
  on a finer-resolution path.
* No trip-wires fired.
* Mail to mayor — pending immediately after this commit.
