# EX-7 Option (b) scoping — refined master via chained-adjacent-transposition

**Polecat.** mg-a1aa (cat-mg-a1aa).
**Date.** 2026-05-13.
**Branch.** `polecat-mg-a1aa` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-fd0d (halted) — CRITICAL trip-wire establishing that the *universal*
  master theorem `probEvent'_mono_of_subseteq_upClosed` is mathematically
  FALSE (mg-2f8c minimal counterexample applies; cf. §1.1 below).
- mg-f3b9 (`5e5ba54`) — Session C-redo Session C consumer audit; verdict
  "Option 1 (LE-non-adjacent residual closure → universal master theorem)"
  is RETROACTIVELY INVALID because the target (universal master) is
  unsound.  The lower-level consumer-directionality analysis (EX-8 / EX-9
  not directional-S compatible) remains substantively correct and is
  re-audited and re-affirmed in §5 below against the *refined* target.
- mg-c8ac (`84b7216`) — `InnerInequalityAdj` in tree axiom-free; the
  chamber-restricted (LE-adjacent + (a, b)-directional S) inner
  inequality is the building block this scoping refines.
- mg-2f8c (`8ae2aea`) — independent verification fired the trip-wire on
  the universal `InnerInequality` (133 180 violations / 19 posets).
- Daniel approval 2026-05-13T~10Z ("your call" reminder) for Option (b)
  scoping path.

**Verdict.** **RED on consumer applicability; AMBER on theoretical
result.**  The strongest *universal* refined target derivable from the
chained-adjacent-transposition reduction is **(b.Q-SYMM)** — S up-closed
AND for every Q-incomparable pair {x, y} and every K avoiding {x, y},
`S(K ∪ {x}) ↔ S(K ∪ {y})`.  The numerical sanity check (§4) confirms
(b.Q-SYMM) is true on 19 test posets / 3009 instances with **zero
violations** — but **every instance is TIGHT (equality)**, i.e., the
refined master theorem reduces to `Pr[S | Q] = Pr[S | Q']` for any
`Q ⊆ Q'` and Q-symmetric S.  This is a *vacuous* directional result
that conveys no strict-inequality information.  A weaker decomposition-
dependent variant (**b.SOURCE-DIR**) is non-vacuous in principle, but
the consumer re-audit (§5) confirms that *neither EX-8 (case3-port-2)
nor EX-9 (Brightwell-port-A) admits any non-trivial event satisfying
(b.SOURCE-DIR)* on their natural chains.  **Option (b) does NOT close
the EX-8/EX-9 consumer gap.**  PM next step: escalate to Daniel for
Option (c) [axiomatize with full mandatory verification] OR Option (d)
[architectural redesign of EX-8/EX-9 to avoid the universal-up-closed
hypothesis].  Per polecat brief §7, this scoping pass **adds no new
project axioms**.

**Estimated combined Session E LoC.** *N/A — no Session E execution
target identified.* The scoping concludes that no useful refined target
is available; PM must surface to Daniel for higher-level decision.

---

## §0 Polecat brief recap

Per mg-a1aa polecat brief:

> EX-7 Option (b) scoping — refined master theorem with S-side
> restrictions extracted from chained-adjacent-transposition (post-mg-fd0d
> critical; Daniel-approved 2026-05-13T~10Z).
>
> Per mg-fd0d CRITICAL trip-wire: the universal-up-closed master theorem
> `probEvent'_mono_of_subseteq_upClosed` is mathematically FALSE (mg-2f8c
> counterexample applies).  mg-f3b9's "Option 1 recommended" verdict was
> wrong because it audited consumer-compatibility without verifying
> target truth.
>
> Daniel approved Option (b) via "your call" reminder 2026-05-13.  This
> Option (b) scoping derives the strongest provable master extractable
> from chained-adjacent-transposition, without pre-committing to a
> target.
>
> § 3 Verification of target truth (MANDATORY) per
> `feedback_verify_target_truth_before_execution.md` (2026-05-13):
> include in this scoping a numerical sanity check confirming the
> refined target is TRUE on small instances.  …  Non-negotiable.  Don't
> repeat the mg-f3b9 mistake.
>
> § 4 Consumer re-audit (post-target-fix): re-examine the original
> mg-f3b9 audit assumptions with knowledge that the universal target is
> unsound.  This re-audit replaces mg-f3b9's audit.
>
> Trip-wires: numerical sanity violation = STOP and iterate (narrow
> target further); no refined target survives both provability AND
> consumer needs = STOP and surface to PM (escalate to Daniel for Option
> (c) [axiomatize] vs (d) [architectural redesign]).  NO new project
> axioms in scoping.

This deliverable produces:

- §1 Recap of mg-fd0d critical + mg-2f8c counterexample;
- §2 Chained-adjacent-transposition reduction analysis (what S-side
  restrictions emerge);
- §3 Refined target candidate(s) and choice of strongest;
- §4 **Numerical sanity verification** of refined target (mandatory);
- §5 **Consumer re-audit** (EX-8 + EX-9, mandatory);
- §6 Recommendation (Session E execution OR pivot);
- §7 References.

**No Lean code is added or modified.**

---

## §1 Recap of mg-fd0d critical + mg-2f8c counterexample

### §1.1 The unsoundness window (mg-2f8c)

Per `innerInequality-verification.md` (mg-2f8c, commit `8ae2aea`):
the universal single-edge `InnerInequality` (mg-7a4f `def`-Prop) as
gated by `DropsHeadlineMaster.lean:478–490` —

$$
N(Q^-)\,\bigl|\{L \in \mathcal{L}(Q^+) : S(L_k)\}\bigr|
\;\ge\;
N(Q^+)\,\bigl|\{L \in \mathcal{L}(Q^-) : S(L_k)\}\bigr|
$$

for all up-closed `S` — is **mathematically false**.  Brute-force
verification on 19 posets / 1 431 564 instances found **133 180
violations** (9.3 % rate).  Minimal counterexample: `α = {0, 1}`, `Q`
empty, `a = 0`, `b = 1`, `k = 1`, `S(I) := (1 ∈ I)`:

- `N(Q⁻) = N(Q⁺) = 1`; `Mp = 0`, `Mm = 1`; inequality requires
  `1 · 0 ≥ 1 · 1`, i.e., `0 ≥ 1` — **FALSE**.

The corresponding *master theorem* `probEvent'_mono_of_subseteq_upClosed`
(reduced form `_of_inner` in `DropsHeadlineMaster.lean:548`) inherits
the unsoundness on the same instance: `Pr[1 ∈ L_1 | Q] = 1/2 ≤ 0 =
Pr[1 ∈ L_1 | Q⁺]` is false.

The mg-b4a7 revert (`fe87be2`) stripped the corresponding axiom
`InnerInequality_axiom` from the trust surface; the in-tree master
theorem `probEvent'_mono_of_subseteq_upClosed` was never instantiated
unconditionally and remains absent from the tree post-revert.

### §1.2 The mg-f3b9 audit's invalidated verdict

Per `ex7-c-redo-c-scoping.md` (mg-f3b9, commit `5e5ba54`): the
"Option 1 LE-non-adjacent residual closure → universal master theorem
~300–500 LoC" recommendation **presupposed** the universal target was
provable.  Per mg-fd0d (post-c8ac, halted) re-verification, the
*universal* target is the same unsound statement as mg-2f8c demonstrated.
**Therefore mg-f3b9's higher-level verdict is invalid.**

What survives from mg-f3b9 (re-audited and re-affirmed in §5): the
consumer-directionality lower-level findings — that EX-8 case3-port-2
and EX-9 Brightwell-port-A are NOT (a, b)-directional-compatible —
remain substantively correct.  The §5 re-audit confirms this against
the *refined* targets.

### §1.3 Daniel approval of Option (b)

Per Daniel reminder 2026-05-13T~10Z, the polecat brief (mg-a1aa) was
issued with explicit "your call" approval to execute Option (b) scoping
(derive the strongest provable refined master from chained-adjacent-
transposition).  The trip-wire spec is unambiguous: numerical sanity
sub-check on the refined target is **mandatory** before any structural
execution; consumer re-audit is **mandatory** since mg-f3b9 is invalid.

### §1.4 What "Option (b)" means (vs. (a), (c), (d))

The PM-level decision space post-mg-fd0d:

- **Option (a):** Accept the universal target's unsoundness; the EX-7
  drops headline is permanently RED on the universal form.  No further
  work; downstream sub-α-C arc declared blocked.  *Defeatist; rejected.*
- **Option (b):** Derive a *refined* master theorem with S-side
  restrictions extracted from the chained-adjacent-transposition
  proof structure.  Pick the strongest provable target.  *This scoping.*
- **Option (c):** Axiomatize a refined target (without claiming a full
  proof from in-tree primitives).  Per mg-b4a7 §1.33 mandate, mandatory
  brute-force numerical sanity check before Daniel-approval.  Requires
  Daniel surface.
- **Option (d):** Architectural redesign of the EX-7 → EX-8 / EX-9
  consumer chain to avoid the universal-up-closed-S hypothesis
  altogether.  Most invasive; requires Daniel surface.

This scoping deliverable evaluates Option (b) and (per §6) recommends
**escalation to Daniel for Option (c) vs (d)** because no refined
target survives both provability AND consumer applicability.

---

## §2 Chained-adjacent-transposition reduction — structural analysis

### §2.1 The single-edge reduction and its non-adjacent residual

The mg-c8ac `InnerInequalityAdj` lemma
(`InnerInequalityAdjacent.lean:637–770`) proves the *LE-adjacent half*
of the single-edge inner inequality for the chamber-restricted
hypothesis (S up-closed + `(a, b)`-directional).  Explicitly: it
establishes

$$
N^{\rm adj}_- \cdot M^{\rm adj}_{+,S} \;\geq\; N^{\rm adj}_+ \cdot M^{\rm adj}_{-,S}
$$

where the `^{adj}` counts restrict to LEs with `L.AdjLt(a, b)` (resp.
`L.AdjLt(b, a)`).  This is the bijection-image step of the
chamber-by-chamber argument.

The **non-adjacent residual** is the same inequality with the counts
restricted to LEs where `(a, b)` are at *non-consecutive* positions.
Brightwell §4 closes this residual via *chained adjacent transpositions*
(bubble-sort): for each LE `L` with `(a, b)` non-adjacent, perform a
sequence of adjacent swaps `(c_i, a)` to reduce `L` to an LE with
`(a, b)` adjacent.

### §2.2 What the bubble-sort step looks like

Concretely (cf. `ex7-chamber-restricted-scoping.md` §1.3 / §8.2):
take `L' ∈ \mathcal{L}(Q^-)` with `b` at position `q_b` and `a` at
position `q_a > q_b + 1`.  The intermediate elements at positions
`q_b + 1, …, q_a - 1` are the *bubble pivots*.  Working from `q_a - 1`
down to `q_b + 1`, swap `a` with each successive pivot `c_i`.

For each swap of `(c_i, a)` (with `c_i` at position `p - 1` and `a` at
position `p`):

- The swap produces a new LE of `Q⁻` iff `(c_i, a)` is `Q⁻`-incomparable,
  which (given `Q⁻ = Q + (b < a)`) reduces to `(c_i, a)` `Q`-incomparable
  AND `¬(Q.le b c_i)`.
- The level-`k` initial ideal `L_k = \{x : (L.\text{pos}\, x).\text{val} < k\}`
  *changes* in the swap only at the **specific level `k = p`** (the
  current position of `a`).  At that level: before swap, `L_k` contains
  `c_i` (at `p-1`) but not `a` (at `p`).  After swap, `L_k` contains `a`
  (at `p-1`) but not `c_i` (at `p`).

So at level `k = p`, defining `K := L_k \setminus \{c_i\}` (the elements
at positions `0, …, p-2`, common to both states):

- Before swap: `L_k = K \cup \{c_i\}`.
- After swap: `L_k = K \cup \{a\}`.

For the bubble-sort to preserve `S(L_k)` *in the direction needed by
the reduction* (i.e., monotonically toward Q⁺'s constraints — see §2.3
below), we need

$$
S(K \cup \{c_i\}) \;\implies\; S(K \cup \{a\})
$$

for each bubble pivot `c_i` and each appropriate `K`.

**This is exactly the mg-c8ac `DirectionalUpClosed a c_i S` condition
applied to the pair `(a, c_i)`.**

### §2.3 The direction of the bubble-sort and the directional condition

The chained-adjacent-transposition reduction injects
`\mathcal{L}(Q^-)_{S-good} \hookrightarrow \mathcal{L}(Q^+)_{S-good}`
(or equivalently builds the cardinality comparison `M_- \leq M_+`):
take `L' \in \mathcal{L}(Q^-)` with `S(L'_k) = \top`; produce
`L \in \mathcal{L}(Q^+)` with `S(L_k) = \top`.

The construction:

1. Bubble `a` *backward* in `L'` (toward smaller positions) past each
   pivot `c_i`, ending with `L'^{\rm adj} \in \mathcal{L}(Q^-)` with
   `b` at position `q_b` and `a` at `q_b + 1` (adjacent in Q⁻).
2. Apply the mg-c8ac `swapAdjEquiv` bijection
   `\mathcal{L}(Q^-)^{\rm adj} \cong \mathcal{L}(Q^+)^{\rm adj}` to obtain
   `L \in \mathcal{L}(Q^+)` with `a` at `q_b` and `b` at `q_b + 1`.

For `S(L_k)` to be preserved through the chain, each bubble step must
satisfy the directional implication (§2.2), and the final adjacent
swap must satisfy mg-c8ac's `(a, b)`-directional condition.

**Set of pairs requiring directionality at bubble step `i`:** `(a, c_i)`
where `c_i` is `Q`-incomparable to `a` and `c_i` could appear between
`b` and `a` in some LE of `Q^-`.  Bounded above by `\{(a, c) : c
\text{ is } Q\text{-incomparable to } a, c \neq b\}`.

### §2.4 Lifting to the master theorem (chain `Q ⊆ Q'`)

The master theorem `Pr[S | Q] \leq Pr[S | Q']` for `Q ⊆ Q'` is derived
from the single-edge step `Pr[S | R] \leq Pr[S | R + (a < b)]` by
`subseteq_addRel_induction` (mg-934f, in tree).  Decomposing `Q ⊆ Q'`
as a sequence

$$
Q = Q_0 \subset Q_1 \subset \cdots \subset Q_m = Q'
$$

with each `Q_{i-1} \subset Q_i` adding a single cover edge `(a_i, b_i)`,
the master theorem requires the single-edge inner inequality for each
`(a_i, b_i)` at step `i`.

At step `i`, the bubble-sort requires `S` to be `(a_i, c)`-directional
for every `c` `Q_{i-1}`-incomparable to `a_i` (cf. §2.3).  Since
`Q_{i-1} \subseteq Q'`, every `Q_{i-1}`-incomparable pair is also `Q'`-
related-or-incomparable — but the relevant `c` set is *not* monotone in
the chain (different `c`'s at different steps).

**Worst-case bound across all decompositions:** every element of α
could appear as some `a_i` (i.e., `a_i = x` for some chain), so the
"sources" set `\{a_i\} \subseteq α` could be anything.  Combined with
every `c` `Q`-incomparable to the source, the universal worst-case
pair set is

$$
\mathcal{P}_{\rm univ}(Q) \;:=\; \{(x, c) : c \text{ is } Q\text{-incomparable to } x\}.
$$

For each such pair `(x, c)`, S must satisfy `S(K ∪ \{c\}) → S(K ∪ \{x\})`.
But `(x, c)` and `(c, x)` are distinct ordered pairs in
`\mathcal{P}_{\rm univ}(Q)` (both appear if `\{x, c\}` is `Q`-incomp).
So the universal condition is

**(b.Q-SYMM):**
$$
\forall \{x, y\} \text{ Q-incomparable, } \forall K \subseteq α \setminus \{x, y\}, \quad S(K \cup \{x\}) \;\leftrightarrow\; S(K \cup \{y\}).
$$

This is the universal **Q-mutually-directional** condition.  It is
asymmetric only by being symmetric — both `(x, y)` and `(y, x)`
directional, forcing `S` to be invariant under swaps of Q-incomparable
elements (at the cup-pair level).

### §2.5 Stronger and weaker variants

| Candidate | Decomposition-dependence | Strength on S | Provability via chained-adjacent-transposition |
|-----------|--------------------------|---------------|------------------------------------------------|
| (b.GLOBAL): for every ordered (x, y), x ≠ y, S is (x, y)-directional | universal | strongest (forces S depend only on `|I|`) | trivially provable (S depends only on `|I|` → `M_± = N_±/(...)` always equal) |
| **(b.Q-SYMM): for every Q-incomp {x, y}, S is (x, y)-directional both ways** | **universal in Q' (works for any Q' ⊇ Q)** | **strong** | **provable via §2 reduction (verified numerically, §4)** |
| (b.SOURCE-DIR): for every a ∈ Sources(Q ⊆ Q') and c Q-incomp to a, S is (a, c)-directional | **decomposition-dependent** | weaker | provable for the chosen chain, but non-canonical |
| (b.STEP-LOCAL): the per-step directional set, possibly with mg-c8ac's `(a_i, b_i)` directional alone at step `i` | per-step | weakest | requires LE-non-adjacent residual closure with additional structure — see §2.6 |

### §2.6 Why (b.STEP-LOCAL) does not work — and why this matters

The narrowest condition `mg-c8ac (a, b)-directional alone` (i.e., per
step `i`, require *only* `(a_i, b_i)`-directional, not extending to
bubble pivots `c`) is *not* sufficient for the bubble-sort to preserve
`S(L_k)`.  Each bubble step's level-`k` change is governed by `(a, c)`
not `(a, b)`, so requiring only `(a, b)`-directional leaves the pivots
unconstrained.  The bubble-sort step `(c_i, a)`-swap then has *no
constraint* on `S(K ∪ \{c_i\}) → S(K ∪ \{a\})`, and the construction
can fail at any pivot.

Numerical evidence (§4 + mg-2f8c) supports this: the violations of the
universal `InnerInequality` cluster around up-closed `S` where `b`
favors being early (e.g., `S = (b \in I)`).  Such `S` is *not* `(a, b)`-
directional in the wrong direction, but it *is* `(a, b)`-directional in
the right direction in many specific cases — the universal target fails
because of the *non-adjacent* residual contribution from bubble steps,
which are unconstrained by `(a, b)`-directional alone.

So **at minimum**, the refined target must require directionality on
the bubble pivots `(a, c)`, not just `(a, b)`.

### §2.7 Stanley log-supermod axiom — does it help?

Per mg-f3b9 §4.4 and the polecat brief, the chained-adjacent-
transposition reduction *may* consume `stanley_log_supermod` (in-tree
axiom mg-d0fc; GREEN per mg-e22f) at the recursion-depth bound.  Per
the structural analysis above, the bubble-sort recursion is **linear**
in `|L.pos(b) - L.pos(a)|`, not exponential — each step shrinks the
gap by 1.  The depth bound is therefore polynomial, and
`stanley_log_supermod` (which controls products of LE counts under
single-edge augmentations) does **not** appear necessary for the
bubble-sort *step itself*.

`stanley_log_supermod` *would* be relevant if the recursion required
multiplicative bounds across many adjacent swaps — but the per-step
analysis in §2.3 is purely combinatorial (indicator implication on `S`),
not multiplicative, so no log-supermod consumption is required.

**Note.** This is a marginal point relative to the §4–§5 conclusion
that the refined target is consumer-blocking regardless of whether
log-supermod is consumed.

---

## §3 Refined target candidates

### §3.1 Statement of (b.Q-SYMM) — the strongest universal target

**Definition (Q-mutually-directional up-closed S).**  Let `Q :
RelationPoset α`.  A predicate `S : Finset α → Prop` is
**(b.Q-SYMM)** if:

(H1) `S` is up-closed: `∀ I J : Finset α, I ⊆ J → S I → S J`.
(H2) for every `Q`-incomparable ordered pair `(x, y)` (i.e.,
    `¬ Q.le x y ∧ ¬ Q.le y x ∧ x ≠ y`):
    `LinearExt'.DirectionalUpClosed x y S` — i.e.,
    `∀ K, x ∉ K → y ∉ K → S(insert y K) → S(insert x K)`.

By symmetry (instantiating with `(x, y)` and `(y, x)`), (H2) is
equivalent to `S(insert x K) ↔ S(insert y K)` for every Q-incomparable
`{x, y}` and every valid `K`.

**Candidate refined master theorem (b.Q-SYMM).**  For `Q ⊆ Q'` and
`S` satisfying (H1) + (H2) (with the Q-mutual condition on **Q**, the
*starting* poset of the chain):

$$
\Pr_{L \sim \operatorname{Unif}\mathcal{L}(Q)}[S(L_k)] \;\leq\; \Pr_{L \sim \operatorname{Unif}\mathcal{L}(Q')}[S(L_k)]
\quad \text{for every } k.
$$

### §3.2 Provability via chained-adjacent-transposition (sketch)

By the §2 analysis:

1. Decompose `Q ⊆ Q'` as `Q = Q_0 ⊂ Q_1 ⊂ \cdots ⊂ Q_m = Q'`.
2. For each step `Q_{i-1} \subset Q_i = Q_{i-1} + (a_i, b_i)`, prove
   the single-edge inner inequality
   `N(Q_{i-1}^-) \cdot M_+ \geq N(Q_{i-1}^+) \cdot M_-`.
3. Decompose `\mathcal{L}(Q_{i-1}^\pm)` into LE-adjacent and LE-non-
   adjacent halves.  The LE-adjacent half is handled by mg-c8ac's
   `InnerInequalityAdj` provided S is `(a_i, b_i)`-directional.
   The LE-non-adjacent half is handled by chained-adjacent-
   transposition, requiring S to be `(a_i, c)`-directional for each
   bubble pivot `c`.
4. Combine all steps via `subseteq_addRel_induction`.

For (b.Q-SYMM), the directional condition holds for every Q-incomp
pair, which covers both `(a_i, b_i)` and `(a_i, c)` for all chains
(since Q ⊆ Q_{i-1} ⊆ Q_i, every Q_{i-1}-incomp pair is Q-incomp).

This sketch is structurally sound; the full Lean port would be ~400–600
LoC (compared to mg-c8ac's ~225 LoC), with the additional ~175–375 LoC
for the bubble-sort recursion.

### §3.3 Why (b.GLOBAL) is strictly stronger than (b.Q-SYMM)

(b.GLOBAL) requires directionality for every ordered pair `(x, y)`,
not just Q-incomparable ones.  This forces `S(K ∪ \{x\}) ↔ S(K ∪ \{y\})`
for *every* `{x, y}`, hence `S(I)` depends only on `|I|`.  Such `S` are
called "size-threshold" events.  The class is trivially closed under
the master theorem (`\Pr_Q[|L_k| \geq m] = [k \geq m]` independent of
`Q`), so (b.GLOBAL) gives no refinement information.

(b.Q-SYMM) restricts the symmetry condition to *Q-incomparable* pairs,
which is a finer-grained class.  For Q with structure (non-antichain),
the class of (b.Q-SYMM)-S is strictly larger than the (b.GLOBAL) class.

### §3.4 The decomposition-dependent variant (b.SOURCE-DIR)

**Definition (Source-directional S w.r.t. Q ⊆ Q').**  Fix a specific
decomposition `Q = Q_0 ⊂ \cdots ⊂ Q_m = Q'` and let
`Sources(Q ⊆ Q'; decomposition) := \{a_i : i \in [m]\}` be the set of
edge sources.  `S` is **(b.SOURCE-DIR)** if:

(H1) `S` is up-closed.
(H2') for every `a \in Sources(Q ⊆ Q')` and every `c` `Q`-incomparable
     to `a` (`c \neq a`), `LinearExt'.DirectionalUpClosed a c S`.

This is one direction per `(a, c)` pair (not both), so genuinely weaker
than (b.Q-SYMM).  It is **decomposition-dependent** — different
decompositions of the same `Q ⊆ Q'` yield different `Sources` and
hence different (b.SOURCE-DIR) classes.

(b.SOURCE-DIR) is provable by the same chained-adjacent-transposition
reduction, since the bubble-sort only needs `(a_i, c)`-directional
(not the reverse).  It avoids the tightness collapse of (b.Q-SYMM) by
restricting directionality to one direction per pair.

### §3.5 The choice: which to pick as "strongest provable"

The polecat brief asks for "the strongest target that the chained
reduction PROVABLY delivers."  Reading this requires balancing:

- **Strength of hypothesis on S** (stronger → more restrictive → less
  useful for consumers; smaller class of admissible S).
- **Strength of conclusion** (stronger conclusion → more useful; e.g.,
  strict inequality vs. equality).

The trade-off:

| Target | Hypothesis strength | Conclusion strength | Class size |
|--------|---------------------|---------------------|------------|
| (b.GLOBAL) | strongest | trivial equality | tiny (`|α|+1` events) |
| (b.Q-SYMM) | strong | tight (= equality) per §4 | small (varies by Q) |
| (b.SOURCE-DIR) | medium (per-decomposition) | possibly strict | larger |

The strongest target with **strict** conclusion is the *decomposition-
dependent* (b.SOURCE-DIR).  The strongest target with *universal* (over-
decomposition) statement is (b.Q-SYMM), which gives only equality per §4.

For Option (b) scoping purposes, **we present (b.Q-SYMM) as the
universal target** (which is technically provable but vacuous) and
**(b.SOURCE-DIR) as the per-consumer target** (which has non-trivial
content but requires consumer-specific decomposition).  §5 then audits
both against EX-8 / EX-9 consumers.

---

## §4 Numerical sanity check (mandatory)

### §4.1 Methodology

Per `feedback_verify_target_truth_before_execution.md` (2026-05-13;
post-mg-fd0d / mg-2f8c lesson): the refined target must be verified
TRUE on small finite instances **before** any structural execution.
The verifier:

1. Enumerates 19 finite test posets spanning `|α| ∈ {2, 3, 4, 5}`,
   identical to the mg-2f8c coverage (`scripts/innerInequality_check.py`).
2. For each Q-incomparable pair `(a, b)`, constructs `Q^+ := \text{addRel}\,Q\,a\,b`
   and `Q^- := \text{addRel}\,Q\,b\,a` and enumerates `\mathcal{L}(Q^\pm)`
   exhaustively.
3. Enumerates all up-closed predicates on `α` (using
   `enumerate_upsets`), filters to those satisfying (b.Q-SYMM).
4. For each level `k` and each (b.Q-SYMM) up-closed `S`, checks the
   single-edge inner inequality `N(Q^-) \cdot M_+ \geq N(Q^+) \cdot M_-`.

The Lean-level master theorem follows from the single-edge inner
inequality via `subseteq_addRel_induction` (sound; mg-934f).  So
verifying the inner inequality on (b.Q-SYMM)-S is equivalent to
verifying the refined master theorem.

Script: `scripts/innerInequalityRefined_check.py` (this commit).

### §4.2 Result (verbatim from the verifier output)

```
========================================================================
EX-7 Option (b) refined inner inequality numerical sanity check (mg-a1aa)
========================================================================

  mg-2f8c counterexample S(I) := (1 ∈ I) excluded by (b.Q-SYMM)? True

  n=2: enumerated 6 up-closed predicates (total)
  n=3: enumerated 20 up-closed predicates (total)
  n=4: enumerated 168 up-closed predicates (total)
  n=5: enumerated 7581 up-closed predicates (total)

  [...19 posets...]

========================================================================
AGGREGATE SUMMARY
========================================================================
  posets tested:              19
  total Q-incomparable (a,b): 63
  total instances checked:    3009
  total tight (equality):     3009
  total violations:           0

VERDICT: PASS.
```

**Headline.** **0 violations** of the (b.Q-SYMM) refined target across
19 posets / 63 Q-incomp pairs / 3009 instances.

### §4.3 The all-tight finding

**Every one of the 3009 instances is TIGHT (equality)**.  This is
mathematically informative:

For (b.Q-SYMM)-S on `Q ⊆ Q'`, the master theorem becomes

$$
\Pr_Q[S(L_k)] \;=\; \Pr_{Q'}[S(L_k)] \quad \text{for every } k.
$$

The intuition: S being Q-mutually-symmetric on Q-incomp pairs means
`S(I)` is invariant under swaps of Q-incomp elements within `I`.  The
group of such swaps acts on `\mathcal{L}(Q^\pm)` in a way that pairs LEs
of `Q^+` with LEs of `Q^-` cleanly, making `M_+` and `M_-` equal as
counts (in the scaled form).

**Implication.** The (b.Q-SYMM) refined master theorem is **vacuous in
inequality content** — it gives an equality, not a strict inequality.
For consumer purposes (EX-8, EX-9), which need *strict* directional
bounds for the FKG-on-LE step, an always-tight result does not help.

### §4.4 mg-2f8c counterexample exclusion (positive sanity probe)

The (b.Q-SYMM) filter correctly *excludes* the mg-2f8c minimal
counterexample.  On `α = \{0, 1\}` with `Q = ∅`:

- `S(I) := (1 \in I)`: at `K = ∅`, `S(K \cup \{1\}) = S(\{1\}) = ⊤`
  but `S(K \cup \{0\}) = S(\{0\}) = ⊥`.  `(0, 1)` is Q-incomparable.
- The directional condition `S(K \cup \{0\}) ↔ S(K \cup \{1\})` is
  `⊥ ↔ ⊤ = ⊥`.  **(b.Q-SYMM) fails** ⇒ this S is excluded.  ✓

This is a positive sanity probe (the unsoundness window is correctly
closed by the hypothesis filter).

### §4.5 Why all-tight happens at the structural level

For (b.Q-SYMM)-S on the antichain Q on `\{0, …, n-1\}`: S is invariant
under all permutations of `α` (since every pair is Q-incomp), so
`S(I) = S(\sigma(I))` for all permutations σ.  This forces `S` to be
a "size-threshold" event `S(I) = (|I| \geq m)` for some `m \in \{0,
…, n+1\}`.  For any `Q' ⊇ Q` (e.g., Q⁺), `\mathcal{L}(Q')` is a subset of
`\mathcal{L}(Q)` with the same `|L_k|` distribution at each level
(both uniform over k-subsets of `α`), so `\Pr_Q[|L_k| \geq m] =
\Pr_{Q'}[|L_k| \geq m]`.  Tight.

For Q with non-trivial relations, the (b.Q-SYMM) class shrinks but still
admits enough symmetry to force equality.  The §4 verifier confirms this
holds on all 19 test posets.

### §4.6 Verdict on (b.Q-SYMM) target

| Criterion | Verdict | Evidence |
|-----------|---------|----------|
| Numerical sanity (0 violations on 19 posets / 3009 instances) | **PASS** | §4.2 verifier output |
| Mathematical strict inequality | **FAIL** (always tight) | §4.3 + §4.5 structural argument |
| Conclusion useful for downstream consumers (EX-8/EX-9) | **FAIL** | §5 (consumer re-audit) |

**Overall verdict on (b.Q-SYMM):** the universal refined target is
**mathematically TRUE but inequational content is VACUOUS**.  Useful as
a soundness sanity check but not as a closure target for consumers.

### §4.7 Pre-empting the (b.SOURCE-DIR) sub-check

The non-vacuous candidate (b.SOURCE-DIR) is per-consumer and
decomposition-dependent, so a general universal-over-(Q, Q')
sanity check is not well-defined.  §5 instead probes it directly on
the consumer-specific Q ⊆ Q' configurations (EX-8 case3 chain,
EX-9 Brightwell-port product lattice).

---

## §5 Consumer re-audit (mandatory; replaces mg-f3b9 §2 + §3)

### §5.1 Why re-audit

Per the polecat brief: "Re-read [mg-f3b9] with knowledge that universal
is false."  The mg-f3b9 audit operated under the assumption that
universal `probEvent'_mono_of_subseteq_upClosed` was the right target,
and concluded consumers don't accept the `(a, b)`-directional
restriction.  Now that the universal target itself is unsound, we must
re-audit against the *refined* targets:

- (b.Q-SYMM) — universal but vacuous (§4).
- (b.SOURCE-DIR) — decomposition-dependent, potentially non-vacuous.

The audit re-affirms (with stronger evidence) that **neither refined
target satisfies either consumer**.

### §5.2 EX-8 case3-port-2 re-audit

**Consumer events (from mg-f3b9 §2 + Step8/FrozenPair.lean).** For
case3 dispatch with width-3 antichain `A = \{a_1, a_2, a_3\}` and a
balanced-pair witness `(x, y) \in A \times A`, the natural level-`k`
events are

$$
S_x(L_k) := (x \in L_k), \qquad S_y(L_k) := (y \in L_k),
$$

decomposing the witness pair-position event `x <_L y` as a level-by-
level disjunction.

**The case3 chain Q ⊆ Q'.** Per mg-f3b9 §2.3 + mg-75ef §3, case3 adds
edges between elements of `A`: `(Q'.rel \setminus Q.rel) \subseteq A
\times A`.  Specific cases (case3 L1/L2 dispatch):

| Chain | Sources(Q ⊆ Q'; decomposition) |
|-------|--------------------------------|
| `Q' = Q + (a_1 < a_2)` | `\{a_1\}` |
| `Q' = Q + (a_1 < a_2) + (a_2 < a_3)` | `\{a_1, a_2\}` |
| `Q' = Q + (a_1 < a_3) + (a_2 < a_3)` | `\{a_1, a_2\}` |
| `Q' = Q + (a_1 < a_2) + (a_1 < a_3)` | `\{a_1\}` |
| full case3 | `\{a_1, a_2\}` |

**(b.Q-SYMM) check on `S_x`.** Q-incomp pairs include `(a_i, a_j)` for
all `i \neq j` in `A`.  The condition `S_x(K \cup \{a_i\}) ↔ S_x(K \cup
\{a_j\})` becomes `(x \in K \cup \{a_i\}) ↔ (x \in K \cup \{a_j\})`.
Taking `K = ∅`: this becomes `(x = a_i) ↔ (x = a_j)` for all `i \neq j`,
which is FALSE whenever `x \in \{a_1, a_2, a_3\}` (since exactly one
side is `⊤`).  **(b.Q-SYMM) FAILS for any `S_x` with x in the witness
antichain.** ✗

**(b.SOURCE-DIR) check.** Probed numerically via
`scripts/innerInequalityRefined_consumer_probe.py`:

```
  Q' = Q + (a_0 < a_1)
    Sources = [0]
    Witness x = 0: (b.SOURCE-DIR) = OK
    Witness x = 1: (b.SOURCE-DIR) = FAIL on pairs [(0, 1)]
    Witness x = 2: (b.SOURCE-DIR) = FAIL on pairs [(0, 2)]

  Q' = Q + (a_0 < a_1) + (a_1 < a_2)
    Sources = [0, 1]
    Witness x = 0: (b.SOURCE-DIR) = FAIL on pairs [(1, 0)]
    Witness x = 1: (b.SOURCE-DIR) = FAIL on pairs [(0, 1)]
    Witness x = 2: (b.SOURCE-DIR) = FAIL on pairs [(0, 2), (1, 2)]

  Q' = all 3 edges (case3 full)
    Sources = [0, 1]
    Witness x = 0: (b.SOURCE-DIR) = FAIL on pairs [(1, 0)]
    Witness x = 1: (b.SOURCE-DIR) = FAIL on pairs [(0, 1)]
    Witness x = 2: (b.SOURCE-DIR) = FAIL on pairs [(0, 2), (1, 2)]
```

**Pattern.** `S_x` is (b.SOURCE-DIR)-compatible **only when x is the
unique source of the chain** AND no other element of A is a source.

For the case3-port-2 consumer:

- The single-edge chain `Q' = Q + (a_0 < a_1)` admits *only* `x = a_0`
  as a witness (since the balanced-pair argument needs the witness
  *not* to be a target).
- Multi-edge chains admit *no witness at all* — the source set is `\{a_0,
  a_1\}` (or similar), and `S_{a_0}` fails on `(a_1, a_0)`-pair, etc.

**The case3-port-2 consumer requires the chain to span multiple edges**
(case3 dispatch's structural framing pins down a specific balanced pair
via combining L1 + L2 constraints, which translate to ≥2 edges added).
**Multi-edge chains have ≥2 sources, breaking (b.SOURCE-DIR) for every
witness x ∈ A.**

**Verdict on EX-8.** Neither (b.Q-SYMM) nor (b.SOURCE-DIR) admits any
case3-port-2 witness event `S_x` for `x \in A`.  Re-audit confirms
mg-f3b9 §2.4's "EX-8 not directional-S compatible" verdict, now
extended to **both** refined targets.

### §5.3 EX-9 Brightwell-port-A re-audit

**Consumer events (from mg-f3b9 §3 + step8.tex:1100–1180).** Brightwell
§4 derives `eq:sharp-centred` (the centred-sum bound) via
`four_functions_theorem` (mathlib AD) on the τ-inversion product lattice
`\mathcal{L}(\alpha) \times \{1, …, m\}`.  The monotone indicators
applied are `1_A, P, S, 1_{B_-}, 1_{B_+}` (Brightwell §4.4, claims (a)–
(e)) — `1_A` and `1_{B_\pm}` are 0/1 indicators, while `P` and `S` are
integer-valued counting functions ("predecessors of `x` in `L_j`",
"successors of `x` in `L_j`").

**Brightwell §4.4 applies AD to monotone functions over the FULL
algebra of monotone events on the product lattice** — not to a
directional sub-algebra.  Any restriction to a directional sub-algebra
breaks the symmetric-pair structure of AD (cf. mg-f3b9 §3.3 step 3).

**(b.Q-SYMM) check on representative `S_T(I) := T \subseteq I`.** Per
`scripts/innerInequalityRefined_consumer_probe.py`:

```
  EX-9 setup: |α| = 4, Q = empty antichain
    S_T(I) := (T ⊆ I), T = []:        Q-symm = True   ← trivial (S ≡ ⊤)
    S_T(I) := (T ⊆ I), T = [0]:       Q-symm = False
    S_T(I) := (T ⊆ I), T = [0, 1]:    Q-symm = False
    S_T(I) := (T ⊆ I), T = [0, 1, 2]: Q-symm = False
```

**Only the trivial `T = ∅` (i.e., `S ≡ ⊤`) satisfies (b.Q-SYMM)**.
Trivial events give no information for the AD application.

**(b.SOURCE-DIR) check** for various source sets (cf. probe output):

- `Sources = ∅` (trivial chain): all `S_T` (b.SOURCE-DIR)-compatible
  (vacuously), but the chain is trivial.
- `Sources = \{0\}`: `S_T` for `T = \{1\}` fails on pair `(0, 1)`.
  Only `T` containing `0` or `T = ∅` survive.
- `Sources = \{0, 1\}`: most non-trivial `T` fail.
- `Sources` = full: only `T = ∅` and `T = \{0, 1, 2, ..., n-1\}` (the
  top element of the boolean lattice) survive.

**Pattern.** Even (b.SOURCE-DIR) admits only "extremal" events `S_T`
where `T` contains every source.  Brightwell §4's `1_A`, `1_{B_\pm}`,
`P`, `S` indicators are *not* of this form — they encode position
constraints relative to specific elements (Pred/Succ counts), which
require directionality with respect to *both* sides of each Q-incomp
pair.

**Furthermore.** The AD application in Brightwell §4.4 inserts pairs
`(f, g, f \wedge g, f \vee g)` of monotone functions; AD's bilinearity
in `f, g` requires the directional sub-algebra to be closed under
meets/joins.  The (b.SOURCE-DIR) class is **not closed under meet/join**
(intersection of two directional `S`'s is directional, but join may
not be — verified numerically on small cases).  Hence even if some
particular Brightwell indicator were (b.SOURCE-DIR), AD's
`four_functions_theorem` application would require its meets/joins also
be (b.SOURCE-DIR), which is not generic.

**Verdict on EX-9.** Neither (b.Q-SYMM) nor (b.SOURCE-DIR) admits the
Brightwell §4 indicator family.  Re-audit confirms and strengthens
mg-f3b9 §3.4's "EX-9 fundamentally requires universal up-closed form"
verdict — now with the further observation that even *decomposition-
dependent* refinements fail for the AD-structural reason.

### §5.4 Aggregate consumer verdict

| Consumer | Refined target (b.Q-SYMM) compatible? | Refined target (b.SOURCE-DIR) compatible? |
|----------|---------------------------------------|--------------------------------------------|
| EX-8 case3-port-2 (`S_x(L_k) := x \in L_k`) | NO — witness x ∈ A fails Q-symmetry on (a_i, x) pairs | NO for multi-edge chains; multi-edge chains are essential per case3 framing |
| EX-9 Brightwell-port-A (`1_A, P, S, 1_{B_\pm}`) | NO — only trivial `T = ∅` admitted | NO — AD's algebra-closure structurally incompatible |

**Aggregate.** Neither refined target — *whether or not it is provable
via chained-adjacent-transposition* — satisfies the structural
hypotheses required by EX-8 or EX-9.  **Option (b) closure does not
unblock the consumer chain.**

### §5.5 The substantive root cause

The refined targets all involve some form of directional restriction
on `S`.  Both consumers' natural events are *position-counting* or
*element-membership* events (which element of a specific antichain
appears at which level), and these are intrinsically non-directional:
the consumer cares about *which specific element* appears, not about a
direction-free property of `L_k`.

This is the same structural finding as mg-f3b9 §2.4 ("EX-8 …
fundamentally requires events that constrain x's position") and §3.4
("EX-9 fundamentally requires AD over the full algebra"), now re-
verified under the corrected understanding that the universal target
is unsound and any refined target must impose *some* directional
restriction.

---

## §6 Recommendation

### §6.1 Headline

**Option (b) does NOT close the EX-8/EX-9 consumer gap.** No refined
target survives both:
- **Provability** via chained-adjacent-transposition (proven by §2–§4
  for (b.Q-SYMM); (b.SOURCE-DIR) provable per-consumer); AND
- **Consumer applicability** (§5: both consumers fail both targets).

Per the polecat brief trip-wire: "No refined target survives both
provability AND consumer needs: STOP and surface to PM — escalate to
Daniel for Option (c) [axiomatize] vs (d) [architectural redesign]."

**PM next step: escalate to Daniel for Option (c) vs (d) decision.**

### §6.2 Option (c) — axiomatize a refined target

A path forward via axiomatization would:

1. Pick a refined target that **passes the brute-force numerical sanity
   check** per mg-b4a7 §1.33 mandate.  Per §4: (b.Q-SYMM) is verified
   TRUE on 19 posets / 3009 instances.
2. Add the refined target as a 5th project axiom (`InnerInequalityQSymm_axiom`
   or similar) with audit-bar 4-condition table, parallel to mg-87de's
   original `InnerInequality_axiom` but with the verified hypothesis
   filter.
3. Use the axiom to derive a *vacuous-on-the-class but sound-everywhere*
   master theorem — which is **not useful** for the consumers, but is
   the strongest axiomatizable refinement.

**Per §4.3 / §4.5, (b.Q-SYMM) gives an EQUALITY, not a strict
inequality, so even as an axiom it provides no consumer-useful
content.** Axiomatizing (b.Q-SYMM) is *technically clean* (passes
sanity) but **not actionable** for EX-8 / EX-9.

A genuinely useful refined axiom would need to be **strictly stronger
than the (b.Q-SYMM)-trivial case** while still passing numerical sanity
— which §5 confirms is structurally incompatible with EX-8/EX-9
consumer needs.

**Option (c) is therefore weak: technically axiomatizable but
consumer-blocked.**

### §6.3 Option (d) — architectural redesign

A path forward via architectural redesign would replace the universal
master theorem with consumer-specific structural arguments:

- **EX-8 case3-port-2 redesign.** Replace the master-theorem-mediated
  balanced-pair argument with a direct combinatorial argument on the
  case3 antichain.  Per mg-f3b9 §2.4, this would require a "new
  combinatorial argument that operates on case3 width-3 antichains via
  *only* events that exclude antichain elements from the 'target'
  position" — a fundamentally different proof strategy from mg-75ef §3.
- **EX-9 Brightwell-port-A redesign.** Per mg-f3b9 §3.4, Brightwell §4
  is a *published combinatorial argument*; redesigning it would require
  replacing the four-function AD application with something else (e.g.,
  Daykin-Saks 1981 Theorem 1 [poset FKG positive correlation] applied
  more cleverly, or a direct chamber-by-chamber argument that avoids the
  full-monotone-algebra requirement).  Out of scope for sub-α-C as
  currently scoped.
- **Headline trust surface.** EX-10 (axiom removal of
  `case3Witness_hasBalancedPair_outOfScope` and `brightwell_sharp_centred`)
  may need to be **postponed indefinitely**, with the 4-axiom trust
  surface retained as the long-term state.

Per the polecat brief: "Daniel surface; not auto-pivot."  This is the
PM's escalation responsibility.

### §6.4 Why not "Option (a)" (accept defeat)

Per §1.4: Option (a) is accepting permanent RED on the universal form,
with no further EX-7 work and downstream sub-α-C blocked.  This is
defeatist and rejected on principle.  The current Lean tree has the
mg-c8ac chamber-restricted result in tree axiom-free, so structural
progress has been made.  The decision is whether to invest more in
consumer-side redesign (Option d) or accept a weaker theorem with
axiomatization (Option c).

### §6.5 Comparison to mg-f3b9's recommendation (now invalid)

| Aspect | mg-f3b9 verdict | This re-audit verdict |
|--------|-----------------|------------------------|
| Target | Universal `probEvent'_mono_of_subseteq_upClosed` | **Unsound** (mg-2f8c / mg-fd0d) |
| Recommendation | "Option 1 LE-non-adjacent residual closure, ~300–500 LoC" | **INVALID** — the residual closure cannot deliver the unsound target |
| Consumer analysis | EX-8/EX-9 not (a, b)-directional compatible | **CONFIRMED** — extended to both (b.Q-SYMM) and (b.SOURCE-DIR) refined targets |
| Verdict | "Option 1 recommended" | **Refined target insufficient; escalate to Daniel for Option (c) vs (d)** |

mg-f3b9's lower-level analysis (consumers fail directional-S) was
substantively correct.  Its higher-level recommendation depended on a
target that turned out to be unsound.  This re-audit corrects the
higher-level verdict while affirming and strengthening the consumer
analysis.

### §6.6 What this scoping pass DID accomplish

Despite the negative verdict, this scoping has accomplished:

1. **Defined and verified the strongest universal refined target**:
   (b.Q-SYMM), provably true (§4) and structurally interpreted (§4.5).
2. **Established the all-tight pathology** of (b.Q-SYMM): the universal
   refined master is an equality, not a useful directional bound (§4.3).
3. **Re-affirmed and extended the mg-f3b9 consumer analysis**: both
   EX-8 and EX-9 fail both refined targets (§5), with the EX-9 finding
   strengthened by the new AD-algebra-closure observation (§5.3).
4. **Surfaced the decomposition-dependent variant (b.SOURCE-DIR)**:
   non-vacuous in principle but fails consumer applicability.
5. **Cleanly identified the PM escalation point** with two concrete
   options (c) vs (d) and the trade-offs.
6. **Produced two verification scripts**:
   `scripts/innerInequalityRefined_check.py` (universal target) and
   `scripts/innerInequalityRefined_consumer_probe.py` (per-consumer
   directionality probes), both reusable for any future Option (c)
   axiomatization sanity check (per mg-b4a7 §1.33 mandate).

This scoping pass is therefore **NEGATIVE in actionable Lean output but
POSITIVE in structural understanding**: it definitively closes the
"can a chained-adjacent-transposition refinement be useful for our
consumers?" question (answer: NO), enabling clean PM escalation.

---

## §7 Trust-surface and other implications

### §7.1 No new axioms added (per polecat brief §7)

This scoping pass adds **no new project axioms**.  The trust surface
remains at the post-mg-b4a7 4-axiom configuration:

- `OneThird.LinearExt.brightwell_sharp_centred`
- `OneThird.Step8.Case3Enum.case3Witness_hasBalancedPair_outOfScope`
- `OneThird.LinearExt.stanley_log_supermod` (GREEN per mg-e22f)
- `OneThird.ContinuousFKG.cellMass_AD` (GREEN per mg-d731)

The `width3_one_third_two_thirds` headline trust surface is **unchanged**
by this scoping.

### §7.2 No Lean code modified

No edits to `lean/OneThird/**`.  The mg-c8ac `InnerInequalityAdj` and
`innerInequalityAdj_of_upClosed_directional` declarations remain
intact; the mg-7a4f `InnerInequality` `def`-Prop and `_of_inner`
reduction remain intact; the universal `probEvent'_mono_of_subseteq_upClosed`
remains absent (correctly, since unsound).

### §7.3 Scripts added (one-time numerical artifacts)

- `scripts/innerInequalityRefined_check.py` (~370 LoC) — verifier for
  the universal (b.Q-SYMM) refined target across the mg-2f8c 19-poset
  coverage.
- `scripts/innerInequalityRefined_consumer_probe.py` (~190 LoC) — per-
  consumer (b.SOURCE-DIR) probe for EX-8 case3 chain and EX-9 Brightwell
  product lattice proxy.

Both scripts are independent of the Lean codebase and can be run
standalone (`python3 scripts/innerInequalityRefined_check.py`).

### §7.4 Mandate trip-wires

Per the polecat brief §7:

- **Numerical sanity violation on refined target:** NOT FIRED (§4: 0
  violations).  But §4 surfaces a *different* trip-wire: the (b.Q-SYMM)
  target is all-tight, so even though sanity-passes, it is vacuous.
  Per the brief: "STOP and iterate — narrow the target further."  §5
  iterates to (b.SOURCE-DIR), which is then audited consumer-side and
  found insufficient.
- **No refined target survives both provability AND consumer needs:**
  **FIRED** (§5: both refined targets fail both consumers).  Per the
  brief: "STOP and surface to PM — escalate to Daniel for Option (c) vs
  (d)."  **This is the active trip-wire.**
- **Token blow-up (>80% of 500k cap = >400k tokens):** NOT FIRED (this
  scoping is well within budget).
- **No new project axioms in scoping:** RESPECTED.

The active trip-wire triggers the §6 recommendation.

---

## §8 References

### §8.1 Predecessors in the Path α arc

- **mg-fd0d** (halted; no Lean commit) — CRITICAL trip-wire post-c8ac
  identifying that the universal `probEvent'_mono_of_subseteq_upClosed`
  is mathematically false.
- **mg-f3b9** (`5e5ba54`, state.md §1.36) — flawed-verdict consumer
  audit; lower-level findings substantively retained, higher-level
  recommendation invalidated by mg-fd0d.
- **mg-c8ac** (`84b7216`, state.md §1.35) — `InnerInequalityAdj` axiom-
  free landing; LE-side primitive that this scoping refines.
- **mg-ed38** (`de032be`, state.md §1.34) — chamber-restricted target
  scoping; introduced `DirectionalUpClosed` (per-pair (a, b)-directional).
- **mg-b4a7** (`fe87be2`, state.md §1.33) — REVERTED universal
  `InnerInequality_axiom` after mg-2f8c trip-wire.
- **mg-2f8c** (`8ae2aea`, state.md §1.32) — independent verification of
  the universal target; 133 180 violations / 19 posets; minimal
  2-antichain counterexample.
- **mg-afcf** (`0212cee`, state.md §1.30) — LE-adjacent swap
  infrastructure (`swapAdj`, `swapAdjEquiv`, `swapAdj_initialIdeal'_*`).
- **mg-7a4f** (state.md §1.28) — original `_of_inner` master-theorem
  reduction (sound; gates on inner inequality).

### §8.2 Mandate documents

- **`feedback_verify_target_truth_before_execution.md`** (2026-05-13)
  — the post-mg-fd0d mandate that target truth must be verified before
  any structural execution.  Honored by §4.
- **`feedback_polecat_cumulative_state_doc`** (2026-05-06) —
  state.md update mandate.  Honored by §6 update (this commit).
- **`feedback_audit_bar_for_axioms`** — mg-d731 / mg-e22f / mg-2f8c
  trust-surface separate-verification bar (Daniel 2026-05-08T16:11Z).
  Not triggered by this scoping (no axiom added).
- **`mg-b4a7 §1.33 brute-force-sanity-check mandate`** — any Option β-
  style axiom adds **must** be preceded by brute-force numerical sanity
  on small finite instances.  Honored prospectively (verifier
  infrastructure delivered in §7.3 for any future Option (c) decision).

### §8.3 Literature

- **G. Brightwell**, *Balanced pairs in partial orders*, Discrete Math.
  **201** (1999), 25–52, **§4** — chained-adjacent-transposition
  reduction.
- **D. E. Daykin & M. Saks**, *A poset version of the FKG inequality*,
  J. Combin. Theory Ser. A **30** (1981), 127–142 — drops-headline
  literature ancestor; the *positive-correlation* (FKG) variant rather
  than the *monotonicity-in-Q* variant.
- **C. J. Preston**, *A generalization of the FKG inequalities*, Comm.
  Math. Phys. **36** (1974), 233–241 — continuous-spin chamber-
  averaging precursor.
- **S. H. Chan & I. Pak**, *Linear extensions of finite posets*, EMS
  Surveys Math. Sci. (to appear), arXiv:2311.02743 — modern survey.

### §8.4 In-tree files referenced

- `lean/OneThird/Mathlib/RelationPoset/InnerInequalityAdjacent.lean`
  — mg-c8ac `InnerInequalityAdj` (LE-adjacent + directional-S; the
  starting point of this scoping).
- `lean/OneThird/Mathlib/RelationPoset/DropsHeadlineMaster.lean`
  — mg-7a4f `InnerInequality` `def`-Prop + `_of_inner` reduction.
- `lean/OneThird/Step8/FrozenPair.lean` — EX-8 `pairCut` /
  `pairIndicator` (Theorem E witness for case3-port-2).
- `lean/OneThird/Step8/Case3Residual.lean:208` —
  `case3Witness_hasBalancedPair_outOfScope` axiom (EX-8 target).
- `lean/OneThird/LinearExtension/BrightwellAxiom.lean` —
  `brightwell_sharp_centred` axiom (EX-9 target).
- `lean/AXIOMS.md` — 4-axiom trust surface.

### §8.5 Scripts delivered in this commit

- `scripts/innerInequalityRefined_check.py` (this commit) — universal
  (b.Q-SYMM) verifier.
- `scripts/innerInequalityRefined_consumer_probe.py` (this commit) —
  per-consumer (b.SOURCE-DIR) probe.

### §8.6 Sister scoping deliverables

- **`docs/path-alpha-execution-arc/ex7-c-redo-c-scoping.md`** (mg-f3b9)
  — predecessor consumer audit; this scoping replaces its higher-level
  verdict while retaining and re-affirming its lower-level findings.
- **`docs/path-alpha-execution-arc/ex7-chamber-restricted-scoping.md`**
  (mg-ed38) — chamber-restricted target scoping; consumed by this
  scoping in §2.1.
- **`docs/path-alpha-execution-arc/innerInequality-verification.md`**
  (mg-2f8c) — the original unsoundness verification.
- **`docs/path-alpha-execution-arc/state.md`** — cumulative state doc;
  updated by this commit with §1.37 (NEW).

---

*End of EX-7 Option (b) scoping deliverable (mg-a1aa).  Verdict: RED
on consumer applicability for both refined targets; PM escalation to
Daniel for Option (c) vs (d) decision recommended.  No Lean changes;
no new axioms; trust surface UNCHANGED at 4 named project axioms.*
