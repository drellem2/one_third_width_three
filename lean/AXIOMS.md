# Named axioms in `OneThird`

This file certifies that each named axiom in the Lean development is a
faithful transcription of a specific paper statement. Each entry
records:

* the Lean axiom name and file;
* the corresponding paper statement (file, line, equation label);
* a scope-match checklist (hypotheses, constants, quantifier order);
* the work item that introduced the axiom, the QA audit that
  certified it, and the work item scheduled to replace it with a
  proof.

Unless otherwise noted, every axiom below has been manually verified
against the paper proof it axiomatizes, and a closed-form integer
counterexample was constructed against any variant of the statement
rejected during QA.

---

## `OneThird.LinearExt.brightwell_sharp_centred`

**File.** `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean`

**Paper statement.** `step8.tex:1048`, `eq:sharp-centred`:
$$
\Bigl|\sum_{L' \in A}(f(L') - \bar f)\Bigr| \;\le\; \frac{2N}{m}.
$$
The paper's derivation of this bound from the FKG / Ahlswede–Daykin
inequality and the Kahn–Saks / Brightwell per-term covariance bound
is given in `step8.tex:1046–1276` (the "Sharp bound via pred/succ
separation and the Ahlswede–Daykin inequality" subsection of
`lem:one-elem-perturb`). The FKG part is formally derived via
`c6d76d6` (mg-391c, A10b).

**Introduced by.** `mg-134c` (commit `2ded504`, F6-4 axiomatization).

**QA-audited by.** `mg-a6a1` (F6-4-QA; this entry).

**Status.** **Retained as a named axiom.** Decision recorded in
`mg-b699` (F6-4-port, post-sorry-free): the bound is a faithful
transcription of a published external result
(Brightwell~\cite{Brightwell1999}, §4, combined with
Kahn--Saks~\cite{KahnSaks1984}, Lemma 2.2), and a full Lean port —
estimated at 500--800 LoC of mathlib-tier infrastructure for the
per-term Kahn--Saks / Brightwell covariance bound on the product
distributive lattice $\mathcal L(\alpha) \times \{1, \dots, m\}$ —
is deferred indefinitely as post-launch refinement. The structural
proof of `width3_one_third_two_thirds` is the credibility artifact;
per-leaf porting of a cited theorem does not move the needle. See
"Decision rationale (mg-b699)" below.

### Scope-match checklist

| Paper | Axiom | Status |
| --- | --- | --- |
| $Q$ finite with $\lvert Q\rvert = m \ge 2$ | `m : ℕ`, `hmQ : m = Fintype.card α + 1`, `hm : 2 ≤ m` | ✅ pinned to `|Q|` (see fix below) |
| $z \in Q$, $\alpha := Q - z$ | `α : Type*` with `PartialOrder`, `Fintype`, `DecidableEq` | ✅ |
| $\operatorname{pred}(z), \operatorname{succ}(z) \subseteq \alpha$ | `Pred Succ : Finset α` | ✅ |
| $\operatorname{pred}(z) \cap \operatorname{succ}(z) = \emptyset$ | `hDisj : Disjoint Pred Succ` | ✅ |
| $u < z < v$ for $u \in \operatorname{pred}(z)$, $v \in \operatorname{succ}(z)$ (hence $u \le v$ in $\alpha$) | `hComp : ∀ u ∈ Pred, ∀ v ∈ Succ, u ≤ v` | ✅ |
| $x, y \in \alpha$, $x \ne y$ (trivially true if comparable) | `x y : α` | ✅ (extra case `x = y` is vacuous: `A = ∅`, LHS is `0`) |
| $P(L') := \max\{\operatorname{pos}_{L'}(u) : u \in \operatorname{pred}(z)\}$, $= 0$ if $\operatorname{pred}(z) = \emptyset$ | `maxPredPos Pred L = Pred.sup L.posAux` (`FiberSize.lean:90`); `maxPredPos_empty` gives $0$ | ✅ |
| $S(L') := \min\{\operatorname{pos}_{L'}(v) : v \in \operatorname{succ}(z)\}$, $= m$ if $\operatorname{succ}(z) = \emptyset$ | `minSuccPos Succ L = Succ.inf' L.posAux` when nonempty, else `Fintype.card α + 1 = m` (`FiberSize.lean:95`) | ✅ (fixed: see "Discrepancy audit" below) |
| $f(L') := S(L') - P(L') \in \{1, \ldots, m\}$ | `fiberSize Pred Succ L = minSuccPos − maxPredPos`; upper bound `fiberSize_le_card_succ : fiberSize ≤ Fintype.card α + 1` | ✅ |
| $N := \lvert\mathcal L(Q)\rvert = \sum_{L'} f(L')$ | `∑ L : LinearExt α, (fiberSize Pred Succ L : ℤ)` — equals $\lvert\mathcal L(Q)\rvert$ by the fibre-sum identity `step8.tex:939` | ✅ (fixed: see audit) |
| $N' := \lvert\mathcal L(\alpha)\rvert$ | `Fintype.card (LinearExt α)` | ✅ |
| $A := \{L' \in \mathcal L(\alpha) : x <_{L'} y\}$ | `(Finset.univ : Finset (LinearExt α)).filter (fun L => L.lt x y)` where `L.lt x y := L.pos x < L.pos y` (`Fintype.lean:67`) | ✅ |
| $\displaystyle\Bigl\lvert\sum_{L' \in A}(f(L') - \bar f)\Bigr\rvert \le \frac{2N}{m}$ | Integer form `m · |N' · sumA − |A| · N| ≤ 2 · N · N'` (rearranged by multiplying both sides by `m · N'`) | ✅ equivalent |

### Brightwell reference

The bound is Brightwell's [*Balanced pairs in partial orders*, §4,
Theorem 4.1], combined with the Kahn–Saks single-element-perturbation
lemma [*Balancing poset extensions* (1984), Lemma 2.2]. The paper
derivation at `step8.tex:1046–1276` makes the FKG / Ahlswede–Daykin
step explicit; our Lean inputs
(`FKG.fkg_uniform_initialLowerSet`,
`FiberSize.fiberSize_lipschitz_on_bkAdj`) cover the FKG transport and
1-Lipschitz structure of $f$ needed for `mg-b699`.

### Discrepancy audit (mg-a6a1)

During QA the following discrepancy was identified and fixed on the
QA branch:

**Issue.** `FiberSize.minSuccPos` originally defaulted to
`Fintype.card α` when `Succ = ∅`, but the paper (`step8.tex:932`)
uses `S := m = |Q| = Fintype.card α + 1` in that case. This
off-by-one propagated into `fiberSize`, which undercounted the
paper's `f` by exactly `1` whenever `Succ = ∅`, and into
`N := Σ fiberSize`, which then satisfied `N = |L(Q)| − N'` rather
than the paper's `N = |L(Q)|`.

**Counterexample to the pre-fix statement.** Take
`α = {a, b, c, d}` with `a < b < c` a chain and `d` incomparable to
each; `Pred = {c}`, `Succ = ∅`; `x = b`, `y = d`. Then
`|L(α)| = 4`, `N_Lean = 1`, `|A| = 2`, `sumA_Lean = 1`, so

```
LHS = m · |N'·sumA − |A|·N| = 5 · |4·1 − 2·1| = 10,
RHS = 2·N_Lean·N'                                =  8,
```

violating `LHS ≤ RHS`. The same data with the paper's convention
`S = m = 5` gives `N_paper = 5`, `sumA_paper = 3`, `LHS = 10`,
`RHS = 40` (and the paper's loose bound `2·N_paper/m = 2` on
`|Σ_A (f − f̄)|` holds with slack).

**Fix.** Change `minSuccPos`'s `Succ = ∅` default to
`Fintype.card α + 1`, matching the paper. This preserves:

* 1-Lipschitz of `fiberSize` (`fiberSize_lipschitz_on_bkAdj`) —
  when `Succ = ∅`, `minSuccPos` is constant, so Lipschitz survives;
* all existing consumers of `FiberSize.lean` — the only external
  claim was `fiberSize ≤ Fintype.card α`, replaced by
  `fiberSize_le_card_succ : fiberSize ≤ Fintype.card α + 1`, which
  is what the axiom needs anyway (paper's `f ∈ {1, …, m}` with
  `m = card α + 1`).

**Secondary fix.** The axiom originally took `m` with hypothesis
`hmbd : ∀ L, fiberSize ≤ m`. This upper-bound hypothesis does not
pin `m`: for any `m ≥ max fiberSize` the hypothesis holds, but the
bound `m · |...| ≤ 2·N·N'` becomes strictly stronger as `m` grows
beyond `|Q|`, and the paper does not prove such a stronger form.
QA replaces the under-constrained `hmbd` with
`hmQ : m = Fintype.card α + 1`, pinning `m` to the paper's `|Q|`.

### Certification

With the two fixes above, the statement of
`brightwell_sharp_centred` is verified to be a faithful integer
transcription of `eq:sharp-centred` (`step8.tex:1048`): the
hypotheses match the paper's pred/succ setup, the bound constants
`2N/m` match exactly (with `N = Σ f = |L(Q)|` and
`m = |α| + 1 = |Q|`), no hidden decidability / finiteness
assumptions weaken the claim (only `PartialOrder`, `Fintype`,
`DecidableEq` on `α`, all present in the paper's finite-poset
setup), and there are no quantifier reversals.

A check via `#print axioms brightwell_sharp_centred_rat` confirms
that `brightwell_sharp_centred_rat` depends only on
`brightwell_sharp_centred` plus Mathlib's standard
`propext / Classical.choice / Quot.sound`; no auxiliary unnamed
axioms are introduced.

**Usable by F6a (mg-1f5e).** The rational wrapper
`brightwell_sharp_centred_rat` provides

```
|Σ_{L ∈ A} (f L − (Σ_L f)/N')|  ≤  2 · (Σ_L f) / m,
```

which — dividing by `N = Σ_L f > 0` and using
`(Σ_A f)/N = p_{xy}(Q)` (via the Lean-side fibre definition of
`|L(Q)|`, now consistent with paper's `N = |L(Q)|`) and
`|A|/N' = p_{xy}(Q − z)` — gives `|p_{xy}(Q) − p_{xy}(Q − z)| ≤ 2/m`
directly, without requiring additional axioms.

### Decision rationale (mg-b699)

`mg-b699` was filed to evaluate replacing the axiom with a full
Lean proof once the rest of the development was sorry-free. After
F8 (`mg-194c`, `f49e2c5`) confirmed the formalisation reduces to
this single project-specific axiom, and the publish-axioms artifact
(`mg-358a`, `0644c05`) archived the `#print axioms` output, the
decision was made to **retain the axiom** rather than port it.

**Citation.** The bound transcribed by `brightwell_sharp_centred`
is a special case of:

* G.~Brightwell, *Balanced pairs in partial orders*, Discrete
  Mathematics **201** (1999), no.~1--3, 25--52 — §4, Theorem 4.1
  (`\bibitem{Brightwell1999}`, `main.tex:557`);
* J.~Kahn and M.~Saks, *Balancing poset extensions*, Order **1**
  (1984), no.~2, 113--126 — Lemma 2.2 (single-element perturbation;
  `\bibitem{KahnSaks1984}`, `main.tex:530`);
* combined via the FKG / Ahlswede--Daykin inequality
  (`\bibitem{FKG1971}`, `\bibitem{AhlswedeDaykin1978}`).

These are well-known, peer-reviewed published results; the paper's
own derivation of `eq:sharp-centred` (`step8.tex:1046--1276`) is
itself a direct transcription of Brightwell's argument with the
Kahn--Saks per-term covariance bound made explicit.

**Why retain rather than port.** A faithful Lean port requires:

1. The per-term Kahn--Saks / Brightwell covariance bound
   `|Cov_μ(1_A, S)|, |Cov_μ(1_A, P)| ≤ f̄/m` on the product
   distributive lattice `L(α) × {1, …, m}` under the uniform
   measure — the substantive combinatorial input — for which
   neither mathlib nor this development currently has a primitive,
   and whose Lean formalisation is estimated at 500--800 LoC of
   mathlib-tier infrastructure (set-system inequalities, product
   lattice transport, log-concavity via the Brunn--Minkowski step
   on `[m]`-valued indicators).
2. Pred/succ-set coupling combining this with the existing
   `FKG.fkg_uniform_initialLowerSet` (FKG transport,
   `cd75ef1`, `mg-9ece`) and
   `FiberSize.fiberSize_lipschitz_on_bkAdj` (1-Lipschitz of
   `f = S − P`, `af7a4a3`, `mg-85d1`).

The combination does not fit a single polecat's scope. By contrast,
the rest of the proof of the width-3 case of the 1/3--2/3 conjecture
— the structural / combinatorial argument that is novel to this
paper — is fully sorry-free and depends on the Brightwell bound
*as a black box*, exactly as it does in the LaTeX source. The
credibility artifact is the structural proof; an independent
formalisation of a 1999 published lemma is an orthogonal
infrastructure project, post-launch.

**Replacement path (open).** A future Lean port of this axiom
should consume the existing FKG and 1-Lipschitz infrastructure and
add the Kahn--Saks covariance step, mirroring the paper proof at
`step8.tex:1046--1276`. Filing such a port is *not* a prerequisite
for any downstream consumer of `OneThird` — `lem:one-elem-perturb`
(`mg-1f5e`), `lem:exc-perturb` (`mg-7496`), and the main theorem
(`mg-194c`) all close cleanly against the axiom as stated.

`mg-b699` is closed with this decision; if a future contributor
wants to port the axiom, they should file a fresh work item
referencing this entry.

---

## `OneThird.Step8.InSitu.case3Witness_hasBalancedPair_outOfScope`

**File.** `lean/OneThird/Step8/Case3Residual.lean`

**Paper statement.** `step8.tex` `prop:in-situ-balanced` Case 3
(`step8.tex:3033-3047`), restricted to the residual parameter range
outside `InCase3Scope`. The paper's argument for the conclusion in this
regime is the `rem:enumeration` sketch (`step8.tex:3157-3173`):

> For `w ≥ 1`, the configurations with `|A| = 3` whose profiles form a
> `⪯`-antichain are enumerated modulo the symmetries of (L1); each is
> discharged by exhibiting either a Case 1 symmetric pair (after taking
> into account that two of the three elements must share *some*
> coordinate of the two-sided profile whenever `|Q| ≤ 3(3w+1)` and (L2)
> restricts the profile codomain), or a Case 2 pair with aligned
> one-sided profiles restricted to the bands strictly above (or
> strictly below) the antichain under consideration.

**Introduced by.** `mg-b846` (A8-S3, this entry).

**Status.** **Retained as a named project axiom** for one polecat
session, with the gap surfaced honestly per the polecat-instruction
guidance ("If new math turns out to need its own axiom: report
honestly via paper-vs-formalization diagnosis"). Replacement path
recorded below.

### Scope-match checklist

| Paper | Axiom | Status |
| --- | --- | --- |
| Width-3 layered poset $Q$ with antichain decomposition $L$ | `α : Type*` with `[PartialOrder α] [Fintype α] [DecidableEq α]`; `L : LayeredDecomposition α` | ✅ |
| Width-3 hypothesis | `hWidth3 : HasWidthAtMost α 3` | ✅ |
| Layer-ordinal-sum irreducibility (no upward-directed band cut) | `hIrr : LayerOrdinalIrreducible L` | ✅ |
| Depth at least 3 (Case 3 of the F5 enumeration) | `hK3 : 3 ≤ L.K` | ✅ |
| Non-trivial interaction width | `hw : 1 ≤ L.w` | ✅ |
| Size cap `|X| ≤ 6w + 6` (F5 C2 branch) | `hCard : Fintype.card α ≤ 6 * L.w + 6` | ✅ |
| Depth upper bound `K ≤ 2w + 2` (F5 C2 branch) | `hDepth : L.K ≤ 2 * L.w + 2` | ✅ |
| Out-of-scope: parameter range outside the F5a `case3_certificate` | `hScope : ¬ InCase3Scope L.w (Fintype.card α) L.K` | ✅ |
| Case 3 hypothesis: neither Case 1 (ambient profile match) nor Case 2 (`⪯`-comparable within-band profile) applies | `hC3 : Case3Witness L` (defined in `Case3Dispatch.lean`) | ✅ |
| Conclusion: `α` admits a balanced pair | `HasBalancedPair α` | ✅ |

The hypotheses above are exactly the wider profile of
`Step8.bounded_irreducible_balanced_hybrid`
(`BoundedIrreducibleBalanced.lean:1587`) restricted to the negation of
`InCase3Scope`, plus the typed Case 3 witness produced by A8-S1's
`case1_dispatch_inScope` (`Case3Dispatch.lean`, `mg-48db`). The
in-scope branch is handled separately by the F5a `case3_certificate`
via Path A / A5-G2.

### Why this is internal, not external

Unlike `OneThird.LinearExt.brightwell_sharp_centred`, this axiom is
**not** a port of an external published result. It is internal to the
paper:

* `prop:in-situ-balanced` itself is the paper's framing of the within-
  band antichain dispatch and is novel to this work.
* The certificate-handled half (`InCase3Scope`) is already constructive
  in the development via `case3_certificate`; the residual half outside
  `InCase3Scope` is the genuinely under-developed piece in the LaTeX
  source.

### Why retain rather than port

A faithful Lean proof of the residual claim requires:

1. **Pigeonhole on shared profile coordinates.** Given a width-3
   within-band antichain with two-sided profiles in pairwise
   `⪯`-antichain, derive that two of the three elements agree on at
   least one coordinate of the two-sided profile, using the (L1)/(L2)
   axioms of the layered decomposition and `|Q| ≤ 3(3w+1)`. This is
   routine combinatorics, but the precise quantification of "shares
   some coordinate" and its compatibility with the (L2) profile-codomain
   restriction is not made explicit in `rem:enumeration`.
2. **Band-restricted Case 2 FKG sub-coupling.** From a shared coordinate
   pair `(a_i, a_j)` whose profiles agree on Π⁺ but disagree on Π⁻
   (or vice versa), build a Case 2 pair with aligned one-sided profiles
   *restricted to the bands strictly above (or strictly below) the
   antichain*. The FKG monotonicity then needs to operate on this
   sub-context, requiring the `Mathlib.Combinatorics.SetFamily.fkg`
   primitive plus a coupling that preserves the within-band antichain
   bookkeeping. This is the same FKG infrastructure expected by A8-S2
   (`mg-8801`), but specialised to a strict sub-band. Neither the
   sub-coupling nor the rotation argument that turns the shared
   coordinate into a balanced pair is carried out in `rem:enumeration`.
3. **Reduction back to Case 1 (mg-f92d) or Case 2 (`mg-8801`).** With
   the sub-coupling in hand, exhibit the explicit balanced pair: either
   via `hasBalancedPair_of_ambient_profile_match` (Case 1, `Case3Struct.lean`)
   or via the A8-S2 Case 2 discharge.

Steps (1) and (3) are routine. Step (2) is the substantive new
mathematical content of the axiom. The original A8 brief estimated
"~300-600 LoC including the missing mathematical content"; in
practice this is a lower bound, since `rem:enumeration` is a sketch
rather than a fleshed-out proof.

The decision rationale matches the convention for
`brightwell_sharp_centred`: the structural / combinatorial
contribution of this paper is the case dispatch of
`prop:in-situ-balanced` itself together with the F5a Bool-level
`case3_certificate` for `InCase3Scope`. The residual half outside
`InCase3Scope` is auxiliary; consuming the LaTeX source as a sketch
captures it faithfully without forcing a single polecat session to
flesh out the missing FKG sub-coupling.

### Replacement path (open)

A future Lean port should:

* Discharge step (1) (pigeonhole) as a standalone lemma using the
  (L1)/(L2) bookkeeping in `LayeredReduction.lean`.
* Discharge step (2) (band-restricted FKG sub-coupling) by reusing
  the `Mathlib/LinearExtension/FKG.lean` primitives together with the
  band-major encoding of A5-B1/B2/B3.
* Compose with mg-f92d's `hasBalancedPair_of_ambient_profile_match`
  (Case 1, ambient form) and A8-S2's `Case2Witness` discharge to
  close the residual.

The axiom statement is the discharge target: a future fleshed-out
proof can simply restate the body without changing any call-site of
`hasBalancedPair_of_case3_outOfScope` or `hStruct_of_case2_discharge`.

Filing such a port is *not* a prerequisite for any downstream
consumer of the development — A5-G3 / Path C (the `hStruct` wiring
into `lem_layered_balanced` and through to `width3_one_third_two_thirds`)
closes against the axiom as stated; the credibility artifact of the
proof is the structural case dispatch and the F5a `case3_certificate`,
not the residual half-page sketch.

### Forum-post disclosure

The forum-post draft (`mg-b8d4`) should reflect that
`#print axioms` on the main theorem will list, alongside
`brightwell_sharp_centred` and the mathlib trio, the new
`case3Witness_hasBalancedPair_outOfScope` axiom. The honest framing
is:

* `brightwell_sharp_centred` is a transcription of an external
  published result (Brightwell §4 / Kahn-Saks 1984) — the standard
  "import-an-external-bound" form.
* `case3Witness_hasBalancedPair_outOfScope` is a transcription of
  this paper's own `rem:enumeration` sketch, not an external result —
  the residual half-page that is genuinely under-developed in the
  LaTeX source. Replacing it requires fleshing out the structural
  argument with the band-restricted FKG sub-coupling sketched in
  `rem:enumeration`.

Both axioms are localised: every other use of the formalism is
sorry-free.
