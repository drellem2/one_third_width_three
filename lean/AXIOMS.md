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

**QA-audited by.** `mg-7377` (A8-S3-QA; this entry — verdict
**axiom is faithful**, see "QA verdict (mg-7377)" below).

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

The headline `#print axioms` output additionally lists six
`_native.native_decide.ax_1_1` entries — one per `native_decide`
invocation in the proof closure
(`Step8.Case3Enum.case3_balanced_w{1,2,3,4}` for the F5a Case-3
enumeration certificate at K=3; the `mg-9a4a` Window C small-size
extension `case3_balanced_K4_w1`; plus `Step8.OptionC.case2_certificate`
for the Option-C Stage-1 K=2 closure). Each is a per-invocation
instance of Lean's `Lean.ofReduceBool` axiom underlying
`native_decide`; the trust surface is "the Lean compiler evaluates
Bool decidable predicates correctly" — standard Lean practice for
finite case analysis. These are not project axioms (they are
introduced by Lean's `native_decide` tactic, not by an `axiom`
declaration in this development), so they are out of scope for
this catalogue, but a forum reader auditing the verbatim
`#print axioms` output (`lean/PRINT_AXIOMS_OUTPUT.txt`) will see
them and they should be disclosed alongside the two named project
axioms when the forum-post foregrounds the full trust surface.

Both project axioms are localised: every other use of the
formalism is sorry-free.

### QA verdict (mg-7377)

**Verdict.** **Axiom is faithful.** The axiom statement is a faithful
transcription of `prop:in-situ-balanced` Case 3 restricted to
`¬ InCase3Scope`. The audit found no missing or extra hypotheses, the
conclusion matches the paper, and the AXIOMS.md disclosure (above)
honestly surfaces the genuine gap (the paper sketch in
`rem:enumeration` is not a fleshed-out proof; the band-restricted FKG
sub-coupling is the substantive new mathematical content needed for a
replacement).

**Audit performed.**

1. **Hypothesis profile match.** Each of the nine axiom hypotheses
   (`L`, `hWidth3`, `hIrr`, `hK3`, `hw`, `hCard`, `hDepth`, `hScope`,
   `hC3`) was matched against (a) the wider hypothesis profile of
   `Step8.bounded_irreducible_balanced_hybrid`
   (`BoundedIrreducibleBalanced.lean:1587`) and (b) the paper's
   `prop:in-situ-balanced` (`step8.tex:2965-3048`). The seven
   structural hypotheses (`L`, `hWidth3`, `hIrr`, `hK3`, `hw`,
   `hCard`, `hDepth`) are byte-for-byte identical to the hybrid
   theorem; the two extra hypotheses (`hScope`, `hC3`) are exactly the
   residual-scope flag and the typed Case 3 witness from A8-S1
   (`mg-48db`, `Step8.InSitu.Case3Witness L = ¬Case1 ∧ ¬Case2Witness L`).
   No hypothesis is missing; no extras are present.

2. **Size-cap relationship to the paper.** The axiom uses
   `|α| ≤ 6w + 6` (the F5 C2 leaf cap) where the paper's
   `prop:in-situ-balanced` uses `|Q| ≤ 3(3w+1) = 9w + 3`. For `w = 1`
   the two coincide (`12 = 12`); for `w ≥ 2` the axiom's hypothesis is
   strictly tighter (e.g. `18 ≤ 21` for `w = 2`). A tighter hypothesis
   means the axiom is **no stronger** than the paper's claim, which is
   conservative and faithful.

3. **Conclusion.** `HasBalancedPair α` matches the paper's "$Q$
   contains a balanced pair" exactly.

4. **Quantifier order.** Standard universal closure over `L` and the
   eight propositional hypotheses; no Skolem reordering or implicit
   choice beyond what the paper makes explicit.

5. **Sketch credibility.** The paper sketch in `rem:enumeration`
   (`step8.tex:3157-3173`) is genuinely a sketch (not a fleshed-out
   proof), but it is a credible structural argument: (a) pigeonhole
   on shared profile coordinates given `|Q| ≤ 3(3w+1)` and the (L2)
   profile-codomain restriction is plausible (and the AXIOMS.md
   "Replacement path" calls it out as routine combinatorics);
   (b) the reduction back to Case 1 (`mg-f92d`) or Case 2 (band-
   restricted A8-S2 / `mg-8801`) is well-defined as a target,
   modulo the band-restricted FKG sub-coupling. The paper itself
   appeals to this sketch for `lem:enum`'s depth-`≥ 3` extension
   ("`extended to profiles of 3-element antichains with 2w
   near-bands` produces a balanced pair in every case",
   `step8.tex:3066-3068`). The axiom transcribes the sketch's
   conclusion at the polecat-instruction-blessed level of fidelity
   ("If new math turns out to need its own axiom: report honestly").

6. **Cross-reference.** `docs/a8-s3-status.md` and the AXIOMS.md
   entry above (the body of this section) are both consistent with
   the axiom statement and with each other. The "Replacement path
   (open)" enumerates the same three steps in both files (pigeonhole,
   band-restricted FKG sub-coupling, reduction back to Case 1/2).

**Caveats noted but not blocking.** The axiom's `Case3Witness L`
hypothesis (`¬Case1 ∧ ¬Case2Witness L`) is broader than the paper's
explicit Case 3 entry condition (`|A| = 3` with three pairwise
`⪯`-incomparable two-sided profiles). A future port that derives the
positive width-3 antichain configuration from the negation will need
to rule out degenerate band-cardinality cases (e.g. `|A| = |B| = 1`
under irreducibility); the paper's case dispatch implicitly assumes
`|A| ≥ 2` or `|B| ≥ 2`, which follows from width-3 + irreducibility +
non-trivial cross-pair but is not explicit in `prop:in-situ-balanced`.
This is a paper-side nuance, not an axiom-faithfulness issue: the
axiom's conclusion is no stronger than the paper's. Recorded here so
that the future replacement-path port carries the bookkeeping
forward.

### Scope narrowing (`mg-9a4a`, post-mg-9d6c Window C, small size-limit variant)

**The axiom signature is unchanged.** The narrowing operates by
*widening* the `InCase3Scope` predicate that gates the axiom's
`hScope : ¬ InCase3Scope` hypothesis, so the negation `¬ InCase3Scope`
captures a strictly smaller parameter range. The trust surface stays
at 4 named project axioms; only the axiom's effective parameter range
shrinks.

**Before mg-9a4a.** `InCase3Scope w card K` was the conjunction

```
K = 3 ∧ w ∈ {1, …, 4} ∧ (w = 1 → card ≤ 9) ∧ (w ≥ 2 → card ≤ 7)
```

corresponding to the four F5a `case3_certificate` slices
`case3_balanced_w{1,…,4}` of `mg-307c`.

**After mg-9a4a (Window C of `docs/compatibility-geometry-pathP3-scoping.md`,
small size-limit variant).** `InCase3Scope w card K` widens to the
two-way disjunction

```
(K = 3 ∧ w ∈ {1, …, 4} ∧ size caps)    ∨    (K = 4 ∧ w = 1 ∧ card ≤ 8)
```

The K=3 disjunct is unchanged (the original 4 size-cap slices). The
K=4 disjunct is new: 50 K=4-w=1 band-tuples at `c ≤ 8`. The new Bool
entry is discharged by `native_decide` in `case3_certificate`:

* `case3_balanced_K4_w1 : allBalancedAtK 4 1 8 = true`.

**Small size-limit variant — what's still axiomatic.** The full
Window C target of the scoping doc would also include

* the `K = 4, w = 1, c ∈ {9, …, 12}` slice (31 K=4-w=1 band-tuples
  at higher `c`); and
* the `K = 3` c-sliver at `c ∈ {8, 9}` for `w ∈ {2, 3, 4}`
  (12 K=3 band-tuples).

Each of these 43 band-tuples has `nfree ≥ 18` (close to the existing
`enumPosetsFor` engineering cap at `nfree ≤ 27`), and the `2^nfree`
native-decide evaluation does not fit the local build window. The
residual axiom continues to apply on those 43 tuples; the remaining
50 of 93 Window C tuples (the K=4-w=1 small-`c` slice) are
discharged here.

**Net effect on the axiom.** The negation `¬ InCase3Scope` now
additionally excludes `(K = 4, w = 1, c ∈ {1, …, 8})`.  Callers of
`case3Witness_hasBalancedPair_outOfScope` cannot land on those 50
small-`c` K=4-w=1 tuples — the F5a certificate-driven branch
discharges them instead.

**What this does NOT do.** The narrowing **does not eliminate** the
axiom. The bulk of the residual parameter range (`K ≥ 5`, and
`K = 4 ∧ w ≥ 2`) remains axiomatised. Per
`docs/compatibility-geometry-pathP3-scoping.md` §2 the residual is
dominated by `~10^5` band-tuples at `w = 4` of which `~99%` have
`nfree > 27` (the `enumPosetsFor` engineering cap), so the bulk is
not addressable by enumeration alone. Elimination of the bulk
requires either the `A8-S2-cont` probability-form cross-poset FKG
infrastructure (`~2000`–`3500` LoC, multi-polecat) or the Garland-
style high-dimensional-expander spectral argument that is the
`mg-c853 §3 Step 2` load-bearing open math.

**Computational trust surface.** Each new `native_decide` invocation
(`case3_balanced_w{2,3,4}_sliver`, `case3_balanced_K4_w1`) adds one
`_native.native_decide.ax_1_1` instance to `#print axioms` output —
the same form already counted for the existing K=3 certificate. The
headline "the Lean compiler evaluates Bool decidable predicates
correctly" framing of the disclosure is unchanged; the
`native_decide` count below "Forum-post disclosure" rises from 5 to
9 (four new sliver/K4 certificates), but the named project axiom
count stays at 4.

**Forward replacement path unchanged.** The three-step replacement
plan ((1) pigeonhole on shared profile coordinates, (2) band-restricted
Case 2 FKG sub-coupling, (3) reduction back to Case 1 / Case 2) is
independent of this narrowing: it would replace the axiom uniformly
over the entire `¬ InCase3Scope` range, whatever the value of
`InCase3Scope`. The mg-9a4a narrowing reduces the surface area that
a future port has to cover, but does not change the substantive math
content required.

---

## `OneThird.Step8.lem_layered_balanced_irreducible_base`

**File.** `lean/OneThird/Step8/LayeredBalancedFull.lean`

**Paper statement.** `step8.tex` `prop:in-situ-balanced` Cases 2 + 3
(`step8.tex:3096-3210`), the irreducible base case of
`lem:layered-balanced` (the full Step 8 G4). The proposition: a
width-3 non-chain poset `β` admitting a layered decomposition `L` of
interaction width `L.w ≤ 4` that is **layer-ordinal irreducible** and
has **no profile collision** contains a balanced pair. The paper's
argument for this regime is the Ahlswede–Daykin / FKG
profile-ordering inequality for linear extensions (Case 2) together
with the finite enumeration of width-3 profile antichains (Case 3 /
`rem:enumeration`).

**Precision (mg-44f1 audit).** The axiom is *not* a literal
transcription of `prop:in-situ-balanced`: that proposition is stated
**with** the size bound `|Q| ≤ 3(3w+1)`, whereas the Lean axiom
**drops** it. The drop is correct and necessary — mg-65de §3 showed
the irreducible residual is genuinely *unbounded* (`P_K = {1,…,K},
i<j ⇔ j−i>2`). So the axiom is the **unbounded extension** of
`prop:in-situ-balanced` Cases 2+3 / `lem:enum` (the size bound
removed; the `rem:enumeration` "extended to … `2w` near-bands"
parenthetical taken as the intended content), not the bounded
proposition verbatim.

**Introduced by.** `mg-65de` (OneThird-Piece6-Redo, this entry).

**QA-audited by.** `mg-44f1` (OneThird-Piece6-Axiom-Verify) — verdict
**TRUE — strong evidence**; provisional accept recommended to become
permanent. See "QA verdict (mg-44f1)" below and the full report
`docs/state-Piece6-Axiom-Verify-Session1.md`. The mg-65de
block-and-report is `docs/state-Piece6-Redo-Session1.md`.

**Status.** **Disclosed project axiom — RETAINED; mg-44f1 audit
recommends permanent accept (pm-onethird to relay to Daniel).**
This is the genuine, *minimal* residual of Piece 6 (the full Step 8
G4 lemma `lem_layered_balanced_full`). It is a sub-lemma **strictly
weaker** than the headline `lem_layered_balanced_full`: the two extra
hypotheses `hIrr` (irreducibility) and `hNoTwin` (no profile
collision) carve out a proper sub-case, and the complementary cases
are **genuinely proved**:

* the **reducible** case (`¬hIrr`) — Case B of
  `lem_layered_balanced_full`: the genuine ordinal-sum recursion plus
  the de-vacuified `lem_layered_reduction` (`LayeredReduction.lean`);
* the **profile-collision** case (`¬hNoTwin`) — Case C-twin:
  `hasBalancedPair_of_ambient_profile_match` (`Case3Struct.lean`),
  the transposition-automorphism argument giving `Pr = 1/2`.

So `lem_layered_balanced_full` = (reducible: proved) ∨ (twin: proved)
∨ (irreducible ∧ twin-free: this axiom). The axiom is **not** a
headline-equivalent dodge.

### Scope-match checklist

| Paper | Axiom | Status |
| --- | --- | --- |
| Width-3 layered poset `β` with layered decomposition `L` | `β : Type u` with `[PartialOrder β] [Fintype β] [DecidableEq β]`; `L : LayeredDecomposition β` | ✅ |
| `|β| ≥ 2` | `h2 : 2 ≤ Fintype.card β` | ✅ |
| `β` is not a chain | `hNotChain : ¬ IsChainPoset β` | ✅ |
| Width-3 hypothesis | `hW3 : HasWidthAtMost β 3` | ✅ |
| Interaction width `w ≤ 4` (the headline cap, `step8.tex:576` `w₀(γ) ≤ 4`) | `hLw : L.w ≤ 4` | ✅ |
| Layer-ordinal-sum irreducible (`prop:in-situ-balanced` treats the irreducible factor; reducible posets reduce by `cor:reducibility-transfer`) | `hIrr : ¬ ∃ k, 1 ≤ k ∧ k < L.K ∧ LayerOrdinalReducible L k ∧ both sides non-empty` | ✅ |
| No symmetric within-band pair / profile collision (Case 1 of `prop:in-situ-balanced` excluded; Cases 2+3 are the residual) | `hNoTwin : ¬ ∃ a a', a ≠ a' ∧ (∀ z, a < z ↔ a' < z) ∧ (∀ z, z < a ↔ z < a')` | ✅ |
| Conclusion: `β` admits a balanced pair | `HasBalancedPair β` | ✅ |

### Why an axiom and not a proof (mg-65de genuine attempt)

Ticket mg-65de instructed: *attempt genuine formalization; do NOT
default to a new axiom; if a sub-piece truly cannot be formalized,
block-and-report with a precise minimal axiom proposal.* The genuine
attempt established:

1. **`Case3Witness_proof` cannot serve as the base case.** It needs
   `Function.Injective L.band` (singleton bands) load-bearing in
   every branch; Piece 6's `L` is a `def:layered` decomposition with
   bands of size `≤ 3` (mg-fdc2 §3.1-§3.2). Verified.

2. **The paper's window-localization Case C1 is invalid for
   irreducible posets.** An ordinal middle piece needs both boundary
   cuts clean (no straddling incomparable pair); a layer-ordinal
   *irreducible* poset has **no** clean cut, so the only window is
   `W = X` itself. The paper's `W(i,j) = L_{min−w} ∪ ⋯ ∪ L_{max+w}`
   is *not* in general an ordinal middle piece (boundary bands differ
   by a single index, which (L2) does not bridge for `w ≥ 1`). This
   is a genuine gap in the paper proof — see
   `docs/state-Piece6-Redo-Session1.md` §3.

3. **The residual is genuinely unbounded.** The paper's
   `prop:in-situ-balanced` size bound `|Q| ≤ 3(3w+1)` does **not**
   hold for irreducible posets: the poset `{1,…,K}` with
   `i <_P j ⇔ j − i > 2` is layer-ordinal irreducible, width 3, of
   interaction width `w = 2`, with `K` *unbounded*. So the existing
   bounded enumeration certificates (`case3_certificate`, the mg-4d7b
   Python enumeration) do **not** cover the residual.

4. **The FKG inequality for linear extensions is not in the tree.**
   The Ahlswede–Daykin / FKG profile-ordering inequality that paper
   Case 2 invokes is listed as future work
   (`Mathlib/RelationPoset/FKG.lean §11`); the in-tree
   `Case2FKGSubClaim` is **provably false** (`OptionC/K2Closure.lean:21`).

A faithful Lean proof therefore requires the FKG-for-linear-extensions
infrastructure (estimated multi-polecat, `~2000`–`3500` LoC) plus a
genuinely new argument for the unbounded irreducible regime — neither
of which is within a single Piece-6 ticket. The axiom is the precise,
minimal residual, filed for pm-onethird review.

### Replacement path

1. Port the Ahlswede–Daykin / FKG inequality for linear extensions
   (replacing the provably-false `Case2FKGSubClaim` — whose `pair`
   field is direction-flipped — with a correctly-directed FKG
   sub-claim) — `Mathlib/RelationPoset/FKG.lean §11`. This part is a
   *standard, true, externally-citable* correlation inequality.
2. Formalise `prop:in-situ-balanced` Case 2 (FKG profile-ordering ⇒
   `Pr ≥ 1/2`, then balanced-or-rotation) for non-singleton bands.
3. Formalise `prop:in-situ-balanced` Case 3 (the width-3 profile
   antichain enumeration) for the *unbounded* irreducible regime.
   **mg-44f1 sharpening: step 3 is genuinely new mathematics, not a
   porting exercise** — the paper's bounded enumeration provably does
   not cover the unbounded irreducible regime, and there is no
   published width-3 1/3–2/3 theorem to cite. The most promising
   route is the "near-twin" argument (`docs/state-Piece6-Axiom-Verify-
   Session1.md` §2.3): under `hNoTwin` + bounded `w`, a most-similar
   incomparable pair always exists and is always balanced — strongly
   supported by the mg-44f1 search but not yet proven.

**mg-44f1 recommended refinement (preferred form).** Split the axiom
along the Case-2 / Case-3 boundary: once step 1 lands, the Case-2
(FKG profile-ordering) content can become a *separate, external-
citable* axiom (brightwell-class, audit-bar 4/4), leaving a strictly
smaller internal axiom carrying only the genuinely-novel Case-3
residual. This is the only refinement that *lowers* the trust surface
rather than relocating it. See
`docs/state-Piece6-Axiom-Verify-Session1.md` §4.

Until then the axiom is retained, fully disclosed, and **strictly
weaker** than the theorem it supports.

### QA verdict (mg-44f1)

**Verdict. TRUE — strong evidence.** The audit determined the
*statement* is true (a full proof is out of scope — FKG-for-linear-
extensions is not in tree). Basis:

1. **It is a special case of the 1/3–2/3 conjecture** restricted to
   the class {width-3, non-chain, `|β|≥2`, admits an irreducible
   width-`≤4` layered decomposition, twin-free}. The conjecture is
   open in general but is verified in the literature to `n = 11`, has
   a proven lower bound `δ* ≥ 0.2764`, and is the very result this
   paper establishes at width 3. The axiom's truth does not depend on
   the paper's separate Hypothesis A (that concerns Steps 1–7).

2. **Counterexample search — zero counterexamples.** An independent
   exact-rational linear-extension verifier
   (`scripts/onethird_mg44f1_axiom_probe.py`,
   `..._deep.py`) checked **1 118 061 posets** exhaustively or via
   structured family — including the canonical unbounded residual
   family `P_K` to `K = 200`, every width-3 non-chain poset to
   `n = 7`, and the singleton-band irreducible width-3 `w≤4` class
   exhaustively to `K = 9` (1 070 326 posets — the mg-4d7b cap-1
   regime run *unbounded*) — plus 2 847 random in-class posets. Zero
   counterexamples. The safest balanced pair stays a strictly
   positive margin inside `[1/3,2/3]` everywhere: minimum
   `safety = 1/51 ≈ 0.0196` over the exhaustive class; `P_K`
   converges to `≈ 0.087`. The margin does not decay with size.

3. **Structural sanity.** twin-free + bounded interaction width
   guarantees "near-twin" incomparable pairs (within-band profiles
   differ only inside the bounded near-band window); the search
   confirms such a pair is always the safest and always balanced.

**Retained-axiom audit bar.** The axiom meets `difficult` (✓) and
`labeled` (✓); fails `external` (✗ — it is the project's own
proposition, not external literature, unlike
`brightwell_sharp_centred`); and meets `low-risk` only partially (◑ —
low risk of being *false*, but it is an instance of an *open*
conjecture, not a proof-backed result). Score ≈ 2.5/4 — the same
category as `case3Witness_hasBalancedPair_outOfScope`, a
strictly-weaker justification than `brightwell_sharp_centred` (4/4).
This supports *retaining* the disclosed axiom (the established bar for
an internal residual with an honest replacement path) but **not**
disclosing it as a brightwell-class external import.

**Load-bearing precision.** As of this audit the axiom is **not** on
the live `#print axioms width3_one_third_two_thirds` dependency
(`lean/PRINT_AXIOMS_OUTPUT.txt`) — it is consumed only by
`lem_layered_balanced_full` (Piece 6 of the FULL REFACTOR) and its
example file. It *is* the intended G4 endpoint; when the Piece-6
route is wired into the headline it should **replace**
`case3Witness_hasBalancedPair_outOfScope`, not add to it.

**Residual risk.** The axiom is an instance of an open conjecture
backed by no proof (the paper's proof of this region is broken — see
the mg-65de findings; the errors are in the proof *method*, not the
*target*). Its acceptability rests on the independent evidence above,
not on the paper's authority. Full statement of residual risk:
`docs/state-Piece6-Axiom-Verify-Session1.md` §6.

---

## `OneThird.Step8.stepsOneToSevenCascade`

**File.** `lean/OneThird/Step8/Cascade.lean`

**Paper statement.** `step8.tex` `thm:main-step8` (`step8.tex:106-260`),
the **Steps 1-7 cascade** segment of the proof-by-contradiction: a
minimal width-3 indecomposable `γ`-counterexample, once Theorem E
(`cexImpliesLowBKExpansion`, landed sorry-free) supplies the
low-conductance cut `S ⊆ 𝓛(P)`, is driven through Steps 1-7 of the
paper — the BK-expansion bound, the per-fiber staircase (Steps 1-4),
the Rich-or-Collapse dichotomy (Step 5, `step5.tex:77` `thm:step5`),
the pointwise / most-good closures (Step 6), and the layered collapse
(Step 7, `step7.tex:1173` `prop:72` + `prop:71` + `lem:bandwidth`).
The output is the Step-5 dichotomy: either the richness route (which
yields a balanced pair, contradicting the counterexample) or the
collapse route delivering a bridge-ready `ChainLiftData` — a Dilworth
chain triple with chain potential, sync maps, bandwidth `K_bw ≤ 2`,
strict poset-monotone potential (`prop:71`), and `O_T(1)` exceptional
budget (`lem:bandwidth`).

**Introduced by.** `mg-52e0` (OneThird-MA-Cascade, FULL REFACTOR
Phase 2 Piece-4 body — this entry).

**QA status.** Pre-flight-pinned by `mg-92a8` (the Piece-4 signature
contract `docs/state-Piece4-Sig-Session1.md`); the contract §5.3/§5.4
satisfiability-verified the cascade codomain. The session state doc
is `docs/state-MA-Cascade-Session1.md`.

**Status.** **Disclosed project axiom — RETAINED.** This axiom is the
honest representation of the un-ported Steps 1-7 paper cascade. It is
**not new debt** — it is a `sorry → documented axiom` *upgrade*:

* Before Piece 4, the Steps-1-7 `w₀(γ) ≤ 4` delivery gap lived as the
  structured `sorry` at `MainAssembly.lean` (`caseC_canonicalLayered`,
  `PROOF-STRUCTURE-ONBOARDING.md` §0 / pitfall #3 / #5). That `sorry`
  is *exactly* this gap (mg-5fbd 7th-vacuity audit: architecturally
  unclosable in-place; closing it honestly requires the multi-month
  Steps 1-6 cascade port).
* Piece 4 rewrites the headline to proof-by-contradiction and replaces
  that `sorry` with this **named, paper-faithful, `AXIOMS.md`-certified
  axiom** — strictly more auditable than an anonymous `sorry`.

Axiomatising Steps 1-7 is the project's sanctioned posture: mg-ac13
Option C and mg-6ab8 explicitly recommend it, and the onboarding §1
step 1 records "Steps 1-7 are paper-axiomatised". The structural
backbone of the headline is Step 8 (G4, `lem_layered_balanced_full`)
plus the S7-F bridge — both genuinely in tree; Steps 1-7 is the
upstream cascade whose full Lean port is multi-month / multi-MTok
(mg-6ab8 Option A, 6-9M tokens).

### Scope-match checklist

| Paper | Axiom | Status |
| --- | --- | --- |
| `γ`-counterexample with `γ ∈ (0, 1/3]` | `γ : ℚ`, `hγ_pos : 0 < γ`, `hγ_third : γ ≤ 1/3` | ✅ |
| Width-3 hypothesis | `hP : HasWidthAtMost α 3` | ✅ |
| Minimal counterexample is indecomposable (`rem:decomp-reduction`) | `hI : Indecomposable α` | ✅ (supplied by `decomp_reduction`, mg-7969) |
| `α` is a `γ`-counterexample | `hCex : IsGammaCounterexample α γ` | ✅ |
| `|α| ≥ 2` | `h2 : 2 ≤ Fintype.card α` | ✅ |
| Hypothesis A (`hyp:arith`, `step8.tex:9-23`) | `hArith : HypothesisArithmetic` | ✅ (in-Lean predicate, not an axiom) |
| `α` large enough to realise the cascade (`n ≥ n₀`) | `hn0 : n_zero γ (hArith.T γ) ≤ Fintype.card α` | ✅ |
| Theorem E low-conductance witness (`thm:cex-implies-low-expansion`) | `hS : ∃ S, γ·vol(univ) ≤ vol S ∧ Φ(S) ≤ 2/(γn)` | ✅ (produced by `theoremE_lowConductanceWitness`, mg-3638) |
| Conclusion: Step-5 dichotomy (R) or (C) | `Step5R α γ (hArith.T γ) ∨ Step5C α (hArith.T γ)` | ✅ |

Every hypothesis is load-bearing: the axiom is invokable only for a
genuine minimal `γ`-counterexample realised above `n_zero` with the
Theorem-E witness in hand.

### Why an axiom and not a proof

The genuine mathematical content — BK-expansion ⇒ Steps 1-4 staircase
⇒ Step-5 Rich-or-Collapse ⇒ Step-6 closures ⇒ Step-7 layered collapse
— is a multi-month Lean port. The current tree has:

* the **abstract** Step-5 dichotomy `Step5.thm_step5`
  (`Step5/Dichotomy.lean`) — a genuine `rcases` theorem, but it
  consumes the per-triple structural inputs as hypotheses; deriving
  those from the low-conductance witness is the Steps 1-4 cascade,
  not in tree;
* the Steps 1-6 grounded cascade `cascade_steps_1_6_grounded`
  (mg-496b, parametric);
* Step 7's `Step7.LayeredWidth3` — which `mg-ca83` Checkpoint 3 found
  is a *rich-pair window packaging with no poset-structural content*;
  there is **no consumable α-side `ChainLiftData`-valued cascade**.

The Piece-4 signature contract `mg-92a8` §7 anticipates exactly this:
*"If, at `mg-MA-Cascade` kickoff, the Piece-1/2 α-side concretisation
is not consumable, that is a hold-the-line finding to surface — not a
defect of this contract (the signatures are correct; the discharge is
the cross-piece work)."* This axiom *is* that disclosed cross-piece
discharge.

### Non-vacuity

The axiom is **not** a `true → false` pin. Its codomain disjunct
`Step5C` (the F2-widened bridge-ready `ChainLiftData` existence) is
satisfiability-verified against the landed S7-F bridge:
`GridChainLift.grid_Step5C` inhabits `Step5C` on the genuine width-3
non-chain 3×3 grid (`gridChainLiftData`), and
`GridChainLift.grid_Step5C_fires_bridge` feeds that witness through
`lem_layered_from_step7` to a genuine three-cap output. Both
`PotPosetMono` and `ExcBudget` provably *fail* for the degenerate
3-disjoint-chains family `Δ_ℓ` (Piece-4 contract §5.3), so the
codomain is a genuine soundness filter.

### Replacement path

Port Steps 1-7 of the paper to Lean (mg-6ab8 Option A, the multi-month
arc): wire the Steps 1-4 per-fiber staircase into the Step-5 abstract
dichotomy `thm_step5`; ground Step 6; and replace `Step7.LayeredWidth3`
with a genuine `ChainLiftData`-valued Step-7 collapse delivering
`prop:72`'s `w₀(γ) ≤ 4`. The Piece-4 signature contract is fixed so
that `mg-MA-Cascade` (this file) needs no downstream signature
re-scope when that port lands — `stepsOneToSevenCascade` becomes a
theorem with no change to its consumers.

**Retained-axiom audit bar.** Meets `difficult` (✓ — a multi-month
port) and `labeled` (✓ — pinned by mg-92a8 to a specific paper
segment); fails `external` (✗ — the project's own Steps 1-7, not an
external citation); meets `low-risk` partially (◑ — the paper's
Steps 1-7 are a genuine published proof, but not yet independently
Lean-checked). Same category as
`case3Witness_hasBalancedPair_outOfScope` and
`lem_layered_balanced_irreducible_base` — a disclosed internal axiom
with an honest replacement path, retained pending the Steps 1-7 port.

## `OneThird.Step8.width3_smallN_hasBalancedPair`

**File.** `lean/OneThird/Step8/MainAssembly.lean`

**Paper statement.** `step8.tex` `lem:small-n` (`step8.tex:757-825`)
together with `rem:small-n` (`step8.tex:827-874`): every finite
width-≤ 3 non-chain poset on `n < n₀(γ, T)` elements — below the
cascade-realisability threshold — has a balanced pair. The paper
proves it by the two-regime base-case argument: the **large-`γ`
regime** (`γ ≥ 1/3 − δ_KL`) by the unconditional Kahn–Linial bound
`δ(P) ≥ δ_KL ≈ 0.276` [KahnLinial1991]; the **small-`γ` regime**
(`γ < 1/3 − δ_KL ≈ 0.057`) by a finite exhaustive enumeration of
width-3 posets on `≤ n₀` elements (`step8.tex:785-814`).

**Introduced by.** `mg-9add` (OneThird-MA-Body, FULL REFACTOR Phase 2
Piece-4 body — this entry; finding F-Body-1).

**QA status.** The session state doc is
`docs/state-MA-Body-Session1.md` (finding F-Body-1). The mg-92a8
Piece-4 signature contract §4.8 pinned this leaf as a "mechanical"
combinator `n_zero_le_of_cascade_realised : n_zero γ T ≤ |α|` — that
pin is **ill-posed** (false for every minimal counterexample with
`|α| < n_zero γ T`, a non-empty reachable regime since
`n_zero ≥ C_exc T ≥ 6`). The honest body uses a `by_cases` dichotomy;
this axiom is the small-`|β|` leaf.

**Status.** **Disclosed project axiom — RETAINED.** The genuine
mathematical content is two un-ported pieces: the Kahn–Linial bound
is an external theorem not in mathlib; the finite enumeration is a
mechanical computation not formalised. The in-tree `Step8.lem_small_n`
(`SmallN.lean`) is **not** a discharge — it packages both regimes'
outputs as the hypothesis `HasBalancedPair α ∨ HasBalancedPair α`, so
it cannot close the proof-by-contradiction's small-`n` leaf. This
axiom supplies the genuine output.

### Non-vacuity

Not a `true → false` pin. The hypotheses are satisfiable jointly —
e.g. `Antichain3` (width-3, non-chain, `|·| = 3 < n_zero γ T` for any
`γ ∈ (0, 1/3]`) — and the conclusion `HasBalancedPair Antichain3` is
genuinely true (the antichain's elements are pairwise symmetric,
`Pr = 1/2`). The statement is a special case of the 1/3–2/3
conjecture itself, true with the same standing as
`lem_layered_balanced_irreducible_base`.

### Replacement path

Two independent ports, both orthogonal to the Steps 1-7 cascade:
formalise the Kahn–Linial bound `δ(P) ≥ (5−√5)/10` for finite
non-chain posets (an external-result port), and formalise the
width-3 finite-enumeration decision procedure of `step8.tex:785-814`
(a `Decidable`-instance + `native_decide` engineering task, the
same flavour as the in-tree `Case3Enum` machinery). Either regime
ported standalone shrinks the axiom; both ported retire it.

**Retained-axiom audit bar.** Meets `difficult` (✓ — two separate
ports, one of an external theorem); meets `labeled` (✓ — pinned to
`lem:small-n` / `rem:small-n`); meets `external` partially (◑ — the
large-`γ` regime *is* an external citation [KahnLinial1991]; the
small-`γ` enumeration is project-internal); meets `low-risk`
partially (◑ — an open-conjecture instance, but the Kahn–Linial
regime is proof-backed). Same category as
`lem_layered_balanced_irreducible_base`.

## `OneThird.Step8.nonChain_compl_of_no_balancedPair`

**File.** `lean/OneThird/Step8/MainAssembly.lean`

**Paper statement.** `step8.tex` `thm:main-step8` perturbation step
(`step8.tex:106-260`): in the proof-by-contradiction, for a width-≤ 3
non-chain **indecomposable** poset `β` with **no balanced pair**, the
deletion of the bounded exceptional set `X^exc` (`|X^exc| ≤ C_exc T`,
an `O_T(1)` bound) from a large `β` (`n₀(γ, T) ≤ |β|`) leaves a
**non-chain** poset on the complement `P|_{X∖X^exc}` — so that the
full Step 8 G4 (`lem_layered_balanced_full`) applies to it.

**Introduced by.** `mg-9add` (OneThird-MA-Body, FULL REFACTOR Phase 2
Piece-4 body — this entry; finding F-Body-2).

**QA status.** The session state doc is
`docs/state-MA-Body-Session1.md` (finding F-Body-2). The mg-92a8
Piece-4 signature contract §4.8 pinned this as a "mechanical"
combinator `non_chain_subtype_of_exc`, justified by "a width-3
non-chain `α` has `≥ |α| − 3` incomparable pairs; deleting `O_T(1)`
elements leaves one." That justification is **false**: a width-3
non-chain poset can concentrate all its incomparability on an
`O_T(1)` vertex cover (a long chain plus `O(1)` floaters has just
those `O(1)` elements in every incomparable pair), so the counting
fails. The fact is true only via `hNoBP`.

**Status.** **Disclosed project axiom — RETAINED.** The genuine
reason `↥(X^exc)ᶜ` is non-chain is `hNoBP`: were `↥(X^exc)ᶜ` a chain,
every incomparable pair of `β` would touch `X^exc`; since `β` is
indecomposable it has `≥ |β|` ordered incomparable pairs
(`card_univ_le_ordIncompPairs_card`, in tree), so some
`X^exc`-element is incomparable to a long *contiguous* sub-chain of
`↥(X^exc)ᶜ` — and a floater incomparable to a long range of a chain
forms a **balanced** pair with that range's middle (`Pr ≈ 1/2`),
contradicting `hNoBP`. That is Step-8-level combinatorics not
Lean-ported.

### Non-vacuity

Not a `true → false` pin. The hypotheses are jointly satisfiable in
the non-degenerate direction: e.g. the 3×3 grid `gridChainLiftData`
witness (`ConcreteChainLiftData.lean`) has `X^exc = {(0,0)}` and
`↥(X^excᶜ)` the 8-element grid-minus-corner, which is genuinely
non-chain — the conclusion holds there. The `hNoBP` hypothesis is
load-bearing: dropping it makes the statement *false* (a long chain
with one global floater `z` is width-2 non-chain indecomposable, yet
`↥({z}ᶜ)` is a chain). So this is a genuine soundness filter, not a
disguised `True`.

### Replacement path

Port the "floater incomparable to a long range ⇒ balanced pair"
argument: a chain element range `[a, b]` all incomparable to a fixed
`z`, with `b − a` large, has `probLT z c ≈ 1/2` for `c` mid-range
(the in-tree `probLT` / `LinearExt` marginal machinery suffices for
the quantitative step); combine with `card_univ_le_ordIncompPairs_card`
to extract the long range from indecomposability. A self-contained
Step-8 lemma, multi-hundred-line but not multi-month.

**Retained-axiom audit bar.** Meets `difficult` (✓ — a substantial
combinatorial argument); meets `labeled` (✓ — pinned to the
`thm:main-step8` perturbation step); fails `external` (✗ —
project-internal Step-8 combinatorics); meets `low-risk` partially
(◑ — an instance of the conjecture's structure, with a concrete
non-vacuity witness and a load-bearing soundness filter `hNoBP`).
Same category as `case3Witness_hasBalancedPair_outOfScope`.
