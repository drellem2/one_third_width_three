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

**Scheduled for proof replacement by.** `mg-b699` (F6-4-port,
post-sorry-free).

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
