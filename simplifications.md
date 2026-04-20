# Potential simplifications and cleaner framings

**Scope.** A running list of places where the current proof could
plausibly be restructured without changing its mathematical content,
but with better conceptual hygiene or better prospects for
generalization to width $w \ge 4$. Each entry states the current
approach, the proposed alternative, and the concrete advantages.
Nothing here is a claim that the current proof is wrong — only that a
future revision might prefer a different framing.

---

## 1. Layered reduction via direct minimality contradiction

**Location.** Lemma `lem:layered-reduction` (`step8.tex:1391–1512`),
discharging GAP G3.

### Current approach

Given a $\gamma$-counterexample $P$ with a deep layered decomposition
($K \ge K_0(\gamma, w)$), the proof applies the cutting lemma to split
$X = A \sqcup B$ with window $W$ of size $\le 6w$, then:

- **Step 3–4.** For pairs $(x,y) \subseteq A \setminus W$, shows
  $p_{xy}(P) = p_{xy}(A)$ *exactly* via the ordinal closure
  $P^\sharp = A \oplus B$.
- **Step 5(a).** For window-touching pairs with $p_{xy}(A) \in [1/3,
  2/3]$, uses $|p_{xy}(P) - p_{xy}(A)| = o_K(1)$ to perturb up to a
  balanced pair in $P$.
- **Step 5, no-case-(a).** Packages $A$ as a
  $(\gamma/2)$-counterexample and recurses via minimality.

The recursion weakens $\gamma$ by a factor of $2$, which is absorbed
by choosing $K_0$ large depending on $\gamma$.

### Proposed alternative

Recognize that a *near*-ordinal-sum can violate minimality of a
counterexample the same way a genuine ordinal sum does, and contradict
minimality in one shot rather than recursing on a weakened constant.

Concretely: fix $P$ a *size*-minimal $\gamma$-counterexample. After
the cut, $|A| < |X|$, so $A$ is not itself a $\gamma$-counterexample —
hence $A$ has some balanced pair $(x, y) \in A$ with $p_{xy}(A) \in
[1/3, 2/3]$. Two cases:

1. **Balanced pair lies in the bulk $A \setminus W$.** By Step 3,
   $p_{xy}(P) = p_{xy}(A)$ *exactly*, so $(x,y)$ is a balanced pair in
   $P$. Contradiction.
2. **Every balanced pair of $A$ meets the window.** Apply the
   perturbation bound from Step 5(a): $|p_{xy}(P) - p_{xy}(A)| =
   o_K(1)$, so for $K_0$ large the perturbation is within the
   $\gamma$-slack of $[1/3, 2/3]$. Again a balanced pair in $P$.
   Contradiction.

Either way, $P$ cannot have been a $\gamma$-counterexample.

### Advantages

1. **No $\gamma$-decay under recursion.** The dependence of $K_0$ on
   $\gamma$ becomes one-sided (absorbing the window perturbation)
   rather than compounded through iterated halving.
2. **Cleaner generalization to width $w \ge 4$.** The argument only
   requires (i) the layered-decomposition comparability property (L2),
   and (ii) a perturbation bound of the form $|p_{xy}(P) - p_{xy}(A)|
   \to 0$ as $K \to \infty$. Both survive the width-3 $\to$ width-$w$
   translation with $|L_i| \le w$ and $|W| \le 2w \cdot w = O(w^2)$,
   and neither depends on recursive $\gamma/2$ structure.
3. **Parallel to the classical ordinal-sum minimality argument.** In
   a genuine ordinal sum $P = A \oplus B$, minimality of $P$ forces
   one of $A, B$ to contain a balanced pair, which lifts exactly. The
   proposed framing is the near-ordinal-sum analogue of that
   one-sentence argument — and structurally identical.

### Subtleties to verify

- **Existence of a bulk balanced pair (case 1) vs. window balanced
  pair (case 2).** The case split is fine as written, but one might
  hope for a cleaner statement: "some balanced pair of $A$ lies in $A
  \setminus W$." For width 3, $|W \cap A| \le 3w$ and $|A| \ge
  |X|/2$, so the bulk has size $\ge |X|/2 - 3w$; if balanced pairs
  are reasonably spread (which the proof of $A$'s balanced pair does
  not directly say), most lie in the bulk. For width $w \ge 4$, this
  is worth tracking explicitly rather than relying on the case-2
  perturbation fallback.
- **Size- vs. $\gamma$-minimality.** The framing uses minimality on
  $|X|$ with $\gamma$ *fixed*. This is the standard minimal-
  counterexample setup in the 1/3–2/3 literature and should cause no
  trouble, but the current proof's choice of $\gamma/2$-weakening
  suggests the author may have had a reason to avoid pure size
  minimality — worth checking whether any downstream step needs the
  $\gamma/2$ structure.

### Implementation cost

Rewriting Lemma `lem:layered-reduction` in this form is local to
`step8.tex:1405–1512`. The Lean file
`lean/OneThird/Step8/LayeredReduction.lean` currently packages the
disjunction (balanced pair *or* smaller counterexample); it would
become a single-conclusion lemma (balanced pair, contradicting
minimality), which is strictly simpler to formalize.
