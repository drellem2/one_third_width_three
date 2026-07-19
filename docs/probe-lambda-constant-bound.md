# Probe: the best constant lower bound on `lambda_std` for primitive / frozen posets

**Work item:** mg-210d.
**Scope note.** This note is deliberately isolated. It is written from the ticket alone and uses
nothing but elementary linear algebra and finite-poset combinatorics. No lemma, conjecture, or
framing from any other document in this repo is invoked, cited, or assumed. Everything below is
re-derived from scratch, including the Buser-type test-vector inequality, which the ticket offered
as a black box. Every claim carries a **[proven]** / **[heuristic]** / **[empirical]** tag.

---

## 0. Executive answer

> **The best *constant* lower bound this route proves is `0` — i.e. nothing.**

The route does prove a sharp *inequality*, and the inequality is genuinely informative, but it is
governed end-to-end by a single quantity that neither primitivity nor freezing controls: the
**incomparability density**

```
d(P) = m / C(n,2),     m = #incomparable pairs = |E(G)|.
```

Concretely, what comes out is:

| hypothesis | bound proved | positive iff |
|---|---|---|
| none (any reference linear extension `L`) | `1 - lambda_std <= 3 E[F_L] / (n^2 - 1)` | — (sharp, see §2) |
| none | `lambda_std >= 1 - (3/2) d * n/(n+1)` | `d < 2/3` |
| **frozen** (minority prob `< 1/3` for every incomparable pair) | **`lambda_std > 1 - d * n/(n+1)`** | `d < 1` |
| frozen, and `d <= D` for a constant `D < 1` | `lambda_std > 1 - D` | always |

Since `d <= 1` always, the frozen row degenerates to `lambda_std > 1 - n/(n+1) = 1/(n+1)`, which is
positive but **not a constant** — it decays. To convert it into a constant one needs exactly one
missing input:

> **Residual (R).** Is there a constant `D < 1` such that every frozen poset has `d(P) <= D`?

If yes, `lambda_std > 1 - D` immediately, with no further work. If no, the Buser route cannot
produce a constant, because the antichain shows the master inequality is *tight* (§2.4) — the loss
is not in the tool, it is in the absence of a density hypothesis.

**Connectivity does not help; it points the wrong way.** Primitivity gives `m >= n-1`, a *lower*
bound on the pair count, which *degrades* the Buser bound. Quantitatively the damage is `O(1/n)`
(§4), so the honest verdict is **inert, with a wrong-signed gradient** — it is a non-degeneracy
hypothesis (it rules out `lambda_std = 1`), not a quantitative lever. Nothing in primitivity bounds
`m` from above, and an upper bound on `m` is the entire content of what is missing.

**One genuinely new positive by-product** (§3.1): under freezing the *majority relation is
automatically a linear extension of `P`*, so the "standard" reference order is canonical rather
than chosen, and the constant `1/3` is exactly the threshold at which that argument works. This
removes what would otherwise be an unproven side-hypothesis in the frozen row above.

---

## 1. Setup, and the Buser tool re-derived

`P` a finite poset on `n` elements, `sigma` a uniform random linear extension. Fix a **reference
linear extension `L`** of `P` and relabel the elements `1, ..., n` by their `L`-position; `sigma(x)`
then denotes the position of the element with `L`-label `x`. This relabelling is what makes `T` a
square matrix with a meaningful transpose, and it is the only place a choice enters — see §3.1,
where freezing removes the choice.

```
T[x,i] = Pr[ sigma(x) = i ],     S = (T + T^T)/2,     lambda_std = max spec( S |_{1-perp} ).
```

`T` is doubly stochastic, hence (Birkhoff) a convex combination of permutation matrices, so
`||T||_{2->2} <= 1` and `spec(S) subset [-1,1]`; also `S1 = 1`.

**Lemma 1.1 (Buser tool). [proven]** For every `A` with `0 < |A| < n`,

```
1 - lambda_std  <=  n * leak(A) / (|A| |A^c|),     leak(A) := E #{ x in A : sigma(x) notin A }.
```

*Proof.* Put `a = |A|/n` and `f = 1_A - a*1`, so `f ⊥ 1` and

```
||f||^2 = |A|(1-a)^2 + |A^c| a^2 = |A||A^c|/n.
```

Since `S1 = 1`,

```
<f, Sf> = <1_A, S 1_A> - 2a<1, S1_A> + a^2 <1,S1> = <1_A, S 1_A> - |A|^2/n.
```

Also `<1_A, S 1_A> = (1/2)( sum_{x,i in A} T[x,i] + sum_{x,i in A} T[i,x] ) = sum_{x,i in A} T[x,i]`
(the two double sums coincide after swapping the names of the summation indices), and that is
`E #{x in A : sigma(x) in A} = |A| - leak(A)`. Rayleigh:

```
lambda_std >= <f,Sf>/||f||^2 = ( |A| - leak(A) - |A|^2/n ) * n/(|A||A^c|)
            = 1 - n*leak(A)/(|A||A^c|).                                              ∎
```

Note `leak` is one-sided by construction (the symmetrisation is already absorbed). Both forms —
the spectral one `|A| - <1_A,S1_A>` and the combinatorial one `E#{x in A: sigma(x) notin A}` — are
checked against each other exactly in `scripts/probe_lambda_constant_bound.py`, identity (I1).

---

## 2. The master bound, and its sharpness

Take `A` to run over the `n-1` **threshold cuts of the reference order**, `A_k = {1,...,k}`, and
write `leak_k := leak(A_k)`.

**Lemma 2.1 (cut sum = half the footrule). [proven]**
With `F(sigma) = sum_x |sigma(x) - x|` the Spearman footrule,

```
sum_{k=1}^{n-1} leak_k = E[F]/2.
```

*Proof.* For a fixed `sigma`, an element `x` is counted in `#{x <= k < sigma(x)}` exactly for
`k in [x, sigma(x)-1]`, i.e. `(sigma(x)-x)^+` times, and never when `sigma(x) <= x`. So
`sum_k leak_k = E sum_x (sigma(x)-x)^+`. Since `sum_x (sigma(x)-x) = 0`, the positive and negative
parts are equal and each is `F/2`. ∎

**Lemma 2.2 (footrule vs inversions, elementary). [proven]** Let `q_{xy}` be the probability that
`sigma` orders the incomparable pair `{x,y}` opposite to `L`, and `E[inv] = sum_{x~y} q_{xy}` the
expected number of inversions of `sigma` relative to `L` (comparable pairs never invert, since `L`
is a linear extension). Then `E[F] <= 2 E[inv]`.

*Proof.* With 1-indexed positions, `x = 1 + #{y : y <_L x}` and `sigma(x) = 1 + #{y : y <_sigma x}`,
so

```
sigma(x) - x = sum_{y != x} ( 1[y <_sigma x] - 1[y <_L x] ) = sum_{y ~ x} delta_y,
```

where `~` is incomparability (comparable `y` contribute `0`, as `sigma` and `L` agree on them) and
`delta_y in {-1,0,1}` with `E|delta_y| = q_{xy}`. Triangle inequality and summing over `x`:

```
E[F] = sum_x E|sigma(x)-x| <= sum_x sum_{y~x} q_{xy} = 2 E[inv].       ∎
```

(This is the upper half of the Diaconis–Graham inequality, but derived here from scratch so the
note stays self-contained; the ticket permitted citing it, we do not need to.)

**Lemma 2.3 (weighted pigeonhole). [proven]** `sum_{k=1}^{n-1} k(n-k)/n = (n^2-1)/6`.

*Proof.* `(1/n)[ n * n(n-1)/2 - (n-1)n(2n-1)/6 ] = (n-1)[ n/2 - (2n-1)/6 ] = (n-1)(n+1)/6`. ∎
(Verified numerically for `n = 2..11`.)

**Theorem 2.4 (master bound). [proven]**

```
1 - lambda_std  <=  3 E[F] / (n^2 - 1)          (footrule form)
                <=  6 E[inv] / (n^2 - 1)        (inversion form)
```

*Proof.* Apply `min_k (a_k/b_k) <= (sum_k a_k)/(sum_k b_k)` with `a_k = leak_k` and
`b_k = k(n-k)/n`; Lemma 1.1 at the minimising `k`, then Lemmas 2.1–2.3. ∎

### 2.4 The footrule constant is optimal — equality at the antichain

For the `n`-antichain `sigma` is a uniform permutation, so
`E|sigma(x)-x| = (1/n) sum_i |i-x|` and `E[F] = (n^3-n)/(3n) = (n^2-1)/3`. Hence
`3E[F]/(n^2-1) = 1` exactly, while `T = J/n` gives `S = J/n` and `lambda_std = 0` exactly. So
Theorem 2.4 holds **with equality**. [proven]

Consequences, stated plainly:

* `3/(n^2-1)` is the **best possible constant** in any inequality of the shape
  `1 - lambda_std <= C_n E[F]`. The cut-and-pigeonhole machinery is not the lossy step.
* The `E[F] <= 2E[inv]` step loses a factor of exactly `3/2` at the antichain
  (`E[inv] = C(n,2)/2`, giving `6E[inv]/(n^2-1) = (3/2)n/(n+1)` against a truth of `1`), and never
  more than `2`. So the inversion form is within a factor `2` of optimal.
* **The obvious refinement fails exactly where it would matter.** In Lemma 2.2 the `delta_y` are
  *signed*, so one is tempted to replace the triangle inequality by a second-moment/cancellation
  estimate `E|sum delta_y| <~ sqrt(deg(x) * q)`, which would give `E[F] = O(n^{3/2})` and hence
  `lambda_std -> 1` for *every* poset. That is false (antichain), and the reason is instructive:
  at the antichain the `delta_y` are maximally positively correlated and there is no cancellation
  at all — `E|sigma(x)-x| ~ n/3` against `sum_y q_{xy} = (n-1)/2`, a loss of only `~1.5`. The
  triangle inequality is near-tight precisely in the hard regime. **[proven for the antichain
  computation; heuristic as a general statement about why cancellation routes fail]**

---

## 3. Feeding in the structural hypotheses

Everything now rests on bounding `E[inv] = sum_{x ~ y} q_{xy}` — a sum over the `m = |E(G)|`
incomparable pairs of the probability that `sigma` disagrees with the reference `L` on that pair.
Let `beta_{xy} = min(p_{xy}, 1-p_{xy})` be the **minority probability**, where
`p_{xy} = Pr[x <_sigma y]`.

Note `q_{xy} >= beta_{xy}`, with equality iff `L` orients `{x,y}` the **majority** way. So the
ticket's identity `E[inv] = sum of minority probabilities` is *not* free: it presupposes a reference
order that is majority-consistent on every incomparable pair, and such an order need not exist in
general (the majority tournament may contain directed cycles, and even when acyclic it must
additionally be a linear extension of `P`). §3.1 shows freezing repairs this for free; §3.3 gives
the unconditional fallback.

### 3.1 Under freezing the majority order *is* a linear extension — and `1/3` is exactly the threshold

**Definition.** `P` is **frozen** iff `beta_{xy} < 1/3` for every incomparable pair.

**Lemma 3.1. [proven]** Let `P` be frozen. Define the relation
`x ≺ y  :iff  (x <_P y)  or  (x ~ y and p_{xy} > 2/3)`. Then `≺` is a strict total order extending
`P`, i.e. a linear extension `L*` of `P`, and it orients every incomparable pair the majority way.

*Proof.* *Totality/antisymmetry.* For comparable pairs this is `P`. For an incomparable pair,
freezing gives `p_{xy} < 1/3` or `p_{xy} > 2/3` and never `1/2`, so exactly one of `x ≺ y`, `y ≺ x`.

*Transitivity.* Suppose `x ≺ y ≺ z`; we show `x ≺ z`. Four cases.

1. `x <_P y <_P z`: then `x <_P z`. ✓
2. `x <_P y`, `y ~ z` with `p_{yz} > 2/3`: every linear extension with `y <_sigma z` also has
   `x <_sigma z` (as `x <_P y`), so `p_{xz} >= p_{yz} > 2/3`. If `x ~ z` this gives `x ≺ z`; if
   `x, z` comparable then `p_{xz} > 0` forces `x <_P z`. ✓
3. `x ~ y` with `p_{xy} > 2/3`, `y <_P z`: symmetrically `p_{xz} >= p_{xy} > 2/3`. ✓
4. `x ~ y` and `y ~ z`, both majority-forward. Then
   `p_{xz} >= Pr[x <_sigma y and y <_sigma z] >= p_{xy} + p_{yz} - 1 > 2/3 + 2/3 - 1 = 1/3`.
   If `x, z` are comparable, `p_{xz} > 0` forces `x <_P z`. If `x ~ z`, freezing says
   `p_{xz} < 1/3` or `p_{xz} > 2/3`; the first is excluded, so `p_{xz} > 2/3`. ✓                  ∎

**Sharpness of the constant `1/3`. [proven]** Run case 4 with a general freezing threshold `beta`
(every `beta_{xy} < beta`, `beta <= 1/2`). It yields `p_{xz} > 1 - 2beta`, and to exclude the
minority branch one needs `1 - 2beta >= beta`, i.e. **`beta <= 1/3`**. So `1/3` is precisely the
largest threshold at which the majority relation is forced to be transitive by this argument. That
the counterexample regime's defining constant is exactly the constant at which the majority order
becomes canonical is, as far as this note can tell, not a coincidence worth dismissing — but no
claim beyond the arithmetic is being made here. **[proven for the arithmetic; heuristic for the
"not a coincidence" reading]**

**Corollary 3.2. [proven]** For a frozen `P`, taking the reference `L = L*` gives
`q_{xy} = beta_{xy} < 1/3` for every incomparable pair, hence `E[inv] < m/3`. In particular
`lambda_std` is computed with respect to a **canonically determined** reference order — no choice
is made.

### 3.2 The frozen bound

**Theorem 3.3. [proven]** Let `P` be frozen, `lambda_std` taken with respect to `L*`. Then

```
1 - lambda_std  <  6*(m/3)/(n^2-1) = 2m/(n^2-1) = d * n/(n+1),
```

i.e.

```
   lambda_std  >  1 - d * n/(n+1)   >   1 - d.
```

*Proof.* Theorem 2.4 (inversion form) with Corollary 3.2, then `m = d*n(n-1)/2` and
`2m/(n^2-1) = d*n/(n+1)`. ∎

**Corollary 3.4 (the unconditional number). [proven]** Since `d <= 1` always,

```
lambda_std > 1 - n/(n+1) = 1/(n+1)   for every frozen poset.
```

This is the one honest positive number the route produces without extra hypotheses. **It is not a
constant.** It decays like `1/n`, and there is no way to stop it decaying without an upper bound on
`d`.

### 3.3 Without freezing (and without Lemma 3.1)

If one does not assume freezing, `beta_{xy} <= 1/2` trivially, but a majority-consistent reference
is no longer available. Two fallbacks, both **[proven]**:

* **Any reference, general skew bound `beta_{xy} <= beta`:** *if* a majority-consistent linear
  extension happens to exist, `E[inv] <= beta m` and
  `lambda_std >= 1 - 3 beta d n/(n+1) ~ 1 - 3 beta d`. Setting `beta = 1/3` recovers Theorem 3.3;
  `beta = 1/2` gives `1 - (3/2)d`.
* **Random reference (no existence hypothesis).** Draw `L` from the uniform linear-extension law,
  independent of `sigma`. Then `E_L E_sigma[inv_L] = sum_{x~y} 2 p_{xy}(1-p_{xy})`, so *there
  exists* a linear extension `L_0` with `E[inv_{L_0}] <= sum 2p(1-p)`. Since `2p(1-p) <= 1/2` in
  general and `< 4/9` under freezing:

  ```
  general:  lambda_std(L_0) >= 1 - 3 d n/(2(n+1))  ~  1 - (3/2) d      (positive iff d < 2/3)
  frozen:   lambda_std(L_0) >= 1 - 4 d n/(3(n+1))  ~  1 - (4/3) d      (positive iff d < 3/4)
  ```

  Identity `E_L E[inv_L] = sum 2p(1-p)` is verified exactly in the script, (I6).

So Lemma 3.1 is worth having: it improves the frozen coefficient from `4/3` to `1` **and** removes
the "for some good `L_0`" weasel, pinning the bound to a canonical reference.

---

## 4. Does connectivity help? No — and here is the quantification

**The ask.** Primitivity = the incomparability graph `G` is connected = `P` is not a nontrivial
ordinal sum. Connectivity implies `m >= n-1`.

**The answer. [proven]** That is a **lower** bound on `m`, and `m` enters the Buser bound *only*
through `E[inv] <= (skew) * m`, which we are trying to make *small*. So connectivity pushes the
bound in the **wrong direction**. Precisely: it forces

```
1 - lambda_std bound  >=  6 * beta_min * (n-1) / (n^2-1)  =  6 beta_min/(n+1)  =  O(1/n),
```

so the cost of connectivity is `O(1/n)` — it can never destroy a constant bound, but it never
supplies one either. The honest verdict is **inert with a wrong-signed gradient**.

Nothing in primitivity gives an *upper* bound on `m`, and an upper bound on `m` is exactly and
solely what is missing. Two remarks make this concrete:

* **Primitivity does not bound `lambda_std` away from `1`.** Take `G` a tree, `m = n-1`: Theorem 2.4
  gives `1 - lambda_std <= 6*(1/2)(n-1)/(n^2-1) = 3/(n+1)`, so `lambda_std >= 1 - 3/(n+1) -> 1`.
  Primitive posets can have `lambda_std` arbitrarily close to `1`.
* **Primitivity does not bound `lambda_std` away from `0`.** The `n`-antichain is primitive
  (`G = K_n`, connected) and has `lambda_std = 0` exactly.

So on primitive posets `lambda_std` ranges over essentially all of `[0,1)`, and the only parameter
in this route that moves it is `d`. Primitivity is the right *non-degeneracy* hypothesis — it is
what makes `lambda_std < 1`, since `lambda_std = 1` iff `P` is an ordinal sum — but it carries no
quantitative content here. **[proven]**

*Reduction sanity check.* Restricting to primitive posets is legitimate for the frozen question:
if `P = A ⊕ B` is an ordinal sum, every incomparable pair lies inside `A` or inside `B`, so `P` is
frozen iff both factors are, and a minimal frozen non-chain poset is therefore primitive. [proven]

---

## 5. What is actually missing, stated as one clean question

Collecting §2.4 (the tool is sharp), §3 (freezing gives coefficient `1`), §4 (connectivity is
inert):

> **Residual (R).** Does there exist a constant `D < 1` such that every frozen poset satisfies
> `d(P) = m/C(n,2) <= D`?

**(R) ⟹ `lambda_std > 1 - D` for every frozen poset, with no further work.** Conversely, if `d` can
approach `1` on frozen posets, this route yields no constant, and the failure is not repairable by
sharpening the tool, because Theorem 2.4 is an equality at `d = 1`.

Two remarks on (R), both honest about their status:

* **It is not resolvable by counting.** The natural entropy/counting attacks are the wrong
  direction. `H(sigma) <= sum_{x~y} H_2(p_{xy}) <= m * H_2(1/3)` is an *upper* bound on
  `log e(P)` in terms of `m`, and a Markov-plus-inversion-count argument
  (`e(P)/2 <= #{perms with inv <= 2m/3}`) is satisfied comfortably whenever `d >~ 3/e^2 ~ 0.41`.
  Neither excludes `d -> 1`. **[proven that these particular attacks fail; the question itself is
  open as far as this note goes]**
* **Heuristic in favour of (R).** To have `d` near `1` the poset must be a near-antichain, i.e.
  contain a large antichain whose induced order is nevertheless nearly deterministic. Pinning an
  antichain of size `w` into a near-deterministic order appears to cost `Theta(w^2)` auxiliary
  elements — e.g. hanging a chain of length `i*K` below the `i`-th antichain element makes the
  induced order essentially deterministic, but uses `n ~ K w^2/2` elements, giving
  `d ~ w^2/n^2 -> 0`. If a `w`-vs-`n` tradeoff of this shape is a theorem, (R) follows. **[heuristic
  — the example is a construction, not a lower bound on the cost of pinning]**

---

## 6. Computations performed

All exact (rational arithmetic) except the symmetric eigensolver, which is a hand-rolled Jacobi
rotation in double precision. Nothing here is a large enumeration.

**`scripts/probe_lambda_constant_bound.py`** — verified identities (I1)–(I6) on **245 random posets**,
`n = 3..7`, all with `e(P) >= 2`:

* (I1) `leak(A) = |A| - <1_A,S1_A> = E#{x in A: sigma(x) notin A}` — spectral vs combinatorial form;
* (I2) `sum_k leak_k = E[F]/2` (Lemma 2.1);
* (I3) `E[F] <= 2E[inv]` (Lemma 2.2);
* (I4) the Buser tool over **every** nonempty proper subset `A`, not just threshold cuts;
* (I5) the master bound `1 - lambda_std <= 6E[inv]/(n^2-1)` (Theorem 2.4);
* (I6) `E_L E[inv_L] = sum_{x~y} 2p(1-p)` (§3.3).

All pass. Also `sum_k k(n-k)/n = (n^2-1)/6` checked for `n = 2..11` (Lemma 2.3).

**`scripts/probe_lambda_frozen_density.py`** — the gap-`g` shift poset `G(n,g)` (`x_i < x_j` iff
`j - i >= g`), the natural interpolation chain → antichain, `n = 6..11`, all `g`. Findings:

* The footrule bound is **exactly tight at `g = n`** (antichain): bound `0.0000`, `lambda_std`
  `0.000000`, for every `n` tested — confirming §2.4. **[empirical, matching a proof]**
* It is informative but not tight in between: e.g. two free chains of length 6 (`n=12`, `d=0.545`)
  give bound `0.721` against a true `lambda_std = 0.914`.
* **No member of the family except the chain is frozen.** `beta_max` at `g=2` converges to
  `(3 - sqrt 5)/2 = 0.381966...` from above/below (extension counts are Fibonacci: `13, 21, 34, 55,
  89, 144`), already above `1/3`; larger `g` only increases it toward `1/2`. **[empirical]**

**`scripts/probe_lambda_frozen_search.py`** — exhaustive over all posets up to isomorphism for
`n <= 7` (`2, 5, 16, 63, 318, 2045` posets):

* **The chain is the only frozen poset at every `n <= 7`.** There are *no* frozen primitive posets
  at these sizes at all. **[empirical]**

That last line is the most important honest caveat in this note, and it deserves to be said
plainly: **"frozen" is a hypothetical regime.** A frozen non-chain poset is by definition a poset in
which every incomparable pair has minority probability `< 1/3`, and no such poset exists for
`n <= 7`. Every frozen statement in §3 is therefore a **conditional** statement about a hypothetical
object, and §5's residual (R) cannot be attacked empirically — there is nothing to measure. This is
a fact about the regime, not a defect of the calculation, but it does mean the frozen row of the §0
table should be read as "what a counterexample would have to satisfy", not as a bound with known
instances.

---

## 7. Claim ledger

| # | Claim | Status |
|---|---|---|
| 1.1 | Buser tool `1-lambda <= n leak(A)/(|A||A^c|)`, all `A` | **proven** (+ verified, I4) |
| 2.1 | `sum_k leak_k = E[F]/2` | **proven** (+ verified, I2) |
| 2.2 | `E[F] <= 2E[inv]`, elementary, no citation needed | **proven** (+ verified, I3) |
| 2.3 | `sum_k k(n-k)/n = (n^2-1)/6` | **proven** (+ verified) |
| 2.4 | `1-lambda <= 3E[F]/(n^2-1) <= 6E[inv]/(n^2-1)` | **proven** (+ verified, I5) |
| 2.4′ | Constant `3/(n^2-1)` optimal; equality at the antichain | **proven** (+ empirical) |
| 2.4″ | Cancellation/second-moment refinements fail at the antichain | **proven** for the antichain; **heuristic** in general |
| 3.1 | Frozen ⟹ majority relation is a linear extension `L*` | **proven** |
| 3.1′ | `beta <= 1/3` is exactly the threshold for that argument | **proven** |
| 3.3 | Frozen ⟹ `lambda_std > 1 - d*n/(n+1) > 1 - d` | **proven** (conditional on the frozen hypothesis) |
| 3.4 | Frozen ⟹ `lambda_std > 1/(n+1)`; **not** a constant | **proven** |
| 3.3′ | Random-reference fallback: `1 - (4/3)d` frozen, `1 - (3/2)d` general | **proven** (+ verified, I6) |
| 4 | Connectivity is inert, gradient wrong-signed, cost `O(1/n)` | **proven** |
| 4′ | Primitive posets realise `lambda_std -> 1` and `lambda_std = 0` | **proven** |
| 4″ | Frozen is closed under / reduces to primitive | **proven** |
| 5 | (R) `d <= D < 1` on frozen posets ⟹ `lambda_std > 1 - D` | **proven** implication; (R) itself **open** |
| 5′ | Entropy and inversion-counting attacks on (R) fail | **proven** that they fail |
| 5″ | Pinning an antichain of size `w` costs `Theta(w^2)` elements | **heuristic** |
| 6 | Chain is the only frozen poset for `n <= 7` | **empirical** (exhaustive) |

---

## 8. Secondary note: what a good vs bad constant would correspond to

Only what falls out of the above; no speculation beyond it.

The whole bound is `lambda_std >~ 1 - c*d`. So within this route, **`lambda_std` is controlled by
incomparability density and by nothing else** — not by width, height, dimension, or connectivity.
Reading off the two extremes:

* **`d` small (sparse incomparability graph, near-chain).** Bound is strong, `lambda_std -> 1`. This
  is correct and unsurprising: `lambda_std = 1` iff `P` is an ordinal sum, and a sparse `G` means `P`
  is close to one. A *good* constant here corresponds to *bad* mixing — the transport operator
  barely moves anything.
* **`d` near `1` (dense incomparability graph, near-antichain).** Bound is vacuous, and *correctly*
  so — the antichain has `lambda_std = 0` and saturates Theorem 2.4. A near-antichain mixes
  perfectly.

The frozen hypothesis sits awkwardly across this axis, and that is the structural content of the
note: freezing is a statement that every incomparable pair is *strongly* oriented, which is
near-chain-flavoured behaviour, while a positive constant needs `d` bounded away from `1`, which is
a near-chain-flavoured *structure*. Lemma 3.1 shows freezing does deliver one piece of near-chain
structure for free (a canonical global majority order). Whether it also delivers the density bound
is exactly residual (R), and this note does not resolve it.

---

## 9. Reproduction

```
python3 scripts/probe_lambda_constant_bound.py 250     # identities (I1)-(I6);  ~5 min
python3 scripts/probe_lambda_frozen_density.py 11      # gap-poset scan;        ~1 s
python3 scripts/probe_lambda_frozen_search.py  7       # exhaustive n<=7;       ~80 s
```
