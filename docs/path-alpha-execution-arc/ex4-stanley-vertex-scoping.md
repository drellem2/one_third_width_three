# EX-4 Session A — Stanley vertex theorem proof writeup + mathlib mapping (latex-first)

**Polecat.** mg-4831 (cat-mg-4831).
**Date.** 2026-05-09.
**Branch.** `polecat-p4831` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α` defined
  with basic structural properties.
- mg-e22f (`f1c4a66`) — Stanley log-supermod independent verification
  GREEN.
- mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolved: GREEN-A; PM
  commits Path A. EX-3 spec drafted in §5.
- mg-d0fc (`00cbc2d`) — EX-1 Option A executed: temp axiom
  `OneThird.LinearExt.stanley_log_supermod` landed.
- mg-91be (`bb450a4`) — sub-α-C high-level scoping; EX-4 spec in §5.4.

**Verdict.** **GREEN with a small spec correction.** Both directions
of Stanley 1986 Theorem 1.2 admit clean, finite-poset-only proofs
(no convex-geometry / mixed-volume machinery; no continuous FKG;
no Aleksandrov–Fenchel). The mathlib `Set.extremePoints` API
(verified at `Mathlib.Analysis.Convex.Extreme`, commit
`v4.29.1`) is **a perfect fit** for the in-tree `OrderPolytope α`:
the typeclass surface (`[Semiring ℝ]`, `[PartialOrder ℝ]`,
`[AddCommMonoid (α → ℝ)]`, `[SMul ℝ (α → ℝ)]`) is automatic, and
useful structural lemmas (`mem_extremePoints`, `extremePoints_pi`,
`Convex.mem_extremePoints_iff_convex_diff`) are available off the
shelf. **The single spec correction surfaced by this Session A**:
the sub-α-C-scoping §5.4 / mg-163f §5.5 target signature uses
`LowerSet α` for the indexing set, but the in-tree `OrderPolytope`
definition (mg-8c66, `f x ≤ f y` for `x ≤ y`) makes `1_I`
order-preserving iff `I` is an **upper set / filter**, not a lower
set. The fix is one line in the Lean signature (use `UpperSet α`,
or equivalently use complement `(I : Set α)ᶜ` for `I : LowerSet α`);
the chamber-decomposition arc downstream (EX-5..EX-7) is unaffected
because it consumes `J(α) = LowerSet α` purely as an indexing set
of cardinality `2^{|J(α)|}`-count, and the upper/lower duality
preserves cardinality.

Session B ETA, contingent on this Session A landing: **1 polecat
session, ~330–470 LoC, ~200–300k tokens**, refining mg-163f §5.5's
"~400-600 LoC, ~200-300k tokens" estimate downward by ~70 LoC on
the back of a clean direct argument (no need for an auxiliary
chamber-volume or Stanley-axiom invocation).

This document is the latex-first deliverable per polecat brief §3
and `feedback_latex_first_for_math_simp`. No Lean source touched.

---

## §1 Statement, conventions, and Stanley 1986 cite

### §1.1 Conventions

Throughout: `α` is a finite poset (`PartialOrder α`, `Fintype α`).
We do not require `[DecidableEq α]` for the math statement
(`Set.indicator` is `noncomputable` in mathlib via
`Classical.decPred`); decidability is only relevant to the Lean
port for unfolding the indicator.

* `IsLowerSet (s : Set α) := ∀ ⦃a b⦄, b ≤ a → a ∈ s → b ∈ s`
  (mathlib, `Mathlib.Order.Defs.Unbundled`). Lower sets are also
  called *order ideals*. `LowerSet α` is the bundled type.
* `IsUpperSet (s : Set α) := ∀ ⦃a b⦄, a ≤ b → a ∈ s → b ∈ s`.
  Upper sets are also called *filters*. `UpperSet α` is the
  bundled type.
* `J(α) := LowerSet α` (the lattice of order ideals; mathlib
  `Mathlib.Order.UpperLower.CompleteLattice` provides the
  `DistribLattice` instance, distributive by Birkhoff's theorem).
* `F(α) := UpperSet α` (the lattice of filters). The complement
  map `s ↦ sᶜ` gives the order-isomorphism
  `LowerSet α ≃o (UpperSet α)ᵒᵈ`, so `|J(α)| = |F(α)|` for any
  finite `α`.
* `O(α) := OrderPolytope α := { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧
  (∀ x y, x ≤ y → f x ≤ f y) }` (in tree at
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`,
  mg-8c66). This is the **Stanley 1986 convention**:
  order-preserving maps with values in `[0,1]`.
* For a set `S ⊆ α`, the **indicator function** `1_S : α → ℝ` is
  `1_S(x) := 1` if `x ∈ S`, else `0`. Mathlib's
  `Set.indicator (S : Set α) (1 : α → ℝ)` realises this via
  `Set.indicator s f x = if x ∈ s then f x else 0` with `f ≡ 1`.

### §1.2 The vertex theorem

**Theorem (Stanley 1986, Theorem 1.2).** *Let `α` be a finite
poset. The extreme points of the order polytope `O(α)` are
exactly the indicator functions `1_I` for `I ∈ F(α)`*:

$$
\mathrm{ext}\bigl(\mathcal{O}(\alpha)\bigr) \;=\; \bigl\{\,\mathbf{1}_I \;:\; I \in F(\alpha)\,\bigr\}.
$$

**Cite.** R. P. Stanley, *Two poset polytopes*, Discrete Comput.
Geom. **1** (1986), 9–23, Theorem 1.2 (p. 10–11). Stanley's
original statement uses *filters*, denoted `J(P)` in his §1
(slightly confusing, since modern usage of `J(P)` is for *ideals*).
The substantive content is independent of the convention; see
§4.1 for the exact mapping to mg-91be §5.4 / mg-163f §5.5's
`LowerSet`-indexed signature.

### §1.3 Why "filter" (upper set), not "order ideal" (lower set)?

The order polytope as defined in tree (mg-8c66) requires
`x ≤ y ⟹ f(x) ≤ f(y)`. For an indicator `1_I` to satisfy this:
suppose `x ≤ y` and `1_I(x) = 1`, i.e., `x ∈ I`. Then we need
`1_I(y) ≥ 1`, i.e., `1_I(y) = 1`, i.e., `y ∈ I`. So **`I` must
be closed upward under `≤`** — exactly the upper-set / filter
property. Conversely if `I` is a lower set and `x ≤ y` with
`x ∈ I` but `y ∉ I` (e.g., `α` is the chain `0 < 1` and
`I = {0}`), then `1_I(x) = 1 > 0 = 1_I(y)`, violating
order-preservation.

The literature uses both the order-preserving and the
order-reversing conventions for `O(α)`; under order-reversing
`x ≤ y ⟹ f(x) ≥ f(y)`, the vertices are lower-set indicators
instead. Mathlib's `Mathlib.Order.UpperLower.CompleteLattice`
gives both `LowerSet α` and `UpperSet α` first-class lattice
status, so either convention is Lean-friendly. Picking one of
the two requires a small spec note (§4.1).

### §1.4 Cardinality sanity check (Stanley §1, hand-verified §3.1 below)

The vertex set has cardinality `|F(α)| = |J(α)|`. For
`α = {a, b, c}` discrete (the canonical width-3 example,
mg-91be §3.1):
- `O(α) = [0,1]^3` (mg-8c66 `OrderPolytope.eq_cube_of_discrete`
  + the `example` on `Three`).
- Vertices of `[0,1]^3` are the 8 functions in `{0, 1}^3`.
- `|F(α)| = |J(α)| = 2^3 = 8` (every subset of a discrete poset
  is both a lower and an upper set).
- The 8 functions in `{0, 1}^3` are exactly the indicators of
  the 8 subsets of `α`. ✓

This sanity check is consistent with mg-91be §3.1's ad-hoc count
(`Vertices {0,1}^3 = 2^3 = 8 = |J(α)|`). No discrepancy with
Stanley §1.

---

## §2 Direction 1 — `1_I` is an extreme point of `O(α)`, for any `I ∈ F(α)`

### §2.1 Statement

**Lemma 2.1.** *Let `α` be a finite poset and `I ∈ F(α)` an upper
set. Then `1_I ∈ O(α)`, and `1_I` is an extreme point of `O(α)`.*

### §2.2 Proof — `1_I ∈ O(α)`

Pointwise, `1_I(x) ∈ {0, 1} ⊆ [0, 1]`. ✓

Order-preservation: for `x ≤ y`, three cases on `(1_I(x), 1_I(y))`:
- `(0, 0)`: `0 ≤ 0`. ✓
- `(0, 1)`: `0 ≤ 1`. ✓
- `(1, 1)`: `1 ≤ 1`. ✓
- `(1, 0)`: would require `x ∈ I` but `y ∉ I` with `x ≤ y` —
  contradicts `I ∈ F(α)` (upper-set property). So this case
  cannot occur. ✓

Hence `1_I ∈ O(α)`. □

### §2.3 Proof — `1_I` is extreme

Let `t ∈ (0, 1)`. Suppose `f, g ∈ O(α)` satisfy
`1_I = (1 - t) \cdot f + t \cdot g`. We show `f = g = 1_I`.

For each `x ∈ α`:

**Case `x ∈ I`.** Then `1_I(x) = 1`, so
$1 = (1 - t) f(x) + t g(x)$.
Since `f(x), g(x) ∈ [0, 1]` (both `f, g ∈ O(α)`) and
`(1 - t) + t = 1`, with `1 - t > 0` and `t > 0`, we have
$1 = (1 - t) f(x) + t g(x) \le (1 - t) \cdot 1 + t \cdot 1 = 1$,
with equality iff `f(x) = g(x) = 1`. So `f(x) = g(x) = 1 = 1_I(x)`.

**Case `x \notin I`.** Then `1_I(x) = 0`, so
$0 = (1 - t) f(x) + t g(x)$.
Since `f(x), g(x) \ge 0` and both coefficients `1 - t, t > 0`, the
sum vanishes iff each summand vanishes: `f(x) = g(x) = 0 = 1_I(x)`.

Both cases give `f(x) = g(x) = 1_I(x)`. Since `x` was arbitrary,
`f = g = 1_I` on `α`. By the `mem_extremePoints` characterisation
(mathlib `Mathlib.Analysis.Convex.Extreme`, line 133–145), this
shows `1_I ∈ \mathrm{ext}(O(α))`. □

### §2.4 Lean signature target for §2 (Lemma 2.1)

```lean
-- lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean
-- (extending the EX-3 file)

namespace OneThird.LinearExt.OrderPolytope

variable {α : Type*} [PartialOrder α]

/-- For an upper set `I ⊆ α`, the {0,1}-indicator `1_I` lies in the
order polytope `O(α)`. -/
lemma indicator_upperSet_mem (I : UpperSet α) :
    Set.indicator (I : Set α) (1 : α → ℝ) ∈ OrderPolytope α := by
  refine ⟨fun x => ?_, fun x y hxy => ?_⟩
  · -- pointwise membership in [0, 1]
    by_cases h : x ∈ I
    · simp [Set.indicator_of_mem h, Set.mem_Icc]
    · simp [Set.indicator_of_notMem h, Set.mem_Icc]
  · -- order-preservation via the upper-set property
    by_cases hx : x ∈ I
    · have hy : y ∈ I := I.upper hxy hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hx]
      -- 0 ≤ Set.indicator I 1 y, automatic from indicator nonneg

/-- For an upper set `I ⊆ α`, `1_I` is an extreme point of `O(α)`. -/
theorem indicator_upperSet_isExtreme (I : UpperSet α) :
    Set.indicator (I : Set α) (1 : α → ℝ) ∈
      Set.extremePoints ℝ (OrderPolytope α) := by
  refine ⟨indicator_upperSet_mem I, ?_⟩
  intro f hf g hg ⟨a, b, ha, hb, hab, hconv⟩
  ext x
  by_cases hx : x ∈ I
  · -- value 1 case: convex combination ≤ 1 with equality
    have h1 : Set.indicator (I : Set α) (1 : α → ℝ) x = 1 := by
      simp [Set.indicator_of_mem hx]
    have hfx : f x ≤ 1 := (hf.1 x).2
    have hgx : g x ≤ 1 := (hg.1 x).2
    have hfx_nn : 0 ≤ f x := (hf.1 x).1
    have hgx_nn : 0 ≤ g x := (hg.1 x).1
    -- a • f x + b • g x = 1 and ≤ 1 ⟹ f x = 1
    have : a * f x + b * g x = 1 := by
      have := congrArg (· x) hconv
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1] at this
      linarith
    -- close: nlinarith, or hand-derive f x = 1
    sorry  -- arithmetic close
  · sorry  -- value 0 case, symmetric

end OneThird.LinearExt.OrderPolytope
```

(The `sorry`s are placeholders for ~10–15 lines of `linarith` /
`nlinarith` arithmetic each. Lean port estimate for §2 alone:
~80–120 LoC.)

---

## §3 Direction 2 — every extreme point of `O(α)` is `1_I` for some `I ∈ F(α)`

### §3.1 Strategy

Let `f ∈ \mathrm{ext}(O(α))`. We show `f` takes only values in
`{0, 1}`. Then `I := f^{-1}(1) = \{x : f(x) = 1\}` is automatically
an upper set (by monotonicity of `f`), and `f = 1_I`.

The contrapositive: if `f` takes some value `c ∈ (0, 1)`, then `f`
is **not** extreme — we exhibit an explicit decomposition
`f = (f_+ + f_-) / 2` with `f_\pm ∈ O(α)`, `f_+ \neq f_-`. The
decomposition perturbs `f` by `\pm \varepsilon` on the
**level set** `S_= := f^{-1}(c) = \{x : f(x) = c\}` (which is
nonempty since `c` is in the range of `f`).

### §3.2 The level decomposition

For `f ∈ O(α)` and `c ∈ ℝ`, partition `α` into three sets:

$$
S_<(c) := \{x : f(x) < c\}, \quad S_=(c) := \{x : f(x) = c\}, \quad S_>(c) := \{x : f(x) > c\}.
$$

These are pairwise disjoint with `S_< \cup S_= \cup S_> = α`.

**Lemma 3.2 (monotonicity in cases).** *If `f \in O(α)` and
`x \le y`, then* (`x \in S_>` and `y \in S_=`) *and* (`x \in S_=`
and `y \in S_<`) *and* (`x \in S_>` and `y \in S_<`) *cannot
hold.*

**Proof.** Each contradicts `f(x) \le f(y)`. □

### §3.3 The perturbation `f_\varepsilon^\pm`

Given `f ∈ O(α)`, `c ∈ \mathrm{range}(f) \cap (0, 1)`, and a
perturbation magnitude `\varepsilon > 0`, define

$$
f_\varepsilon^+(x) :=
\begin{cases}
f(x) + \varepsilon & \text{if } x \in S_=(c) \\
f(x) & \text{otherwise}
\end{cases}
\qquad
f_\varepsilon^-(x) :=
\begin{cases}
f(x) - \varepsilon & \text{if } x \in S_=(c) \\
f(x) & \text{otherwise.}
\end{cases}
$$

By construction, $f = (f_\varepsilon^+ + f_\varepsilon^-) / 2$
pointwise (the perturbations cancel). Also
$f_\varepsilon^+ \neq f_\varepsilon^-$ because `S_=(c)` is
non-empty and the two functions differ by `2\varepsilon > 0`
there.

### §3.4 Choice of `\varepsilon`

Define

$$
\varepsilon^* := \min\Bigl(c,\; 1 - c,\; G(f, c)\Bigr)
$$

where the **gap function** `G(f, c)` is the minimum, over the
"new boundary" pairs created by perturbing `S_=(c)`, of the
slack to monotonicity:

$$
G(f, c) := \min\Bigl(\,
  \min_{\substack{x \in S_=(c),\, y \in S_>(c) \\ x \le y}} \bigl(f(y) - c\bigr),\;
  \min_{\substack{x \in S_<(c),\, y \in S_=(c) \\ x \le y}} \bigl(c - f(x)\bigr)
\Bigr).
$$

Conventions: an empty `min` is `+\infty` (skip the term). Both
gap-min terms are over **finite** index sets (since `α` is
finite) and consist of **strictly positive** terms (each summand
is a strict inequality by definition of `S_<, S_>`); so
`G(f, c) > 0` whenever the index sets are non-empty (and
`+\infty` otherwise). Hence `\varepsilon^* > 0`, since
`c, 1 - c > 0` by hypothesis.

We take `\varepsilon \in (0, \varepsilon^* / 2]`, e.g.
`\varepsilon := \varepsilon^* / 2`.

### §3.5 `f_\varepsilon^\pm \in O(α)`

We verify the two defining conditions for `f_\varepsilon^+`; the
argument for `f_\varepsilon^-` is symmetric.

**(a) Pointwise membership in `[0, 1]`.** For `x \notin S_=(c)`:
`f_\varepsilon^+(x) = f(x) \in [0, 1]` by `f ∈ O(α)`. For
`x \in S_=(c)`: `f_\varepsilon^+(x) = c + \varepsilon`. Since
`\varepsilon \le \varepsilon^*/2 \le (1 - c)/2 < 1 - c`,
`c + \varepsilon < 1`. And `c + \varepsilon > c > 0`. So
`f_\varepsilon^+(x) \in (0, 1) \subseteq [0, 1]`. ✓

**(b) Order-preservation.** For `x \le y` in `α`, the case
analysis on `(S_*(c)\text{-classification of } x, S_*(c)\text{-classification of } y)`
gives nine cases, six of which are ruled out by Lemma 3.2 (no
`x \le y` with `x \in S_>, y \in S_=` etc.). The remaining six:

| `x` ∈ | `y` ∈ | `f_\varepsilon^+(x)` | `f_\varepsilon^+(y)` | Required: `f_\varepsilon^+(x) \le f_\varepsilon^+(y)`? |
|---|---|---|---|---|
| `S_<` | `S_<` | `f(x)` | `f(y)` | `f(x) \le f(y)` ✓ (from `f \in O(α)`) |
| `S_<` | `S_=` | `f(x)` | `c + \varepsilon` | `f(x) \le c + \varepsilon` — `f(x) < c \le c + \varepsilon` ✓ |
| `S_<` | `S_>` | `f(x)` | `f(y)` | `f(x) \le f(y)` ✓ (from `f \in O(α)`; both unchanged) |
| `S_=` | `S_=` | `c + \varepsilon` | `c + \varepsilon` | `=` ✓ |
| `S_=` | `S_>` | `c + \varepsilon` | `f(y)` | `c + \varepsilon \le f(y)` — by `\varepsilon \le G(f,c) \le f(y) - c` ✓ |
| `S_>` | `S_>` | `f(x)` | `f(y)` | `f(x) \le f(y)` ✓ (from `f \in O(α)`) |

All six pass. Hence `f_\varepsilon^+ \in O(α)`. ✓

For `f_\varepsilon^-` the analogous table replaces `+\varepsilon`
by `-\varepsilon`; the only non-trivial cases are `S_<` → `S_=`
(needs `f(x) \le c - \varepsilon`, which holds by
`\varepsilon \le G(f,c) \le c - f(x)`) and `S_=` → `S_>` (trivial
since `c - \varepsilon < c < f(y)`). ✓

### §3.6 Conclusion of Direction 2

We have shown: if `f ∈ O(α)` takes some value `c \in (0, 1)`,
then `f = (f_\varepsilon^+ + f_\varepsilon^-) / 2` with
`f_\varepsilon^+, f_\varepsilon^- ∈ O(α)` distinct, so `f` is
**not** extreme.

Contrapositively: every extreme `f ∈ O(α)` takes values only in
`\{0, 1\}`. Setting `I := f^{-1}(1)`:

* `I ⊆ α` is well-defined.
* `I` is an upper set: for `x \le y` with `x \in I` (so
  `f(x) = 1`), monotonicity gives `f(y) \ge 1`; combined with
  `f(y) \le 1`, we get `f(y) = 1`, so `y \in I`. ✓
* `f = 1_I`: pointwise, `f(x) \in \{0, 1\}` and
  `f(x) = 1 \iff x \in I`. ✓

So `f ∈ \{1_I : I \in F(α)\}`. □

### §3.7 Lean signature target for Direction 2

```lean
namespace OneThird.LinearExt.OrderPolytope

variable {α : Type*} [PartialOrder α] [Fintype α]

/-- The level set `{x : f x = c}` for `f : α → ℝ`. -/
private def levelSet (f : α → ℝ) (c : ℝ) : Finset α :=
  {x | f x = c}

/-- The perturbation `f_+ε` from §3.3. -/
private noncomputable def perturbUp
    (f : α → ℝ) (c ε : ℝ) (x : α) : ℝ :=
  if f x = c then f x + ε else f x

/-- The perturbation `f_-ε` from §3.3. -/
private noncomputable def perturbDown
    (f : α → ℝ) (c ε : ℝ) (x : α) : ℝ :=
  if f x = c then f x - ε else f x

/-- The gap function `G(f, c)` from §3.4. -/
private noncomputable def gap
    (f : α → ℝ) (c : ℝ) : ℝ :=
  -- min over a Finset (constructed from the relevant pairs);
  -- defaults to 1 if the Finset is empty.
  sorry

private lemma gap_pos (f : α → ℝ) (hf : f ∈ OrderPolytope α)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    0 < gap f c := sorry

private lemma perturbUp_mem (f : α → ℝ) (hf : f ∈ OrderPolytope α)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) {ε : ℝ} (hε : 0 < ε)
    (hεgap : ε ≤ gap f c / 2) (hεbnd : ε ≤ min c (1 - c) / 2) :
    perturbUp f c ε ∈ OrderPolytope α := sorry

-- Symmetric for perturbDown.

/-- If `f ∈ O(α)` is an extreme point, then `f` takes only values
in `{0, 1}`. -/
private lemma extremePoint_isBoolean
    {f : α → ℝ} (hf : f ∈ Set.extremePoints ℝ (OrderPolytope α)) :
    ∀ x, f x = 0 ∨ f x = 1 := sorry

/-- The "1-level" of an order-polytope element is an upper set. -/
private lemma onePreimage_isUpperSet
    {f : α → ℝ} (hf : f ∈ OrderPolytope α) :
    IsUpperSet { x : α | f x = 1 } := sorry

/-- Every extreme point of `O(α)` is the indicator of an upper set. -/
theorem extremePoint_eq_indicator_upperSet
    {f : α → ℝ} (hf : f ∈ Set.extremePoints ℝ (OrderPolytope α)) :
    ∃ I : UpperSet α, f = Set.indicator (I : Set α) (1 : α → ℝ) := by
  refine ⟨⟨{ x | f x = 1 }, onePreimage_isUpperSet hf.1⟩, ?_⟩
  ext x
  by_cases hfx : f x = 1
  · simp [Set.indicator_of_mem (show x ∈ ({y | f y = 1}) from hfx), hfx]
  · have h0 : f x = 0 := (extremePoint_isBoolean hf x).resolve_right hfx
    simp [Set.indicator_of_notMem (show x ∉ ({y | f y = 1}) from hfx), h0]

end OneThird.LinearExt.OrderPolytope
```

Lean port estimate for §3 alone: ~200–280 LoC, of which the
`gap` Finset construction + the 6-case order-preservation
verification of `perturbUp` is ~120–160 LoC.

---

## §4 Mathlib `Set.extremePoints` API check + signature verification

### §4.1 Spec correction — `LowerSet` → `UpperSet`

The mg-91be §5.4 / mg-163f §5.5 target signature reads

```lean
theorem orderPolytope_extremePoints (α : Type*) [PartialOrder α]
    [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
    { f : α → ℝ | ∃ I : LowerSet α,
        f = Set.indicator (I : Set α) (1 : α → ℝ) }
```

By §1.3 and §2.2 above, the right-hand side as written is
**false**: an indicator `1_I` for `I : LowerSet α` is not
order-preserving (consider the chain `0 < 1` with `I = {0}`),
so it cannot be in `O(α)`, let alone an extreme point.

**Recommended Lean signature** (used as the target throughout
this Session A):

```lean
theorem orderPolytope_extremePoints (α : Type*) [PartialOrder α]
    [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
    { f : α → ℝ | ∃ I : UpperSet α,
        f = Set.indicator (I : Set α) (1 : α → ℝ) }
```

**Equivalent alternative** (preserves the `LowerSet`
parameterisation that downstream chamber-decomposition consumers
in EX-5..EX-7 use, via complement):

```lean
theorem orderPolytope_extremePoints (α : Type*) [PartialOrder α]
    [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
    { f : α → ℝ | ∃ I : LowerSet α,
        f = Set.indicator ((I : Set α)ᶜ) (1 : α → ℝ) }
```

Both signatures are equivalent via the order-isomorphism
`UpperSet α ≃o (LowerSet α)ᵒᵈ` realised by complement
(`UpperSet.compl` / `LowerSet.compl`, mathlib
`Mathlib.Order.UpperLower.CompleteLattice`). The cardinality
identity `|F(α)| = |J(α)|` is preserved, so the chamber-decomp
arc downstream (which uses `J(α) = LowerSet α` purely as an
indexing set of `numLinExt`-many chambers) is unaffected by
either choice.

**PM call.** Session B should pick **option 1** (UpperSet
directly) for cleanliness — the proof is most natural in upper-set
language (the upper-set property of `I` is exactly what makes
`1_I` order-preserving). If the chamber-decomp arc downstream
needs a `LowerSet`-indexed alias, a one-line bridge

```lean
theorem orderPolytope_extremePoints_lowerSet [PartialOrder α]
    [Fintype α] :
    Set.extremePoints ℝ (OrderPolytope α) =
    { f : α → ℝ | ∃ I : LowerSet α,
        f = Set.indicator ((I : Set α)ᶜ) (1 : α → ℝ) } :=
  orderPolytope_extremePoints.trans (by
    -- bijection upperSet ↔ lowerSet via complement
    sorry)
```

is trivial (one `Set.ext` + `UpperSet.compl` invocation).

### §4.2 Mathlib API — `Set.extremePoints` typeclass surface

`Mathlib.Analysis.Convex.Extreme.Set.extremePoints` (line 68):

```lean
def Set.extremePoints (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
    {E : Type*} [AddCommMonoid E] [SMul 𝕜 E] (A : Set E) : Set E :=
  { x ∈ A | ∀ ⦃x₁⦄, x₁ ∈ A → ∀ ⦃x₂⦄, x₂ ∈ A →
      x ∈ openSegment 𝕜 x₁ x₂ → x₁ = x }
```

For our use case:

- `𝕜 = ℝ`. ✓ (`Real` is a `Semiring` with `PartialOrder`.)
- `E = α → ℝ`. ✓ Has `AddCommMonoid` (pointwise) and `SMul ℝ`
  (pointwise) instances automatically derived from `ℝ`'s
  structure. No additional typeclass-finding work needed.
- `A = OrderPolytope α : Set (α → ℝ)`. ✓ This is precisely the
  shape `Set.extremePoints` consumes.

### §4.3 Useful structural lemmas (all in
`Mathlib.Analysis.Convex.Extreme`)

* **`mem_extremePoints`** (line 133–139). The most useful
  characterisation for Direction 1:
  ```
  x ∈ A.extremePoints 𝕜 ↔
    x ∈ A ∧ ∀ x₁ ∈ A, ∀ x₂ ∈ A, x ∈ openSegment 𝕜 x₁ x₂ →
      x₁ = x ∧ x₂ = x
  ```
  Direction 1 (§2.3) consumes this directly: given the
  `openSegment` triple `(x, x₁, x₂)` and the convexity equation,
  derive `x₁ = x` and `x₂ = x` by the [0, 1]-pinning argument.

* **`Convex.mem_extremePoints_iff_convex_diff`** (line 267–275),
  available in `[Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E]` (all hold for
  `𝕜 = ℝ` and `E = α → ℝ`):
  ```
  x ∈ A.extremePoints 𝕜 ↔ x ∈ A ∧ Convex 𝕜 (A \ {x})
  ```
  An alternative formulation of Direction 2 — show `O(α) \ {f}`
  is non-convex for non-boolean `f`. Equivalent to §3.3's
  perturbation construction (the convex combination
  `(f_\varepsilon^+ + f_\varepsilon^-) / 2 = f` is exactly the
  segment witness that fails to be in `O(α) \ {f}`). The
  perturbation form is cleaner for Lean port (more direct), so
  **Session B should use the `mem_extremePoints` / openSegment
  form** rather than the `convex_diff` form.

* **`extremePoints_pi`** (line 211–228). For the discrete
  3-antichain hand-verification (§3.1 and §1.4):
  ```
  (univ.pi s).extremePoints 𝕜 = univ.pi fun i ↦ (s i).extremePoints 𝕜
  ```
  Combined with mg-8c66's `OrderPolytope.eq_cube_of_discrete`
  and the standard fact `Set.extremePoints ℝ (Set.Icc 0 1) =
  {0, 1}` (which mathlib has as a consequence of
  `extremePoints_Icc` or similar; see §4.4), this gives
  `extremePoints (OrderPolytope Three) = {0, 1}^Three`
  in ~10–20 LoC.

* **`extremePoints_subset`** (line 153). Trivial but useful:
  `A.extremePoints 𝕜 ⊆ A`.

### §4.4 Mathlib gap check — `extremePoints (Icc a b)`

Searched for `extremePoints_Icc` / `extremePoints (Set.Icc 0 1)`
in `Mathlib.Analysis.Convex.Extreme` and `Mathlib.Analysis.Convex.*`.
The standard fact `extremePoints (Icc a b) = {a, b}` (for
`a ≤ b`) is **not directly** in mathlib v4.29.1 as a named
lemma. However:

* `Mathlib.Analysis.Convex.Strict.Extreme` has
  `extremePoints_strictConvex` and friends, but not the `Icc`
  case specifically.
* The result is a one-line consequence of either
  `mem_extremePoints` (direct check that `0` and `1` are extreme,
  and any `c ∈ (0, 1)` decomposes as
  `c = (1 - c) \cdot 0 + c \cdot 1`) or
  `Convex.mem_extremePoints_iff_convex_diff` (`Icc 0 1 \ {0}` is
  `Ioc 0 1`, which is convex; symmetrically for `1`; for any
  `c \in Ioo 0 1`, `Icc 0 1 \ {c} = Icc 0 c \cup Icc c 1` minus
  `c` is non-convex).

**Resolution.** Session B should **prove the `Icc` extreme-point
lemma in tree** (~15-25 LoC) and use it as a building block.
This is also a candidate for upstream mathlib PR (a small,
self-contained add to `Mathlib.Analysis.Convex.Extreme`). Not
on the critical path of EX-4 itself; only relevant to the
discrete-3-antichain hand-verification (§4.5). Mark as a
secondary mathlib upstream candidate (DH-5, low priority).

Alternative: avoid `extremePoints_pi` for the hand-verification
and prove the discrete case directly via the main
`orderPolytope_extremePoints` theorem (since `O(Three) = [0,1]^3`
and on the discrete 3-antichain `UpperSet Three ≃ Set Three`, so
`{1_I : I ∈ F(Three)} = {0,1}^3`). This route doesn't need
`extremePoints_Icc`. Cleaner for Session B.

### §4.5 Mathlib gap check — `Set.indicator` for `LinearMapClass` etc.

Direction 1 + Direction 2 only consume `Set.indicator` at the
arithmetic level (`indicator_of_mem`, `indicator_of_notMem`,
`indicator_apply`). All three are in mathlib
(`Mathlib.Algebra.Notation.Indicator`, line 67, 70, 61). No
gap.

### §4.6 Summary — mathlib API verdict

**GREEN.** Mathlib's `Set.extremePoints` is a clean fit for
`OrderPolytope α : Set (α → ℝ)`. The two-direction proof
(§2 + §3) lifts to Lean using only:

- `Mathlib.Analysis.Convex.Extreme` (`Set.extremePoints`,
  `mem_extremePoints`, `extremePoints_pi`).
- `Mathlib.Algebra.Notation.Indicator` (`Set.indicator`,
  `indicator_of_mem`, `indicator_of_notMem`).
- `Mathlib.Order.UpperLower.Basic` (`UpperSet`, `IsUpperSet`,
  `SetLike` coercion).
- `Mathlib.Analysis.Convex.Basic` (already imported by EX-3 file).
- `Mathlib.Order.UpperLower.CompleteLattice` (only needed if
  bridging to `LowerSet` via §4.1 alternative; otherwise not
  needed).

No measure-theoretic infrastructure required (Direction 2's
perturbation argument is purely order-theoretic and arithmetic).
No continuous FKG / Aleksandrov–Fenchel needed. No new mathlib
PR is on the EX-4 critical path; the `extremePoints_Icc`
helper noted in §4.4 is optional and trivially worked around.

---

## §5 Mathlib gaps (if any) + upstream-PR-class assessment

### §5.1 No critical gap

Per §4.6, EX-4 has **no critical mathlib gap** that blocks
Session B. The `extremePoints_Icc` gap noted in §4.4 is
secondary and worked around without cost. Both directions of
Stanley vertex theorem proceed using only mathlib's existing
extreme-point + indicator + upper/lower-set APIs.

### §5.2 Optional upstream-PR-class chunks (DH-5 candidate)

Two small lemmas surface as plausible upstream-PR candidates,
but **neither is on the critical path of sub-α-C** and both can
be left in tree if Session B goes mathlib-PR-light:

* **DH-5a.** `extremePoints (Set.Icc a b) = {a, b}` for
  `a ≤ b` in a `LinearOrderedField` (or appropriate generality).
  ~15-25 LoC. Maintainer: Yaël Dillies (consistent with
  `Mathlib.Analysis.Convex.Extreme`).
* **DH-5b.** `Set.extremePoints ℝ (OrderPolytope α) =
  {1_I : I ∈ F(α)}` itself, packaged as the Stanley vertex
  theorem. **This is EX-4** — could be upstream-PR'd as a follow-up
  to EX-3 (which is also an upstream-PR candidate per mg-91be
  §5.3 / mg-163f §2.8). Combined upstream PR
  (`Mathlib/Combinatorics/Order/StanleyOrderPolytope.lean`):
  EX-3 (definition + basic instances) + EX-4 (vertex theorem).
  ~600-900 LoC of cumulative mathlib value. Maintainer: Yaël
  Dillies.

Neither DH-5a nor DH-5b is on the **critical path** of sub-α-C
(EX-5..EX-10 don't strictly require either to be in mathlib —
the in-tree versions are sufficient for the chamber-decomp arc).
DH-5b is heightened relative to DH-5a because the combined
EX-3 + EX-4 PR has a cleaner "Stanley order polytope basics"
mathlib unit story than each alone.

**PM action.** Surface DH-5b to Daniel as a secondary mathlib-
upstream candidate alongside DH-1 (Stanley log-supermod) and
DH-4 (continuous FKG). Lower priority than DH-1 and DH-4 since
the LoC saving is smaller and the mathlib reviewer's interest
threshold may be higher (EX-4 is more "applied combinatorics"
than the broader-interest Stanley log-supermod / continuous FKG).

### §5.3 No structural surprise

Per polecat brief §5 trip-wires:

* **Mathlib API mismatch.** Not fired. The `Set.extremePoints`
  typeclass surface is fully compatible with `OrderPolytope α`;
  the lemma library is rich enough to support both directions
  cleanly. The §4.1 spec correction is a **convention**
  question (LowerSet vs UpperSet), not an API mismatch — both
  forms are equally well-supported by mathlib.
* **Direction 2 proof harder than expected.** Not fired. The
  perturbation argument (§3.3–§3.5) is short and rigorous; no
  hidden gap in Stanley 1986's argument.
* **Token blow-up.** Not fired. This Session A spent ~120k of the
  350k cap.

---

## §6 Session B ETA estimate (refined from mg-91be §5.4)

mg-91be §5.4 estimated EX-4 at **"1 polecat session, ~400-600
LoC, ~200-300k tokens."** mg-163f §2.2 left this unchanged
post-fork-resolution.

This Session A refines downward:

| Component | LoC est. | Tokens (k) |
|-----------|---------:|-----------:|
| `indicator_upperSet_mem` (§2.4) | 25–35 | 10–15 |
| `indicator_upperSet_isExtreme` (§2.4, Direction 1) | 60–90 | 30–50 |
| Aux: `gap` Finset construction + `gap_pos` (§3.4) | 40–60 | 20–35 |
| Aux: `perturbUp` / `perturbDown` definitions + `_mem` lemmas (§3.5) | 80–110 | 40–60 |
| `extremePoint_isBoolean` (§3.6 contrapositive) | 50–70 | 30–45 |
| `onePreimage_isUpperSet` (§3.6) | 10–15 | 5–10 |
| `extremePoint_eq_indicator_upperSet` (§3.7) | 20–30 | 10–15 |
| Main theorem `orderPolytope_extremePoints` | 25–40 | 15–20 |
| Discrete 3-antichain hand-verification (§3.1, §4.4 alt route) | 20–30 | 10–15 |
| **Total (Session B)** | **~330–470** | **~170–265** |

**Session B verdict targets.**

* **GREEN.** Both directions formalised; main theorem statement
  matches the §4.1 recommended signature; discrete 3-antichain
  example green; build green; no new axioms (EX-4 does **not**
  consume `stanley_log_supermod` — it is purely a
  characterisation of extreme points, not a count). Session
  estimate ~330–470 LoC, well within the 600k token budget.

* **AMBER.** Some auxiliary lemma surfaces an unexpected
  mathlib-side gap (e.g., the `Finset.min'` over a derived
  Finset of pairs needs a non-trivial decidability instance
  that isn't off-the-shelf). Workaround: in-tree statement of
  the missing lemma; do not block Session B.

* **RED.** Direction 2's `perturbUp`/`perturbDown` definition or
  `gap` construction surfaces a structural obstruction in mathlib
  (e.g., the `Finset` of relevant pairs requires
  `[DecidableRel (· ≤ ·)]` that isn't automatic for an arbitrary
  `[PartialOrder α]`; or the level-set `{x | f x = c}` isn't
  decidably-filterable on `Finset α`). In that case Session B
  STOPs and surfaces the gap; mg-4831 follow-up scoping ticket
  needed before re-attempting Session B.

The classical-decision (`Classical.decEq`, `Classical.decPred`)
escape hatch is always available for a `noncomputable`
formulation; Session B should use it freely if a decidability
instance is missing — Direction 2's perturbation is intrinsically
non-computable anyway (the gap function involves a `min` over
a propositional family).

**Calendar.** 1 polecat session ≈ 3–5 days. No dependencies on
other in-flight tickets; Session B can dispatch immediately on
this Session A landing.

---

## §7 References

### §7.1 Predecessor polecat documents

* mg-91be (`bb450a4`) — sub-α-C high-level scoping; EX-4 spec
  in §5.4. `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`.
* mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolution;
  GREEN-A. EX-4 spec in §5.5 (carries the `LowerSet`
  parameterisation that this Session A flags for correction in
  §4.1). `docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`.
* mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod`
  axiom landed.
  `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`.
* mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α`
  defined with basic structural properties (convex, closed,
  bounded, compact, measurable) + discrete-3-antichain
  hand-verification.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`.
* mg-e22f (`f1c4a66`) — Stanley log-supermod independent
  verification: GREEN.
  `docs/path-alpha-execution-arc/stanley-log-supermod-verification.md`.
* mg-c7b9 (`4b5b1ba`) — EX-1 Session A scoping (latex pattern
  reference for this Session A's structure).
  `docs/path-alpha-execution-arc/ex1-stanley-log-supermod-scoping.md`.

### §7.2 Literature

* Stanley 1986. R. P. Stanley, *Two poset polytopes*,
  Discrete Comput. Geom. **1** (1986), 9–23. — original
  vertex theorem (Theorem 1.2). Stanley's §1 also contains
  the order-polytope definition, the chamber decomposition
  (consumed by EX-5), and the volume formula
  `Vol(O(α)) = e(α) / n!` (consumed by EX-5).
* Stanley 1981. R. P. Stanley, *Two combinatorial applications
  of the Aleksandrov–Fenchel inequalities*, J. Combin. Theory
  Ser. A **31** (1981), 56–65. — Stanley log-supermod (EX-1
  axiom source). Cited here only for upstream cross-reference;
  EX-4 does not consume this result.
* Brightwell 1999. G. Brightwell, *Balanced pairs in partial
  orders*, Discrete Math. — §4 Daykin–Saks via chamber decomp +
  continuous FKG (EX-7, EX-9 source). Brightwell §4 cites the
  Stanley vertex theorem as a black box; this Session A
  formalises that black box.

### §7.3 In-tree code (verified at this commit)

* `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`
  (mg-8c66) — `OrderPolytope α` definition + basic structural
  properties (convex, closed, bounded, compact, measurable).
  EX-4 extends this file.
* `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`
  (mg-d0fc) — `stanley_log_supermod` temp axiom + `subPoset`
  definition. EX-4 does **not** consume this axiom.
* `lean/OneThird/Mathlib/LinearExtension/Fintype.lean:45,105` —
  `LinearExt α`, `numLinExt`. EX-4 does **not** consume.
* `lean/AXIOMS.md` — three named project axioms. EX-4
  introduces no new axioms.

### §7.4 Mathlib code (verified at this commit's `lake-manifest`)

* `Mathlib.Analysis.Convex.Extreme` — `Set.extremePoints`,
  `mem_extremePoints`, `extremePoints_pi`,
  `Convex.mem_extremePoints_iff_convex_diff`. Verified line-numbers
  133–145 (`mem_extremePoints`), 211–228 (`extremePoints_pi`),
  267–275 (`convex_diff` form).
* `Mathlib.Analysis.Convex.Segment` — `openSegment`,
  `openSegment_subset_segment`. Verified line 56.
* `Mathlib.Algebra.Notation.Indicator` — `Set.indicator`,
  `indicator_of_mem`, `indicator_of_notMem`. Verified line 67, 70.
* `Mathlib.Order.UpperLower.Basic` — `UpperSet`, `IsUpperSet`,
  `SetLike` coercion. Verified line 286 (`LowerSet`),
  `Mathlib.Order.UpperLower.CompleteLattice:37` (`SetLike` for
  `UpperSet`, dual'd to `LowerSet`).
* `Mathlib.Analysis.Convex.Basic` — `Convex` predicate (already
  consumed by mg-8c66 EX-3 file).

### §7.5 Feedback / policy applied

* `feedback_polecat_cumulative_state_doc` — applied (state.md
  updates per §10 mandate; see commit diff).
* `feedback_latex_first_for_math_simp` — applied (this document
  is the deliverable; no Lean source touched).
* `feedback_complexity_blowup_means_wrong_path` — applied
  (trip-wires §5.3).
* `feedback_polecat_stop_runaway` — applied (no auto-extension;
  Session B is filed by PM as a separate ticket).
* `feedback_pre_execution_dependency_verification` — applied
  (§4 mathlib API verified against current `lake-manifest`).
* `feedback_pm_is_mini_ceo_default` — applied (Path A vs Path B
  fork-resolution-style spec correction in §4.1 is a Lean-ticket-
  shape decision; PM decides + informs Daniel via digest).
* `feedback_block_and_report` — applied (no blocking on Daniel
  acknowledgment; PM dispatches Session B on this Session A
  landing, Daniel's default-acceptance window applies).

---

*End of EX-4 Session A — Stanley vertex theorem proof writeup +
mathlib mapping. Lean source unchanged. Verdict: **GREEN with
small spec correction** (LowerSet → UpperSet); PM files Session B
(direct Lean port) per §6.*

— polecat mg-4831 (cat-mg-4831), 2026-05-09.
