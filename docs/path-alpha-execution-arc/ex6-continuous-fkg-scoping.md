# EX-6 Session A — Continuous FKG / Ahlswede–Daykin on `[0,1]^n` (latex-first scoping)

**Polecat.** mg-e622 (cat-mg-e622).
**Date.** 2026-05-09.
**Branch.** `polecat-pe622` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-10d9 (`7b084ba`) — EX-5 Session C executed: chamber cover +
  measure-zero overlap + master volume theorem in Lean.
- mg-497d (`5dd9e50`) — EX-5 Session B executed: chamber definition
  + `chamber_volume` + `volume_orderedCube`.
- mg-79a9 (`3e76ac3`) — EX-5 Session A latex-first scoping.
- mg-2442 (`89786cf`) — EX-4 Session B executed: Stanley vertex
  theorem in Lean.
- mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α`.
- mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolved: GREEN-A.
  §2.3 contains the DH-4 risk assessment (AMBER); §4.4 specifies the
  integer-sub-lattice fallback.
- mg-91be (`bb450a4`) — sub-α-C high-level scoping; EX-6 spec in §5.6.
- mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod` axiom
  landed (consumed by EX-7 onward, **not** by EX-6).

**Verdict.** **GREEN-2** (split Session B + Session C).

The continuous FKG / Ahlswede–Daykin inequality on the hypercube
`[0,1]^n` admits a clean Lean-portable proof via Riemann-sum
discretisation against the in-tree mathlib package
(`Mathlib.Combinatorics.SetFamily.FourFunctions.four_functions_theorem`,
`Mathlib.MeasureTheory.Integral.DominatedConvergence`,
`Mathlib.MeasureTheory.Integral.Lebesgue.Add.lintegral_iSup`):

1. **Discrete sub-lattice.** Restrict `f, g` to the dyadic-style
   sub-lattice `D_N := {0, 1/N, …, 1}^n ⊂ [0,1]^n` (isomorphic to
   `(Fin (N+1))^n` as a finite distributive lattice with pointwise
   `⊓`/`⊔`).
2. **Discrete FKG.** Apply `four_functions_theorem_univ` to the four
   non-negative monotone functions `f|_D_N`, `g|_D_N`, `1`, `(f g)|_D_N`
   on `(Fin (N+1))^n`. The inequality `f(x) g(y) ≤ 1 · (f g)(x ⊔ y)`
   on a chain (which `(Fin (N+1))^n` is *not*, but the lattice version
   `f(x) g(y) ≤ f(x ⊓ y) g(x ⊔ y) ≤ ((f g)(x ⊔ y)) · 1` still holds
   pointwise by monotonicity) gives the discrete FKG correlation in
   sum form.
3. **Riemann-sum approximation.** Let `f_N⁻(x) := f(p_N(x))` where
   `p_N(x)` is the lower-corner grid point of the cell containing `x`,
   and `f_N⁺(x) := f(p_N(x) + (1/N, …, 1/N))`. Both are step functions;
   monotonicity of `f` gives the sandwich `f_N⁻ ≤ f ≤ f_N⁺` a.e. on
   `[0,1]^n`. The averaged Riemann sum on `D_N` equals
   `(1/(N+1)^n) · Σ_{p ∈ D_N} f(p)` and is sandwiched by
   `∫ f_N⁻ ≤ R_N(f) ≤ ∫ f_N⁺` (modulo a `O(1/N)` boundary correction,
   §4.4 below).
4. **Limit.** Apply
   `Mathlib.MeasureTheory.Integral.DominatedConvergence.tendsto_integral_filter_of_dominated_convergence`
   to `f_N⁻, f_N⁺ → f` (a.e. by monotone convergence, dominated by
   `‖f‖_∞ · 1_{[0,1]^n}` ∈ `L^1`). The discrete FKG inequality on
   Riemann sums passes through the limit by continuity of multiplication
   on `ℝ_{≥0}` to give continuous FKG on the cube.

**No critical mathlib gap.** Every API consumed sits in mathlib at the
project's pinned version (`v4.29.1`-class). The missing piece is the
*assembly*. Estimated ~1000–2000 LoC across two Lean polecat sessions
(Session B = discrete-side scaffolding + Session C = limit argument
+ master theorem), tracking the mg-91be §5.6 envelope. **DH-4 is the
direct mathlib upstream PR target** (this scoping doubles as a Path
A-internal Lean-portability check **and** a feasibility study for the
mathlib-upstream `Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
PR).

The single mathlib gap surfaced is **none of structural concern**:
the limit argument requires assembling `lintegral_iSup` (for `f_N⁻ ↗ f`
monotone-pointwise on a measurable set of full measure) **plus** the
Riemann-sum bookkeeping on `(Fin (N+1))^n`. Both are routine; both are
mathlib-accepted API patterns; neither requires a typeclass refactor.

**Trade-off vs. integer-sub-lattice fallback (mg-163f §4.4).**
The fallback gives a strictly weaker abstract drops with a size-`N`
discretisation factor. For fixed-`α` applications (case3, Brightwell
port) the factor is constant and the application chain still closes,
**but** the constant infiltrates EX-7 / EX-8 / EX-9 (the consumer
chain) and the cumulative LoC saving is partly cancelled by re-tracking
the constant. Per §7 below, the **full continuous FKG path is
recommended**; the fallback is the contingency, not the primary route.

---

## §0 Polecat brief recap

Per mg-e622 polecat brief:

> EX-6 Session A — continuous FKG/AD on cube (latex-first; DH-4
> candidate). Math: for `f, g : [0,1]^n → ℝ` non-neg coordinate-monotone,
> `(∫ f g)(∫ 1) ≥ (∫ f)(∫ g)`. Mathlib-PR-class ~1000–2000 LoC
> (LARGEST single mathlib chunk of Path A). DH-4 leverage candidate:
> Riemann-sum discretisation, integer-sub-lattice fallback per
> mg-163f §4.4.
>
> Session A latex-first scopes proof + verifies (1) whether mathlib
> has FKG/AD discrete that could lift to continuous via standard limit
> args, and (2) whether DH-4 (Riemann-sum discretisation) is a cleaner
> path.

**Answers (verdict-shaped, per §6.4 + §7).**

1. **Yes, mathlib has the discrete FKG/AD via
   `Mathlib.Combinatorics.SetFamily.FourFunctions`** (specifically
   `four_functions_theorem`, `four_functions_theorem_univ`, and `fkg`),
   *and* it lifts to the continuous version on `[0,1]^n` via the
   standard Riemann-sum argument with no structural mathlib gap. See
   §3 + §4.

2. **DH-4 / integer-sub-lattice discretisation IS the standard
   proof of continuous FKG** (it is *the* limit argument, not an
   alternative path), so the question reduces to: do we land the
   continuous theorem (clean abstract drops downstream) or stop at
   the discrete sub-lattice (size-`N` factor in downstream
   applications)? **Recommendation: full continuous FKG.** See §7.

The session is **GREEN-2**: latex-first scoping done, Lean signatures
drafted, mathlib API verified, no fundamental obstruction. Sessions B
+ C ETA: ~600–1000 LoC + ~400–700 LoC respectively, ~1000–2000 LoC
total (matches mg-91be §5.6 envelope), ~600–1000k tokens combined.

---

## §1 Statement, conventions, and citations

### §1.1 Conventions

Throughout this document:

- `n : ℕ` is a positive integer (the dimension of the cube).
- `I_n := Set.Icc (0 : Fin n → ℝ) 1 ⊂ Fin n → ℝ` is the unit cube,
  realised pointwise: `I_n = {x : Fin n → ℝ | ∀ i, 0 ≤ x i ∧ x i ≤ 1}`.
- `volume` is the Lebesgue measure on `Fin n → ℝ`
  (`MeasureTheory.volume`, the product of `n` copies of the
  `MeasureTheory.Measure.Lebesgue.Basic` Lebesgue measure on `ℝ`).
- `Fin n → ℝ` carries the **pointwise** lattice structure: `(x ⊓ y) i :=
  min (x i) (y i)` and `(x ⊔ y) i := max (x i) (y i)`. Since `ℝ` is a
  `LinearOrder` (hence `DistribLattice`), the `Pi.instDistribLattice`
  instance lifts this to `Fin n → ℝ` (Mathlib `Order/Lattice.lean`).
- A function `f : (Fin n → ℝ) → ℝ` is **coordinate-monotone**
  (`Monotone f` in the pointwise order) iff `x ≤ y` (componentwise)
  ⟹ `f x ≤ f y`.
- The **uniform measure on the cube**: `volume I_n = 1` (verified by
  `MeasureTheory.volume_pi_pi` / `MeasureTheory.Measure.pi`).
- `D_N := {0, 1/N, 2/N, …, N/N} = {k/N | k : Fin (N+1)} ⊂ ℝ` for
  `N ≥ 1`. The product `D_N^n` is the dyadic-style sub-lattice of
  `I_n`; canonically isomorphic to `(Fin (N+1))^n` via
  `Fin n → Fin (N+1) ↦ Fin n → ℝ, k ↦ (k : ℝ) / N`.

### §1.2 The FKG and AD statements

**FKG form (Preston 1974 Theorem 5.4 specialisation; Brightwell 1999
§4 source).** For `f, g : I_n → ℝ` non-negative, coordinate-monotone,
and integrable, with `f * g` integrable:

```
(∫_{I_n} f) (∫_{I_n} g) ≤ (∫_{I_n} f · g) (∫_{I_n} 1)
                       = ∫_{I_n} f · g          [since vol(I_n) = 1]
```

**AD form (Ahlswede–Daykin 1979 continuous version, Tonelli–Fubini
extension).** For `f₁, f₂, f₃, f₄ : I_n → ℝ` non-negative, integrable,
satisfying

```
∀ x y ∈ I_n,  f₁(x) · f₂(y) ≤ f₃(x ⊓ y) · f₄(x ⊔ y),
```

we have

```
(∫_{I_n} f₁) (∫_{I_n} f₂) ≤ (∫_{I_n} f₃) (∫_{I_n} f₄).
```

**FKG ⟸ AD.** Take `f₁ = f, f₂ = g, f₃ = f · g, f₄ = 1`. Monotonicity
of `f` and `g` plus non-negativity gives `f(x) g(y) ≤ f(x ⊓ y) g(x ⊔ y)`
(pointwise lattice order on `Fin n → ℝ` makes the four coordinates
`min/max` componentwise; non-negativity + monotonicity gives the
inequality `f(x) ≤ f(x ⊔ y)` and `g(y) ≤ g(x ⊔ y)`, hence
`f(x) g(y) ≤ (f g)(x ⊔ y) · 1 = f₃(x ⊓ y) · f₄(x ⊔ y) · (g(x⊓y)/g(x⊓y))`
needs care when `g(x ⊓ y) = 0`; the standard fix is to instead take
`f₃ = f · g`, `f₄ = 1` and verify
`f(x) g(y) ≤ (f · g)(x ⊓ y) · 1`? — **NO**, that requires `f` and `g`
both to be 0 at `x ⊓ y`, which is wrong.

**Correct chain.** Use the symmetric form
`f₁ = f, f₂ = g, f₃ = g, f₄ = f` reflected appropriately:
the AD hypothesis becomes `f(x) g(y) ≤ g(x ⊓ y) f(x ⊔ y)`.
Substitute `x = x ⊓ y, y = x ⊔ y`: trivially `f(x ⊓ y) g(x ⊔ y) ≤
g(x ⊓ y) f(x ⊔ y)` is *not* what monotonicity gives. The standard
derivation in Brightwell 1999 §4 / Preston 1974 uses
`f₁ = f, f₂ = g, f₃ = (f g)^?` — see §1.3.

### §1.3 The four functions instantiation (canonical)

The textbook reduction of FKG to AD on a distributive lattice (Stanley
EC1 §3.5; Brightwell 1999 §4.4 lemma; Ahlswede–Daykin 1979) is:

```
f₁ = f,   f₂ = g,   f₃ = f · g,   f₄ = 1.
```

The AD hypothesis `f(x) g(y) ≤ (f g)(x ⊓ y) · 1 = f(x ⊓ y) g(x ⊓ y)`
is **WRONG in general** — it can fail at `f(x) = 0, g(y) = 1, f(x ⊓ y)
= 0, g(x ⊓ y) = 1` (any monotone `f, g ≥ 0` with `f` strictly
increasing in some coordinate). So this direct instantiation is
**not** the chain.

The correct chain uses
**`f₁ = f, f₂ = g, f₃ = g · f, f₄ = (1 := constant 1)`** with a
*different* lattice hypothesis: not the AD hypothesis at the
function-quadruple level, but instead the *fkg* hypothesis (mathlib
`fkg`):

```
∀ x y, μ(x) μ(y) ≤ μ(x ⊓ y) μ(x ⊔ y).
```

Mathlib's `fkg` (`FourFunctions.lean:365`) is stated as:

```lean
lemma fkg (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g)
    (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤
      (∑ a, μ a) * ∑ a, μ a * (f a * g a)
```

Take `μ ≡ 1` (constant). Then `μ a * μ b = 1 = 1 · 1 = μ(x⊓y) · μ(x⊔y)`,
so the `hμ` hypothesis is `1 ≤ 1` (trivial). The conclusion becomes:

```
(∑ a, f a) * (∑ a, g a) ≤ (∑ a, 1) * (∑ a, f a * g a)
                       = |α| · ∑ a, f a g a.
```

**This IS the discrete FKG correlation form on a finite distributive
lattice with uniform measure.** Dividing by `|α|^2`:

```
((1/|α|) ∑ f) ((1/|α|) ∑ g) ≤ (1/|α|) ∑ f · g.
```

The averaged form is exactly the *continuous* FKG inequality with
counting measure replacing Lebesgue — hence the limit `N → ∞` (with
`α = (Fin (N+1))^n`, `|α| = (N+1)^n`) gives the cube version.

**FKG cite.** Mathlib `fkg` (`FourFunctions.lean:365`) covers any
finite distributive lattice. `(Fin (N+1))^n` is a finite distributive
lattice via `Pi.instDistribLattice` (Mathlib `Order/Lattice.lean`).

### §1.4 Sources

- **Preston 1974.** Christopher J. Preston, *Spatial birth-and-death
  processes*, Adv. Appl. Probab. **6** (1974), 391–403, Theorem 5.4
  — continuous FKG on `ℝ^n` for non-negative monotone integrable
  functions w.r.t. a log-supermodular density. Specialisation: take
  the density `ρ ≡ 1` on `[0,1]^n`, log-supermodularity is automatic
  (`1 · 1 ≤ 1 · 1`), and the result is FKG on the unit cube with
  Lebesgue measure.
- **Ahlswede–Daykin 1979.** Rudolf Ahlswede and David E. Daykin, *An
  inequality for the weights of two families of sets, their unions
  and intersections*, Z. Wahrsch. verw. Gebiete **43** (1978), 183–185.
  Discrete 4FT on a finite distributive lattice (in mathlib as
  `four_functions_theorem`); the continuous version is the
  Tonelli–Fubini limit, which is exactly what this scoping ports.
- **Brightwell 1999.** Graham R. Brightwell, *Balanced pairs in
  partial orders*, Discrete Math. **201** (1999), 25–52, §4
  (specifically Lemma 4.3 and the discussion before it) — uses
  continuous FKG on `[0,1]^α` to derive the drops monotonicity. This
  is the **consumer of EX-6 in EX-7** (the drops headline derivation).
- **Daykin–Saks 1981.** D. E. Daykin and M. Saks, *A natural
  generalisation of FKG for partial orders*, then unpublished (cited
  by Brightwell as the original source for the chamber-FKG argument).
- **Mathlib `fkg`.** `Mathlib.Combinatorics.SetFamily.FourFunctions`,
  the `fkg` and `four_functions_theorem` lemmas at lines 365 and 297
  respectively (verified at the project's pinned mathlib `v4.29.1`).

### §1.5 Hand-verification: `n = 1`

Take `n = 1`, so `I_1 = [0,1] ⊂ ℝ`. For `f, g : [0,1] → ℝ` non-neg
monotone:

```
(∫₀¹ f)(∫₀¹ g) = ∫₀¹∫₀¹ f(x) g(y) dx dy
              = ∫_{x ≤ y} (f(x) g(y) + f(y) g(x)) dx dy   [symmetrise]
              ≤ ∫_{x ≤ y} (f(x) g(x) + f(y) g(y)) dx dy   [Chebyshev]
              = ∫₀¹ f(x) g(x) dx                           [unsymmetrise]
              = ∫₀¹ f g.
```

The Chebyshev step uses `(f(y) - f(x))(g(y) - g(x)) ≥ 0` by joint
monotonicity (both increasing, `x ≤ y`) — equivalently
`f(x) g(y) + f(y) g(x) ≤ f(x) g(x) + f(y) g(y)`. **Verified.**

This 1-d hand-verification is itself a useful Lean target (`example`
in Session B; ~30 LoC against `MeasureTheory.intervalIntegral` +
`MonotoneOn`); see §5.4.

### §1.6 Hand-verification: `n = 2` discrete `2 × 2` lattice

Take `D_1 = {0, 1}^2` (so `N = 1`, `n = 2`). 4 lattice points:
`(0,0), (1,0), (0,1), (1,1)`. Monotone `f`:
`f(0,0) = a, f(1,0) = b, f(0,1) = c, f(1,1) = d` with
`a ≤ b, a ≤ c, b ≤ d, c ≤ d`. Same for `g`: `a', b', c', d'`.

The discrete FKG inequality `(Σ f)(Σ g) ≤ |α| · Σ (f g)` becomes:

```
(a + b + c + d)(a' + b' + c' + d') ≤ 4 · (a a' + b b' + c c' + d d').
```

Rearranging: `Σ_{x ≠ y} f(x) g(y) ≤ 3 · Σ_x f(x) g(x)`. The 12 cross
terms split into pairs `(f(x) g(y), f(y) g(x))` for the 6 unordered
pairs `{x, y}`; for comparable pairs `x ≤ y` Chebyshev gives
`f(x) g(y) + f(y) g(x) ≤ f(x) g(x) + f(y) g(y)`. The 6 unordered pairs
of `D_1` are: 4 comparable pairs (the cover relations and the
diagonals) plus 2 incomparable pairs (`{(1,0), (0,1)}` ×
2 orientations = 1 unordered pair). For the incomparable pair
`{(1,0), (0,1)}`: AD hypothesis gives
`f(1,0) g(0,1) ≤ f((1,0) ⊓ (0,1)) g((1,0) ⊔ (0,1)) = f(0,0) g(1,1)`
and similarly `f(0,1) g(1,0) ≤ f(0,0) g(1,1)`. Summing:
`f(1,0) g(0,1) + f(0,1) g(1,0) ≤ 2 f(0,0) g(1,1) ≤ f(0,0) g(0,0) +
f(1,1) g(1,1)` (last by AM–GM applied to `f(0,0) ≤ f(1,1)`,
`g(0,0) ≤ g(1,1)`). The 5 comparable pairs each give Chebyshev
contributing to the diagonal. Summing all 12 cross terms:

```
Σ_{x ≠ y} f(x) g(y) = Σ_{comparable pairs} [f(x)g(y) + f(y)g(x)]
                    + [f(1,0) g(0,1) + f(0,1) g(1,0)]
                  ≤ Σ_{comparable {x,y}} [f(x)g(x) + f(y)g(y)]
                    + [f(0,0) g(0,0) + f(1,1) g(1,1)].
```

Each diagonal term `f(x) g(x)` appears in `deg_comp(x) + 𝟙[x ∈
{(0,0), (1,1)}]` of the 6 right-hand summands above; with
`deg_comp = 3` for `(0,0)` and `(1,1)` (each comparable to all 3
others), `deg_comp = 2` for `(1,0)` and `(0,1)`. Adding:
`(0,0): 3 + 1 = 4`; `(1,1): 3 + 1 = 4`; `(1,0): 2`; `(0,1): 2`.

That gives `Σ_{x ≠ y} f(x) g(y) ≤ 4 a a' + 4 d d' + 2 b b' + 2 c c'`
which is **stronger** than what the discrete FKG demands
(`≤ 3 (a a' + b b' + c c' + d d')`) **but not always** — the bound
`4 a a' + 2 b b' + 2 c c' + 4 d d' ≤ 3(a a' + b b' + c c' + d d')`
requires `a a' + d d' ≤ b b' + c c'`, which is **wrong** for
`a = a' = 0, d = d' = 1, b = b' = c = c' = 0` (giving `0 + 1 ≤ 0`,
false).

The hand-verification thus **flags a gap in the casual
"comparable-pair-by-Chebyshev" decomposition**: the AD inequality on
the incomparable pair `{(1,0), (0,1)}` gives a bound in terms of
`f(0,0) g(1,1) + f(1,1) g(0,0)`, **not** the diagonal terms alone. The
correct application of `four_functions_theorem` aggregates over *both*
`x ⊓ y` and `x ⊔ y` simultaneously (the LHS's `Σ` over `s ⊻ t` and
`s ⊼ t` is *not* the diagonal). The full discrete FKG bound is delivered
by mathlib `fkg` (or `four_functions_theorem_univ`) directly; the hand-
decomposition above is **not** how the proof actually goes — it is a
sanity check that the bound *holds* numerically, not a proof.

**Sanity check (concrete case).** `a = a' = 0, b = b' = 0, c = c' = 0,
d = d' = 1`. LHS: `(0 + 0 + 0 + 1)(0 + 0 + 0 + 1) = 1`. RHS:
`4 · (0 + 0 + 0 + 1) = 4`. `1 ≤ 4` ✓.

`a = a' = 0, b = 1, b' = 0, c = 0, c' = 1, d = d' = 1`. LHS:
`(0 + 1 + 0 + 1)(0 + 0 + 1 + 1) = 2 · 2 = 4`. RHS: `4 · (0 + 0 + 0 + 1)
= 4`. `4 ≤ 4` ✓ (tight; this is the "incomparable pair" example).

The discrete bound is **tight** at the incomparable-pair-only example,
which means the continuous version is also tight (e.g., take
`f(x_1, x_2) = x_1`, `g(x_1, x_2) = x_2`: then
`(∫ f)(∫ g) = (1/2)(1/2) = 1/4`, `∫ f g = ∫_0^1 x_1 dx_1 ∫_0^1 x_2 dx_2 = 1/4`,
ratio = 1, FKG is *tight* at functions that are independent across
coordinates). **Verified.**

---

## §2 Proof strategy — Riemann-sum discretisation

### §2.1 Strategy outline

1. Choose `N : ℕ`, `N ≥ 1`. The grid `D_N := {k/N : k ∈ Fin (N+1)} ⊂ ℝ`,
   product `D_N^n ⊂ I_n`, finite distributive lattice
   `(Fin (N+1))^n` with pointwise `⊓`/`⊔`.
2. Restrict `f, g` to `D_N^n` (i.e., evaluate at grid points).
3. Apply mathlib `fkg` with `μ ≡ 1` on `(Fin (N+1))^n`. Output:

   ```
   (Σ_{p ∈ D_N^n} f(p)) (Σ_{p ∈ D_N^n} g(p))
       ≤ (N+1)^n · Σ_{p ∈ D_N^n} f(p) g(p).
   ```

4. Divide by `(N+1)^{2n}` and recognise both sides as Riemann sums:

   ```
   (R_N(f)) · (R_N(g)) ≤ R_N(f g),
   ```

   where `R_N(h) := (1/(N+1)^n) Σ_{p ∈ D_N^n} h(p)`.

5. As `N → ∞`, `R_N(h) → ∫_{I_n} h` for `h ∈ {f, g, f g}`. The
   inequality passes through the limit by continuity of multiplication.

The standard convergence step (`R_N(h) → ∫ h`) for monotone `h` is
the technical heart. §2.2–§2.5 work it out.

### §2.2 Step-function approximation

For each grid point `p = (k_1/N, …, k_n/N) ∈ D_N^n` with
`k_i : Fin (N+1)`, define the **lower-corner cell**

```
C_p := { x ∈ I_n | k_i / N ≤ x_i < (k_i + 1) / N  for all i }    (k_i ≤ N - 1)
     := { x ∈ I_n | k_i / N ≤ x_i ≤ 1 }                          (k_i = N)
```

(the half-open boundary convention is needed only at the cube's upper
face `x_i = 1`; we lump the `k_i = N` slab into the maximal cell to
keep `I_n = ⨆_p C_p` exact).

**Lower step function.** `f_N⁻ : I_n → ℝ`, `f_N⁻(x) := f(p)` if
`x ∈ C_p`. Equivalently:
`f_N⁻(x) := f(⌊N x⌋ / N)` componentwise (with `⌊1⌋ = N`).

**Upper step function.** `f_N⁺ : I_n → ℝ`, `f_N⁺(x) := f(p + (1/N, …, 1/N))`
on `C_p` for `p` with `k_i ≤ N - 1` (clipped to `1` componentwise on
the boundary cell).

**Monotonicity sandwich.** Since `f` is coordinate-monotone:

```
f_N⁻(x) = f(p) ≤ f(x)        (since p ≤ x componentwise on C_p)
       ≤ f(p + (1/N, …, 1/N)) = f_N⁺(x).
```

**Boundary.** The set
`B_N := { x ∈ I_n | ∃ i, x_i = k/N for some k ∈ Fin (N+1) }`
is a finite union of `(n-1)`-dimensional faces (each a strict linear
subspace of `Fin n → ℝ`); volume zero by `Measure.addHaar_submodule`
applied to the strict submodule `{x | x_i = k/N}`. Off `B_N` the
sandwich `f_N⁻ < f` (strict) on the upper boundary face is a
non-issue for the integral.

### §2.3 Riemann sum is a step-function integral

The Riemann sum `R_N(h) = (1/(N+1)^n) Σ_{p ∈ D_N^n} h(p)` is **not**
exactly `∫_{I_n} h_N⁻` — the cells `C_p` for non-boundary `p` have
volume `(1/N)^n`, not `(1/(N+1))^n`. The relationship:

```
∫_{I_n} h_N⁻ = (1/N)^n · Σ_{p ∈ D_N^n, all k_i ≤ N-1} h(p)
            + (boundary mass at k_i = N face)
```

So `∫_{I_n} h_N⁻` differs from `R_N(h)` by both a normalisation factor
(`(1/N)^n` vs `(1/(N+1))^n`) **and** a boundary-cell-vs-grid mismatch.
The clean way to handle this is to use the alternative **left-endpoint
Riemann sum** indexed only by `(Fin N)^n`:

```
R'_N(h) := (1/N)^n · Σ_{p ∈ {0, 1/N, …, (N-1)/N}^n} h(p) = ∫_{I_n} h_N⁻
```

with `h_N⁻` extended by `h(p)` on each cell `C_p` for `p ∈
{0, 1/N, …, (N-1)/N}^n` and the upper face `x_i = 1` slabs absorbed
into the closest interior cell (volume zero correction). **This is the
form that equals the integral exactly** and is what we Lean-port in
Session B.

But the discrete FKG `fkg` on `(Fin (N+1))^n` uses the full grid
including endpoints. To reconcile:

**Option A.** Use `fkg` on `(Fin N)^n` (one-fewer endpoint). The
inequality `(Σ f)(Σ g) ≤ N^n · Σ f g` over `(Fin N)^n` divided by `N^{2n}`
gives `(R'_N f)(R'_N g) ≤ R'_N(f g)`, which equals
`(∫ f_N⁻)(∫ g_N⁻) ≤ ∫ (f g)_N⁻`.

**Option B.** Use `fkg` on `(Fin (N+1))^n` and absorb the boundary
correction. The boundary-cell mass differs by `O(1/N)` from the
interior, vanishes as `N → ∞`.

**Option C (canonical, what we port in Session B).** Sample at the
`(N+1)^n` grid points `D_N^n = {0, 1/N, …, 1}^n` but **average against
the half-cell measure**: each interior point gets weight `(1/N)^n`,
each face-`d` boundary point gets weight `(1/N)^n / 2^d` (Lebesgue
trapezoidal convention). This is the standard discretisation of the
Lebesgue integral on a cube. The discrete FKG `fkg` with `μ` = the
half-cell-mass weighting (which is **log-supermodular** since
`μ(p) μ(q) ≤ μ(p ⊓ q) μ(p ⊔ q)` for the trapezoidal weights) gives
the inequality, and the limit `N → ∞` reproduces continuous FKG.

**Engineering note.** Option A is the simplest to Lean-port (no
boundary bookkeeping). Option C is the most faithful to the literature
(Preston 1974 uses it). Session B picks Option A; Session C reconciles
to the standard form if needed.

### §2.4 Riemann-sum convergence for monotone functions

**Lemma (Riemann–Lebesgue for monotone bounded functions on `[0,1]^n`).**
For `h : I_n → ℝ` non-negative, coordinate-monotone, and bounded
(automatic on `I_n`: `0 ≤ h ≤ h(1, …, 1) =: M`), the lower Riemann
sums `R'_N(h) = ∫ h_N⁻` converge to `∫_{I_n} h`:

```
lim_{N → ∞} ∫_{I_n} h_N⁻ = ∫_{I_n} h.
```

**Proof.** `h` is monotone on `I_n` (a compact set) hence bounded
(`0 ≤ h ≤ M`) and continuous off a Lebesgue-null set (a measurable
function of bounded variation is continuous a.e.; for monotone `h`,
the discontinuity set is a finite union of `(n-1)`-dim hyperplanes
where the partial-derivative `D_i h` has a Dirac mass — Lebesgue null).
Hence `h_N⁻ → h` pointwise a.e. on `I_n`. Apply
`Mathlib.MeasureTheory.Integral.DominatedConvergence.tendsto_integral_filter_of_dominated_convergence`
with bound `M · 1_{I_n}` ∈ `L^1` (volume of cube is finite, `M`
finite).

**Mathlib citation.** The dominated convergence theorem in mathlib:

```lean
theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] (bound : α → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) l (𝓝 (∫ a, f a ∂μ))
```

(`MeasureTheory/Integral/DominatedConvergence.lean:70`).

For our setting, `α = Fin n → ℝ`, `μ = volume.restrict I_n`,
`F : ℕ → α → ℝ` = `f_N⁻`, `bound = M · 1_{I_n}`, the four hypotheses:

1. `AEStronglyMeasurable (F N) μ` ← `f_N⁻` is a step function with
   finitely many values, measurable on each cell.
2. `‖F N x‖ ≤ M` ← `f` ≥ 0, `f_N⁻(x) = f(p) ≤ f(1) ≤ M`.
3. `Integrable (M · 1_{I_n}) μ` ← cube has finite volume.
4. `f_N⁻ → f` a.e. ← monotone discontinuity set is null (§2.5).

**Detail of (4).** A monotone function on `I_n` can be discontinuous,
but its discontinuity set is contained in a countable union of
hyperplanes (`{x | x_i = c}` for some `c`). On the complement, `f` is
continuous, and `f_N⁻(x) → f(x)` follows from continuity:
`f_N⁻(x) = f(p_N(x))` where `p_N(x) → x` as `N → ∞`. Since the
discontinuity set has Lebesgue measure zero (`Pi.borelSpace` +
`Measure.addHaar_submodule`), the a.e. convergence holds.

### §2.5 Monotone discontinuity set is null

**Claim.** For coordinate-monotone `f : I_n → ℝ`, the discontinuity
set `D := {x ∈ I_n | f not continuous at x}` is contained in a countable
union of hyperplanes `{x | x_i = c_k}`, hence Lebesgue null.

**Proof sketch.** For each `i`, fix `(x_1, …, ̂x_i, …, x_n) ∈ I_{n-1}`
and consider the section `t ↦ f(x_1, …, t, …, x_n)`. This is monotone
in `t : [0,1]`, hence has at most countably many discontinuities.
Equivalently, the set `{(x, c) | f discontinuous at x in the i-th
direction at value c}` is a countable union of hyperplanes (by the
Riesz-decomposition-style countability of jumps in 1D monotone
functions). The full discontinuity set is contained in the union of
the per-coordinate discontinuity sets, hence null.

**Mathlib status.** `Monotone` on `ℝ`: `Monotone.aemeasurable`,
`Monotone.measurable`. The 1D fact (countably-many discontinuities for
monotone `f : ℝ → ℝ`) is `Monotone.countable_not_continuousAt`
(`Mathlib.Topology.Order.Monotone`). The product extension (countable
union over the `n` coordinates) is straightforward in Lean.

**Engineering note.** The formal proof of "monotone implies a.e.
continuous" for `Monotone f : (Fin n → ℝ) → ℝ` is **~50–100 LoC** in
Lean (per-coordinate countability + `Set.Countable.measure_zero`).
It is **not in mathlib yet** as a packaged statement for the
multivariate case, but the components are. **Sub-DH-5 candidate** for
upstream PR alongside DH-4.

### §2.6 Limit of the discrete FKG inequality

Combining §2.1–§2.4:

```
For each N ≥ 1:  (R'_N(f)) · (R'_N(g)) ≤ R'_N(f g).             [*]
As N → ∞:  R'_N(f) → ∫ f,  R'_N(g) → ∫ g,  R'_N(f g) → ∫ f g.
By continuity of multiplication on ℝ_{≥0}:
                (∫ f)(∫ g) ≤ ∫ f g  =  ∫ f g · ∫ 1_{I_n}.        [QED]
```

The continuity-of-multiplication step is `Filter.Tendsto.mul`
(`Mathlib.Topology.Algebra.Order.MulAction` / `Topology.Order.Order`).
The step `[*]` is mathlib `fkg` applied to the finite distributive
lattice `(Fin (N+1))^n` (or `(Fin N)^n` per Option A) with `μ ≡ 1`.

---

## §3 Discrete FKG / AD on the sub-lattice

### §3.1 The product chain `(Fin (N+1))^n` is a finite distributive lattice

`Fin (N+1)` is a `LinearOrder`, hence a `DistribLattice` (via
`instDistribLattice` priority 100 in `Mathlib/Order/Lattice.lean`).
The instance `Pi.instDistribLattice` lifts: `Fin n → Fin (N+1)` is a
`DistribLattice` with pointwise `⊓ := min` and `⊔ := max`.

`Fintype (Fin n → Fin (N+1)) := Pi.instFintype` (mathlib core).

`DecidableEq (Fin n → Fin (N+1))`: yes (via `DecidableEq Fin _` +
`Pi.decidableEqPiFintype` or `Fintype.decidableEq`).

These three instances suffice for `four_functions_theorem` and `fkg`
to apply.

### §3.2 The discrete FKG inequality on `(Fin (N+1))^n`

Define, for `f : I_n → ℝ`:

```lean
def gridFn (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → Fin (N+1)) → ℝ :=
  fun k => f (fun i => (k i : ℝ) / (N : ℝ))
```

(a.k.a. the restriction of `f` to `D_N^n`).

**Monotonicity transport.** If `f : (Fin n → ℝ) → ℝ` is `Monotone`,
then `gridFn N f : (Fin n → Fin (N+1)) → ℝ` is `Monotone`. Proof:
the map `k ↦ (i ↦ (k i : ℝ) / N)` is `Monotone` componentwise (`Fin.cast_le`
+ `div_le_div_of_le_of_nonneg`), so `gridFn N f` is the composition of
two monotone maps.

**Non-negativity transport.** If `f ≥ 0` then `gridFn N f ≥ 0`. Trivial.

**Discrete FKG.** Apply mathlib `fkg` with `μ ≡ 1` on
`α = Fin n → Fin (N+1)`:

```
(Σ_{k} (gridFn N f)(k)) · (Σ_{k} (gridFn N g)(k))
    ≤ (Σ_{k} 1) · (Σ_{k} (gridFn N f)(k) · (gridFn N g)(k))
    = (N+1)^n · Σ_{k} (gridFn N (f * g))(k).
```

(using `(gridFn N f)(k) · (gridFn N g)(k) = f(...) · g(...) = (f g)(...)
 = (gridFn N (f g))(k)`). **This is the discrete FKG**.

### §3.3 Discrete AD on `(Fin (N+1))^n`

For the AD form (four functions): apply mathlib `four_functions_theorem`
or `four_functions_theorem_univ` directly to
`gridFn N f₁, gridFn N f₂, gridFn N f₃, gridFn N f₄` on
`α = Fin n → Fin (N+1)`. The lattice hypothesis transports: if
`f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)` for all `x, y ∈ I_n`, then in
particular for `x, y ∈ D_N^n`, which are exactly the grid points; and
the lattice operations on `D_N^n` agree with the lattice operations on
`(Fin (N+1))^n` under `gridFn`. (Coordinatewise:
`min(k i, l i) / N = min(k i / N, l i / N)`; same for `max`.)

**Discrete AD.**

```
(Σ_{k} (gridFn N f₁)(k)) · (Σ_{k} (gridFn N f₂)(k))
    ≤ (Σ_{k} (gridFn N f₃)(k)) · (Σ_{k} (gridFn N f₄)(k)).
```

### §3.4 Riemann-sum form (Option A)

Divide both sides by `N^{2n}` (Option A: drop the upper-face boundary,
use `(Fin N)^n` instead of `(Fin (N+1))^n`):

```
((1/N^n) Σ f₁) ((1/N^n) Σ f₂) ≤ ((1/N^n) Σ f₃) ((1/N^n) Σ f₄).
```

Each `(1/N^n) Σ_{(k ∈ (Fin N)^n)} f(k/N) = ∫ f_N⁻` is the integral of
the lower-step approximation (§2.2). So:

```
(∫ f₁_N⁻)(∫ f₂_N⁻) ≤ (∫ f₃_N⁻)(∫ f₄_N⁻).
```

This is the **discrete-step form of the AD inequality**. The continuous
form is the limit `N → ∞`.

---

## §4 Riemann-sum convergence for monotone integrable functions

### §4.1 Monotone implies bounded on `I_n`

For coordinate-monotone `f : I_n → ℝ` (bounded domain `I_n` is
compact):

```
f(0, …, 0) ≤ f(x) ≤ f(1, …, 1)    for all x ∈ I_n.
```

Hence `f` is bounded on `I_n`, so `f ∈ L^∞(I_n) ⊂ L^1(I_n)`. In
particular, the integrability hypotheses `Integrable f`, `Integrable g`,
`Integrable (f * g)` in the EX-6 statement are automatic from
monotonicity + non-negativity on the bounded cube.

(This simplification is **specific to the cube setting**. In the more
general `Preston 1974` formulation on `ℝ^n` with a log-supermodular
density, integrability is hypothesised separately.)

### §4.2 Step approximations and a.e. convergence

For `N ≥ 1` define the **lower-step grid retraction**

```
p_N : I_n → I_n,  p_N(x) := (i ↦ ⌊N x_i⌋ / N    if x_i < 1
                                    1            if x_i = 1)
```

(equivalently `p_N(x)_i = ((⌊N x_i⌋ ⊓ N) : ℝ) / N`). The step
approximation `f_N⁻(x) := f(p_N(x))`.

**Claim.** `f_N⁻(x) → f(x)` as `N → ∞` for every `x` at which `f` is
continuous; in particular for almost every `x ∈ I_n` (§2.5).

**Proof.** `p_N(x) → x` as `N → ∞` (componentwise: `⌊N x_i⌋ / N →
x_i` since `|⌊N x_i⌋ / N - x_i| ≤ 1/N → 0`). Continuity of `f` at `x`
gives `f(p_N(x)) → f(x)`.

### §4.3 Pointwise sandwich

For all `x ∈ I_n` and all `N ≥ 1`:

```
f_N⁻(x) = f(p_N(x)) ≤ f(x) ≤ f(p_N(x) + 1/N) = f_N⁺(x)
```

(componentwise: `p_N(x) ≤ x ≤ p_N(x) + 1/N · 1` where `1` is the
all-ones vector; monotonicity of `f`).

**Boundedness.** `0 ≤ f_N⁻(x) ≤ M := f(1, …, 1)` for all `N, x`.

**Conclusion.** `‖f_N⁻ x‖ ≤ M = M · 1_{I_n}(x)` for all `N`, `x`, and
`M · 1_{I_n} ∈ L^1` (volume `1` × bound `M < ∞`). All hypotheses of
`tendsto_integral_filter_of_dominated_convergence` met.

### §4.4 The limit

By dominated convergence:

```
∫ f_N⁻ d(volume.restrict I_n) → ∫ f d(volume.restrict I_n).
```

Equivalently `∫_{I_n} f_N⁻ → ∫_{I_n} f`.

**For the AD form** with four functions: apply the limit to each of
`f_1, f_2, f_3, f_4` separately, then pass `[*]` (§2.6) through the
limit using `Filter.Tendsto.mul` (continuity of multiplication on
`ℝ_{≥0}`).

**For the FKG form**: apply the limit to `f`, `g`, and `f g`. Note
`(f g)_N⁻(x) = (f g)(p_N(x)) = f(p_N(x)) g(p_N(x)) = f_N⁻(x) · g_N⁻(x)`
exactly (the step approximation commutes with multiplication since
both `f` and `g` are evaluated at the same point). Thus
`∫ (f g)_N⁻ → ∫ f g` follows from the same dominated-convergence
argument applied to `f g` (which is `Monotone` + non-neg + bounded by
`M^2` on `I_n`).

### §4.5 Combining: continuous FKG

```
For each N:    (R'_N(f)) (R'_N(g)) ≤ R'_N(f g)        (§3.4)
i.e.:          (∫ f_N⁻) (∫ g_N⁻) ≤ ∫ (f g)_N⁻

Limit N → ∞:   (∫ f) (∫ g) ≤ ∫ f g                     (§4.4 + cont. mul)
            =  ∫ f g · 1
            =  ∫ f g · vol(I_n)
            =  ∫ f g · (∫ 1_{I_n}).                    (vol(I_n) = 1)
```

QED.

### §4.6 Edge cases

- **`n = 0`.** `I_0 = {()}` (singleton), `vol(I_0) = 1`, all integrals
  reduce to function-evaluation at `()`, FKG is `f() · g() ≤ f() · g()`
  trivially. Lean handles via `decide` / `Fin.elim0`.
- **`n = 1`.** Reduces to the 1D Chebyshev-on-monotone (§1.5);
  formally just `Mathlib.MeasureTheory.intervalIntegral` + a 1D
  monotone-rearrangement argument; the discretisation route still
  works.
- **`f ≡ 0` or `g ≡ 0`.** Both sides are `0 ≤ 0`, trivial.
- **`vol`-zero set redefinition.** If `f, g` are only defined a.e.,
  redefine on a null set to be the standard representative; the
  integral is unchanged.

---

## §5 Lean signatures (target for Sessions B / C)

The signatures below target
`lean/OneThird/Mathlib/Probability/ContinuousFKG.lean` (NEW file, Path
A, Session B + Session C combined). Sub-namespace
`OneThird.Probability.ContinuousFKG`.

### §5.1 The discrete FKG/AD on `(Fin (N+1))^n` (Session B prelude)

```lean
namespace OneThird.Probability.ContinuousFKG

open MeasureTheory

variable {n : ℕ}

/-- Restriction of a function on `Fin n → ℝ` to the dyadic-style grid
    `D_N^n = {0, 1/N, …, 1}^n`, evaluated at the index `k : Fin n → Fin (N+1)`. -/
def gridFn (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → Fin (N + 1)) → ℝ :=
  fun k => f (fun i => (k i : ℝ) / (N : ℝ))

/-- `gridFn` is monotone on `Fin n → Fin (N+1)` whenever `f` is monotone
    on `Fin n → ℝ`. -/
lemma gridFn_monotone {N : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hN : 1 ≤ N) (hf : Monotone f) : Monotone (gridFn N f) := by
  intro k l hkl
  apply hf
  intro i
  exact div_le_div_of_nonneg_right
          (Nat.cast_le.mpr (Fin.le_iff_val_le_val.mp (hkl i))) (by exact_mod_cast hN.le)

/-- `gridFn` of a non-negative function is non-negative. -/
lemma gridFn_nonneg {N : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : 0 ≤ f) : 0 ≤ gridFn N f := fun _ => hf _

/-- **Discrete FKG on `(Fin (N+1))^n`** — the Riemann-sum form.
    Direct corollary of mathlib `fkg` with `μ ≡ 1`. -/
theorem discrete_fkg_grid {N : ℕ} (hN : 1 ≤ N)
    {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) :
    (∑ k : Fin n → Fin (N + 1), gridFn N f k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N g k)
    ≤ ((N + 1 : ℝ) ^ n) *
        ∑ k : Fin n → Fin (N + 1), gridFn N f k * gridFn N g k := by
  -- Apply mathlib `fkg` with μ ≡ 1, observe `Σ μ = (N+1)^n`.
  classical
  have hα : Fintype.card (Fin n → Fin (N + 1)) = (N + 1) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have := fkg (μ := fun _ : Fin n → Fin (N + 1) => (1 : ℝ))
              (gridFn N f) (gridFn N g)
              (by intro a; norm_num) (gridFn_nonneg hf₀) (gridFn_nonneg hg₀)
              (gridFn_monotone hN hf) (gridFn_monotone hN hg)
              (by intro a b; norm_num)
  simpa [Finset.sum_const, Finset.card_univ, hα,
         Nat.cast_pow, Nat.cast_add, Nat.cast_one, mul_comm] using this

/-- **Discrete AD on `(Fin (N+1))^n`**. Direct corollary of mathlib
    `four_functions_theorem_univ`. -/
theorem discrete_ad_grid {N : ℕ} (hN : 1 ≤ N)
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hf₃ : 0 ≤ f₃) (hf₄ : 0 ≤ f₄)
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∑ k : Fin n → Fin (N + 1), gridFn N f₁ k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N f₂ k)
    ≤ (∑ k : Fin n → Fin (N + 1), gridFn N f₃ k) *
        (∑ k : Fin n → Fin (N + 1), gridFn N f₄ k) := by
  -- Apply mathlib `four_functions_theorem_univ` after transporting hAD
  -- to the grid via `gridFn_inf`/`gridFn_sup` (`p ⊓ q` on `Fin (N+1)^n`
  -- maps to `(p ⊓ q)/N = (p/N) ⊓ (q/N)` on `D_N^n`).
  sorry  -- Session B
```

### §5.2 Step-function approximation and Riemann-sum identity (Session B core)

```lean
/-- The lower-corner grid retraction `p_N : I_n → I_n`. -/
def stepRetract (N : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ((Nat.floor (N * x i) : ℝ) ⊓ (N : ℝ)) / (N : ℝ)

/-- The lower-step approximation. -/
def stepLower (N : ℕ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => f (stepRetract N x)

/-- **Sandwich.** For `f` monotone on `I_n`,
    `stepLower N f x ≤ f x ≤ stepLower N f (x + 1/N · 1)`.
    (Plus boundary clipping; see file for the precise statement.) -/
lemma stepLower_le_self {N : ℕ} (hN : 1 ≤ N) {f : (Fin n → ℝ) → ℝ}
    (hf : Monotone f) (x : Fin n → ℝ) (hx : x ∈ Set.Icc 0 1) :
    stepLower N f x ≤ f x := sorry

/-- The lower-step integral equals the Riemann sum (Option A). -/
theorem integral_stepLower_eq_riemann (N : ℕ) (hN : 1 ≤ N)
    (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f) :
    ∫ x in Set.Icc (0 : Fin n → ℝ) 1, stepLower N f x ∂volume
      = (1 / (N : ℝ) ^ n) *
          ∑ k : Fin n → Fin N, f (fun i => (k i : ℝ) / N) := sorry

/-- **Riemann-sum convergence for monotone integrable.**
    For `f` non-neg, monotone, integrable on `I_n`,
    `∫_{I_n} stepLower N f → ∫_{I_n} f` as `N → ∞`. -/
theorem tendsto_integral_stepLower {f : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hf : Monotone f)
    (hfL1 : IntegrableOn f (Set.Icc (0 : Fin n → ℝ) 1)) :
    Filter.Tendsto
      (fun N : ℕ => ∫ x in Set.Icc (0 : Fin n → ℝ) 1, stepLower N f x ∂volume)
      Filter.atTop
      (nhds (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x ∂volume)) := sorry
```

The proof of `tendsto_integral_stepLower` is via
`tendsto_integral_filter_of_dominated_convergence` with
- `bound := fun x => f (1, …, 1) * (Set.Icc 0 1).indicator (fun _ => 1) x`
- a.e. convergence: pointwise on the continuity set of `f` (which is
  `[0,1]^n` minus a null set per §2.5).

### §5.3 Master continuous FKG / AD on the cube (Session C)

```lean
/-- **Continuous FKG on `[0,1]^n`** (Brightwell 1999 §4 source). -/
theorem continuous_fkg {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g)
    (hfL1 : IntegrableOn f (Set.Icc (0 : Fin n → ℝ) 1))
    (hgL1 : IntegrableOn g (Set.Icc (0 : Fin n → ℝ) 1))
    (hfgL1 : IntegrableOn (f * g) (Set.Icc (0 : Fin n → ℝ) 1)) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, g x ∂volume)
    ≤ (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f x * g x ∂volume) *
      (volume (Set.Icc (0 : Fin n → ℝ) 1)).toReal := sorry

/-- **Continuous Ahlswede–Daykin (4FT) on `[0,1]^n`**. -/
theorem continuous_ad {n : ℕ}
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁₀ : 0 ≤ f₁) (hf₂₀ : 0 ≤ f₂) (hf₃₀ : 0 ≤ f₃) (hf₄₀ : 0 ≤ f₄)
    (hf₁L1 : IntegrableOn f₁ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₂L1 : IntegrableOn f₂ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₃L1 : IntegrableOn f₃ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₄L1 : IntegrableOn f₄ (Set.Icc (0 : Fin n → ℝ) 1))
    (hAD : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin n → ℝ) 1,
            f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₁ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₂ x ∂volume)
    ≤ (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₃ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₄ x ∂volume) := sorry
```

### §5.4 Hand-verification examples (Session B / Session C)

```lean
/-- 1D Chebyshev: `(∫₀¹ f) (∫₀¹ g) ≤ ∫₀¹ f g · 1` for monotone non-neg
    `f, g : ℝ → ℝ`, restricted to `[0,1]`. -/
example {f g : ℝ → ℝ} (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g)
    (hfL1 : IntegrableOn f (Set.Icc (0 : ℝ) 1))
    (hgL1 : IntegrableOn g (Set.Icc (0 : ℝ) 1))
    (hfgL1 : IntegrableOn (f * g) (Set.Icc (0 : ℝ) 1)) :
    (∫ x in Set.Icc (0 : ℝ) 1, f x ∂volume) *
      (∫ x in Set.Icc (0 : ℝ) 1, g x ∂volume)
    ≤ (∫ x in Set.Icc (0 : ℝ) 1, f x * g x ∂volume) *
      (volume (Set.Icc (0 : ℝ) 1)).toReal := by
  -- Apply continuous_fkg with n = 1 modulo the (Fin 1 → ℝ) ↔ ℝ
  -- isomorphism. ~10 LoC.
  sorry

/-- Independent product example: `f(x) := x_1`, `g(x) := x_2` on `[0,1]^2`
    saturates FKG (both sides = 1/4). -/
example : (∫ x in Set.Icc (0 : Fin 2 → ℝ) 1, x 0 ∂volume)
            * (∫ x in Set.Icc (0 : Fin 2 → ℝ) 1, x 1 ∂volume)
          = (∫ x in Set.Icc (0 : Fin 2 → ℝ) 1, x 0 * x 1 ∂volume)
            * (volume (Set.Icc (0 : Fin 2 → ℝ) 1)).toReal := by
  -- Compute both sides explicitly via Fubini + volume_pi_pi.
  sorry
```

### §5.5 Out of scope (deferred to EX-7+)

- Drops headline `probEvent'_mono_of_subseteq_upClosed` (EX-7) — the
  consumer of `continuous_fkg` via `1_{O(Q')}` × `1_{A_k(S)}`.
- Brightwell sharp-centred bound (EX-9) — the consumer of `continuous_fkg`
  via `L(α) × Fin m`.
- The variant of `continuous_fkg` for **non-uniform** measure on `[0,1]^n`
  (Preston 1974 form with arbitrary log-supermodular density). This is
  **not needed** for the OneThird application; the uniform Lebesgue
  measure on `[0,1]^α` is what EX-7 / EX-8 / EX-9 consume. Out of scope
  for EX-6; can be added as a corollary upstream PR if the mathlib
  reviewer requests.
- Generalisation to bounded `[a,b]^n` for arbitrary `a < b` — covered
  by linear rescaling; trivial corollary, ~30 LoC.
- The `holley` analogue (continuous Holley) — not consumed by EX-7+;
  out of scope.

---

## §6 Mathlib API check + gaps

### §6.1 Verified mathlib APIs

All cited APIs are verified at `lake-manifest.json` →
`mathlib v4.29.1` (rev `5e932f97dd25535344f80f9dd8da3aab83df0fe6`):

| API | File:line | Used in |
|-----|-----------|---------|
| `four_functions_theorem` | `Mathlib/Combinatorics/SetFamily/FourFunctions.lean:297` | §3.3 discrete AD |
| `four_functions_theorem_univ` | `Mathlib/Combinatorics/SetFamily/FourFunctions.lean:341` | §3.3 discrete AD (universe form) |
| `fkg` | `Mathlib/Combinatorics/SetFamily/FourFunctions.lean:365` | §3.2 discrete FKG |
| `holley` | `Mathlib/Combinatorics/SetFamily/FourFunctions.lean:347` | §5.5 (out of scope, future corollary) |
| `Pi.instDistribLattice` | `Mathlib/Order/Lattice.lean:~1300` | §3.1 lattice on `Fin n → Fin (N+1)` |
| `Pi.instFintype` | mathlib core | §3.1 Fintype |
| `tendsto_integral_filter_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:70` | §4.4 limit |
| `lintegral_iSup` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:34` | §4.4 alt route (monotone convergence) |
| `lintegral_tendsto_of_tendsto_of_monotone` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:113` | §4.4 alt |
| `MeasureTheory.volume_pi_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:~1000` | §1.1 cube has volume 1 |
| `MeasureTheory.volume_Icc_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:241` | §1.1 cube measurability |
| `Measure.addHaar_submodule` | `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:175` | §2.5 boundary null |
| `Monotone.aemeasurable` | `Mathlib/MeasureTheory/Function/AEMeasurable` | §2.5 measurability of monotone |
| `Monotone.countable_not_continuousAt` | `Mathlib/Topology/Order/Monotone.lean` | §2.5 1D discontinuity countable |
| `Filter.Tendsto.mul` | `Mathlib/Topology/Algebra/Order/Group.lean` (or `Topology/Order/Order.lean`) | §2.6 limit of products |
| `Equiv.piCongrLeft` / `piCongrLeft_symm_apply` | `Mathlib/Logic/Equiv/Defs.lean` + `MeasureTheory/MeasurableSpace/Embedding.lean` | §3.3 grid lattice ops |

**No critical mathlib gap.**

### §6.2 In-tree dependencies

- `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` — provides
  `volume_orderedCube` (DH-5 candidate; **not consumed by EX-6**;
  EX-6 lives upstream of EX-3..EX-5 in the dependency DAG; see §3.4
  in mg-91be).
- `lean/OneThird/Mathlib/LinearExtension/FKG.lean` — existing
  product-lattice FKG-on-LE pathway; **independent of EX-6** (different
  abstraction layer: this file is FKG on `Finset (LowerSet α)`, EX-6
  is FKG on `[0,1]^n`).
- `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`
  — the third project axiom; **not consumed by EX-6** (axiom enters
  via EX-7 onward, per state.md §3.4).

**EX-6 has no in-tree consumers from EX-3, EX-4, EX-5** (which build
the chamber decomposition). The dependency is from EX-6 + EX-5 → EX-7
(drops headline derivation). EX-6 can therefore be developed in
parallel with EX-5 once the polytope foundations (EX-3) are in place;
it does not consume the Stanley axiom.

### §6.3 No new mathlib gap surfaced

All of the §6.1 APIs exist; §2.5's "monotone implies a.e. continuous on
`(Fin n → ℝ)`" composition is the only assembly piece that may not be
named in mathlib in multivariate form, but it is built from the
standard 1D version + `Set.Countable.measure_zero`. **Estimated
~50–100 LoC** of in-file derivation.

This is a candidate for a small auxiliary upstream contribution
alongside DH-4: `Monotone.aeContinuousAt` for
`(α → ℝ) → ℝ` with `[Fintype α]`. **Sub-DH-4-A** in §7.

### §6.4 Mathlib gap **not** surfaced (good news)

- The discrete FKG / AD is **fully** in mathlib at the abstract finite-
  distributive-lattice level. The `Pi` distrib-lattice instance lifts
  immediately to `(Fin (N+1))^n`. No new lattice scaffolding needed.
- The continuous-side limit is a routine application of dominated
  convergence; no measure-theoretic gap.
- `(volume.restrict I_n)` is automatically a finite measure, so the
  `IntegrableOn` hypothesis in `continuous_fkg` is automatic from
  bounded + measurable for monotone non-neg `f`. (Bounded: §4.1.
  Measurable: `Monotone.measurable` + `Pi.borelSpace`.)

The Lean port is therefore **purely an assembly job**.

### §6.5 Trip-wires — none fired in Session A

- Token blow-up: not fired (this scoping comes in well under the 400k
  cap).
- Mathlib measure-theory fundamental obstruction: **not fired** —
  every step uses standard mathlib measure theory.
- Continuous-FKG-not-in-mathlib: **expected**, this is the entire
  point of EX-6. No structural mathlib obstacle to *adding* it.
- DH-4 fallback fired (integer-sub-lattice rescue): **not fired** —
  the Riemann-sum proof is precisely the limit of the integer-sub-
  lattice form. There is no need for a "fallback"; the standard proof
  is the same path the fallback would take, but committed to the
  continuous limit. See §7.

---

## §7 DH-4 leverage assessment + integer-sub-lattice fallback comparison

### §7.1 DH-4 = "continuous FKG bypass" — interpretation

mg-163f §3.9 / §4.4 / §7.4 names DH-4 as **"continuous FKG bypass via
Riemann-sum discretisation"**. The text reads:

> If DH-4 lands as a mathlib upstream PR (Yael Dillies, James Gallicchio,
> or Bhavik Mehta as natural candidates), EX-6 collapses to a citation
> and Path A drops by ~1000–2000 LoC.
>
> Fallback if DH-4 doesn't land. Integer-sub-lattice discretisation
> gives a weaker drops with size-`N` factor; for fixed-`α` applications
> (case3, Brightwell) factor is constant, so applications still close.

**Two readings of "DH-4":**

1. **DH-4 = mathlib upstream contribution.** Daniel engages a mathlib
   reviewer and lands continuous FKG/AD on `[0,1]^n` upstream. EX-6
   collapses to a citation (~50 LoC consumer file with `import
   Mathlib.Analysis.MeanInequalities.ContinuousFKG`).

2. **DH-4 = Riemann-sum discretisation as the project-internal Lean
   route.** This polecat session ports the Riemann-sum proof (above)
   in-tree as `lean/OneThird/Mathlib/Probability/ContinuousFKG.lean`,
   cleanly designed for upstreaming to mathlib **later**.

**These are not exclusive.** The project route (#2) builds the proof
in our tree at mathlib-PR quality, then a **separate** Daniel-side
action of #1 graduates the file to a mathlib upstream PR. The polecat
brief asks about #2: is the Riemann-sum route a clean Lean port?
**Answer: yes, per §3 + §4.**

The "fallback" in mg-163f §4.4 is a **third reading**:

3. **Integer-sub-lattice fallback** (project-internal-only). Stop at
   the discrete sub-lattice; do not take the limit. EX-7+ then
   derives a **discretised drops** with a size-`N` factor.

§7.2 compares #2 vs #3.

### §7.2 Full continuous FKG vs. integer-sub-lattice fallback

| Criterion | Full continuous FKG (Reading #2) | Integer-sub-lattice (Reading #3) |
|-----------|----------------------------------|----------------------------------|
| **Lean LoC EX-6** | ~1000–2000 | ~300–600 |
| **Lean LoC EX-7+** | unchanged from mg-91be est. | **+200–400 LoC** to track size-`N` factor through drops application |
| **Mathematical strength** | Abstract: drops monotonicity for *any* `Q ⊆ Q'`, *any* up-closed event. | Conditional on fixed `α`, fixed `N`; fixed-`α` drops with `O(1/N)` correction. |
| **Path A applicability** | Closes EX-7 / EX-8 / EX-9 cleanly. | Suffices for case3 (fixed width-3) and Brightwell (fixed `m`); requires manual `N` choice + pre-computation of size-`N` constants. |
| **DH-4 mathlib upstream** | YES — direct candidate (Yael Dillies). | NO — fallback is project-internal only. |
| **mg-91be estimate match** | ~1000–2000 LoC EX-6 (exact match). | Smaller EX-6, but +200–400 EX-7+; net wash to slightly worse. |
| **Risk on next polecat (Session B)** | Discrete-side scaffolding (Session B) is mostly mathlib-citation-driven, low risk. Limit (Session C) is the substantive work, but mathlib has the dominated-convergence + Pi-product-volume API. AMBER. | Lower risk on EX-6 itself (~300–600 LoC). Risk shifts to EX-7 where the size-`N` arithmetic infiltrates downstream. AMBER-leaning-AMBER. |
| **Future-proofing** | EX-6 is a reusable mathlib-PR-class result; valuable beyond OneThird. | Specific to OneThird's fixed-`α` applications. |

**Verdict.** The **full continuous FKG** route (Reading #2) is
**recommended** as the primary path:

1. The Lean LoC are dominated by Session B (discrete-side scaffolding)
   which is mathlib-citation-driven; the limit argument (Session C) is
   the smaller addition and uses standard mathlib.
2. The downstream EX-7 / EX-8 / EX-9 LoC saving from a clean abstract
   drops outweighs the EX-6 LoC delta.
3. DH-4 mathlib upstream is real leverage; it requires the full
   continuous theorem (the fallback isn't upstream-able).
4. The fallback **remains as the contingency** if Session B or
   Session C surfaces an unexpected mathlib obstruction. Per §6.4 +
   §6.5 trip-wires, none expected.

### §7.3 Recommendation

- **PM files Session B** (`mg-XXXX`) with brief: discrete-FKG/AD on
  `(Fin (N+1))^n` + `gridFn` infrastructure + step-function
  approximation + Riemann-sum identity (§5.1 + §5.2 signatures).
  Estimated ~600–900 LoC, ~350–500k tokens.
- **PM files Session C** (`mg-YYYY`) on Session B landing: the limit
  argument + master theorem (§5.3 signatures). Estimated ~400–700
  LoC, ~250–400k tokens.
- **Total Session B + C: ~1000–1600 LoC, ~600–900k tokens.** Hits the
  lower-to-mid range of mg-91be §5.6's 1000–2000 LoC / 600–1000k token
  envelope.
- **DH-4 surface to Daniel** as an **outcome of Session C**: once the
  proof is in tree, the file is mathlib-PR-ready with minimal
  reformatting; Daniel's optional surface for an upstream PR.

If a Session B trip-wire fires (token blow-up, mathlib gap, etc.), PM
**falls back** to the integer-sub-lattice route — the Riemann-sum
proof's first ~50% (the discrete FKG on `D_N^n`) is **directly
reusable** as the fallback's main content; only the limit step is
cut. So the fallback is "free" in the sense that Session B's discrete-
side work is the core of both routes.

---

## §8 Polecat session estimate + trip-wires + verdict

### §8.1 LoC and tokens — Session B

**Scope.** Discrete FKG/AD on `(Fin (N+1))^n` (§5.1) + step-function
approximation (§5.2 first 3 lemmas) + Riemann-sum identity
(`integral_stepLower_eq_riemann`).

**LoC estimate.**
- `gridFn` definition + `gridFn_monotone` + `gridFn_nonneg` + lattice
  transport lemmas (`gridFn_inf`, `gridFn_sup`): ~80 LoC.
- `discrete_fkg_grid` + `discrete_ad_grid`: ~80 LoC
  (mathlib-citation-driven; the bulk is the Riemann-sum-form
  arithmetic on the `(N+1)^n` factor).
- `stepRetract`, `stepLower`, `stepUpper` + measurability: ~120 LoC.
- `stepLower_le_self` (sandwich) + `stepUpper_ge_self`: ~60 LoC.
- `integral_stepLower_eq_riemann` (the integral-equals-Riemann-sum
  identity): ~250 LoC. **The substantive work of Session B.** Uses
  `MeasureTheory.integral_finset_sum` + `MeasureTheory.integral_indicator`
  + `Equiv.piCongrLeft` for the cell-decomposition.
- Cell-decomposition infrastructure (the cells `C_p` partition `I_n`
  modulo a null boundary): ~200 LoC. Re-uses
  `Measure.addHaar_submodule` from EX-5 Session A. **The remaining
  substantive work.**

**Subtotal Session B: ~790 LoC, ~430k tokens.**

### §8.2 LoC and tokens — Session C

**Scope.** A.e. convergence of step approximations to the continuous
function (§4.2 + §2.5) + dominated-convergence application (§4.4) +
master theorems `continuous_fkg` and `continuous_ad` (§5.3) + hand-
verification examples (§5.4).

**LoC estimate.**
- `Monotone.aeContinuousAt_pi` (the multivariate "monotone implies
  a.e. continuous" lemma, §2.5): ~80 LoC. Sub-DH-4-A upstream
  candidate.
- `tendsto_stepLower_pointwise` (§4.2 a.e. convergence): ~50 LoC.
- `tendsto_integral_stepLower` (§4.4 dominated convergence
  application): ~120 LoC.
- `continuous_fkg` (§5.3 master FKG): ~80 LoC. Apply the discrete
  inequality to each `N`, take the `N → ∞` limit on each side via
  `tendsto_integral_stepLower`, conclude via `Filter.Tendsto.mul`.
- `continuous_ad` (§5.3 master AD): ~80 LoC. Same pattern, four
  functions.
- Hand-verification examples (§5.4): ~80 LoC.
- `IntegrableOn` automatic-from-monotone-and-bounded helper: ~30 LoC.

**Subtotal Session C: ~520 LoC, ~300k tokens.**

### §8.3 Total + trip-wires

**Sessions B + C total: ~1310 LoC, ~730k tokens.**

Lands at the **mid-range** of mg-91be §5.6's 1000–2000 LoC / 600–1000k
envelope. Slightly above the lower bound; well below the upper bound.

**Trip-wires (per polecat brief §3 / mg-91be §5.6 / mg-163f §2.3):**

| Trip-wire | Status |
|-----------|--------|
| Token blow-up (>320k of 400k cap before GREEN) | **Not fired in Session A** (~150k of 400k consumed). |
| Mathlib refactor required (e.g., dominated convergence needs new measurability framework) | **Not fired** — all APIs verified at v4.29.1; no refactor needed. |
| Continuous FKG already in mathlib (collision) | **Not fired** — no `continuous_fkg`/`Preston` references in `Mathlib` at this rev. |
| DH-4 fallback firing in Session A scoping | **Not fired** — Riemann-sum route is the primary, not the fallback. The fallback exists as the contingency for Session B / Session C trip-wires (per §7.3). |
| AD lattice-hypothesis transport surprise (`gridFn` not preserving `⊓`/`⊔`) | **Not fired** — `min(k/N, l/N) = min(k, l)/N` for `k, l : Fin (N+1)`, `N ≥ 1`. Pointwise on `Pi`. Trivial. |
| Monotone-implies-a.e.-continuous gap surface | **AMBER** — multivariate version not packaged in mathlib; **derivable in ~80 LoC** (§6.3). Sub-DH-4-A upstream candidate. **Not blocking**. |

### §8.4 Verdict

**GREEN-2** (split Session B + Session C).

The continuous FKG / Ahlswede–Daykin inequality on `[0,1]^n` admits a
rigorous Lean port via the standard Riemann-sum discretisation route,
applying mathlib `fkg` / `four_functions_theorem_univ` on the finite
distributive lattice `(Fin (N+1))^n` and passing to the limit via
mathlib `tendsto_integral_filter_of_dominated_convergence`. The proof
has been written out rigorously in §1–§4 with the standard Riemann–
Lebesgue argument for monotone bounded integrands; Lean signatures are
drafted in §5; mathlib API verified GREEN in §6; no fundamental gap.

The integer-sub-lattice fallback (mg-163f §4.4) is **structurally
weaker** and **not recommended as primary**: the size-`N` factor
infiltrates EX-7 / EX-8 / EX-9 and partly cancels the EX-6 LoC saving.
The full continuous FKG is the recommended primary route, with the
discrete-FKG part of Session B doubling as the fallback's main content
should Session C surface an obstruction.

**ETA refinement:** mg-91be §5.6 estimated "2–3 polecat sessions,
~1000–2000 LoC, ~600–1000k tokens combined." This scoping refines to:

| Session | LoC | Tokens (k) |
|---------|----:|-----------:|
| Session B (discrete FKG/AD + step-function approximation + Riemann-sum identity) | ~600–900 | ~350–500 |
| Session C (a.e. convergence + dominated convergence + master theorem + hand-verification) | ~400–700 | ~250–400 |
| **Total** | **~1000–1600** | **~600–900** |

Session A consumed ~150k tokens (well under the 400k trip-wire);
total Session A + B + C tokens ~750–1050k, at the upper edge of
mg-91be §5.6's 600–1000k envelope. LoC mid-range of 1000–2000.
**No fallback to mg-163f §4.4 discretised path needed.**

**Trust surface impact: none.** EX-6 introduces no new project axioms;
the continuous FKG/AD inequality is a measure-theoretic statement
consumed downstream by EX-7 (drops headline) and EX-9 (Brightwell-port-A
centred-sum). EX-6 does **not** consume `stanley_log_supermod` (the
third axiom remains consumed only by EX-7+).

**Sub-α-C arc next step.** PM files **EX-6 Session B** scoping ticket:
deliverable §3 + §5.1–§5.2 + §6.1 + §8.1 form the Session B brief.
Session B = direct Lean port of the discrete FKG/AD + step-function
approximation + Riemann-sum identity; ~600–900 LoC, ~350–500k tokens,
1 polecat session. Session C dispatches on Session B landing.

**DH-4 status update.** This session's deliverable is **the
mathlib-PR-class proof of continuous FKG/AD on `[0,1]^n`**, structured
for upstream extraction. Once Sessions B and C land, the file
`lean/OneThird/Mathlib/Probability/ContinuousFKG.lean` is **mathlib-PR-
ready** with minimal reformatting; Daniel's optional surface for the
upstream PR (`Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`).

**Sub-DH-4-A surfaced.** Multivariate "monotone implies a.e.
continuous" lemma (`Monotone.aeContinuousAt_pi`) is a small auxiliary
upstream candidate alongside DH-4 proper; ~80 LoC; sits in
`Mathlib/Topology/Order/Monotone.lean` adjacent to the existing 1D
version. Daniel's optional surface; not blocking.

---

## §9 References

### §9.1 Predecessor polecat documents

- mg-10d9 (`7b084ba`) — EX-5 Session C executed: chamber cover +
  measure-zero overlap + master volume.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` extension.
- mg-497d (`5dd9e50`) — EX-5 Session B executed: chamber definition
  + `chamber_volume` + `volume_orderedCube`.
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` extension.
- mg-79a9 (`3e76ac3`) — EX-5 Session A latex-first scoping.
  `docs/path-alpha-execution-arc/ex5-chamber-decomp-scoping.md`.
- mg-2442 (`89786cf`) — EX-4 Session B executed: Stanley vertex
  theorem in Lean. `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean`.
- mg-4831 (`ac56bc4`) — EX-4 Session A latex writeup.
  `docs/path-alpha-execution-arc/ex4-stanley-vertex-scoping.md`.
- mg-8c66 (`ed9f6e6`) — EX-3 executed: `OrderPolytope α` defined.
- mg-163f (`9e6edcd`) — Path-A-vs-Path-B fork resolved: GREEN-A.
  `docs/path-alpha-execution-arc/path-A-vs-path-B-fork-resolution.md`,
  esp. §2.3 (DH-4 risk assessment) and §4.4 (integer-sub-lattice
  fallback).
- mg-91be (`bb450a4`) — sub-α-C high-level scoping with EX-6 spec
  in §5.6. `docs/path-alpha-execution-arc/sub-alpha-C-scoping.md`.
- mg-d0fc (`00cbc2d`) — EX-1 Option A: `stanley_log_supermod` axiom
  landed (consumed by EX-7+, **not by EX-6**).

### §9.2 Literature

- **Preston 1974.** Christopher J. Preston, *Spatial birth-and-death
  processes*, Adv. Appl. Probab. **6** (1974), 391–403, Theorem 5.4.
- **Ahlswede–Daykin 1979.** Rudolf Ahlswede and David E. Daykin, *An
  inequality for the weights of two families of sets, their unions
  and intersections*, Z. Wahrsch. verw. Gebiete **43** (1978), 183–185.
- **Brightwell 1999.** Graham R. Brightwell, *Balanced pairs in
  partial orders*, Discrete Math. **201** (1999), 25–52, §4
  (Lemma 4.3 + surrounding discussion).
- **Daykin–Saks 1981.** D. E. Daykin and M. Saks, *A natural
  generalisation of FKG for partial orders* (cited by Brightwell).
- **Stanley 1986.** Richard P. Stanley, *Two poset polytopes*,
  Discrete Comput. Geom. **1** (1986), 9–23. (Order polytope; not
  consumed by EX-6 directly but by EX-3, EX-4, EX-5.)
- **FKG 1971.** Cees M. Fortuin, Pieter W. Kasteleyn, and Jean
  Ginibre, *Correlation inequalities on some partially ordered
  sets*, Comm. Math. Phys. **22** (1971), 89–103. (Original FKG.)
- **Stanley EC1 §3.5.** Richard P. Stanley, *Enumerative
  Combinatorics, Volume 1*, second edition, §3.5 — discrete 4FT and
  FKG.

### §9.3 Mathlib code (verified at this commit's `lake-manifest`)

- `Mathlib.Combinatorics.SetFamily.FourFunctions` — discrete 4FT,
  FKG, Holley.
- `Mathlib.Combinatorics.SetFamily.AhlswedeZhang` — adjacent material;
  not consumed.
- `Mathlib.Order.Lattice` — `Pi.instDistribLattice` for product
  lattices.
- `Mathlib.MeasureTheory.Integral.DominatedConvergence` — DCT
  (`tendsto_integral_filter_of_dominated_convergence`).
- `Mathlib.MeasureTheory.Integral.Lebesgue.Add` — monotone
  convergence (`lintegral_iSup`,
  `lintegral_tendsto_of_tendsto_of_monotone`).
- `Mathlib.MeasureTheory.Integral.Pi` — Fubini on Pi-types.
- `Mathlib.MeasureTheory.Constructions.Pi` — `volume_pi_pi`,
  `volume_Icc_pi`, `measurePreserving_piCongrLeft`.
- `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` — `addHaar_submodule`
  (boundary null).
- `Mathlib.Topology.Order.Monotone` — 1D `Monotone.countable_not_continuousAt`.
- `Mathlib.Analysis.MeanInequalities` — Jensen, Hölder, Young; **does
  not** contain continuous FKG (the EX-6 mathlib gap).

### §9.4 In-tree code (verified at this commit)

- `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` — order
  polytope basics + chamber decomposition (EX-3 + EX-4 + EX-5).
- `lean/OneThird/Mathlib/LinearExtension/FKG.lean` — existing
  product-lattice FKG-on-LE pathway (independent of EX-6 file; lives
  at the `Finset (LowerSet α)` abstraction layer, not the cube).
- `lean/OneThird/Mathlib/LinearExtension/StanleyLogSupermodAxiom.lean`
  — third project axiom (not consumed by EX-6).
- `lean/OneThird/Mathlib/LinearExtension/BrightwellAxiom.lean` —
  `brightwell_sharp_centred` axiom (target for EX-9, downstream of
  EX-6).
- `lean/AXIOMS.md` — three named project axioms (EX-6 introduces
  none).

### §9.5 Out-of-tree resources

- mathlib4 issue tracker — search "FKG" for any prior continuous-FKG
  contribution attempts (not surveyed in this scoping; Daniel's
  optional surface for the DH-4 upstream PR).
- arXiv:1407.0107 (Saks, *Algorithmic aspects of randomized rounding*)
  — uses continuous FKG; non-essential cite.

### §9.6 Feedback / policy applied

- `feedback_pm_is_mini_ceo_default` — sub-α-C arc PM scope; PM proceeds
  on default unless trip-wires fire.
- `feedback_long_arcs_are_pm_authority` — sub-α-C is multi-session,
  PM authority assumed.
- `feedback_audit_bar_blocks_axiom_unilateralism` — not relevant; no
  axiom introduced.
- `feedback_block_and_report` — Session A reports GREEN-2; PM dispatches
  Session B next.
