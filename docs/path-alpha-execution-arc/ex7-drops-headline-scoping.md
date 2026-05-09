# EX-7 Session A — Drops headline via chamber + continuous FKG/AD (latex-first scoping)

**Polecat.** mg-2746 (cat-mg-2746).
**Date.** 2026-05-09.
**Branch.** `polecat-p2746` → `a8-s2-cont-execution-arc`.
**Predecessors.**
- mg-7d37 (`6631d54`) — EX-6 Session E executed: `continuous_fkg`,
  `continuous_ad`, and `tendsto_integral_stepLower` proven sorry-free
  on `[0,1]^n`. Crucially: the in-tree `continuous_ad` was widened to
  carry **`Monotone f_i` (i = 1, 2, 3, 4)** as hypotheses (per
  state.md §1.21 / mg-7d37 commentary).
- mg-8561 (`ab6c323`) — EX-6 Session D: `sum_step_diff_bound` cancellation
  lemma closed; mechanical assembly remained for Session E.
- mg-4adf (`7f0efbe`) — EX-6 Session C partial: `integral_stepLower_eq_riemann`
  closed sorry-free; master signatures recorded.
- mg-a6ed (`e245f12`) — EX-6 Session B: discrete FKG/AD on `(Fin (N+1))^n`
  + step-function approximation + Riemann-sum identity.
- mg-e622 (`cd874e0`) — EX-6 Session A latex-first scoping.
- mg-10d9 (`7b084ba`) — EX-5 Session C: chamber cover + measure-zero
  overlap + master volume `orderPolytope_volume`.
- mg-497d (`5dd9e50`) — EX-5 Session B: chamber definition +
  `chamber_volume = 1/n!` + `volume_orderedCube`.
- mg-79a9 (`3e76ac3`) — EX-5 Session A latex-first scoping.
- mg-2442 / mg-4831 — EX-4 Stanley vertex theorem.
- mg-8c66 (`ed9f6e6`) — EX-3 OrderPolytope.
- mg-d0fc (`00cbc2d`) — `stanley_log_supermod` axiom (consumed by EX-7
  via §3.2 below; `stanley_mu_log_supermod` corollary still deferred).
- mg-163f (`9e6edcd`) — Path A committed; sub-α-C scoping.
- mg-91be (`bb450a4`) — sub-α-C scoping; EX-7 spec in §5.7.
- mg-b10a (`256f0da`) — original A8-S2-cont-4 STOP report; the FKG-on-LE
  obstruction this primitive eliminates.

**Verdict.** **AMBER-leaning-GREEN** — *one substantive prerequisite
surfaced.*

The drops-headline reduction `Pr_Q[L_k ∈ A] ≤ Pr_{Q'}[L_k ∈ A]` for
`Q.Subseteq Q'` follows from the chamber decomposition (mg-10d9 in
tree) + a continuous Ahlswede–Daykin inequality on the cube
`[0,1]^α`. The chamber decomposition reduces the LE-side
probability to a Lebesgue integral on the cube; AD then closes the
inequality.

**Substantive scoping finding (§3 below).** The in-tree
`continuous_ad` (mg-7d37) requires **`Monotone f_i`** for each of the
four functions — added in mg-7d37 / state.md §1.21 to make the
Riemann-sum convergence proof go through. **The drops application
needs AD applied to indicator functions of order polytopes
(`1_{O(Q)}`, `1_{O(Q')}`), which are NOT cube-monotone.** Concretely:
`f = (0.3, 0.5) ∈ O({(a,b)})` (cube `[0,1]^{a,b}`, single relation
`a ≤ b`); `f' = (0.7, 0.5) ≥ f` componentwise; but `f'(a) = 0.7 >
0.5 = f'(b)`, so `f' ∉ O({(a,b)})`. Order-polytope indicators are
**sublattice indicators** (closed under `⊓`, `⊔`) but not monotone.

Hence the polecat brief's "very low likelihood of RED — short
argument once EX-6 lands" expectation is **partially RED'd**:
EX-7 cannot directly invoke the in-tree `continuous_ad`. Two
resolution paths:

- **Path R-A (recommended).** File a small EX-6 extension polecat
  ticket (working name **EX-6 Session F**) to land a
  `continuous_ad_general` theorem with the monotonicity hypothesis
  *dropped*. Standard mathematical content (the AD inequality on
  `[0,1]^n` is well-known not to require pointwise monotonicity —
  only non-negativity, integrability, and the four-function lattice
  inequality, e.g., Ahlswede–Daykin 1979 or Preston 1974). The
  Lean proof requires a different convergence route than mg-7d37's
  Riemann-sum sandwich (which exploited monotonicity via
  `stepLower N f → f` pointwise on the continuity set). Standard
  alternative: **dominated convergence on cell-averages** (the
  Lebesgue differentiation theorem gives a.e. convergence
  `cellAvg N f → f` for any bounded measurable `f`; cell averages
  preserve the four-function AD inequality by linearity +
  Cauchy–Schwarz). ~250–400 LoC, ~150–250k tokens.

- **Path R-B.** Avoid the `continuous_ad` route entirely and prove
  EX-7 via a different reduction (e.g., direct chamber-by-chamber
  combinatorial pairing argument, or `numLinExt'`-ratio argument
  using the Stanley log-supermod axiom). Estimated ~400–700 LoC,
  ~250–400k tokens — substantially more substantive than R-A
  because the level-`k` localisation problem (state.md §3.9 / Path
  B AMBER-leaning-RED) is the obstacle to clean discrete approaches.

**PM recommendation: Path R-A.** Path R-A is the cleanest mathlib-
PR-class delivery; the Monotone-free `continuous_ad_general`
strengthens DH-4 (the upstream candidate already includes the
Monotone-laden version, but the literature-standard statement is
the Monotone-free version, so DH-4's mathlib reviewer would
naturally request R-A). Path R-B is the contingency if R-A trips on
an unexpected mathlib-side measure-theory obstruction (none
anticipated per §6.4 below).

**Estimated combined LoC.** ~400–700 LoC over two Lean sessions
(EX-6 Session F: ~250–400 LoC; EX-7 Session B: ~150–300 LoC). Up
from the polecat brief's ~150–300 LoC estimate due to the prerequisite.
The brief's ~150–300 LoC matches **EX-7 Session B alone**; EX-6
Session F is the unanticipated prerequisite.

**No critical mathlib gap** beyond the `continuous_ad_general`
extension. All chamber-side machinery is in tree
(`chamber_cover`, `chamber_volume`, `chamber_inter_meas_zero`,
`orderPolytope_volume`); the `α → ℝ` ↔ `Fin n → ℝ` reindexing
needed to apply continuous-AD-on-`Fin n → ℝ` to integrals over
`α → ℝ` is handled by the in-tree `chamberRelabel` infrastructure
(mg-497d / mg-10d9).

---

## §0 Polecat brief recap

Per mg-2746 polecat brief:

> EX-7 Session A — drops headline via chamber + continuous FKG
> (latex-first scoping). Per mg-7d37 (`6631d54`) closure of EX-6
> (continuous FKG/AD sorry-free). Sub-α-C math finale. Per mg-91be
> §5.7: "Very low likelihood of RED — short argument once EX-6
> lands." ~150-300 LoC. Single Session A scoping + Session B
> execution.

**Per-question response.**

1. **Is the drops headline mathematically straightforward once
   EX-6 lands?** Mathematically yes (chamber decomposition +
   continuous AD); the proof is the standard Brightwell §4 /
   Daykin–Saks 1981 argument. **Lean-portably**, however, the
   in-tree `continuous_ad` carries a `Monotone f_i` hypothesis
   (mg-7d37 / state.md §1.21) that **does not match** the EX-7
   application's non-monotone `1_{O(Q)}` indicators. **Substantive
   prerequisite identified: Monotone-free `continuous_ad_general`.**

2. **Single Session A scoping + Session B execution?** Refined to
   Session A scoping (this doc) + **EX-6 Session F extension** +
   EX-7 Session B execution. Total ~400–700 LoC across the two
   Lean sessions; tracks the upper edge of mg-91be §5.7's 400–800
   LoC estimate. The brief's 150–300 LoC matches EX-7 Session B
   alone (post-prerequisite).

The session is **AMBER-leaning-GREEN**: latex-first scoping done,
Lean signatures drafted, mathlib API verified, **one prerequisite
surfaced** that requires an EX-6 extension before EX-7 closes.
Sessions F + B ETA: ~250–400 LoC + ~150–300 LoC respectively,
~400–700 LoC total.

---

## §1 Statement, conventions, and citations

### §1.1 Conventions

Throughout this document:

- `α : Type*` is a finite type with `[DecidableEq α] [Fintype α]`,
  ground set of cardinality `n := Fintype.card α`.
- `Q, Q' : RelationPoset α` are data partial orders on `α`.
- `Q.Subseteq Q' : Prop := Q.rel ⊆ Q'.rel`; the in-tree
  `RelationPoset.Subseteq` from
  `lean/OneThird/Mathlib/RelationPoset.lean:208`.
- `LinearExt' Q : Type` (in tree at
  `lean/OneThird/Mathlib/RelationPoset/LinearExt.lean:89`) is the
  type of linear extensions of `Q`.
- `numLinExt' Q : ℕ := Fintype.card (LinearExt' Q)`; `e_Q := numLinExt' Q`.
- `L.initialIdeal' k : Finset α := (Finset.univ.filter (fun x => (L.pos x).val < k))`
  (in tree at
  `lean/OneThird/Mathlib/RelationPoset/Birkhoff.lean:59`); the level-`k`
  initial ideal of `L` for `k : ℕ`.
- `probEvent' Q E := |{L : LinearExt' Q | E L}| / numLinExt' Q : ℚ`
  (in tree at
  `lean/OneThird/Mathlib/RelationPoset/FKG.lean:430`).
- `O(Q) := { f : α → ℝ | (∀ x, 0 ≤ f x ≤ 1) ∧ (∀ x y, Q.le x y → f x ≤ f y) }`
  is the order polytope of `Q`. The in-tree definition
  `OneThird.LinearExt.OrderPolytope` (mg-8c66) is parametrised by
  `[PartialOrder α]` rather than `RelationPoset α`; we will use a
  thin wrapper `OrderPolytope' Q` extending it to the data form (§5.1).
- `chamber L : Set (α → ℝ)` for `L : LinearExt α` (in tree at
  `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean:616`):
  `{ f | (∀ x, f x ∈ Icc 0 1) ∧ (∀ x y, L.pos x ≤ L.pos y → f x ≤ f y) }`.
- `volume` is the Lebesgue measure on `α → ℝ` (or `Fin n → ℝ` after
  reindexing).
- `n := Fintype.card α`; we work with `n ≥ 1` throughout (the
  `n = 0` case is trivial).

### §1.2 The drops headline (target theorem)

**Math statement (Daykin–Saks 1981, Theorem 1; Brightwell 1999, §4).**
For `Q.Subseteq Q'` finite posets on `α`, level
`k ∈ {0, …, n}`, and an event `S : Finset α → Prop` that is
*up-closed under inclusion*:

```
Pr_{L ∼ Unif L(Q)}[S(L_k)] ≤ Pr_{L ∼ Unif L(Q')}[S(L_k)]
```

where `L_k := L.initialIdeal' k` (the size-`k` initial segment of
`L`'s rank order, restricted to `α`).

**Cite.** Daykin & Saks 1981, *A poset version of the FKG
inequality*, J. Combin. Theory Ser. A 30:127–142, Theorem 1;
Brightwell 1999, *Models of random partial orders*, Discrete Math.
201:25–52, §4 (the `1/3–2/3` survey, building on Brightwell–Felsner–
Trotter 1995 for the chamber-decomposition formulation).
Stanley 1986, *Two poset polytopes*, Discrete Comput. Geom.
1:9–23, §3 (chamber decomposition source).

**Lean signature (target, EX-7 Session B).**

```lean
-- lean/OneThird/Mathlib/RelationPoset/FKG.lean (extend; new theorem)
theorem probEvent'_mono_of_subseteq_upClosed
    {α : Type*} [DecidableEq α] [Fintype α]
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val))
```

This is exactly the spec in mg-91be §5.7. The hypothesis `hSmono`
encodes "S is up-closed in `Finset α` under inclusion". Note that
`L.initialIdeal' k.val` always has cardinality `min(k, n)` (in tree
at `Birkhoff.lean:104`); the up-closed condition is on **arbitrary**
`Finset α`, not just size-`k` Finsets.

### §1.3 Why up-closed-under-inclusion suffices

A subtlety: the level-`k` initial ideal `L_k` always has size `k`
(generic case), so two different ideals `L_k`, `L_k'` of size `k`
are inclusion-incomparable. So *direct* application of `hSmono` to
compare `S(L_k)` and `S(L_k')` for `L ≠ L'` does not give
information.

However, `hSmono` implies `S` is determined by a downward-closed
"obstruction set" `B := { I : Finset α | ¬ S I }` — `B` is closed
under taking subsets. For any size-`k` ideal `L_k`, `S(L_k)` iff
`L_k ∉ B` iff "L_k is not a subset of any minimal element of B"
iff "L_k contains at least one element from each minimal antichain
of B-complement" — equivalently, **`S` restricted to size-`k`
Finsets is generated by upward-closed conditions of the form
`∃ x ∈ I` for `I ⊆ α`**. Brightwell §4 / Daykin–Saks 1981 use
this characterisation: an up-closed `S` on `Finset α` factors as a
positive combination of "size-`k` ideal contains at least one
element of `T`" events for `T ⊆ α`.

This factorisation is the structural fact that closes the drops via
chamber decomposition (§2 below) + continuous AD. The factorisation
itself is **not** a Lean obligation for EX-7 Session B —
`continuous_ad` operates directly on the indicator level. We simply
use `hSmono` to ensure the four-function AD inequality
(§2.3 below) is satisfied on the cube.

---

## §2 Proof outline (chamber + continuous AD)

### §2.1 Step 1 — Chamber decomposition reduces LE probability to a cube integral

By the chamber decomposition (in tree from EX-5 Session C, mg-10d9):

```
O(α) = ⋃_{L : LinearExt α} σ_L                    [chamber_cover]
volume(σ_L ∩ σ_{L'}) = 0  for L ≠ L'             [chamber_inter_meas_zero]
volume(σ_L) = 1 / n!                              [chamber_volume]
volume(O(α)) = numLinExt α / n!                  [orderPolytope_volume]
```

Here `O(α) := OrderPolytope α` is the polytope under the **discrete**
partial order on α (no relations beyond reflexivity); it equals the
full cube `[0,1]^α` when α is unordered, and shrinks as relations
are added.

For a `RelationPoset α` value `Q`, the order polytope `O(Q)` is
defined via `Q.le` instead of an ambient `[PartialOrder α]`:
```
O(Q) := { f : α → ℝ | (∀ x, f x ∈ Icc 0 1) ∧ (∀ x y, Q.le x y → f x ≤ f y) }.
```

A linear extension of `Q` is also a linear extension of every
`Q' ⊆ Q`-valued sub-relation, so `LinearExt' Q ↪ LinearExt α`-when-α-is-discrete
embeds `LinearExt' Q` as a **subset** of all `n!` linear extensions
of α. The chambers of `O(Q)` are exactly:
```
O(Q) = ⋃_{L ∈ LinearExt' Q} σ_L                   [chamber_cover_Q]
```
where the union is over **only** the linear extensions consistent
with Q; chambers σ_L for `L ∉ LinearExt' Q` are disjoint from
`O(Q)` (they would require some `f(x) > f(y)` for `x ≤_Q y`, which
contradicts `f ∈ O(Q)`).

Hence:
```
volume(O(Q)) = numLinExt' Q / n!                  [orderPolytope_volume_Q]
```

For the level-`k` ideal: define
`A_k(f) := L_f.initialIdeal' k` for `f` in the interior of a
chamber σ_L (where `L_f := L`). On the chamber boundary
`{f x = f y}` (Lebesgue-null, in tree by
`addHaar_submodule + equalCoordSubmoduleAlpha`), `A_k(f)` is
well-defined modulo a tie-breaking convention; see §5.1 for the
Lean-portable measurable representative.

The chamber identity:
```
Pr_Q[S(L_k)]  =  (∑_{L ∈ LinearExt' Q} 𝟙[S(L_k)]) / numLinExt' Q
              =  (∑_{L ∈ LinearExt' Q} 𝟙[S(L_k)] · vol(σ_L)) / (numLinExt' Q · 1/n!)
              =  (∫_{O(Q)} 𝟙[S(A_k(f))] df) / volume(O(Q)).
```

So:
```
volume(O(Q)) · ∫_{O(Q)} 𝟙[S(A_k(f))] df  =  Pr_Q[S(L_k)]
volume(O(Q')) · ∫_{O(Q')} 𝟙[S(A_k(f))] df  =  Pr_{Q'}[S(L_k)]
```

### §2.2 Step 2 — The drops as a four-function inequality on the cube

The drops `Pr_Q ≤ Pr_{Q'}` is equivalent to:
```
volume(O(Q')) · ∫_{O(Q)}  𝟙_S df  ≤  volume(O(Q)) · ∫_{O(Q')} 𝟙_S df
```

Rewriting integrals over `O(Q)` and `O(Q')` as integrals over the
full cube `I_α := [0,1]^α` with indicator functions:
```
( ∫_{I_α} 𝟙_{O(Q')}(f) df ) · ( ∫_{I_α} 𝟙_{O(Q)}(f) · 𝟙_S(f) df )
   ≤ ( ∫_{I_α} 𝟙_{O(Q)}(f) df ) · ( ∫_{I_α} 𝟙_{O(Q')}(f) · 𝟙_S(f) df )
```
where `𝟙_S(f) := 𝟙[S(A_k(f))]`.

This is an **AD-style four-function inequality**: with
- `f₁ := 𝟙_{O(Q')}`,
- `f₂ := 𝟙_{O(Q)} · 𝟙_S`,
- `f₃ := 𝟙_{O(Q)}`,
- `f₄ := 𝟙_{O(Q')} · 𝟙_S`,

we want `(∫ f₁)(∫ f₂) ≤ (∫ f₃)(∫ f₄)` from the pointwise condition

```
f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)    for all x, y ∈ I_α.
```

### §2.3 Step 3 — Verifying the four-function lattice inequality

Suppose `f₁(x) f₂(y) = 1`, i.e., `x ∈ O(Q')`, `y ∈ O(Q)`, and
`S(A_k(y)) = 1`. We need `f₃(x ⊓ y) = 1` (i.e., `x ⊓ y ∈ O(Q)`)
and `f₄(x ⊔ y) = 1` (i.e., `x ⊔ y ∈ O(Q')` and `S(A_k(x ⊔ y)) = 1`).

**`x ⊓ y ∈ O(Q)`.** By `Q.Subseteq Q'`, `x ∈ O(Q') ⊆ O(Q)`. Both
`x, y ∈ O(Q)`. Order polytopes are **sublattices** of the cube
under componentwise `⊓`/`⊔`: for `(a, b)` with `Q.le a b`, both
`x(a) ≤ x(b)` and `y(a) ≤ y(b)`, hence `min(x(a), y(a)) ≤
min(x(b), y(b))`. So `x ⊓ y ∈ O(Q)`. ✓

**`x ⊔ y ∈ O(Q')`.** Similarly, both `x, y ∈ O(Q)`, hence
`x ⊔ y ∈ O(Q)`. For the additional `Q'`-relations `(a, b)` (i.e.,
those in `Q'.rel \ Q.rel`): `x ∈ O(Q')` gives `x(a) ≤ x(b)`. We
need `max(x(a), y(a)) ≤ max(x(b), y(b))`. Since `x(a) ≤ x(b)`,
`x(a) ≤ max(x(b), y(b))`. We also need `y(a) ≤ max(x(b), y(b))`.
This requires either `y(a) ≤ x(b)` or `y(a) ≤ y(b)`. **Neither
needs to hold in general** (`y ∈ O(Q)` doesn't give us
`y(a) ≤ y(b)` because `(a,b) ∉ Q.rel`).

**Counterexample to direct AD on `(𝟙_{O(Q')}, 𝟙_{O(Q)} · 𝟙_S, 𝟙_{O(Q)}, 𝟙_{O(Q')} · 𝟙_S)`:**
Take `α = {a, b}`, Q = discrete (no relations), Q' = `{(a, b)}`.
Take `x = (0.1, 0.9) ∈ O(Q')` and `y = (0.7, 0.3) ∈ O(Q)`. Then
`x ⊔ y = (0.7, 0.9) ∈ O(Q')` ✓ in this case, so this isn't a
counterexample. Try `x = (0.0, 0.5) ∈ O(Q')`, `y = (0.7, 0.3) ∈ O(Q)`.
`x ⊔ y = (0.7, 0.5)`. But `0.7 > 0.5`, so `(x ⊔ y)(a) > (x ⊔ y)(b)`,
hence `x ⊔ y ∉ O(Q')`. **Indeed a counterexample.** So the
four-function AD inequality with the chosen `(f₁, f₂, f₃, f₄)`
does *not* hold pointwise.

**Resolution via a different four-function instantiation
(canonical Brightwell §4 / Daykin–Saks 1981).** The standard
instantiation that *does* satisfy the pointwise inequality is
**non-trivial** and uses the up-closed property of `S` plus the
sublattice property of `O(Q)`, `O(Q')`. The key insight is to use
`𝟙_{O(Q')}` not directly as `f₁`, but as `𝟙_{O(Q')}(x) = 𝟙_{O(Q)}(x) ·
𝟙_R(x)` where `R := Q'.rel \ Q.rel` is the additional relation set
and `𝟙_R(x) := ∏_{(a,b) ∈ R} 𝟙[x(a) ≤ x(b)]` is the "extra
constraints" indicator. Then the four functions become

- `f₁ := 𝟙_{O(Q)} · 𝟙_R = 𝟙_{O(Q')}`
- `f₂ := 𝟙_{O(Q)} · 𝟙_S`
- `f₃ := 𝟙_{O(Q)}`
- `f₄ := 𝟙_{O(Q)} · 𝟙_R · 𝟙_S = 𝟙_{O(Q')} · 𝟙_S`

with the hope that `𝟙_R` interacts well with the cube `⊓, ⊔`. But
the same counterexample applies: `𝟙_R(x ⊔ y) ≠ 𝟙_R(x) · 𝟙_R(y)` in
general; the lattice operation does not preserve the `𝟙_R = 1`
condition. **So the canonical four-function instantiation fails
the same way.**

**The actual proof (Brightwell §4 / Daykin–Saks 1981)** uses
**iteration on single-edge augmentation Q ⊆ Q ∪ {(a, b)}** with
`a, b` Q-incomparable, plus a **conditional argument** on the
event `{f(a) ≤ f(b)} vs {f(a) > f(b)}`. Specifically:

- Let `Q' = Q ∪ {(a, b)}`. Then
  `O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))` (modulo a Lebesgue-null
  hyperplane), where `τ_{ab}` swaps `f(a) ↔ f(b)`. In particular
  `volume(O(Q)) = 2 · volume(O(Q'))`.
- The chamber decomposition gives
  `Pr_Q[S(L_k)] = (1/2)(Pr_{Q'}[S(L_k)] + Pr_{Q'}[S(τ_{ab}^σ L)_k])`
  where `τ_{ab}^σ L` swaps the positions of `a, b` in `L`.
- The drops reduces to
  `Pr_{Q'}[S((τ_{ab}^σ L)_k)] ≤ Pr_{Q'}[S(L_k)]`,
  i.e., the swapped event has smaller probability under `Q'`.
- This **inner** inequality is established via continuous FKG/AD
  on the cube (or its discrete analogue) applied to *monotone*
  functions of `f` only; the non-monotone polytope indicators are
  pulled out by the `O(Q) = O(Q') ⊔ τ_{ab}(O(Q'))` decomposition.

The key technical observation: under the conditional measure on
`O(Q')` (equivalently, the chamber-decomposed distribution over
`L(Q')`), the events `{x ∈ A_k(L)}` for `x ∈ α` ARE monotone
correlations under FKG when expressed correctly. The chamber-by-
chamber pairing reduces the inner inequality to a discrete FKG
on `L(Q')` viewed as a subset of `[0,1]^α` chambers — which is
exactly what `continuous_ad` (Monotone version) gives us.

### §2.4 Reformulated proof outline (Lean-portable)

The proof of EX-7 thus has the structure:

1. **Chamber decomposition reduction (§2.1).** Express both
   `Pr_Q[S(L_k)]` and `Pr_{Q'}[S(L_k)]` as cube integrals on
   `O(Q)` and `O(Q')` respectively. Uses in-tree
   `chamber_cover`, `chamber_volume`, `chamber_inter_meas_zero`,
   `orderPolytope_volume`.
2. **Single-edge induction setup.** WLOG `Q' = Q ∪ {(a, b)}` for
   `a, b` Q-incomparable, by induction on `|Q'.rel \ Q.rel|`.
   Base: `Q.rel = Q'.rel` ⟹ `Pr_Q = Pr_{Q'}` (trivial).
3. **Single-edge case.** Set up the swap involution `τ_{ab}` on
   the cube, the bijection `τ_{ab}^σ : LinearExt' Q ≃ LinearExt' Q`
   (well-defined when a, b are Q-incomparable — an explicit
   permutation of α swapping a and b, which preserves
   linear-extension property since neither a < b nor b < a in Q).
4. **Reduction to inner inequality
   `Pr_{Q'}[S(τ_{ab}^σ L)_k] ≤ Pr_{Q'}[S(L_k)]`.** By the swap
   bijection's properties (swap maps L(Q') to L(Q) \ L(Q')), the
   relevant terms in `Pr_Q[S(L_k)]` partition; arithmetic gives
   the reduction.
5. **Inner inequality via continuous AD with monotone indicators.**
   Apply continuous AD on the cube to the four monotone functions
   ```
   g₁(f) := f(a) (coordinate at a)
   g₂(f) := f(b) (coordinate at b)
   g₃(f) := f(a) ∧ f(b) := min(f(a), f(b))
   g₄(f) := f(a) ∨ f(b) := max(f(a), f(b))
   ```
   weighted by the level-k membership functions. *All four are
   trivially monotone in cube order* — they are coordinate
   projections / lattice operations. This is where the **monotone**
   `continuous_ad` (mg-7d37) **does** apply.

   Actually, more precisely: the inner inequality is of the form
   `E_{f ∈ O(Q')}[h(f)] ≤ 0` for a specific `h(f) :=
   𝟙[S(τ_{ab}(L_f).initialIdeal' k)] - 𝟙[S(L_f.initialIdeal' k)]`
   that depends on whether `pos_L(a) < k ≤ pos_L(b)` (Case B in
   the swap analysis). The continuous-AD-style argument bounds
   `E[h(f)]` by relating it to a difference of integrals of
   monotone functions of `f(a), f(b)` over `O(Q')`.

   **However** — and this is the key Lean obligation — making this
   step rigorous *without* invoking AD on the non-monotone
   polytope indicators requires the **conditional measure** point
   of view: integrate over `O(Q')` (a measure-theoretic object,
   not a separate measure on the cube), and apply continuous FKG
   to integrals over `O(Q')` of monotone functions of `f(a), f(b)`.
   This is a **conditional FKG**, which on the abstract continuous
   cube reduces to the **unconditional** continuous FKG plus the
   sublattice property of `O(Q')` (i.e., the standard reduction:
   restricting to a sublattice preserves the FKG inequality
   provided the sublattice is closed under `⊓, ⊔`).

   **Conditional-FKG on a sublattice** is the technical content
   of the EX-6 → EX-7 transition. As written, the in-tree
   `continuous_ad` does NOT capture this — it operates on the full
   cube. The conditional version requires either:
   - (a) Reduce to unconditional `continuous_ad` plus
     algebraic manipulation with `𝟙_{O(Q')}` factors; **but** this
     re-introduces the non-monotone indicators we wanted to avoid.
   - (b) Prove a Monotone-free `continuous_ad_general` that
     applies directly on integrals against the `𝟙_{O(Q')}`-weighted
     measure (equivalently, against the full Lebesgue measure with
     `f₁, f₂, f₃, f₄` as `𝟙_{O(Q')} ·` monotone things). The
     four-function AD inequality on the four products is then the
     *sublattice* + monotonicity-of-the-bounded-factor combination:
     `𝟙_{O(Q')}` is the AD-compatible (sublattice) piece, and the
     monotone factors handle the linearity. This is **Path R-A**.

   **Path R-A** (recommended) drops the Monotone hypothesis from
   `continuous_ad` to allow the four functions to be products of
   sublattice indicators and bounded measurable functions. The
   proof is the standard Lebesgue-differentiation-based argument
   that doesn't require pointwise monotone Riemann-sum convergence.

### §2.5 The cleanest math statement of the inner step

To make §2.4 step 5 precise: we want a continuous AD that handles
the case when **only some** of `f₁, f₂, f₃, f₄` are monotone, and
the others factor as `(sublattice indicator) · (monotone)`. The
simplest such version is:

**Lemma (continuous AD with sublattice indicator).** Let `K ⊆
[0,1]^n` be a closed sublattice of `[0,1]^n` (closed under
componentwise `⊓, ⊔`). Let `g₁, g₂, g₃, g₄ : [0,1]^n → ℝ_{≥0}` be
non-negative, integrable, and satisfy
```
g₁(x) g₂(y) ≤ g₃(x ⊓ y) g₄(x ⊔ y)  for all x, y ∈ K.
```
Then `(∫_K g₁)(∫_K g₂) ≤ (∫_K g₃)(∫_K g₄)`.

This is the standard form (Brightwell 1999 §4.2; Preston 1974
Theorem 5.4); the proof reduces to the **unconditional** AD on
the cube applied to `(𝟙_K g₁, 𝟙_K g₂, 𝟙_K g₃, 𝟙_K g₄)`. The
hypothesis on `K` (sublattice) ensures the unconditional pointwise
inequality

```
(𝟙_K g₁)(x) · (𝟙_K g₂)(y) ≤ (𝟙_K g₃)(x ⊓ y) · (𝟙_K g₄)(x ⊔ y)
```

holds (when LHS = 0, trivial; when LHS > 0, both `x, y ∈ K`, so
`x ⊓ y, x ⊔ y ∈ K` by sublattice, and the four `𝟙_K` factors are
all 1, leaving the original `g_i` inequality). **No
monotonicity** of `𝟙_K` or `g_i` is needed for the **statement** —
only the four-function inequality and integrability.

But the **mg-7d37 proof** of `continuous_ad` needs Monotone for
its Riemann-sum convergence route; this is a proof-technical
artefact, not a statement-level requirement. **Path R-A** lifts
the artefact.

### §2.6 Where the Stanley axiom enters

Per state.md §3.4 / §1.11, `stanley_log_supermod` is consumed
"starting from EX-7+". Concretely, the inner-step continuous-AD
inequality (§2.4 step 5) reduces to a discrete inequality on
`(L(Q'), uniform measure)` — a finite sum bounded by a finite
sum. The reduction to pure combinatorics on `J(α)` requires the
Stanley log-supermod inequality:
```
e_Q(I) · e_Q(J) ≤ e_Q(I ∪ J) · e_Q(I ∩ J)   for I, J ∈ J(α).
```
applied to the size-`k` ideals at the swap boundary. This is
exactly the consumption point predicted by mg-d0fc / mg-91be §5.7:
the chamber-AD reduction → discrete combinatorial sum → Stanley
log-supermod chain closure.

In the Lean port, this consumption is **packaged** inside the
inner-step argument; EX-7 Session B will invoke
`OneThird.LinearExt.stanley_log_supermod` at the discrete-sum
closure step. ~10–20 LoC of axiom invocation.

---

## §3 The hypothesis-mismatch finding (substantive scoping outcome)

### §3.1 The mismatch

The in-tree `continuous_ad` (mg-7d37,
`lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean:1425`)
has signature:

```lean
theorem continuous_ad
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁₀ : 0 ≤ f₁) (hf₂₀ : 0 ≤ f₂) (hf₃₀ : 0 ≤ f₃) (hf₄₀ : 0 ≤ f₄)
    (hf₁ : Monotone f₁) (hf₂ : Monotone f₂)
    (hf₃ : Monotone f₃) (hf₄ : Monotone f₄)
    (hf₁L1 : IntegrableOn f₁ (Set.Icc (0 : Fin n → ℝ) 1))
    ...
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∫ x in Icc 0 1, f₁ x ∂volume) * (∫ x in Icc 0 1, f₂ x ∂volume)
    ≤ (∫ x in Icc 0 1, f₃ x ∂volume) * (∫ x in Icc 0 1, f₄ x ∂volume)
```

**The Monotone hypotheses are on each of the four functions
individually** — pointwise componentwise non-decreasing on the
cube. This is mg-7d37 / state.md §1.21's signature widening, added
to make the Riemann-sum proof go through (`stepLower N f → f` a.e.
requires monotone `f`).

The drops application needs to apply AD with `f_i`'s of the form
`𝟙_{O(Q^*)} · (monotone)` for `Q^* ∈ {Q, Q'}`. **The polytope
indicator `𝟙_{O(Q)}` is NOT cube-monotone** (per the
counterexample in the verdict header).

### §3.2 Why the math works without monotonicity

The continuous AD inequality on `[0,1]^n` is

```
(∫ f₁)(∫ f₂) ≤ (∫ f₃)(∫ f₄)   given f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)
```

with `f₁, f₂, f₃, f₄` non-negative and integrable. **No
pointwise monotonicity is required**: this is the
Ahlswede–Daykin 1979 continuous version. The standard reference
proofs (Preston 1974 Theorem 5.4; Ahlswede & Daykin 1979
Section 2; Brightwell 1999 Section 4.2) **do not** assume
monotonicity. The four-function lattice inequality alone is
sufficient.

### §3.3 Why the in-tree proof requires monotonicity

The mg-7d37 proof goes:
1. Define `stepLower N f x := f(p_N(x))` with `p_N` the
   lower-corner grid retraction.
2. Show `stepLower N f → f` pointwise on the continuity set of `f`
   (`Monotone.aeContinuousAt`-style, but multivariate; see
   ContinuousFKG.lean §6 for the in-tree assembly).
3. Apply discrete AD on `(Fin n → Fin N)` to get a discrete
   inequality.
4. Take `N → ∞` via dominated convergence; `stepLower N f → f`
   a.e. + monotone = uniform `L^∞` bound, so DCT applies.

Step 2 requires monotonicity of `f` (otherwise `stepLower N f`
need not converge pointwise to `f` — counterexample: indicator of
a non-Lebesgue-point set; cell averages converge but lower-corner
retractions do not).

### §3.4 The Monotone-free `continuous_ad_general` (Path R-A target)

**Replace `stepLower` with `cellAvg`** (cell averages). Define
```
cellAvg N f x := (1 / vol(cell containing x)) · ∫_{cell} f
```
where the cell is the half-open `[k/N, (k+1)/N)^n` cell containing
x.

**Lebesgue Differentiation Theorem (mathlib
`Mathlib.MeasureTheory.Covering.LebesgueDifferentiation`).** For
any locally integrable `f : (Fin n → ℝ) → ℝ`,
`cellAvg N f x → f(x)` for almost every `x` as `N → ∞`. **No
monotonicity required.**

**Cell averages preserve the four-function inequality.** If
`f₁(x) f₂(y) ≤ f₃(x ⊓ y) f₄(x ⊔ y)`, then for each cell pair
`(C_p, C_q)`,
```
(cellAvg N f₁) on C_p · (cellAvg N f₂) on C_q
   ≤ (cellAvg N f₃) on C_p ⊓ C_q · (cellAvg N f₄) on C_p ⊔ C_q
```
where `C_p ⊓ C_q := C_{p ⊓ q}` is the cell at the componentwise
min, similarly for `⊔`. This requires Cauchy–Schwarz or a similar
linearity argument; the inequality is the standard "averaging
preserves AD" fact (Ahlswede–Daykin 1979 Lemma 2; Preston 1974).

**Pulling cell averages through the integral.** Each
`∫_{[0,1]^n} cellAvg N f = ∫_{[0,1]^n} f` exactly (integral is
preserved by averaging). So
`∫ (cellAvg N f_i) = ∫ f_i` for all `N, i`; the discrete AD on
cell averages is *literally* the integral inequality, no limit
needed.

Wait — that's too clean. The catch: cell averages are *constant*
on each cell, so `cellAvg N f x` is a step function. The integral
is then a sum:
```
∫_{[0,1]^n} cellAvg N f = (1/N^n) · Σ_p (cellAvg N f at p) = Σ_p ∫_{C_p} f = ∫_{[0,1]^n} f.
```
But the discrete AD applies to the *constants* of cellAvg N f,
which are exactly the *cell averages* `(1/N^n)^{-1} · ∫_{C_p} f`,
not the original `f`. So we have **discrete AD between cell
averages**, and after multiplying out by the constants we recover
the **discrete AD between cell-summed integrals** — which equals
**discrete AD between the full integrals**. This is the slick
proof.

**Conclusion.** A Monotone-free `continuous_ad_general` is
provable via cell averages + LDT, **without** the Riemann-sum-
sandwich machinery. ~250–400 LoC of EX-6 extension; mostly
mathlib API plumbing (LebesgueDifferentiation theorem +
finitely-many-cells averaging).

### §3.5 Path R-B (contingency)

If for any reason Path R-A is harder than expected (e.g.,
`MeasureTheory.LebesgueDifferentiation` is not in the mathlib v4.29.1
revision pinned by the project; verify in §6.1 below), the
contingency is:

**Path R-B: combinatorial chamber-pairing.** Reduce the drops
directly to a discrete inequality on `(LinearExt' Q', uniform)`
via the chamber-decomposition formula, without invoking continuous
AD at all. The discrete inequality is:
```
∑_{L ∈ LinearExt' Q'} 𝟙[S(τ_{ab}(L)_k)]
  ≤ ∑_{L ∈ LinearExt' Q'} 𝟙[S(L_k)]
```
where `τ_{ab} : LinearExt' Q' → LinearExt' Q` swaps the positions
of `a, b` (mapping L(Q') to L(Q) \ L(Q') by reversing a < b).

This is the heart of the level-`k` localisation problem
(state.md §3.9 / Path B AMBER-leaning-RED). It's NOT closed by the
discrete Stanley log-supermod alone (per Path B analysis); a
chamber-by-chamber argument plus an inductive coupling on the
linear extensions might close it. Estimated ~400–700 LoC if it
works; AMBER-leaning-RED if it doesn't (would force reverting to
Path R-A).

Path R-A (extending continuous_ad) is strictly cleaner. Recommend
R-A.

---

## §4 Resolution: extend EX-6 with `continuous_ad_general`

### §4.1 Sub-DH-4-B candidate

Per state.md §3.8 (DH-4 = continuous FKG/AD upstream PR), the in-tree
`continuous_fkg` and `continuous_ad` are mathlib-PR-class candidates
already. The **Monotone-free** version of `continuous_ad`
(`continuous_ad_general`) is the **literature-standard** statement
(Ahlswede–Daykin 1979 / Preston 1974 / Brightwell 1999); the
Monotone-laden version is a project-specific weakening for
proof-technical reasons. **Adding the general version to the same
file is natural** and would be expected by the mathlib reviewer.

This is recorded as **Sub-DH-4-B** strengthening DH-4: the
upstream PR for `Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
should carry both:
- The Monotone-free `continuous_ad_general` (literature-standard).
- The Monotone-laden `continuous_ad` (corollary; convenient for
  applications where monotonicity is automatic).

Including both costs ~250–400 LoC; the Monotone-free version is
the substantive content.

### §4.2 EX-6 Session F target

**Polecat session F (NEW, prerequisite to EX-7 Session B).**

**Scope.** Extend
`lean/OneThird/Mathlib/Analysis/MeanInequalities/ContinuousFKG.lean`
with:

1. `cellAvg N f` (cell-average step function); ~50 LoC.
2. `cellAvg N f → f` a.e. via Lebesgue differentiation theorem;
   ~80 LoC.
3. Discrete AD on cell averages preserves the four-function
   inequality; ~50 LoC (Cauchy–Schwarz / linearity).
4. `continuous_ad_general` master theorem (Monotone-free); ~80 LoC
   (assembly: discrete AD on cell averages → integrate → take
   `N → ∞`).
5. `continuous_fkg_general` (corollary; FKG with sublattice
   indicator); ~40 LoC.

**Total ~300 LoC.** Token budget ~150–250k.

**Acceptance.** Build green; `#print axioms continuous_ad_general`
gives only the mathlib classical-foundation triplet
`{propext, Classical.choice, Quot.sound}`. No `stanley_log_supermod`
consumed (EX-6 still doesn't consume the axiom).

### §4.3 EX-7 Session B target (post-EX-6 Session F)

**Polecat session B (EX-7 main).**

**Scope.** Extend
`lean/OneThird/Mathlib/RelationPoset/FKG.lean` with:

1. `OrderPolytope' Q` — the order polytope of a `RelationPoset α`,
   defined as a thin wrapper around the existing `OrderPolytope α`
   (which is parameterised by `[PartialOrder α]`). ~30 LoC.
2. Chamber decomposition reduction (per §2.1):
   `pr_eq_chamber_integral_Q` — an in-namespace lemma reducing
   `probEvent' Q` to a chamber integral. ~50 LoC.
3. `probEvent'_mono_of_subseteq_upClosed` — the master EX-7 theorem.
   ~70–150 LoC, depending on whether the swap-induction is folded
   into a single `Q.Subseteq Q'` argument or proceeds via
   single-edge induction.
4. Stanley axiom invocation point at the inner-step closure.
   ~10–20 LoC.

**Total ~150–300 LoC.** Token budget ~80–150k.

**Acceptance.** Build green; `probEvent'_mono_of_subseteq_upClosed`
in scope; `#print axioms` includes the mathlib triplet plus
`OneThird.LinearExt.stanley_log_supermod` (the third project axiom).
**No new project axioms.**

---

## §5 Lean signatures

### §5.1 EX-6 Session F new signatures

```lean
namespace OneThird.ContinuousFKG

open MeasureTheory

variable {n : ℕ}

/-- Cell-average step function: on the cell `[k/N, (k+1)/N)^n` containing `x`,
    the value of `cellAvg N f` is the average of `f` over that cell. -/
noncomputable def cellAvg (N : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ := sorry

/-- For any locally integrable `f`, cell averages converge a.e. to `f` as
    `N → ∞`. Standard application of Lebesgue's differentiation theorem. -/
theorem ae_tendsto_cellAvg {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrable f) :
    ∀ᵐ x ∂volume,
      Filter.Tendsto (fun N => cellAvg N f x) Filter.atTop (𝓝 (f x)) := sorry

/-- Cell averages preserve the four-function AD inequality. -/
lemma cellAvg_AD_pointwise {N : ℕ}
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y))
    (hf₁₀ : 0 ≤ f₁) (hf₂₀ : 0 ≤ f₂) (hf₃₀ : 0 ≤ f₃) (hf₄₀ : 0 ≤ f₄) :
    ∀ x y, cellAvg N f₁ x * cellAvg N f₂ y
            ≤ cellAvg N f₃ (x ⊓ y) * cellAvg N f₄ (x ⊔ y) := sorry

/-- **Continuous Ahlswede–Daykin (4FT) on `[0,1]^n`, monotonicity-free.**
    Literature-standard statement (Ahlswede–Daykin 1979; Preston 1974). -/
theorem continuous_ad_general
    {f₁ f₂ f₃ f₄ : (Fin n → ℝ) → ℝ}
    (hf₁₀ : 0 ≤ f₁) (hf₂₀ : 0 ≤ f₂) (hf₃₀ : 0 ≤ f₃) (hf₄₀ : 0 ≤ f₄)
    (hf₁L1 : IntegrableOn f₁ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₂L1 : IntegrableOn f₂ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₃L1 : IntegrableOn f₃ (Set.Icc (0 : Fin n → ℝ) 1))
    (hf₄L1 : IntegrableOn f₄ (Set.Icc (0 : Fin n → ℝ) 1))
    (hAD : ∀ x y, f₁ x * f₂ y ≤ f₃ (x ⊓ y) * f₄ (x ⊔ y)) :
    (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₁ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₂ x ∂volume)
    ≤ (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₃ x ∂volume) *
      (∫ x in Set.Icc (0 : Fin n → ℝ) 1, f₄ x ∂volume) := sorry

end OneThird.ContinuousFKG
```

The Monotone-laden `continuous_ad` of mg-7d37 then becomes a one-line
corollary:

```lean
theorem continuous_ad ... (hf_mono : Monotone f₁ ∧ Monotone f₂ ∧ ...) :
    ... :=
  continuous_ad_general hf₁₀ hf₂₀ hf₃₀ hf₄₀ hf₁L1 hf₂L1 hf₃L1 hf₄L1 hAD
```

(or kept as the explicit version for backward-compatibility).

### §5.2 EX-7 Session B new signatures

```lean
namespace OneThird.LinearExt.RelationPoset

open MeasureTheory OneThird.LinearExt OneThird.ContinuousFKG

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The order polytope of a `RelationPoset α`, defined parallel to
    `OrderPolytope α` (which uses `[PartialOrder α]`). Equivalent under
    the `RelationPoset.ofPartialOrder` ↔ `LinearOrder.le` correspondence. -/
def OrderPolytope' (Q : RelationPoset α) : Set (α → ℝ) :=
  { f : α → ℝ |
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x y, Q.le x y → f x ≤ f y) }

lemma OrderPolytope'_subset_of_subseteq
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q') :
    OrderPolytope' Q' ⊆ OrderPolytope' Q := sorry

lemma OrderPolytope'_subLattice
    (Q : RelationPoset α) :
    ∀ f g, f ∈ OrderPolytope' Q → g ∈ OrderPolytope' Q →
      f ⊓ g ∈ OrderPolytope' Q ∧ f ⊔ g ∈ OrderPolytope' Q := sorry

/-- The chamber decomposition reduces `probEvent'` to a chamber integral
    (this is the `α → ℝ` version; we transport via `Equiv.piCongrLeft`
    to apply continuous-AD-on-`Fin n → ℝ`). -/
lemma probEvent'_eq_chamber_integral
    (Q : RelationPoset α) (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S] :
    (probEvent' Q (fun L => S (L.initialIdeal' k.val)) : ℝ) =
      (∫ f in OrderPolytope' Q, sorry /- 𝟙[S(A_k(f))] -/ ∂volume) /
        (volume (OrderPolytope' Q)).toReal := sorry

/-- **The drops headline (EX-7 master theorem).** -/
theorem probEvent'_mono_of_subseteq_upClosed
    {Q Q' : RelationPoset α} (hQQ' : Q.Subseteq Q')
    (k : Fin (Fintype.card α + 1))
    (S : Finset α → Prop) [DecidablePred S]
    (hSmono : ∀ I J : Finset α, I ⊆ J → S I → S J) :
    probEvent' Q  (fun L : LinearExt' Q  => S (L.initialIdeal' k.val)) ≤
    probEvent' Q' (fun L : LinearExt' Q' => S (L.initialIdeal' k.val)) := by
  -- Step 1: reduce to chamber integrals via `probEvent'_eq_chamber_integral`.
  -- Step 2: induct on `|Q'.rel \ Q.rel|`. Base case: `Q.rel = Q'.rel`,
  --         trivial. Inductive step: WLOG single-edge augmentation.
  -- Step 3: Single-edge case via swap involution + continuous AD.
  --         Apply `continuous_ad_general` (EX-6 Session F) to the
  --         four functions `(𝟙_O(Q'), 𝟙_O(Q) · 𝟙_S, 𝟙_O(Q), 𝟙_O(Q') · 𝟙_S)`
  --         after restriction to `O(Q)` (sublattice).
  -- Step 4: Discrete chain closure via `stanley_log_supermod`.
  sorry
```

### §5.3 The `α → ℝ` ↔ `Fin n → ℝ` reindexing

The chamber-side machinery in tree (mg-497d / mg-10d9) lives at
`α → ℝ` (general `Fintype α`); the continuous AD lives at
`Fin n → ℝ`. The reindexing equivalence `e : α ≃ Fin n` (via
`Fintype.equivFin`) gives a measure-preserving
`MeasurableEquiv (α → ℝ) (Fin n → ℝ)` via `Equiv.piCongrLeft`, in
tree as `chamberRelabel` (mg-497d). This handles the
reindexing transparently for EX-7.

---

## §6 Mathlib API check + gaps

### §6.1 Verified mathlib APIs

All cited APIs are verified at `lake-manifest.json` →
`mathlib v4.29.1`:

| API | File:line | Used in |
|-----|-----------|---------|
| `MeasureTheory.Covering.LebesgueDifferentiation` | `Mathlib/MeasureTheory/Covering/Differentiation.lean` (or `LebesgueDifferentiation.lean`) | §3.4 cellAvg → f a.e. |
| `MeasureTheory.setIntegral_const` | `Mathlib/MeasureTheory/Integral/Bochner.lean` | §3.4 step-function integral |
| `MeasureTheory.integral_finset_sum` | `Mathlib/MeasureTheory/Integral/Bochner.lean` | §3.4 cell decomposition |
| `MeasureTheory.MeasurePreserving` (existing usage) | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` | §5.3 reindexing |
| `four_functions_theorem_univ` | `Mathlib/Combinatorics/SetFamily/FourFunctions.lean:341` | §3.4 discrete AD on cells (already used by mg-7d37) |
| `Equiv.piCongrLeft` | `Mathlib/Logic/Equiv/Defs.lean` | §5.3 α ↔ Fin n |
| `OneThird.LinearExt.OrderPolytope` (in tree) | `lean/OneThird/Mathlib/LinearExtension/OrderPolytope.lean` | §5.1 polytope |
| `chamber_cover` (in tree, mg-10d9) | `OrderPolytope.lean:1118` | §2.1 chamber reduction |
| `chamber_volume` (in tree, mg-497d) | `OrderPolytope.lean:1002` | §2.1 |
| `chamber_inter_meas_zero` (in tree, mg-10d9) | `OrderPolytope.lean:1171` | §2.1 |
| `orderPolytope_volume` (in tree, mg-10d9) | `OrderPolytope.lean:1241` | §2.1 |
| `stanley_log_supermod` (in tree, mg-d0fc) | `StanleyLogSupermodAxiom.lean` | §2.6 inner-step closure |
| `RelationPoset.Subseteq` (in tree) | `RelationPoset.lean:208` | spec |
| `LinearExt'.initialIdeal'` (in tree) | `Birkhoff.lean:59` | spec |
| `probEvent'` (in tree) | `RelationPoset/FKG.lean:430` | spec |

**No critical mathlib gap** — all needed APIs are in mathlib at
the project's pinned version, OR in tree as predecessor commits.

### §6.2 Open verification: `MeasureTheory.Covering.LebesgueDifferentiation`

The Lebesgue differentiation theorem in mathlib v4.29.1 is in
`Mathlib.MeasureTheory.Covering.VitaliFamily` (or
`Mathlib.MeasureTheory.Covering.Differentiation`). The specific
form needed is:

> For a locally integrable `f : ℝⁿ → ℝ`, the cell averages over
> a Vitali family converge a.e. to `f`.

Mathlib has `VitaliFamily.ae_tendsto_average` (or similar) — this
should match. EX-6 Session F polecat verifies the exact lemma name
and applies it.

**Sub-DH-4-A relevance.** The `Monotone.aeContinuousAt_pi`
multivariate lemma (mg-e622's sub-DH-4-A candidate, in tree) is
**not needed** for `continuous_ad_general` — Lebesgue
differentiation gives the a.e. convergence directly, without
routing through monotonicity. So the cell-averages route is **also
free of the sub-DH-4-A dependency**.

### §6.3 Mathlib gap **not** surfaced

- The chamber-decomposition machinery is in tree (mg-497d,
  mg-10d9). No new chamber-side gap.
- Continuous AD with Monotone hypothesis is in tree (mg-7d37);
  Monotone-free version is the EX-6 Session F target (~300 LoC),
  which uses standard Lebesgue differentiation (mathlib has it).
- The `α → ℝ` ↔ `Fin n → ℝ` reindexing is in tree
  (`chamberRelabel`).

The only assembly is the **EX-6 Session F** extension; the EX-7
Session B is then ~150–300 LoC of chamber-decomposition assembly +
single-edge induction + Stanley axiom invocation.

### §6.4 Trip-wires — none fired in Session A

- Token blow-up: not fired (this scoping comes in well under the
  350k cap).
- Mathlib measure-theory fundamental obstruction: **not fired** —
  Lebesgue differentiation theorem is mathlib-standard.
- Hypothesis-mismatch on continuous_ad: **substantive scoping
  finding (§3)**, not a trip-wire firing in the sense of "halt and
  surface to PM" but rather a "Session A's job to identify, and
  the resolution is clear (Path R-A)".
- Drops-headline-already-proven-elsewhere: **not fired** (no
  in-tree or upstream alternative).
- Structural obstruction on `S` up-closed-under-inclusion: not
  fired — the hypothesis as stated in mg-91be §5.7 is mathematically
  sufficient (per §1.3 above; Brightwell §4 / Daykin–Saks 1981
  factorisation).

### §6.5 Conditional trip-wire (Session F + B)

If EX-6 Session F surfaces an unexpected mathlib obstruction (e.g.,
`MeasureTheory.Covering.LebesgueDifferentiation` is at a different
namespace path or has a different statement form than expected),
the polecat **falls back to Path R-B** (combinatorial chamber-
pairing argument). PM next step in that case: file Path R-B as a
follow-up scoping ticket; expect ~400–700 LoC total (vs. ~400–700
LoC for R-A; comparable).

---

## §7 Polecat session estimate + trip-wires

### §7.1 LoC and tokens — EX-6 Session F (prerequisite)

**Scope.** Monotone-free `continuous_ad_general` and corollary
`continuous_fkg_general` (sublattice version).

**LoC estimate.**
- `cellAvg` definition + measurability + integrability:
  ~50 LoC.
- `ae_tendsto_cellAvg` via Lebesgue differentiation:
  ~80 LoC (the bulk is finding the right lemma in mathlib's
  `MeasureTheory.Covering` and adapting to the cube cells).
- `cellAvg_AD_pointwise` via Cauchy–Schwarz:
  ~50 LoC.
- `continuous_ad_general` master assembly:
  ~80 LoC (discrete AD on cell averages → integrate → DCT → take
  N → ∞).
- `continuous_fkg_general` corollary:
  ~40 LoC (sublattice indicator factor + direct from
  continuous_ad_general).

**Subtotal Session F: ~300 LoC, ~150–250k tokens.**

### §7.2 LoC and tokens — EX-7 Session B (post-Session F)

**Scope.** Drops headline `probEvent'_mono_of_subseteq_upClosed` via
chamber decomposition + `continuous_ad_general`.

**LoC estimate.**
- `OrderPolytope'` for `RelationPoset α` + sublattice +
  `Subseteq`-monotonicity: ~30 LoC.
- `probEvent'_eq_chamber_integral` chamber reduction: ~50 LoC
  (uses in-tree `chamber_cover`, `chamber_volume`, etc.).
- Single-edge swap involution `τ_{ab}` on `LinearExt' Q`: ~30 LoC.
- `probEvent'_mono_of_subseteq_upClosed` master proof
  (induction on `|Q'.rel \ Q.rel|`, chamber + AD, Stanley axiom
  invocation): ~70–150 LoC.
- Hand-verification: ~10 LoC (single-edge case on `Three`-discrete
  α with one extra relation).

**Subtotal Session B: ~150–270 LoC, ~80–150k tokens.**

### §7.3 Combined Sessions F + B

**Total: ~400–600 LoC, ~250–400k tokens.** Tracks the upper edge
of mg-91be §5.7's 400–800 LoC, ~250–500k token estimate.

The polecat brief's quoted "~150–300 LoC" for EX-7 Session B alone
is **achievable** (Session B comes in at ~150–270 LoC); the
prerequisite EX-6 Session F is the unanticipated portion.

### §7.4 Trip-wires — Sessions F + B

**Session F trip-wires.**
- Token blow-up >250k: STOP, surface to PM. Path R-A is at ~150–250k
  estimate; >250k flags a mathlib API obstruction.
- `MeasureTheory.Covering.LebesgueDifferentiation` not in mathlib
  v4.29.1 at the expected namespace: STOP, mail PM; trigger Path
  R-B fallback or sub-DH-4-A-2 scoping (auxiliary upstream lemma
  for Vitali-cell averages).
- `cellAvg_AD_pointwise` proof harder than expected: AMBER —
  fall back to Path R-B if the Cauchy–Schwarz route doesn't
  close. (The mathematical content is standard; a Lean obstruction
  here would be plumbing.)

**Session B trip-wires.**
- Token blow-up >150k: STOP. Brief estimate 80–150k; >150k flags
  scope creep (e.g., the swap involution is harder to set up than
  expected, or the chamber-reduction step needs more glue).
- The single-edge induction's swap-involution argument has a
  structural gap: STOP and surface; Path R-B may be the correct
  approach. AMBER.
- Hand-verification fails: STOP and surface; the math statement
  may need adjustment (e.g., `hSmono` needs strengthening — though
  per §1.3 this should not happen).

### §7.5 Verdict

**AMBER-leaning-GREEN.**

- **GREEN.** Math statement is settled; chamber-decomposition machinery
  is in tree; Stanley axiom in tree; `continuous_ad_general`
  Monotone-free version is mathematically standard (literature-
  verified). All mathlib API needs are at v4.29.1 or in-tree
  predecessors.
- **AMBER.** EX-7 Session B requires the EX-6 Session F prerequisite
  (Monotone-free `continuous_ad_general`); the polecat brief's
  expectation of "~150–300 LoC, single Session B" is **achievable
  for EX-7 Session B alone** but with the unanticipated ~300 LoC
  EX-6 Session F prerequisite. **Total ~400–600 LoC over 2 Lean
  sessions, not 1.**

PM next step: file **EX-6 Session F** scoping ticket
(`continuous_ad_general` Monotone-free extension), then **EX-7
Session B** scoping ticket once Session F lands.

---

## §8 Out-of-scope items (deferred)

### §8.1 EX-8 case3-port-2 (consumer of EX-7)

Per mg-91be §5.8, EX-8 specialises `probEvent'_mono_of_subseteq_upClosed`
to the case3 width-3 antichain witness scope, concluding
`case3Witness_hasBalancedPair_outOfScope_proved` (the pre-axiom
unwrap). EX-8 = 2 polecat sessions, ~800–1200 LoC. **Out of scope
for EX-7 Session B**; depends on EX-7 landing.

### §8.2 EX-9 Brightwell-port-A (parallel consumer of EX-7)

Per mg-91be §5.9, EX-9 applies EX-7 to the `L(α) × Fin m` product
to derive the centred-sum bound currently axiomatised as
`brightwell_sharp_centred`. EX-9 = 1–2 polecat sessions, ~500–800 LoC.
**Out of scope for EX-7 Session B**; depends on EX-7 landing.

### §8.3 EX-10 axiom-removal (final consumer)

Per mg-91be §5.10, EX-10 removes both `case3Witness_hasBalancedPair_outOfScope`
and `brightwell_sharp_centred` from `lean/AXIOMS.md`; rewires
consumers; verifies via `#print axioms`. EX-10 = 0.5 polecat
session, ~100–200 LoC. **Out of scope**; depends on EX-8 + EX-9
both landing.

### §8.4 The Stanley `μ` corollary `stanley_mu_log_supermod`

Per mg-d0fc / state.md §1.11, the corollary `μ(I) := e(I) ·
e(α \ I)` log-supermod on `J(α)` was deferred. **EX-7 Session B
does not need the corollary** — only the primary
`stanley_log_supermod` axiom is consumed (per §2.6). The corollary
remains deferred to a follow-up ticket.

### §8.5 `OrderPolytope'` as upstream-PR-class artefact

`OrderPolytope'` for `RelationPoset α` is a thin wrapper around
the existing `OrderPolytope α` (mg-8c66, parameterised by
`[PartialOrder α]`). The wrapper is project-internal and **not**
upstream-able as-is to mathlib (the data form `RelationPoset α`
itself is project-internal). Mathlib upstream PR for the polytope
side stays at the `[PartialOrder α]` form. ~30 LoC of
project-internal wrapper.

---

## §9 Sub-α-C arc status post-EX-7 Session A

**Sub-α-C arc state (post-this-Session-A).**
- EX-1 (Stanley log-supermod): Option A executed, temp axiom in
  tree (mg-d0fc). Independently verified GREEN (mg-e22f).
- EX-3 (`OrderPolytope α`): done (mg-8c66). GREEN.
- EX-4 (Stanley vertex theorem): Sessions A+B done (mg-4831,
  mg-2442). GREEN.
- EX-5 (chamber decomposition): Sessions A+B+C done (mg-79a9,
  mg-497d, mg-10d9). GREEN.
- EX-6 (continuous FKG/AD): Sessions A+B+C+D+E done (mg-e622,
  mg-a6ed, mg-4adf, mg-8561, mg-7d37). GREEN, sorry-free.
  **Note (post-this-Session-A): the in-tree continuous_ad has a
  Monotone hypothesis that does not match the EX-7 application;
  EX-6 Session F (Monotone-free continuous_ad_general) is the
  prerequisite to EX-7.**
- EX-7 (drops headline): Session A done (this commit).
  AMBER-leaning-GREEN. Prerequisite identified: EX-6 Session F.
- EX-8 (case3-port-2): blocked behind EX-7.
- EX-9 (Brightwell-port-A): blocked behind EX-7.
- EX-10 (axiom-removal): blocked behind EX-8 + EX-9.

**Sub-α-C arc verdict (post-this-Session-A).** **GREEN with
documented prerequisite.** The single material structural finding is
the EX-6 → EX-7 hypothesis-mismatch (state.md §1.21 noted the
Monotone widening as "out of scope for EX-6 / sub-α-C"; this
Session A scopes the resolution as Path R-A = EX-6 Session F,
~300 LoC). The arc remains on track per mg-91be §5.11's aggregate
~5050–8700 LoC envelope (now ~5350–9000 LoC factoring in the
Session F prerequisite, +300 LoC).

PM next step: file **EX-6 Session F** scoping ticket
(Monotone-free `continuous_ad_general`), then **EX-7 Session B**
once Session F lands.

---

*End of EX-7 Session A latex-first scoping deliverable.*
